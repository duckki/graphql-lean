import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupRawBatches
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupGroupClosureAccounting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupStreamNoticeMetadata
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupStreamAnnouncements

/-! The actual startup publisher registry agrees with observable open group refs. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Generated group refs cannot appear in any actual raw startup stream notice or reference. -/
theorem ExecutedWork.startup_rawBatches_noStreamRef
    {work batches group dependencies producer} (generated : ExecutedWork work)
    (startup : InitialStartup) (valid : ValidGraphEvents work batches.flatten)
    (known : NodeAt work group .group dependencies producer)
    : let initial := State.initialize (Work.fromExecution work) startup
      ∀ output ∈ (initial.rawBatches batches).2, output.NoStreamRef group.ref := by
  let initial := State.initialize (Work.fromExecution work) startup
  have streams : initial.StreamsSatisfy (StreamLocated work) := by
    intro stream member
    rw [State.initializeWithStartup_streams] at member
    exact ⟨[], none, (createWorkQueue_initialStreams_nodeAt work).1 stream member⟩
  have notices := streams.rawBatches_notices batches
    (fun _ member => (valid.event_matches member).childStreamsLocated)
  have noNotice output (member : output ∈ (initial.rawBatches batches).2)
      : group.ref ∉ rawStreamNoticeRefs output := by
    intro notice
    obtain ⟨stream, _, _, same, located⟩ := (notices output member).located_ref notice
    exact generated.groupStreamRefsDisjoint known located same.symm
  dsimp only
  intro output member
  refine ⟨noNotice output member, ?_⟩
  intro reference
  obtain ⟨index, selected⟩ := List.mem_iff_getElem?.mp member
  have earlier :=
    (initial.rawBatches_streamReferencesAnnounced batches).atEvent
    selected reference
  rcases List.mem_append.mp earlier with root | noticed
  · have initialNotice :=
      State.initializeWithStartup_streamRoots (Work.fromExecution work) startup root
    rw [State.initializeWithStartup_initialStreams] at initialNotice
    obtain ⟨stream, member, same⟩ := List.mem_map.mp initialNotice
    exact generated.groupStreamRefsDisjoint known
      ((createWorkQueue_initialStreams_nodeAt work).2 stream member) same.symm
  · obtain ⟨carrier, prior, notice⟩ := List.mem_flatMap.mp noticed
    exact noNotice carrier (List.mem_of_mem_take prior) notice

/-- On every actual raw startup prefix, active publisher group refs agree exactly with
observable open refs. Initial failed roots stay wire-open until their real forwarded
completion, while retirement prevents their later reannouncement.
-/
theorem ExecutedWork.startup_rawBatchPrefix_groupRegistry
    {work batches group dependencies producer before}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (valid : ValidGraphEvents work batches.flatten)
    (known : NodeAt work group .group dependencies producer)
    (isPrefix
      : let initial := State.initialize (Work.fromExecution work) startup
        before.IsPrefix (initial.rawBatches batches).2)
    : let initial := State.initialize (Work.fromExecution work) startup
      let publisher : IncrementalPublisher :=
        { active := initial.initialGroups ++ initial.initialStreams }
      group.ref
        ∈ (publisher.normalizeBatch before).1.active.map Execution.DeliveryNode.ref
      ↔ Open
          ((initial.initialGroups ++ initial.initialStreams).map
            Execution.DeliveryNode.ref)
          (publisher.normalizeBatch before).2 group.ref := by
  let initial := State.initialize (Work.fromExecution work) startup
  let publisher : IncrementalPublisher :=
    { active := initial.initialGroups ++ initial.initialStreams }
  have pending := State.initializeWithStartup_pendingAccounting work generated.declarations startup
  have fresh := State.rawBatches_groupNoticesFresh pending.liveGroups
    (State.initializeWithStartup_pendingGroupFailures work startup)
    batches (fun _ member => valid.event_matches member)
  have registry := publisher.registry_group_ref_normalize
    ((initial.initialGroups ++ initial.initialStreams).map Execution.DeliveryNode.ref) [] before
    (IncrementalPublisher.registry_initial _ group.ref) (by simp [completedRefs])
    (fun event member => generated.startup_rawBatches_noStreamRef startup valid known event
      (isPrefix.subset member)) (fresh.prefix isPrefix)
  simpa only [List.nil_append] using registry

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
