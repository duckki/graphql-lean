import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupPublisherRegistry
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.BatchOutputReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.OutputShape

/-! The publisher's group registry follows actual batched notice and closure histories. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Actual batches preserve stream references to earlier notices. -/
theorem State.rawBatches_streamReferencesAnnounced (queue : State)
    (batches : List (List GraphEvent))
    : ReferencesAnnounced rawStreamNoticeRefs rawStreamReferenceRefs queue.rootStreams
        (queue.rawBatches batches).2 := by
  induction batches generalizing queue with
  | nil => trivial
  | cons batch rest ih =>
      exact (queue.handleGraphEvents_streamReferencesAnnounced batch).append
        ((ih _).mono (queue.handleGraphEvents_streamRoots batch))

/-- Stream notice descriptors remain located throughout actual raw host batches. -/
theorem State.StreamsSatisfy.rawBatches_notices {queue : State} {property}
    (known : queue.StreamsSatisfy property) (batches : List (List GraphEvent))
    (supplied : ∀ event ∈ batches.flatten, event.ChildStreamsSatisfy property)
    : ∀ output ∈ (queue.rawBatches batches).2, output.StreamNoticesSatisfy property := by
  induction batches generalizing queue with
  | nil => intro output impossible; cases impossible
  | cons batch rest ih =>
      have first : ∀ event ∈ batch, event.ChildStreamsSatisfy property :=
        fun event member => supplied event (List.mem_append_left _ member)
      have later := ih (known.handleGraphEvents batch first)
        (fun event member => supplied event (List.mem_append_right _ member))
      intro output member
      exact (List.mem_append.mp member).elim (known.handleGraphEvents_notices batch first output)
        (later output)

/-- A generated group ref is never a stream notice or reference in actual raw batch output. -/
theorem createWorkQueue_rawBatches_noStreamRef {work batches group dependencies producer}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work (List.flatten batches))
    (known : NodeAt work group .group dependencies producer)
    : ∀ output ∈ ((State.initialize (Work.fromExecution work)).rawBatches batches).2,
        output.NoStreamRef group.ref := by
  let queue := State.initialize (Work.fromExecution work)
  have initial : queue.StreamsSatisfy (StreamLocated work) := fun stream member =>
    ⟨[], none, (createWorkQueue_initialStreams_nodeAt work).1 stream member⟩
  have notices := initial.rawBatches_notices batches
    (fun _ member => (valid.event_matches member).childStreamsLocated)
  have noNotice output (member : output ∈ (queue.rawBatches batches).2)
      : group.ref ∉ rawStreamNoticeRefs output := by
    intro notice
    obtain ⟨stream, _, _, same, located⟩ := (notices output member).located_ref notice
    exact generated.groupStreamRefsDisjoint known located same.symm
  intro output member
  refine ⟨noNotice output member, ?_⟩
  intro reference
  obtain ⟨index, selected⟩ := List.mem_iff_getElem?.mp member
  have earlier := (queue.rawBatches_streamReferencesAnnounced batches).atEvent selected reference
  rcases List.mem_append.mp earlier with initial | noticed
  · obtain ⟨stream, member, same⟩ := List.mem_map.mp
      (createWorkQueue_streamRoots (Work.fromExecution work) initial)
    exact generated.groupStreamRefsDisjoint known
      ((createWorkQueue_initialStreams_nodeAt work).2 stream member) same.symm
  · obtain ⟨carrier, prior, notice⟩ := List.mem_flatMap.mp noticed
    exact noNotice carrier (List.mem_of_mem_take prior) notice

/-- Actual batch concatenation preserves freshness against every earlier group closure. -/
theorem State.rawBatches_groupNoticesFresh {queue : State} {work}
    (live : queue.LiveGroupsRegistered) (pending : queue.PendingGroupFailures)
    (batches : List (List GraphEvent))
    (matching : ∀ event ∈ batches.flatten, event.MatchesWork work)
    : GroupNoticesFresh queue.RetiredGroup (queue.rawBatches batches).2 := by
  induction batches generalizing queue with
  | nil => trivial
  | cons batch rest ih =>
      have first : ∀ event ∈ batch, event.MatchesWork work :=
        fun event member => matching event (List.mem_append_left _ member)
      have closed := State.handleGraphEvents_closureAccounting live pending batch
      have later := ih (live.handleGraphEvents batch) closed.1
        (fun event member => matching event (List.mem_append_right _ member))
      exact (State.handleGraphEvents_groupNoticesFresh live pending batch first).append
        (later.mono (fun ref old => old.elim
          (fun retired => retired.handleGraphEvents batch)
          (fun member => (closed.2.closed ref member).1)))

/-- Every value-bearing event in actual raw output has a nonempty value list. -/
theorem State.rawBatches_nonemptyValues (queue : State) (batches : List (List GraphEvent))
    (nonempty : ∀ event ∈ batches.flatten, event.NonemptyItems)
    : ∀ output ∈ (queue.rawBatches batches).2, output.NonemptyValues := by
  induction batches generalizing queue with
  | nil => intro output impossible; cases impossible
  | cons batch rest ih =>
      intro output member
      exact (List.mem_append.mp member).elim
        (queue.handleGraphEvents_nonemptyValues batch
          (fun event member => nonempty event (List.mem_append_left _ member)) output)
        (ih _ (fun event member => nonempty event (List.mem_append_right _ member)) output)

/-- Every actual raw batch prefix has exact active/open agreement on generated group refs. -/
theorem createWorkQueue_rawBatchPrefix_groupRegistry
    {work batches group dependencies producer before} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work (List.flatten batches))
    (known : NodeAt work group .group dependencies producer)
    (isPrefix
      : before.IsPrefix
          ((State.initialize (Work.fromExecution work)).rawBatches batches).2)
    : let queue := State.initialize (Work.fromExecution work)
      let publisher : IncrementalPublisher :=
        { active := queue.initialGroups ++ queue.initialStreams }
      group.ref
        ∈ (publisher.normalizeBatch before).1.active.map Execution.DeliveryNode.ref
      ↔ Open
          ((queue.initialGroups ++ queue.initialStreams).map Execution.DeliveryNode.ref)
          (publisher.normalizeBatch before).2 group.ref := by
  let queue := State.initialize (Work.fromExecution work)
  let publisher : IncrementalPublisher := { active := queue.initialGroups ++ queue.initialStreams }
  have fresh := State.rawBatches_groupNoticesFresh
    (createWorkQueue_liveGroupsRegistered (Work.fromExecution work))
    (createWorkQueue_pendingGroupFailures (Work.fromExecution work)) batches (fun _ member => valid.event_matches member)
  have registry := publisher.registry_group_ref_normalize
    ((queue.initialGroups ++ queue.initialStreams).map Execution.DeliveryNode.ref) [] before
    (IncrementalPublisher.registry_initial _ group.ref) (by simp [completedRefs])
    (fun event member => createWorkQueue_rawBatches_noStreamRef generated valid known event
      (isPrefix.subset member)) (fresh.prefix isPrefix)
  simpa only [List.nil_append] using registry

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
