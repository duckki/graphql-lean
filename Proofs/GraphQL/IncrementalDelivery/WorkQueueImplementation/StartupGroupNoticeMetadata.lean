import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialStartupRetirement
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupNoticeMetadata
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupRawBatches
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupGroupClosureMetadata

/-! Actual startup group notices retain exact contributing descriptors from the original work. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Structural notice provenance follows every actual startup host batch and raw control.
The explicit initial report tail emits no new group descriptor.
-/
theorem NoticeReplayFrame.rawBatches {work queue} (frame : NoticeReplayFrame work queue)
    (generated : ExecutedWork work)
    (batches : List (List GraphEvent))
    (matching : ∀ event ∈ batches.flatten, event.MatchesWork work)
    : NoticeReplayFrame work (queue.rawBatches batches).1
      ∧ ∀ output ∈ (queue.rawBatches batches).2, output.GroupNoticesLocated work := by
  have ordinary (current : State) (known : NoticeReplayFrame work current)
      (more : List (List GraphEvent))
      (sources : ∀ event ∈ more.flatten, event.MatchesWork work)
      : NoticeReplayFrame work (current.rawBatches more).1
        ∧ ∀ output ∈ (current.rawBatches more).2,
            output.GroupNoticesLocated work := by
    induction more generalizing current with
    | nil => exact ⟨known, by simp [State.rawBatches]⟩
    | cons batch rest ih =>
        obtain ⟨next, first⟩ := known.handleGraphEvents generated batch
          (fun event member => sources event (List.mem_append_left _ member))
        obtain ⟨last, later⟩ := ih _ next
          (fun event member => sources event (List.mem_append_right _ member))
        exact ⟨last, fun output member =>
          (List.mem_append.mp member).elim (first output) (later output)⟩
  exact ordinary queue frame batches matching

/-- Every actual startup atomic group notice has exact structural contributor provenance.
The proof follows the actual raw output and publisher, independently of notice admission.
-/
theorem State.startup_runNormalized_atomicGroupNoticesLocated {work inputs}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (valid : ValidGraphEvents work inputs.flatten)
    : let initial := State.initialize (Work.fromExecution work) startup
      ∀ event ∈ (initial.runNormalized inputs).2.flatten.flatMap publicationAtoms,
        GroupNoticesLocated work event := by
  let initial := State.initialize (Work.fromExecution work) startup
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have parent := generated.initialStartup_parentCutFrame canonical startup
  have owners := State.initializeWithStartup_taskOwnerFrame work startup
  have frame : NoticeReplayFrame work initial :=
    ⟨⟨owners.keys, parent.records, (generated.initialStartup_rootReplayFrame canonical
      startup).live.support⟩,
      owners.registered, owners.matching⟩
  have raw := (frame.rawBatches generated inputs
    (fun event member => valid.event_matches member)).2
  let publisher : IncrementalPublisher :=
    { active := initial.initialGroups ++ initial.initialStreams }
  have normalized := publisher.normalizeBatch_groupNoticesLocated raw
  dsimp only
  rw [State.runNormalized_rawBatches]
  intro event member
  obtain ⟨original, emitted, atom⟩ := List.mem_flatMap.mp member
  exact publicationAtoms_groupNoticesLocated original (normalized original emitted) event atom

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
