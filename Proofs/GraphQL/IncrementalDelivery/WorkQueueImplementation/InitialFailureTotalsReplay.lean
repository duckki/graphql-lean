import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupFailureBlocks

/-! Retained initial observations license diagnostics through the ordinary FIFO runner. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Actual batch blocks preserve queued causes and emitted aggregate provenance.
The entire supplied batch licenses cache exposure before individual callback consumption. -/
theorem State.FailureSourceFrame.sourceBatchBlocks_initial_totals {queue : State}
    {work before} (frame : queue.FailureSourceFrame work before)
    (queued : queue.QueuedFailureSources work before) (publisher : IncrementalPublisher)
    (events : List GraphEvent)
    (sources : ∀ event ∈ before ++ events, event.MatchesWork work)
    (running : queue.terminated = false)
    : (queue.sourceBatchBlocks publisher events).1.FailureSourceFrame work
        (before ++ events)
      ∧ (queue.sourceBatchBlocks publisher events).1.QueuedFailureSources work
          (before ++ events)
      ∧ SourceBlocksHaveFailureTotals work before
          (queue.sourceBatchBlocks publisher events).2.2 := by
  have extended : queue.FailureSourceFrame work (before ++ events) :=
    ⟨frame.rejections.mono (fun _ _ member => List.mem_append_left events member),
      frame.unique, frame.sound, frame.matching, frame.started⟩
  have waiting := queued.weaken (List.subset_append_left before events)
  have reports := extended.handleGraphEvents_sources waiting events
    (List.subset_append_right _ _) sources
  refine ⟨?_, ?_, ?_⟩
  · rw [(queue.sourceBatchBlocks_agrees publisher events).1]
    exact extended.handleGraphEvents events (List.subset_append_right _ _)
      sources
  · rw [(queue.sourceBatchBlocks_agrees publisher events).1]
    exact reports.1
  · intro group errors emitted
    rw [queue.sourceBatchBlocks_inputs_of_open publisher events running]
    rw [(queue.sourceBatchBlocks_agrees publisher events).2.2] at emitted
    exact reports.2 group errors
      ((publisher.normalizeBatch_atomicGroupFailure_mem _).mp emitted)

/-- Multi-batch provenance follows actual cache snapshots and pending FIFO state. -/
theorem State.FailureSourceFrame.sourceRunBlocks_initial_totals {queue : State}
    {work before} (frame : queue.FailureSourceFrame work before)
    (queued : queue.QueuedFailureSources work before) (publisher : IncrementalPublisher)
    (batches : List (List GraphEvent))
    (sources : ∀ event ∈ before ++ batches.flatten, event.MatchesWork work)
    : SourceBlocksHaveFailureTotals work before
        (queue.sourceRunBlocks publisher batches).2.2 := by
  induction batches generalizing queue publisher before with
  | nil => intro group errors emitted; cases emitted
  | cons batch rest ih =>
      cases running : queue.terminated with
      | true =>
          rw [queue.sourceRunBlocks_of_terminated publisher _ running]
          intro group errors emitted
          cases emitted
      | false =>
          have firstMatches : ∀ event ∈ before ++ batch, event.MatchesWork work := by
            intro event member
            apply sources event
            simpa only [List.flatten_cons, List.append_assoc]
              using List.mem_append_left rest.flatten member
          obtain ⟨next, waiting, certified⟩ := frame.sourceBatchBlocks_initial_totals queued publisher
            batch firstMatches running
          have tailTotals := ih next waiting (queue.sourceBatchBlocks publisher batch).2.1
            (by simpa only [List.flatten_cons, List.append_assoc] using sources)
          apply certified.append
          rw [queue.sourceBatchBlocks_inputs_of_open publisher batch running]
          exact tailTotals

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
