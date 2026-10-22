import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureReportReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.UncancelledReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.BatchOutputReplay

/-! Cancellation reports follow actual batches, including deferred startup forwarding. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Every cancellation marker has a positive emitted or still-pending report.
The source frame licenses each batch's cached causes. Actual dispatch consumes pending
controls at their FIFO position; a prefix may retain unconsumed notifications. -/
theorem ExecutedWork.rawBatches_fifoCancelledRecordsReported {work batches}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work (List.flatten batches))
    (started : inputsStarted work batches = true)
    : let queue := State.initialize (Work.fromExecution work)
      (queue.rawBatches batches).1.FifoCancelledRecordsReported work
        (queue.rawBatches batches).2 := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have loop {queue before events}
      (frame : UncancelledReplayFrame queue work parents before)
      (reported : queue.FifoCancelledRecordsReported work events)
      (more : List (List GraphEvent))
      (valid : ValidGraphEvents work (before ++ more.flatten))
      (started : queue.batchesStarted more = true)
      : (queue.rawBatches more).1.FifoCancelledRecordsReported work
          (events ++ (queue.rawBatches more).2) := by
    induction more generalizing queue before events with
    | nil => simpa only [State.rawBatches, List.append_nil] using reported
    | cons batch rest ih =>
        obtain ⟨running, accepted, remaining⟩ := queue.batchesStarted_cons batch rest started
        have firstValid := valid.prefix
          (show (before ++ batch).IsPrefix (before ++ (batch :: rest).flatten) from
            ⟨rest.flatten, by simp [List.append_assoc]⟩)
        have cached := frame.rejected.mono
          (fun _ _ matching => generated.matchedTaskFailure_positive matching)
        have nextReported := reported.handleGraphEvents generated cached frame.parent.records
          frame.parent.links canonical batch
          (fun _ member => firstValid.eachMatches (List.mem_append_right _ member))
        have nextFrame := frame.handleGraphEvents generated canonical batch firstValid running
          accepted
        have final := ih nextFrame nextReported
          (by simpa only [List.flatten_cons, List.append_assoc] using valid) remaining
        simpa only [State.rawBatches, List.append_assoc] using final
  simpa only [List.nil_append]
    using loop (events := []) (initial_uncancelledReplayFrame generated canonical)
      (createWorkQueue_cancelledRecordsReported (Work.fromExecution work) work _) batches
      valid (by rwa [← inputsStarted_eq_batchesStarted])

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
