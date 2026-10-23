import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupRawBatches
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialStartupSourceFrames
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialStartupBatchShape
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NormalizedFailureReports

/-! Startup cancellation markers retain actual positive reports through first-batch forwarding. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Initial cancellation is explained by the local notices returned from synchronous startup.
These reports are proof evidence awaiting first-batch forwarding, not extra queue state.
-/
theorem ExecutedWork.initialStartup_cancelledRecordsReported {work}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (matched : startup.MatchesWork work)
    : let initial := State.initialize (Work.fromExecution work) startup
      initial.CancelledRecordsReported work
        (initial.groupFailureEvents.map
          (fun failure => .groupFailure failure.group failure.errors)) := by
  have empty : (initialPreparation work).1.CancelledRecordsReported work [] := by
    intro node dependencies known cancelled
    rw [initialPreparation_cancelledGroups_empty] at cancelled
    cases cancelled
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have frame := initialPreparation_parentCutFrame generated canonical
  have noneRejected : ({} : State).TaskRejectionsSatisfy (fun _ errors => 0 < errors) := by
    intro task impossible; cases impossible
  have positive := (noneRejected.maybeIntegrateWork (Work.fromExecution work)).pruneEmptyGroups
    (({} : State).maybeIntegrateWork (Work.fromExecution work)).2.newGroups
  have reports := empty.startNewWork generated frame.records frame.links canonical positive
    (initialPreparation work).2 startup.failures (fun occurrence errors member =>
      generated.matchedTaskFailure_positive (matched.2 occurrence errors member).1)
  unfold State.initialize
  simpa only [List.nil_append, State.CancelledRecordsReported, initialPreparation,
    State.enqueueGroupFailures, State.startNewWork_groupFailureEvents,
    State.pruneEmptyGroups_groupFailureEvents,
    State.maybeIntegrateWork_groupFailureEvents]
    using reports

/-- A supplied report inventory follows source-valid ordinary host-batch replay.
This generic proof also accepts initial local reports before their actual forwarding.
-/
theorem UncancelledReplayFrame.rawBatches_fifoCancelledRecordsReported
    {queue work parents before events}
    (frame : UncancelledReplayFrame queue work parents before)
    (reported : queue.FifoCancelledRecordsReported work events)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work (before ++ batches.flatten))
    (started : queue.batchesStarted batches = true)
    : (queue.rawBatches batches).1.FifoCancelledRecordsReported work
        (events ++ (queue.rawBatches batches).2) := by
  induction batches generalizing queue before events with
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

/-- Startup replay retains each cancellation explanation as emitted or still pending.
The completion-only projection is established after the terminal FIFO guard. -/
theorem ExecutedWork.startup_rawBatches_cancelledRecordsReported {work inputs}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (matched : startup.MatchesWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    : let initial := State.initialize (Work.fromExecution work) startup
      (initial.rawBatches inputs).1.FifoCancelledRecordsReported work
        (initial.rawBatches inputs).2 := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have reported : (State.initialize (Work.fromExecution work) startup).FifoCancelledRecordsReported work [] := by
    simpa only [State.FifoCancelledRecordsReported, State.pendingFailureOutputs,
      List.nil_append]
      using generated.initialStartup_cancelledRecordsReported startup matched
  simpa only [List.nil_append]
    using (generated.initialStartup_uncancelledReplayFrame canonical startup
            matched).rawBatches_fifoCancelledRecordsReported
      reported generated canonical inputs valid
      (by rwa [← inputsStartedWithStartup_eq_batchesStarted])

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
