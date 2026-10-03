import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CompleteFailureAccounting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PendingReplay

/-! Complete group error totals through accepted generated source replay. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- The actual source replay supplies full-inventory accounting, not a new premise
-----------------------------------------------------------------------------------------

/-- Accepted source replay preserves complete totals for eligible object failures.
Witness: joint induction with pending/registration accounting. `failed` is the earlier
inventory; the actual guard selects new contributions without omitting any source input.
-/
theorem State.GroupErrorAccounting.replayGraphEvents {queue : State} {work before failed}
    (counts : queue.GroupErrorAccounting work failed)
    (ledger : queue.PendingAccounting work (GraphEvent.taskSettlements before))
    (generated : ExecutedWork work) (events : List GraphEvent)
    (valid : ValidGraphEvents work (before ++ events))
    (accepted : queue.acceptsBatch events = true)
    : (queue.replayGraphEvents events).GroupErrorAccounting work
        (queue.objectFailureContributions events ++ failed) := by
  induction events generalizing queue before failed with
  | nil => simpa [State.replayGraphEvents, State.objectFailureContributions] using counts
  | cons event rest ih =>
      have initialPart : (before ++ [event]).IsPrefix (before ++ event :: rest) :=
        ⟨rest, by simp [List.append_assoc]⟩
      obtain ⟨_, matching, fresh⟩ := validGraphEvents_last (valid.prefix initialPart)
      have accepts : queue.acceptsGraphEvent event = true
          ∧ (queue.handleGraphEvent event).1.acceptsBatch rest = true := by
        simpa only [State.acceptsBatch, Bool.and_eq_true] using accepted
      have nextCounts := counts.handleGraphEvent generated ledger.liveGroups ledger.taskGroups
        ledger.started ledger.matching event matching accepts.1
      have nextLedger := ledger.handleGraphEvent generated
        (GraphEvent.taskSettlements_subsetIdentities before) event matching fresh accepts.1
      rw [← GraphEvent.taskSettlements_append] at nextLedger
      have result := ih nextCounts nextLedger
        (by simpa [List.append_assoc] using valid) accepts.2
      simpa [State.replayGraphEvents, State.objectFailureContributions, List.append_assoc]
        using result

/-- Real batch wrapping retains complete group totals, including a terminating batch.
Witness: handler replay and the control-only final termination flag.
-/
theorem State.GroupErrorAccounting.handleGraphEvents {queue : State} {work before failed}
    (counts : queue.GroupErrorAccounting work failed)
    (ledger : queue.PendingAccounting work (GraphEvent.taskSettlements before))
    (generated : ExecutedWork work) (events : List GraphEvent)
    (valid : ValidGraphEvents work (before ++ events))
    (running : queue.terminated = false) (accepted : queue.acceptsBatch events = true)
    : (queue.handleGraphEvents events).1.GroupErrorAccounting work
        (queue.objectFailureContributions events ++ failed) := by
  have accounted := counts.replayGraphEvents ledger generated events valid accepted
  unfold State.handleGraphEvents
  simp only [running, Bool.false_eq_true, ↓reduceIte]
  split <;> simpa only [State.foldGraphEvents_state, State.GroupErrorAccounting] using accounted

/-- Normalized batching preserves exact eligible-failure totals.
Witness: started batches flatten to accepted handler replay; its final state differs only
in the termination flag. Guards therefore select contributions at the same actual states.
-/
theorem State.GroupErrorAccounting.runNormalized {queue : State} {work before failed}
    (counts : queue.GroupErrorAccounting work failed)
    (ledger : queue.PendingAccounting work (GraphEvent.taskSettlements before))
    (generated : ExecutedWork work) (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work (before ++ batches.flatten))
    (started : queue.batchesStarted batches = true)
    : (queue.runNormalized batches).1.GroupErrorAccounting work
        (queue.objectFailureContributions batches.flatten ++ failed) := by
  have accounted := counts.replayGraphEvents ledger generated batches.flatten valid
    (queue.batchesStarted_acceptsBatch batches started)
  obtain ⟨terminal, same⟩ := queue.runNormalized_stateCore batches started
  rw [same]
  exact accounted

/-- Every live cache counts exactly the prior eligible object-failure inventory.
Witness: initialization and normalized replay with the executable owner guard. The same
inventory is used at every ref; no per-cache subset or output-admission premise is assumed.
-/
theorem ExecutedWork.runNormalized_groupErrorAccounting {work : Execution.Work}
    (generated : ExecutedWork work) (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    : ((State.initialize (Work.fromExecution work)).runNormalized
        batches).1.GroupErrorAccounting
        work
        ((State.initialize (Work.fromExecution work)).objectFailureContributions
          batches.flatten) := by
  simpa only [List.append_nil]
    using (createWorkQueue_groupErrorAccounting _ _).runNormalized (before := [])
      (createWorkQueue_pendingAccounting work) generated batches valid
      (by rwa [inputsStarted_eq_batchesStarted] at started)

-----------------------------------------------------------------------------------------
-- A later successful handler releases exactly the complete pre-input failure total
-----------------------------------------------------------------------------------------

/-- Complete accounting certifies each populated cache's exact full-inventory error count.
Witness: specialize the live-node clause at its stored option value.
-/
theorem State.GroupErrorAccounting.cached {queue : State} {work failed}
    (counts : queue.GroupErrorAccounting work failed)
    : queue.CachedErrorsSatisfy
        (fun ref errors => NodeErrors work failed ref errors) := by
  intro node member errors cached
  simpa only [cached, Option.getD_some] using counts.live node member

/-- Failed closures released by successful settlement count all previous object failures.
Witness: full-inventory cache accounting and the unchanged exact cache-to-output transfer.
This discharges contributor completeness for this local release, not failure-cut licensing.
-/
theorem State.GroupErrorAccounting.taskSuccess_output {queue : State} {work failed}
    (counts : queue.GroupErrorAccounting work failed) (occurrence : Occurrence)
    (result : TaskResult) {group errors}
    (emitted
      : Execution.WorkQueueEvent.groupFailure group errors
        ∈ (queue.taskSuccess occurrence result).2)
    : NodeErrors work failed group.ref errors :=
  counts.cached.taskSuccess_output occurrence result emitted

/-- Failed closures released by stream items count all previous object failures.
Witness: integration preserves complete caches and the drain reports their exact counts.
-/
theorem State.GroupErrorAccounting.streamItems_output {queue : State} {work failed}
    (counts : queue.GroupErrorAccounting work failed) (stream : Execution.DeliveryNode)
    (items : List StreamItem) {group errors}
    (emitted
      : Execution.WorkQueueEvent.groupFailure group errors
        ∈ (queue.streamItems stream items).2)
    : NodeErrors work failed group.ref errors :=
  counts.cached.streamItems_output stream items emitted

/-- A later task success reports the complete failure total derived from actual prior replay.
Witness: generated replay supplies the invariant, then exact cache transfer supplies the
emitted count. No contributor coverage premise is left to the caller for this branch.
-/
theorem ExecutedWork.runNormalized_taskSuccess_nodeErrors {work : Execution.Work}
    (generated : ExecutedWork work) (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true) (occurrence : Occurrence)
    (result : TaskResult) {group errors}
    (emitted
      : Execution.WorkQueueEvent.groupFailure group errors
        ∈ (((State.initialize (Work.fromExecution work)).runNormalized
              batches).1.taskSuccess
            occurrence result).2)
    : NodeErrors work
        ((State.initialize (Work.fromExecution work)).objectFailureContributions
          batches.flatten)
        group.ref errors :=
  (generated.runNormalized_groupErrorAccounting batches valid started).taskSuccess_output
    occurrence result emitted

/-- A later item handler reports the complete failure total derived from actual prior replay.
Witness: generated full-inventory accounting and the item handler's exact cached output.
-/
theorem ExecutedWork.runNormalized_streamItems_nodeErrors {work : Execution.Work}
    (generated : ExecutedWork work) (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true) (stream : Execution.DeliveryNode)
    (items : List StreamItem) {group errors}
    (emitted
      : Execution.WorkQueueEvent.groupFailure group errors
        ∈ (((State.initialize (Work.fromExecution work)).runNormalized
              batches).1.streamItems
            stream items).2)
    : NodeErrors work
        ((State.initialize (Work.fromExecution work)).objectFailureContributions
          batches.flatten)
        group.ref errors :=
  (generated.runNormalized_groupErrorAccounting batches valid started).streamItems_output
    stream items emitted

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
