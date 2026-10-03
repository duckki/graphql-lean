import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PendingDebt
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.HealthyEligibility

/-! Safe pending bounds and healthy exact counters after an ignored settlement. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- All live groups keep the safety bound needed by zero-counter draining
-----------------------------------------------------------------------------------------

/-- Enlarging the settled ledger preserves every selected group's pending lower bound.
Witness: additional settlement tokens only reduce the unsettled-membership count.
-/
theorem State.PendingBound.weakenSettled {queue : State} {eligible before after}
    (bounded : queue.PendingBound eligible before) (included : before.Subset after)
    : queue.PendingBound eligible after := by
  intro node member relevant
  exact Nat.le_trans (unsettledCount_antitone node.tasks included)
    (bounded node member relevant)

/-- Removing an ignored task preserves the lower bound without decrementing counters.
Witness: first record the settlement in the proof ledger, then remove its membership.
The pending counter may overcount in failed groups, but cannot undercount live work.
-/
theorem State.PendingBound.ignoreTask {queue : State} {eligible settled}
    (bounded : queue.PendingBound eligible settled) (occurrence : Occurrence)
    : (queue.removeTask occurrence).PendingBound eligible (occurrence :: settled) :=
  (bounded.weakenSettled
    (by intro task member; exact List.mem_cons_of_mem _ member)).removeTask
    occurrence (by simp)

/-- A rejected success preserves the pending lower bound and adds no child counters.
Witness: the executable guard reduces the whole handler to ignored-task cleanup.
-/
theorem State.PendingBound.taskSuccess_of_noHealthyOwner {queue : State}
    {eligible settled} (bounded : queue.PendingBound eligible settled) {occurrence node}
    (found : queue.taskNode? occurrence = some node)
    (inactive : queue.taskHasHealthyOwner node.task = false) (result : TaskResult)
    : (queue.taskSuccess occurrence result).1.PendingBound eligible
        (occurrence :: settled) := by
  rw [State.taskSuccess_of_noHealthyOwner found inactive result]
  exact bounded.ignoreTask occurrence

/-- A rejected failure preserves the same bound while retaining previous error records.
Witness: the failure guard also selects ignored-task cleanup before any owner update.
-/
theorem State.PendingBound.taskFailure_of_noHealthyOwner {queue : State}
    {eligible settled} (bounded : queue.PendingBound eligible settled) {occurrence node}
    (found : queue.taskNode? occurrence = some node)
    (inactive : queue.taskHasHealthyOwner node.task = false) (errors : Nat)
    : (queue.taskFailure occurrence errors).1.PendingBound eligible
        (occurrence :: settled) := by
  rw [State.taskFailure_of_noHealthyOwner found inactive errors]
  exact bounded.ignoreTask occurrence

-----------------------------------------------------------------------------------------
-- Healthy groups still have exact counters
-----------------------------------------------------------------------------------------

/-- Ignoring a task absent from every healthy group preserves their exact counters.
Witness: neither removing nor recording an absent occurrence changes the group's count.
Failed-group counters need only the bound above, not an incorrect exactness assertion.
-/
theorem State.HealthyPendingTracks.ignoreTask {queue : State} {work settled failed}
    (tracks : queue.HealthyPendingTracks work settled failed) (occurrence : Occurrence)
    (absent
      : ∀ node ∈ queue.groupNodes,
          ¬GroupInvalidated work failed node.group.node.ref → occurrence ∉ node.tasks)
    : (queue.removeTask occurrence).HealthyPendingTracks work (occurrence :: settled)
        failed := by
  intro node member healthy
  obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
  change old.pending = unsettledCount (old.tasks.filter (· != occurrence)) (occurrence :: settled)
  rw [unsettledCount_remove_settled _ _ _ (by simp),
    unsettledCount_settle_absent _ _ _ (absent old oldMember healthy)]
  exact tracks old oldMember healthy

/-- A rejected success preserves exact healthy counters under the existing metadata facts.
Witness: causal health makes each healthy group's membership exclude the ignored task;
the handler only removes that task and does not integrate its supplied child work.
-/
theorem State.HealthyPendingTracks.taskSuccess_of_noHealthyOwner {queue : State}
    {work settled failed} (tracks : queue.HealthyPendingTracks work settled failed)
    (sound : queue.GroupMembershipSound) (registered : queue.StartedTasksRegistered)
    (matching : queue.RegisteredTasksMatch work)
    (supported : queue.CachedFailuresSupported work failed)
    (cancelled : queue.CancelledRecordsSupported work failed)
    (generated : ExecutedWork work)
    (descriptors
      : ∀ node ∈ queue.groupNodes,
          ∃ dependencies,
            GroupRecordAt work node.group.node dependencies
            ∧ node.group.parent = dependencies.head?)
    {occurrence node} (found : queue.taskNode? occurrence = some node)
    (inactive : queue.taskHasHealthyOwner node.task = false) (result : TaskResult)
    : (queue.taskSuccess occurrence result).1.HealthyPendingTracks
        work (occurrence :: settled) failed := by
  rw [State.taskSuccess_of_noHealthyOwner found inactive result]
  apply tracks.ignoreTask occurrence
  intro owner member healthy
  have absent := sound.rejectedTask_absentFromHealthy registered matching supported cancelled
    generated descriptors (List.mem_of_find?_eq_some found) inactive member healthy
  have same : node.task.occurrence = occurrence := (occurrence_beq_iff_eq _ _).mp
    (List.find?_some (p := fun node : TaskNode => node.task.occurrence == occurrence) found)
  simpa only [same] using absent

/-- A rejected failure preserves exact healthy counters before extending the failure ledger.
Witness: the same membership exclusion and cancellation-only handler equation. The
separate invalidation-equivalence theorem justifies recording the ignored source token
for health reasoning without counting it as a new error contribution.
-/
theorem State.HealthyPendingTracks.taskFailure_of_noHealthyOwner {queue : State}
    {work settled failed} (tracks : queue.HealthyPendingTracks work settled failed)
    (sound : queue.GroupMembershipSound) (registered : queue.StartedTasksRegistered)
    (matching : queue.RegisteredTasksMatch work)
    (supported : queue.CachedFailuresSupported work failed)
    (cancelled : queue.CancelledRecordsSupported work failed)
    (generated : ExecutedWork work)
    (descriptors
      : ∀ node ∈ queue.groupNodes,
          ∃ dependencies,
            GroupRecordAt work node.group.node dependencies
            ∧ node.group.parent = dependencies.head?)
    {occurrence node} (found : queue.taskNode? occurrence = some node)
    (inactive : queue.taskHasHealthyOwner node.task = false) (errors : Nat)
    : (queue.taskFailure occurrence errors).1.HealthyPendingTracks
        work (occurrence :: settled) failed := by
  rw [State.taskFailure_of_noHealthyOwner found inactive errors]
  apply tracks.ignoreTask occurrence
  intro owner member healthy
  have absent := sound.rejectedTask_absentFromHealthy registered matching supported cancelled
    generated descriptors (List.mem_of_find?_eq_some found) inactive member healthy
  have same : node.task.occurrence = occurrence := (occurrence_beq_iff_eq _ _).mp
    (List.find?_some (p := fun node : TaskNode => node.task.occurrence == occurrence) found)
  simpa only [same] using absent

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
