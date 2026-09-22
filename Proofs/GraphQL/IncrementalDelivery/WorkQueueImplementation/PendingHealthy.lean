import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.HealthyCounterReplay

/-! Relating all-outcome counters to the success-only healthy-group ledger. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- A healthy live group's memberships contain no source-failed task.
Witness: sound membership identifies a registered contributor; source provenance rules
out its recorded failure under the healthy-owner guard.
-/
theorem State.PendingAccounting.healthyMembership_not_failed
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (accounted : queue.PendingAccounting work settled)
    {node : GroupNode} (member : node ∈ queue.groupNodes)
    (healthy : ¬GroupInvalidated work failed node.group.node.key)
    {occurrence : Occurrence} (taskMember : occurrence ∈ node.tasks)
    : occurrence ∉ failed :=
  accounted.sound.healthyMembership_not_failed accounted.matching member healthy
    taskMember

/-- Exact healthy all-outcome counters imply the success-only healthy-group equation.
Witness: failed settlements never occur in a healthy group's task list, so both filters
count exactly the same unsettled memberships. Healthy exactness is supplied separately;
it is not inferred from the accounting record's all-group lower bound.
-/
theorem State.PendingAccounting.healthyPendingTracks
    {queue : State} {work : Execution.Work} {events : List GraphEvent}
    (accounted : queue.PendingAccounting work (GraphEvent.taskSettlements events))
    (tracks
      : queue.HealthyPendingTracks work (GraphEvent.taskSettlements events)
          (GraphEvent.failureSettlements events))
    : queue.HealthyPendingTracks work (GraphEvent.groupSettlements events)
        (GraphEvent.failureSettlements events) := by
  classical
  intro node member healthy
  change node.pending = _
  rw [tracks node member healthy]
  unfold unsettledCount
  congr 1
  apply List.filter_congr
  intro occurrence taskMember
  have notFailed := accounted.healthyMembership_not_failed member healthy taskMember
  simp only [GraphEvent.mem_taskSettlements, notFailed, or_false]

/-- All-owner registered-task links imply the older healthy started-task links.
Witness: a not-yet-successful task with a healthy contributor cannot be a recorded failure,
so it remains unsettled in the combined ledger and retains its contributor membership.
-/
theorem State.PendingAccounting.healthyTaskLinks
    {queue : State} {work : Execution.Work} {events : List GraphEvent}
    (accounted : queue.PendingAccounting work (GraphEvent.taskSettlements events))
    : queue.HealthyTaskLinks work (GraphEvent.groupSettlements events)
        (GraphEvent.failureSettlements events) := by
  intro task member unsettled node nodeMember healthy contributor
  have registered := accounted.started task member
  have notFailed := (accounted.matching task.task registered).not_failed_of_healthy
    contributor healthy
  have unprocessed : task.task.occurrence ∉ GraphEvent.taskSettlements events := by
    simp only [GraphEvent.mem_taskSettlements, unsettled, notFailed, or_self, not_false_eq_true]
  exact accounted.links task.task registered unprocessed node nodeMember contributor

/-- Valid started generated replay recovers both healthy pending counts and task links.
Witness: cancellation-aware healthy-counter replay, then the success/failure ledger bridges.
No root-health, output-admission, or healthy-owner-existence premise is required.
-/
theorem ExecutedWork.runNormalized_healthyPendingAndLinks {work : Execution.Work}
    (generated : ExecutedWork work) (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    : let queue := ((State.initialize (Work.fromExecution work)).runNormalized batches).1
      queue.HealthyPendingTracks work (GraphEvent.groupSettlements batches.flatten)
        (GraphEvent.failureSettlements batches.flatten)
      ∧ queue.HealthyTaskLinks work (GraphEvent.groupSettlements batches.flatten)
          (GraphEvent.failureSettlements batches.flatten) := by
  obtain ⟨_, accounted⟩ := generated.runNormalized_healthyCounterLedger batches valid started
  exact ⟨accounted.pending.healthyPendingTracks accounted.healthy,
    accounted.pending.healthyTaskLinks⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
