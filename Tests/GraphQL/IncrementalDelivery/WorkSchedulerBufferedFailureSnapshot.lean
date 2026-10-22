import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.BatchCallbackWorkLaws
import Tests.GraphQL.IncrementalDelivery.Execution
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureProjection
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ActiveRejectionReplay

/-! Removing a stale callback changes the earlier batch-wide cached-error snapshot. -/

namespace GraphQL.IncrementalDelivery.Tests.WorkSchedulerBufferedFailureSnapshot
open GraphQL.IncrementalDelivery
open GraphQL.IncrementalDelivery.Execution
open ReferenceWorkQueue WorkQueueSemantics

private def r : DeliveryNode := ⟨0, [], some (.string "R")⟩
private def p : DeliveryNode := ⟨1, [], some (.string "P")⟩
private def x : DeliveryNode := ⟨2, [], some (.string "X")⟩
private def y : DeliveryNode := ⟨3, [], some (.string "Y")⟩
private def aTask : Occurrence := .executionGroup [1, 0]
private def bTask : Occurrence := .executionGroup [1, 1, 0]
private def pTask : Occurrence := .executionGroup [1, 1, 1, 0]

private def pValue : ExecutionGroupValue :=
  { path := [], data := [("c", .scalar "c")], errors := 0, deliveryGroups := [p] }

private def work : Execution.Work :=
  .combine .empty
    (.declareGroups [⟨r, []⟩, ⟨p, []⟩, ⟨x, [p]⟩, ⟨y, [p]⟩]
      (.combine
        (.executionGroup [⟨r, []⟩, ⟨x, [p]⟩] [] { result := .error 1, cause := some 1 }
          .empty)
        (.combine
          (.executionGroup [⟨r, []⟩, ⟨x, [p]⟩, ⟨y, [p]⟩] []
            { result := .error 1, cause := some 1 } .empty)
          (.combine
            (.executionGroup [⟨p, []⟩] [] { result := .ok (pValue.data, 0) }
              (.combine .empty .empty))
            .empty))))

theorem generated : ExecutedWork work := by
  refine ⟨Nat, schema, resolvers, [], 50, "Query", .object "Query" 0,
    [defer [field "required" [] [] (some "a"), field "required" [] [] (some "b")] (some "R"),
     defer [field "c",
       defer [field "required" [] [] (some "a"), field "required" [] [] (some "b")] (some "X"),
       defer [field "required" [] [] (some "b")] (some "Y")] (some "P")], ?_⟩
  cbv

private def initial : ReferenceWorkQueue.State :=
  .initialize (ReferenceWorkQueue.Work.fromExecution work)

private def finish : GraphEvent := .taskSuccess pTask ⟨pValue, {}⟩

private def batch : List GraphEvent :=
  [finish, .taskFailure bTask 1, .taskFailure aTask 1]

/-- The former eventwise filter drops A after B has removed their last live owners. -/
private def reduced : List GraphEvent := [finish, .taskFailure bTask 1]

private def failureCounts (events : List WorkQueueEvent) : List (Nat × Nat) :=
  events.filterMap
    fun event =>
      match event with
      | .groupFailure group count => some (group.ref, count)
      | _ => none

/-- Both task failures match distinct generated computations; all producers are absent. -/
theorem raw_work_valid : ValidGraphEvents work batch := by
  have aKnown : TaskAt work aTask [r.ref, x.ref] none (.object [] (.error 1)) :=
    ⟨[⟨r, []⟩, ⟨x, [p]⟩], [], { result := .error 1, cause := some 1 }, .empty, [],
      rfl, rfl, rfl⟩
  have bKnown : TaskAt work bTask [r.ref, x.ref, y.ref] none (.object [] (.error 1)) :=
    ⟨[⟨r, []⟩, ⟨x, [p]⟩, ⟨y, [p]⟩], [], { result := .error 1, cause := some 1 }, .empty, [],
      rfl, rfl, rfl⟩
  have pKnown : TaskAt work pTask [p.ref] none (.object [] (.ok (pValue.data, 0))) :=
    ⟨[⟨p, []⟩], [], { result := .ok (pValue.data, 0) }, .combine .empty .empty, [],
      rfl, rfl, rfl⟩
  have one : ValidGraphEvents work [finish] :=
    .append .nil ⟨_, _, pKnown, rfl, rfl⟩
      (by simp [finish, GraphEvent.Fresh, GraphEvent.identities])
      ⟨_, _, _, pKnown, by intro source impossible; cases impossible⟩
  have two : ValidGraphEvents work [finish, .taskFailure bTask 1] :=
    .append one ⟨_, _, _, bKnown⟩
      (by simp [finish, GraphEvent.Fresh, GraphEvent.identities, bTask, pTask])
      ⟨_, _, _, bKnown, by intro source impossible; cases impossible⟩
  exact .append two ⟨_, _, _, aKnown⟩
    (by simp [finish, GraphEvent.Fresh, GraphEvent.identities, aTask, bTask, pTask])
    ⟨_, _, _, aKnown, by intro source impossible; cases impossible⟩

/-- Every callback can already be enqueued at the original host boundary. -/
theorem all_enqueued_tasks_started : batch.all initial.acceptsGraphEvent = true := by cbv

/-- Cached startup removes X before notification B; B then removes R and retires A. -/
theorem last_notification_stale
    : let available := GraphEvent.availableFailures batch
      let released := (initial.handleGraphEvent finish available).1
      let failed := (released.handleGraphEvent (.taskFailure bTask 1) available).1
      failed.acceptsGraphEvent (.taskFailure aTask 1) = false := by cbv

/-- Initial eligibility admits the complete batch even when its final task has retired. -/
theorem original_batch_admitted : initial.acceptsBatch batch = true := by cbv

/-- Matching, freshness, producer order and batch start discipline hold together. -/
theorem original_source_discipline
    : ValidGraphEvents work batch ∧ inputsStarted work [batch] = true :=
  ⟨raw_work_valid, by cbv⟩

/-- The reduced batch is also admissible, but changes X's collected diagnostics. -/
theorem reduced_batch_admitted : initial.acceptsBatch reduced = true := by cbv

/-- A task retired before a later batch gains no permission from historical starts. -/
theorem retired_before_batch_not_admitted
    : (initial.handleGraphEvents batch).1.acceptsBatch [.taskFailure aTask 1]
      = false := by
  cbv

/-- A callback for work that has never started remains inadmissible. -/
theorem unstarted_task_not_admitted
    : initial.acceptsBatch [.taskFailure (.executionGroup [99]) 1] = false := by cbv

/-- Live notification consumption omits A after its last owner retires. -/
theorem guard_failure_inventory_omits_retired_task
    : initial.objectFailureContributionsForBatches [batch] = [bTask] := by cbv

/-- Source admission retains both cached causes even when A's notification is stale. -/
theorem admitted_failure_inventory_retains_cached_task
    : initial.admittedObjectFailureContributionsForBatches [batch] = [aTask, bTask] := by
  cbv

/-- The general batch theorem clears active rejection caches even with stale A. -/
theorem batch_end_has_no_active_cached_failure
    : (initial.runNormalized [batch]).1.NoActiveCachedFailure :=
  createWorkQueue_runNormalized_noActiveCachedFailure generated [batch]
    (by simpa using raw_work_valid) original_source_discipline.2

private def dispatched : List GraphEvent :=
  batch ++ [.groupFailure ⟨x, 2⟩, .groupFailure ⟨y, 1⟩]

private def reducedDispatched : List GraphEvent :=
  reduced ++ [.groupFailure ⟨x, 1⟩, .groupFailure ⟨y, 1⟩]

/-- X sees both task causes before B's FIFO notification consumes either failure. -/
theorem original_failure_counts
    : failureCounts (initial.handleGraphEvents dispatched).2
      = [(0, 1), (2, 2), (3, 1)] := by
  cbv

/-- Filtering A out of the host batch loses one of X's available causes. -/
theorem reduced_failure_counts
    : failureCounts (initial.handleGraphEvents reducedDispatched).2
      = [(0, 1), (2, 1), (3, 1)] := by
  cbv

/-- Filtering changes the work-event output, even though all source values match. -/
theorem filtering_changes_output
    : (initial.handleGraphEvents dispatched).2
      ≠ (initial.handleGraphEvents reducedDispatched).2 := by
  intro same
  have counts := congrArg failureCounts same
  rw [original_failure_counts, reduced_failure_counts] at counts
  cases counts

/-- Publisher normalization retains the observable difference in collected diagnostics. -/
theorem normalized_failure_counts
    : failureCounts (initial.runNormalized [dispatched]).2.flatten
        = [(0, 1), (2, 2), (3, 1)]
      ∧ failureCounts (initial.runNormalized [reducedDispatched]).2.flatten
        = [(0, 1), (2, 1), (3, 1)] := by
  constructor <;> cbv

/-- Retirement at batch entry is stronger than stale notification consumption within it. -/
theorem initially_available_failure_not_retired : ¬initial.RetiredTask aTask := by
  intro retired
  have missing := retired.missing
  cbv at missing
  cases missing

private def earlierBatch := [finish, .taskFailure bTask 1]

private def retiredBoundary :=
  initial.replayGraphEvents earlierBatch (GraphEvent.availableFailures earlierBatch)

private theorem retiredBoundary_groups : retiredBoundary.groupNodes = [] := by cbv
private theorem retiredBoundary_missing : retiredBoundary.taskNode? aTask = none := by cbv

/-- In a later host batch A is globally retired; removing its callback preserves even
terminal output. The earlier multi-cause batch counterexample remains unchanged.
-/
theorem later_retired_callback_can_be_removed
    : let earlier := [finish, .taskFailure bTask 1]
      let queue :=
        initial.replayGraphEvents earlier (GraphEvent.availableFailures earlier)
      queue.handleGraphEvents [.taskFailure aTask 1] = queue.handleGraphEvents [] := by
  let earlier := earlierBatch
  let queue := retiredBoundary
  have gone : queue.groupNodes = [] := retiredBoundary_groups
  have missing : queue.taskNode? aTask = none := retiredBoundary_missing
  have retired : queue.RetiredTask aTask := ⟨missing, fun node member => by
    rw [gone] at member
    cases member⟩
  have equality :=
    queue.handleGraphEvents_filterRetired
      (work := work)
      (before := earlier)
      (retainedBefore := earlier)
      [.taskFailure aTask 1]
      (fun _ => false)
      [aTask]
      ((createWorkQueue_taskNodeKeysUnique _).replayGraphEvents earlier
        (GraphEvent.availableFailures earlier))
      (by
        intro occurrence member; simp only [List.mem_singleton] at member; exact member ▸ retired)
      (by
        intro event member discarded
        simp only [List.mem_singleton] at member
        subst event
        exact ⟨aTask, by simp, rfl⟩)
      (by
        intro occurrence member event received task listed
        simp only [List.mem_singleton] at received
        subst event
        cases listed)
      raw_work_valid
      (by
        simpa only [List.filter_cons, Bool.false_eq_true, ↓reduceIte, List.filter_nil,
          List.append_nil]
          using (raw_work_valid.prefix (before := earlier) ⟨[.taskFailure aTask 1], rfl⟩))
  exact equality.symm

/-- Entry-based projection keeps A's available cause despite its stale later notification. -/
theorem entry_projection_keeps_cached_causes
    : AlternativeWorkQueue.NativeRefinement.BufferedCallbacks.projectBatchAtEntry initial
        batch
      = batch := by cbv

/-- The replacement projector preserves the full aggregate X=2 diagnostic report. -/
theorem entry_projection_preserves_failure_counts
    : failureCounts
        (initial.handleGraphEvents
          (AlternativeWorkQueue.NativeRefinement.BufferedCallbacks.projectBatchAtEntry
              initial batch
            ++ [.groupFailure ⟨x, 2⟩, .groupFailure ⟨y, 1⟩])).2
      = [(0, 1), (2, 2), (3, 1)] := by
  rw [entry_projection_keeps_cached_causes]
  exact original_failure_counts

#print axioms State.handleGraphEvents_filterRetired

end GraphQL.IncrementalDelivery.Tests.WorkSchedulerBufferedFailureSnapshot
