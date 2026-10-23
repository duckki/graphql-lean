import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationClassification
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RegisteredTasks

/-! Completing the active projection of one task recovers reference registration. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue

-----------------------------------------------------------------------------------------
-- Structural provenance rules out conflicting task catalogue entries
-----------------------------------------------------------------------------------------

/-- Two matched registrations of one occurrence retain the same contributor descriptors.
Witness: both descriptor lists are the value of the same structural taskGroups? lookup.
This reuses provenance, rather than imposing a new uniqueness premise on the host.
-/
theorem matchedTasks_eq_of_occurrence_eq {work : Work}
    {first second : ReferenceWorkQueue.Task}
    (firstMatch : ReferenceWorkQueue.TaskMatches work first)
    (secondMatch : ReferenceWorkQueue.TaskMatches work second)
    (same : first.occurrence = second.occurrence)
    : first = second := by
  have groups : first.groups = second.groups := by
    apply Option.some.inj
    rw [← firstMatch.2, same, secondMatch.2]
  cases first
  cases second
  cases same
  cases groups
  rfl

/-- New registration preserves the reference catalogue provenance invariant.
Witness: provenance sees only the permanent catalogue, which the projection preserves.
-/
theorem State.addTask_registeredTasksMatch {state : State} {work : Work}
    (matching : state.queue.RegisteredTasksMatch work) (task : ReferenceWorkQueue.Task)
    (known : ReferenceWorkQueue.TaskMatches work task)
    : (state.addTask task).1.queue.RegisteredTasksMatch work := by
  change (registrationCore (state.addTask task).1.queue).RegisteredTasksMatch work
  rw [state.addTask_registrationCore task]
  exact matching.addTask task known

/-- Occurrence lookup recovers the exact task, even if its catalogue entry is repeated.
Witness: structural matching fixes contributors at that occurrence; no whole-list NoDup
assumption is required. This is the lookup used by delayed startTask.
-/
theorem registeredTask_lookup {queue : ReferenceWorkQueue.State} {work : Work}
    (matching : queue.RegisteredTasksMatch work) {task : ReferenceWorkQueue.Task}
    (member : task ∈ queue.tasks)
    : queue.task? task.occurrence = some task := by
  cases found : queue.task? task.occurrence with
  | none =>
      have excluded := List.find?_eq_none.mp found task member
      exact (excluded ((ReferenceWorkQueue.occurrence_beq_iff_eq _ _).mpr rfl)).elim
  | some other =>
      have present := List.mem_of_find?_eq_some found
      have same := (ReferenceWorkQueue.occurrence_beq_iff_eq _ _).mp
        (List.find?_some (p := fun candidate : ReferenceWorkQueue.Task =>
          candidate.occurrence == task.occurrence) found)
      exact congrArg some
        (matchedTasks_eq_of_occurrence_eq (matching other present) (matching task member) same)

-----------------------------------------------------------------------------------------
-- Single-task registration followed by its active completion
-----------------------------------------------------------------------------------------

/-- Delayed activation of the returned active task has the reference registration effect.
Witness: live-root classification, exact catalogue lookup from existing provenance, and
the shared membership fold. RegistrationTaskReplay composes settlement and replay.
-/
theorem State.addTask_complete_eq_reference {state : State} {work : Work}
    (present : state.queue.RootGroupsPresent)
    (matching : state.queue.RegisteredTasksMatch work) (task : ReferenceWorkQueue.Task)
    (known : ReferenceWorkQueue.TaskMatches work task)
    : (if (state.addTask task).2 = .active then
          (state.addTask task).1.queue.startTask task.occurrence
        else
          (state.addTask task).1.queue)
      = state.queue.addTask task := by
  have registered := state.addTask_registeredTasksMatch matching task known
  have member : task ∈ (state.addTask task).1.queue.tasks := by
    rw [state.addTask_tasks task]
    simp
  have lookup := registeredTask_lookup registered member
  have reference : state.queue.addTask task =
      if task.groups.any (fun group => (state.addTask task).1.queue.rootGroups.contains group.ref)
          && ((state.addTask task).1.queue.taskNode? task.occurrence).isNone then
        { (state.addTask task).1.queue with
          taskNodes := (state.addTask task).1.queue.taskNodes ++ [{ task }] }
      else (state.addTask task).1.queue := by
    rw [state.addTask_ownerState task]
    rfl
  rw [reference, state.addTask_rootGroups task]
  by_cases active : (state.addTask task).2 = .active
  · have selected := (state.addTask_active_iff task present).mp active
    simp only [active, ↓reduceIte, selected, Bool.true_and, ReferenceWorkQueue.State.startTask]
    cases node : (state.addTask task).1.queue.taskNode? task.occurrence with
    | none => simp only [Option.isSome_none, Option.isNone_none, Bool.false_eq_true,
        ↓reduceIte, lookup, List.findSome?]
    | some found => simp only [Option.isSome_some, Option.isNone_some, ↓reduceIte,
        Bool.false_eq_true]
  · have unselected : task.groups.any (fun group => state.queue.rootGroups.contains group.ref)
        = false := by
      cases selected
            : task.groups.any
                (fun group => state.queue.rootGroups.contains group.ref) with
      | false => rfl
      | true => exact (active ((state.addTask_active_iff task present).mpr selected)).elim
    simp only [active, ↓reduceIte, unselected, Bool.false_and, Bool.false_eq_true]

end GraphQL.IncrementalDelivery.AlternativeWorkQueue
