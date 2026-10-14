import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationProjection
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationActivation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TerminationShape

/-! Exact startup correspondence, before the high-risk live-registration bridge. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics (Occurrence)

-----------------------------------------------------------------------------------------
-- Registration before any previously active roots
-----------------------------------------------------------------------------------------

/-- Registration never changes the graph-reader interruption guard. -/
theorem State.addTask_stopped (state : State) (task : ReferenceWorkQueue.Task)
    : (state.addTask task).1.stopped = state.stopped :=
  rfl

/-- The registration-only scope fold preserves the interruption guard. -/
theorem State.maybeIntegrateWork_stopped (state : State) (work : ReferenceWorkQueue.Work)
    (parent : Option Occurrence := none)
    : (state.maybeIntegrateWork work parent).1.stopped = state.stopped := by
  let step (acc : State × List ReferenceWorkQueue.Task × List ReferenceWorkQueue.Task)
      (task : ReferenceWorkQueue.Task)
      : State × List ReferenceWorkQueue.Task × List ReferenceWorkQueue.Task :=
    let next := acc.1.addTask task
    match next.2 with
    | .active => (next.1, acc.2.1 ++ [task], acc.2.2)
    | .registered => (next.1, acc.2.1, acc.2.2)
    | .rejected => (next.1, acc.2.1, acc.2.2 ++ [task])
  have next (acc : State × List ReferenceWorkQueue.Task × List ReferenceWorkQueue.Task)
      (task : ReferenceWorkQueue.Task) : (step acc task).1.stopped = acc.1.stopped := by
    unfold step
    dsimp only
    split <;> exact acc.1.addTask_stopped task
  have loop (tasks : List ReferenceWorkQueue.Task)
      (acc : State × List ReferenceWorkQueue.Task × List ReferenceWorkQueue.Task)
      : (tasks.foldl step acc).1.stopped = acc.1.stopped := by
    induction tasks generalizing acc with
    | nil => rfl
    | cons task rest ih => rw [List.foldl_cons, ih, next]
  exact loop work.tasks
    ({ state with queue := (state.queue.addGroups work.groups).1 }, [], [])

/-- Initial-scope registration has the complete reference state and release lists.
Witness: every task uses the no-active-root correspondence; stream registration is then
literally the shared operation on equal states. The rejected projection need not be empty.
-/
theorem State.maybeIntegrateWork_eq_reference_of_no_roots (state : State)
    (work : ReferenceWorkQueue.Work) (empty : state.queue.rootGroups = [])
    (parent : Option Occurrence := none)
    : let alternative := state.maybeIntegrateWork work parent
      let reference := state.queue.maybeIntegrateWork work parent
      alternative.1.queue = reference.1
      ∧ alternative.2.newWork = reference.2
      ∧ alternative.2.activeTasks = [] := by
  let step (acc : State × List ReferenceWorkQueue.Task × List ReferenceWorkQueue.Task)
      (task : ReferenceWorkQueue.Task)
      : State × List ReferenceWorkQueue.Task × List ReferenceWorkQueue.Task :=
    let next := acc.1.addTask task
    match next.2 with
    | .active => (next.1, acc.2.1 ++ [task], acc.2.2)
    | .registered => (next.1, acc.2.1, acc.2.2)
    | .rejected => (next.1, acc.2.1, acc.2.2 ++ [task])
  have loop (tasks : List ReferenceWorkQueue.Task)
      (acc : State × List ReferenceWorkQueue.Task × List ReferenceWorkQueue.Task)
      (roots : acc.1.queue.rootGroups = []) (inactive : acc.2.1 = [])
      : (tasks.foldl step acc).1.queue
          = tasks.foldl ReferenceWorkQueue.State.addTask acc.1.queue
        ∧ (tasks.foldl step acc).2.1 = [] := by
    induction tasks generalizing acc with
    | nil => exact ⟨rfl, inactive⟩
    | cons task rest ih =>
        have notActive := acc.1.addTask_not_active_of_no_roots task roots
        have same := acc.1.addTask_eq_reference_of_no_roots task roots
        have nextRoots := (acc.1.addTask_rootGroups task).trans roots
        cases disposition : (acc.1.addTask task).2 with
        | active => exact (notActive disposition).elim
        | registered =>
            have more := ih ((acc.1.addTask task).1, acc.2.1, acc.2.2) nextRoots inactive
            simpa only [List.foldl_cons, step, disposition, same] using more
        | rejected =>
            have more := ih ((acc.1.addTask task).1, acc.2.1, acc.2.2 ++ [task]) nextRoots inactive
            simpa only [List.foldl_cons, step, disposition, same] using more
  let registered := (state.queue.addGroups work.groups).1
  let initial : State × List ReferenceWorkQueue.Task × List ReferenceWorkQueue.Task :=
    ({ state with queue := registered }, [], [])
  obtain ⟨same, inactive⟩ := loop work.tasks initial
    ((ReferenceWorkQueue.State.addGroups_rootGroups state.queue work.groups).trans empty) rfl
  change ((work.tasks.foldl step initial).1.queue.addStreams work.streams parent).1 =
      ((work.tasks.foldl ReferenceWorkQueue.State.addTask registered).addStreams work.streams parent).1
    ∧ ({ newGroups := (state.queue.addGroups work.groups).2,
          newStreams := ((work.tasks.foldl step initial).1.queue.addStreams work.streams parent).2 }
          : ReferenceWorkQueue.NewWork)
        = ⟨(state.queue.addGroups work.groups).2,
            ((work.tasks.foldl ReferenceWorkQueue.State.addTask registered).addStreams
              work.streams parent).2⟩
    ∧ (work.tasks.foldl step initial).2.1 = []
  rw [same]
  exact ⟨rfl, rfl, inactive⟩

-----------------------------------------------------------------------------------------
-- Complete initialization projects to the reference state
-----------------------------------------------------------------------------------------

/-- Both implementations construct exactly the same initial accounting kernel.
Witness: root-free registration has no active task projection, then source-first release
activation commutes with the shared group starts. Host disposal observations are separate.
-/
theorem State.initialize_queue (work : Work)
    : (State.initialize work).queue
      = ReferenceWorkQueue.State.initialize
          (ReferenceWorkQueue.Work.fromExecution work) := by
  let initial : State := { queue := {} }
  let lowered := ReferenceWorkQueue.Work.fromExecution work
  obtain ⟨same, roots, inactive⟩ := initial.maybeIntegrateWork_eq_reference_of_no_roots
    lowered rfl
  have sameGroups := congrArg ReferenceWorkQueue.NewWork.newGroups roots
  have sameStreams := congrArg ReferenceWorkQueue.NewWork.newStreams roots
  have running := initial.maybeIntegrateWork_stopped lowered
  let integrated := initial.maybeIntegrateWork lowered
  let pruned := integrated.1.queue.pruneEmptyGroups integrated.2.newGroups
  let ready : State := { integrated.1 with queue := pruned.1 }
  let released : ReferenceWorkQueue.NewWork :=
    { integrated.2.newWork with newGroups := pruned.2 }
  have readyRunning : ready.stopped = false := running
  have started := ready.startNewWork_queue_of_no_active released integrated.2 []
    readyRunning inactive
  unfold State.initialize
  dsimp only
  rw [started]
  simp only [IntegratedWork.newWork] at sameGroups sameStreams
  dsimp only [initial, lowered] at same sameGroups sameStreams
  dsimp only [ready, released, pruned, integrated, initial, lowered, IntegratedWork.newWork]
  simp only [same, sameGroups, sameStreams, ReferenceWorkQueue.State.initialize]

/-- Initial construction has not interrupted or retired the graph reader.
Witness: registration and activation both preserve the initially false guard.
-/
theorem State.initialize_stopped (work : Work)
    : (State.initialize work).stopped = false := by
  unfold State.initialize
  dsimp only
  rw [State.startNewWork_stopped, State.maybeIntegrateWork_stopped]

/-- The existing live/retired state projection is exact at initialization.
Witness: full kernel equality and a false interruption guard; startup is not terminated.
-/
@[simp]
theorem State.initialize_fromReference (work : Work)
    : State.initialize work
      = State.fromReference
          (ReferenceWorkQueue.State.initialize
            (ReferenceWorkQueue.Work.fromExecution work)) := by
  calc
    State.initialize work
        = ⟨(State.initialize work).queue, (State.initialize work).stopped⟩ :=
      rfl
    _ = ⟨
        ReferenceWorkQueue.State.initialize (ReferenceWorkQueue.Work.fromExecution work),
        false
      ⟩ := by
      rw [State.initialize_queue, State.initialize_stopped]
    _ = State.fromReference
          (ReferenceWorkQueue.State.initialize
            (ReferenceWorkQueue.Work.fromExecution work)) := by
      simp only [State.fromReference, ReferenceWorkQueue.createWorkQueue_terminated,
        Bool.false_eq_true, ↓reduceIte]

end GraphQL.IncrementalDelivery.AlternativeWorkQueue
