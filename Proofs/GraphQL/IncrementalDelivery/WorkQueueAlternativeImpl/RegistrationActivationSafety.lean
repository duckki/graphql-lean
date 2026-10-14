import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.SuccessfulBufferRetention

/-! Delayed active-task starts preserve existing buffers and the cleanup proof frame. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open GraphQL.IncrementalDelivery.WorkQueueSemantics (Occurrence)
private abbrev Kernel := ReferenceWorkQueue.State

-----------------------------------------------------------------------------------------
-- Task starts extend computation storage without changing the accounting core
-----------------------------------------------------------------------------------------

private theorem startTasks_core (queue : Kernel) (tasks : List ReferenceWorkQueue.Task)
    : registrationCore
        (tasks.foldl (fun current task => current.startTask task.occurrence) queue)
      = registrationCore queue := by
  induction tasks generalizing queue with
  | nil => rfl
  | cons task rest ih =>
      rw [List.foldl_cons, ih]
      unfold ReferenceWorkQueue.State.startTask
      split
      · rfl
      · split <;> rfl

private theorem SnapshotTaskEvidence.startTask {queue : Kernel} {work}
    (frame : SnapshotTaskEvidence queue work) (occurrence : Occurrence)
    : SnapshotTaskEvidence (queue.startTask occurrence) work := by
  have core : registrationCore (queue.startTask occurrence) = registrationCore queue := by
    unfold ReferenceWorkQueue.State.startTask
    split
    · rfl
    · split <;> rfl
  refine ⟨?_, ?_, ?_, frame.started.startTask occurrence,
    frame.matching.startTask occurrence, frame.buffered.startTask occurrence,
    frame.sound.startTask occurrence⟩
  · change (registrationCore (queue.startTask occurrence)).GroupRefsUnique
    rw [core]; exact frame.keys
  · change (registrationCore (queue.startTask occurrence)).LiveGroupsRegistered
    rw [core]; exact frame.live
  · change (registrationCore (queue.startTask occurrence)).TaskGroupsRegistered
    rw [core]; exact frame.contributors

/-- Actual delayed activation retains the complete cleanup frame. -/
theorem SnapshotTaskEvidence.startAlternative {state : State} {work}
    (frame : SnapshotTaskEvidence state.queue work) (roots : ReferenceWorkQueue.NewWork)
    (integrated : IntegratedWork) (targets : List CleanupTarget := [])
    : SnapshotTaskEvidence (state.startNewWork roots integrated targets).1.queue
        work := by
  cases running : state.stopped with
  | true => simpa only [State.startNewWork, running, ↓reduceIte] using frame
  | false =>
      rw [State.startNewWork_queue _ _ _ _ running]
      have loop (tasks : List ReferenceWorkQueue.Task) (queue : Kernel)
          (initial : SnapshotTaskEvidence queue work)
          : SnapshotTaskEvidence
              (tasks.foldl (fun current task => current.startTask task.occurrence) queue)
              work := by
        induction tasks generalizing queue with
        | nil => exact initial
        | cons task rest ih => exact ih _ (initial.startTask task.occurrence)
      exact (loop integrated.activeTasks state.queue frame).startNewWork roots

/-- Activation changes no group record, including its child frontier and memberships. -/
theorem State.startNewWork_groupNodes (state : State) (roots : ReferenceWorkQueue.NewWork)
    (integrated : IntegratedWork) (targets : List CleanupTarget := [])
    : (state.startNewWork roots integrated targets).1.queue.groupNodes
      = state.queue.groupNodes := by
  cases running : state.stopped with
  | true => simp only [State.startNewWork, running, ↓reduceIte]
  | false =>
      rw [State.startNewWork_queue _ _ _ _ running,
        (ReferenceWorkQueue.State.startNewWork_groupCore _ _).1]
      change (registrationCore (integrated.activeTasks.foldl
        (fun current task => current.startTask task.occurrence) state.queue)).groupNodes
        = (registrationCore state.queue).groupNodes
      exact congrArg ReferenceWorkQueue.State.groupNodes (startTasks_core state.queue integrated.activeTasks)

/-- Delayed activation retains the permanent task and group catalogues. -/
theorem State.startNewWork_catalogues (state : State) (roots : ReferenceWorkQueue.NewWork)
    (integrated : IntegratedWork) (targets : List CleanupTarget := [])
    : (state.startNewWork roots integrated targets).1.queue.tasks = state.queue.tasks
      ∧ (state.startNewWork roots integrated targets).1.queue.registeredGroups
        = state.queue.registeredGroups := by
  cases running : state.stopped with
  | true => simp [State.startNewWork, running]
  | false =>
      rw [State.startNewWork_queue _ _ _ _ running,
        (ReferenceWorkQueue.State.startNewWork_groupCore _ _).2.1,
        ReferenceWorkQueue.State.startNewWork_registeredGroups]
      change (registrationCore (integrated.activeTasks.foldl
        (fun current task => current.startTask task.occurrence) state.queue)).tasks
          = (registrationCore state.queue).tasks
        ∧ (registrationCore (integrated.activeTasks.foldl
          (fun current task => current.startTask task.occurrence) state.queue)).registeredGroups
          = (registrationCore state.queue).registeredGroups
      exact ⟨congrArg ReferenceWorkQueue.State.tasks (startTasks_core state.queue integrated.activeTasks),
        congrArg ReferenceWorkQueue.State.registeredGroups
          (startTasks_core state.queue integrated.activeTasks)⟩

/-- Already buffered nodes and their held sources cannot be overwritten by delayed starts. -/
theorem State.startNewWork_lookup_existing {state : State} {occurrence node}
    (found : state.queue.taskNode? occurrence = some node)
    (roots : ReferenceWorkQueue.NewWork) (integrated : IntegratedWork)
    (targets : List CleanupTarget := [])
    : (state.startNewWork roots integrated targets).1.queue.taskNode? occurrence
      = some node := by
  cases running : state.stopped with
  | true => simpa only [State.startNewWork, running, ↓reduceIte] using found
  | false =>
      rw [State.startNewWork_queue _ _ _ _ running]
      apply ReferenceWorkQueue.State.startNewWork_lookup_existing _ roots
      have loop (tasks : List ReferenceWorkQueue.Task) (queue : Kernel)
          (prior : queue.taskNode? occurrence = some node)
          : (tasks.foldl (fun current task => current.startTask task.occurrence) queue).taskNode?
            occurrence = some node := by
        induction tasks generalizing queue with
        | nil => exact prior
        | cons task rest ih =>
            exact ih _ (ReferenceWorkQueue.State.startTask_lookup_existing prior _)
      exact loop _ _ found

/-- The finite generated forest is unchanged by the actual active-task/release starts. -/
theorem removalForest_startAlternative {state : State} {parents}
    (forest : state.queue.RemovalForest parents) (roots : ReferenceWorkQueue.NewWork)
    (integrated : IntegratedWork) (targets : List CleanupTarget := [])
    : (state.startNewWork roots integrated targets).1.queue.RemovalForest parents := by
  have groups := State.startNewWork_groupNodes state roots integrated targets
  refine ⟨?_, ?_, ?_⟩
  · simpa only [ReferenceWorkQueue.State.ChildGroupsUnique, groups] using forest.uniqueChildren
  · simpa only [ReferenceWorkQueue.State.ChildLinksCanonical, groups] using forest.canonical
  · intro parent child memberParent memberChild linked
    rw [groups] at memberParent memberChild
    exact forest.increasing memberParent memberChild linked

/-- Delayed starts cannot resurrect a retired group. -/
theorem retiredGroup_startAlternative {state : State} {key}
    (retired : state.queue.RetiredGroup key) (roots : ReferenceWorkQueue.NewWork)
    (integrated : IntegratedWork) (targets : List CleanupTarget := [])
    : (state.startNewWork roots integrated targets).1.queue.RetiredGroup key := by
  cases running : state.stopped with
  | true => simpa only [State.startNewWork, running, ↓reduceIte] using retired
  | false =>
      rw [State.startNewWork_queue _ _ _ _ running]
      apply ReferenceWorkQueue.State.RetiredGroup.startNewWork _ roots
      change (registrationCore (integrated.activeTasks.foldl
        (fun current task => current.startTask task.occurrence) state.queue)).RetiredGroup key
      rw [startTasks_core]
      exact retired

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
