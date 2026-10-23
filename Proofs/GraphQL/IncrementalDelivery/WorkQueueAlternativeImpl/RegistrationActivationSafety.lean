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
    frame.sound.startTask occurrence, ?_⟩
  · change (registrationCore (queue.startTask occurrence)).GroupRefsUnique
    rw [core]; exact frame.keys
  · change (registrationCore (queue.startTask occurrence)).LiveGroupsRegistered
    rw [core]; exact frame.live
  · change (registrationCore (queue.startTask occurrence)).TaskGroupsRegistered
    rw [core]; exact frame.contributors
  · refine frame.registration.retain (next := queue.startTask occurrence)
      ?_ ?_ (frame.started.startTask occurrence) ?_ ?_
    · change (registrationCore (queue.startTask occurrence)).LiveGroupsRegistered
      rw [core]; exact frame.live
    · change (registrationCore (queue.startTask occurrence)).TaskGroupsRegistered
      rw [core]; exact frame.contributors
    · change (registrationCore (queue.startTask occurrence)).tasks.Subset queue.tasks
      rw [core]; exact fun _ member => member
    · change queue.registeredGroups.Subset
        (registrationCore (queue.startTask occurrence)).registeredGroups
      rw [core]; exact fun _ member => member

/-- Structural evidence at the actual delayed activation boundary.
The ownership certificate is for the queue after active-task starts, before any released
group can reject and remove records. It is derived from source registration, not supplied
as an endpoint correspondence or host requirement.
-/
structure ActivationFrame (state : State) (integrated : IntegratedWork) (work : Work)
    (parents : Nat → WorkQueueSemantics.NodeRefs)
    : Prop where
  owners
    : (integrated.activeTasks.foldl
        (fun current task => current.startTask task.occurrence)
        state.queue).TaskOwnerFrame
        work
  forest : state.queue.RemovalForest parents

/-- Active-task starts preserve the activation boundary’s generated forest. -/
theorem ActivationFrame.startedForest {state integrated work parents}
    (frame : ActivationFrame state integrated work parents)
    : (integrated.activeTasks.foldl
        (fun current task => current.startTask task.occurrence) state.queue).RemovalForest
        parents := by
  have core := startTasks_core state.queue integrated.activeTasks
  have groups := congrArg ReferenceWorkQueue.State.groupNodes core
  change (integrated.activeTasks.foldl (fun current task => current.startTask task.occurrence)
    state.queue).groupNodes = state.queue.groupNodes at groups
  exact ⟨
    by
      simpa only [ReferenceWorkQueue.State.ChildGroupsUnique, groups]
        using frame.forest.uniqueChildren,
    by
      simpa only [ReferenceWorkQueue.State.ChildLinksCanonical, groups]
        using frame.forest.canonical,
    by
      intro parent child memberParent memberChild linked
      rw [groups] at memberParent memberChild
      exact frame.forest.increasing memberParent memberChild linked
  ⟩

/-- Native startup shares the reference queue transition after active-task starts. -/
theorem ActivationFrame.queueProjection {state integrated work parents}
    (frame : ActivationFrame state integrated work parents)
    (roots : ReferenceWorkQueue.NewWork) (targets : List CleanupTarget)
    (running : state.stopped = false)
    : (state.startNewWork roots integrated targets).1.queue
      = ((integrated.activeTasks.foldl
            (fun current task => current.startTask task.occurrence)
            state.queue).startNewWork
          roots).1 :=
  state.startNewWork_queue roots integrated targets running [] frame.owners
    frame.startedForest

/-- Actual delayed activation retains the complete cleanup evidence on surviving records. -/
theorem SnapshotTaskEvidence.startAlternative {state : State} {work parents}
    (frame : SnapshotTaskEvidence state.queue work) (roots : ReferenceWorkQueue.NewWork)
    (integrated : IntegratedWork) (targets : List CleanupTarget := [])
    (activation : ActivationFrame state integrated work parents)
    : SnapshotTaskEvidence (state.startNewWork roots integrated targets).1.queue
        work := by
  cases running : state.stopped with
  | true => simpa only [State.startNewWork, running, ↓reduceIte] using frame
  | false =>
      rw [activation.queueProjection roots targets running]
      have loop (tasks : List ReferenceWorkQueue.Task) (queue : Kernel)
          (initial : SnapshotTaskEvidence queue work)
          : SnapshotTaskEvidence
              (tasks.foldl (fun current task => current.startTask task.occurrence) queue)
              work := by
        induction tasks generalizing queue with
        | nil => exact initial
        | cons task rest ih => exact ih _ (initial.startTask task.occurrence)
      exact (loop integrated.activeTasks state.queue frame).startNewWork roots

/-- Delayed startup can remove group records from its pre-startup queue. -/
theorem State.startNewWork_groupNodes_sublist (state : State) {work parents}
    (roots : ReferenceWorkQueue.NewWork) (integrated : IntegratedWork)
    (targets : List CleanupTarget := [])
    (activation : ActivationFrame state integrated work parents)
    : (state.startNewWork roots integrated targets).1.queue.groupNodes.Sublist
        state.queue.groupNodes := by
  cases running : state.stopped with
  | true => simp only [State.startNewWork, running, ↓reduceIte]; exact .refl _
  | false =>
      rw [activation.queueProjection roots targets running]
      have included := (ReferenceWorkQueue.State.startNewWork_groupCore
        (integrated.activeTasks.foldl (fun current task => current.startTask task.occurrence)
          state.queue) roots).1
      have groups := congrArg ReferenceWorkQueue.State.groupNodes
        (startTasks_core state.queue integrated.activeTasks)
      change (integrated.activeTasks.foldl (fun current task => current.startTask task.occurrence)
        state.queue).groupNodes = state.queue.groupNodes at groups
      rwa [groups] at included

/-- Delayed activation retains the permanent task and group catalogues. -/
theorem State.startNewWork_catalogues (state : State) {work parents}
    (roots : ReferenceWorkQueue.NewWork) (integrated : IntegratedWork)
    (targets : List CleanupTarget := [])
    (activation : ActivationFrame state integrated work parents)
    : (state.startNewWork roots integrated targets).1.queue.tasks = state.queue.tasks
      ∧ (state.startNewWork roots integrated targets).1.queue.registeredGroups
        = state.queue.registeredGroups := by
  cases running : state.stopped with
  | true => simp [State.startNewWork, running]
  | false =>
      rw [activation.queueProjection roots targets running,
        (ReferenceWorkQueue.State.startNewWork_groupCore _ _).2.1,
        ReferenceWorkQueue.State.startNewWork_registeredGroups]
      change (registrationCore (integrated.activeTasks.foldl
        (fun current task => current.startTask task.occurrence) state.queue)).tasks
          = (registrationCore state.queue).tasks ∧
        (registrationCore (integrated.activeTasks.foldl
          (fun current task => current.startTask task.occurrence) state.queue)).registeredGroups
          = (registrationCore state.queue).registeredGroups
      exact ⟨congrArg ReferenceWorkQueue.State.tasks
          (startTasks_core state.queue integrated.activeTasks),
        congrArg ReferenceWorkQueue.State.registeredGroups
          (startTasks_core state.queue integrated.activeTasks)⟩

/-- A buffered computation is retained when one of its contributing owners survives startup. -/
theorem State.startNewWork_lookup_existing {state : State} {occurrence node work parents}
    (found : state.queue.taskNode? occurrence = some node)
    (roots : ReferenceWorkQueue.NewWork) (integrated : IntegratedWork)
    (targets : List CleanupTarget := [])
    (activation : ActivationFrame state integrated work parents)
    {contributor : Execution.DeliveryNode} (contributes : contributor ∈ node.task.groups)
    {owner : ReferenceWorkQueue.GroupNode}
    (live : owner ∈ (state.startNewWork roots integrated targets).1.queue.groupNodes)
    (same : owner.group.node.ref = contributor.ref)
    : (state.startNewWork roots integrated targets).1.queue.taskNode? occurrence
      = some node := by
  cases running : state.stopped with
  | true => simpa only [State.startNewWork, running, ↓reduceIte] using found
  | false =>
      rw [activation.queueProjection roots targets running] at live ⊢
      have loop (tasks : List ReferenceWorkQueue.Task) (queue : Kernel)
          (prior : queue.taskNode? occurrence = some node)
          : (tasks.foldl (fun current task => current.startTask task.occurrence) queue).taskNode?
            occurrence = some node := by
        induction tasks generalizing queue with
        | nil => exact prior
        | cons task rest ih =>
            exact ih _ (ReferenceWorkQueue.State.startTask_lookup_existing prior _)
      exact ReferenceWorkQueue.State.startNewWork_lookup_existing (loop _ _ found) roots
        [] (by intro errors member; cases member) contributes live same

/-- Removal during delayed startup preserves the finite generated forest. -/
theorem removalForest_startAlternative {state : State} {parents work}
    (roots : ReferenceWorkQueue.NewWork) (integrated : IntegratedWork)
    (targets : List CleanupTarget := [])
    (activation : ActivationFrame state integrated work parents)
    : (state.startNewWork roots integrated targets).1.queue.RemovalForest parents := by
  cases running : state.stopped with
  | true => simpa only [State.startNewWork, running, ↓reduceIte] using activation.forest
  | false =>
      rw [activation.queueProjection roots targets running]
      exact activation.startedForest.startNewWork roots

/-- Delayed starts cannot resurrect a retired group. -/
theorem retiredGroup_startAlternative {state : State} {key work parents}
    (retired : state.queue.RetiredGroup key) (roots : ReferenceWorkQueue.NewWork)
    (integrated : IntegratedWork) (targets : List CleanupTarget := [])
    (activation : ActivationFrame state integrated work parents)
    : (state.startNewWork roots integrated targets).1.queue.RetiredGroup key := by
  cases running : state.stopped with
  | true => simpa only [State.startNewWork, running, ↓reduceIte] using retired
  | false =>
      rw [activation.queueProjection roots targets running]
      apply ReferenceWorkQueue.State.RetiredGroup.startNewWork _ roots
      change (registrationCore (integrated.activeTasks.foldl
        (fun current task => current.startTask task.occurrence) state.queue)).RetiredGroup key
      rw [startTasks_core]
      exact retired

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
