import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationRejections

/-! Cached startup failure can remove live owners but preserves permanent catalogues.
These field facts follow the literal fused traversal without a refinement premise.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue
open WorkQueueSemantics (Occurrence)

private abbrev catalogues (state : State) :=
  (state.queue.tasks, state.queue.registeredGroups)

private theorem removalTaskStep_catalogues (acc : State × List CleanupTarget)
    (occurrence : Occurrence)
    : catalogues (fusedRemovalTaskStep acc occurrence).1 = catalogues acc.1 := by
  unfold fusedRemovalTaskStep
  split
  · rfl
  · split <;> rfl

private theorem removalTaskFold_catalogues (tasks : List Occurrence)
    (acc : State × List CleanupTarget)
    : catalogues (tasks.foldl fusedRemovalTaskStep acc).1 = catalogues acc.1 := by
  induction tasks generalizing acc with
  | nil => rfl
  | cons task rest ih =>
      exact (ih (fusedRemovalTaskStep acc task)).trans (removalTaskStep_catalogues acc task)

/-- Fused last-owner disposal never deletes a permanent task or group registration. -/
theorem State.removeGroup_permanentCatalogues (state : State) (ref : Nat)
    (targets : List CleanupTarget := [])
    : (state.removeGroup ref targets).1.queue.tasks = state.queue.tasks
      ∧ (state.removeGroup ref targets).1.queue.registeredGroups
        = state.queue.registeredGroups := by
  have loop (fuel : Nat) (current : State) (pending removed) (targets)
      : catalogues (State.removeGroup.walk fuel current pending removed targets).1
        = catalogues current := by
    induction fuel generalizing current pending removed targets with
    | zero => simp only [State.removeGroup.walk]
    | succ fuel ih =>
        induction pending generalizing current removed targets with
        | nil => simp only [State.removeGroup.walk]
        | cons key rest tailIH =>
            cases found : current.queue.groupNode? key with
            | none =>
                simpa only [State.removeGroup.walk, found] using tailIH current removed targets
            | some group =>
                rw [State.removeGroup.walk, found]
                let erased := eraseRemovalGroup current key
                let folded := group.tasks.foldl fusedRemovalTaskStep (erased, targets)
                exact (ih folded.1 (group.childGroups ++ rest) (key :: removed) folded.2).trans
                  (removalTaskFold_catalogues group.tasks (erased, targets))
  have same : catalogues (state.removeGroup ref targets).1 = catalogues state := loop _ _ _ _ _
  exact ⟨congrArg Prod.fst same, congrArg Prod.snd same⟩

private theorem startTask_catalogues (queue : ReferenceWorkQueue.State)
    (occurrence : Occurrence) (available : List (Occurrence × Nat))
    : (queue.startTask occurrence available).tasks = queue.tasks
      ∧ (queue.startTask occurrence available).registeredGroups
        = queue.registeredGroups := by
  unfold ReferenceWorkQueue.State.startTask
  split
  · exact ⟨rfl, rfl⟩
  · split <;> exact ⟨rfl, rfl⟩

/-- Both startup branches retain the same permanent descriptors under any cache snapshot. -/
theorem State.startGroup_permanentCatalogues (state : State) (ref : Nat)
    (targets : List CleanupTarget := []) (available : List (Occurrence × Nat) := [])
    : (state.startGroup ref targets available).1.queue.tasks = state.queue.tasks
      ∧ (state.startGroup ref targets available).1.queue.registeredGroups
        = state.queue.registeredGroups := by
  have tasks (more : List Occurrence) (queue : ReferenceWorkQueue.State)
      : (more.foldl (fun current task => current.startTask task available) queue).tasks
          = queue.tasks
        ∧ (more.foldl (fun current task => current.startTask task available) queue).registeredGroups
          = queue.registeredGroups := by
    induction more generalizing queue with
    | nil => exact ⟨rfl, rfl⟩
    | cons task rest ih =>
        have next := ih (queue.startTask task available)
        have step := startTask_catalogues queue task available
        exact ⟨next.1.trans step.1, next.2.trans step.2⟩
  unfold State.startGroup
  dsimp only
  split
  · exact ⟨ReferenceWorkQueue.State.cacheTaskFailures_tasks _ _,
      ReferenceWorkQueue.State.cacheTaskFailures_registeredGroups _ _⟩
  · rename_i group found
    split
    · have next := tasks group.tasks (state.queue.cacheTaskFailures available)
      exact ⟨next.1.trans (ReferenceWorkQueue.State.cacheTaskFailures_tasks _ _),
        next.2.trans (ReferenceWorkQueue.State.cacheTaskFailures_registeredGroups _ _)⟩
    · have next := State.removeGroup_permanentCatalogues
        { state with queue := state.queue.cacheTaskFailures available } group.group.node.ref targets
      exact ⟨next.1.trans (ReferenceWorkQueue.State.cacheTaskFailures_tasks _ _),
        next.2.trans (ReferenceWorkQueue.State.cacheTaskFailures_registeredGroups _ _)⟩

/-- Delayed activation preserves permanent catalogues even when cached startup removes
live owners. No task-owner frame, generated forest, or healthy-startup premise is needed.
-/
theorem State.startNewWork_permanentCatalogues (state : State)
    (roots : ReferenceWorkQueue.NewWork) (integrated : IntegratedWork)
    (targets : List CleanupTarget := []) (available : List (Occurrence × Nat) := [])
    : (state.startNewWork roots integrated targets available).1.queue.tasks
        = state.queue.tasks
      ∧ (state.startNewWork roots integrated targets available).1.queue.registeredGroups
        = state.queue.registeredGroups := by
  have streams (more : List Execution.DeliveryNode) (queue : ReferenceWorkQueue.State)
      : (more.foldl (fun current stream => current.startStream stream.ref) queue).tasks
          = queue.tasks
        ∧ (more.foldl (fun current stream => current.startStream stream.ref) queue).registeredGroups
          = queue.registeredGroups := by
    induction more generalizing queue with
    | nil => exact ⟨rfl, rfl⟩
    | cons stream rest ih =>
        rw [List.foldl_cons]
        have next := ih (queue.startStream stream.ref)
        have step : (queue.startStream stream.ref).tasks = queue.tasks
            ∧ (queue.startStream stream.ref).registeredGroups = queue.registeredGroups := by
          unfold ReferenceWorkQueue.State.startStream
          split <;> exact ⟨rfl, rfl⟩
        exact ⟨next.1.trans step.1, next.2.trans step.2⟩
  have tasks (more : List ReferenceWorkQueue.Task) (queue : ReferenceWorkQueue.State)
      : (more.foldl (fun current task => current.startTask task.occurrence available) queue).tasks
          = queue.tasks
        ∧ (more.foldl (fun current task => current.startTask task.occurrence available)
            queue).registeredGroups = queue.registeredGroups := by
    induction more generalizing queue with
    | nil => exact ⟨rfl, rfl⟩
    | cons task rest ih =>
        have next := ih (queue.startTask task.occurrence available)
        have step := startTask_catalogues queue task.occurrence available
        exact ⟨next.1.trans step.1, next.2.trans step.2⟩
  have groups (more : WorkQueueSemantics.NodeRefs)
      (acc : State × List CleanupTarget × List ReferenceWorkQueue.GroupFailureEvent)
      : catalogues (more.foldl
          (fun (current, targets, failures) ref =>
            let (next, targets, queued) := current.startGroup ref targets available
            (next, targets, failures ++ queued)) acc).1 = catalogues acc.1 := by
    induction more generalizing acc with
    | nil => rfl
    | cons ref rest ih =>
        have next := ih ((acc.1.startGroup ref acc.2.1 available).1,
          (acc.1.startGroup ref acc.2.1 available).2.1,
          acc.2.2 ++ (acc.1.startGroup ref acc.2.1 available).2.2)
        have step := State.startGroup_permanentCatalogues acc.1 ref acc.2.1 available
        exact next.trans (Prod.ext step.1 step.2)
  unfold State.startNewWork
  split
  · exact ⟨rfl, rfl⟩
  · dsimp only
    let installedQueue := roots.newStreams.foldl
      (fun current stream => current.startStream stream.ref)
      { state.queue with
        rootGroups := state.queue.rootGroups ++ roots.newGroups.map Execution.DeliveryNode.ref }
    let installed : State := { state with queue := installedQueue }
    let startedQueue := integrated.activeTasks.foldl
      (fun current task => current.startTask task.occurrence available) installedQueue
    have grouped := groups (roots.newGroups.map Execution.DeliveryNode.ref)
      ({ installed with queue := startedQueue },
        installed.disposeRejectedTasks integrated targets, [])
    have started := tasks integrated.activeTasks installedQueue
    have installedFields := streams roots.newStreams { state.queue with
      rootGroups := state.queue.rootGroups ++ roots.newGroups.map Execution.DeliveryNode.ref }
    exact ⟨(congrArg Prod.fst grouped).trans (started.1.trans installedFields.1),
      (congrArg Prod.snd grouped).trans (started.2.trans installedFields.2)⟩

end GraphQL.IncrementalDelivery.AlternativeWorkQueue
