import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ActivationCatalogues
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedTaskRemoval
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedCleanupTargets
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationRejections

/-! A fresh linked task either keeps a live owner during native startup or is aborted
by that startup's actual fused removal. No owner-survival assumption is supplied.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open WorkQueueSemantics (Occurrence NodeRefs)
open ReferenceWorkQueue (Task)
open GraphQL.IncrementalDelivery.Execution (DeliveryNode)

private theorem taskTarget_of_abort {targets : List CleanupTarget} {occurrence}
    (emitted : .abortTask occurrence ∈ targets.flatMap CleanupTarget.effects)
    : .task occurrence ∈ targets := by
  obtain ⟨target, member, supplied⟩ := List.mem_flatMap.mp emitted
  cases target with
  | task other =>
      have same : occurrence = other := by simpa [CleanupTarget.effects] using supplied
      exact same.symm ▸ member
  | stream key => simp [CleanupTarget.effects, cancelStream] at supplied

private theorem startTasks_nodes (tasks : List Occurrence)
    (queue : ReferenceWorkQueue.State) (available : List (Occurrence × Nat))
    : (tasks.foldl (fun current task => current.startTask task available)
        queue).groupNodes
      = queue.groupNodes := by
  induction tasks generalizing queue with
  | nil => rfl
  | cons task rest ih =>
      rw [List.foldl_cons, ih, ReferenceWorkQueue.State.startTask_groupNodes]

/-- Startup preserves the ordered cleanup prefix, including cached-failure disposal. -/
theorem startGroup_targets (state : State) (ref : NodeRef) (targets : List CleanupTarget)
    (unique : targets.Nodup) (available : List (Occurrence × Nat) := [])
    : (state.startGroup ref targets available).2.1.Nodup
      ∧ targets.IsPrefix (state.startGroup ref targets available).2.1 := by
  unfold State.startGroup
  dsimp only
  split
  · exact ⟨unique, List.prefix_refl _⟩
  · split
    · exact ⟨unique, List.prefix_refl _⟩
    · exact State.removeGroup_targets _ _ targets unique

/-- A linked task keeps an owner or is aborted under the actual availability snapshot.
Available failures may retire other owners but cannot reject the tracked computation.
-/
theorem startGroup_linkedTask_progress_available (state : State) (ref : NodeRef)
    (task : Task) (targets : List CleanupTarget) (unique : targets.Nodup)
    (catalogue : state.queue.task? task.occurrence = some task)
    (links : state.queue.TaskLinkedOn task.occurrence (task.groups.map DeliveryNode.ref))
    (owned
      : ∃ owner ∈ task.groups, ∃ group, state.queue.groupNode? owner.ref = some group)
    (unrejected
      : state.queue.TaskRejectionsSatisfy (fun rejected _ => rejected ≠ task.occurrence))
    (available : List (Occurrence × Nat))
    (licensed
      : ∀ occurrence errors,
          (occurrence, errors) ∈ available → occurrence ≠ task.occurrence)
    : let next := state.startGroup ref targets available
      (next.1.queue.TaskLinkedOn task.occurrence (task.groups.map DeliveryNode.ref)
        ∧ ∃ owner ∈ task.groups, ∃ group, next.1.queue.groupNode? owner.ref = some group)
      ∨ .task task.occurrence ∈ next.2.1 := by
  let cached : State := { state with queue := state.queue.cacheTaskFailures available }
  have nodeEq := congrArg ReferenceWorkQueue.State.groupNodes
    (state.queue.cacheTaskFailures_frame available)
  change cached.queue.groupNodes = state.queue.groupNodes at nodeEq
  have cachedLinks : cached.queue.TaskLinkedOn task.occurrence
      (task.groups.map DeliveryNode.ref) := by
    simpa only [ReferenceWorkQueue.State.TaskLinkedOn, nodeEq] using links
  have cachedOwned : ∃ owner ∈ task.groups, ∃ group,
      cached.queue.groupNode? owner.ref = some group := by
    simpa only [ReferenceWorkQueue.State.groupNode?, nodeEq] using owned
  have cachedCatalogue : cached.queue.task? task.occurrence = some task := by
    simpa only [cached, ReferenceWorkQueue.State.task?,
      ReferenceWorkQueue.State.cacheTaskFailures_tasks]
      using catalogue
  have cachedUnrejected := unrejected.cacheTaskFailures available licensed
  cases found : (state.queue.cacheTaskFailures available).groupNode? ref with
  | none =>
      simpa only [State.startGroup, found] using Or.inl ⟨cachedLinks, cachedOwned⟩
  | some group =>
      by_cases rejected :
        (group.tasks.filterMap
          (fun task =>
            ((state.queue.cacheTaskFailures available).taskNode? task).bind
              (·.rejection))).isEmpty
        = true
      · have nodes := startTasks_nodes group.tasks cached.queue available
        have kept : (List.foldl (fun current task => current.startTask task available) cached.queue
              group.tasks).TaskLinkedOn task.occurrence (task.groups.map DeliveryNode.ref)
            ∧ ∃ owner ∈ task.groups, ∃ ownerNode,
              (List.foldl (fun current task => current.startTask task available) cached.queue
                group.tasks).groupNode? owner.ref = some ownerNode :=
          ⟨by simpa only [ReferenceWorkQueue.State.TaskLinkedOn, nodes] using cachedLinks,
            by simpa only [ReferenceWorkQueue.State.groupNode?, nodes] using cachedOwned⟩
        simp only [State.startGroup, found, rejected, ↓reduceIte]
        exact .inl kept
      · rcases FusedRemovalTaskProgress_holds cached group.group.node.ref task targets unique
            cachedCatalogue cachedLinks cachedOwned cachedUnrejected with kept | aborted
        · simp only [State.startGroup, found, rejected, Bool.false_eq_true, ↓reduceIte,
            State.finishGroupFailure]
          exact .inl kept
        · have requested := taskTarget_of_abort aborted
          simp only [State.startGroup, found, rejected, Bool.false_eq_true, ↓reduceIte,
            State.finishGroupFailure]
          exact .inr requested

/-- The empty-snapshot specialization retains the existing startup progress interface. -/
theorem startGroup_linkedTask_progress (state : State) (ref : NodeRef) (task : Task)
    (targets : List CleanupTarget) (unique : targets.Nodup)
    (catalogue : state.queue.task? task.occurrence = some task)
    (links : state.queue.TaskLinkedOn task.occurrence (task.groups.map DeliveryNode.ref))
    (owned
      : ∃ owner ∈ task.groups, ∃ group, state.queue.groupNode? owner.ref = some group)
    (unrejected
      : state.queue.TaskRejectionsSatisfy (fun rejected _ => rejected ≠ task.occurrence))
    : let next := state.startGroup ref targets
      (next.1.queue.TaskLinkedOn task.occurrence (task.groups.map DeliveryNode.ref)
        ∧ ∃ owner ∈ task.groups, ∃ group, next.1.queue.groupNode? owner.ref = some group)
      ∨ .task task.occurrence ∈ next.2.1 :=
  startGroup_linkedTask_progress_available state ref task targets unique catalogue links
    owned unrejected [] (by intro occurrence errors impossible; cases impossible)

private def startupTaskStep (available : List (Occurrence × Nat))
    (acc : State × List CleanupTarget × List ReferenceWorkQueue.GroupFailureEvent)
    (ref : NodeRef)
    : State × List CleanupTarget × List ReferenceWorkQueue.GroupFailureEvent :=
  let (next, targets, queued) := acc.1.startGroup ref acc.2.1 available
  (next, targets, acc.2.2 ++ queued)

private theorem startupTaskFold_targets (refs : NodeRefs)
    (available : List (Occurrence × Nat))
    (acc : State × List CleanupTarget × List ReferenceWorkQueue.GroupFailureEvent)
    (unique : acc.2.1.Nodup)
    : acc.2.1.IsPrefix (refs.foldl (startupTaskStep available) acc).2.1 := by
  induction refs generalizing acc with
  | nil => exact List.prefix_refl _
  | cons ref rest ih =>
      have step := startGroup_targets acc.1 ref acc.2.1 unique available
      exact step.2.trans (ih (startupTaskStep available acc ref) step.1)

/-- A fresh linked task keeps a live owner or contributes its abort during the complete
native activation fold. Other cached failures may remove any subset of its live owners.
-/
theorem startNewWork_linkedTask_progress_available (state : State)
    (roots : ReferenceWorkQueue.NewWork) (integrated : IntegratedWork) (task : Task)
    (targets : List CleanupTarget) (_unique : targets.Nodup)
    (catalogue : state.queue.task? task.occurrence = some task)
    (links : state.queue.TaskLinkedOn task.occurrence (task.groups.map DeliveryNode.ref))
    (owned
      : ∃ owner ∈ task.groups, ∃ group, state.queue.groupNode? owner.ref = some group)
    (unrejected
      : state.queue.TaskRejectionsSatisfy (fun rejected _ => rejected ≠ task.occurrence))
    (available : List (Occurrence × Nat))
    (licensed
      : ∀ occurrence errors,
          (occurrence, errors) ∈ available → occurrence ≠ task.occurrence)
    : let next := state.startNewWork roots integrated targets available
      (next.1.queue.TaskLinkedOn task.occurrence (task.groups.map DeliveryNode.ref)
        ∧ ∃ owner ∈ task.groups, ∃ group, next.1.queue.groupNode? owner.ref = some group)
      ∨ .task task.occurrence ∈ next.2.1 := by
  have loop (refs : NodeRefs)
      (acc : State × List CleanupTarget × List ReferenceWorkQueue.GroupFailureEvent)
      (unique : acc.2.1.Nodup)
      (catalogue : acc.1.queue.task? task.occurrence = some task)
      (links : acc.1.queue.TaskLinkedOn task.occurrence (task.groups.map DeliveryNode.ref))
      (owned : ∃ owner ∈ task.groups, ∃ group, acc.1.queue.groupNode? owner.ref = some group)
      (unrejected : acc.1.queue.TaskRejectionsSatisfy
        (fun rejected _ => rejected ≠ task.occurrence))
      : let next := refs.foldl (startupTaskStep available) acc
        (next.1.queue.TaskLinkedOn task.occurrence (task.groups.map DeliveryNode.ref)
          ∧ ∃ owner ∈ task.groups, ∃ group, next.1.queue.groupNode? owner.ref = some group)
        ∨ .task task.occurrence ∈ next.2.1 := by
    induction refs generalizing acc with
    | nil => exact .inl ⟨links, owned⟩
    | cons ref rest ih =>
        let step := startupTaskStep available acc ref
        have targetFrame := startGroup_targets acc.1 ref acc.2.1 unique available
        rcases startGroup_linkedTask_progress_available acc.1 ref task acc.2.1
            unique catalogue links
            owned unrejected available licensed with kept | requested
        · have nextCatalogue : step.1.queue.task? task.occurrence = some task := by
            change ((acc.1.startGroup ref acc.2.1 available).1.queue).task? _ = _
            simpa only [ReferenceWorkQueue.State.task?,
              (State.startGroup_permanentCatalogues acc.1 ref acc.2.1 available).1] using catalogue
          have nextUnrejected : step.1.queue.TaskRejectionsSatisfy
              (fun rejected _ => rejected ≠ task.occurrence) :=
            State.startGroup_taskRejections unrejected ref acc.2.1 available licensed
          exact ih step targetFrame.1 nextCatalogue kept.1 kept.2 nextUnrejected
        · exact .inr ((startupTaskFold_targets rest available step targetFrame.1).subset requested)
  have streamCore (more : List DeliveryNode) (queue : ReferenceWorkQueue.State)
      : ((more.foldl (fun current stream => current.startStream stream.ref) queue).tasks,
          (more.foldl (fun current stream => current.startStream stream.ref) queue).groupNodes)
        = (queue.tasks, queue.groupNodes) := by
    induction more generalizing queue with
    | nil => rfl
    | cons stream rest ih =>
        rw [List.foldl_cons, ih]
        unfold ReferenceWorkQueue.State.startStream
        split <;> rfl
  have taskCore (more : List Task) (queue : ReferenceWorkQueue.State)
      : ((more.foldl (fun current task => current.startTask task.occurrence available) queue).tasks,
          (more.foldl (fun current task => current.startTask task.occurrence available)
            queue).groupNodes)
        = (queue.tasks, queue.groupNodes) := by
    induction more generalizing queue with
    | nil => rfl
    | cons task rest ih =>
        rw [List.foldl_cons, ih]
        unfold ReferenceWorkQueue.State.startTask
        split
        · rfl
        · split <;> rfl
  have streamRejections (more : List DeliveryNode) (queue : ReferenceWorkQueue.State)
      (prior : queue.TaskRejectionsSatisfy (fun rejected _ => rejected ≠ task.occurrence))
      : (more.foldl (fun current stream => current.startStream stream.ref)
          queue).TaskRejectionsSatisfy (fun rejected _ => rejected ≠ task.occurrence) := by
    induction more generalizing queue with
    | nil => exact prior
    | cons stream rest ih =>
        apply ih (queue.startStream stream.ref)
        change (queue.startStream stream.ref).TaskRejectionsSatisfy
          (fun rejected _ => rejected ≠ task.occurrence)
        unfold ReferenceWorkQueue.State.startStream
        split <;> exact prior
  have taskRejections (more : List Task) (queue : ReferenceWorkQueue.State)
      (prior : queue.TaskRejectionsSatisfy (fun rejected _ => rejected ≠ task.occurrence))
      : (more.foldl (fun current task => current.startTask task.occurrence available)
          queue).TaskRejectionsSatisfy (fun rejected _ => rejected ≠ task.occurrence) := by
    induction more generalizing queue with
    | nil => exact prior
    | cons task rest ih =>
        exact ih _
          (prior.startTask task.occurrence available licensed)
  unfold State.startNewWork
  split
  · exact .inl ⟨links, owned⟩
  · dsimp only
    let rooted := { state.queue with
      rootGroups := state.queue.rootGroups ++ roots.newGroups.map DeliveryNode.ref }
    let installedQueue := roots.newStreams.foldl
      (fun current stream => current.startStream stream.ref) rooted
    let installed : State := { state with queue := installedQueue }
    let started := integrated.activeTasks.foldl
      (fun current task => current.startTask task.occurrence available) installedQueue
    have core : (started.tasks, started.groupNodes) = (state.queue.tasks, state.queue.groupNodes) :=
      (taskCore integrated.activeTasks installedQueue).trans (streamCore roots.newStreams rooted)
    have taskEq : started.tasks = state.queue.tasks := congrArg Prod.fst core
    have nodeEq : started.groupNodes = state.queue.groupNodes := congrArg Prod.snd core
    have initialCatalogue : started.task? task.occurrence = some task := by
      simpa only [ReferenceWorkQueue.State.task?, taskEq] using catalogue
    have initialLinks :
        started.TaskLinkedOn task.occurrence (task.groups.map DeliveryNode.ref) := by
      simpa only [ReferenceWorkQueue.State.TaskLinkedOn, nodeEq] using links
    have initialOwned :
        ∃ owner ∈ task.groups, ∃ group, started.groupNode? owner.ref = some group := by
      simpa only [ReferenceWorkQueue.State.groupNode?, nodeEq] using owned
    exact loop (roots.newGroups.map DeliveryNode.ref)
      (
        { installed with queue := started },
        installed.disposeRejectedTasks integrated targets,
        []
      )
      (State.disposeRejectedTasks_nodup _ _ _) initialCatalogue initialLinks initialOwned
      (taskRejections integrated.activeTasks installedQueue
        (streamRejections roots.newStreams rooted unrejected))

/-- Existing empty-snapshot activation progress follows from the batch-aware theorem. -/
theorem startNewWork_linkedTask_progress (state : State)
    (roots : ReferenceWorkQueue.NewWork) (integrated : IntegratedWork) (task : Task)
    (targets : List CleanupTarget) (_unique : targets.Nodup)
    (catalogue : state.queue.task? task.occurrence = some task)
    (links : state.queue.TaskLinkedOn task.occurrence (task.groups.map DeliveryNode.ref))
    (owned
      : ∃ owner ∈ task.groups, ∃ group, state.queue.groupNode? owner.ref = some group)
    (unrejected
      : state.queue.TaskRejectionsSatisfy (fun rejected _ => rejected ≠ task.occurrence))
    : let next := state.startNewWork roots integrated targets
      (next.1.queue.TaskLinkedOn task.occurrence (task.groups.map DeliveryNode.ref)
        ∧ ∃ owner ∈ task.groups, ∃ group, next.1.queue.groupNode? owner.ref = some group)
      ∨ .task task.occurrence ∈ next.2.1 :=
  startNewWork_linkedTask_progress_available state roots integrated task targets _unique
    catalogue links owned unrejected []
    (by intro occurrence errors impossible; cases impossible)

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
