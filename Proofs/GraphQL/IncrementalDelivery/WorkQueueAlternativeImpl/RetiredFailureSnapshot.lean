import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RetiredTaskReplay

/-! Removing a retired task's stale failure from a host availability snapshot is inert.
This applies only after both its computation node and all group memberships are gone.
-/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open WorkQueueSemantics (Occurrence NodeRefs)

/-- A missing task contributes no rejection slot at any position in cache exposure. -/
theorem State.RetiredTask.cacheTaskFailures_drop {queue occurrence}
    (retired : State.RetiredTask queue occurrence)
    (before after : List (Occurrence × Nat)) (errors : Nat)
    : queue.cacheTaskFailures (before ++ (occurrence, errors) :: after)
      = queue.cacheTaskFailures (before ++ after) := by
  have missing := (retired.cacheTaskFailures before).missing
  simp only [State.cacheTaskFailures, List.foldl_append, List.foldl_cons] at missing ⊢
  rw [missing]

private theorem failureLookup_drop (occurrence started : Occurrence)
    (different : occurrence ≠ started) (before after : List (Occurrence × Nat))
    (errors : Nat)
    : (before ++ (occurrence, errors) :: after).findSome?
        (fun entry => if entry.1 == started then some entry.2 else none)
      = (before ++ after).findSome?
          (fun entry => if entry.1 == started then some entry.2 else none) := by
  simp only [List.findSome?_append, List.findSome?_cons, occurrence_beq_iff_eq,
    different, ↓reduceIte]

/-- Another task's initial rejection is independent of the removed failure entry. -/
theorem State.startTask_dropFailure (queue : State) (occurrence started : Occurrence)
    (different : occurrence ≠ started) (before after : List (Occurrence × Nat))
    (errors : Nat)
    : queue.startTask started (before ++ (occurrence, errors) :: after)
      = queue.startTask started (before ++ after) := by
  simp only [State.startTask, failureLookup_drop occurrence started different before after errors]

private theorem startTasks_dropFailure (queue : State) (occurrence : Occurrence)
    (tasks : List Occurrence) (fresh : occurrence ∉ tasks)
    (before after : List (Occurrence × Nat)) (errors : Nat)
    : tasks.foldl
        (fun q task => q.startTask task (before ++ (occurrence, errors) :: after)) queue
      = tasks.foldl (fun q task => q.startTask task (before ++ after)) queue := by
  induction tasks generalizing queue with
  | nil => rfl
  | cons task rest ih =>
      simp only [List.mem_cons, not_or] at fresh
      rw [List.foldl_cons, List.foldl_cons,
        State.startTask_dropFailure queue occurrence task fresh.1 before after errors]
      exact ih _ fresh.2

/-- A retired failure changes neither the cached startup decision nor private task starts. -/
theorem State.RetiredTask.startGroup_dropFailure {queue occurrence}
    (retired : State.RetiredTask queue occurrence) (ref : Nat)
    (before after : List (Occurrence × Nat)) (errors : Nat)
    : queue.startGroup ref (before ++ (occurrence, errors) :: after)
      = queue.startGroup ref (before ++ after) := by
  have cached := retired.cacheTaskFailures (before ++ after)
  simp only [State.startGroup, retired.cacheTaskFailures_drop before after errors]
  split
  · rfl
  · rename_i node found
    split
    · congr 1
      exact startTasks_dropFailure _ occurrence node.tasks
        (cached.unlinked node (List.mem_of_find?_eq_some found)) before after errors
    · rfl

/-- Released work sees the same startup results after a retired failure entry is removed. -/
theorem State.RetiredTask.startNewWork_dropFailure {queue occurrence}
    (retired : State.RetiredTask queue occurrence) (released : NewWork)
    (before after : List (Occurrence × Nat)) (errors : Nat)
    : queue.startNewWork released (before ++ (occurrence, errors) :: after)
      = queue.startNewWork released (before ++ after) := by
  let step (available : List (Occurrence × Nat))
      (acc : State × List GroupFailureEvent) (ref : Nat) :=
    let next := acc.1.startGroup ref available
    (next.1, acc.2 ++ next.2)
  have groups (refs : NodeRefs) (acc : State × List GroupFailureEvent)
      (prior : acc.1.RetiredTask occurrence)
      : refs.foldl (step (before ++ (occurrence, errors) :: after)) acc
        = refs.foldl (step (before ++ after)) acc := by
    induction refs generalizing acc with
    | nil => rfl
    | cons ref rest ih =>
        simp only [List.foldl_cons, step, prior.startGroup_dropFailure ref before after errors]
        exact ih _ (prior.startGroup ref (before ++ after))
  unfold State.startNewWork
  dsimp only
  rw [groups _ _ ⟨retired.missing, retired.unlinked⟩]

/-- Ready draining cannot observe a failure whose task is already globally retired. -/
theorem State.RetiredTask.drainReadyGroups_dropFailure {queue occurrence}
    (retired : State.RetiredTask queue occurrence) (fuel : Nat)
    (before after : List (Occurrence × Nat)) (errors : Nat)
    : State.drainReadyGroups.go (before ++ (occurrence, errors) :: after) fuel queue
      = State.drainReadyGroups.go (before ++ after) fuel queue := by
  induction fuel generalizing queue with
  | zero => rfl
  | succ fuel ih =>
      simp only [State.drainReadyGroups.go]
      split
      · rfl
      · rename_i node selected
        have finished := retired.finishGroupSuccess node
        rw [finished.startNewWork_dropFailure _ before after errors]
        rw [ih (finished.startNewWork _ (before ++ after))]

/-- A fresh task-success payload cannot make a retired failure relevant again. -/
theorem State.RetiredTask.taskSuccess_dropFailure {queue occurrence}
    (retired : State.RetiredTask queue occurrence) (source : Occurrence)
    (result : TaskResult)
    (fresh : ∀ task ∈ result.work.tasks, occurrence ≠ task.occurrence)
    (before after : List (Occurrence × Nat)) (errors : Nat)
    : queue.taskSuccess source result (before ++ (occurrence, errors) :: after)
      = queue.taskSuccess source result (before ++ after) := by
  cases found : queue.taskNode? source with
  | none => simp only [State.taskSuccess, found]
  | some node =>
      rw [queue.taskSuccess_eq source result node found (before ++ (occurrence, errors) :: after),
        queue.taskSuccess_eq source result node found (before ++ after)]
      dsimp only
      have prepared := (retired.putTaskNode {node with value := some result.value})
        |>.maybeIntegrateWork result.work fresh (some source)
      have released := prepared.successGroupFold node.task.groups [] {}
      rw [released.startNewWork_dropFailure _ before after errors]
      unfold State.drainReadyGroups
      rw [(released.startNewWork _ (before ++ after)).drainReadyGroups_dropFailure
        _ before after errors]

private abbrev ItemAcc :=
  State
  × List Execution.DeliveryNode
  × List Execution.DeliveryNode
  × List Execution.StreamItemValue
  × List GroupFailureEvent

private theorem itemFold_dropFailure (items : List StreamItem) (acc : ItemAcc)
    {occurrence} (retired : acc.1.RetiredTask occurrence)
    (fresh : ∀ item ∈ items, ∀ task ∈ item.work.tasks, occurrence ≠ task.occurrence)
    (before after : List (Occurrence × Nat)) (errors : Nat)
    : items.foldl
        (fun acc item =>
          streamItemStep acc item (before ++ (occurrence, errors) :: after))
        acc
      = items.foldl (fun acc item => streamItemStep acc item (before ++ after)) acc := by
  induction items generalizing acc with
  | nil => rfl
  | cons item rest ih =>
      have integrated := retired.maybeIntegrateWork item.work (fresh item List.mem_cons_self)
      have pruned := integrated.pruneEmptyGroups
        (acc.1.maybeIntegrateWork item.work).2.newGroups
      have step : streamItemStep acc item (before ++ (occurrence, errors) :: after)
          = streamItemStep acc item (before ++ after) := by
        simp only [streamItemStep, pruned.startNewWork_dropFailure _ before after errors]
      rw [List.foldl_cons, List.foldl_cons, step]
      exact ih _ (pruned.startNewWork _ (before ++ after))
        (fun next member => fresh next (List.mem_cons_of_mem _ member))

/-- A whole receipt sees identical startup and drain results after dropping a retired cause. -/
theorem State.RetiredTask.streamItems_dropFailure {queue occurrence stream items}
    (retired : State.RetiredTask queue occurrence)
    (fresh : ∀ item ∈ items, ∀ task ∈ item.work.tasks, occurrence ≠ task.occurrence)
    (before after : List (Occurrence × Nat)) (errors : Nat)
    : queue.streamItems stream items (before ++ (occurrence, errors) :: after)
      = queue.streamItems stream items (before ++ after) := by
  rw [queue.streamItems_eq stream items (before ++ (occurrence, errors) :: after),
    queue.streamItems_eq stream items (before ++ after)]
  split
  · rfl
  · rw [itemFold_dropFailure items (queue, [], [], [], []) retired fresh before after errors]
    have prepared : (queue.preparedStreamItems items (before ++ after)).RetiredTask occurrence := by
      apply State.preparedStreamItems_preserves (fun q => q.RetiredTask occurrence)
        retired items (before ++ after)
      intro current item member prior
      exact ((prior.maybeIntegrateWork item.work (fresh item member)).pruneEmptyGroups _)
        |>.startNewWork _ (before ++ after)
    unfold State.preparedStreamItems at prepared
    dsimp only
    unfold State.drainReadyGroups
    rw [prepared.drainReadyGroups_dropFailure _ before after errors]

/-- Dispatch preserves exact queue state and both output channels when a retired snapshot
entry is removed. The supplied child work must not reuse the retired occurrence.
-/
theorem State.RetiredTask.handleGraphEvent_dropFailure {queue occurrence event}
    (retired : State.RetiredTask queue occurrence)
    (fresh : ∀ child ∈ event.childTasks, occurrence ≠ child.occurrence)
    (before after : List (Occurrence × Nat)) (errors : Nat)
    : queue.handleGraphEvent event (before ++ (occurrence, errors) :: after)
      = queue.handleGraphEvent event (before ++ after) := by
  have cached := retired.cacheTaskFailures (before ++ after)
  simp only [State.handleGraphEvent, retired.cacheTaskFailures_drop before after errors]
  cases event with
  | taskSuccess source result =>
      exact cached.taskSuccess_dropFailure source result fresh before after errors
  | streamItems stream items =>
      exact cached.streamItems_dropFailure
        (fun item member task listed => fresh task (List.mem_flatMap.mpr ⟨item, member, listed⟩))
        before after errors
  | taskFailure | streamSuccess | streamFailure | groupFailure => rfl

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
