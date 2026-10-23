import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationRelease
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PendingDebtBound

/-! Fresh delayed task starts commute with successful flushing of settled memberships. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue
open GraphQL.IncrementalDelivery.Execution (ExecutionGroupValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics (Occurrence NodeRefs)

-----------------------------------------------------------------------------------------
-- Exact lookups and removal outside the delayed active subset
-----------------------------------------------------------------------------------------

/-- Completing a different task cannot change even an absent first-match lookup. -/
theorem activateRegisteredTask_lookup_other (queue : ReferenceWorkQueue.State)
    (task : ReferenceWorkQueue.Task) (occurrence : Occurrence)
    (different : task.occurrence ≠ occurrence)
    : (activateRegisteredTask queue task).taskNode? occurrence
      = queue.taskNode? occurrence := by
  unfold activateRegisteredTask
  split
  · rfl
  · change (queue.taskNodes ++ ([{ task }] : List ReferenceWorkQueue.TaskNode)).find?
      (fun node => node.task.occurrence == occurrence) = _
    rw [List.find?_append]
    have excluded : (task.occurrence == occurrence) = false :=
      Bool.eq_false_iff.mpr (fun same => different
        ((ReferenceWorkQueue.occurrence_beq_iff_eq _ _).mp same))
    simp only [List.find?_cons, excluded,
      List.find?_nil, Option.or_none]
    rfl

/-- Completing the active subset preserves the exact lookup of an unlisted occurrence. -/
theorem activateRegisteredTasks_lookup_other (queue : ReferenceWorkQueue.State)
    (tasks : List ReferenceWorkQueue.Task) (occurrence : Occurrence)
    (different : ∀ task ∈ tasks, task.occurrence ≠ occurrence)
    : (activateRegisteredTasks queue tasks).taskNode? occurrence
      = queue.taskNode? occurrence := by
  induction tasks generalizing queue with
  | nil => rfl
  | cons task rest ih =>
      change (activateRegisteredTasks (activateRegisteredTask queue task) rest).taskNode? occurrence = _
      rw [ih _ (fun child member => different child (List.mem_cons_of_mem task member)),
        activateRegisteredTask_lookup_other queue task occurrence (different task List.mem_cons_self)]

private theorem activateRegisteredTask_removeTask (queue : ReferenceWorkQueue.State)
    (task : ReferenceWorkQueue.Task) (occurrence : Occurrence)
    (different : task.occurrence ≠ occurrence)
    : activateRegisteredTask (queue.removeTask occurrence) task
      = (activateRegisteredTask queue task).removeTask occurrence := by
  unfold activateRegisteredTask
  rw [ReferenceWorkQueue.State.removeTask_lookup_other queue different]
  split
  · rfl
  · simp only [ReferenceWorkQueue.State.removeTask, List.filter_append, List.filter_cons,
      List.filter_nil]
    have excluded : (task.occurrence == occurrence) = false :=
      Bool.eq_false_iff.mpr (fun same => different
        ((ReferenceWorkQueue.occurrence_beq_iff_eq _ _).mp same))
    simp only [bne, excluded, Bool.not_false, ↓reduceIte]

/-- Removing an unlisted settled task commutes with completing the delayed active subset. -/
theorem activateRegisteredTasks_removeTask (queue : ReferenceWorkQueue.State)
    (tasks : List ReferenceWorkQueue.Task) (occurrence : Occurrence)
    (different : ∀ task ∈ tasks, task.occurrence ≠ occurrence)
    : activateRegisteredTasks (queue.removeTask occurrence) tasks
      = (activateRegisteredTasks queue tasks).removeTask occurrence := by
  induction tasks generalizing queue with
  | nil => rfl
  | cons task rest ih =>
      change activateRegisteredTasks (activateRegisteredTask (queue.removeTask occurrence) task) rest = _
      rw [activateRegisteredTask_removeTask queue task occurrence (different task List.mem_cons_self)]
      exact ih _ (fun child member => different child (List.mem_cons_of_mem task member))

/-- A group-record update commutes with completion of the active task subset. -/
theorem activateRegisteredTasks_putGroupNode (queue : ReferenceWorkQueue.State)
    (tasks : List ReferenceWorkQueue.Task) (group : ReferenceWorkQueue.GroupNode)
    : activateRegisteredTasks (queue.putGroupNode group) tasks
      = (activateRegisteredTasks queue tasks).putGroupNode group := by
  rw [activateRegisteredTasks_nodes, activateRegisteredTasks_nodes]
  rfl

-----------------------------------------------------------------------------------------
-- Flushing a group disjoint from the delayed active subset
-----------------------------------------------------------------------------------------

private theorem flushGroupTask_activation
    (acc : ReferenceWorkQueue.State × List ExecutionGroupValue × NodeRefs)
    (tasks : List ReferenceWorkQueue.Task) (occurrence : Occurrence)
    (different : ∀ task ∈ tasks, task.occurrence ≠ occurrence)
    : ReferenceWorkQueue.flushGroupTask
        (activateRegisteredTasks acc.1 tasks, acc.2) occurrence
      = (
        activateRegisteredTasks (ReferenceWorkQueue.flushGroupTask acc occurrence).1
          tasks,
        (ReferenceWorkQueue.flushGroupTask acc occurrence).2
      ) := by
  unfold ReferenceWorkQueue.flushGroupTask
  rw [activateRegisteredTasks_lookup_other acc.1 tasks occurrence different]
  cases found : acc.1.taskNode? occurrence with
  | none => rfl
  | some node =>
      simp only
      rw [activateRegisteredTasks_removeTask acc.1 tasks occurrence different]

private theorem flushGroupTasks_activation
    (acc : ReferenceWorkQueue.State × List ExecutionGroupValue × NodeRefs)
    (tasks : List ReferenceWorkQueue.Task) (occurrences : List Occurrence)
    (different : ∀ task ∈ tasks, task.occurrence ∉ occurrences)
    : occurrences.foldl ReferenceWorkQueue.flushGroupTask
        (activateRegisteredTasks acc.1 tasks, acc.2)
      = (
        activateRegisteredTasks
          (occurrences.foldl ReferenceWorkQueue.flushGroupTask acc).1 tasks,
        (occurrences.foldl ReferenceWorkQueue.flushGroupTask acc).2
      ) := by
  induction occurrences generalizing acc with
  | nil => rfl
  | cons occurrence rest ih =>
      rw [List.foldl_cons, List.foldl_cons, flushGroupTask_activation acc tasks occurrence
        (fun task member same => different task member (List.mem_cons.mpr (.inl same)))]
      exact ih _ (fun task member later => different task member (List.mem_cons_of_mem _ later))

private def finishFlushedGroup (group : ReferenceWorkQueue.GroupNode)
    (flushed : ReferenceWorkQueue.State × List ExecutionGroupValue × NodeRefs)
    : ReferenceWorkQueue.State × List WorkQueueEvent × ReferenceWorkQueue.NewWork :=
  let current : ReferenceWorkQueue.State :=
    {
      flushed.1 with
        groupNodes :=
          flushed.1.groupNodes.filter
            (fun node => node.group.node.ref != group.group.node.ref)
        rootGroups := flushed.1.rootGroups.filter (· != group.group.node.ref)
    }
  let children :=
    group.childGroups.filterMap
      (fun key => (current.groupNode? key).map (fun node => node.group.node))
  let pruned := current.pruneEmptyGroups children
  let streams :=
    flushed.2.2.filterMap
      (fun key => (pruned.1.stream? key).map ReferenceWorkQueue.Stream.node)
  let values :=
    if flushed.2.1.isEmpty then [] else [.groupValues group.group.node flushed.2.1]
  (
    pruned.1,
    values ++ [.groupSuccess group.group.node pruned.2 streams],
    ⟨pruned.2, streams⟩
  )

/-- A successful flush commutes with delayed starts outside its task memberships.
Witness: exact lookup/removal correspondence in the flush, followed by group-only shell
pruning. Values, child-stream release, wire events and release order are retained exactly.
-/
theorem activateRegisteredTasks_finishGroupSuccess (queue : ReferenceWorkQueue.State)
    (tasks : List ReferenceWorkQueue.Task) (group : ReferenceWorkQueue.GroupNode)
    (different : ∀ task ∈ tasks, task.occurrence ∉ group.tasks)
    : (activateRegisteredTasks queue tasks).finishGroupSuccess group
      = (
        activateRegisteredTasks (queue.finishGroupSuccess group).1 tasks,
        (queue.finishGroupSuccess group).2
      ) := by
  have flush := flushGroupTasks_activation (queue, [], []) tasks group.tasks different
  let flushed := group.tasks.foldl ReferenceWorkQueue.flushGroupTask (queue, [], [])
  let current : ReferenceWorkQueue.State :=
    { flushed.1 with
      groupNodes := flushed.1.groupNodes.filter (fun node => node.group.node.ref != group.group.node.ref)
      rootGroups := flushed.1.rootGroups.filter (· != group.group.node.ref) }
  let children := group.childGroups.filterMap
    (fun key => (current.groupNode? key).map (fun node => node.group.node))
  have records :
      { activateRegisteredTasks flushed.1 tasks with
        groupNodes := (activateRegisteredTasks flushed.1 tasks).groupNodes.filter
          (fun node => node.group.node.ref != group.group.node.ref)
        rootGroups := (activateRegisteredTasks flushed.1 tasks).rootGroups.filter
          (· != group.group.node.ref) }
      = activateRegisteredTasks current tasks := by
    rw [activateRegisteredTasks_nodes, activateRegisteredTasks_nodes]
  have pruning := activateRegisteredTasks_pruneEmptyGroups current children tasks
  unfold ReferenceWorkQueue.State.finishGroupSuccess
  simp only
  change finishFlushedGroup group (group.tasks.foldl ReferenceWorkQueue.flushGroupTask
      (activateRegisteredTasks queue tasks, [], []))
    = (activateRegisteredTasks (finishFlushedGroup group flushed).1 tasks,
        (finishFlushedGroup group flushed).2)
  rw [flush]
  unfold finishFlushedGroup
  dsimp only
  rw [records]
  have core (current : ReferenceWorkQueue.State)
      : registrationCore (activateRegisteredTasks current tasks) = registrationCore current := by
    rw [activateRegisteredTasks_nodes]
    rfl
  have groups : (activateRegisteredTasks current tasks).groupNodes = current.groupNodes := by
    have same := congrArg ReferenceWorkQueue.State.groupNodes (core current)
    exact same
  have lookup (key : Nat) : (activateRegisteredTasks current tasks).groupNode? key
      = current.groupNode? key := by
    change ((activateRegisteredTasks current tasks).groupNodes.find? _) = _
    rw [groups]
    rfl
  simp only [lookup]
  rw [← pruning]
  have streams : (activateRegisteredTasks (current.pruneEmptyGroups children).1 tasks).streams
      = (current.pruneEmptyGroups children).1.streams := by
    have same := congrArg ReferenceWorkQueue.State.streams (core (current.pruneEmptyGroups children).1)
    exact same
  have streamLookup (key : Nat)
      : (activateRegisteredTasks (current.pruneEmptyGroups children).1 tasks).stream? key
        = (current.pruneEmptyGroups children).1.stream? key := by
    change ((activateRegisteredTasks (current.pruneEmptyGroups children).1 tasks).streams.find? _) = _
    rw [streams]
    rfl
  simp only [streamLookup]
  rfl

-----------------------------------------------------------------------------------------
-- Pending debt justifies exact completion through the single-pass owner fold
-----------------------------------------------------------------------------------------

/-- Complete only the queue component of the shared success accumulator. -/
def completeSuccessAcc
    (acc : ReferenceWorkQueue.State × List WorkQueueEvent × ReferenceWorkQueue.NewWork)
    (tasks : List ReferenceWorkQueue.Task)
    : ReferenceWorkQueue.State × List WorkQueueEvent × ReferenceWorkQueue.NewWork :=
  (activateRegisteredTasks acc.1 tasks, acc.2)

private theorem activation_groupNode? (queue : ReferenceWorkQueue.State)
    (tasks : List ReferenceWorkQueue.Task) (key : Nat)
    : (activateRegisteredTasks queue tasks).groupNode? key = queue.groupNode? key := by
  rw [activateRegisteredTasks_nodes]
  rfl

private theorem activation_rootGroups (queue : ReferenceWorkQueue.State)
    (tasks : List ReferenceWorkQueue.Task)
    : (activateRegisteredTasks queue tasks).rootGroups = queue.rootGroups := by
  rw [activateRegisteredTasks_nodes]

private theorem putGroupNode_rootGroups (queue : ReferenceWorkQueue.State)
    (node : ReferenceWorkQueue.GroupNode)
    : (queue.putGroupNode node).rootGroups = queue.rootGroups :=
  rfl

/-- Completing fresh active tasks before or after successful owner settlement is exact.
Witness: pending debt reserves each remaining decrement. At a zero-counter flush every
membership is settled, so none of the fresh active tasks can be selected or removed.
The theorem retains the complete kernel, ordered wire events and pending releases.
-/
theorem successGroupFold_activateRegisteredTasks
    (settled : List Occurrence) (tasks : List ReferenceWorkQueue.Task)
    (fresh : ∀ task ∈ tasks, task.occurrence ∉ settled)
    (groups : List Execution.DeliveryNode)
    (unique : (groups.map Execution.DeliveryNode.ref).Nodup)
    (acc : ReferenceWorkQueue.State × List WorkQueueEvent × ReferenceWorkQueue.NewWork)
    (keys : acc.1.GroupRefsUnique)
    (bounded
      : acc.1.PendingDebtBound (fun _ => True) settled
          (groups.map Execution.DeliveryNode.ref))
    : groups.foldl ReferenceWorkQueue.successGroupStep (completeSuccessAcc acc tasks)
      = completeSuccessAcc (groups.foldl ReferenceWorkQueue.successGroupStep acc)
          tasks := by
  induction groups generalizing acc with
  | nil => rfl
  | cons group rest ih =>
      obtain ⟨absent, tailUnique⟩ := List.nodup_cons.mp unique
      obtain ⟨queue, events, released⟩ := acc
      let original : ReferenceWorkQueue.State × List WorkQueueEvent × ReferenceWorkQueue.NewWork :=
        (queue, events, released)
      have step :
          (ReferenceWorkQueue.successGroupStep original group).1.GroupRefsUnique
          ∧ (ReferenceWorkQueue.successGroupStep original group).1.PendingDebtBound
              (fun _ => True) settled (rest.map Execution.DeliveryNode.ref)
          ∧ ReferenceWorkQueue.successGroupStep (completeSuccessAcc original tasks) group
              = completeSuccessAcc (ReferenceWorkQueue.successGroupStep original group) tasks := by
        cases found : queue.groupNode? group.ref with
        | none =>
            have missing := bounded.skipMissing found
            simp only [ReferenceWorkQueue.successGroupStep, completeSuccessAcc,
              activation_groupNode?, found, original]
            exact ⟨keys, missing, True.intro⟩
        | some node =>
            let updated : ReferenceWorkQueue.GroupNode := { node with pending := node.pending - 1 }
            let next := queue.putGroupNode updated
            have nextKeys := keys.putGroupNode updated
            have nextBound := bounded.decrement keys absent found
            have member : updated ∈ next.groupNodes := by
              exact List.mem_map.mpr ⟨node, List.mem_of_find?_eq_some found, by simp [updated]⟩
            by_cases ready : (next.rootGroups.contains group.ref
                && updated.pending == 0) = true
            · have zero : updated.pending = 0 :=
                beq_iff_eq.mp (Bool.and_eq_true_iff.mp ready).2
              have all := nextBound.allSettled member True.intro zero
              have different : ∀ task ∈ tasks, task.occurrence ∉ updated.tasks := by
                intro task included linked
                exact fresh task included (all task.occurrence linked)
              have closed := activateRegisteredTasks_finishGroupSuccess next tasks updated different
              change (queue.rootGroups.contains group.ref && node.pending - 1 == 0) = true at ready
              dsimp only [next, updated] at closed
              simp only [ReferenceWorkQueue.successGroupStep, completeSuccessAcc, original,
                activation_groupNode?, found, ← activateRegisteredTasks_putGroupNode,
                activation_rootGroups, putGroupNode_rootGroups, ready, ↓reduceIte, closed]
              exact ⟨nextKeys.finishGroupSuccess updated,
                nextBound.finishGroupSuccess updated all, True.intro⟩
            · change ¬(queue.rootGroups.contains group.ref && node.pending - 1 == 0) = true at ready
              simp only [ReferenceWorkQueue.successGroupStep, completeSuccessAcc, original,
                activation_groupNode?, found, ← activateRegisteredTasks_putGroupNode,
                activation_rootGroups, putGroupNode_rootGroups, ready, Bool.false_eq_true, ↓reduceIte]
              exact ⟨nextKeys, nextBound, True.intro⟩
      rw [List.foldl_cons, List.foldl_cons, step.2.2]
      exact ih tailUnique _ step.1 step.2.1

end GraphQL.IncrementalDelivery.AlternativeWorkQueue
