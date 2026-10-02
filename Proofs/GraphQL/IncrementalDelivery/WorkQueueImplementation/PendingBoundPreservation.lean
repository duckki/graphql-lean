import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PendingDebtBound
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PendingCancellation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ActiveLinks
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ReadyDrain

/-! Pending lower bounds survive active settlements, cancellation, and release draining. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (StreamItemValue)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Registration may overcount, but never undercounts unsettled memberships
-----------------------------------------------------------------------------------------

/-- A balanced replacement preserves the selected groups' pending lower bound.
Witness: each updated record is either the replacement or an unchanged earlier node.
-/
theorem State.PendingBound.putGroupNode {queue : State} {eligible settled}
    (bounded : queue.PendingBound eligible settled) (updated : GroupNode)
    (balanced
      : eligible updated.group.node.key
        → unsettledCount updated.tasks settled ≤ updated.pending)
    : (queue.putGroupNode updated).PendingBound eligible settled := by
  intro node member relevant
  obtain ⟨old, oldMember, same⟩ := List.mem_map.mp member
  split at same
  · subst node
    exact balanced relevant
  · subst node
    exact bounded old oldMember relevant

/-- An empty group shell has a safe zero counter.
Witness: existing groups retain their bound and the new group has no memberships.
-/
theorem State.PendingBound.addGroup {queue : State} {eligible settled}
    (bounded : queue.PendingBound eligible settled) (group : Group)
    : (queue.addGroup group).PendingBound eligible settled := by
  unfold State.addGroup
  split
  · exact bounded
  · dsimp only
    split
    · exact bounded
    · intro node member relevant
      rcases List.mem_append.mp member with earlier | new
      · exact bounded node earlier relevant
      · obtain rfl := List.mem_singleton.mp new
        simp [unsettledCount]

/-- Group registration and parent-link installation preserve pending lower bounds.
Witness: two fold inductions; parent links change neither counters nor task memberships.
-/
theorem State.PendingBound.addGroups {queue : State} {eligible settled}
    (bounded : queue.PendingBound eligible settled) (groups : List Group)
    : (queue.addGroups groups).1.PendingBound eligible settled := by
  let linkStep (current : State) (group : Group) : State :=
    match group.parent with
    | none => current
    | some parent =>
        match current.groupNode? parent with
        | none => current
        | some node =>
            let children := if node.childGroups.contains group.node.key then
              node.childGroups else node.childGroups ++ [group.node.key]
            current.putGroupNode { node with childGroups := children }
  have linkBound (current : State) (group : Group)
      (prior : current.PendingBound eligible settled)
      : (linkStep current group).PendingBound eligible settled := by
    unfold linkStep
    split
    · exact prior
    · split
      · exact prior
      · rename_i node found
        exact prior.putGroupNode _ (prior node (List.mem_of_find?_eq_some found))
  have linkFold (more : List Group) (current : State)
      (prior : current.PendingBound eligible settled)
      : (more.foldl linkStep current).PendingBound eligible settled := by
    induction more generalizing current with
    | nil => exact prior
    | cons group rest ih => exact ih _ (linkBound current group prior)
  have registered (more : List Group) :
      (more.foldl State.addGroup queue).PendingBound eligible settled := by
    induction more generalizing queue with
    | nil => exact bounded
    | cons group rest ih => exact ih (bounded.addGroup group)
  let fresh := groups.filter (fun group =>
    !queue.registeredGroups.contains group.node.key
      && (queue.groupNode? group.node.key).isNone)
  change (fresh.foldl linkStep (fresh.foldl State.addGroup queue)).PendingBound eligible settled
  exact linkFold fresh _ (registered fresh)

/-- Registering one membership adds at most one unsettled token.
Witness: the filter of a singleton has length at most one. No freshness assumption is
needed for a lower bound, although exact-count registration requires freshness.
-/
private theorem unsettledCount_append_le (tasks settled : List Occurrence)
    (occurrence : Occurrence)
    : unsettledCount (tasks ++ [occurrence]) settled
      ≤ unsettledCount tasks settled + 1 := by
  classical
  unfold unsettledCount
  rw [List.filter_append, List.length_append]
  exact Nat.add_le_add_left (List.length_filter_le _ _) _

/-- Task registration preserves lower bounds even for an already-settled task.
Witness: duplicate links do nothing; a new link increments the counter by one and its
unsettled-membership count by at most one.
-/
theorem State.PendingBound.addTask {queue : State} {eligible settled}
    (bounded : queue.PendingBound eligible settled) (task : Task)
    : (queue.addTask task).PendingBound eligible settled := by
  let registered : State := { queue with tasks := queue.tasks ++ [task] }
  let step (current : State) (group : Execution.DeliveryNode) : State :=
    match current.groupNode? group.key with
    | none => current
    | some node =>
        if node.tasks.contains task.occurrence then current
        else current.putGroupNode
          { node with tasks := node.tasks ++ [task.occurrence], pending := node.pending + 1 }
  have stepBound (current : State) (group : Execution.DeliveryNode)
      (prior : current.PendingBound eligible settled)
      : (step current group).PendingBound eligible settled := by
    unfold step
    split
    · exact prior
    · rename_i node found
      split
      · exact prior
      · apply prior.putGroupNode
        intro relevant
        exact Nat.le_trans (unsettledCount_append_le _ _ _)
          (Nat.add_le_add_right (prior node (List.mem_of_find?_eq_some found) relevant) 1)
  have foldBound (groups : List Execution.DeliveryNode) (current : State)
      (prior : current.PendingBound eligible settled)
      : (groups.foldl step current).PendingBound eligible settled := by
    induction groups generalizing current with
    | nil => exact prior
    | cons group rest ih => exact ih _ (stepBound current group prior)
  let current := task.groups.foldl step registered
  have currentBound : current.PendingBound eligible settled :=
    foldBound task.groups registered bounded
  change (if task.groups.any (fun group => current.rootGroups.contains group.key)
      && (current.taskNode? task.occurrence).isNone then
      { current with taskNodes := current.taskNodes ++ [{ task }] }
    else current).PendingBound eligible settled
  split <;> exact currentBound

/-- Stream registration changes no group counter or membership.
Witness: both producer branches leave the group-node list unchanged.
-/
theorem State.PendingBound.addStreams {queue : State} {eligible settled}
    (bounded : queue.PendingBound eligible settled) (streams : List Stream)
    (parentTask : Option Occurrence)
    : (queue.addStreams streams parentTask).1.PendingBound eligible settled := by
  cases parentTask with
  | none => exact bounded
  | some occurrence =>
      simp only [State.addStreams]
      split <;> exact bounded

/-- Child-work integration preserves the lower bound without source-freshness premises.
Witness: group and task registration preserve it independently, as does stream setup.
-/
theorem State.PendingBound.maybeIntegrateWork {queue : State} {eligible settled}
    (bounded : queue.PendingBound eligible settled) (work : Work)
    (parentTask : Option Occurrence := none)
    : (queue.maybeIntegrateWork work parentTask).1.PendingBound eligible settled := by
  have taskFold (tasks : List Task) (current : State)
      (prior : current.PendingBound eligible settled)
      : (tasks.foldl State.addTask current).PendingBound eligible settled := by
    induction tasks generalizing current with
    | nil => exact prior
    | cons task rest ih => exact ih _ (prior.addTask task)
  exact (taskFold work.tasks _ (bounded.addGroups work.groups)).addStreams _ parentTask

-----------------------------------------------------------------------------------------
-- Release and draining only flush settled memberships
-----------------------------------------------------------------------------------------

/-- Pruning retains unchanged bounded counters.
Witness: view a bound as debt with no remaining decrement and reuse pruning preservation.
-/
theorem State.PendingBound.pruneEmptyGroups {queue : State} {eligible settled}
    (bounded : queue.PendingBound eligible settled) (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.PendingBound eligible settled :=
  ((State.pendingDebtBound_nil.mpr bounded).pruneEmptyGroups groups).toBound

/-- Flushing only settled tasks preserves pending lower bounds.
Witness: the debt-bound flush theorem with an empty decrement suffix.
-/
theorem State.PendingBound.finishGroupSuccess {queue : State} {eligible settled}
    (bounded : queue.PendingBound eligible settled) (group : GroupNode)
    (all : ∀ occurrence ∈ group.tasks, occurrence ∈ settled)
    : (queue.finishGroupSuccess group).1.PendingBound eligible settled :=
  ((State.pendingDebtBound_nil.mpr bounded).finishGroupSuccess group all).toBound

/-- Failed-group removal cannot undercount any surviving group.
Witness: failure only filters group records, preserving their counters and memberships.
-/
theorem State.PendingBound.removeGroup {queue : State} {eligible settled}
    (bounded : queue.PendingBound eligible settled) (key : Nat)
    : (queue.removeGroup key).PendingBound eligible settled :=
  ((State.pendingDebtBound_nil.mpr bounded).removeGroup key).toBound

/-- Work activation leaves the group-node map, hence every pending bound, unchanged.
Witness: the independently proved activation group-core equation.
-/
theorem State.PendingBound.startNewWork {queue : State} {eligible settled}
    (bounded : queue.PendingBound eligible settled) (work : NewWork)
    : (queue.startNewWork work).PendingBound eligible settled := by
  intro node member relevant
  rw [(queue.startNewWork_groupCore work).1] at member
  exact bounded node member relevant

/-- A lower bound on all groups suffices for safe recursive draining.
Witness: a selected zero counter certifies settled memberships; success flush, failure
removal, and child activation preserve the bound for subsequent drain iterations.
-/
theorem State.PendingBound.drainReadyGroups {queue : State} {settled}
    (bounded : queue.PendingBound (fun _ => True) settled)
    : queue.drainReadyGroups.1.PendingBound (fun _ => True) settled := by
  apply State.drainReadyGroups_preserves
    (fun state => state.PendingBound (fun _ => True) settled)
    (fun _ node prior member _ _ zero =>
      (prior.finishGroupSuccess node (prior.allSettled member trivial zero)).startNewWork _)
    (fun _ node _ prior _ _ _ => prior.removeGroup node.group.node.key) bounded

-----------------------------------------------------------------------------------------
-- Both branches of each executable handler preserve counter safety
-----------------------------------------------------------------------------------------

/-- Task failure preserves the lower bound whether the task is active or cancelled.
Witness: ignored tasks only remove memberships; active tasks reserve and discharge one
decrement per distinct owner. The healthy-owner guard is not an assumption of this lemma.
-/
theorem State.PendingBound.taskFailure {queue : State} {settled}
    (bounded : queue.PendingBound (fun _ => True) settled)
    (keyUnique : queue.GroupKeysUnique) (taskUnique : queue.TaskMembershipsUnique)
    (occurrence : Occurrence) (errors : Nat)
    (taskNode : TaskNode) (found : queue.taskNode? occurrence = some taskNode)
    (fresh : occurrence ∉ settled)
    (uniqueContributors : (taskNode.task.groups.map Execution.DeliveryNode.key).Nodup)
    (owned
      : queue.OwnedExactlyBy occurrence
          (taskNode.task.groups.map Execution.DeliveryNode.key))
    : (queue.taskFailure occurrence errors).1.PendingBound (fun _ => True)
        (occurrence :: settled) := by
  cases active : queue.taskHasHealthyOwner taskNode.task with
  | false => exact bounded.taskFailure_of_noHealthyOwner found active errors
  | true =>
      have debt := bounded.beginSettlement taskUnique (fun node member _ => owned node member)
        fresh
      have facts := failureGroupFold_preservesBound (fun _ => True) (occurrence :: settled)
        State.GroupKeysUnique (fun _ valid => valid)
        (fun _ _ _ valid _ => valid.putGroupNode _)
        (fun _ key valid => valid.removeGroup key)
        errors taskNode.task.groups uniqueContributors (queue.removeTask occurrence, [])
        (keyUnique.removeTask occurrence) (debt.removeTask occurrence (by simp))
      rw [queue.taskFailure_eq occurrence errors taskNode found]
      simpa only [active, Bool.not_true, Bool.false_eq_true, ↓reduceIte] using facts.2

/-- Task success preserves the bound through child integration, owner release, and drain.
Witness: guard case analysis followed by bounded-debt induction on the original
single-pass owner loop. Ignored successes need not integrate their supplied child work.
-/
theorem State.PendingBound.taskSuccess {queue : State} {settled}
    (bounded : queue.PendingBound (fun _ => True) settled)
    (keyUnique : queue.GroupKeysUnique) (taskUnique : queue.TaskMembershipsUnique)
    (occurrence : Occurrence) (result : TaskResult)
    (taskNode : TaskNode) (found : queue.taskNode? occurrence = some taskNode)
    (fresh : occurrence ∉ settled)
    (uniqueContributors : (taskNode.task.groups.map Execution.DeliveryNode.key).Nodup)
    (owned
      : ((queue.putTaskNode
            { taskNode with value := some result.value }).maybeIntegrateWork
          result.work (some occurrence)).1.OwnedExactlyBy
          occurrence (taskNode.task.groups.map Execution.DeliveryNode.key))
    : (queue.taskSuccess occurrence result).1.PendingBound (fun _ => True)
        (occurrence :: settled) := by
  cases active : queue.taskHasHealthyOwner taskNode.task with
  | false => exact bounded.taskSuccess_of_noHealthyOwner found active result
  | true =>
      let withValue := queue.putTaskNode { taskNode with value := some result.value }
      have valueBound : withValue.PendingBound (fun _ => True) settled := bounded
      have valueKeys : withValue.GroupKeysUnique := keyUnique
      have valueTasks : withValue.TaskMembershipsUnique := taskUnique
      let integrated := (withValue.maybeIntegrateWork result.work (some occurrence)).1
      have integratedBound : integrated.PendingBound (fun _ => True) settled :=
        valueBound.maybeIntegrateWork result.work (some occurrence)
      have integratedKeys : integrated.GroupKeysUnique :=
        valueKeys.maybeIntegrateWork result.work (some occurrence)
      have integratedTasks : integrated.TaskMembershipsUnique :=
        valueTasks.maybeIntegrateWork result.work (some occurrence)
      have debt := integratedBound.beginSettlement integratedTasks
        (fun node member _ => owned node member) fresh
      have facts := successGroupFold_preservesBound (fun _ => True) (occurrence :: settled)
        State.GroupKeysUnique (fun _ valid => valid) (by intros; trivial)
        (fun _ _ valid _ => valid.putGroupNode _)
        (fun _ node _ valid _ _ _ _ _ => valid.finishGroupSuccess node)
        taskNode.task.groups uniqueContributors (integrated, [], {}) integratedKeys debt
      rw [queue.taskSuccess_eq occurrence result taskNode found]
      simp only [active, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      exact (facts.2.startNewWork _).drainReadyGroups

/-- Stream item delivery preserves the lower bound through every child registration.
Witness: item-fold induction followed by safe release draining; unlike exact accounting,
the bound requires no freshness premise on the newly integrated tasks.
-/
theorem State.PendingBound.streamItems {queue : State} {settled}
    (bounded : queue.PendingBound (fun _ => True) settled)
    (stream : Execution.DeliveryNode) (items : List StreamItem)
    : (queue.streamItems stream items).1.PendingBound (fun _ => True) settled := by
  let step (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue) (item : StreamItem) :=
    let (current, groups, streams, values) := acc
    let (integrated, newWork) := current.maybeIntegrateWork item.work
    let (pruned, nonempty) := integrated.pruneEmptyGroups newWork.newGroups
    (pruned.startNewWork { newWork with newGroups := nonempty }, groups ++ nonempty,
      streams ++ newWork.newStreams, values ++ [item.value])
  have stepBound (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue) (item : StreamItem)
      (prior : acc.1.PendingBound (fun _ => True) settled)
      : (step acc item).1.PendingBound (fun _ => True) settled :=
    ((prior.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _
  have foldBound (more : List StreamItem)
      (acc : State × List Execution.DeliveryNode
        × List Execution.DeliveryNode × List StreamItemValue)
      (prior : acc.1.PendingBound (fun _ => True) settled)
      : (more.foldl step acc).1.PendingBound (fun _ => True) settled := by
    induction more generalizing acc with
    | nil => exact prior
    | cons item rest ih => exact ih _ (stepBound acc item prior)
  dsimp only [State.streamItems]
  split
  · exact bounded
  · exact (foldBound items (queue, [], [], []) bounded).drainReadyGroups

/-- Stream completion leaves group counters and memberships unchanged.
Witness: both executable root-membership branches preserve the group-node list.
-/
theorem State.PendingBound.streamSuccess {queue : State} {eligible settled}
    (bounded : queue.PendingBound eligible settled) (stream : Execution.DeliveryNode)
    : (queue.streamSuccess stream).1.PendingBound eligible settled := by
  unfold State.streamSuccess
  split <;> exact bounded

/-- Stream failure likewise preserves all group pending lower bounds.
Witness: the stream-root update never changes a group record.
-/
theorem State.PendingBound.streamFailure {queue : State} {eligible settled}
    (bounded : queue.PendingBound eligible settled)
    (stream : Execution.DeliveryNode) (errors : Nat)
    : (queue.streamFailure stream errors).1.PendingBound eligible settled := by
  unfold State.streamFailure
  split <;> exact bounded

/-- Queue initialization has safe counters for every group before any settlement.
Witness: integrate initial work into an empty state, then prune and activate it.
-/
theorem createWorkQueue_pendingBound_empty (work : Work)
    : (State.initialize work).PendingBound (fun _ => True) [] := by
  have empty : ({} : State).PendingBound (fun _ => True) [] := by
    intro node member
    cases member
  exact ((empty.maybeIntegrateWork work).pruneEmptyGroups _).startNewWork _

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
