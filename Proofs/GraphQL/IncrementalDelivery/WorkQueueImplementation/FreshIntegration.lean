import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.IntegrationCandidates
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GeneratedDescriptors
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.GroupAccounting

/-! Fresh integration roots remain nonempty independently of older settlement counters. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Integration balances new groups without assuming anything about old counters
-----------------------------------------------------------------------------------------

/-- At the selected key, pending tokens equal current task memberships.
This local proof invariant imposes no condition on other live groups. -/
private def State.InitialCountsAt (queue : State) (key : Nat) : Prop :=
  ∀ node ∈ queue.groupNodes, node.group.node.key = key → node.pending = node.tasks.length

/-- A preserved predicate extends through a state fold.
Witness: list induction on the actual intermediate states. -/
private theorem fold_preserves {α β : Type} (step : β → α → β) (property : β → Prop)
    (preserved : ∀ state item, property state → property (step state item))
    (items : List α) (state : β) (initial : property state)
    : property (items.foldl step state) := by
  induction items generalizing state with
  | nil => exact initial
  | cons item rest ih => exact ih _ (preserved state item initial)

/-- Replacing metadata retains the local count equation when the replacement does.
Witness: every output node is unchanged or is the supplied replacement. -/
private theorem State.InitialCountsAt.putGroupNode {queue : State} {key : Nat}
    (counts : queue.InitialCountsAt key) (updated : GroupNode)
    (balanced : updated.group.node.key = key → updated.pending = updated.tasks.length)
    : (queue.putGroupNode updated).InitialCountsAt key := by
  intro node member sameKey
  obtain ⟨old, oldMember, same⟩ := List.mem_map.mp member
  split at same
  · subst node; exact balanced sameKey
  · subst node; exact counts old oldMember sameKey

/-- A new empty group starts balanced at every key; skipped registration changes nothing.
Witness: the registration branch appends a zero-task, zero-pending node. -/
private theorem State.InitialCountsAt.addGroup {queue : State} {key : Nat}
    (counts : queue.InitialCountsAt key) (group : Group)
    : (queue.addGroup group).InitialCountsAt key := by
  unfold State.addGroup
  split
  · exact counts
  · dsimp only
    split
    · exact counts
    · intro node member sameKey
      rcases List.mem_append.mp member with old | new
      · exact counts node old sameKey
      · have same := List.mem_singleton.mp new
        subst node
        rfl

/-- Group registration and parent-link installation preserve the selected count equation.
Witness: registration starts balanced nodes and linking changes only child lists. -/
private theorem State.InitialCountsAt.addGroups {queue : State} {key : Nat}
    (counts : queue.InitialCountsAt key) (groups : List Group)
    : (queue.addGroups groups).1.InitialCountsAt key := by
  let link (current : State) (group : Group) : State :=
    match group.parent with
    | none => current
    | some parent =>
        match current.groupNode? parent with
        | none => current
        | some node =>
            let children := if node.childGroups.contains group.node.key then node.childGroups
              else node.childGroups ++ [group.node.key]
            current.putGroupNode { node with childGroups := children }
  have preserved (current : State) (group : Group) (prior : current.InitialCountsAt key)
      : (link current group).InitialCountsAt key := by
    unfold link
    split
    · exact prior
    · split
      · exact prior
      · rename_i node found
        exact prior.putGroupNode _ (prior node (List.mem_of_find?_eq_some found))
  let fresh := groups.filter (fun group =>
    !queue.registeredGroups.contains group.node.key
      && (queue.groupNode? group.node.key).isNone)
  exact fold_preserves link (fun state => state.InitialCountsAt key) preserved fresh _
    (fold_preserves State.addGroup (fun state => state.InitialCountsAt key)
      (fun _ group prior => prior.addGroup group) fresh queue counts)

/-- Task integration preserves local balance, even if it skips duplicate memberships.
Witness: each inserted membership increments pending by exactly one. -/
private theorem State.InitialCountsAt.addTask {queue : State} {key : Nat}
    (counts : queue.InitialCountsAt key) (task : Task)
    : (queue.addTask task).InitialCountsAt key := by
  let step (current : State) (group : Execution.DeliveryNode) : State :=
    match current.groupNode? group.key with
    | none => current
    | some node =>
        if node.tasks.contains task.occurrence then current
        else current.putGroupNode
          { node with tasks := node.tasks ++ [task.occurrence], pending := node.pending + 1 }
  have preserved (current : State) (group : Execution.DeliveryNode)
      (prior : current.InitialCountsAt key) : (step current group).InitialCountsAt key := by
    unfold step
    split
    · exact prior
    · rename_i node found
      split
      · exact prior
      · apply prior.putGroupNode
        intro sameKey
        have balanced := prior node (List.mem_of_find?_eq_some found) sameKey
        simp [balanced]
  let current := task.groups.foldl step { queue with tasks := queue.tasks ++ [task] }
  have balanced : current.InitialCountsAt key :=
    fold_preserves step (fun state => state.InitialCountsAt key) preserved task.groups _ counts
  change (if task.groups.any (fun group => current.rootGroups.contains group.key)
      && (current.taskNode? task.occurrence).isNone then
      { current with taskNodes := current.taskNodes ++ [{ task }] }
    else current).InitialCountsAt key
  split <;> exact balanced

/-- Immediate integration preserves a local initial-count equation.
Witness: the group/task folds preserve it; stream registration changes neither field. -/
private theorem State.InitialCountsAt.maybeIntegrateWork {queue : State} {key : Nat}
    (counts : queue.InitialCountsAt key) (work : Work) (parentTask : Option Occurrence)
    : (queue.maybeIntegrateWork work parentTask).1.InitialCountsAt key := by
  let grouped := (queue.addGroups work.groups).1
  let tasked := work.tasks.foldl State.addTask grouped
  have balanced : tasked.InitialCountsAt key :=
    fold_preserves State.addTask (fun state => state.InitialCountsAt key)
      (fun _ task prior => prior.addTask task) work.tasks grouped (counts.addGroups work.groups)
  change (tasked.addStreams work.streams parentTask).1.InitialCountsAt key
  unfold State.addStreams
  split
  · exact balanced
  · dsimp
    split <;> exact balanced

/-- A group whose key was absent before integration has exact initial pending counts.
Witness: local balance is initially vacuous and is preserved by integration, regardless
of other groups' prior successes, failures, or counter values. -/
theorem State.maybeIntegrateWork_freshCounts (queue : State) (work : Work)
    (parentTask : Option Occurrence) {key : Nat} (absent : queue.groupNode? key = none)
    {node : GroupNode}
    (found : (queue.maybeIntegrateWork work parentTask).1.groupNode? key = some node)
    : node.pending = node.tasks.length := by
  have counts : queue.InitialCountsAt key := by
    intro old member sameKey
    have noMatch := (List.find?_eq_none.mp absent) old member
    exact False.elim (noMatch (beq_iff_eq.mpr sameKey))
  exact (counts.maybeIntegrateWork work parentTask) node
    (List.mem_of_find?_eq_some found) (State.groupNode?_key found)

-----------------------------------------------------------------------------------------
-- Fresh root candidates cannot be empty and cannot promote descendants
-----------------------------------------------------------------------------------------

/-- A task-supported integration root is nonempty, without a prior pending ledger.
Witness: the returned candidate was absent before registration, hence its new count is
exact; one of the incoming tasks is linked to it. Old-group counters are irrelevant. -/
theorem State.maybeIntegrateWork_freshRoot_nonzero {queue : State}
    (unique : queue.GroupKeysUnique) (work : Work) (covered : work.GroupsHaveTasks)
    (parentTask : Option Occurrence) {group : Execution.DeliveryNode}
    (candidate : group ∈ (queue.maybeIntegrateWork work parentTask).2.newGroups)
    {node : GroupNode}
    (found
      : (queue.maybeIntegrateWork work parentTask).1.groupNode? group.key = some node)
    : node.pending ≠ 0 := by
  rw [queue.maybeIntegrateWork_newGroups work parentTask] at candidate
  obtain ⟨descriptor, member, same, _, _, absent⟩ :=
    queue.addGroups_newGroup_candidate work.groups candidate
  obtain ⟨task, taskMember, contributor⟩ := covered descriptor member
  have nodeKey : node.group.node.key = descriptor.node.key := by
    rw [State.groupNode?_key found, same]
  have linked := queue.maybeIntegrateWork_newTask_linked unique work parentTask taskMember
    node (List.mem_of_find?_eq_some found) (nodeKey.symm ▸ contributor)
  have balanced := queue.maybeIntegrateWork_freshCounts work parentTask (same ▸ absent) found
  intro zero
  have empty : node.tasks = [] := by simpa using balanced.symm.trans zero
  simp [empty] at linked

/-- Task-supported fresh integration roots do not trigger pruning or promotion.
Witness: every present returned root is nonempty. This removes the settled-list,
task-freshness, and global pending-count premises of the older integration theorem. -/
theorem State.maybeIntegrateWork_prune_freshRoots {queue : State}
    (unique : queue.GroupKeysUnique) (work : Work) (covered : work.GroupsHaveTasks)
    (parentTask : Option Occurrence := none)
    : let integrated := queue.maybeIntegrateWork work parentTask
      (integrated.1.pruneEmptyGroups integrated.2.newGroups).1 = integrated.1
      ∧ (integrated.1.pruneEmptyGroups integrated.2.newGroups).2.Subset
          integrated.2.newGroups := by
  apply State.pruneEmptyGroups_of_nonempty
  intro group candidate node found
  rw [queue.maybeIntegrateWork_newGroups work parentTask] at candidate
  obtain ⟨descriptor, member, same, _⟩ :=
    queue.addGroups_newGroup_candidate work.groups candidate
  obtain ⟨task, taskMember, contributor⟩ := covered descriptor member
  have nodeKey : node.group.node.key = descriptor.node.key := by
    rw [State.groupNode?_key found, same]
  exact List.ne_nil_of_mem
    (queue.maybeIntegrateWork_newTask_linked unique work parentTask taskMember node
      (List.mem_of_find?_eq_some found) (nodeKey.symm ▸ contributor))

/-- If every registration candidate owns a task, a stream item's released group has
empty defer dependencies and a fresh registry key.
Witness: task-supported fresh roots cannot be pruned into descendants; canonical parent
metadata identifies each surviving parentless candidate's empty ancestor list.
The extra shape premise excludes taskless wrappers; general integration uses record-aware
retirement certificates instead. No counter or previous-success restriction is needed.
-/
theorem GraphEvent.MatchesWork.streamItem_freshRoot_of_taskSupported
    {queue : State} {work : Execution.Work} {stream : Execution.DeliveryNode}
    {items : List StreamItem} (generated : ExecutedWork work)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (unique : queue.GroupKeysUnique) {item : StreamItem} (member : item ∈ items)
    (covered : item.work.GroupsHaveTasks)
    {node : Execution.DeliveryNode}
    (announced
      : node
        ∈ ((queue.maybeIntegrateWork item.work).1.pruneEmptyGroups
            (queue.maybeIntegrateWork item.work).2.newGroups).2)
    : (∃ producer, NodeAt work node .group [] producer)
      ∧ node.key ∉ queue.registeredGroups := by
  have original := (queue.maybeIntegrateWork_prune_freshRoots unique item.work
    covered).2 announced
  rw [State.maybeIntegrateWork_newGroups] at original
  obtain ⟨group, candidate, same, parentless, fresh, _⟩ :=
    queue.addGroups_newGroup_candidate item.work.groups original
  obtain ⟨task, taskMember, contributor⟩ := covered group candidate
  obtain ⟨address, payload, taskEq, taskAt⟩ :=
    matching.streamItem_childTask_producer member taskMember
  obtain ⟨descriptor, dependencies, known, keyEq⟩ :=
    TaskAt.executionGroup_owner (taskEq ▸ taskAt) contributor
  obtain ⟨recordDependencies, record⟩ :=
    matching.streamItem_childGroups_recordAt member candidate
  have sameNode := generated.record_eq_node record known keyEq.symm
  have located : NodeAt work group.node .group dependencies (some item.occurrence) :=
    sameNode.symm ▸ known
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have parent := matching.streamItem_childGroups_parentCanonical canonical member candidate
  rw [parentless, ← canonical _ _ (groupRecordAt_of_nodeAt located)] at parent
  have empty : dependencies = [] := by
    cases dependencies with
    | nil => rfl
    | cons head tail => simp at parent
  exact ⟨⟨some item.occurrence, same ▸ empty ▸ located⟩, same ▸ fresh⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
