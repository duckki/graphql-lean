import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.IntegrationCandidates
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GeneratedDescriptors
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.GroupAccounting

/-! Fresh integration roots remain nonempty independently of older settlement counters. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Integration balances new groups without assuming anything about old counters
-----------------------------------------------------------------------------------------

/-- At the selected ref, pending tokens equal current task memberships.
This local proof invariant imposes no condition on other live groups. -/
private def State.InitialCountsAt (queue : State) (ref : NodeRef) : Prop :=
  ∀ node ∈ queue.groupNodes, node.group.node.ref = ref → node.pending = node.tasks.length

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
private theorem State.InitialCountsAt.putGroupNode {queue : State} {ref : NodeRef}
    (counts : queue.InitialCountsAt ref) (updated : GroupNode)
    (balanced : updated.group.node.ref = ref → updated.pending = updated.tasks.length)
    : (queue.putGroupNode updated).InitialCountsAt ref := by
  intro node member sameRef
  obtain ⟨old, oldMember, same⟩ := List.mem_map.mp member
  split at same
  · subst node; exact balanced sameRef
  · subst node; exact counts old oldMember sameRef

/-- A new empty group starts balanced at every ref; skipped registration changes nothing.
Witness: the registration branch appends a zero-task, zero-pending node. -/
private theorem State.InitialCountsAt.addGroup {queue : State} {ref : NodeRef}
    (counts : queue.InitialCountsAt ref) (group : Group)
    : (queue.addGroup group).InitialCountsAt ref := by
  unfold State.addGroup
  split
  · exact counts
  · dsimp only
    split
    · exact counts
    · intro node member sameRef
      rcases List.mem_append.mp member with old | new
      · exact counts node old sameRef
      · have same := List.mem_singleton.mp new
        subst node
        rfl

/-- Group registration and parent-link installation preserve the selected count equation.
Witness: registration starts balanced nodes and linking changes only child lists. -/
private theorem State.InitialCountsAt.addGroups {queue : State} {ref : NodeRef}
    (counts : queue.InitialCountsAt ref) (groups : List Group)
    : (queue.addGroups groups).1.InitialCountsAt ref := by
  let link (current : State) (group : Group) : State :=
    match group.parent with
    | none => current
    | some parent =>
        match current.groupNode? parent with
        | none => current
        | some node =>
            let children := if node.childGroups.contains group.node.ref then node.childGroups
              else node.childGroups ++ [group.node.ref]
            current.putGroupNode { node with childGroups := children }
  have preserved (current : State) (group : Group) (prior : current.InitialCountsAt ref)
      : (link current group).InitialCountsAt ref := by
    unfold link
    split
    · exact prior
    · split
      · exact prior
      · rename_i node found
        exact prior.putGroupNode _ (prior node (List.mem_of_find?_eq_some found))
  let fresh := groups.filter (fun group =>
    !queue.registeredGroups.contains group.node.ref
      && (queue.groupNode? group.node.ref).isNone)
  exact fold_preserves link (fun state => state.InitialCountsAt ref) preserved fresh _
    (fold_preserves State.addGroup (fun state => state.InitialCountsAt ref)
      (fun _ group prior => prior.addGroup group) fresh queue counts)

/-- Task integration preserves local balance, even if it skips duplicate memberships.
Witness: each inserted membership increments pending by exactly one. -/
private theorem State.InitialCountsAt.addTask {queue : State} {ref : NodeRef}
    (counts : queue.InitialCountsAt ref) (task : Task)
    : (queue.addTask task).InitialCountsAt ref := by
  let step (current : State) (group : Execution.DeliveryNode) : State :=
    match current.groupNode? group.ref with
    | none => current
    | some node =>
        if node.tasks.contains task.occurrence then current
        else current.putGroupNode
          { node with tasks := node.tasks ++ [task.occurrence], pending := node.pending + 1 }
  have preserved (current : State) (group : Execution.DeliveryNode)
      (prior : current.InitialCountsAt ref) : (step current group).InitialCountsAt ref := by
    unfold step
    split
    · exact prior
    · rename_i node found
      split
      · exact prior
      · apply prior.putGroupNode
        intro sameRef
        have balanced := prior node (List.mem_of_find?_eq_some found) sameRef
        simp [balanced]
  let current := task.groups.foldl step { queue with tasks := queue.tasks ++ [task] }
  have balanced : current.InitialCountsAt ref :=
    fold_preserves step (fun state => state.InitialCountsAt ref) preserved task.groups _ counts
  change (if task.groups.any (fun group => current.rootGroups.contains group.ref)
      && (current.taskNode? task.occurrence).isNone then
      { current with taskNodes := current.taskNodes ++ [{ task }] }
    else current).InitialCountsAt ref
  split <;> exact balanced

/-- Immediate integration preserves a local initial-count equation.
Witness: the group/task folds preserve it; stream registration changes neither field. -/
private theorem State.InitialCountsAt.maybeIntegrateWork {queue : State} {ref : NodeRef}
    (counts : queue.InitialCountsAt ref) (work : Work) (parentTask : Option Occurrence)
    : (queue.maybeIntegrateWork work parentTask).1.InitialCountsAt ref := by
  let grouped := (queue.addGroups work.groups).1
  let tasked := work.tasks.foldl State.addTask grouped
  have balanced : tasked.InitialCountsAt ref :=
    fold_preserves State.addTask (fun state => state.InitialCountsAt ref)
      (fun _ task prior => prior.addTask task) work.tasks grouped (counts.addGroups work.groups)
  change (tasked.addStreams work.streams parentTask).1.InitialCountsAt ref
  unfold State.addStreams
  split
  · exact balanced
  · dsimp
    split <;> exact balanced

/-- A group whose ref was absent before integration has exact initial pending counts.
Witness: local balance is initially vacuous and is preserved by integration, regardless
of other groups' prior successes, failures, or counter values. -/
theorem State.maybeIntegrateWork_freshCounts (queue : State) (work : Work)
    (parentTask : Option Occurrence) {ref : NodeRef}
    (absent : queue.groupNode? ref = none) {node : GroupNode}
    (found : (queue.maybeIntegrateWork work parentTask).1.groupNode? ref = some node)
    : node.pending = node.tasks.length := by
  have counts : queue.InitialCountsAt ref := by
    intro old member sameRef
    have noMatch := (List.find?_eq_none.mp absent) old member
    exact False.elim (noMatch (beq_iff_eq.mpr sameRef))
  exact (counts.maybeIntegrateWork work parentTask) node
    (List.mem_of_find?_eq_some found) (State.groupNode?_ref found)

-----------------------------------------------------------------------------------------
-- Fresh root candidates cannot be empty and cannot promote descendants
-----------------------------------------------------------------------------------------

/-- A task-supported integration root is nonempty, without a prior pending ledger.
Witness: the returned candidate was absent before registration, hence its new count is
exact; one of the incoming tasks is linked to it. Old-group counters are irrelevant. -/
theorem State.maybeIntegrateWork_freshRoot_nonzero {queue : State}
    (unique : queue.GroupRefsUnique) (work : Work) (covered : work.GroupsHaveTasks)
    (parentTask : Option Occurrence) {group : Execution.DeliveryNode}
    (candidate : group ∈ (queue.maybeIntegrateWork work parentTask).2.newGroups)
    {node : GroupNode}
    (found
      : (queue.maybeIntegrateWork work parentTask).1.groupNode? group.ref = some node)
    : node.pending ≠ 0 := by
  rw [queue.maybeIntegrateWork_newGroups work parentTask] at candidate
  obtain ⟨descriptor, member, same, _, _, absent⟩ :=
    queue.addGroups_newGroup_candidate work.groups candidate
  obtain ⟨task, taskMember, contributor⟩ := covered descriptor member
  have nodeRef : node.group.node.ref = descriptor.node.ref := by
    rw [State.groupNode?_ref found, same]
  have linked := queue.maybeIntegrateWork_newTask_linked unique work parentTask taskMember
    node (List.mem_of_find?_eq_some found) (nodeRef.symm ▸ contributor)
  have balanced := queue.maybeIntegrateWork_freshCounts work parentTask (same ▸ absent) found
  intro zero
  have empty : node.tasks = [] := by simpa using balanced.symm.trans zero
  simp [empty] at linked

/-- Task-supported fresh integration roots do not trigger pruning or promotion.
Witness: every present returned root is nonempty. This removes the settled-list,
task-freshness, and global pending-count premises of the older integration theorem. -/
theorem State.maybeIntegrateWork_prune_freshRoots {queue : State}
    (unique : queue.GroupRefsUnique) (work : Work) (covered : work.GroupsHaveTasks)
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
  have nodeRef : node.group.node.ref = descriptor.node.ref := by
    rw [State.groupNode?_ref found, same]
  exact List.ne_nil_of_mem
    (queue.maybeIntegrateWork_newTask_linked unique work parentTask taskMember node
      (List.mem_of_find?_eq_some found) (nodeRef.symm ▸ contributor))

/-- If every registration candidate owns a task, a stream item's released group has
empty defer dependencies and a fresh registry ref.
Witness: task-supported fresh roots cannot be pruned into descendants; canonical parent
metadata identifies each surviving parentless candidate's empty ancestor list.
The extra shape premise excludes taskless wrappers; general integration uses record-aware
retirement certificates instead. No counter or previous-success restriction is needed.
-/
theorem GraphEvent.MatchesWork.streamItem_freshRoot_of_taskSupported
    {queue : State} {work : Execution.Work} {stream : Execution.DeliveryNode}
    {items : List StreamItem} (generated : ExecutedWork work)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (unique : queue.GroupRefsUnique) {item : StreamItem} (member : item ∈ items)
    (covered : item.work.GroupsHaveTasks)
    {node : Execution.DeliveryNode}
    (announced
      : node
        ∈ ((queue.maybeIntegrateWork item.work).1.pruneEmptyGroups
            (queue.maybeIntegrateWork item.work).2.newGroups).2)
    : (∃ producer, NodeAt work node .group [] producer)
      ∧ node.ref ∉ queue.registeredGroups := by
  have original := (queue.maybeIntegrateWork_prune_freshRoots unique item.work
    covered).2 announced
  rw [State.maybeIntegrateWork_newGroups] at original
  obtain ⟨group, candidate, same, parentless, fresh, _⟩ :=
    queue.addGroups_newGroup_candidate item.work.groups original
  obtain ⟨task, taskMember, contributor⟩ := covered group candidate
  obtain ⟨address, payload, taskEq, taskAt⟩ :=
    matching.streamItem_childTask_producer member taskMember
  obtain ⟨descriptor, dependencies, known, refEq⟩ :=
    TaskAt.executionGroup_owner (taskEq ▸ taskAt) contributor
  obtain ⟨recordDependencies, record⟩ :=
    matching.streamItem_childGroups_recordAt member candidate
  have sameNode := generated.record_eq_node record known refEq.symm
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
