import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskRegistrationOrder
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RegistrationCoverage

/-! Each live group's task memberships retain the permanent task-registration order. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (
  ExecutionGroupValue StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Every live group's task list is an ordered subsequence of permanent task registrations.
This is proof evidence about existing lists, not an implementation field or source law.
-/
def State.GroupMembershipOrder (queue : State) : Prop :=
  ∀ node ∈ queue.groupNodes, node.tasks.Sublist (queue.tasks.map Task.occurrence)

-----------------------------------------------------------------------------------------
-- Registration appends task occurrences without reordering old memberships
-----------------------------------------------------------------------------------------

/-- Replacing group metadata preserves order when the replacement has an ordered task list.
Witness: each mapped node is either the replacement or an unchanged old node.
-/
theorem State.GroupMembershipOrder.putGroupNode {queue : State}
    (ordered : queue.GroupMembershipOrder) (updated : GroupNode)
    (tasks : updated.tasks.Sublist (queue.tasks.map Task.occurrence))
    : (queue.putGroupNode updated).GroupMembershipOrder := by
  intro node member
  obtain ⟨prior, before, same⟩ := List.mem_map.mp member
  split at same
  · subst node; exact tasks
  · subst node; exact ordered prior before

/-- Registering an empty group preserves membership order.
Witness: old lists are unchanged; a fresh group has no task memberships yet.
-/
theorem State.GroupMembershipOrder.addGroup {queue : State}
    (ordered : queue.GroupMembershipOrder) (group : Group)
    : (queue.addGroup group).GroupMembershipOrder := by
  unfold State.addGroup
  split
  · exact ordered
  · split
    · exact ordered
    · intro node member
      rcases List.mem_append.mp member with old | fresh
      · exact ordered node old
      · cases List.mem_singleton.mp fresh
        exact List.nil_sublist _

/-- Group registration and parent linking leave all task membership orders unchanged.
Witness: new nodes are empty; parent-link replacement retains the old task list.
-/
theorem State.GroupMembershipOrder.addGroups {queue : State}
    (ordered : queue.GroupMembershipOrder) (groups : List Group)
    : (queue.addGroups groups).1.GroupMembershipOrder := by
  let step (current : State) (group : Group) : State :=
    match group.parent with
    | none => current
    | some parent =>
        match current.groupNode? parent with
        | none => current
        | some node =>
            let children := if node.childGroups.contains group.node.key then
              node.childGroups else node.childGroups ++ [group.node.key]
            current.putGroupNode { node with childGroups := children }
  have links (more : List Group) (current : State) (prior : current.GroupMembershipOrder)
      : (more.foldl step current).GroupMembershipOrder := by
    induction more generalizing current with
    | nil => exact prior
    | cons group rest ih =>
        apply ih
        unfold step
        split
        · exact prior
        · split
          · exact prior
          · rename_i node found
            exact prior.putGroupNode _ (prior node (List.mem_of_find?_eq_some found))
  have register (more : List Group) (current : State) (prior : current.GroupMembershipOrder)
      : (more.foldl State.addGroup current).GroupMembershipOrder := by
    induction more generalizing current with
    | nil => exact prior
    | cons group rest ih => exact ih _ (prior.addGroup group)
  exact links _ _ (register _ queue ordered)

/-- Adding one task appends its occurrence to each group at most once, in registration order.
Witness: the permanent registry is extended first. An owner without the new occurrence
still has its old-prefix subsequence; appending the occurrence preserves that subsequence.
-/
theorem State.GroupMembershipOrder.addTask {queue : State}
    (ordered : queue.GroupMembershipOrder) (task : Task)
    : (queue.addTask task).GroupMembershipOrder := by
  let registered : State := { queue with tasks := queue.tasks ++ [task] }
  let step (current : State) (group : Execution.DeliveryNode) : State :=
    match current.groupNode? group.key with
    | none => current
    | some node =>
        if node.tasks.contains task.occurrence then current
        else current.putGroupNode
          { node with tasks := node.tasks ++ [task.occurrence], pending := node.pending + 1 }
  have loop (groups : List Execution.DeliveryNode) (current : State)
      (prior : current.GroupMembershipOrder) (same : current.tasks = queue.tasks ++ [task])
      : (groups.foldl step current).GroupMembershipOrder := by
    induction groups generalizing current with
    | nil => exact prior
    | cons group rest ih =>
        apply ih
        · unfold step
          split
          · exact prior
          · rename_i node found
            split
            · exact prior
            · rename_i absent
              apply prior.putGroupNode
              have old := prior node (List.mem_of_find?_eq_some found)
              rw [same, List.map_append, List.map_singleton] at old ⊢
              have shorter := old.of_sublist_append_left (by
                intro occurrence member single
                have equal := List.mem_singleton.mp single
                subst occurrence
                exact absent ((List.contains_iff_exists_mem_beq).mpr
                  ⟨_, member, (occurrence_beq_iff_eq _ _).mpr rfl⟩))
              exact shorter.append (.refl _)
        · unfold step
          split
          · exact same
          · split <;> exact same
  have initial : registered.GroupMembershipOrder := by
    intro node member
    rw [show registered.tasks = queue.tasks ++ [task] from rfl, List.map_append]
    exact List.sublist_append_of_sublist_left (ordered node member)
  have result := loop task.groups registered initial rfl
  let current := task.groups.foldl step registered
  change (if task.groups.any (fun group => current.rootGroups.contains group.key)
      && (current.taskNode? task.occurrence).isNone then
      { current with taskNodes := current.taskNodes ++ [{ task }] }
    else current).GroupMembershipOrder
  split <;> exact result

/-- Stream registration changes no task membership or permanent task list.
Witness: both root and parent-linked branches affect only stream and live-task metadata.
-/
theorem State.GroupMembershipOrder.addStreams {queue : State}
    (ordered : queue.GroupMembershipOrder) (streams : List Stream)
    (producer : Option Occurrence)
    : (queue.addStreams streams producer).1.GroupMembershipOrder := by
  unfold State.addStreams
  split
  · exact ordered
  · dsimp only
    split <;> exact ordered

/-- Integrating any work chunk preserves each group's registration-order subsequence.
Witness: register groups, append tasks in chunk order, then register streams.
-/
theorem State.GroupMembershipOrder.maybeIntegrateWork {queue : State}
    (ordered : queue.GroupMembershipOrder) (work : Work)
    (producer : Option Occurrence := none)
    : (queue.maybeIntegrateWork work producer).1.GroupMembershipOrder := by
  have loop (tasks : List Task) (current : State) (prior : current.GroupMembershipOrder)
      : (tasks.foldl State.addTask current).GroupMembershipOrder := by
    induction tasks generalizing current with
    | nil => exact prior
    | cons task rest ih => exact ih _ (prior.addTask task)
  exact (loop work.tasks _ (ordered.addGroups work.groups)).addStreams work.streams
    producer

-----------------------------------------------------------------------------------------
-- Cleanup removes memberships without reordering the retained tasks
-----------------------------------------------------------------------------------------

/-- Pruning deletes whole nodes and leaves every surviving membership list unchanged.
Witness: induction through the finite empty-group traversal.
-/
theorem State.GroupMembershipOrder.pruneEmptyGroups {queue : State}
    (ordered : queue.GroupMembershipOrder) (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.GroupMembershipOrder := by
  have loop (fuel : Nat) (current : State) (remaining kept : List Execution.DeliveryNode)
      (prior : current.GroupMembershipOrder)
      : (State.pruneEmptyGroups.go fuel current remaining kept).1.GroupMembershipOrder := by
    induction fuel generalizing current remaining kept with
    | zero => exact prior
    | succ fuel ih =>
        cases remaining with
        | nil => exact prior
        | cons group rest =>
            unfold State.pruneEmptyGroups.go
            split
            · exact ih _ _ _ prior
            · split
              · apply ih _ _ _
                intro node member
                exact prior node (List.mem_filter.mp member).1
              · exact ih _ _ _ prior
  exact loop _ queue groups [] ordered

/-- Activating work preserves the exact group nodes and permanent task registry.
Witness: the existing activation projection equations transport the subsequence property.
-/
theorem State.GroupMembershipOrder.startNewWork {queue : State}
    (ordered : queue.GroupMembershipOrder) (work : NewWork)
    : (queue.startNewWork work).GroupMembershipOrder := by
  intro node member
  rw [(State.startNewWork_groupCore _ _).1] at member
  rw [(State.startNewWork_groupCore _ _).2.1]
  exact ordered node member

/-- Removing a shared task filters all owner memberships while preserving their order.
Witness: filtering yields a subsequence of each already ordered list.
-/
theorem State.GroupMembershipOrder.removeTask {queue : State}
    (ordered : queue.GroupMembershipOrder) (occurrence : Occurrence)
    : (queue.removeTask occurrence).GroupMembershipOrder := by
  intro node member
  obtain ⟨prior, before, same⟩ := List.mem_map.mp member
  subst node
  exact List.filter_sublist.trans (ordered prior before)

/-- Cancelling a group retains only unchanged live group nodes.
Witness: membership in the filtered nodes implies membership in the old queue.
-/
theorem State.GroupMembershipOrder.removeGroup {queue : State}
    (ordered : queue.GroupMembershipOrder) (key : Nat)
    : (queue.removeGroup key).GroupMembershipOrder := by
  intro node member
  exact ordered node (List.mem_filter.mp member).1

/-- Failure closure uses only cancellation and therefore preserves membership order.
Witness: the group-removal preservation theorem.
-/
theorem State.GroupMembershipOrder.finishGroupFailure {queue : State}
    (ordered : queue.GroupMembershipOrder) (group : GroupNode) (errors : Nat)
    : (queue.finishGroupFailure group errors).1.GroupMembershipOrder :=
  ordered.removeGroup group.group.node.key

private theorem fold_preserves {α β : Type} (step : β → α → β) (property : β → Prop)
    (preserves : ∀ current next, property current → property (step current next))
    (inputs : List α) (initial : β) (valid : property initial)
    : property (inputs.foldl step initial) := by
  induction inputs generalizing initial with
  | nil => exact valid
  | cons next rest ih => exact ih _ (preserves initial next valid)

/-- Successful flushing removes memberships and group shells without permuting either.
Witness: the actual task-flush fold preserves ordered subsequences, followed by pruning.
-/
theorem State.GroupMembershipOrder.finishGroupSuccess {queue : State}
    (ordered : queue.GroupMembershipOrder) (group : GroupNode)
    : (queue.finishGroupSuccess group).1.GroupMembershipOrder := by
  have step (acc : State × List ExecutionGroupValue × Keys) (occurrence : Occurrence)
      (prior : acc.1.GroupMembershipOrder)
      : (flushGroupTask acc occurrence).1.GroupMembershipOrder := by
    obtain ⟨current, values, streams⟩ := acc
    unfold flushGroupTask
    split
    · exact prior
    · exact prior.removeTask occurrence
  let flushed := (group.tasks.foldl flushGroupTask (queue, [], [])).1
  have flushedOrder : flushed.GroupMembershipOrder :=
    fold_preserves flushGroupTask (fun acc => acc.1.GroupMembershipOrder)
      step group.tasks (queue, [], []) ordered
  let current : State := { flushed with
    groupNodes := flushed.groupNodes.filter
      (fun node => node.group.node.key != group.group.node.key)
    rootGroups := flushed.rootGroups.filter (· != group.group.node.key) }
  have currentOrder : current.GroupMembershipOrder := by
    intro node member
    exact flushedOrder node (List.mem_filter.mp member).1
  exact currentOrder.pruneEmptyGroups _

/-- Releasing settled roots preserves registration-order memberships at every iteration.
Witness: the generic drain induction uses successful cleanup, activation, and failure.
-/
theorem State.GroupMembershipOrder.drainReadyGroups {queue : State}
    (ordered : queue.GroupMembershipOrder)
    : queue.drainReadyGroups.1.GroupMembershipOrder := by
  apply State.drainReadyGroups_preserves State.GroupMembershipOrder (valid := ordered)
  · intro current node prior _ _ _ _
    exact (prior.finishGroupSuccess node).startNewWork _
  · intro current node errors prior _ _ _
    exact prior.finishGroupFailure node errors

-----------------------------------------------------------------------------------------
-- Host-event handling preserves the order through all registration and release paths
-----------------------------------------------------------------------------------------

/-- Each successful contributor step decrements metadata and may flush an ordered group.
Witness: the replacement keeps its task list; successful cleanup preserves order.
-/
theorem successGroupStep_groupMembershipOrder
    (acc : State × List WorkQueueEvent × NewWork) (group : Execution.DeliveryNode)
    (ordered : acc.1.GroupMembershipOrder)
    : (successGroupStep acc group).1.GroupMembershipOrder := by
  obtain ⟨current, events, released⟩ := acc
  dsimp only [successGroupStep]
  split
  · exact ordered
  · rename_i node found
    have updated := ordered.putGroupNode { node with pending := node.pending - 1 }
      (ordered node (List.mem_of_find?_eq_some found))
    split
    · exact updated.finishGroupSuccess _
    · exact updated

/-- The owner fold preserves membership order and the exact permanent registry.
Witness: fold induction over counter updates and successful cleanup.
-/
theorem State.GroupMembershipOrder.successGroupFold {queue : State}
    (ordered : queue.GroupMembershipOrder) (groups : List Execution.DeliveryNode)
    : (groups.foldl successGroupStep (queue, [], {})).1.GroupMembershipOrder :=
  fold_preserves successGroupStep (fun acc => acc.1.GroupMembershipOrder)
    successGroupStep_groupMembershipOrder groups (queue, [], {}) ordered

/-- Successful owner processing never appends or removes permanent task definitions.
Witness: the one-owner registry equation iterated through the actual fold.
-/
theorem successGroupFold_tasks (groups : List Execution.DeliveryNode)
    (acc : State × List WorkQueueEvent × NewWork)
    : (groups.foldl successGroupStep acc).1.tasks = acc.1.tasks := by
  induction groups generalizing acc with
  | nil => rfl
  | cons group rest ih => rw [List.foldl_cons, ih, successGroupStep_tasks]

/-- A successful settlement appends child tasks and releases groups without reordering.
Witness: value storage leaves memberships unchanged, then integration and release preserve
their subsequences of the extended permanent registry.
-/
theorem State.GroupMembershipOrder.taskSuccess {queue : State}
    (ordered : queue.GroupMembershipOrder) (occurrence : Occurrence) (result : TaskResult)
    : (queue.taskSuccess occurrence result).1.GroupMembershipOrder := by
  unfold State.taskSuccess
  split
  · exact ordered
  · rename_i node found
    split
    · exact ordered.removeTask occurrence
    · have stored : (queue.putTaskNode
          { node with value := some result.value }).GroupMembershipOrder := ordered
      have integrated := stored.maybeIntegrateWork result.work (some occurrence)
      have released := fold_preserves successGroupStep
        (fun acc => acc.1.GroupMembershipOrder) successGroupStep_groupMembershipOrder
        node.task.groups (_, [], {}) integrated
      exact (released.startNewWork _).drainReadyGroups

/-- Failure either removes owners or changes only their counters and retained errors.
Witness: each failure-owner step preserves its surviving ordered membership list.
-/
theorem State.GroupMembershipOrder.taskFailure {queue : State}
    (ordered : queue.GroupMembershipOrder) (occurrence : Occurrence) (errors : Nat)
    : (queue.taskFailure occurrence errors).1.GroupMembershipOrder := by
  have step (acc : State × List WorkQueueEvent) (group : Execution.DeliveryNode)
      (prior : acc.1.GroupMembershipOrder)
      : (failureGroupStep errors acc group).1.GroupMembershipOrder := by
    obtain ⟨current, events⟩ := acc
    dsimp only [failureGroupStep]
    split
    · exact prior
    · rename_i node found
      split
      · exact prior.finishGroupFailure node errors
      · exact prior.putGroupNode _ (prior node (List.mem_of_find?_eq_some found))
  unfold State.taskFailure
  split
  · exact ordered
  · rename_i node found
    split
    · exact ordered.removeTask occurrence
    · exact fold_preserves (failureGroupStep errors)
        (fun acc => acc.1.GroupMembershipOrder) step node.task.groups
        (queue.removeTask occurrence, []) (ordered.removeTask occurrence)

/-- Each stream-item chunk appends its child tasks before ordered activation and draining.
Witness: fold over the real item-integration step, retaining the extended registry order.
-/
theorem State.GroupMembershipOrder.streamItems {queue : State}
    (ordered : queue.GroupMembershipOrder) (stream : Execution.DeliveryNode)
    (items : List StreamItem)
    : (queue.streamItems stream items).1.GroupMembershipOrder := by
  let step (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue) (item : StreamItem) :=
    let (current, groups, streams, values) := acc
    let (integrated, work) := current.maybeIntegrateWork item.work
    let (pruned, nonempty) := integrated.pruneEmptyGroups work.newGroups
    (pruned.startNewWork { work with newGroups := nonempty },
      groups ++ nonempty, streams ++ work.newStreams, values ++ [item.value])
  have preserved (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue) (item : StreamItem)
      (prior : acc.1.GroupMembershipOrder) : (step acc item).1.GroupMembershipOrder :=
    ((prior.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _
  unfold State.streamItems
  split
  · exact ordered
  · exact (fold_preserves step (fun acc => acc.1.GroupMembershipOrder) preserved
      items (queue, [], [], []) ordered).drainReadyGroups

/-- Every graph-event handler preserves the task-membership ordering invariant.
Witness: task and item handlers preserve it; stream closure changes only root streams.
-/
theorem State.GroupMembershipOrder.handleGraphEvent {queue : State}
    (ordered : queue.GroupMembershipOrder) (event : GraphEvent)
    : (queue.handleGraphEvent event).1.GroupMembershipOrder := by
  cases event with
  | taskSuccess occurrence result => exact ordered.taskSuccess occurrence result
  | taskFailure occurrence errors => exact ordered.taskFailure occurrence errors
  | streamItems stream items => exact ordered.streamItems stream items
  | streamSuccess stream =>
      change (queue.streamSuccess stream).1.GroupMembershipOrder
      unfold State.streamSuccess
      split <;> exact ordered
  | streamFailure stream errors =>
      change (queue.streamFailure stream errors).1.GroupMembershipOrder
      unfold State.streamFailure
      split <;> exact ordered

/-- Initial queue construction orders memberships by its immediate task registrations.
Witness: empty-state integration, pruning, and activation preserve the empty invariant.
-/
theorem createWorkQueue_groupMembershipOrder (work : Work)
    : (State.initialize work).GroupMembershipOrder := by
  have empty : ({} : State).GroupMembershipOrder := by
    intro node member
    cases member
  exact ((empty.maybeIntegrateWork work).pruneEmptyGroups _).startNewWork _

/-- Replaying any graph-event sequence retains ordered live group memberships.
Witness: induction over the actual replay, using each handler's preservation theorem.
No source validity or generated-work premise is required for this list-order fact.
-/
theorem State.GroupMembershipOrder.replayGraphEvents {queue : State}
    (ordered : queue.GroupMembershipOrder) (events : List GraphEvent)
    : (queue.replayGraphEvents events).GroupMembershipOrder := by
  induction events generalizing queue with
  | nil => exact ordered
  | cons event rest ih => exact ih (ordered.handleGraphEvent event)

-----------------------------------------------------------------------------------------
-- Actual flush selections retain the permanent registration order
-----------------------------------------------------------------------------------------

/-- A live group's actual flush uses one complete selection in permanent registry order.
Witness: compose the executable flush's membership subsequence with the live-group
invariant. Stored values and child-stream releases still use this same selection.
-/
theorem State.finishGroupSuccess_orderedSelection {queue : State}
    (ordered : queue.GroupMembershipOrder) {group : GroupNode}
    (live : group ∈ queue.groupNodes)
    : ∃ selected : List TaskNode,
        (selected.map (fun node => node.task.occurrence)).Nodup
        ∧ (selected.map (fun node => node.task.occurrence)).Sublist
            (queue.tasks.map Task.occurrence)
        ∧ (∀ node ∈ selected, node ∈ queue.taskNodes ∧ node.task.occurrence ∈ group.tasks)
        ∧ (queue.finishGroupSuccess group).2.1
          = (if (selected.filterMap TaskNode.value).isEmpty then
                []
              else
                [.groupValues group.group.node (selected.filterMap TaskNode.value)])
            ++ [.groupSuccess group.group.node
                  (queue.finishGroupSuccess group).2.2.newGroups
                  (queue.finishGroupSuccess group).2.2.newStreams]
        ∧ (∀ occurrence ∈ group.tasks,
            ∀ node, queue.taskNode? occurrence = some node → node ∈ selected)
        ∧ (∀ stream ∈ (queue.finishGroupSuccess group).2.2.newStreams,
            ∃ node ∈ selected, stream.key ∈ node.childStreams) := by
  obtain ⟨selected, unique, known, events, _, _, streams, complete, subsequence⟩ :=
    queue.finishGroupSuccess_completeSelection group
  exact ⟨selected, unique, subsequence.trans (ordered group live), known, events,
    complete, streams⟩

/-- Every actual replay state retains a complete ordered flush witness for each live group.
Witness: initialize and replay the unconditional membership-order invariant, then project
the exact successful flush. This is a concrete list-order result, not full event admission.
-/
theorem createWorkQueue_replayGraphEvents_orderedSelection (work : Work)
    (events : List GraphEvent) {group : GroupNode}
    (live : group ∈ ((State.initialize work).replayGraphEvents events).groupNodes)
    : ∃ selected : List TaskNode,
        (selected.map (fun node => node.task.occurrence)).Sublist
          (((State.initialize work).replayGraphEvents events).tasks.map Task.occurrence)
        ∧ (((State.initialize work).replayGraphEvents events).finishGroupSuccess
            group).2.1
          = (if (selected.filterMap TaskNode.value).isEmpty then
                []
              else
                [.groupValues group.group.node (selected.filterMap TaskNode.value)])
            ++ [.groupSuccess group.group.node
                  (((State.initialize work).replayGraphEvents events).finishGroupSuccess
                    group).2.2.newGroups
                  (((State.initialize work).replayGraphEvents events).finishGroupSuccess
                    group).2.2.newStreams] := by
  obtain ⟨selected, _, ordered, _, outputs, _⟩ :=
    State.finishGroupSuccess_orderedSelection
      ((createWorkQueue_groupMembershipOrder work).replayGraphEvents events) live
  exact ⟨selected, ordered, outputs⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
