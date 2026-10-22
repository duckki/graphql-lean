import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupPublication
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.DrainAccounting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ActiveLinks

/-! Task membership absence through release and removal, independently of publication. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (
  ExecutionGroupValue StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- No live group record retains `occurrence` in its task-membership list. -/
def State.TaskMembershipAbsent (queue : State) (occurrence : Occurrence) : Prop :=
  ∀ node ∈ queue.groupNodes, occurrence ∉ node.tasks

/-- Removing any task preserves an already absent membership.
Witness: every surviving task list is a filter of its original list.
-/
theorem State.TaskMembershipAbsent.removeTask {queue : State} {occurrence}
    (absent : queue.TaskMembershipAbsent occurrence) (removed : Occurrence)
    : (queue.removeTask removed).TaskMembershipAbsent occurrence := by
  intro node member task
  obtain ⟨old, prior, rfl⟩ := List.mem_map.mp member
  exact absent old prior (List.mem_filter.mp task).1

/-- Removing a task clears all of its shared group memberships, including duplicates.
Witness: the same occurrence filter is applied to every live group record.
-/
theorem State.removeTask_membershipAbsent (queue : State) (occurrence : Occurrence)
    : (queue.removeTask occurrence).TaskMembershipAbsent occurrence := by
  intro node member task
  obtain ⟨old, prior, rfl⟩ := List.mem_map.mp member
  have different := (List.mem_filter.mp task).2
  simp [bne, (occurrence_beq_iff_eq occurrence occurrence).mpr rfl] at different

/-- Empty-shell pruning cannot reintroduce a previously absent task membership.
Witness: its pointwise record-preservation theorem; promoted notices do not mutate lists.
-/
theorem State.TaskMembershipAbsent.pruneEmptyGroups {queue : State} {occurrence}
    (absent : queue.TaskMembershipAbsent occurrence) (groups)
    : (queue.pruneEmptyGroups groups).1.TaskMembershipAbsent occurrence := by
  exact State.pruneEmptyGroups_nodeProperty (fun node => occurrence ∉ node.tasks) absent groups

/-- The complete task flush preserves all earlier membership exclusions.
Witness: each selected task is removed globally; a missing lookup changes nothing.
-/
theorem State.TaskMembershipAbsent.flushGroupTasks {queue : State} {occurrence}
    (absent : queue.TaskMembershipAbsent occurrence) (tasks : List Occurrence)
    (values : List ExecutionGroupValue) (streams : NodeRefs)
    : (tasks.foldl flushGroupTask (queue, values, streams)).1.TaskMembershipAbsent
        occurrence := by
  induction tasks generalizing queue values streams with
  | nil => exact absent
  | cons task rest ih =>
      simp only [List.foldl_cons, flushGroupTask]
      split
      · exact ih absent _ _
      · exact ih (absent.removeTask task) _ _

/-- An initially findable selected task is absent from every group after the flush.
Witness: its first selected occurrence removes it globally. Earlier different removals
preserve its exact lookup, and the remaining loop preserves the exclusion. No source,
ref uniqueness, distinct membership, or already-admitted-history premise is needed.
-/
theorem flushGroupTask_membershipAbsent {queue : State} {tasks : List Occurrence}
    (values : List ExecutionGroupValue) (streams : NodeRefs) {occurrence node}
    (member : occurrence ∈ tasks) (found : queue.taskNode? occurrence = some node)
    : (tasks.foldl flushGroupTask (queue, values, streams)).1.TaskMembershipAbsent
        occurrence := by
  induction tasks generalizing queue values streams with
  | nil => cases member
  | cons head rest ih =>
      by_cases same : occurrence = head
      · subst head
        simp only [List.foldl_cons, flushGroupTask, found]
        exact (queue.removeTask_membershipAbsent occurrence).flushGroupTasks rest _ _
      · have later := (List.mem_cons.mp member).resolve_left same
        simp only [List.foldl_cons, flushGroupTask]
        split
        · exact ih _ _ later found
        · apply ih _ _ later
          rwa [queue.removeTask_lookup_other same]

-----------------------------------------------------------------------------------------
-- Successful closure keeps that exclusion through group removal and child promotion
-----------------------------------------------------------------------------------------

/-- Successful closure preserves exclusions established by earlier publications.
Witness: task removal, filtering the closed owner, and pruning can only remove memberships.
-/
theorem State.TaskMembershipAbsent.finishGroupSuccess {queue : State} {occurrence}
    (absent : queue.TaskMembershipAbsent occurrence) (group : GroupNode)
    : (queue.finishGroupSuccess group).1.TaskMembershipAbsent occurrence := by
  have flushed := absent.flushGroupTasks group.tasks [] []
  let values := group.tasks.foldl flushGroupTask (queue, [], [])
  let current : State := { values.1 with
    groupNodes := values.1.groupNodes.filter
      (fun node => node.group.node.ref != group.group.node.ref)
    rootGroups := values.1.rootGroups.filter (· != group.group.node.ref) }
  have removed : current.TaskMembershipAbsent occurrence :=
    fun node member => flushed node (List.mem_filter.mp member).1
  exact removed.pruneEmptyGroups _

/-- A flushed membership cannot remain in a child or any other surviving co-owner.
Witness: the actual findable-task selection removes the occurrence from every group's
list before the closing owner is removed and taskless child wrappers are pruned.
This supplies local publication exclusion for the kept-notice contents bridge.
-/
theorem State.finishGroupSuccess_membershipAbsent {queue : State} (group : GroupNode)
    {occurrence node} (member : occurrence ∈ group.tasks)
    (found : queue.taskNode? occurrence = some node)
    : (queue.finishGroupSuccess group).1.TaskMembershipAbsent occurrence := by
  have flushed := flushGroupTask_membershipAbsent [] [] member found
  let values := group.tasks.foldl flushGroupTask (queue, [], [])
  let current : State := { values.1 with
    groupNodes := values.1.groupNodes.filter
      (fun node => node.group.node.ref != group.group.node.ref)
    rootGroups := values.1.rootGroups.filter (· != group.group.node.ref) }
  have removed : current.TaskMembershipAbsent occurrence :=
    fun node member => flushed node (List.mem_filter.mp member).1
  exact removed.pruneEmptyGroups _

/-- Any selected stored node's occurrence is removed from all surviving memberships.
Witness: its original task-map membership ensures a successful lookup, even when raw
task nodes duplicate an occurrence. The flush's selection premise places it on the list.
-/
theorem State.finishGroupSuccess_selectedMembershipAbsent {queue : State}
    (group : GroupNode) {node : TaskNode} (known : node ∈ queue.taskNodes)
    (selected : node.task.occurrence ∈ group.tasks)
    : (queue.finishGroupSuccess group).1.TaskMembershipAbsent node.task.occurrence := by
  cases found : queue.taskNode? node.task.occurrence with
  | none =>
      have impossible := List.find?_eq_none.mp found node known
      simp [(occurrence_beq_iff_eq node.task.occurrence node.task.occurrence).mpr rfl]
        at impossible
  | some task => exact queue.finishGroupSuccess_membershipAbsent group selected found

/-- Cache exposure leaves every live task-membership list unchanged. -/
theorem State.TaskMembershipAbsent.cacheTaskFailures {queue : State} {occurrence}
    (absent : queue.TaskMembershipAbsent occurrence) (available : List (Occurrence × Nat))
    : (queue.cacheTaskFailures available).TaskMembershipAbsent occurrence := by
  intro node member
  rw [State.cacheTaskFailures_groupNodes] at member
  exact absent node member

/-- Startup preserves publication exclusion on every surviving group record. -/
theorem State.TaskMembershipAbsent.startNewWork {queue : State} {occurrence}
    (absent : queue.TaskMembershipAbsent occurrence) (newWork : NewWork)
    (available : List (Occurrence × Nat) := [])
    : (queue.startNewWork newWork available).1.TaskMembershipAbsent occurrence := by
  intro node member
  exact absent node ((queue.startNewWork_groupNodes_sublist newWork available).subset member)

/-- Cancelling a group only removes records and cannot restore delivered memberships.
Witness: surviving records belong to the original group-node map.
-/
theorem State.TaskMembershipAbsent.removeGroup {queue : State} {occurrence}
    (absent : queue.TaskMembershipAbsent occurrence) (ref : NodeRef)
    : (queue.removeGroup ref).TaskMembershipAbsent occurrence :=
  fun node member => absent node (List.mem_filter.mp member).1

/-- Rejection processing only removes group records and keeps surviving memberships. -/
theorem State.TaskMembershipAbsent.taskFailure_preserves {queue : State} {occurrence}
    (absent : queue.TaskMembershipAbsent occurrence) (failed : Occurrence) (errors : Nat)
    : (queue.taskFailure failed errors).1.TaskMembershipAbsent occurrence := by
  cases found : queue.taskNode? failed with
  | none => simpa [State.taskFailure, found] using absent
  | some task =>
      rw [queue.taskFailure_eq failed errors task found]
      exact failureGroupFold_preserves (fun next => next.TaskMembershipAbsent occurrence)
        (fun _ ref valid => valid.removeGroup ref) errors task.task.groups _ absent

/-- Every bounded drain prefix preserves any earlier publication's membership exclusion.
Witness: successful flushing and activation preserve the absent membership; failed
closure only removes records. The induction does not select a publication ledger.
-/
theorem State.TaskMembershipAbsent.drainReadyGroups_go {queue : State} {occurrence}
    (absent : queue.TaskMembershipAbsent occurrence) (fuel : Nat)
    (available : List (Occurrence × Nat) := [])
    : (State.drainReadyGroups.go available fuel queue).1.TaskMembershipAbsent
        occurrence := by
  induction fuel generalizing queue with
  | zero => exact absent
  | succ fuel ih =>
      unfold State.drainReadyGroups.go
      dsimp only
      split
      · exact absent
      · rename_i node selected
        exact ih ((absent.finishGroupSuccess node).startNewWork _ available)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
