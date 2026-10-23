import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupRefs
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupFrames

/-! Initial pending counts produced by work integration. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Before any settlement, every registered group has one pending token per task. -/
def State.InitialCounts (queue : State) : Prop :=
  ∀ node ∈ queue.groupNodes, node.pending = node.tasks.length

/-- Replacing group metadata preserves initial counts when the replacement has the
same pending-token count as its task list. Witness: every other node is unchanged.
-/
theorem State.InitialCounts.putGroupNode {queue : State} (counts : queue.InitialCounts)
    (updated : GroupNode) (balanced : updated.pending = updated.tasks.length)
    : (queue.putGroupNode updated).InitialCounts := by
  intro node member
  change node ∈ queue.groupNodes.map
    (fun old => if old.group.node.ref == updated.group.node.ref then updated else old)
    at member
  obtain ⟨old, oldMember, same⟩ := List.mem_map.mp member
  split at same
  · subst node
    exact balanced
  · subst node
    exact counts old oldMember

/-- Registering one group with no tasks preserves the initial count invariant. -/
theorem State.InitialCounts.addGroup {queue : State} (counts : queue.InitialCounts)
    (group : Group)
    : (queue.addGroup group).InitialCounts := by
  have appended : ({ queue with
      groupNodes := queue.groupNodes ++ [({ group } : GroupNode)] } : State).InitialCounts := by
    intro node member
    rcases List.mem_append.mp member with earlier | new
    · exact counts node earlier
    · have same := List.mem_singleton.mp new
      subst node
      rfl
  unfold State.addGroup
  split
  · exact counts
  · split
    · exact appended
    · split
      · split <;> exact counts
      · rename_i node found
        exact appended.putGroupNode _ (counts node (List.mem_of_find?_eq_some found))

/-- Parent-first registration preserves all task counts while installing empty shells. -/
theorem State.InitialCounts.addGroups {queue : State} (counts : queue.InitialCounts)
    (groups : List Group)
    : (queue.addGroups groups).1.InitialCounts := by
  exact State.addGroups_preserves State.InitialCounts groups
    (fun _ group _ valid => valid.addGroup group) queue counts

/-- Task registration adds one pending token wherever it adds a group membership. -/
theorem State.InitialCounts.addTask {queue : State} (counts : queue.InitialCounts)
    (task : Task)
    : (queue.addTask task).InitialCounts := by
  let registered : State := { queue with tasks := queue.tasks ++ [task] }
  let step (current : State) (group : Execution.DeliveryNode) : State :=
    match current.groupNode? group.ref with
    | none => current
    | some node =>
        if node.tasks.contains task.occurrence then
          current
        else
          current.putGroupNode
            {
              node with
                tasks := node.tasks ++ [task.occurrence], pending := node.pending + 1
            }
  have stepCounts (current : State) (group : Execution.DeliveryNode)
      (balanced : current.InitialCounts) : (step current group).InitialCounts := by
    unfold step
    split
    · exact balanced
    · rename_i node found
      split
      · exact balanced
      · have nodeMember : node ∈ current.groupNodes := by
          exact List.mem_of_find?_eq_some found
        have nodeCount := balanced node nodeMember
        apply balanced.putGroupNode
        simp [nodeCount]
  have foldCounts (groups : List Execution.DeliveryNode) :
      ∀ current, current.InitialCounts → (groups.foldl step current).InitialCounts := by
    induction groups with
    | nil => intro current balanced; exact balanced
    | cons group rest ih =>
        intro current balanced
        exact ih (step current group) (stepCounts current group balanced)
  let current := task.groups.foldl step registered
  have currentCounts : current.InitialCounts :=
    foldCounts task.groups registered counts
  change (if task.groups.any (fun group => current.rootGroups.contains group.ref)
      && (current.taskNode? task.occurrence).isNone then
      { current with taskNodes := current.taskNodes ++ [{ task }] }
    else current).InitialCounts
  split <;> exact currentCounts

/-- Registering streams changes no group's pending count or task list. -/
theorem State.InitialCounts.addStreams {queue : State} (counts : queue.InitialCounts)
    (streams : List Stream) (parentTask : Option Occurrence)
    : (queue.addStreams streams parentTask).1.InitialCounts := by
  let fresh :=
    streams.foldl
      (fun selected stream =>
        if (queue.stream? stream.node.ref).isSome
            || selected.any (fun known => known.node.ref == stream.node.ref) then
          selected
        else
          selected ++ [stream])
      []
  let current : State := { queue with streams := queue.streams ++ fresh }
  have currentCounts : current.InitialCounts := counts
  cases parentTask with
  | none => exact currentCounts
  | some occurrence =>
      simp only [State.addStreams]
      split <;> exact currentCounts

/-- Integrating immediate Work preserves initial task-count accounting. Witness:
group registration, task registration, then stream registration.
-/
theorem State.InitialCounts.maybeIntegrateWork {queue : State}
    (counts : queue.InitialCounts) (work : Work)
    (parentTask : Option Occurrence := none)
    : (queue.maybeIntegrateWork work parentTask).1.InitialCounts := by
  let withGroups := (queue.addGroups work.groups).1
  let withTasks := work.tasks.foldl State.addTask withGroups
  have taskFold (tasks : List Task) :
      ∀ current, current.InitialCounts → (tasks.foldl State.addTask current).InitialCounts := by
    induction tasks with
    | nil => intro current balanced; exact balanced
    | cons task rest ih =>
        intro current balanced
        exact ih (current.addTask task) (balanced.addTask task)
  have tasksCounts : withTasks.InitialCounts :=
    taskFold work.tasks withGroups (counts.addGroups work.groups)
  change (withTasks.addStreams work.streams parentTask).1.InitialCounts
  exact tasksCounts.addStreams work.streams parentTask

/-- Removing group shells cannot invalidate the count equation for retained nodes. -/
theorem State.InitialCounts.filterGroupNodes {queue : State}
    (counts : queue.InitialCounts) (keep : GroupNode → Bool)
    : ({ queue with groupNodes := queue.groupNodes.filter keep }).InitialCounts := by
  intro node member
  exact counts node (List.mem_filter.mp member).1

/-- Pruning empty shells preserves the initial pending-count invariant. Witness:
induction on the finite pruning fuel, using only filtering in the removal branch.
-/
theorem State.InitialCounts.pruneEmptyGroups {queue : State}
    (counts : queue.InitialCounts) (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.InitialCounts := by
  have loop (fuel : Nat) (current : State)
      (remaining kept : List Execution.DeliveryNode)
      (balanced : current.InitialCounts)
      : (State.pruneEmptyGroups.go fuel current remaining kept).1.InitialCounts := by
    induction fuel generalizing current remaining kept with
    | zero => exact balanced
    | succ fuel ih =>
        cases remaining with
        | nil => exact balanced
        | cons group rest =>
            unfold State.pruneEmptyGroups.go
            split
            · exact ih _ _ _ balanced
            · split
              · exact ih _ _ _ (balanced.filterGroupNodes _)
              · exact ih _ _ _ balanced
  exact loop _ queue groups [] counts

/-- Starting a task only changes started-task bookkeeping, not group counts. -/
theorem State.InitialCounts.startTask {queue : State} (counts : queue.InitialCounts)
    (occurrence : Occurrence)
    : (queue.startTask occurrence).InitialCounts := by
  unfold State.startTask
  split
  · exact counts
  · split <;> exact counts

/-- Group startup only removes records, preserving counts on all surviving groups. -/
theorem State.InitialCounts.startGroup {queue : State} (counts : queue.InitialCounts)
    (ref : NodeRef) (available : List (Occurrence × Nat) := [])
    : (queue.startGroup ref available).1.InitialCounts := by
  intro node member
  exact counts node ((queue.startGroup_groupNodes_sublist ref available).subset member)

/-- Starting a stream changes only its root-ref registry. -/
theorem State.InitialCounts.startStream {queue : State} (counts : queue.InitialCounts)
    (ref : NodeRef)
    : (queue.startStream ref).InitialCounts := by
  unfold State.startStream
  split <;> exact counts

/-- Root activation preserves counts because its only group changes are removals. -/
theorem State.InitialCounts.startNewWork {queue : State} (counts : queue.InitialCounts)
    (newWork : NewWork) (available : List (Occurrence × Nat) := [])
    : (queue.startNewWork newWork available).1.InitialCounts := by
  intro node member
  exact counts node ((queue.startNewWork_groupNodes_sublist newWork available).subset member)

/-- Queue creation balances every live group's initial pending count. Witness:
registration balances task memberships, pruning only removes nodes, and starting
new work does not alter group counts.
-/
theorem createWorkQueue_initialCounts (initialWork : Work)
    : (State.initialize initialWork).InitialCounts := by
  let integrated := (({} : State).maybeIntegrateWork initialWork).1
  let newWork := (({} : State).maybeIntegrateWork initialWork).2
  let pruned := (integrated.pruneEmptyGroups newWork.newGroups).1
  let groups := (integrated.pruneEmptyGroups newWork.newGroups).2
  let roots := { newWork with newGroups := groups }
  let started := (pruned.startNewWork roots).1
  have emptyCounts : ({} : State).InitialCounts := by
    intro node member
    cases member
  have integratedCounts : integrated.InitialCounts :=
    emptyCounts.maybeIntegrateWork initialWork
  have prunedCounts : pruned.InitialCounts :=
    integratedCounts.pruneEmptyGroups newWork.newGroups
  have startedCounts : started.InitialCounts := prunedCounts.startNewWork roots
  change State.InitialCounts
    { started with initialGroups := groups, initialStreams := roots.newStreams }
  exact startedCounts

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
