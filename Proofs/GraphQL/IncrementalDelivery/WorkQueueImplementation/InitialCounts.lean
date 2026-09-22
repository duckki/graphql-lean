import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupKeys

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
    (fun old => if old.group.node.key == updated.group.node.key then updated else old)
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
  unfold State.addGroup
  split
  · exact counts
  · split
    · exact counts
    · intro node member
      simp only [List.mem_append, List.mem_singleton] at member
      rcases member with earlier | new
      · exact counts node earlier
      · subst node
        rfl

/-- Group registration and parent-link installation preserve zero-task shells and
all existing pending counts. Witness: two folds, neither changing task counts alone.
-/
theorem State.InitialCounts.addGroups {queue : State} (counts : queue.InitialCounts)
    (groups : List Group)
    : (queue.addGroups groups).1.InitialCounts := by
  let linkStep (current : State) (group : Group) : State :=
    match group.parent with
    | none => current
    | some parent =>
        match current.groupNode? parent with
        | none => current
        | some node =>
            let children :=
              if node.childGroups.contains group.node.key then
                node.childGroups
              else
                node.childGroups ++ [group.node.key]
            current.putGroupNode { node with childGroups := children }
  have linkCounts (current : State) (group : Group)
      (balanced : current.InitialCounts) : (linkStep current group).InitialCounts := by
    unfold linkStep
    cases parent : group.parent with
    | none => simpa only [parent] using balanced
    | some key =>
        cases found : current.groupNode? key with
        | none => simpa only [parent, found] using balanced
        | some node =>
            simp only [found]
            apply balanced.putGroupNode
            exact balanced node (List.mem_of_find?_eq_some found)
  have foldCounts (more : List Group) :
      ∀ current, current.InitialCounts → (more.foldl linkStep current).InitialCounts := by
    induction more with
    | nil => intro current balanced; exact balanced
    | cons group rest ih =>
        intro current balanced
        exact ih (linkStep current group) (linkCounts current group balanced)
  have registeredCounts (more : List Group) : (more.foldl State.addGroup queue).InitialCounts := by
    induction more generalizing queue with
    | nil => exact counts
    | cons group rest ih =>
        simpa only [List.foldl_cons]
          using ih (queue := queue.addGroup group) (counts.addGroup group)
  let fresh := groups.filter (fun group =>
    !queue.registeredGroups.contains group.node.key
      && (queue.groupNode? group.node.key).isNone)
  change (fresh.foldl linkStep (fresh.foldl State.addGroup queue)).InitialCounts
  exact foldCounts fresh _ (registeredCounts fresh)

/-- Task registration adds one pending token wherever it adds a group membership. -/
theorem State.InitialCounts.addTask {queue : State} (counts : queue.InitialCounts)
    (task : Task)
    : (queue.addTask task).InitialCounts := by
  let registered : State := { queue with tasks := queue.tasks ++ [task] }
  let step (current : State) (group : Execution.DeliveryNode) : State :=
    match current.groupNode? group.key with
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
  change (if task.groups.any (fun group => current.rootGroups.contains group.key)
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
        if (queue.stream? stream.node.key).isSome
            || selected.any (fun known => known.node.key == stream.node.key) then
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

/-- Starting a group preserves every pending count through its task fold. -/
theorem State.InitialCounts.startGroup {queue : State} (counts : queue.InitialCounts)
    (key : Nat)
    : (queue.startGroup key).InitialCounts := by
  unfold State.startGroup
  split
  · exact counts
  · rename_i node found
    have taskFold (tasks : List Occurrence) :
        ∀ current, current.InitialCounts →
          (tasks.foldl State.startTask current).InitialCounts := by
      induction tasks with
      | nil => intro current balanced; exact balanced
      | cons task rest ih =>
          intro current balanced
          exact ih (current.startTask task) (balanced.startTask task)
    split
    · exact counts
    · exact taskFold node.tasks queue counts

/-- Starting a stream changes only its root-key registry. -/
theorem State.InitialCounts.startStream {queue : State} (counts : queue.InitialCounts)
    (key : Nat)
    : (queue.startStream key).InitialCounts := by
  unfold State.startStream
  split <;> exact counts

/-- Releasing new roots preserves initial counts through group and stream starts. -/
theorem State.InitialCounts.startNewWork {queue : State} (counts : queue.InitialCounts)
    (newWork : NewWork)
    : (queue.startNewWork newWork).InitialCounts := by
  let groups := newWork.newGroups.map Execution.DeliveryNode.key
  let streams := newWork.newStreams.map Execution.DeliveryNode.key
  let current : State := { queue with rootGroups := queue.rootGroups ++ groups }
  have groupFold (keys : Keys) :
      ∀ current, current.InitialCounts →
        (keys.foldl State.startGroup current).InitialCounts := by
    induction keys with
    | nil => intro current balanced; exact balanced
    | cons key rest ih =>
        intro current balanced
        exact ih (current.startGroup key) (balanced.startGroup key)
  have streamFold (keys : Keys) :
      ∀ current, current.InitialCounts →
        (keys.foldl State.startStream current).InitialCounts := by
    induction keys with
    | nil => intro current balanced; exact balanced
    | cons key rest ih =>
        intro current balanced
        exact ih (current.startStream key) (balanced.startStream key)
  change (streams.foldl State.startStream
    (groups.foldl State.startGroup current)).InitialCounts
  exact streamFold streams _ (groupFold groups current counts)

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
  let started := pruned.startNewWork roots
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
