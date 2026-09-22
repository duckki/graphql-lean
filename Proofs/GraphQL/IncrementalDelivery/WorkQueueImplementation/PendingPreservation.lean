import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PendingDebt
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureDebt
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ReadyDrain

/-! Pending-count preservation across queue operations. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (
  ExecutionGroupValue StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Replacing one group preserves the ledger when the replacement is balanced. -/
theorem State.PendingTracks.putGroupNode {queue : State}
    {settled : List Occurrence} (tracks : queue.PendingTracks settled)
    (updated : GroupNode) (balanced : updated.PendingTracks settled)
    : (queue.putGroupNode updated).PendingTracks settled := by
  intro node member
  change node ∈ queue.groupNodes.map
    (fun old => if old.group.node.key == updated.group.node.key then updated else old)
    at member
  obtain ⟨old, oldMember, same⟩ := List.mem_map.mp member
  split at same
  · subst node
    exact balanced
  · subst node
    exact tracks old oldMember

/-- Registering an empty group shell preserves every pending-token equation. -/
theorem State.PendingTracks.addGroup {queue : State}
    {settled : List Occurrence} (tracks : queue.PendingTracks settled)
    (group : Group)
    : (queue.addGroup group).PendingTracks settled := by
  unfold State.addGroup
  split
  · exact tracks
  · split
    · exact tracks
    · intro node member
      simp only [List.mem_append, List.mem_singleton] at member
      rcases member with earlier | new
      · exact tracks node earlier
      · subst node
        simp [GroupNode.PendingTracks, unsettledCount]

/-- Parent-link installation leaves the group ledger unchanged. -/
theorem State.PendingTracks.addGroups {queue : State}
    {settled : List Occurrence} (tracks : queue.PendingTracks settled)
    (groups : List Group)
    : (queue.addGroups groups).1.PendingTracks settled := by
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
  have linkTracks (current : State) (group : Group)
      (balanced : current.PendingTracks settled)
      : (linkStep current group).PendingTracks settled := by
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
  have linkFold (more : List Group) :
      ∀ current, current.PendingTracks settled →
        (more.foldl linkStep current).PendingTracks settled := by
    induction more with
    | nil => intro current balanced; exact balanced
    | cons group rest ih =>
        intro current balanced
        exact ih (linkStep current group) (linkTracks current group balanced)
  have registered (more : List Group) :
      (more.foldl State.addGroup queue).PendingTracks settled := by
    induction more generalizing queue with
    | nil => exact tracks
    | cons group rest ih =>
        simpa only [List.foldl_cons]
          using ih (queue := queue.addGroup group) (tracks.addGroup group)
  let fresh := groups.filter (fun group =>
    !queue.registeredGroups.contains group.node.key
      && (queue.groupNode? group.node.key).isNone)
  change (fresh.foldl linkStep (fresh.foldl State.addGroup queue)).PendingTracks settled
  exact linkFold fresh _ (registered fresh)

/-- Registering a task preserves the ledger when its settlement has not yet
occurred. This freshness is supplied by the host event-prefix contract.
-/
theorem State.PendingTracks.addTask {queue : State}
    {settled : List Occurrence} (tracks : queue.PendingTracks settled)
    (task : Task) (fresh : task.occurrence ∉ settled)
    : (queue.addTask task).PendingTracks settled := by
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
  have stepTracks (current : State) (group : Execution.DeliveryNode)
      (balanced : current.PendingTracks settled)
      : (step current group).PendingTracks settled := by
    unfold step
    split
    · exact balanced
    · rename_i node found
      split
      · exact balanced
      · apply balanced.putGroupNode
        exact GroupNode.PendingTracks.register node settled task.occurrence
          (balanced node (List.mem_of_find?_eq_some found)) fresh
  have foldTracks (groups : List Execution.DeliveryNode) :
      ∀ current, current.PendingTracks settled →
        (groups.foldl step current).PendingTracks settled := by
    induction groups with
    | nil => intro current balanced; exact balanced
    | cons group rest ih =>
        intro current balanced
        exact ih (step current group) (stepTracks current group balanced)
  let current := task.groups.foldl step registered
  have currentTracks : current.PendingTracks settled :=
    foldTracks task.groups registered tracks
  change (if task.groups.any (fun group => current.rootGroups.contains group.key)
      && (current.taskNode? task.occurrence).isNone then
      { current with taskNodes := current.taskNodes ++ [{ task }] }
    else current).PendingTracks settled
  split <;> exact currentTracks

/-- Stream registration changes no live group accounting. -/
theorem State.PendingTracks.addStreams {queue : State}
    {settled : List Occurrence} (tracks : queue.PendingTracks settled)
    (streams : List Stream) (parentTask : Option Occurrence)
    : (queue.addStreams streams parentTask).1.PendingTracks settled := by
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
  have currentTracks : current.PendingTracks settled := tracks
  cases parentTask with
  | none => exact currentTracks
  | some occurrence =>
      simp only [State.addStreams]
      split <;> exact currentTracks

/-- Integrating child work preserves pending counts when each new task is
unsettled in the existing event prefix.
-/
theorem State.PendingTracks.maybeIntegrateWork {queue : State}
    {settled : List Occurrence} (tracks : queue.PendingTracks settled)
    (work : Work) (fresh : ∀ task ∈ work.tasks, task.occurrence ∉ settled)
    (parentTask : Option Occurrence := none)
    : (queue.maybeIntegrateWork work parentTask).1.PendingTracks settled := by
  let withGroups := (queue.addGroups work.groups).1
  let withTasks := work.tasks.foldl State.addTask withGroups
  have taskFold (tasks : List Task) (allFresh : ∀ task ∈ tasks, task.occurrence ∉ settled) :
      ∀ current, current.PendingTracks settled →
        (tasks.foldl State.addTask current).PendingTracks settled := by
    induction tasks with
    | nil => intro current balanced; exact balanced
    | cons task rest ih =>
        intro current balanced
        have taskFresh := allFresh task (by simp)
        have restFresh : ∀ next ∈ rest, next.occurrence ∉ settled := by
          intro next member
          exact allFresh next (by simp [member])
        exact ih restFresh (current.addTask task) (balanced.addTask task taskFresh)
  have taskTracks : withTasks.PendingTracks settled :=
    taskFold work.tasks fresh withGroups (tracks.addGroups work.groups)
  change (withTasks.addStreams work.streams parentTask).1.PendingTracks settled
  exact taskTracks.addStreams work.streams parentTask

/-- Pruning may discard group nodes but cannot change retained counters. -/
theorem State.PendingTracks.pruneEmptyGroups {queue : State}
    {settled : List Occurrence} (tracks : queue.PendingTracks settled)
    (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.PendingTracks settled := by
  have loop (fuel : Nat) (current : State)
      (remaining kept : List Execution.DeliveryNode)
      (balanced : current.PendingTracks settled)
      : (State.pruneEmptyGroups.go fuel current remaining kept).1.PendingTracks settled := by
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
              · apply ih
                intro node member
                exact balanced node (List.mem_filter.mp member).1
              · exact ih _ _ _ balanced
  exact loop _ queue groups [] tracks

/-- Failure pruning retains unchanged ledgers on surviving group nodes. -/
theorem State.PendingTracks.removeGroup {queue : State}
    {settled : List Occurrence} (tracks : queue.PendingTracks settled)
    (key : Nat)
    : (queue.removeGroup key).PendingTracks settled := by
  intro node member
  exact tracks node (List.mem_filter.mp member).1

/-- A group flush removes only already-settled task memberships. The queue's
pending counters therefore continue to count precisely the unsettled ones.
-/
theorem State.PendingTracks.removeTask {queue : State}
    {settled : List Occurrence} (tracks : queue.PendingTracks settled)
    (occurrence : Occurrence) (already : occurrence ∈ settled)
    : (queue.removeTask occurrence).PendingTracks settled := by
  intro node member
  change node ∈ queue.groupNodes.map
    (fun prior => { prior with tasks := prior.tasks.filter (· != occurrence) })
    at member
  obtain ⟨prior, priorMember, same⟩ := List.mem_map.mp member
  subst node
  change prior.pending = unsettledCount
    (prior.tasks.filter (· != occurrence)) settled
  rw [unsettledCount_remove_settled prior.tasks settled occurrence already]
  exact tracks prior priorMember

/-- A zero-pending group flush removes only settled memberships and otherwise
prunes unchanged group nodes. Its raw value and notice events do not affect
the accounting ledger.
-/
theorem State.PendingTracks.finishGroupSuccess {queue : State}
    {settled : List Occurrence} (tracks : queue.PendingTracks settled)
    (group : GroupNode) (all : ∀ occurrence ∈ group.tasks, occurrence ∈ settled)
    : (queue.finishGroupSuccess group).1.PendingTracks settled := by
  let step (acc : State × List ExecutionGroupValue × Keys)
      (occurrence : Occurrence) :=
    let (current, values, streams) := acc
    match current.taskNode? occurrence with
    | none => (current, values, streams)
    | some taskNode =>
        let values :=
          match taskNode.value with
          | none => values
          | some value => values ++ [value]
        (current.removeTask occurrence, values, streams ++ taskNode.childStreams)
  have stepTracks (acc : State × List ExecutionGroupValue × Keys)
      (occurrence : Occurrence) (balanced : acc.1.PendingTracks settled)
      (already : occurrence ∈ settled)
      : (step acc occurrence).1.PendingTracks settled := by
    obtain ⟨current, values, streams⟩ := acc
    dsimp only [step]
    split
    · exact balanced
    · exact balanced.removeTask occurrence already
  have foldTracks (tasks : List Occurrence)
      (all : ∀ occurrence ∈ tasks, occurrence ∈ settled) :
      ∀ acc : State × List ExecutionGroupValue × Keys,
        acc.1.PendingTracks settled →
          (tasks.foldl step acc).1.PendingTracks settled := by
    induction tasks with
    | nil => intro acc balanced; exact balanced
    | cons occurrence rest ih =>
        intro acc balanced
        have head : occurrence ∈ settled := all occurrence (by simp)
        have tail : ∀ task ∈ rest, task ∈ settled := by
          intro task member
          exact all task (by simp [member])
        exact ih tail (step acc occurrence) (stepTracks acc occurrence balanced head)
  let flushed := (group.tasks.foldl step (queue, [], [])).1
  have flushedTracks : flushed.PendingTracks settled :=
    foldTracks group.tasks all (queue, [], []) tracks
  let current : State :=
    { flushed with
        groupNodes := flushed.groupNodes.filter
          (fun node => node.group.node.key != group.group.node.key)
        rootGroups := flushed.rootGroups.filter (· != group.group.node.key) }
  have currentTracks : current.PendingTracks settled := by
    intro node member
    exact flushedTracks node (List.mem_filter.mp member).1
  let children := group.childGroups.filterMap
    (fun key => (current.groupNode? key).map (fun node => node.group.node))
  change (current.pruneEmptyGroups children).1.PendingTracks settled
  exact currentTracks.pruneEmptyGroups children

/-- The group-release fold following a task settlement preserves the global
pending ledger. A zero counter justifies flushing only settled memberships.
-/
theorem State.PendingTracks.releaseTaskGroups {queue : State}
    {settled : List Occurrence} (tracks : queue.PendingTracks settled)
    (groups : List Execution.DeliveryNode)
    : (groups.foldl
        (fun (acc : State × List WorkQueueEvent × NewWork) group =>
          let (current, events, released) := acc
          match current.groupNode? group.key with
          | none => (current, events, released)
          | some node =>
              if current.rootGroups.contains group.key && node.pending == 0 then
                let (next, finished, newWork) := current.finishGroupSuccess node
                (
                  next,
                  events ++ finished,
                  ⟨
                    released.newGroups ++ newWork.newGroups,
                    released.newStreams ++ newWork.newStreams
                  ⟩
                )
              else
                (current, events, released))
        (queue, [], {})).1.PendingTracks
        settled := by
  let step (acc : State × List WorkQueueEvent × NewWork)
      (group : Execution.DeliveryNode) : State × List WorkQueueEvent × NewWork :=
    let (current, events, released) := acc
    match current.groupNode? group.key with
    | none => (current, events, released)
    | some node =>
        if current.rootGroups.contains group.key && node.pending == 0 then
          let (next, finished, newWork) := current.finishGroupSuccess node
          (next, events ++ finished,
            ⟨released.newGroups ++ newWork.newGroups,
              released.newStreams ++ newWork.newStreams⟩)
        else
          (current, events, released)
  have stepTracks (acc : State × List WorkQueueEvent × NewWork)
      (group : Execution.DeliveryNode)
      (balanced : acc.1.PendingTracks settled)
      : (step acc group).1.PendingTracks settled := by
    obtain ⟨current, events, released⟩ := acc
    dsimp only [step]
    split
    · exact balanced
    · rename_i node found
      split
      · rename_i ready
        have zero : node.pending = 0 := by
          have pendingZero := (Bool.and_eq_true_iff.mp ready).2
          exact beq_iff_eq.mp pendingZero
        have nodeMember : node ∈ current.groupNodes :=
          List.mem_of_find?_eq_some found
        exact balanced.finishGroupSuccess node
          (GroupNode.PendingTracks.allSettled node settled
            (balanced node nodeMember) zero)
      · exact balanced
  have foldTracks (more : List Execution.DeliveryNode) :
      ∀ acc : State × List WorkQueueEvent × NewWork,
        acc.1.PendingTracks settled →
          (more.foldl step acc).1.PendingTracks settled := by
    induction more with
    | nil => intro acc balanced; exact balanced
    | cons group rest ih =>
        intro acc balanced
        exact ih (step acc group) (stepTracks acc group balanced)
  exact foldTracks groups (queue, [], {}) tracks

/-- Failed-group closure only removes group nodes, preserving the ledger of
every group that remains live.
-/
theorem State.PendingTracks.finishGroupFailure {queue : State}
    {settled : List Occurrence} (tracks : queue.PendingTracks settled)
    (group : GroupNode) (errors : Nat)
    : (queue.finishGroupFailure group errors).1.PendingTracks settled :=
  tracks.removeGroup group.group.node.key

/-- A fresh failed task discharges each contributor's pending token exactly once.
Witness: exact ownership starts one debt per distinct contributor; membership removal
preserves that debt, and the failure fold either removes the owner or pays its decrement.
This is the active branch; ignored settlements do not decrement retained group counters.
These are internal bookkeeping premises, not additional host-source assumptions.
-/
theorem State.PendingTracks.taskFailure {queue : State}
    {settled : List Occurrence} (tracks : queue.PendingTracks settled)
    (keyUnique : queue.GroupKeysUnique) (taskUnique : queue.TaskMembershipsUnique)
    (occurrence : Occurrence) (errors : Nat)
    (taskNode : TaskNode) (found : queue.taskNode? occurrence = some taskNode)
    (active : queue.taskHasHealthyOwner taskNode.task = true)
    (fresh : occurrence ∉ settled)
    (uniqueContributors : (taskNode.task.groups.map Execution.DeliveryNode.key).Nodup)
    (owned
      : queue.OwnedExactlyBy occurrence
          (taskNode.task.groups.map Execution.DeliveryNode.key))
    : (queue.taskFailure occurrence errors).1.PendingTracks (occurrence :: settled) := by
  have debt : queue.PendingDebt (fun _ => True) (occurrence :: settled)
      (taskNode.task.groups.map Execution.DeliveryNode.key) :=
    State.PendingDebt.beginSettlement (fun node member _ => tracks node member)
      taskUnique (fun node member _ => owned node member) fresh
  have removed := debt.removeTask occurrence (by simp)
  have facts := failureGroupFold_preserves (fun _ => True) (occurrence :: settled)
    State.GroupKeysUnique (fun _ valid => valid)
    (fun _ _ _ valid _ => valid.putGroupNode _)
    (fun _ key valid => valid.removeGroup key)
    errors taskNode.task.groups uniqueContributors (queue.removeTask occurrence, [])
    (keyUnique.removeTask occurrence) removed
  rw [queue.taskFailure_eq occurrence errors taskNode found]
  simp only [active, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  intro node member
  simpa [GroupNode.PendingTracks] using facts.2 node member trivial

/-- Closing a stream changes only its started-root registry. -/
theorem State.PendingTracks.streamSuccess {queue : State}
    {settled : List Occurrence} (tracks : queue.PendingTracks settled)
    (stream : Execution.DeliveryNode)
    : (queue.streamSuccess stream).1.PendingTracks settled := by
  unfold State.streamSuccess
  split <;> exact tracks

/-- Stream failure likewise leaves live group accounting untouched. -/
theorem State.PendingTracks.streamFailure {queue : State}
    {settled : List Occurrence} (tracks : queue.PendingTracks settled)
    (stream : Execution.DeliveryNode) (errors : Nat)
    : (queue.streamFailure stream errors).1.PendingTracks settled := by
  unfold State.streamFailure
  split <;> exact tracks

/-- Starting work changes roots and task-node registries, not pending counters. -/
theorem State.PendingTracks.startNewWork {queue : State}
    {settled : List Occurrence} (tracks : queue.PendingTracks settled)
    (newWork : NewWork)
    : (queue.startNewWork newWork).PendingTracks settled := by
  let groups := newWork.newGroups.map Execution.DeliveryNode.key
  let streams := newWork.newStreams.map Execution.DeliveryNode.key
  let current : State := { queue with rootGroups := queue.rootGroups ++ groups }
  have groupFold (keys : Keys) :
      ∀ current, current.PendingTracks settled →
        (keys.foldl State.startGroup current).PendingTracks settled := by
    induction keys with
    | nil => intro current balanced; exact balanced
    | cons key rest ih =>
        intro current balanced
        apply ih (current.startGroup key)
        unfold State.startGroup
        split
        · exact balanced
        · rename_i node found
          have taskFold (tasks : List Occurrence) :
              ∀ current, current.PendingTracks settled →
                (tasks.foldl State.startTask current).PendingTracks settled := by
            induction tasks with
            | nil => intro current counts; exact counts
            | cons task rest next =>
                intro current counts
                apply next (current.startTask task)
                unfold State.startTask
                split
                · exact counts
                · split <;> exact counts
          split
          · exact balanced
          · exact taskFold node.tasks current balanced
  have streamFold (keys : Keys) :
      ∀ current, current.PendingTracks settled →
        (keys.foldl State.startStream current).PendingTracks settled := by
    induction keys with
    | nil => intro current balanced; exact balanced
    | cons key rest ih =>
        intro current balanced
        apply ih (current.startStream key)
        unfold State.startStream
        split <;> exact balanced
  change (streams.foldl State.startStream
    (groups.foldl State.startGroup current)).PendingTracks settled
  exact streamFold streams _ (groupFold groups current tracks)

/-- Release-time draining preserves every surviving group's pending count.
Witness: zero-count healthy closures remove only settled memberships; cached failures
remove groups, and child activation leaves counters unchanged.
-/
theorem State.PendingTracks.drainReadyGroups {queue : State}
    {settled : List Occurrence} (tracks : queue.PendingTracks settled)
    : queue.drainReadyGroups.1.PendingTracks settled := by
  apply State.drainReadyGroups_preserves (fun state => state.PendingTracks settled)
    (fun _ node prior member _ _ zero =>
      (prior.finishGroupSuccess node
        (GroupNode.PendingTracks.allSettled node settled (prior node member) zero)).startNewWork _)
    (fun _ node errors prior _ _ _ => prior.finishGroupFailure node errors) tracks

/-- Task success preserves pending accounting once the host supplies fresh
child tasks, a healthy owner survives, and memberships match the task's contributors.
Witness: `successGroupFold_preserves` carries one decrement debt per remaining key.
-/
theorem State.PendingTracks.taskSuccess {queue : State}
    {settled : List Occurrence}
    (tracks : queue.PendingTracks settled)
    (keyUnique : queue.GroupKeysUnique)
    (taskUnique : queue.TaskMembershipsUnique)
    (occurrence : Occurrence) (result : TaskResult)
    (taskNode : TaskNode) (found : queue.taskNode? occurrence = some taskNode)
    (active : queue.taskHasHealthyOwner taskNode.task = true)
    (fresh : occurrence ∉ settled)
    (freshChildren : ∀ task ∈ result.work.tasks, task.occurrence ∉ settled)
    (uniqueContributors : (taskNode.task.groups.map Execution.DeliveryNode.key).Nodup)
    (owned
      : ((queue.putTaskNode
            { taskNode with value := some result.value }).maybeIntegrateWork
          result.work (some occurrence)).1.OwnedExactlyBy
          occurrence (taskNode.task.groups.map Execution.DeliveryNode.key))
    : (queue.taskSuccess occurrence result).1.PendingTracks (occurrence :: settled) := by
  let withValue := queue.putTaskNode { taskNode with value := some result.value }
  have withValueTracks : withValue.PendingTracks settled := tracks
  have withValueKeys : withValue.GroupKeysUnique := keyUnique
  have withValueTasks : withValue.TaskMembershipsUnique := taskUnique
  let integrated := (withValue.maybeIntegrateWork result.work (some occurrence)).1
  have integratedTracks : integrated.PendingTracks settled :=
    withValueTracks.maybeIntegrateWork result.work freshChildren (some occurrence)
  have integratedKeys : integrated.GroupKeysUnique :=
    withValueKeys.maybeIntegrateWork result.work (some occurrence)
  have integratedTasks : integrated.TaskMembershipsUnique :=
    withValueTasks.maybeIntegrateWork result.work (some occurrence)
  have debt : integrated.PendingDebt (fun _ => True) (occurrence :: settled)
      (taskNode.task.groups.map Execution.DeliveryNode.key) :=
    State.PendingDebt.beginSettlement (fun node member _ => integratedTracks node member)
      integratedTasks (fun node member _ => owned node member) fresh
  have facts := successGroupFold_preserves (fun _ => True) (occurrence :: settled)
    State.GroupKeysUnique (fun _ valid => valid) (by intros; trivial)
    (fun _ node valid _ => valid.putGroupNode _)
    (fun _ node _ valid _ _ _ _ _ => valid.finishGroupSuccess node)
    taskNode.task.groups uniqueContributors (integrated, [], {}) integratedKeys debt
  let released := taskNode.task.groups.foldl successGroupStep (integrated, [], {})
  have releasedTracks : released.1.PendingTracks (occurrence :: settled) := by
    intro node member
    simpa [GroupNode.PendingTracks] using facts.2 node member trivial
  rw [queue.taskSuccess_eq occurrence result taskNode found]
  simp only [active, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  exact (releasedTracks.startNewWork released.2.2).drainReadyGroups

/-- Publishing stream items integrates their child work without settling any
of its newly registered tasks. Their structural freshness preserves the
pending ledger across the entire item batch.
-/
theorem State.PendingTracks.streamItems {queue : State}
    {settled : List Occurrence} (tracks : queue.PendingTracks settled)
    (stream : Execution.DeliveryNode) (items : List StreamItem)
    (fresh : ∀ item ∈ items, ∀ task ∈ item.work.tasks, task.occurrence ∉ settled)
    : (queue.streamItems stream items).1.PendingTracks settled := by
  let step (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue)
      (item : StreamItem) :=
    let (current, groups, streams, values) := acc
    let (integrated, newWork) := current.maybeIntegrateWork item.work
    let (pruned, nonempty) := integrated.pruneEmptyGroups newWork.newGroups
    (
      pruned.startNewWork { newWork with newGroups := nonempty },
      groups ++ nonempty,
      streams ++ newWork.newStreams,
      values ++ [item.value]
    )
  have stepTracks (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue)
      (item : StreamItem) (balanced : acc.1.PendingTracks settled)
      (freshItem : ∀ task ∈ item.work.tasks, task.occurrence ∉ settled)
      : (step acc item).1.PendingTracks settled := by
    obtain ⟨current, groups, streams, values⟩ := acc
    let integrated := current.maybeIntegrateWork item.work
    have integratedTracks : integrated.1.PendingTracks settled :=
      balanced.maybeIntegrateWork item.work freshItem
    let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
    have prunedTracks : pruned.1.PendingTracks settled :=
      integratedTracks.pruneEmptyGroups integrated.2.newGroups
    exact prunedTracks.startNewWork { integrated.2 with newGroups := pruned.2 }
  have foldTracks (more : List StreamItem)
      (allFresh : ∀ item ∈ more,
        ∀ task ∈ item.work.tasks, task.occurrence ∉ settled) :
      ∀ acc : State × List Execution.DeliveryNode
        × List Execution.DeliveryNode × List StreamItemValue,
        acc.1.PendingTracks settled →
          (more.foldl step acc).1.PendingTracks settled := by
    induction more with
    | nil => intro acc balanced; exact balanced
    | cons item rest ih =>
        intro acc balanced
        have head := allFresh item (by simp)
        have tail : ∀ next ∈ rest,
            ∀ task ∈ next.work.tasks, task.occurrence ∉ settled := by
          intro next member
          exact allFresh next (by simp [member])
        exact ih tail (step acc item) (stepTracks acc item balanced head)
  dsimp only [State.streamItems]
  split
  · exact tracks
  · exact (foldTracks items fresh (queue, [], [], []) tracks).drainReadyGroups

/-- The queue's initial pending counts instantiate the ledger with no settled
tasks. The implementation need not store this proof-only list.
-/
theorem createWorkQueue_pendingTracks_empty (work : Work)
    : (State.initialize work).PendingTracks [] := by
  classical
  intro node member
  have count := createWorkQueue_initialCounts work node member
  have all : node.tasks.filter
      (fun task => decide (task ∉ ([] : List Occurrence))) = node.tasks := by
    apply List.filter_eq_self.mpr
    intro task taskMember
    simp
  change node.pending = unsettledCount node.tasks []
  unfold unsettledCount
  rw [all]
  exact count

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
