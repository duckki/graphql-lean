import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupProvenance

/-! Canonical immediate-parent metadata across queue transitions. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (
  ExecutionGroupValue StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

theorem State.GroupParentsCanonical.putGroupNode
    {queue : State} {parents : Nat → NodeRefs}
    (canonical : queue.GroupParentsCanonical parents)
    (updated : GroupNode)
    (updatedCanonical : updated.group.parent = (parents updated.group.node.ref).head?)
    : (queue.putGroupNode updated).GroupParentsCanonical parents := by
  intro node member
  change node ∈ queue.groupNodes.map
    (fun old => if old.group.node.ref == updated.group.node.ref then updated else old)
    at member
  obtain ⟨old, oldMember, same⟩ := List.mem_map.mp member
  split at same
  · subst node
    exact updatedCanonical
  · subst node
    exact canonical old oldMember

/-- Registering one group preserves canonical parents when its descriptor
uses the execution-assigned parent. -/
theorem State.GroupParentsCanonical.addGroup
    {queue : State} {parents : Nat → NodeRefs}
    (canonical : queue.GroupParentsCanonical parents)
    (group : Group)
    (groupCanonical : group.parent = (parents group.node.ref).head?)
    : (queue.addGroup group).GroupParentsCanonical parents := by
  have appended : ({ queue with
      groupNodes := queue.groupNodes ++ [({ group } : GroupNode)] } : State).GroupParentsCanonical parents := by
    intro node member
    rcases List.mem_append.mp member with old | fresh
    · exact canonical node old
    · cases List.mem_singleton.mp fresh
      exact groupCanonical
  unfold State.addGroup
  split
  · exact canonical
  · split
    · exact appended
    · split
      · split <;> exact canonical
      · rename_i node found
        exact appended.putGroupNode _ (canonical node (List.mem_of_find?_eq_some found))

/-- Group integration keeps a canonical parent on every old or newly
registered group, while mutable child links remain separate metadata. -/
theorem State.GroupParentsCanonical.addGroups
    {queue : State} {parents : Nat → NodeRefs}
    (canonical : queue.GroupParentsCanonical parents)
    (groups : List Group)
    (all : ∀ group ∈ groups, group.parent = (parents group.node.ref).head?)
    : (queue.addGroups groups).1.GroupParentsCanonical parents := by
  exact State.addGroups_preserves (fun current => current.GroupParentsCanonical parents) groups
    (fun _ group member valid => valid.addGroup group (all group member)) queue canonical

/-- Task registration changes memberships and counters, not a group's
primary-parent descriptor. -/
theorem State.GroupParentsCanonical.addTask
    {queue : State} {parents : Nat → NodeRefs}
    (canonical : queue.GroupParentsCanonical parents) (task : Task)
    : (queue.addTask task).GroupParentsCanonical parents := by
  let registered : State := { queue with tasks := queue.tasks ++ [task] }
  let step (current : State) (group : Execution.DeliveryNode) : State :=
    match current.groupNode? group.ref with
    | none => current
    | some node =>
        if node.tasks.contains task.occurrence then current
        else
          current.putGroupNode
            {
              node with
                tasks := node.tasks ++ [task.occurrence], pending := node.pending + 1
            }
  have stepCanonical (current : State) (group : Execution.DeliveryNode)
      (currentCanonical : current.GroupParentsCanonical parents)
      : (step current group).GroupParentsCanonical parents := by
    unfold step
    split
    · exact currentCanonical
    · rename_i node found
      split
      · exact currentCanonical
      · exact currentCanonical.putGroupNode _
          (currentCanonical node (List.mem_of_find?_eq_some found))
  have foldCanonical (more : List Execution.DeliveryNode) :
      ∀ current, current.GroupParentsCanonical parents
        → (more.foldl step current).GroupParentsCanonical parents := by
    induction more with
    | nil => intro current currentCanonical; exact currentCanonical
    | cons group rest ih =>
        intro current currentCanonical
        exact ih (step current group) (stepCanonical current group currentCanonical)
  let current := task.groups.foldl step registered
  have currentCanonical : current.GroupParentsCanonical parents :=
    foldCanonical task.groups registered canonical
  change (if task.groups.any (fun group => current.rootGroups.contains group.ref)
      && (current.taskNode? task.occurrence).isNone then
      { current with taskNodes := current.taskNodes ++ [{ task }] }
    else current).GroupParentsCanonical parents
  split <;> exact currentCanonical

/-- Stream registration does not modify the group-node map. -/
theorem State.GroupParentsCanonical.addStreams
    {queue : State} {parents : Nat → NodeRefs}
    (canonical : queue.GroupParentsCanonical parents)
    (streams : List Stream) (parentTask : Option Occurrence)
    : (queue.addStreams streams parentTask).1.GroupParentsCanonical parents := by
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
  have currentCanonical : current.GroupParentsCanonical parents := canonical
  cases parentTask with
  | none => exact currentCanonical
  | some occurrence =>
      simp only [State.addStreams]
      split <;> exact currentCanonical

/-- Child Work integration preserves the global parent assignment whenever
each newly supplied group is itself canonically parented. -/
theorem State.GroupParentsCanonical.maybeIntegrateWork
    {queue : State} {parents : Nat → NodeRefs}
    (canonical : queue.GroupParentsCanonical parents)
    (newWork : Work)
    (newCanonical
      : ∀ group ∈ newWork.groups, group.parent = (parents group.node.ref).head?)
    (parentTask : Option Occurrence := none)
    : (queue.maybeIntegrateWork newWork parentTask).1.GroupParentsCanonical parents := by
  let withGroups := (queue.addGroups newWork.groups).1
  let withTasks := newWork.tasks.foldl State.addTask withGroups
  have grouped : withGroups.GroupParentsCanonical parents :=
    canonical.addGroups newWork.groups newCanonical
  have taskFold (tasks : List Task) :
      ∀ current, current.GroupParentsCanonical parents
        → (tasks.foldl State.addTask current).GroupParentsCanonical parents := by
    induction tasks with
    | nil => intro current currentCanonical; exact currentCanonical
    | cons task rest ih =>
        intro current currentCanonical
        exact ih (current.addTask task) (currentCanonical.addTask task)
  have tasked : withTasks.GroupParentsCanonical parents :=
    taskFold newWork.tasks withGroups grouped
  change (withTasks.addStreams newWork.streams parentTask).1.GroupParentsCanonical
    parents
  exact tasked.addStreams newWork.streams parentTask

/-- Removing empty group shells keeps the parent descriptor of each survivor. -/
theorem State.GroupParentsCanonical.pruneEmptyGroups
    {queue : State} {parents : Nat → NodeRefs}
    (canonical : queue.GroupParentsCanonical parents)
    (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.GroupParentsCanonical parents := by
  have loop (fuel : Nat) (current : State)
      (remaining kept : List Execution.DeliveryNode)
      (currentCanonical : current.GroupParentsCanonical parents)
      : (State.pruneEmptyGroups.go fuel current remaining kept).1.GroupParentsCanonical
          parents := by
    induction fuel generalizing current remaining kept with
    | zero => exact currentCanonical
    | succ fuel ih =>
        cases remaining with
        | nil => exact currentCanonical
        | cons group rest =>
            unfold State.pruneEmptyGroups.go
            split
            · exact ih _ _ _ currentCanonical
            · split
              · apply ih
                intro node member
                exact currentCanonical node (List.mem_filter.mp member).1
              · exact ih _ _ _ currentCanonical
  exact loop _ queue groups [] canonical

/-- Cache exposure preserves all stored group metadata. -/
theorem State.GroupParentsCanonical.cacheTaskFailures {queue : State}
    {parents : Nat → NodeRefs} (canonical : queue.GroupParentsCanonical parents)
    (available : List (Occurrence × Nat))
    : (queue.cacheTaskFailures available).GroupParentsCanonical parents := by
  intro node member
  rw [State.cacheTaskFailures_groupNodes] at member
  exact canonical node member

/-- Startup preserves canonical metadata on each surviving group record. -/
theorem State.GroupParentsCanonical.startNewWork
    {queue : State} {parents : Nat → NodeRefs}
    (canonical : queue.GroupParentsCanonical parents) (newWork : NewWork)
    (available : List (Occurrence × Nat) := [])
    : (queue.startNewWork newWork available).1.GroupParentsCanonical parents := by
  intro node member
  exact canonical node ((queue.startNewWork_groupNodes_sublist newWork available).subset member)

/-- Removing a failed subtree retains only canonically parented group nodes. -/
theorem State.GroupParentsCanonical.removeGroup
    {queue : State} {parents : Nat → NodeRefs}
    (canonical : queue.GroupParentsCanonical parents) (ref : NodeRef)
    : (queue.removeGroup ref).GroupParentsCanonical parents := by
  intro node member
  unfold State.removeGroup at member
  exact canonical node (List.mem_filter.mp member).1

/-- Dropping a settled task changes group memberships, not group parents. -/
theorem State.GroupParentsCanonical.removeTask
    {queue : State} {parents : Nat → NodeRefs}
    (canonical : queue.GroupParentsCanonical parents) (occurrence : Occurrence)
    : (queue.removeTask occurrence).GroupParentsCanonical parents := by
  intro node member
  change node ∈ queue.groupNodes.map
    (fun old => { old with tasks := old.tasks.filter (· != occurrence) }) at member
  obtain ⟨old, oldMember, same⟩ := List.mem_map.mp member
  subst node
  exact canonical old oldMember

/-- The initial queue inherits canonical parents from all initially lowered
group descriptors. -/
theorem createWorkQueue_groupParentsCanonical
    (initialWork : Work) (parents : Nat → NodeRefs)
    (all : ∀ group ∈ initialWork.groups, group.parent = (parents group.node.ref).head?)
    : (State.initialize initialWork).GroupParentsCanonical parents := by
  let integrated := (({} : State).maybeIntegrateWork initialWork).1
  let newWork := (({} : State).maybeIntegrateWork initialWork).2
  let pruned := (integrated.pruneEmptyGroups newWork.newGroups).1
  let groups := (integrated.pruneEmptyGroups newWork.newGroups).2
  let roots := { newWork with newGroups := groups }
  let started := (pruned.startNewWork roots).1
  have emptyCanonical : ({} : State).GroupParentsCanonical parents := by
    intro node member
    cases member
  have integratedCanonical : integrated.GroupParentsCanonical parents :=
    emptyCanonical.maybeIntegrateWork initialWork all
  have prunedCanonical : pruned.GroupParentsCanonical parents :=
    integratedCanonical.pruneEmptyGroups newWork.newGroups
  have startedCanonical : started.GroupParentsCanonical parents :=
    prunedCanonical.startNewWork roots
  change State.GroupParentsCanonical
    { started with initialGroups := groups, initialStreams := roots.newStreams }
      parents
  exact startedCanonical

/-- Every execution-generated initial queue has a fixed, coherent primary
parent assignment inherited from the source Work tree. -/
private theorem ExecutedWork.initialQueueGroupParentsCanonical
    {work : Execution.Work} (generated : ExecutedWork work)
    : ∃ parents : Nat → NodeRefs,
        (State.initialize (Work.fromExecution work)).GroupParentsCanonical parents := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  refine ⟨parents, createWorkQueue_groupParentsCanonical
    (Work.fromExecution work) parents ?_⟩
  intro group member
  exact workFromSpec_groups_parentCanonical_root canonical member

/-- A successful group flush removes task nodes and group shells without
changing the parent assignment on survivors. -/
theorem State.GroupParentsCanonical.finishGroupSuccess
    {queue : State} {parents : Nat → NodeRefs}
    (canonical : queue.GroupParentsCanonical parents) (group : GroupNode)
    : (queue.finishGroupSuccess group).1.GroupParentsCanonical parents := by
  let step (acc : State × List ExecutionGroupValue × NodeRefs)
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
  have stepCanonical (acc : State × List ExecutionGroupValue × NodeRefs)
      (occurrence : Occurrence)
      (currentCanonical : acc.1.GroupParentsCanonical parents)
      : (step acc occurrence).1.GroupParentsCanonical parents := by
    obtain ⟨current, values, streams⟩ := acc
    dsimp only [step]
    split
    · exact currentCanonical
    · exact currentCanonical.removeTask occurrence
  have foldCanonical (tasks : List Occurrence) :
      ∀ acc : State × List ExecutionGroupValue × NodeRefs,
        acc.1.GroupParentsCanonical parents
          → (tasks.foldl step acc).1.GroupParentsCanonical parents := by
    induction tasks with
    | nil => intro acc currentCanonical; exact currentCanonical
    | cons occurrence rest ih =>
        intro acc currentCanonical
        exact ih (step acc occurrence)
          (stepCanonical acc occurrence currentCanonical)
  let flushed := (group.tasks.foldl step (queue, [], [])).1
  have flushedCanonical : flushed.GroupParentsCanonical parents :=
    foldCanonical group.tasks (queue, [], []) canonical
  let current : State :=
    { flushed with
        groupNodes := flushed.groupNodes.filter
          (fun node => node.group.node.ref != group.group.node.ref)
        rootGroups := flushed.rootGroups.filter (· != group.group.node.ref) }
  have currentCanonical : current.GroupParentsCanonical parents := by
    intro node member
    exact flushedCanonical node (List.mem_filter.mp member).1
  let children := group.childGroups.filterMap
    (fun ref => (current.groupNode? ref).map (fun node => node.group.node))
  change (current.pruneEmptyGroups children).1.GroupParentsCanonical parents
  exact currentCanonical.pruneEmptyGroups children

/-- Failure closure removes a subtree and retains canonical parents. -/
theorem State.GroupParentsCanonical.finishGroupFailure
    {queue : State} {parents : Nat → NodeRefs}
    (canonical : queue.GroupParentsCanonical parents)
    (group : GroupNode) (errors : Nat)
    : (queue.finishGroupFailure group errors).1.GroupParentsCanonical parents := by
  unfold State.finishGroupFailure
  exact canonical.removeGroup group.group.node.ref

/-- Retained task rejections leave surviving group-parent metadata unchanged. -/
theorem State.GroupParentsCanonical.taskFailure
    {queue : State} {parents : Nat → NodeRefs}
    (canonical : queue.GroupParentsCanonical parents)
    (occurrence : Occurrence) (errors : Nat)
    : (queue.taskFailure occurrence errors).1.GroupParentsCanonical parents := by
  cases found : queue.taskNode? occurrence with
  | none => simpa [State.taskFailure, found] using canonical
  | some node =>
      rw [queue.taskFailure_eq occurrence errors node found]
      exact failureGroupFold_preserves (fun state => state.GroupParentsCanonical parents)
        (fun _ ref prior => prior.removeGroup ref) _ _ _ canonical

/-- Recursive release preserves canonical group parents.
Witness: closure removes records, while child activation preserves the group-node map.
-/
theorem State.GroupParentsCanonical.drainReadyGroups {queue : State}
    {parents : Nat → NodeRefs} (canonical : queue.GroupParentsCanonical parents)
    (available : List (Occurrence × Nat) := [])
    : (queue.drainReadyGroups available).1.GroupParentsCanonical parents :=
  State.drainReadyGroups_preserves (fun state => state.GroupParentsCanonical parents)
    (fun _ node prior _ _ _ => (prior.finishGroupSuccess node).startNewWork _ available)
    canonical

/-- Successful task settlement preserves the source's primary-parent assignment.
Witness: matched child integration, the actual single-pass contributor fold, and recursive
release draining; an ignored success only removes its task and integrates no children.
-/
theorem State.GroupParentsCanonical.taskSuccess
    {queue : State} {parents : Nat → NodeRefs}
    (canonical : queue.GroupParentsCanonical parents)
    (occurrence : Occurrence) (result : TaskResult)
    (childrenCanonical
      : ∀ group ∈ result.work.groups, group.parent = (parents group.node.ref).head?)
    (available : List (Occurrence × Nat) := [])
    : (queue.taskSuccess occurrence result available).1.GroupParentsCanonical
        parents := by
  have step (acc : State × List WorkQueueEvent × NewWork) (group : Execution.DeliveryNode)
      (prior : acc.1.GroupParentsCanonical parents)
      : (successGroupStep acc group).1.GroupParentsCanonical parents := by
    obtain ⟨current, events, released⟩ := acc
    dsimp only [successGroupStep]
    split
    · exact prior
    · rename_i node found
      have updated := prior.putGroupNode { node with pending := node.pending - 1 }
        (prior node (List.mem_of_find?_eq_some found))
      split
      · exact updated.finishGroupSuccess _
      · exact updated
  have loop (groups : List Execution.DeliveryNode)
      (acc : State × List WorkQueueEvent × NewWork)
      (prior : acc.1.GroupParentsCanonical parents)
      : (groups.foldl successGroupStep acc).1.GroupParentsCanonical parents := by
    induction groups generalizing acc with
    | nil => exact prior
    | cons group rest ih => exact ih _ (step acc group prior)
  cases found : queue.taskNode? occurrence with
  | none => simpa [State.taskSuccess, found] using canonical
  | some node =>
      rw [queue.taskSuccess_eq occurrence result node found available]
      let stored := queue.putTaskNode { node with value := some result.value }
      have storedCanonical : stored.GroupParentsCanonical parents := canonical
      have integrated := storedCanonical.maybeIntegrateWork result.work childrenCanonical
        (some occurrence)
      exact ((loop node.task.groups (_, [], {}) integrated).startNewWork
        _ available).drainReadyGroups available

/-- Stream item integration preserves canonical parents for every supplied
item-work group, regardless of item batch width. -/
theorem State.GroupParentsCanonical.streamItems
    {queue : State} {parents : Nat → NodeRefs}
    (canonical : queue.GroupParentsCanonical parents)
    (stream : Execution.DeliveryNode) (items : List StreamItem)
    (childrenCanonical
      : ∀ item ∈ items,
        ∀ group ∈ item.work.groups, group.parent = (parents group.node.ref).head?)
    (available : List (Occurrence × Nat) := [])
    : (queue.streamItems stream items available).1.GroupParentsCanonical parents := by
  let step (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue × List GroupFailureEvent)
      (item : StreamItem) :=
    let (current, groups, streams, values, failures) := acc
    let (integrated, newWork) := current.maybeIntegrateWork item.work
    let (pruned, nonempty) := integrated.pruneEmptyGroups newWork.newGroups
    let (started, queued) := pruned.startNewWork { newWork with newGroups := nonempty } available
    (started, groups ++ nonempty, streams ++ newWork.newStreams,
      values ++ [item.value], failures ++ queued)
  have stepCanonical (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue × List GroupFailureEvent)
      (item : StreamItem) (currentCanonical : acc.1.GroupParentsCanonical parents)
      (itemMember : item ∈ items)
      : (step acc item).1.GroupParentsCanonical parents := by
    obtain ⟨current, groups, streams, values, failures⟩ := acc
    let integrated := current.maybeIntegrateWork item.work
    have integratedCanonical : integrated.1.GroupParentsCanonical parents :=
      currentCanonical.maybeIntegrateWork item.work
        (childrenCanonical item itemMember)
    let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
    have prunedCanonical : pruned.1.GroupParentsCanonical parents :=
      integratedCanonical.pruneEmptyGroups integrated.2.newGroups
    exact prunedCanonical.startNewWork
      { integrated.2 with newGroups := pruned.2 } available
  have foldCanonical (more : List StreamItem)
      (subset : ∀ item ∈ more, item ∈ items) :
      ∀ acc : State × List Execution.DeliveryNode
        × List Execution.DeliveryNode × List StreamItemValue × List GroupFailureEvent,
        acc.1.GroupParentsCanonical parents
          → (more.foldl step acc).1.GroupParentsCanonical parents := by
    induction more with
    | nil => intro acc currentCanonical; exact currentCanonical
    | cons item rest ih =>
        intro acc currentCanonical
        have itemMember : item ∈ items := subset item (by simp)
        have restSubset : ∀ next ∈ rest, next ∈ items := by
          intro next nextMember
          exact subset next (by simp [nextMember])
        exact ih restSubset (step acc item)
          (stepCanonical acc item currentCanonical itemMember)
  unfold State.streamItems
  split
  · exact canonical
  · exact (foldCanonical items (by intro item member; exact member)
      (queue, [], [], [], []) canonical).drainReadyGroups available

/-- Closing a stream changes no group-parent metadata. -/
theorem State.GroupParentsCanonical.streamSuccess
    {queue : State} {parents : Nat → NodeRefs}
    (canonical : queue.GroupParentsCanonical parents)
    (stream : Execution.DeliveryNode)
    : (queue.streamSuccess stream).1.GroupParentsCanonical parents := by
  unfold State.streamSuccess
  split <;> exact canonical

/-- Failing a stream likewise leaves group-parent metadata untouched. -/
theorem State.GroupParentsCanonical.streamFailure
    {queue : State} {parents : Nat → NodeRefs}
    (canonical : queue.GroupParentsCanonical parents)
    (stream : Execution.DeliveryNode) (errors : Nat)
    : (queue.streamFailure stream errors).1.GroupParentsCanonical parents := by
  unfold State.streamFailure
  split <;> exact canonical

/-- Matched graph events preserve the generated queue's canonical group
parents, including the groups revealed by successful tasks and stream items. -/
theorem State.GroupParentsCanonical.handleGraphEvent
    {queue : State} {work : Execution.Work} {parents : Nat → NodeRefs}
    (canonical : queue.GroupParentsCanonical parents)
    (event : GraphEvent) (matching : event.MatchesWork work)
    (workCanonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (available : List (Occurrence × Nat) := [])
    : (queue.handleGraphEvent event available).1.GroupParentsCanonical parents := by
  have cached := canonical.cacheTaskFailures available
  cases event with
  | taskSuccess occurrence result =>
      exact cached.taskSuccess occurrence result
        (fun group member =>
          matching.taskChildGroups_parentCanonical workCanonical member) available
  | taskFailure occurrence errors =>
      exact cached.taskFailure occurrence errors
  | groupFailure failure =>
      change ((queue.cacheTaskFailures available).groupFailure failure).1.GroupParentsCanonical parents
      unfold State.groupFailure
      split
      · exact cached
      · split <;> exact cached
  | streamItems stream items =>
      exact cached.streamItems stream items
        (fun item itemMember group groupMember =>
          matching.streamItem_childGroups_parentCanonical workCanonical
            itemMember groupMember) available
  | streamSuccess stream => exact cached.streamSuccess stream
  | streamFailure stream errors => exact cached.streamFailure stream errors

/-- A host batch preserves canonical group parents if every input event
matches the fixed generated work tree. -/
theorem State.GroupParentsCanonical.handleGraphEvents
    {queue : State} {work : Execution.Work} {parents : Nat → NodeRefs}
    (canonical : queue.GroupParentsCanonical parents)
    (batch : List GraphEvent)
    (allMatch : ∀ event ∈ batch, event.MatchesWork work)
    (workCanonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    : (queue.handleGraphEvents batch).1.GroupParentsCanonical parents := by
  let available := GraphEvent.availableFailures batch
  let step (acc : State × List WorkQueueEvent) (event : GraphEvent) :=
    let (next, produced) := acc.1.dispatchGraphEvent event available
    (next, acc.2 ++ produced)
  have foldCanonical (events : List GraphEvent)
      (subset : ∀ event ∈ events, event ∈ batch) :
      ∀ acc : State × List WorkQueueEvent,
        acc.1.GroupParentsCanonical parents
          → (events.foldl step acc).1.GroupParentsCanonical parents := by
    induction events with
    | nil => intro acc currentCanonical; exact currentCanonical
    | cons event rest ih =>
        intro acc currentCanonical
        have eventMatch : event.MatchesWork work := allMatch event (subset event (by simp))
        have restSubset : ∀ member ∈ rest, member ∈ batch := by
          intro member memberRest
          exact subset member (by simp [memberRest])
        obtain ⟨current, outputs⟩ := acc
        have nextCanonical : (step (current, outputs) event).1.GroupParentsCanonical
            parents := currentCanonical.handleGraphEvent event eventMatch workCanonical available
        exact ih restSubset (step (current, outputs) event) nextCanonical
  unfold State.handleGraphEvents
  split
  · exact canonical
  · let folded := batch.foldl step (queue, [])
    have final : folded.1.GroupParentsCanonical parents :=
      foldCanonical batch (fun _ member => member) (queue, []) canonical
    cases folded with
    | mk current outputs =>
        dsimp only at final ⊢
        split <;> exact final

/-- Replaying matched host batches preserves each live group's generated
primary parent, irrespective of publication order and batching. -/
theorem State.GroupParentsCanonical.runNormalized
    {queue : State} {work : Execution.Work} {parents : Nat → NodeRefs}
    (canonical : queue.GroupParentsCanonical parents)
    (batches : List (List GraphEvent))
    (allMatch : ∀ batch ∈ batches, ∀ event ∈ batch, event.MatchesWork work)
    (workCanonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    : (queue.runNormalized batches).1.GroupParentsCanonical parents := by
  have stepCanonical (acc : NormalizedAcc) (batch : List GraphEvent)
      (currentCanonical : acc.1.GroupParentsCanonical parents)
      (batchMatch : ∀ event ∈ batch, event.MatchesWork work)
      : (normalizedStep acc batch).1.GroupParentsCanonical parents := by
    obtain ⟨current, publisher, outputs⟩ := acc
    unfold normalizedStep
    cases outcome : current.handleGraphEvents batch with
    | mk next raw =>
        have nextCanonical : next.GroupParentsCanonical parents := by
          have handled := currentCanonical.handleGraphEvents batch batchMatch
            workCanonical
          rw [outcome] at handled
          exact handled
        dsimp only
        simp only [outcome]
        split <;> exact nextCanonical
  have foldCanonical (more : List (List GraphEvent))
      (subset : ∀ batch ∈ more, batch ∈ batches) :
      ∀ acc : NormalizedAcc,
        acc.1.GroupParentsCanonical parents
          → (more.foldl normalizedStep acc).1.GroupParentsCanonical parents := by
    induction more with
    | nil => intro acc currentCanonical; exact currentCanonical
    | cons batch rest ih =>
        intro acc currentCanonical
        have batchMatch : ∀ event ∈ batch, event.MatchesWork work :=
          allMatch batch (subset batch (by simp))
        have restSubset : ∀ later ∈ rest, later ∈ batches := by
          intro later member
          exact subset later (by simp [member])
        exact ih restSubset (normalizedStep acc batch)
          (stepCanonical acc batch currentCanonical batchMatch)
  let publisher : IncrementalPublisher :=
    { active := queue.initialGroups ++ queue.initialStreams }
  change (batches.foldl normalizedStep (queue, publisher, [])).1.GroupParentsCanonical
    parents
  exact foldCanonical batches (fun _ member => member)
    (queue, publisher, []) canonical

/-- Every matched generated-work replay retains canonical parents, including taskless groups.
Witness: the full-chain assignment from execution and preservation through all handlers.
-/
theorem ExecutedWork.runNormalized_groupParentsCanonical
    {work : Execution.Work} (generated : ExecutedWork work)
    (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work batches.flatten)
    : ∃ parents : Nat → NodeRefs,
        (((State.initialize (Work.fromExecution work)).runNormalized
            batches).1).GroupParentsCanonical
          parents := by
  obtain ⟨parents, workCanonical⟩ := generated.groupRecordsCanonical
  refine ⟨parents, ?_⟩
  have initial : (State.initialize (Work.fromExecution work)).GroupParentsCanonical
      parents :=
    createWorkQueue_groupParentsCanonical (Work.fromExecution work) parents
      (by
        intro group member
        exact workFromSpec_groups_parentCanonical_root workCanonical member)
  apply initial.runNormalized batches
  · intro batch batchMember event eventMember
    exact valid.eachMatches
      (List.mem_flatten.mpr ⟨batch, batchMember, eventMember⟩)
  · exact workCanonical

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
