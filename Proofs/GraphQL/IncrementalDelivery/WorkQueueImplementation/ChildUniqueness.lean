import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ChildLinks

/-! Duplicate-free child lists across every executable queue transition. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (
  ExecutionGroupValue StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Registration is the only operation that adds child links
-----------------------------------------------------------------------------------------

/-- Each live group's stored child-ref list has no duplicates, including stale refs.
This concrete invariant is preserved even by raw inputs with no generated-work premise.
-/
def State.ChildGroupsUnique (queue : State) : Prop :=
  ∀ node ∈ queue.groupNodes, node.childGroups.Nodup

/-- Replacing a group preserves child-list uniqueness when the replacement is unique.
Witness: split the map update into replaced and untouched records.
-/
theorem State.ChildGroupsUnique.putGroupNode
    {queue : State}
    (uniqueChildren : queue.ChildGroupsUnique)
    (updated : GroupNode)
    (updatedUniqueChildren : updated.childGroups.Nodup)
    : (queue.putGroupNode updated).ChildGroupsUnique := by
  intro node member
  change node ∈ queue.groupNodes.map
    (fun old => if old.group.node.ref == updated.group.node.ref then updated else old)
    at member
  obtain ⟨old, oldMember, same⟩ := List.mem_map.mp member
  split at same
  · subst node
    exact updatedUniqueChildren
  · subst node
    exact uniqueChildren old oldMember

/-- New group records start with an empty child list.
Witness: existing records are retained and the added list is trivially duplicate-free.
-/
theorem State.ChildGroupsUnique.addGroup
    {queue : State}
    (uniqueChildren : queue.ChildGroupsUnique)
    (group : Group)
    : (queue.addGroup group).ChildGroupsUnique := by
  have appended : ({ queue with
      groupNodes := queue.groupNodes ++ [({ group } : GroupNode)] } : State).ChildGroupsUnique := by
    intro node member
    rcases List.mem_append.mp member with old | added
    · exact uniqueChildren node old
    · cases List.mem_singleton.mp added
      exact List.nodup_nil
  unfold State.addGroup
  split
  · exact uniqueChildren
  · split
    · exact appended
    · split
      · split <;> exact uniqueChildren
      · rename_i node found
        apply appended.putGroupNode
        have prior := uniqueChildren node (List.mem_of_find?_eq_some found)
        split
        · exact prior
        · simp_all [List.nodup_append]
          intro child member same
          subst child
          contradiction

/-- Recursive parent linking adds a child ref only when it is absent. -/
theorem State.ChildGroupsUnique.addGroups
    {queue : State} (uniqueChildren : queue.ChildGroupsUnique) (groups : List Group)
    : (queue.addGroups groups).1.ChildGroupsUnique := by
  exact State.addGroups_preserves State.ChildGroupsUnique groups
    (fun _ group _ valid => valid.addGroup group) queue uniqueChildren

/-- Task registration preserves duplicate-free child lists.
Witness: its node updates change only task memberships and pending counts.
-/
theorem State.ChildGroupsUnique.addTask
    {queue : State}
    (uniqueChildren : queue.ChildGroupsUnique) (task : Task)
    : (queue.addTask task).ChildGroupsUnique := by
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
  have stepUniqueChildren (current : State) (group : Execution.DeliveryNode)
      (currentUniqueChildren : current.ChildGroupsUnique)
      : (step current group).ChildGroupsUnique := by
    unfold step
    split
    · exact currentUniqueChildren
    · rename_i node found
      split
      · exact currentUniqueChildren
      · exact currentUniqueChildren.putGroupNode _
          (currentUniqueChildren node (List.mem_of_find?_eq_some found))
  have foldUniqueChildren (more : List Execution.DeliveryNode) :
      ∀ current, current.ChildGroupsUnique
        → (more.foldl step current).ChildGroupsUnique := by
    induction more with
    | nil => intro current currentUniqueChildren; exact currentUniqueChildren
    | cons group rest ih =>
        intro current currentUniqueChildren
        exact ih (step current group) (stepUniqueChildren current group currentUniqueChildren)
  let current := task.groups.foldl step registered
  have currentUniqueChildren : current.ChildGroupsUnique :=
    foldUniqueChildren task.groups registered uniqueChildren
  change (if task.groups.any (fun group => current.rootGroups.contains group.ref)
      && (current.taskNode? task.occurrence).isNone then
      { current with taskNodes := current.taskNodes ++ [{ task }] }
    else current).ChildGroupsUnique
  split <;> exact currentUniqueChildren

/-- Stream registration preserves duplicate-free child lists.
Witness: neither stream records nor task-child-stream updates change group nodes.
-/
theorem State.ChildGroupsUnique.addStreams
    {queue : State}
    (uniqueChildren : queue.ChildGroupsUnique)
    (streams : List Stream) (parentTask : Option Occurrence)
    : (queue.addStreams streams parentTask).1.ChildGroupsUnique := by
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
  have currentUniqueChildren : current.ChildGroupsUnique := uniqueChildren
  cases parentTask with
  | none => exact currentUniqueChildren
  | some occurrence =>
      simp only [State.addStreams]
      split <;> exact currentUniqueChildren

/-- Integrating arbitrary child work preserves duplicate-free child lists.
Witness: compose group registration/linking, task registration, and stream registration.
-/
theorem State.ChildGroupsUnique.maybeIntegrateWork
    {queue : State}
    (uniqueChildren : queue.ChildGroupsUnique)
    (newWork : Work)
    (parentTask : Option Occurrence := none)
    : (queue.maybeIntegrateWork newWork parentTask).1.ChildGroupsUnique := by
  let withGroups := (queue.addGroups newWork.groups).1
  let withTasks := newWork.tasks.foldl State.addTask withGroups
  have grouped : withGroups.ChildGroupsUnique :=
    uniqueChildren.addGroups newWork.groups
  have taskFold (tasks : List Task) :
      ∀ current, current.ChildGroupsUnique
        → (tasks.foldl State.addTask current).ChildGroupsUnique := by
    induction tasks with
    | nil => intro current currentUniqueChildren; exact currentUniqueChildren
    | cons task rest ih =>
        intro current currentUniqueChildren
        exact ih (current.addTask task) (currentUniqueChildren.addTask task)
  have tasked : withTasks.ChildGroupsUnique :=
    taskFold newWork.tasks withGroups grouped
  change (withTasks.addStreams newWork.streams parentTask).1.ChildGroupsUnique
  exact tasked.addStreams newWork.streams parentTask

-----------------------------------------------------------------------------------------
-- Pruning, activation, and removal preserve existing child lists
-----------------------------------------------------------------------------------------

/-- Pruning empty shells preserves duplicate-free lists on surviving group records.
Witness: induction on the pruning loop; removed shells only restrict the node list.
-/
theorem State.ChildGroupsUnique.pruneEmptyGroups
    {queue : State}
    (uniqueChildren : queue.ChildGroupsUnique)
    (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.ChildGroupsUnique := by
  have loop (fuel : Nat) (current : State)
      (remaining kept : List Execution.DeliveryNode)
      (currentUniqueChildren : current.ChildGroupsUnique)
      : (State.pruneEmptyGroups.go fuel current remaining kept).1.ChildGroupsUnique := by
    induction fuel generalizing current remaining kept with
    | zero => exact currentUniqueChildren
    | succ fuel ih =>
        cases remaining with
        | nil => exact currentUniqueChildren
        | cons group rest =>
            unfold State.pruneEmptyGroups.go
            split
            · exact ih _ _ _ currentUniqueChildren
            · split
              · apply ih
                intro node member
                exact currentUniqueChildren node (List.mem_filter.mp member).1
              · exact ih _ _ _ currentUniqueChildren
  exact loop _ queue groups [] uniqueChildren

/-- Cache exposure leaves every child list unchanged. -/
theorem State.ChildGroupsUnique.cacheTaskFailures {queue : State}
    (unique : queue.ChildGroupsUnique) (available : List (Occurrence × Nat))
    : (queue.cacheTaskFailures available).ChildGroupsUnique := by
  intro node member
  rw [State.cacheTaskFailures_groupNodes] at member
  exact unique node member

/-- Activation retains a sublist of unchanged group records. -/
theorem State.ChildGroupsUnique.startNewWork {queue : State}
    (unique : queue.ChildGroupsUnique) (newWork : NewWork)
    (available : List (Occurrence × Nat) := [])
    : (queue.startNewWork newWork available).1.ChildGroupsUnique := by
  intro node member
  exact unique node ((queue.startNewWork_groupNodes_sublist newWork available).subset member)

/-- Removing a failed subtree preserves duplicate-free child lists on survivors.
Witness: the handler filters group records without altering their child lists.
-/
theorem State.ChildGroupsUnique.removeGroup
    {queue : State}
    (uniqueChildren : queue.ChildGroupsUnique) (ref : NodeRef)
    : (queue.removeGroup ref).ChildGroupsUnique := by
  intro node member
  unfold State.removeGroup at member
  exact uniqueChildren node (List.mem_filter.mp member).1

/-- Dropping a task preserves duplicate-free child lists.
Witness: only the task-membership field of each group record changes.
-/
theorem State.ChildGroupsUnique.removeTask
    {queue : State}
    (uniqueChildren : queue.ChildGroupsUnique) (occurrence : Occurrence)
    : (queue.removeTask occurrence).ChildGroupsUnique := by
  intro node member
  change node ∈ queue.groupNodes.map
    (fun old => { old with tasks := old.tasks.filter (· != occurrence) }) at member
  obtain ⟨old, oldMember, same⟩ := List.mem_map.mp member
  subst node
  exact uniqueChildren old oldMember

/-- Every initialized queue has duplicate-free child lists, even for raw Work.
Witness: integration, pruning, and activation preserve the empty initial invariant.
-/
theorem createWorkQueue_childGroupsUnique (initialWork : Work)
    : (State.initialize initialWork).ChildGroupsUnique := by
  let integrated := (({} : State).maybeIntegrateWork initialWork).1
  let newWork := (({} : State).maybeIntegrateWork initialWork).2
  let pruned := (integrated.pruneEmptyGroups newWork.newGroups).1
  let groups := (integrated.pruneEmptyGroups newWork.newGroups).2
  let roots := { newWork with newGroups := groups }
  let started := (pruned.startNewWork roots).1
  have emptyUniqueChildren : ({} : State).ChildGroupsUnique := by
    intro node member
    cases member
  have integratedUniqueChildren : integrated.ChildGroupsUnique :=
    emptyUniqueChildren.maybeIntegrateWork initialWork
  have prunedUniqueChildren : pruned.ChildGroupsUnique :=
    integratedUniqueChildren.pruneEmptyGroups newWork.newGroups
  have startedUniqueChildren : started.ChildGroupsUnique :=
    prunedUniqueChildren.startNewWork roots
  change State.ChildGroupsUnique
    { started with initialGroups := groups, initialStreams := roots.newStreams }
  exact startedUniqueChildren

-----------------------------------------------------------------------------------------
-- Success and failure handlers compose the primitive preservation results
-----------------------------------------------------------------------------------------

/-- A group flush preserves duplicate-free child lists on surviving nodes.
Witness: task removal, group filtering, and child pruning each retain the invariant.
-/
theorem State.ChildGroupsUnique.finishGroupSuccess
    {queue : State}
    (uniqueChildren : queue.ChildGroupsUnique) (group : GroupNode)
    : (queue.finishGroupSuccess group).1.ChildGroupsUnique := by
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
  have stepUniqueChildren (acc : State × List ExecutionGroupValue × NodeRefs)
      (occurrence : Occurrence)
      (currentUniqueChildren : acc.1.ChildGroupsUnique)
      : (step acc occurrence).1.ChildGroupsUnique := by
    obtain ⟨current, values, streams⟩ := acc
    dsimp only [step]
    split
    · exact currentUniqueChildren
    · exact currentUniqueChildren.removeTask occurrence
  have foldUniqueChildren (tasks : List Occurrence) :
      ∀ acc : State × List ExecutionGroupValue × NodeRefs,
        acc.1.ChildGroupsUnique
          → (tasks.foldl step acc).1.ChildGroupsUnique := by
    induction tasks with
    | nil => intro acc currentUniqueChildren; exact currentUniqueChildren
    | cons occurrence rest ih =>
        intro acc currentUniqueChildren
        exact ih (step acc occurrence)
          (stepUniqueChildren acc occurrence currentUniqueChildren)
  let flushed := (group.tasks.foldl step (queue, [], [])).1
  have flushedUniqueChildren : flushed.ChildGroupsUnique :=
    foldUniqueChildren group.tasks (queue, [], []) uniqueChildren
  let current : State :=
    { flushed with
        groupNodes := flushed.groupNodes.filter
          (fun node => node.group.node.ref != group.group.node.ref)
        rootGroups := flushed.rootGroups.filter (· != group.group.node.ref) }
  have currentUniqueChildren : current.ChildGroupsUnique := by
    intro node member
    exact flushedUniqueChildren node (List.mem_filter.mp member).1
  let children := group.childGroups.filterMap
    (fun ref => (current.groupNode? ref).map (fun node => node.group.node))
  change (current.pruneEmptyGroups children).1.ChildGroupsUnique
  exact currentUniqueChildren.pruneEmptyGroups children

/-- Failure closure preserves duplicate-free child lists.
Witness: the group-removal preservation theorem.
-/
theorem State.ChildGroupsUnique.finishGroupFailure
    {queue : State}
    (uniqueChildren : queue.ChildGroupsUnique)
    (group : GroupNode) (errors : Nat)
    : (queue.finishGroupFailure group errors).1.ChildGroupsUnique := by
  unfold State.finishGroupFailure
  exact uniqueChildren.removeGroup group.group.node.ref

/-- Rejection replay removes groups without changing surviving child lists. -/
theorem State.ChildGroupsUnique.taskFailure
    {queue : State} (uniqueChildren : queue.ChildGroupsUnique)
    (occurrence : Occurrence) (errors : Nat)
    : (queue.taskFailure occurrence errors).1.ChildGroupsUnique := by
  cases found : queue.taskNode? occurrence with
  | none => simpa only [State.taskFailure, found] using uniqueChildren
  | some node =>
      rw [queue.taskFailure_eq occurrence errors node found]
      exact failureGroupFold_preserves State.ChildGroupsUnique
        (fun _ ref prior => prior.removeGroup ref) _ _ _ uniqueChildren

/-- Recursive draining preserves duplicate-free child lists, including stale links.
Witness: every success/failure closure and subsequent activation preserves uniqueness.
-/
theorem State.ChildGroupsUnique.drainReadyGroups {queue : State}
    (unique : queue.ChildGroupsUnique) (available : List (Occurrence × Nat) := [])
    : (queue.drainReadyGroups available).1.ChildGroupsUnique :=
  State.drainReadyGroups_preserves State.ChildGroupsUnique
    (fun _ node prior _ _ _ => (prior.finishGroupSuccess node).startNewWork _ available)
    unique

/-- Single-pass task success preserves duplicate-free child lists.
Witness: ignored settlement cleans up only its task; active settlement composes child
integration, the actual contributor fold, activation, and the recursive release drain.
No generated-work or source-validity premise is required.
-/
theorem State.ChildGroupsUnique.taskSuccess
    {queue : State}
    (uniqueChildren : queue.ChildGroupsUnique)
    (occurrence : Occurrence) (result : TaskResult)
    (available : List (Occurrence × Nat) := [])
    : (queue.taskSuccess occurrence result available).1.ChildGroupsUnique := by
  have loop (groups : List Execution.DeliveryNode)
      (acc : State × List WorkQueueEvent × NewWork) (prior : acc.1.ChildGroupsUnique)
      : (groups.foldl successGroupStep acc).1.ChildGroupsUnique := by
    induction groups generalizing acc with
    | nil => exact prior
    | cons group rest ih =>
        apply ih
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
  cases found : queue.taskNode? occurrence with
  | none => simpa only [State.taskSuccess, found] using uniqueChildren
  | some node =>
      rw [queue.taskSuccess_eq occurrence result node found available]
      have installed : State.ChildGroupsUnique
          (queue.putTaskNode { node with value := some result.value }) := uniqueChildren
      have integrated := installed.maybeIntegrateWork result.work (some occurrence)
      exact ((loop node.task.groups (_, [], {}) integrated).startNewWork
        _ available).drainReadyGroups available

/-- Stream-item batches preserve duplicate-free child lists.
Witness: each item's integration, pruning, and activation retain the invariant.
-/
theorem State.ChildGroupsUnique.streamItems
    {queue : State}
    (uniqueChildren : queue.ChildGroupsUnique)
    (stream : Execution.DeliveryNode) (items : List StreamItem)
    (available : List (Occurrence × Nat) := [])
    : (queue.streamItems stream items available).1.ChildGroupsUnique := by
  let step (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue × List GroupFailureEvent)
      (item : StreamItem) :=
    let (current, groups, streams, values, failures) := acc
    let (integrated, newWork) := current.maybeIntegrateWork item.work
    let (pruned, nonempty) := integrated.pruneEmptyGroups newWork.newGroups
    let (started, queued) := pruned.startNewWork { newWork with newGroups := nonempty } available
    (started, groups ++ nonempty, streams ++ newWork.newStreams,
      values ++ [item.value], failures ++ queued)
  have stepUniqueChildren (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue × List GroupFailureEvent)
      (item : StreamItem) (currentUniqueChildren : acc.1.ChildGroupsUnique)
      : (step acc item).1.ChildGroupsUnique := by
    obtain ⟨current, groups, streams, values, failures⟩ := acc
    let integrated := current.maybeIntegrateWork item.work
    have integratedUniqueChildren : integrated.1.ChildGroupsUnique :=
      currentUniqueChildren.maybeIntegrateWork item.work
    let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
    have prunedUniqueChildren : pruned.1.ChildGroupsUnique :=
      integratedUniqueChildren.pruneEmptyGroups integrated.2.newGroups
    exact prunedUniqueChildren.startNewWork
      { integrated.2 with newGroups := pruned.2 } available
  have foldUniqueChildren (more : List StreamItem)
      (subset : ∀ item ∈ more, item ∈ items) :
      ∀ acc : State × List Execution.DeliveryNode
        × List Execution.DeliveryNode × List StreamItemValue × List GroupFailureEvent,
        acc.1.ChildGroupsUnique
          → (more.foldl step acc).1.ChildGroupsUnique := by
    induction more with
    | nil => intro acc currentUniqueChildren; exact currentUniqueChildren
    | cons item rest ih =>
        intro acc currentUniqueChildren
        have restSubset : ∀ next ∈ rest, next ∈ items := by
          intro next nextMember
          exact subset next (by simp [nextMember])
        exact ih restSubset (step acc item)
          (stepUniqueChildren acc item currentUniqueChildren)
  unfold State.streamItems
  split
  · exact uniqueChildren
  · exact (foldUniqueChildren items (by intro item member; exact member)
      (queue, [], [], [], []) uniqueChildren).drainReadyGroups available

/-- Stream exhaustion preserves duplicate-free group child lists.
Witness: stream closure does not modify group records.
-/
theorem State.ChildGroupsUnique.streamSuccess
    {queue : State}
    (uniqueChildren : queue.ChildGroupsUnique)
    (stream : Execution.DeliveryNode)
    : (queue.streamSuccess stream).1.ChildGroupsUnique := by
  unfold State.streamSuccess
  split <;> exact uniqueChildren

/-- Stream failure preserves duplicate-free group child lists.
Witness: stream closure does not modify group records.
-/
theorem State.ChildGroupsUnique.streamFailure
    {queue : State}
    (uniqueChildren : queue.ChildGroupsUnique)
    (stream : Execution.DeliveryNode) (errors : Nat)
    : (queue.streamFailure stream errors).1.ChildGroupsUnique := by
  unfold State.streamFailure
  split <;> exact uniqueChildren

-----------------------------------------------------------------------------------------
-- The invariant holds for arbitrary event streams and response normalization
-----------------------------------------------------------------------------------------

/-- Each raw graph event preserves duplicate-free child lists.
Witness: the corresponding handler theorem; no host-event semantic premise is needed.
-/
theorem State.ChildGroupsUnique.handleGraphEvent {queue : State}
    (unique : queue.ChildGroupsUnique) (event : GraphEvent)
    (available : List (Occurrence × Nat) := [])
    : (queue.handleGraphEvent event available).1.ChildGroupsUnique := by
  have cached := unique.cacheTaskFailures available
  cases event with
  | taskSuccess occurrence result => exact cached.taskSuccess occurrence result available
  | taskFailure occurrence errors => exact cached.taskFailure occurrence errors
  | streamItems stream items => exact cached.streamItems stream items available
  | streamSuccess stream => exact cached.streamSuccess stream
  | streamFailure stream errors => exact cached.streamFailure stream errors
  | groupFailure failure =>
      change ((queue.cacheTaskFailures available).groupFailure failure).1.ChildGroupsUnique
      unfold State.groupFailure
      split
      · exact cached
      · split <;> exact cached

/-- Enqueuing startup effects leaves child-list uniqueness unchanged. -/
theorem State.ChildGroupsUnique.dispatchGraphEvent {queue : State}
    (unique : queue.ChildGroupsUnique) (event : GraphEvent)
    (available : List (Occurrence × Nat) := [])
    : (queue.dispatchGraphEvent event available).1.ChildGroupsUnique := by
  exact unique.handleGraphEvent event available

/-- FIFO handlers preserve child-list uniqueness under their common cache snapshot. -/
theorem State.ChildGroupsUnique.replayGraphEvents {queue : State}
    (unique : queue.ChildGroupsUnique) (events : List GraphEvent)
    (available : List (Occurrence × Nat) := [])
    : (queue.replayGraphEvents events available).ChildGroupsUnique := by
  induction events generalizing queue with
  | nil => exact unique
  | cons event rest ih => exact ih (unique.dispatchGraphEvent event available)

/-- A raw host batch preserves child-list uniqueness.
Witness: handler induction, including termination-flag updates and absorbed batches.
-/
theorem State.ChildGroupsUnique.handleGraphEvents {queue : State}
    (unique : queue.ChildGroupsUnique) (batch : List GraphEvent)
    : (queue.handleGraphEvents batch).1.ChildGroupsUnique := by
  cases running : queue.terminated with
  | true => simpa only [State.handleGraphEvents, running, ↓reduceIte] using unique
  | false =>
      obtain ⟨terminal, same⟩ := queue.handleGraphEvents_stateCore batch running
      rw [same]
      exact unique.replayGraphEvents batch (GraphEvent.availableFailures batch)

/-- Normalized replay preserves duplicate-free child lists for arbitrary input batches.
Witness: each batch updates the queue independently of publisher normalization.
-/
theorem State.ChildGroupsUnique.runNormalized {queue : State}
    (unique : queue.ChildGroupsUnique) (batches : List (List GraphEvent))
    : (queue.runNormalized batches).1.ChildGroupsUnique := by
  have step (acc : NormalizedAcc) (batch : List GraphEvent)
      (current : acc.1.ChildGroupsUnique)
      : (normalizedStep acc batch).1.ChildGroupsUnique := by
    obtain ⟨queue, publisher, outputs⟩ := acc
    unfold normalizedStep
    cases outcome : queue.handleGraphEvents batch with
    | mk next raw =>
        have nextUnique : next.ChildGroupsUnique := by
          have handled := current.handleGraphEvents batch
          rw [outcome] at handled
          exact handled
        dsimp only
        simp only [outcome]
        split <;> exact nextUnique
  have fold (more : List (List GraphEvent)) :
      ∀ acc : NormalizedAcc, acc.1.ChildGroupsUnique
        → (more.foldl normalizedStep acc).1.ChildGroupsUnique := by
    induction more with
    | nil => intro acc current; exact current
    | cons batch rest ih =>
        intro acc current
        exact ih (normalizedStep acc batch) (step acc batch current)
  exact fold batches _ unique

/-- Every initialized reference queue retains duplicate-free child links under replay.
Witness: empty child lists at registration and guarded append during parent linking.
-/
theorem createWorkQueue_runNormalized_childGroupsUnique
    (work : Work) (batches : List (List GraphEvent))
    : ((State.initialize work).runNormalized batches).1.ChildGroupsUnique :=
  (createWorkQueue_childGroupsUnique work).runNormalized batches

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
