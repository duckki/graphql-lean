import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupMetadata

/-! Structural provenance of group nodes across queue transitions. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (
  ExecutionGroupValue StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Replacing mutable group metadata preserves work provenance when the
replacement's delivery node is known. -/
theorem State.GroupNodesMatchWork.putGroupNode
    {queue : State} {work : Execution.Work}
    (matching : queue.GroupNodesMatchWork work) (updated : GroupNode)
    (updatedMatch : ∃ dependencies, GroupRecordAt work updated.group.node dependencies)
    : (queue.putGroupNode updated).GroupNodesMatchWork work := by
  intro node member
  change node ∈ queue.groupNodes.map
    (fun old => if old.group.node.key == updated.group.node.key then updated else old)
    at member
  obtain ⟨old, oldMember, same⟩ := List.mem_map.mp member
  split at same
  · subst node
    exact updatedMatch
  · subst node
    exact matching old oldMember

/-- Registering a fixed-work group extends the provenance invariant. -/
theorem State.GroupNodesMatchWork.addGroup
    {queue : State} {work : Execution.Work}
    (matching : queue.GroupNodesMatchWork work) (group : Group)
    (known : ∃ dependencies, GroupRecordAt work group.node dependencies)
    : (queue.addGroup group).GroupNodesMatchWork work := by
  unfold State.addGroup
  split
  · exact matching
  · split
    · exact matching
    · intro node member
      rcases List.mem_append.mp member with old | added
      · exact matching node old
      · have same : node = { group } := List.mem_singleton.mp added
        subst node
        exact known

/-- The link-installation pass modifies only child lists, so exact group-node
provenance remains valid after integrating a list of fixed-work groups. -/
theorem State.GroupNodesMatchWork.addGroups
    {queue : State} {work : Execution.Work}
    (matching : queue.GroupNodesMatchWork work) (groups : List Group)
    (all : ∀ group ∈ groups, ∃ dependencies, GroupRecordAt work group.node dependencies)
    : (queue.addGroups groups).1.GroupNodesMatchWork work := by
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
              else node.childGroups ++ [group.node.key]
            current.putGroupNode { node with childGroups := children }
  have registerFold (more : List Group)
      (subset : ∀ group ∈ more, group ∈ groups) :
      ∀ current, current.GroupNodesMatchWork work
        → (more.foldl State.addGroup current).GroupNodesMatchWork work := by
    induction more with
    | nil => intro current currentMatch; exact currentMatch
    | cons group rest ih =>
        intro current currentMatch
        have restSubset : ∀ next ∈ rest, next ∈ groups := by
          intro next member
          exact subset next (by simp [member])
        exact ih restSubset (current.addGroup group)
          (currentMatch.addGroup group (all group (subset group (by simp))))
  have linkFold (more : List Group) :
      ∀ current, current.GroupNodesMatchWork work
        → (more.foldl linkStep current).GroupNodesMatchWork work := by
    induction more with
    | nil => intro current currentMatch; exact currentMatch
    | cons group rest ih =>
        intro current currentMatch
        apply ih (linkStep current group)
        unfold linkStep
        split
        · exact currentMatch
        · split
          · exact currentMatch
          · rename_i node found
            exact currentMatch.putGroupNode _
              (currentMatch node (List.mem_of_find?_eq_some found))
  let fresh := groups.filter (fun group =>
    !queue.registeredGroups.contains group.node.key
      && (queue.groupNode? group.node.key).isNone)
  change (fresh.foldl linkStep
    (fresh.foldl State.addGroup queue)).GroupNodesMatchWork work
  exact linkFold fresh _
    (registerFold fresh (fun _ member => (List.mem_filter.mp member).1) queue matching)

/-- Task registration updates no group's delivery-node provenance. -/
theorem State.GroupNodesMatchWork.addTask
    {queue : State} {work : Execution.Work}
    (matching : queue.GroupNodesMatchWork work) (task : Task)
    : (queue.addTask task).GroupNodesMatchWork work := by
  let registered : State := { queue with tasks := queue.tasks ++ [task] }
  let step (current : State) (group : Execution.DeliveryNode) : State :=
    match current.groupNode? group.key with
    | none => current
    | some node =>
        if node.tasks.contains task.occurrence then current
        else current.putGroupNode
          { node with tasks := node.tasks ++ [task.occurrence], pending := node.pending + 1 }
  have stepMatch (current : State) (group : Execution.DeliveryNode)
      (currentMatch : current.GroupNodesMatchWork work)
      : (step current group).GroupNodesMatchWork work := by
    unfold step
    split
    · exact currentMatch
    · rename_i node found
      split
      · exact currentMatch
      · exact currentMatch.putGroupNode _
          (currentMatch node (List.mem_of_find?_eq_some found))
  have foldMatch (more : List Execution.DeliveryNode) :
      ∀ current, current.GroupNodesMatchWork work
        → (more.foldl step current).GroupNodesMatchWork work := by
    induction more with
    | nil => intro current currentMatch; exact currentMatch
    | cons group rest ih =>
        intro current currentMatch
        exact ih (step current group) (stepMatch current group currentMatch)
  let current := task.groups.foldl step registered
  have currentMatch : current.GroupNodesMatchWork work :=
    foldMatch task.groups registered matching
  change (if task.groups.any (fun group => current.rootGroups.contains group.key)
      && (current.taskNode? task.occurrence).isNone then
    { current with taskNodes := current.taskNodes ++ [{ task }] }
    else current).GroupNodesMatchWork work
  split <;> exact currentMatch

/-- Stream registration changes no group nodes. -/
theorem State.GroupNodesMatchWork.addStreams
    {queue : State} {work : Execution.Work}
    (matching : queue.GroupNodesMatchWork work)
    (streams : List Stream) (parentTask : Option Occurrence)
    : (queue.addStreams streams parentTask).1.GroupNodesMatchWork work := by
  unfold State.addStreams
  split
  · exact matching
  · dsimp
    split <;> exact matching

/-- Integrating matched Work preserves provenance for every old and newly
registered group node. -/
theorem State.GroupNodesMatchWork.maybeIntegrateWork
    {queue : State} {specWork : Execution.Work}
    (matching : queue.GroupNodesMatchWork specWork) (newWork : Work)
    (all
      : ∀ group ∈ newWork.groups,
          ∃ dependencies, GroupRecordAt specWork group.node dependencies)
    (parentTask : Option Occurrence := none)
    : (queue.maybeIntegrateWork newWork parentTask).1.GroupNodesMatchWork specWork := by
  let withGroups := (queue.addGroups newWork.groups).1
  let withTasks := newWork.tasks.foldl State.addTask withGroups
  have groupMatch : withGroups.GroupNodesMatchWork specWork :=
    matching.addGroups newWork.groups all
  have taskFold (more : List Task) :
      ∀ current, current.GroupNodesMatchWork specWork
        → (more.foldl State.addTask current).GroupNodesMatchWork specWork := by
    induction more with
    | nil => intro current currentMatch; exact currentMatch
    | cons task rest ih =>
        intro current currentMatch
        exact ih (current.addTask task) (currentMatch.addTask task)
  have taskMatch : withTasks.GroupNodesMatchWork specWork :=
    taskFold newWork.tasks withGroups groupMatch
  change (withTasks.addStreams newWork.streams parentTask).1.GroupNodesMatchWork
    specWork
  exact taskMatch.addStreams newWork.streams parentTask

/-- Pruning and activation retain the provenance of surviving group nodes. -/
theorem State.GroupNodesMatchWork.pruneEmptyGroups
    {queue : State} {work : Execution.Work}
    (matching : queue.GroupNodesMatchWork work)
    (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.GroupNodesMatchWork work := by
  have loop (fuel : Nat) (current : State)
      (remaining kept : List Execution.DeliveryNode)
      (currentMatch : current.GroupNodesMatchWork work)
      : (State.pruneEmptyGroups.go fuel current remaining kept).1.GroupNodesMatchWork
          work := by
    induction fuel generalizing current remaining kept with
    | zero => exact currentMatch
    | succ fuel ih =>
        cases remaining with
        | nil => exact currentMatch
        | cons group rest =>
            unfold State.pruneEmptyGroups.go
            split
            · exact ih _ _ _ currentMatch
            · split
              · apply ih
                intro node member
                exact currentMatch node (List.mem_filter.mp member).1
              · exact ih _ _ _ currentMatch
  exact loop _ queue groups [] matching

theorem State.GroupNodesMatchWork.startNewWork
    {queue : State} {work : Execution.Work}
    (matching : queue.GroupNodesMatchWork work) (newWork : NewWork)
    : (queue.startNewWork newWork).GroupNodesMatchWork work := by
  intro node member
  have same := (queue.startNewWork_groupCore newWork).1
  rw [same] at member
  exact matching node member

/-- Removing a subtree or a settled task cannot fabricate a group node. -/
theorem State.GroupNodesMatchWork.removeGroup
    {queue : State} {work : Execution.Work}
    (matching : queue.GroupNodesMatchWork work) (key : Nat)
    : (queue.removeGroup key).GroupNodesMatchWork work := by
  intro node member
  unfold State.removeGroup at member
  exact matching node (List.mem_filter.mp member).1

theorem State.GroupNodesMatchWork.removeTask
    {queue : State} {work : Execution.Work}
    (matching : queue.GroupNodesMatchWork work) (occurrence : Occurrence)
    : (queue.removeTask occurrence).GroupNodesMatchWork work := by
  intro node member
  change node ∈ queue.groupNodes.map
    (fun old => { old with tasks := old.tasks.filter (· != occurrence) }) at member
  obtain ⟨old, oldMember, same⟩ := List.mem_map.mp member
  subst node
  exact matching old oldMember

/-- The initialized queue registers only groups in the input spec Work. -/
theorem createWorkQueue_groupNodesMatchWork (work : Execution.Work)
    : (State.initialize (Work.fromExecution work)).GroupNodesMatchWork work := by
  let initialWork := Work.fromExecution work
  let integrated := (({} : State).maybeIntegrateWork initialWork).1
  let newWork := (({} : State).maybeIntegrateWork initialWork).2
  let pruned := (integrated.pruneEmptyGroups newWork.newGroups).1
  let groups := (integrated.pruneEmptyGroups newWork.newGroups).2
  let roots := { newWork with newGroups := groups }
  let started := pruned.startNewWork roots
  have emptyMatch : ({} : State).GroupNodesMatchWork work := by
    intro node member
    cases member
  have integratedMatch : integrated.GroupNodesMatchWork work :=
    emptyMatch.maybeIntegrateWork initialWork
      (by
        intro group member
        obtain ⟨dependencies, known, _⟩ :=
          workFromSpec_groups_recordAt (Located.root (root := work)) member
        exact ⟨dependencies, known⟩)
  have prunedMatch : pruned.GroupNodesMatchWork work :=
    integratedMatch.pruneEmptyGroups newWork.newGroups
  have startedMatch : started.GroupNodesMatchWork work :=
    prunedMatch.startNewWork roots
  change State.GroupNodesMatchWork
    { started with initialGroups := groups, initialStreams := roots.newStreams }
      work
  exact startedMatch

/-- Group success flushes memberships and removes nodes; it retains source
provenance on every survivor. -/
theorem State.GroupNodesMatchWork.finishGroupSuccess
    {queue : State} {work : Execution.Work}
    (matching : queue.GroupNodesMatchWork work) (group : GroupNode)
    : (queue.finishGroupSuccess group).1.GroupNodesMatchWork work := by
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
  have stepMatch (acc : State × List ExecutionGroupValue × Keys)
      (occurrence : Occurrence)
      (currentMatch : acc.1.GroupNodesMatchWork work)
      : (step acc occurrence).1.GroupNodesMatchWork work := by
    obtain ⟨current, values, streams⟩ := acc
    dsimp only [step]
    split
    · exact currentMatch
    · exact currentMatch.removeTask occurrence
  have foldMatch (tasks : List Occurrence) :
      ∀ acc : State × List ExecutionGroupValue × Keys,
        acc.1.GroupNodesMatchWork work
          → (tasks.foldl step acc).1.GroupNodesMatchWork work := by
    induction tasks with
    | nil => intro acc currentMatch; exact currentMatch
    | cons occurrence rest ih =>
        intro acc currentMatch
        exact ih (step acc occurrence) (stepMatch acc occurrence currentMatch)
  let flushed := (group.tasks.foldl step (queue, [], [])).1
  have flushedMatch : flushed.GroupNodesMatchWork work :=
    foldMatch group.tasks (queue, [], []) matching
  let current : State :=
    { flushed with
        groupNodes := flushed.groupNodes.filter
          (fun node => node.group.node.key != group.group.node.key)
        rootGroups := flushed.rootGroups.filter (· != group.group.node.key) }
  have currentMatch : current.GroupNodesMatchWork work := by
    intro node member
    exact flushedMatch node (List.mem_filter.mp member).1
  let children := group.childGroups.filterMap
    (fun key => (current.groupNode? key).map (fun node => node.group.node))
  change (current.pruneEmptyGroups children).1.GroupNodesMatchWork work
  exact currentMatch.pruneEmptyGroups children

/-- Failed group closure removes a group, preserving provenance elsewhere. -/
theorem State.GroupNodesMatchWork.finishGroupFailure
    {queue : State} {work : Execution.Work}
    (matching : queue.GroupNodesMatchWork work)
    (group : GroupNode) (errors : Nat)
    : (queue.finishGroupFailure group errors).1.GroupNodesMatchWork work := by
  unfold State.finishGroupFailure
  exact matching.removeGroup group.group.node.key

/-- Recursive release retains every surviving group's fixed-work provenance.
Witness: the drain induction composes success, activation, and failure preservation.
-/
theorem State.GroupNodesMatchWork.drainReadyGroups
    {queue : State} {work : Execution.Work} (matching : queue.GroupNodesMatchWork work)
    : queue.drainReadyGroups.1.GroupNodesMatchWork work := by
  exact State.drainReadyGroups_preserves (fun state => state.GroupNodesMatchWork work)
    (fun _ node prior _ _ _ _ => (prior.finishGroupSuccess node).startNewWork _)
    (fun _ node errors prior _ _ _ => prior.finishGroupFailure node errors) matching

/-- Task failure closes active groups and updates latent counters/caches without
changing fixed-work provenance. Witness: removal, same-descriptor replacement, and fold.
-/
theorem State.GroupNodesMatchWork.taskFailure
    {queue : State} {work : Execution.Work}
    (matching : queue.GroupNodesMatchWork work)
    (occurrence : Occurrence) (errors : Nat)
    : (queue.taskFailure occurrence errors).1.GroupNodesMatchWork work := by
  let step (acc : State × List WorkQueueEvent)
      (group : Execution.DeliveryNode) :=
    let (current, events) := acc
    match current.groupNode? group.key with
    | none => (current, events)
    | some node =>
        if current.rootGroups.contains group.key then
          let (next, failure) := current.finishGroupFailure node errors
          (next, events ++ [failure])
        else (current.putGroupNode
          { node with
            pending := node.pending - 1
            failure := some (node.failure.getD 0 + errors) }, events)
  have stepMatch (acc : State × List WorkQueueEvent)
      (group : Execution.DeliveryNode)
      (currentMatch : acc.1.GroupNodesMatchWork work)
      : (step acc group).1.GroupNodesMatchWork work := by
    obtain ⟨current, events⟩ := acc
    dsimp only [step]
    split
    · exact currentMatch
    · rename_i node found
      split
      · exact currentMatch.finishGroupFailure _ errors
      · exact currentMatch.putGroupNode _
          (currentMatch node (List.mem_of_find?_eq_some found))
  have foldMatch (groups : List Execution.DeliveryNode) :
      ∀ acc : State × List WorkQueueEvent,
        acc.1.GroupNodesMatchWork work
          → (groups.foldl step acc).1.GroupNodesMatchWork work := by
    induction groups with
    | nil => intro acc currentMatch; exact currentMatch
    | cons group rest ih =>
        intro acc currentMatch
        exact ih (step acc group) (stepMatch acc group currentMatch)
  unfold State.taskFailure
  split
  · exact matching
  · rename_i taskNode found
    let current := queue.removeTask occurrence
    have currentMatch : current.GroupNodesMatchWork work := matching.removeTask occurrence
    split
    · exact currentMatch
    change (taskNode.task.groups.foldl step (current, [])).1.GroupNodesMatchWork work
    exact foldMatch taskNode.task.groups (current, []) currentMatch

/-- Task success registers only its matched child groups; settlement and
release remove or update existing nodes without changing provenance. -/
theorem State.GroupNodesMatchWork.taskSuccess
    {queue : State} {work : Execution.Work}
    (matching : queue.GroupNodesMatchWork work)
    (occurrence : Occurrence) (result : TaskResult)
    (childrenMatch
      : ∀ group ∈ result.work.groups,
          ∃ dependencies, GroupRecordAt work group.node dependencies)
    : (queue.taskSuccess occurrence result).1.GroupNodesMatchWork work := by
  let settleStep (current : State) (group : Execution.DeliveryNode) : State :=
    match current.groupNode? group.key with
    | none => current
    | some node => current.putGroupNode { node with pending := node.pending - 1 }
  have settleMatch (current : State) (group : Execution.DeliveryNode)
      (currentMatch : current.GroupNodesMatchWork work)
      : (settleStep current group).GroupNodesMatchWork work := by
    unfold settleStep
    split
    · exact currentMatch
    · rename_i node found
      exact currentMatch.putGroupNode _
        (currentMatch node (List.mem_of_find?_eq_some found))
  let releaseStep (acc : State × List WorkQueueEvent × NewWork)
      (group : Execution.DeliveryNode) :=
    let (current, events, released) := acc
    match current.groupNode? group.key with
    | none => (current, events, released)
    | some node =>
        let node := { node with pending := node.pending - 1 }
        let current := current.putGroupNode node
        if current.rootGroups.contains group.key && node.pending == 0
            && node.failure.isNone then
          let (next, finished, newWork) := current.finishGroupSuccess node
          (next, events ++ finished,
            ⟨released.newGroups ++ newWork.newGroups,
              released.newStreams ++ newWork.newStreams⟩)
        else (current, events, released)
  have releaseMatch (acc : State × List WorkQueueEvent × NewWork)
      (group : Execution.DeliveryNode)
      (currentMatch : acc.1.GroupNodesMatchWork work)
      : (releaseStep acc group).1.GroupNodesMatchWork work := by
    obtain ⟨current, events, released⟩ := acc
    dsimp only [releaseStep]
    split
    · exact currentMatch
    · rename_i node found
      have decremented : (current.putGroupNode
          { node with pending := node.pending - 1 }).GroupNodesMatchWork work := by
        simpa only [settleStep, found] using settleMatch current group currentMatch
      split
      · exact decremented.finishGroupSuccess _
      · exact decremented
  have releaseFold (groups : List Execution.DeliveryNode) :
      ∀ acc : State × List WorkQueueEvent × NewWork,
        acc.1.GroupNodesMatchWork work
          → (groups.foldl releaseStep acc).1.GroupNodesMatchWork work := by
    induction groups with
    | nil => intro acc currentMatch; exact currentMatch
    | cons group rest ih =>
        intro acc currentMatch
        exact ih (releaseStep acc group) (releaseMatch acc group currentMatch)
  unfold State.taskSuccess
  split
  · exact matching
  · rename_i taskNode found
    split
    · exact matching.removeTask occurrence
    let withValue := queue.putTaskNode { taskNode with value := some result.value }
    have withValueMatch : withValue.GroupNodesMatchWork work := matching
    let integrated := (withValue.maybeIntegrateWork result.work (some occurrence)).1
    have integratedMatch : integrated.GroupNodesMatchWork work :=
      withValueMatch.maybeIntegrateWork result.work childrenMatch
        (some occurrence)
    let released := taskNode.task.groups.foldl releaseStep (integrated, [], {})
    have releasedMatch : released.1.GroupNodesMatchWork work :=
      releaseFold taskNode.task.groups (integrated, [], {}) integratedMatch
    change (released.1.startNewWork released.2.2).drainReadyGroups.1.GroupNodesMatchWork work
    exact (releasedMatch.startNewWork released.2.2).drainReadyGroups

/-- Each stream item contributes only group nodes in its matched item-child
Work; the queue retains that provenance across a whole item batch. -/
theorem State.GroupNodesMatchWork.streamItems
    {queue : State} {work : Execution.Work}
    (matching : queue.GroupNodesMatchWork work)
    (stream : Execution.DeliveryNode) (items : List StreamItem)
    (childrenMatch
      : ∀ item ∈ items,
        ∀ group ∈ item.work.groups,
          ∃ dependencies, GroupRecordAt work group.node dependencies)
    : (queue.streamItems stream items).1.GroupNodesMatchWork work := by
  let step (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue)
      (item : StreamItem) :=
    let (current, groups, streams, values) := acc
    let (integrated, newWork) := current.maybeIntegrateWork item.work
    let (pruned, nonempty) := integrated.pruneEmptyGroups newWork.newGroups
    (pruned.startNewWork { newWork with newGroups := nonempty },
      groups ++ nonempty, streams ++ newWork.newStreams,
      values ++ [item.value])
  have stepMatch (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue)
      (item : StreamItem) (currentMatch : acc.1.GroupNodesMatchWork work)
      (itemMember : item ∈ items)
      : (step acc item).1.GroupNodesMatchWork work := by
    obtain ⟨current, groups, streams, values⟩ := acc
    let integrated := current.maybeIntegrateWork item.work
    have integratedMatch : integrated.1.GroupNodesMatchWork work :=
      currentMatch.maybeIntegrateWork item.work
        (childrenMatch item itemMember)
    let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
    have prunedMatch : pruned.1.GroupNodesMatchWork work :=
      integratedMatch.pruneEmptyGroups integrated.2.newGroups
    exact prunedMatch.startNewWork
      { integrated.2 with newGroups := pruned.2 }
  have foldMatch (more : List StreamItem)
      (subset : ∀ item ∈ more, item ∈ items) :
      ∀ acc : State × List Execution.DeliveryNode
        × List Execution.DeliveryNode × List StreamItemValue,
        acc.1.GroupNodesMatchWork work
          → (more.foldl step acc).1.GroupNodesMatchWork work := by
    induction more with
    | nil => intro acc currentMatch; exact currentMatch
    | cons item rest ih =>
        intro acc currentMatch
        have itemMember : item ∈ items := subset item (by simp)
        have restSubset : ∀ next ∈ rest, next ∈ items := by
          intro next nextMember
          exact subset next (by simp [nextMember])
        exact ih restSubset (step acc item)
          (stepMatch acc item currentMatch itemMember)
  unfold State.streamItems
  split
  · exact matching
  · exact (foldMatch items (by intro item member; exact member)
      (queue, [], [], []) matching).drainReadyGroups

/-- Stream closures alter no group-node records. -/
theorem State.GroupNodesMatchWork.streamSuccess
    {queue : State} {work : Execution.Work}
    (matching : queue.GroupNodesMatchWork work)
    (stream : Execution.DeliveryNode)
    : (queue.streamSuccess stream).1.GroupNodesMatchWork work := by
  unfold State.streamSuccess
  split <;> exact matching

theorem State.GroupNodesMatchWork.streamFailure
    {queue : State} {work : Execution.Work}
    (matching : queue.GroupNodesMatchWork work)
    (stream : Execution.DeliveryNode) (errors : Nat)
    : (queue.streamFailure stream errors).1.GroupNodesMatchWork work := by
  unfold State.streamFailure
  split <;> exact matching

/-- Fixed-work event matching supplies provenance for all newly registered
group nodes, so one executable handler preserves the invariant. -/
theorem State.GroupNodesMatchWork.handleGraphEvent
    {queue : State} {work : Execution.Work}
    (registered : queue.GroupNodesMatchWork work)
    (event : GraphEvent) (matching : event.MatchesWork work)
    : (queue.handleGraphEvent event).1.GroupNodesMatchWork work := by
  cases event with
  | taskSuccess occurrence result =>
      exact registered.taskSuccess occurrence result
        (fun group member => matching.taskChildGroups_recordAt member)
  | taskFailure occurrence errors =>
      exact registered.taskFailure occurrence errors
  | streamItems stream items =>
      exact registered.streamItems stream items
        (fun item itemMember group groupMember =>
          matching.streamItem_childGroups_recordAt itemMember groupMember)
  | streamSuccess stream => exact registered.streamSuccess stream
  | streamFailure stream errors => exact registered.streamFailure stream errors

/-- Every matched host batch retains exact group-node provenance. -/
theorem State.GroupNodesMatchWork.handleGraphEvents
    {queue : State} {work : Execution.Work}
    (registered : queue.GroupNodesMatchWork work)
    (batch : List GraphEvent)
    (allMatch : ∀ event ∈ batch, event.MatchesWork work)
    : (queue.handleGraphEvents batch).1.GroupNodesMatchWork work := by
  let step (acc : State × List WorkQueueEvent) (event : GraphEvent) :=
    let (current, outputs) := acc
    let (next, produced) := current.handleGraphEvent event
    (next, outputs ++ produced)
  have foldMatch (events : List GraphEvent)
      (subset : ∀ event ∈ events, event ∈ batch) :
      ∀ acc : State × List WorkQueueEvent,
        acc.1.GroupNodesMatchWork work
          → (events.foldl step acc).1.GroupNodesMatchWork work := by
    induction events with
    | nil => intro acc currentMatch; exact currentMatch
    | cons event rest ih =>
        intro acc currentMatch
        have eventMatch : event.MatchesWork work := allMatch event (subset event (by simp))
        have restSubset : ∀ member ∈ rest, member ∈ batch := by
          intro member memberRest
          exact subset member (by simp [memberRest])
        obtain ⟨current, outputs⟩ := acc
        have nextMatch : (step (current, outputs) event).1.GroupNodesMatchWork work :=
          currentMatch.handleGraphEvent event eventMatch
        exact ih restSubset (step (current, outputs) event) nextMatch
  unfold State.handleGraphEvents
  split
  · exact registered
  · cases outcome : batch.foldl step (queue, []) with
    | mk current outputs =>
        have currentMatch : current.GroupNodesMatchWork work := by
          have folded := foldMatch batch (fun _ member => member)
            (queue, []) registered
          rw [outcome] at folded
          exact folded
        dsimp only
        split <;> exact currentMatch

/-- Arbitrary groupings of admissible graph events keep the group-node
registry tied to the fixed Work tree. -/
theorem State.GroupNodesMatchWork.runNormalized
    {queue : State} {work : Execution.Work}
    (registered : queue.GroupNodesMatchWork work)
    (batches : List (List GraphEvent))
    (allMatch : ∀ batch ∈ batches, ∀ event ∈ batch, event.MatchesWork work)
    : (queue.runNormalized batches).1.GroupNodesMatchWork work := by
  have stepMatch (acc : NormalizedAcc) (batch : List GraphEvent)
      (currentMatch : acc.1.GroupNodesMatchWork work)
      (batchMatch : ∀ event ∈ batch, event.MatchesWork work)
      : (normalizedStep acc batch).1.GroupNodesMatchWork work := by
    obtain ⟨current, publisher, outputs⟩ := acc
    unfold normalizedStep
    cases outcome : current.handleGraphEvents batch with
    | mk next raw =>
        have nextMatch : next.GroupNodesMatchWork work := by
          have handled := currentMatch.handleGraphEvents batch batchMatch
          rw [outcome] at handled
          exact handled
        dsimp only
        simp only [outcome]
        split <;> exact nextMatch
  have foldMatch (more : List (List GraphEvent))
      (subset : ∀ batch ∈ more, batch ∈ batches) :
      ∀ acc : NormalizedAcc,
        acc.1.GroupNodesMatchWork work
          → (more.foldl normalizedStep acc).1.GroupNodesMatchWork work := by
    induction more with
    | nil => intro acc currentMatch; exact currentMatch
    | cons batch rest ih =>
        intro acc currentMatch
        have batchMatch : ∀ event ∈ batch, event.MatchesWork work :=
          allMatch batch (subset batch (by simp))
        have restSubset : ∀ later ∈ rest, later ∈ batches := by
          intro later member
          exact subset later (by simp [member])
        exact ih restSubset (normalizedStep acc batch)
          (stepMatch acc batch currentMatch batchMatch)
  let publisher : IncrementalPublisher :=
    { active := queue.initialGroups ++ queue.initialStreams }
  change (batches.foldl normalizedStep (queue, publisher, [])).1.GroupNodesMatchWork
    work
  exact foldMatch batches (fun _ member => member)
    (queue, publisher, []) registered

/-- Every replay of matched events retains only contributor/ancestor registration records.
Witness: initialization provenance and per-handler replay preservation; output admission
and started-input assumptions are not needed for this structural fact.
-/
theorem ValidGraphEvents.runNormalized_groupNodesMatchWork
    {work : Execution.Work} {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten)
    : (((State.initialize (Work.fromExecution work)).runNormalized
          batches).1).GroupNodesMatchWork
        work := by
  apply (createWorkQueue_groupNodesMatchWork work).runNormalized batches
  intro batch batchMember event eventMember
  exact valid.eachMatches
    (List.mem_flatten.mpr ⟨batch, batchMember, eventMember⟩)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
