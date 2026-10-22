import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RegisteredTasks

/-! Registration and exact contributors of started task nodes. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (
  ExecutionGroupValue StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Started task nodes remain linked to registered task definitions
-----------------------------------------------------------------------------------------

/-- Every live task node refers to a task already registered by WorkQueue.
This ties the executable node map to the structural provenance ledger above.
-/
def State.StartedTasksRegistered (queue : State) : Prop :=
  ∀ node ∈ queue.taskNodes, node.task ∈ queue.tasks

/-- Replacing a task node preserves its registration when the replacement has
the same registered task definition.
-/
theorem State.StartedTasksRegistered.putTaskNode
    {queue : State} (registered : queue.StartedTasksRegistered)
    (updated : TaskNode) (known : updated.task ∈ queue.tasks)
    : (queue.putTaskNode updated).StartedTasksRegistered := by
  intro node member
  change node ∈ queue.taskNodes.map
    (fun old => if old.task.occurrence == updated.task.occurrence then updated else old)
    at member
  obtain ⟨old, oldMember, same⟩ := List.mem_map.mp member
  split at same
  · subst node
    exact known
  · subst node
    exact registered old oldMember

/-- Group-node updates cannot alter task-node registration. -/
theorem State.StartedTasksRegistered.putGroupNode
    {queue : State} (registered : queue.StartedTasksRegistered)
    (updated : GroupNode)
    : (queue.putGroupNode updated).StartedTasksRegistered :=
  registered

theorem State.StartedTasksRegistered.addGroup
    {queue : State} (registered : queue.StartedTasksRegistered) (group : Group)
    : (queue.addGroup group).StartedTasksRegistered := by
  unfold State.addGroup
  split
  · exact registered
  · split
    · exact registered
    · split
      · split <;> exact registered
      · exact registered

theorem State.StartedTasksRegistered.addGroups
    {queue : State} (registered : queue.StartedTasksRegistered)
    (groups : List Group)
    : (queue.addGroups groups).1.StartedTasksRegistered := by
  exact State.addGroups_preserves State.StartedTasksRegistered groups
    (fun _ group _ valid => valid.addGroup group) queue registered

/-- Task registration creates a started node only after appending that same
definition to the task list.
-/
theorem State.StartedTasksRegistered.addTask
    {queue : State} (registered : queue.StartedTasksRegistered) (task : Task)
    : (queue.addTask task).StartedTasksRegistered := by
  let withTask : State := { queue with tasks := queue.tasks ++ [task] }
  let step (current : State) (group : Execution.DeliveryNode) : State :=
    match current.groupNode? group.ref with
    | none => current
    | some node =>
        if node.tasks.contains task.occurrence then
          current
        else
          current.putGroupNode
            { node with tasks := node.tasks ++ [task.occurrence], pending := node.pending + 1 }
  have stepRegistered (current : State) (group : Execution.DeliveryNode)
      (currentRegistered : current.StartedTasksRegistered)
      (taskMember : task ∈ current.tasks)
      : (step current group).StartedTasksRegistered
        ∧ task ∈ (step current group).tasks := by
    unfold step
    split
    · exact ⟨currentRegistered, taskMember⟩
    · split
      · exact ⟨currentRegistered, taskMember⟩
      · exact ⟨currentRegistered.putGroupNode _, taskMember⟩
  have foldRegistered (groups : List Execution.DeliveryNode) :
      ∀ current, current.StartedTasksRegistered → task ∈ current.tasks
        → (groups.foldl step current).StartedTasksRegistered
          ∧ task ∈ (groups.foldl step current).tasks := by
    induction groups with
    | nil =>
        intro current currentRegistered taskMember
        exact ⟨currentRegistered, taskMember⟩
    | cons group rest ih =>
        intro current currentRegistered taskMember
        obtain ⟨nextRegistered, nextMember⟩ :=
          stepRegistered current group currentRegistered taskMember
        exact ih (step current group) nextRegistered nextMember
  have withTaskRegistered : withTask.StartedTasksRegistered := by
    intro node member
    exact List.mem_append.mpr (Or.inl (registered node member))
  have taskMember : task ∈ withTask.tasks := by simp [withTask]
  let current := task.groups.foldl step withTask
  obtain ⟨currentRegistered, currentMember⟩ :=
    foldRegistered task.groups withTask withTaskRegistered taskMember
  change (if task.groups.any (fun group => current.rootGroups.contains group.ref)
      && (current.taskNode? task.occurrence).isNone then
      { current with taskNodes := current.taskNodes ++ [{ task }] }
    else current).StartedTasksRegistered
  split
  · intro node member
    rcases List.mem_append.mp member with earlier | added
    · exact currentRegistered node earlier
    · simp only [List.mem_singleton] at added
      subst node
      exact currentMember
  · exact currentRegistered

/-- Stream integration can only update a preexisting producer task node. -/
theorem State.StartedTasksRegistered.addStreams
    {queue : State} (registered : queue.StartedTasksRegistered)
    (streams : List Stream) (parentTask : Option Occurrence)
    : (queue.addStreams streams parentTask).1.StartedTasksRegistered := by
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
  have currentRegistered : current.StartedTasksRegistered := registered
  cases parentTask with
  | none => exact currentRegistered
  | some occurrence =>
      simp only [State.addStreams]
      split
      · exact currentRegistered
      · rename_i node found
        apply currentRegistered.putTaskNode
        exact currentRegistered node (List.mem_of_find?_eq_some found)

/-- Work integration preserves started-task registration across its group,
task, and stream phases.
-/
theorem State.StartedTasksRegistered.maybeIntegrateWork
    {queue : State} (registered : queue.StartedTasksRegistered)
    (newWork : Work) (parentTask : Option Occurrence := none)
    : (queue.maybeIntegrateWork newWork parentTask).1.StartedTasksRegistered := by
  let withGroups := (queue.addGroups newWork.groups).1
  let withTasks := newWork.tasks.foldl State.addTask withGroups
  have taskFold (tasks : List Task) :
      ∀ current, current.StartedTasksRegistered
        → (tasks.foldl State.addTask current).StartedTasksRegistered := by
    induction tasks with
    | nil => intro current currentRegistered; exact currentRegistered
    | cons task rest ih =>
        intro current currentRegistered
        exact ih (current.addTask task) (currentRegistered.addTask task)
  have withTasksRegistered : withTasks.StartedTasksRegistered :=
    taskFold newWork.tasks withGroups (registered.addGroups newWork.groups)
  change (withTasks.addStreams newWork.streams parentTask).1.StartedTasksRegistered
  exact withTasksRegistered.addStreams newWork.streams parentTask

/-- Pruning empty group shells leaves both task lists unchanged. -/
theorem State.StartedTasksRegistered.pruneEmptyGroups
    {queue : State} (registered : queue.StartedTasksRegistered)
    (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.StartedTasksRegistered := by
  have loop (fuel : Nat) (current : State)
      (remaining kept : List Execution.DeliveryNode)
      (currentRegistered : current.StartedTasksRegistered)
      : (State.pruneEmptyGroups.go fuel current remaining kept).1.StartedTasksRegistered := by
    induction fuel generalizing current remaining kept with
    | zero => exact currentRegistered
    | succ fuel ih =>
        cases remaining with
        | nil => exact currentRegistered
        | cons group rest =>
            unfold State.pruneEmptyGroups.go
            split
            · exact ih _ _ _ currentRegistered
            · split
              · apply ih
                exact currentRegistered
              · exact ih _ _ _ currentRegistered
  exact loop _ queue groups [] registered

/-- A started task comes from the registered-task lookup. -/
theorem State.StartedTasksRegistered.startTask
    {queue : State} (registered : queue.StartedTasksRegistered)
    (occurrence : Occurrence) (available : List (Occurrence × Nat) := [])
    : (queue.startTask occurrence available).StartedTasksRegistered := by
  unfold State.startTask
  split
  · exact registered
  · split
    · exact registered
    · rename_i task found
      intro node member
      rcases List.mem_append.mp member with earlier | added
      · exact registered node earlier
      · simp only [List.mem_singleton] at added
        subst node
        exact List.mem_of_find?_eq_some found

/-- Cache exposure replaces outcomes while retaining a registered task definition. -/
theorem State.StartedTasksRegistered.cacheTaskFailures {queue : State}
    (registered : queue.StartedTasksRegistered) (available : List (Occurrence × Nat))
    : (queue.cacheTaskFailures available).StartedTasksRegistered := by
  induction available generalizing queue with
  | nil => exact registered
  | cons entry rest ih =>
      simp only [State.cacheTaskFailures, List.foldl_cons]
      split
      · exact ih registered
      · rename_i node found
        exact ih (registered.putTaskNode _ (registered node (List.mem_of_find?_eq_some found)))

/-- Group startup starts registered tasks or removes rejected groups and task nodes. -/
theorem State.StartedTasksRegistered.startGroup
    {queue : State} (registered : queue.StartedTasksRegistered) (ref : NodeRef)
    (available : List (Occurrence × Nat) := [])
    : (queue.startGroup ref available).1.StartedTasksRegistered := by
  have cached := registered.cacheTaskFailures available
  have tasks (more : List Occurrence) (current : State)
      (valid : current.StartedTasksRegistered)
      : (more.foldl (fun current task => current.startTask task available)
          current).StartedTasksRegistered := by
    induction more generalizing current with
    | nil => exact valid
    | cons task rest ih => exact ih _ (valid.startTask task available)
  unfold State.startGroup
  dsimp only
  split
  · exact cached
  · split
    · exact tasks _ _ cached
    · intro node member
      exact cached node (List.mem_filter.mp member).1

theorem State.StartedTasksRegistered.startStream
    {queue : State} (registered : queue.StartedTasksRegistered) (ref : NodeRef)
    : (queue.startStream ref).StartedTasksRegistered := by
  unfold State.startStream
  split <;> exact registered

/-- Newly released groups start only task definitions already registered by
the corresponding Work integration step.
-/
theorem State.StartedTasksRegistered.startNewWork
    {queue : State} (registered : queue.StartedTasksRegistered)
    (newWork : NewWork) (available : List (Occurrence × Nat) := [])
    : (queue.startNewWork newWork available).1.StartedTasksRegistered := by
  have groups (refs : NodeRefs) (current : State) (failures : List GroupFailureEvent)
      (valid : current.StartedTasksRegistered)
      : (refs.foldl
          (fun (current, failures) ref =>
            let (next, queued) := current.startGroup ref available
            (next, failures ++ queued))
          (current, failures)).1.StartedTasksRegistered := by
    induction refs generalizing current failures with
    | nil => exact valid
    | cons ref rest ih => exact ih _ _ (valid.startGroup ref available)
  have streams (refs : NodeRefs) (current : State) (valid : current.StartedTasksRegistered)
      : (refs.foldl State.startStream current).StartedTasksRegistered := by
    induction refs generalizing current with
    | nil => exact valid
    | cons ref rest ih => exact ih _ (valid.startStream ref)
  unfold State.startNewWork
  exact streams _ _ (groups _ _ [] registered)

/-- WorkQueue initialization starts no unregistered task node. -/
theorem createWorkQueue_startedTasksRegistered (initialWork : Work)
    : (State.initialize initialWork).StartedTasksRegistered := by
  let integrated := (({} : State).maybeIntegrateWork initialWork).1
  let newWork := (({} : State).maybeIntegrateWork initialWork).2
  let pruned := (integrated.pruneEmptyGroups newWork.newGroups).1
  let groups := (integrated.pruneEmptyGroups newWork.newGroups).2
  let roots := { newWork with newGroups := groups }
  let started := (pruned.startNewWork roots).1
  have emptyRegistered : ({} : State).StartedTasksRegistered := by
    intro node member
    cases member
  have integratedRegistered : integrated.StartedTasksRegistered :=
    emptyRegistered.maybeIntegrateWork initialWork
  have prunedRegistered : pruned.StartedTasksRegistered :=
    integratedRegistered.pruneEmptyGroups newWork.newGroups
  have startedRegistered : started.StartedTasksRegistered :=
    prunedRegistered.startNewWork roots
  change State.StartedTasksRegistered
    { started with initialGroups := groups, initialStreams := roots.newStreams }
  exact startedRegistered

/-- An initialized task node inherits distinct contributor refs from its
registered definition and the generated Work tree.
-/
private theorem createWorkQueue_fromSpec_startedContributorsNodup
    {work : Execution.Work} (generated : ExecutedWork work)
    {node : TaskNode}
    (member : node ∈ (State.initialize (Work.fromExecution work)).taskNodes)
    : (node.task.groups.map Execution.DeliveryNode.ref).Nodup := by
  have taskMember : node.task ∈ (State.initialize (Work.fromExecution work)).tasks :=
    createWorkQueue_startedTasksRegistered (Work.fromExecution work) node member
  exact createWorkQueue_fromSpec_registeredContributorsNodup generated taskMember

/-- Filtering settled or cancelled task nodes cannot introduce a node whose
task was not previously registered.
-/
theorem State.StartedTasksRegistered.removeTask
    {queue : State} (registered : queue.StartedTasksRegistered)
    (occurrence : Occurrence)
    : (queue.removeTask occurrence).StartedTasksRegistered := by
  intro node member
  exact registered node (List.mem_filter.mp member).1

theorem State.StartedTasksRegistered.removeGroup
    {queue : State} (registered : queue.StartedTasksRegistered) (ref : NodeRef)
    : (queue.removeGroup ref).StartedTasksRegistered := by
  intro node member
  exact registered node (List.mem_filter.mp member).1

/-- Flushing a group removes task nodes and prunes group shells, but never
creates a node outside the registered task set.
-/
theorem State.StartedTasksRegistered.finishGroupSuccess
    {queue : State} (registered : queue.StartedTasksRegistered)
    (group : GroupNode)
    : (queue.finishGroupSuccess group).1.StartedTasksRegistered := by
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
  have stepRegistered (acc : State × List ExecutionGroupValue × NodeRefs)
      (occurrence : Occurrence)
      (currentRegistered : acc.1.StartedTasksRegistered)
      : (step acc occurrence).1.StartedTasksRegistered := by
    obtain ⟨current, values, streams⟩ := acc
    dsimp only [step]
    split
    · exact currentRegistered
    · exact currentRegistered.removeTask occurrence
  have foldRegistered (tasks : List Occurrence) :
      ∀ acc : State × List ExecutionGroupValue × NodeRefs,
        acc.1.StartedTasksRegistered
          → (tasks.foldl step acc).1.StartedTasksRegistered := by
    induction tasks with
    | nil => intro acc currentRegistered; exact currentRegistered
    | cons occurrence rest ih =>
        intro acc currentRegistered
        exact ih (step acc occurrence)
          (stepRegistered acc occurrence currentRegistered)
  let flushed := (group.tasks.foldl step (queue, [], [])).1
  have flushedRegistered : flushed.StartedTasksRegistered :=
    foldRegistered group.tasks (queue, [], []) registered
  let current : State :=
    { flushed with
        groupNodes := flushed.groupNodes.filter
          (fun node => node.group.node.ref != group.group.node.ref)
        rootGroups := flushed.rootGroups.filter (· != group.group.node.ref) }
  have currentRegistered : current.StartedTasksRegistered := flushedRegistered
  let children := group.childGroups.filterMap
    (fun ref => (current.groupNode? ref).map (fun node => node.group.node))
  change (current.pruneEmptyGroups children).1.StartedTasksRegistered
  exact currentRegistered.pruneEmptyGroups children

theorem State.StartedTasksRegistered.finishGroupFailure
    {queue : State} (registered : queue.StartedTasksRegistered)
    (group : GroupNode) (errors : Nat)
    : (queue.finishGroupFailure group errors).1.StartedTasksRegistered :=
  registered.removeGroup group.group.node.ref

/-- Rejection retention preserves started nodes' registered task definitions. -/
theorem State.StartedTasksRegistered.taskFailure
    {queue : State} (registered : queue.StartedTasksRegistered)
    (occurrence : Occurrence) (errors : Nat)
    : (queue.taskFailure occurrence errors).1.StartedTasksRegistered := by
  cases found : queue.taskNode? occurrence with
  | none => simpa [State.taskFailure, found] using registered
  | some node =>
      rw [queue.taskFailure_eq occurrence errors node found]
      exact failureGroupFold_preserves State.StartedTasksRegistered
        (fun _ ref prior => prior.removeGroup ref) _ _ _
        (registered.putTaskNode _ (registered node (List.mem_of_find?_eq_some found)))

/-- Draining settled roots starts only previously registered tasks.
Witness: both closure paths and activation preserve the registration invariant.
-/
theorem State.StartedTasksRegistered.drainReadyGroups
    {queue : State} (registered : queue.StartedTasksRegistered)
    (available : List (Occurrence × Nat) := [])
    : (queue.drainReadyGroups available).1.StartedTasksRegistered :=
  State.drainReadyGroups_preserves State.StartedTasksRegistered
    (fun _ node prior _ _ _ => (prior.finishGroupSuccess node).startNewWork _ available)
    registered

/-- The single-pass success-owner fold preserves started-task registration before
activation and draining. Witness: each decrement or successful flush preserves it.
-/
theorem State.StartedTasksRegistered.successGroupFold
    (groups : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent × NewWork)
    (registered : acc.1.StartedTasksRegistered)
    : (groups.foldl successGroupStep acc).1.StartedTasksRegistered := by
  induction groups generalizing acc with
  | nil => exact registered
  | cons group rest ih =>
      apply ih
      obtain ⟨current, events, released⟩ := acc
      dsimp only [successGroupStep]
      split
      · exact registered
      · rename_i node found
        have decremented := registered.putGroupNode { node with pending := node.pending - 1 }
        split
        · exact decremented.finishGroupSuccess _
        · exact decremented

/-- Successful task settlement keeps stored task nodes linked to registered
definitions through value storage, child integration, and group flushes.
-/
theorem State.StartedTasksRegistered.taskSuccess
    {queue : State} (registered : queue.StartedTasksRegistered)
    (occurrence : Occurrence) (result : TaskResult)
    (available : List (Occurrence × Nat) := [])
    : (queue.taskSuccess occurrence result available).1.StartedTasksRegistered := by
  let settleStep (current : State) (group : Execution.DeliveryNode) : State :=
    match current.groupNode? group.ref with
    | none => current
    | some node => current.putGroupNode { node with pending := node.pending - 1 }
  have settleRegistered (current : State) (group : Execution.DeliveryNode)
      (currentRegistered : current.StartedTasksRegistered)
      : (settleStep current group).StartedTasksRegistered := by
    unfold settleStep
    split
    · exact currentRegistered
    · exact currentRegistered.putGroupNode _
  let releaseStep (acc : State × List WorkQueueEvent × NewWork)
      (group : Execution.DeliveryNode) : State × List WorkQueueEvent × NewWork :=
    let (current, events, released) := acc
    match current.groupNode? group.ref with
    | none => (current, events, released)
    | some node =>
        let node := { node with pending := node.pending - 1 }
        let current := current.putGroupNode node
        if current.rootGroups.contains group.ref && node.pending == 0 then
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
          (current, events, released)
  have releaseRegistered (acc : State × List WorkQueueEvent × NewWork)
      (group : Execution.DeliveryNode)
      (currentRegistered : acc.1.StartedTasksRegistered)
      : (releaseStep acc group).1.StartedTasksRegistered := by
    obtain ⟨current, events, released⟩ := acc
    dsimp only [releaseStep]
    split
    · exact currentRegistered
    · rename_i node found
      have decremented : (current.putGroupNode
          { node with pending := node.pending - 1 }).StartedTasksRegistered := by
        simpa only [settleStep, found]
          using settleRegistered current group currentRegistered
      split
      · exact decremented.finishGroupSuccess _
      · exact decremented
  have releaseFold (groups : List Execution.DeliveryNode) :
      ∀ acc : State × List WorkQueueEvent × NewWork,
        acc.1.StartedTasksRegistered
          → (groups.foldl releaseStep acc).1.StartedTasksRegistered := by
    induction groups with
    | nil => intro acc currentRegistered; exact currentRegistered
    | cons group rest ih =>
        intro acc currentRegistered
        exact ih (releaseStep acc group)
          (releaseRegistered acc group currentRegistered)
  unfold State.taskSuccess
  split
  · exact registered
  · rename_i taskNode found
    have taskMember : taskNode.task ∈ queue.tasks :=
      registered taskNode (List.mem_of_find?_eq_some found)
    let withValue := queue.putTaskNode { taskNode with value := some result.value }
    have withValueRegistered : withValue.StartedTasksRegistered :=
      registered.putTaskNode _ taskMember
    let integrated := (withValue.maybeIntegrateWork result.work (some occurrence)).1
    have integratedRegistered : integrated.StartedTasksRegistered :=
      withValueRegistered.maybeIntegrateWork result.work (some occurrence)
    let finished := taskNode.task.groups.foldl releaseStep (integrated, [], {})
    have finishedRegistered : finished.1.StartedTasksRegistered :=
      releaseFold taskNode.task.groups (integrated, [], {}) integratedRegistered
    change ((finished.1.startNewWork finished.2.2 available).1.drainReadyGroups
      available).1.StartedTasksRegistered
    exact (finishedRegistered.startNewWork finished.2.2 available).drainReadyGroups available

/-- Each stream item may integrate child work and start its task nodes; every
such node remains linked to the integrated task definition.
-/
theorem State.StartedTasksRegistered.streamItems {queue : State}
    (unique : queue.StartedTasksRegistered) (stream : Execution.DeliveryNode)
    (items : List StreamItem) (available : List (Occurrence × Nat) := [])
    : (queue.streamItems stream items available).1.StartedTasksRegistered := by
  let step (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue × List GroupFailureEvent)
      (item : StreamItem) :=
    let (current, groups, streams, values, failures) := acc
    let (integrated, newWork) := current.maybeIntegrateWork item.work
    let (pruned, nonempty) := integrated.pruneEmptyGroups newWork.newGroups
    let (started, queued) :=
      pruned.startNewWork { newWork with newGroups := nonempty } available
    (
      started,
      groups ++ nonempty,
      streams ++ newWork.newStreams,
      values ++ [item.value],
      failures ++ queued
    )
  have stepUnique (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue × List GroupFailureEvent)
      (item : StreamItem) (currentUnique : acc.1.StartedTasksRegistered)
      : (step acc item).1.StartedTasksRegistered := by
    obtain ⟨current, groups, streams, values, failures⟩ := acc
    let integrated := current.maybeIntegrateWork item.work
    have integratedUnique : integrated.1.StartedTasksRegistered :=
      currentUnique.maybeIntegrateWork item.work
    let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
    have prunedUnique : pruned.1.StartedTasksRegistered :=
      integratedUnique.pruneEmptyGroups integrated.2.newGroups
    exact prunedUnique.startNewWork { integrated.2 with newGroups := pruned.2 } available
  have foldUnique (more : List StreamItem) :
      ∀ acc : State × List Execution.DeliveryNode
        × List Execution.DeliveryNode × List StreamItemValue × List GroupFailureEvent,
        acc.1.StartedTasksRegistered → (more.foldl step acc).1.StartedTasksRegistered := by
    induction more with
    | nil => intro acc currentUnique; exact currentUnique
    | cons item rest ih =>
        intro acc currentUnique
        exact ih (step acc item) (stepUnique acc item currentUnique)
  dsimp only [State.streamItems]
  split
  · exact unique
  · exact (foldUnique items (queue, [], [], [], []) unique).drainReadyGroups available

theorem State.StartedTasksRegistered.streamSuccess
    {queue : State} (registered : queue.StartedTasksRegistered)
    (stream : Execution.DeliveryNode)
    : (queue.streamSuccess stream).1.StartedTasksRegistered := by
  unfold State.streamSuccess
  split <;> exact registered

theorem State.StartedTasksRegistered.streamFailure
    {queue : State} (registered : queue.StartedTasksRegistered)
    (stream : Execution.DeliveryNode) (errors : Nat)
    : (queue.streamFailure stream errors).1.StartedTasksRegistered := by
  unfold State.streamFailure
  split <;> exact registered

/-- Started-node registration holds after any queue event, independently of
whether that host event matched the spec Work.
-/
theorem State.StartedTasksRegistered.handleGraphEvent {queue : State}
    (unique : queue.StartedTasksRegistered) (event : GraphEvent)
    (available : List (Occurrence × Nat) := [])
    : (queue.handleGraphEvent event available).1.StartedTasksRegistered := by
  have cached := unique.cacheTaskFailures available
  cases event with
  | taskSuccess occurrence result => exact cached.taskSuccess occurrence result available
  | taskFailure occurrence errors => exact cached.taskFailure occurrence errors
  | groupFailure failure =>
      change ((queue.cacheTaskFailures available).groupFailure failure).1.StartedTasksRegistered
      unfold State.groupFailure
      split
      · exact cached
      · split <;> exact cached
  | streamItems stream items => exact cached.streamItems stream items available
  | streamSuccess stream => exact cached.streamSuccess stream
  | streamFailure stream errors => exact cached.streamFailure stream errors

/-- Every available host batch retains registration of started computations. -/
theorem State.StartedTasksRegistered.handleGraphEvents {queue : State}
    (unique : queue.StartedTasksRegistered) (batch : List GraphEvent)
    : (queue.handleGraphEvents batch).1.StartedTasksRegistered := by
  let available := GraphEvent.availableFailures batch
  let step (acc : State × List WorkQueueEvent) (event : GraphEvent) :=
    let (next, produced) := acc.1.dispatchGraphEvent event available
    (next, acc.2 ++ produced)
  have foldUnique (events : List GraphEvent) :
      ∀ acc : State × List WorkQueueEvent,
        acc.1.StartedTasksRegistered → (events.foldl step acc).1.StartedTasksRegistered := by
    induction events with
    | nil => intro acc currentUnique; exact currentUnique
    | cons event rest ih =>
        intro acc currentUnique
        exact ih (step acc event) (currentUnique.handleGraphEvent event available)
  unfold State.handleGraphEvents
  split
  · exact unique
  · dsimp only
    split <;> exact foldUnique batch (queue, []) unique

/-- The registration invariant survives all finite graph-event batches and
publisher normalization, without a source assumption.
-/
theorem State.runNormalized_startedTasksRegistered
    {queue : State} (registered : queue.StartedTasksRegistered)
    (batches : List (List GraphEvent))
    : (queue.runNormalized batches).1.StartedTasksRegistered := by
  have stepRegistered (acc : NormalizedAcc) (batch : List GraphEvent)
      (currentRegistered : acc.1.StartedTasksRegistered)
      : (normalizedStep acc batch).1.StartedTasksRegistered := by
    obtain ⟨current, publisher, outputs⟩ := acc
    unfold normalizedStep
    cases outcome : current.handleGraphEvents batch with
    | mk next raw =>
        have nextRegistered : next.StartedTasksRegistered := by
          have handled := currentRegistered.handleGraphEvents batch
          rw [outcome] at handled
          exact handled
        dsimp only
        simp only [outcome]
        split <;> exact nextRegistered
  have foldRegistered (more : List (List GraphEvent)) :
      ∀ acc : NormalizedAcc, acc.1.StartedTasksRegistered
        → (more.foldl normalizedStep acc).1.StartedTasksRegistered := by
    induction more with
    | nil => intro acc currentRegistered; exact currentRegistered
    | cons batch rest ih =>
        intro acc currentRegistered
        exact ih (normalizedStep acc batch)
          (stepRegistered acc batch currentRegistered)
  let publisher : IncrementalPublisher :=
    { active := queue.initialGroups ++ queue.initialStreams }
  change (batches.foldl normalizedStep
    (queue, publisher, [])).1.StartedTasksRegistered
  exact foldRegistered batches (queue, publisher, []) registered

/-- In every admitted replay, each live task node inherits distinct
contributor refs from its registered task's generated-work provenance.
-/
private theorem createWorkQueue_runNormalized_startedContributorsNodup
    {work : Execution.Work} (generated : ExecutedWork work)
    {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten)
    {node : TaskNode}
    (member
      : node
        ∈ ((State.initialize (Work.fromExecution work)).runNormalized
            batches).1.taskNodes)
    : (node.task.groups.map Execution.DeliveryNode.ref).Nodup := by
  let queue := State.initialize (Work.fromExecution work)
  let current := (queue.runNormalized batches).1
  have started : current.StartedTasksRegistered :=
    State.runNormalized_startedTasksRegistered
      (createWorkQueue_startedTasksRegistered (Work.fromExecution work)) batches
  have matching : current.RegisteredTasksMatch work :=
    createWorkQueue_runNormalized_registeredTasksMatch valid
  exact matching.contributorsNodup generated (started node member)

/-- A started task node retains exactly the spec Work's contributor descriptors,
not merely an equal list of contributor refs.
-/
private theorem createWorkQueue_runNormalized_startedGroupsExact
    {work : Execution.Work} {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten)
    {node : TaskNode}
    (member
      : node
        ∈ ((State.initialize (Work.fromExecution work)).runNormalized
            batches).1.taskNodes)
    : taskGroups? work node.task.occurrence = some node.task.groups := by
  let queue := State.initialize (Work.fromExecution work)
  let current := (queue.runNormalized batches).1
  have started : current.StartedTasksRegistered :=
    State.runNormalized_startedTasksRegistered
      (createWorkQueue_startedTasksRegistered (Work.fromExecution work)) batches
  have matching : current.RegisteredTasksMatch work :=
    createWorkQueue_runNormalized_registeredTasksMatch valid
  exact (matching node.task (started node member)).2

/-- A matched successful host value and the live queue task agree on their
complete contributor list. This follows from the two exact Work lookups.
-/
private theorem createWorkQueue_runNormalized_successGroupsExact
    {work : Execution.Work} {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten)
    {occurrence : Occurrence} {result : TaskResult}
    (eventMatch : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    {node : TaskNode}
    (member
      : node
        ∈ ((State.initialize (Work.fromExecution work)).runNormalized
            batches).1.taskNodes)
    (same : node.task.occurrence = occurrence)
    : node.task.groups = result.value.deliveryGroups := by
  have exactNode := createWorkQueue_runNormalized_startedGroupsExact valid member
  obtain ⟨owners, producer, known, exactResult, childWork⟩ := eventMatch
  rw [same, exactResult] at exactNode
  exact Option.some.inj exactNode.symm

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
