import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureDebt
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GraphEvents
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SourceObservation

/-! Structural provenance of registered task definitions. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (
  ExecutionGroupValue StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Structural provenance of registered queue tasks
-----------------------------------------------------------------------------------------

/-- Structural task provenance includes both its occurrence/owner refs and
the exact contributor descriptors retained by the executable queue.
-/
def TaskMatches (work : Execution.Work) (task : Task) : Prop :=
  (∃ address payload producer,
    task.occurrence = .executionGroup address
    ∧ TaskAt work task.occurrence
        (task.groups.map Execution.DeliveryNode.ref) producer payload)
  ∧ taskGroups? work task.occurrence = some task.groups

/-- Every registered task comes from one located execution group in the original
Work. This is proof-only state evidence; the executable queue stores no spec Work.
-/
def State.RegisteredTasksMatch (queue : State) (work : Execution.Work) : Prop :=
  ∀ task ∈ queue.tasks, TaskMatches work task

/-- Every matched task contributor has an actual group descriptor, unlike an ancestor.
Witness: exact contributor-list matching at the task's located execution-group boundary.
-/
theorem TaskMatches.contributorsLocated {work task} (matching : TaskMatches work task)
    {group : Execution.DeliveryNode} (member : group ∈ task.groups)
    : ∃ dependencies producer, NodeAt work group .group dependencies producer := by
  obtain ⟨⟨address, payload, producer, occurrenceEq, known⟩, exactGroups⟩ := matching
  rw [occurrenceEq] at known exactGroups
  obtain ⟨groups, path, outcome, children, enclosing, located, _, _⟩ := known
  change locateWork work address = some
    ⟨.executionGroup groups path outcome children, producer, enclosing⟩ at located
  have mapped : groups.map Execution.DeferredFragment.node = task.groups := by
    simpa [taskGroups?_eq_lookup, located] using exactGroups
  rw [← mapped] at member
  obtain ⟨fragment, inGroups, same⟩ := List.mem_map.mp member
  exact ⟨fragment.ancestors.map Execution.DeliveryNode.ref, producer,
    address, groups, path, outcome, children, enclosing, fragment,
    located, inGroups, same.symm, rfl⟩

/-- A matched task's owner ref denotes a genuine contributor with fixed dependencies.
Witness: select its retained descriptor and project its source group occurrence.
-/
theorem TaskMatches.contributorKnown {work task ref} (matching : TaskMatches work task)
    (member : ref ∈ task.groups.map Execution.DeliveryNode.ref)
    : ∃ dependencies, NodeHasDependencies work ref .group dependencies := by
  obtain ⟨group, member, same⟩ := List.mem_map.mp member
  obtain ⟨dependencies, producer, known⟩ := matching.contributorsLocated member
  exact ⟨dependencies, group, producer, known, same⟩

/-- Group-node replacement does not change registered tasks. -/
theorem State.RegisteredTasksMatch.putGroupNode {queue : State} {work : Execution.Work}
    (matching : queue.RegisteredTasksMatch work) (updated : GroupNode)
    : (queue.putGroupNode updated).RegisteredTasksMatch work :=
  matching

/-- Registering a group leaves the registered-task list unchanged. -/
theorem State.RegisteredTasksMatch.addGroup {queue : State} {work : Execution.Work}
    (matching : queue.RegisteredTasksMatch work) (group : Group)
    : (queue.addGroup group).RegisteredTasksMatch work := by
  unfold State.addGroup
  split
  · exact matching
  · split
    · exact matching
    · split
      · split <;> exact matching
      · exact matching

/-- Recursive parent registration leaves the registered-task list unchanged. -/
theorem State.RegisteredTasksMatch.addGroups {queue : State} {work : Execution.Work}
    (matching : queue.RegisteredTasksMatch work) (groups : List Group)
    : (queue.addGroups groups).1.RegisteredTasksMatch work := by
  exact State.addGroups_preserves (fun current => current.RegisteredTasksMatch work) groups
    (fun _ group _ valid => valid.addGroup group) queue matching

/-- Task integration appends exactly one new task definition; group-link and
starting bookkeeping do not change the registered-task list.
-/
theorem State.RegisteredTasksMatch.addTask {queue : State} {work : Execution.Work}
    (matching : queue.RegisteredTasksMatch work) (task : Task)
    (known : TaskMatches work task)
    : (queue.addTask task).RegisteredTasksMatch work := by
  let registered : State := { queue with tasks := queue.tasks ++ [task] }
  let step (current : State) (group : Execution.DeliveryNode) : State :=
    match current.groupNode? group.ref with
    | none => current
    | some node =>
        if node.tasks.contains task.occurrence then
          current
        else
          current.putGroupNode
            { node with tasks := node.tasks ++ [task.occurrence], pending := node.pending + 1 }
  have stepMatch (current : State) (group : Execution.DeliveryNode)
      (currentMatch : current.RegisteredTasksMatch work)
      : (step current group).RegisteredTasksMatch work := by
    unfold step
    split
    · exact currentMatch
    · split
      · exact currentMatch
      · exact currentMatch.putGroupNode _
  have foldMatch (groups : List Execution.DeliveryNode) :
      ∀ current, current.RegisteredTasksMatch work
        → (groups.foldl step current).RegisteredTasksMatch work := by
    induction groups with
    | nil => intro current currentMatch; exact currentMatch
    | cons group rest ih =>
        intro current currentMatch
        exact ih (step current group) (stepMatch current group currentMatch)
  have registeredMatch : registered.RegisteredTasksMatch work := by
    intro candidate member
    change candidate ∈ queue.tasks ++ [task] at member
    rcases List.mem_append.mp member with earlier | added
    · exact matching candidate earlier
    · simp only [List.mem_singleton] at added
      subst candidate
      exact known
  let current := task.groups.foldl step registered
  have currentMatch : current.RegisteredTasksMatch work :=
    foldMatch task.groups registered registeredMatch
  change (if task.groups.any (fun group => current.rootGroups.contains group.ref)
      && (current.taskNode? task.occurrence).isNone then
      { current with taskNodes := current.taskNodes ++ [{ task }] }
    else current).RegisteredTasksMatch work
  split <;> exact currentMatch

/-- Stream registration and task-node links leave registered tasks unchanged. -/
theorem State.RegisteredTasksMatch.addStreams {queue : State} {work : Execution.Work}
    (matching : queue.RegisteredTasksMatch work) (streams : List Stream)
    (parentTask : Option Occurrence)
    : (queue.addStreams streams parentTask).1.RegisteredTasksMatch work := by
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
  have currentMatch : current.RegisteredTasksMatch work := matching
  cases parentTask with
  | none => exact currentMatch
  | some occurrence =>
      simp only [State.addStreams]
      split <;> exact currentMatch

/-- Every newly integrated task is structurally located if the input task
descriptors are. The other two Work collections never create task definitions.
-/
theorem State.RegisteredTasksMatch.maybeIntegrateWork
    {queue : State} {work : Execution.Work}
    (matching : queue.RegisteredTasksMatch work) (newWork : Work)
    (newTasks : ∀ task ∈ newWork.tasks, TaskMatches work task)
    (parentTask : Option Occurrence := none)
    : (queue.maybeIntegrateWork newWork parentTask).1.RegisteredTasksMatch work := by
  let withGroups := (queue.addGroups newWork.groups).1
  let withTasks := newWork.tasks.foldl State.addTask withGroups
  have taskFold (tasks : List Task) :
      ∀ current, current.RegisteredTasksMatch work
        → (∀ task ∈ tasks, TaskMatches work task)
        → (tasks.foldl State.addTask current).RegisteredTasksMatch work := by
    induction tasks with
    | nil => intro current currentMatch _; exact currentMatch
    | cons task rest ih =>
        intro current currentMatch allKnown
        have headKnown := allKnown task (by simp)
        have tailKnown : ∀ candidate ∈ rest, TaskMatches work candidate := by
          intro candidate member
          exact allKnown candidate (by simp [member])
        simpa only [List.foldl_cons]
          using ih (current.addTask task) (currentMatch.addTask task headKnown) tailKnown
  have withTasksMatch : withTasks.RegisteredTasksMatch work :=
    taskFold newWork.tasks withGroups (matching.addGroups newWork.groups) newTasks
  change (withTasks.addStreams newWork.streams parentTask).1.RegisteredTasksMatch work
  exact withTasksMatch.addStreams newWork.streams parentTask

/-- Empty-group pruning changes only live group nodes. -/
theorem State.RegisteredTasksMatch.pruneEmptyGroups
    {queue : State} {work : Execution.Work}
    (matching : queue.RegisteredTasksMatch work)
    (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.RegisteredTasksMatch work := by
  have loop (fuel : Nat) (current : State)
      (remaining kept : List Execution.DeliveryNode)
      (currentMatch : current.RegisteredTasksMatch work)
      : (State.pruneEmptyGroups.go fuel current remaining kept).1.RegisteredTasksMatch
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
                exact currentMatch
              · exact ih _ _ _ currentMatch
  exact loop _ queue groups [] matching

/-- Starting host work only adds task nodes; it does not register new tasks. -/
theorem State.RegisteredTasksMatch.startTask
    {queue : State} {work : Execution.Work}
    (matching : queue.RegisteredTasksMatch work) (occurrence : Occurrence)
    (available : List (Occurrence × Nat) := [])
    : (queue.startTask occurrence available).RegisteredTasksMatch work := by
  unfold State.startTask
  split
  · exact matching
  · split <;> exact matching

/-- Starting a group's registered tasks leaves provenance unchanged. -/
theorem State.RegisteredTasksMatch.startGroup
    {queue : State} {work : Execution.Work}
    (matching : queue.RegisteredTasksMatch work) (ref : NodeRef)
    (available : List (Occurrence × Nat) := [])
    : (queue.startGroup ref available).1.RegisteredTasksMatch work := by
  simpa only [State.RegisteredTasksMatch, State.startGroup_tasks] using matching

/-- Cached task outcomes do not change registered task definitions. -/
theorem State.RegisteredTasksMatch.cacheTaskFailures
    {queue : State} {work : Execution.Work}
    (matching : queue.RegisteredTasksMatch work) (available : List (Occurrence × Nat))
    : (queue.cacheTaskFailures available).RegisteredTasksMatch work := by
  simpa only [State.RegisteredTasksMatch, State.cacheTaskFailures_tasks] using matching

/-- Starting a stream only changes the active-root list. -/
theorem State.RegisteredTasksMatch.startStream
    {queue : State} {work : Execution.Work}
    (matching : queue.RegisteredTasksMatch work) (ref : NodeRef)
    : (queue.startStream ref).RegisteredTasksMatch work := by
  unfold State.startStream
  split <;> exact matching

/-- Newly released roots preserve provenance of all registered tasks. -/
theorem State.RegisteredTasksMatch.startNewWork
    {queue : State} {work : Execution.Work}
    (matching : queue.RegisteredTasksMatch work) (newWork : NewWork)
    (available : List (Occurrence × Nat) := [])
    : (queue.startNewWork newWork available).1.RegisteredTasksMatch work := by
  simpa only [State.RegisteredTasksMatch, State.startNewWork_tasks] using matching

/-- Initial queue registration exactly inherits structural task provenance
from the generated Work tree, including combined root work.
-/
private theorem createWorkQueue_registeredTasksMatch
    {work : Execution.Work} (initialWork : Work)
    (tasksLocated : ∀ task ∈ initialWork.tasks, TaskMatches work task)
    : (State.initialize initialWork).RegisteredTasksMatch work := by
  let integrated := (({} : State).maybeIntegrateWork initialWork).1
  let newWork := (({} : State).maybeIntegrateWork initialWork).2
  let pruned := (integrated.pruneEmptyGroups newWork.newGroups).1
  let groups := (integrated.pruneEmptyGroups newWork.newGroups).2
  let roots := { newWork with newGroups := groups }
  let started := (pruned.startNewWork roots).1
  have emptyMatch : ({} : State).RegisteredTasksMatch work := by
    intro task member
    cases member
  have integratedMatch : integrated.RegisteredTasksMatch work :=
    emptyMatch.maybeIntegrateWork initialWork tasksLocated
  have prunedMatch : pruned.RegisteredTasksMatch work :=
    integratedMatch.pruneEmptyGroups newWork.newGroups
  have startedMatch : started.RegisteredTasksMatch work :=
    prunedMatch.startNewWork roots
  change State.RegisteredTasksMatch
    { started with initialGroups := groups, initialStreams := roots.newStreams } work
  exact startedMatch

/-- The initialized reference queue registers only tasks from the input Work. -/
theorem createWorkQueue_fromSpec_registeredTasksMatch (work : Execution.Work)
    : (State.initialize (Work.fromExecution work)).RegisteredTasksMatch work := by
  apply createWorkQueue_registeredTasksMatch
  intro task member
  obtain ⟨address, payload, occurrenceEq, known⟩ :=
    workFromSpec_tasks_taskAt WorkQueueSemantics.Located.root member
  exact ⟨⟨address, payload, none, occurrenceEq, known⟩,
    workFromSpec_tasks_groupsExact WorkQueueSemantics.Located.root member⟩

/-- Every registered task in a structurally matched queue has distinct
contributors when its source Work was produced by root execution.
-/
theorem State.RegisteredTasksMatch.contributorsNodup
    {queue : State} {work : Execution.Work}
    (matching : queue.RegisteredTasksMatch work)
    (generated : ExecutedWork work)
    {task : Task} (member : task ∈ queue.tasks)
    : (task.groups.map Execution.DeliveryNode.ref).Nodup := by
  obtain ⟨⟨address, payload, producer, occurrenceEq, known⟩, _⟩ :=
    matching task member
  exact generated.taskOwners_nodup known

/-- In particular, initialization cannot register a task with a repeated
contributor ref, even when that task is shared by overlapping defers.
-/
theorem createWorkQueue_fromSpec_registeredContributorsNodup
    {work : Execution.Work} (generated : ExecutedWork work)
    {task : Task}
    (member : task ∈ (State.initialize (Work.fromExecution work)).tasks)
    : (task.groups.map Execution.DeliveryNode.ref).Nodup :=
  (createWorkQueue_fromSpec_registeredTasksMatch work).contributorsNodup generated member

/-- Settling a task removes live memberships, but keeps task definitions. -/
theorem State.RegisteredTasksMatch.removeTask
    {queue : State} {work : Execution.Work}
    (matching : queue.RegisteredTasksMatch work) (occurrence : Occurrence)
    : (queue.removeTask occurrence).RegisteredTasksMatch work :=
  matching

/-- Group cancellation retains the registered-task list. -/
theorem State.RegisteredTasksMatch.removeGroup
    {queue : State} {work : Execution.Work}
    (matching : queue.RegisteredTasksMatch work) (ref : NodeRef)
    : (queue.removeGroup ref).RegisteredTasksMatch work :=
  matching

/-- Group flushing removes task nodes and group shells but does not alter the
provenance of any registered task definition.
-/
theorem State.RegisteredTasksMatch.finishGroupSuccess
    {queue : State} {work : Execution.Work}
    (matching : queue.RegisteredTasksMatch work) (group : GroupNode)
    : (queue.finishGroupSuccess group).1.RegisteredTasksMatch work := by
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
  have stepMatch (acc : State × List ExecutionGroupValue × NodeRefs)
      (occurrence : Occurrence) (currentMatch : acc.1.RegisteredTasksMatch work)
      : (step acc occurrence).1.RegisteredTasksMatch work := by
    obtain ⟨current, values, streams⟩ := acc
    dsimp only [step]
    split
    · exact currentMatch
    · exact currentMatch.removeTask occurrence
  have foldMatch (tasks : List Occurrence) :
      ∀ acc : State × List ExecutionGroupValue × NodeRefs,
        acc.1.RegisteredTasksMatch work
          → (tasks.foldl step acc).1.RegisteredTasksMatch work := by
    induction tasks with
    | nil => intro acc currentMatch; exact currentMatch
    | cons occurrence rest ih =>
        intro acc currentMatch
        exact ih (step acc occurrence) (stepMatch acc occurrence currentMatch)
  let flushed := (group.tasks.foldl step (queue, [], [])).1
  have flushedMatch : flushed.RegisteredTasksMatch work :=
    foldMatch group.tasks (queue, [], []) matching
  let current : State :=
    { flushed with
        groupNodes := flushed.groupNodes.filter
          (fun node => node.group.node.ref != group.group.node.ref)
        rootGroups := flushed.rootGroups.filter (· != group.group.node.ref) }
  have currentMatch : current.RegisteredTasksMatch work := flushedMatch
  let children := group.childGroups.filterMap
    (fun ref => (current.groupNode? ref).map (fun node => node.group.node))
  change (current.pruneEmptyGroups children).1.RegisteredTasksMatch work
  exact currentMatch.pruneEmptyGroups children

/-- A failed group also leaves registered task definitions untouched. -/
theorem State.RegisteredTasksMatch.finishGroupFailure
    {queue : State} {work : Execution.Work}
    (matching : queue.RegisteredTasksMatch work) (group : GroupNode) (errors : Nat)
    : (queue.finishGroupFailure group errors).1.RegisteredTasksMatch work :=
  matching.removeGroup group.group.node.ref

/-- Retaining a task rejection and removing active owners adds no task definitions. -/
theorem State.RegisteredTasksMatch.taskFailure
    {queue : State} {work : Execution.Work}
    (matching : queue.RegisteredTasksMatch work)
    (occurrence : Occurrence) (errors : Nat)
    : (queue.taskFailure occurrence errors).1.RegisteredTasksMatch work := by
  cases found : queue.taskNode? occurrence with
  | none => simpa [State.taskFailure, found] using matching
  | some node =>
      rw [queue.taskFailure_eq occurrence errors node found]
      exact failureGroupFold_preserves (fun state => state.RegisteredTasksMatch work)
        (fun _ ref prior => prior.removeGroup ref) _ _ _ matching

/-- Draining retained outcomes adds no task definitions. Witness: provenance is
preserved by both closure paths and by activation of already registered work.
-/
theorem State.RegisteredTasksMatch.drainReadyGroups {queue : State}
    {work : Execution.Work} (matching : queue.RegisteredTasksMatch work)
    (available : List (Occurrence × Nat) := [])
    : (queue.drainReadyGroups available).1.RegisteredTasksMatch work :=
  State.drainReadyGroups_preserves (fun current => current.RegisteredTasksMatch work)
    (fun _ node prior _ _ _ => (prior.finishGroupSuccess node).startNewWork _ available)
    matching

/-- A successful task integrates only its supplied child task definitions;
settlement, flushing, and activation preserve their provenance.
-/
theorem State.RegisteredTasksMatch.taskSuccess
    {queue : State} {work : Execution.Work}
    (matching : queue.RegisteredTasksMatch work)
    (occurrence : Occurrence) (result : TaskResult)
    (childTasks : ∀ task ∈ result.work.tasks, TaskMatches work task)
    (available : List (Occurrence × Nat) := [])
    : (queue.taskSuccess occurrence result available).1.RegisteredTasksMatch work := by
  let settleStep (current : State) (group : Execution.DeliveryNode) : State :=
    match current.groupNode? group.ref with
    | none => current
    | some node => current.putGroupNode { node with pending := node.pending - 1 }
  have settleMatch (current : State) (group : Execution.DeliveryNode)
      (currentMatch : current.RegisteredTasksMatch work)
      : (settleStep current group).RegisteredTasksMatch work := by
    unfold settleStep
    split
    · exact currentMatch
    · exact currentMatch.putGroupNode _
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
  have releaseMatch (acc : State × List WorkQueueEvent × NewWork)
      (group : Execution.DeliveryNode) (currentMatch : acc.1.RegisteredTasksMatch work)
      : (releaseStep acc group).1.RegisteredTasksMatch work := by
    obtain ⟨current, events, released⟩ := acc
    dsimp only [releaseStep]
    split
    · exact currentMatch
    · rename_i node found
      have decremented : (current.putGroupNode
          { node with pending := node.pending - 1 }).RegisteredTasksMatch work := by
        simpa only [settleStep, found] using settleMatch current group currentMatch
      split
      · exact decremented.finishGroupSuccess _
      · exact decremented
  have releaseFold (groups : List Execution.DeliveryNode) :
      ∀ acc : State × List WorkQueueEvent × NewWork,
        acc.1.RegisteredTasksMatch work
          → (groups.foldl releaseStep acc).1.RegisteredTasksMatch work := by
    induction groups with
    | nil => intro acc currentMatch; exact currentMatch
    | cons group rest ih =>
        intro acc currentMatch
        exact ih (releaseStep acc group) (releaseMatch acc group currentMatch)
  unfold State.taskSuccess
  split
  · exact matching
  · rename_i taskNode found
    let withValue := queue.putTaskNode { taskNode with value := some result.value }
    have withValueMatch : withValue.RegisteredTasksMatch work := matching
    let integrated := (withValue.maybeIntegrateWork result.work (some occurrence)).1
    have integratedMatch : integrated.RegisteredTasksMatch work :=
      withValueMatch.maybeIntegrateWork result.work childTasks (some occurrence)
    let finished := taskNode.task.groups.foldl releaseStep (integrated, [], {})
    have finishedMatch : finished.1.RegisteredTasksMatch work :=
      releaseFold taskNode.task.groups (integrated, [], {}) integratedMatch
    change ((finished.1.startNewWork finished.2.2 available).1.drainReadyGroups
      available).1.RegisteredTasksMatch work
    exact (finishedMatch.startNewWork finished.2.2 available).drainReadyGroups available

/-- One stream batch integrates only the child task definitions supplied by its
items; each item may reveal work independently of the others.
-/
theorem State.RegisteredTasksMatch.streamItems
    {queue : State} {work : Execution.Work}
    (matching : queue.RegisteredTasksMatch work)
    (stream : Execution.DeliveryNode) (items : List StreamItem)
    (childTasks : ∀ item ∈ items, ∀ task ∈ item.work.tasks, TaskMatches work task)
    (available : List (Occurrence × Nat) := [])
    : (queue.streamItems stream items available).1.RegisteredTasksMatch work := by
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
  have stepMatch (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue × List GroupFailureEvent)
      (item : StreamItem) (itemMember : item ∈ items)
      (currentMatch : acc.1.RegisteredTasksMatch work)
      : (step acc item).1.RegisteredTasksMatch work := by
    obtain ⟨current, groups, streams, values, failures⟩ := acc
    let integrated := current.maybeIntegrateWork item.work
    have integratedMatch : integrated.1.RegisteredTasksMatch work :=
      currentMatch.maybeIntegrateWork item.work (childTasks item itemMember)
    let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
    have prunedMatch : pruned.1.RegisteredTasksMatch work :=
      integratedMatch.pruneEmptyGroups integrated.2.newGroups
    exact prunedMatch.startNewWork { integrated.2 with newGroups := pruned.2 } available
  have foldMatch (more : List StreamItem) (sublist : ∀ item ∈ more, item ∈ items) :
      ∀ acc : State × List Execution.DeliveryNode
        × List Execution.DeliveryNode × List StreamItemValue × List GroupFailureEvent,
        acc.1.RegisteredTasksMatch work
          → (more.foldl step acc).1.RegisteredTasksMatch work := by
    induction more with
    | nil => intro acc currentMatch; exact currentMatch
    | cons item rest ih =>
        intro acc currentMatch
        have headMember : item ∈ items := sublist item (by simp)
        have tailMember : ∀ item ∈ rest, item ∈ items := by
          intro candidate member
          exact sublist candidate (by simp [member])
        exact ih tailMember (step acc item)
          (stepMatch acc item headMember currentMatch)
  dsimp only [State.streamItems]
  split
  · exact matching
  · exact (foldMatch items (fun _ member => member) (queue, [], [], [], [])
      matching).drainReadyGroups available

/-- Stream closure, successful or failed, cannot register tasks. -/
theorem State.RegisteredTasksMatch.streamSuccess
    {queue : State} {work : Execution.Work}
    (matching : queue.RegisteredTasksMatch work) (stream : Execution.DeliveryNode)
    : (queue.streamSuccess stream).1.RegisteredTasksMatch work := by
  unfold State.streamSuccess
  split <;> exact matching

theorem State.RegisteredTasksMatch.streamFailure
    {queue : State} {work : Execution.Work}
    (matching : queue.RegisteredTasksMatch work) (stream : Execution.DeliveryNode)
    (errors : Nat)
    : (queue.streamFailure stream errors).1.RegisteredTasksMatch work := by
  unfold State.streamFailure
  split <;> exact matching

/-- Exact host-outcome matching supplies the child-task provenance premises
needed by the executable queue handlers.
-/
theorem State.RegisteredTasksMatch.handleGraphEvent
    {queue : State} {work : Execution.Work}
    (registered : queue.RegisteredTasksMatch work)
    (event : GraphEvent) (matching : event.MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : (queue.handleGraphEvent event available).1.RegisteredTasksMatch work := by
  have cached := registered.cacheTaskFailures available
  cases event with
  | taskSuccess occurrence result =>
      apply cached.taskSuccess occurrence result (available := available)
      intro task member
      obtain ⟨address, payload, occurrenceEq, known⟩ :=
        matching.childTask_producer member
      exact ⟨⟨address, payload, some occurrence, occurrenceEq, known⟩,
        matching.childTask_groupsExact member⟩
  | groupFailure failure =>
      change ((queue.cacheTaskFailures available).groupFailure failure).1.RegisteredTasksMatch work
      unfold State.groupFailure
      split
      · exact cached
      · split <;> exact cached
  | taskFailure occurrence errors => exact cached.taskFailure occurrence errors
  | streamItems stream items =>
      apply cached.streamItems stream items (available := available)
      intro item itemMember task taskMember
      obtain ⟨address, payload, occurrenceEq, known⟩ :=
        matching.streamItem_childTask_producer itemMember taskMember
      exact ⟨⟨address, payload, some item.occurrence, occurrenceEq, known⟩,
        matching.streamItem_childTask_groupsExact itemMember taskMember⟩
  | streamSuccess stream => exact cached.streamSuccess stream
  | streamFailure stream errors => exact cached.streamFailure stream errors

/-- Every event in a valid graph-event prefix has the required fixed-outcome
match, including events that occurred before the latest append.
-/
theorem ValidGraphEvents.eachMatches
    {work : Execution.Work} {events : List GraphEvent}
    (valid : ValidGraphEvents work events)
    {event : GraphEvent} (member : event ∈ events)
    : event.MatchesWork work := by
  induction valid with
  | nil => cases member
  | @append before latest _ latestMatch _ _ ih =>
      rcases List.mem_append.mp member with earlier | newest
      · exact ih earlier
      · simp only [List.mem_singleton] at newest
        subst event
        exact latestMatch

/-- A host batch preserves registered task provenance when every one of its
events matches the original Work tree.
-/
theorem State.RegisteredTasksMatch.handleGraphEvents
    {queue : State} {work : Execution.Work}
    (registered : queue.RegisteredTasksMatch work)
    (batch : List GraphEvent)
    (allMatch : ∀ event ∈ batch, event.MatchesWork work)
    : (queue.handleGraphEvents batch).1.RegisteredTasksMatch work := by
  let available := GraphEvent.availableFailures batch
  let step (acc : State × List WorkQueueEvent) (event : GraphEvent) :=
    let (next, produced) := acc.1.dispatchGraphEvent event available
    (next, acc.2 ++ produced)
  have foldMatch (events : List GraphEvent)
      (subset : ∀ event ∈ events, event ∈ batch) :
      ∀ acc : State × List WorkQueueEvent,
        acc.1.RegisteredTasksMatch work
          → (events.foldl step acc).1.RegisteredTasksMatch work := by
    induction events with
    | nil => intro acc currentMatch; exact currentMatch
    | cons event rest ih =>
        intro acc currentMatch
        have eventMatch : event.MatchesWork work := allMatch event (subset event (by simp))
        have restSubset : ∀ member ∈ rest, member ∈ batch := by
          intro member memberRest
          exact subset member (by simp [memberRest])
        have nextMatch : (step acc event).1.RegisteredTasksMatch work :=
          currentMatch.handleGraphEvent event eventMatch available
        exact ih restSubset (step acc event) nextMatch
  unfold State.handleGraphEvents
  split
  · exact registered
  · dsimp only
    split <;> exact foldMatch batch (fun _ member => member) (queue, []) registered

/-- Publisher normalization never changes the queue's registered task set.
Provenance therefore survives every finite sequence of matching host batches.
-/
private theorem State.runNormalized_registeredTasksMatch
    {queue : State} {work : Execution.Work}
    (registered : queue.RegisteredTasksMatch work)
    (batches : List (List GraphEvent))
    (allMatch : ∀ batch ∈ batches, ∀ event ∈ batch, event.MatchesWork work)
    : (queue.runNormalized batches).1.RegisteredTasksMatch work := by
  have stepMatch (acc : NormalizedAcc) (batch : List GraphEvent)
      (batchMatch : ∀ event ∈ batch, event.MatchesWork work)
      (currentMatch : acc.1.RegisteredTasksMatch work)
      : (normalizedStep acc batch).1.RegisteredTasksMatch work := by
    obtain ⟨current, publisher, outputs⟩ := acc
    unfold normalizedStep
    cases outcome : current.handleGraphEvents batch with
    | mk next raw =>
        have nextMatch : next.RegisteredTasksMatch work := by
          have handled := currentMatch.handleGraphEvents batch batchMatch
          rw [outcome] at handled
          exact handled
        dsimp only
        simp only [outcome]
        split <;> exact nextMatch
  have foldMatch (more : List (List GraphEvent))
      (subset : ∀ batch ∈ more, batch ∈ batches) :
      ∀ acc : NormalizedAcc, acc.1.RegisteredTasksMatch work
        → (more.foldl normalizedStep acc).1.RegisteredTasksMatch work := by
    induction more with
    | nil => intro acc currentMatch; exact currentMatch
    | cons batch rest ih =>
        intro acc currentMatch
        have batchMatch := allMatch batch (subset batch (by simp))
        have restSubset : ∀ candidate ∈ rest, candidate ∈ batches := by
          intro candidate member
          exact subset candidate (by simp [member])
        exact ih restSubset (normalizedStep acc batch)
          (stepMatch acc batch batchMatch currentMatch)
  let publisher : IncrementalPublisher :=
    { active := queue.initialGroups ++ queue.initialStreams }
  change (batches.foldl normalizedStep
    (queue, publisher, [])).1.RegisteredTasksMatch work
  exact foldMatch batches (fun _ member => member) (queue, publisher, []) registered

/-- An admitted host replay keeps every registered task structurally matched
to the execution-generated Work, including tasks revealed by stream items.
-/
theorem createWorkQueue_runNormalized_registeredTasksMatch
    {work : Execution.Work} {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten)
    : ((State.initialize (Work.fromExecution work)).runNormalized
        batches).1.RegisteredTasksMatch
        work := by
  apply State.runNormalized_registeredTasksMatch
    (createWorkQueue_fromSpec_registeredTasksMatch work) batches
  intro batch batchMember event eventMember
  exact valid.eachMatches (List.mem_flatten.mpr
    ⟨batch, batchMember, eventMember⟩)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
