import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupProvenance
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupRemoval
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.HealthyRegistration

/-! Canonical child links, ancestor order, and failure bookkeeping. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (
  ExecutionGroupValue StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- In generated Work, every live child link points to a strictly newer
delivery ref. This rules out cycles in the executable queue's child links. -/
private theorem State.ChildLinksCanonical.childRefGreater
    {queue : State} {work : Execution.Work} {parents : Nat → NodeRefs}
    (generated : ExecutedWork work)
    (links : queue.ChildLinksCanonical parents)
    (matching : queue.GroupNodesMatchWork work)
    (workCanonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    {parent child : GroupNode}
    (parentMember : parent ∈ queue.groupNodes)
    (childMember : child ∈ queue.groupNodes)
    (linked : child.group.node.ref ∈ parent.childGroups)
    : parent.group.node.ref < child.group.node.ref := by
  obtain ⟨dependencies, known⟩ := matching child childMember
  have head : dependencies.head? = some parent.group.node.ref := by
    rw [workCanonical child.group.node dependencies known]
    exact links parent parentMember child.group.node.ref linked
  cases dependencies with
  | nil => simp at head
  | cons first rest =>
      simp only [List.head?_cons] at head
      have firstEq : first = parent.group.node.ref := Option.some.inj head
      subst first
      exact generated.groupRecordAncestorSmaller known (by simp)

/-- Replacing a group node preserves child-edge coherence when the replacement
retains coherent links. -/
theorem State.ChildLinksCanonical.putGroupNode
    {queue : State} {parents : Nat → NodeRefs}
    (links : queue.ChildLinksCanonical parents) (updated : GroupNode)
    (updatedLinks
      : ∀ child ∈ updated.childGroups,
          (parents child).head? = some updated.group.node.ref)
    : (queue.putGroupNode updated).ChildLinksCanonical parents := by
  intro node member child childMember
  change node ∈ queue.groupNodes.map
    (fun old => if old.group.node.ref == updated.group.node.ref then updated else old)
    at member
  obtain ⟨old, oldMember, same⟩ := List.mem_map.mp member
  split at same
  · subst node
    exact updatedLinks child childMember
  · subst node
    exact links old oldMember child childMember

/-- Installing a group immediately attaches its canonical parent link. -/
theorem State.ChildLinksCanonical.addGroup
    {queue : State} {parents : Nat → NodeRefs}
    (links : queue.ChildLinksCanonical parents) (group : Group)
    (groupCanonical : group.parent = (parents group.node.ref).head?)
    : (queue.addGroup group).ChildLinksCanonical parents := by
  have appended : ({ queue with
      groupNodes := queue.groupNodes ++ [({ group } : GroupNode)] } : State).ChildLinksCanonical parents := by
    intro node member child childMember
    rcases List.mem_append.mp member with old | added
    · exact links node old child childMember
    · cases List.mem_singleton.mp added
      cases childMember
  unfold State.addGroup
  split
  · exact links
  · split
    · exact appended
    · rename_i parent parentEq
      split
      · split <;> exact links
      · rename_i node found
        apply appended.putGroupNode
        intro child childMember
        split at childMember
        · exact links node (List.mem_of_find?_eq_some found) child childMember
        · rcases List.mem_append.mp childMember with old | fresh
          · exact links node (List.mem_of_find?_eq_some found) child old
          · cases List.mem_singleton.mp fresh
            rw [← groupCanonical]
            simpa [State.groupNode?_ref found] using parentEq

/-- Recursive installation adds only each descriptor's canonical parent link. -/
theorem State.ChildLinksCanonical.addGroups
    {queue : State} {parents : Nat → NodeRefs}
    (links : queue.ChildLinksCanonical parents) (groups : List Group)
    (all : ∀ group ∈ groups, group.parent = (parents group.node.ref).head?)
    : (queue.addGroups groups).1.ChildLinksCanonical parents := by
  exact State.addGroups_preserves (fun current => current.ChildLinksCanonical parents) groups
    (fun _ group member valid => valid.addGroup group (all group member)) queue links

/-- Adding a task updates group memberships and counters, but no child edge. -/
theorem State.ChildLinksCanonical.addTask
    {queue : State} {parents : Nat → NodeRefs}
    (links : queue.ChildLinksCanonical parents) (task : Task)
    : (queue.addTask task).ChildLinksCanonical parents := by
  let registered : State := { queue with tasks := queue.tasks ++ [task] }
  let step (current : State) (group : Execution.DeliveryNode) : State :=
    match current.groupNode? group.ref with
    | none => current
    | some node =>
        if node.tasks.contains task.occurrence then current
        else current.putGroupNode
          { node with tasks := node.tasks ++ [task.occurrence], pending := node.pending + 1 }
  have stepLinks (current : State) (group : Execution.DeliveryNode)
      (currentLinks : current.ChildLinksCanonical parents)
      : (step current group).ChildLinksCanonical parents := by
    unfold step
    split
    · exact currentLinks
    · rename_i node found
      split
      · exact currentLinks
      · exact currentLinks.putGroupNode _
          (currentLinks node (List.mem_of_find?_eq_some found))
  have foldLinks (more : List Execution.DeliveryNode) :
      ∀ current, current.ChildLinksCanonical parents
        → (more.foldl step current).ChildLinksCanonical parents := by
    induction more with
    | nil => intro current currentLinks; exact currentLinks
    | cons group rest ih =>
        intro current currentLinks
        exact ih (step current group) (stepLinks current group currentLinks)
  let current := task.groups.foldl step registered
  have currentLinks : current.ChildLinksCanonical parents :=
    foldLinks task.groups registered links
  change (if task.groups.any (fun group => current.rootGroups.contains group.ref)
      && (current.taskNode? task.occurrence).isNone then
    { current with taskNodes := current.taskNodes ++ [{ task }] }
    else current).ChildLinksCanonical parents
  split <;> exact currentLinks

/-- Stream registration changes no group child links. -/
theorem State.ChildLinksCanonical.addStreams
    {queue : State} {parents : Nat → NodeRefs}
    (links : queue.ChildLinksCanonical parents)
    (streams : List Stream) (parentTask : Option Occurrence)
    : (queue.addStreams streams parentTask).1.ChildLinksCanonical parents := by
  unfold State.addStreams
  split
  · exact links
  · dsimp
    split <;> exact links

/-- Integrating new Work preserves child-edge coherence if each new group
has the primary parent assigned by execution. -/
theorem State.ChildLinksCanonical.maybeIntegrateWork
    {queue : State} {parents : Nat → NodeRefs}
    (links : queue.ChildLinksCanonical parents) (work : Work)
    (groupsCanonical
      : ∀ group ∈ work.groups, group.parent = (parents group.node.ref).head?)
    (parentTask : Option Occurrence := none)
    : (queue.maybeIntegrateWork work parentTask).1.ChildLinksCanonical parents := by
  let withGroups := (queue.addGroups work.groups).1
  let withTasks := work.tasks.foldl State.addTask withGroups
  have groupLinks : withGroups.ChildLinksCanonical parents :=
    links.addGroups work.groups groupsCanonical
  have taskFold (more : List Task) :
      ∀ current, current.ChildLinksCanonical parents
        → (more.foldl State.addTask current).ChildLinksCanonical parents := by
    induction more with
    | nil => intro current currentLinks; exact currentLinks
    | cons task rest ih =>
        intro current currentLinks
        exact ih (current.addTask task) (currentLinks.addTask task)
  have taskLinks : withTasks.ChildLinksCanonical parents :=
    taskFold work.tasks withGroups groupLinks
  change (withTasks.addStreams work.streams parentTask).1.ChildLinksCanonical parents
  exact taskLinks.addStreams work.streams parentTask

/-- Pruning removes group nodes but never changes links on survivors. -/
theorem State.ChildLinksCanonical.pruneEmptyGroups
    {queue : State} {parents : Nat → NodeRefs}
    (links : queue.ChildLinksCanonical parents)
    (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.ChildLinksCanonical parents := by
  have loop (fuel : Nat) (current : State)
      (remaining kept : List Execution.DeliveryNode)
      (currentLinks : current.ChildLinksCanonical parents)
      : (State.pruneEmptyGroups.go fuel current remaining kept).1.ChildLinksCanonical
          parents := by
    induction fuel generalizing current remaining kept with
    | zero => exact currentLinks
    | succ fuel ih =>
        cases remaining with
        | nil => exact currentLinks
        | cons group rest =>
            unfold State.pruneEmptyGroups.go
            split
            · exact ih _ _ _ currentLinks
            · split
              · apply ih
                intro node member child childMember
                exact currentLinks node (List.mem_filter.mp member).1
                  child childMember
              · exact ih _ _ _ currentLinks
  exact loop _ queue groups [] links

/-- Cache exposure preserves all stored group metadata. -/
theorem State.ChildLinksCanonical.cacheTaskFailures
    {queue : State} {parents : Nat → NodeRefs}
    (links : queue.ChildLinksCanonical parents) (available : List (Occurrence × Nat))
    : (queue.cacheTaskFailures available).ChildLinksCanonical parents := by
  intro node member child childMember
  rw [State.cacheTaskFailures_groupNodes] at member
  exact links node member child childMember

/-- Startup preserves canonical metadata on each surviving group record. -/
theorem State.ChildLinksCanonical.startNewWork
    {queue : State} {parents : Nat → NodeRefs}
    (links : queue.ChildLinksCanonical parents) (newWork : NewWork)
    (available : List (Occurrence × Nat) := [])
    : (queue.startNewWork newWork available).1.ChildLinksCanonical parents := by
  intro node member child childMember
  exact links node ((queue.startNewWork_groupNodes_sublist newWork available).subset member)
    child childMember

/-- Removing a group preserves all edges on remaining nodes. -/
theorem State.ChildLinksCanonical.removeGroup
    {queue : State} {parents : Nat → NodeRefs}
    (links : queue.ChildLinksCanonical parents) (ref : NodeRef)
    : (queue.removeGroup ref).ChildLinksCanonical parents := by
  intro node member child childMember
  unfold State.removeGroup at member
  exact links node (List.mem_filter.mp member).1 child childMember

/-- Removing a task changes memberships, not child edges. -/
theorem State.ChildLinksCanonical.removeTask
    {queue : State} {parents : Nat → NodeRefs}
    (links : queue.ChildLinksCanonical parents) (occurrence : Occurrence)
    : (queue.removeTask occurrence).ChildLinksCanonical parents := by
  intro node member child childMember
  change node ∈ queue.groupNodes.map
    (fun old => { old with tasks := old.tasks.filter (· != occurrence) }) at member
  obtain ⟨old, oldMember, same⟩ := List.mem_map.mp member
  subst node
  exact links old oldMember child childMember

/-- Once a structurally matched failed task's contributors are invalidated, failure
cleanup preserves healthy registration. Witness: failed-membership removal, healthy
subtree retention, and cache updates restricted to invalidated refs.
-/
theorem State.HealthyRegisteredTaskAccounting.taskFailure
    {queue : State} {work : Execution.Work} {parents : Nat → NodeRefs}
    {settled failed : List Occurrence}
    (accounted : queue.HealthyRegisteredTaskAccounting work settled failed)
    (taskMatching : queue.RegisteredTasksMatch work)
    (generated : ExecutedWork work)
    (links : queue.ChildLinksCanonical parents)
    (matching : queue.GroupNodesMatchWork work)
    (workCanonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (occurrence : Occurrence) (errors : Nat)
    (taskNode : TaskNode) (found : queue.taskNode? occurrence = some taskNode)
    (failedOwners
      : ∀ group ∈ taskNode.task.groups,
          GroupInvalidated work (occurrence :: failed) group.ref)
    : (queue.taskFailure occurrence errors).1.HealthyRegisteredTaskAccounting
        work settled (occurrence :: failed) := by
  let invariant (current : State) :=
    current.HealthyRegisteredTaskAccounting work settled (occurrence :: failed)
      ∧ current.ChildLinksCanonical parents
      ∧ current.GroupNodesMatchWork work ∧ current.RegisteredTasksMatch work
  rw [queue.taskFailure_eq occurrence errors taskNode found]
  have final := failureGroupFold_preserves_on invariant
    (GroupInvalidated work (occurrence :: failed))
    (fun current ref prior invalidated =>
      ⟨prior.1.removeInvalidatedGroup prior.2.2.2 generated prior.2.1 prior.2.2.1
        workCanonical ref invalidated.toRecordInvalidated,
        prior.2.1.removeGroup ref, prior.2.2.1.removeGroup ref, prior.2.2.2.removeGroup ref⟩)
    errors taskNode.task.groups failedOwners
    (queue.putTaskNode { taskNode with rejection := some errors }, [])
    ⟨accounted.weakenFailures (by intro task member; simp [member]), links, matching,
      taskMatching⟩
  exact final.1

/-- A failed registered task invalidates every one of its contributor
groups. This discharges the local premise of the removal proof. -/
private theorem State.registeredTaskFailure_failsOwners
    {queue : State} {work : Execution.Work}
    (registered : queue.StartedTasksRegistered)
    (matching : queue.RegisteredTasksMatch work)
    {occurrence : Occurrence} {taskNode : TaskNode}
    (found : queue.taskNode? occurrence = some taskNode)
    (failed : List Occurrence)
    : ∀ group ∈ taskNode.task.groups,
        GroupInvalidated work (occurrence :: failed) group.ref := by
  have taskMember : taskNode.task ∈ queue.tasks :=
    registered taskNode (List.mem_of_find?_eq_some found)
  obtain ⟨⟨_, payload, producer, _, taskAt⟩, _⟩ := matching taskNode.task taskMember
  have occurrenceEq : taskNode.task.occurrence = occurrence := by
    have selected := List.find?_some
      (p := fun candidate : TaskNode => candidate.task.occurrence == occurrence)
      (by simpa [State.taskNode?] using found)
    exact (occurrence_beq_iff_eq _ _).mp selected
  intro group groupMember
  have owners : TaskHasOwners work taskNode.task.occurrence
      (taskNode.task.groups.map Execution.DeliveryNode.ref) :=
    ⟨producer, payload, taskAt⟩
  have owner : group.ref ∈ taskNode.task.groups.map Execution.DeliveryNode.ref :=
    List.mem_map.mpr ⟨group, groupMember, rfl⟩
  have failedMember : taskNode.task.occurrence ∈ occurrence :: failed := by
    simp [occurrenceEq]
  exact GroupInvalidated.task owners owner failedMember

/-- Registered task provenance and canonical child links make task-failure
preservation unconditional on any extra owner-failure assumption. -/
private theorem State.HealthyRegisteredTaskAccounting.taskFailure_registered
    {queue : State} {work : Execution.Work} {parents : Nat → NodeRefs}
    {settled failed : List Occurrence}
    (accounted : queue.HealthyRegisteredTaskAccounting work settled failed)
    (generated : ExecutedWork work)
    (links : queue.ChildLinksCanonical parents)
    (groupMatching : queue.GroupNodesMatchWork work)
    (workCanonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (registered : queue.StartedTasksRegistered)
    (taskMatching : queue.RegisteredTasksMatch work)
    (occurrence : Occurrence) (errors : Nat)
    (taskNode : TaskNode) (found : queue.taskNode? occurrence = some taskNode)
    : (queue.taskFailure occurrence errors).1.HealthyRegisteredTaskAccounting
        work settled (occurrence :: failed) := by
  exact accounted.taskFailure taskMatching generated links groupMatching workCanonical
    occurrence errors taskNode found
    (queue.registeredTaskFailure_failsOwners registered taskMatching found failed)

/-- Whether or not the task is still started, processing its failure retains
accounting for every registered task with a uninvalidated owner. -/
theorem State.HealthyRegisteredTaskAccounting.taskFailure_any
    {queue : State} {work : Execution.Work} {parents : Nat → NodeRefs}
    {settled failed : List Occurrence}
    (accounted : queue.HealthyRegisteredTaskAccounting work settled failed)
    (generated : ExecutedWork work)
    (links : queue.ChildLinksCanonical parents)
    (groupMatching : queue.GroupNodesMatchWork work)
    (workCanonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (registered : queue.StartedTasksRegistered)
    (taskMatching : queue.RegisteredTasksMatch work)
    (occurrence : Occurrence) (errors : Nat)
    : (queue.taskFailure occurrence errors).1.HealthyRegisteredTaskAccounting
        work settled (occurrence :: failed) := by
  cases found : queue.taskNode? occurrence with
  | none =>
      simp only [State.taskFailure, found]
      exact accounted.weakenFailures (by intro item member; simp [member])
  | some taskNode =>
      exact accounted.taskFailure_registered generated links groupMatching workCanonical
        registered taskMatching occurrence errors taskNode found

/-- Queue initialization preserves every parent-child edge created by the
initial Work lowering. -/
theorem createWorkQueue_childLinksCanonical
    (initialWork : Work) (parents : Nat → NodeRefs)
    (all : ∀ group ∈ initialWork.groups, group.parent = (parents group.node.ref).head?)
    : (State.initialize initialWork).ChildLinksCanonical parents := by
  let integrated := (({} : State).maybeIntegrateWork initialWork).1
  let newWork := (({} : State).maybeIntegrateWork initialWork).2
  let pruned := (integrated.pruneEmptyGroups newWork.newGroups).1
  let groups := (integrated.pruneEmptyGroups newWork.newGroups).2
  let roots := { newWork with newGroups := groups }
  let started := (pruned.startNewWork roots).1
  have emptyLinks : ({} : State).ChildLinksCanonical parents := by
    intro node member
    cases member
  have integratedLinks : integrated.ChildLinksCanonical parents :=
    emptyLinks.maybeIntegrateWork initialWork all
  have prunedLinks : pruned.ChildLinksCanonical parents :=
    integratedLinks.pruneEmptyGroups newWork.newGroups
  have startedLinks : started.ChildLinksCanonical parents :=
    prunedLinks.startNewWork roots
  change State.ChildLinksCanonical
    { started with initialGroups := groups, initialStreams := roots.newStreams }
      parents
  exact startedLinks

/-- Every generated root queue begins with primary-parent-correct child
links, even when a group ref has multiple execution occurrences. -/
private theorem ExecutedWork.initialQueueChildLinksCanonical
    {work : Execution.Work} (generated : ExecutedWork work)
    : ∃ parents : Nat → NodeRefs,
        (State.initialize (Work.fromExecution work)).ChildLinksCanonical parents := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  refine ⟨parents, createWorkQueue_childLinksCanonical
    (Work.fromExecution work) parents ?_⟩
  intro group member
  exact workFromSpec_groups_parentCanonical_root canonical member

/-- Flushing a group deletes task memberships and group nodes without
changing any child edge on a surviving node. -/
theorem State.ChildLinksCanonical.finishGroupSuccess
    {queue : State} {parents : Nat → NodeRefs}
    (links : queue.ChildLinksCanonical parents) (group : GroupNode)
    : (queue.finishGroupSuccess group).1.ChildLinksCanonical parents := by
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
  have stepLinks (acc : State × List ExecutionGroupValue × NodeRefs)
      (occurrence : Occurrence)
      (currentLinks : acc.1.ChildLinksCanonical parents)
      : (step acc occurrence).1.ChildLinksCanonical parents := by
    obtain ⟨current, values, streams⟩ := acc
    dsimp only [step]
    split
    · exact currentLinks
    · exact currentLinks.removeTask occurrence
  have foldLinks (tasks : List Occurrence) :
      ∀ acc : State × List ExecutionGroupValue × NodeRefs,
        acc.1.ChildLinksCanonical parents
          → (tasks.foldl step acc).1.ChildLinksCanonical parents := by
    induction tasks with
    | nil => intro acc currentLinks; exact currentLinks
    | cons occurrence rest ih =>
        intro acc currentLinks
        exact ih (step acc occurrence) (stepLinks acc occurrence currentLinks)
  let flushed := (group.tasks.foldl step (queue, [], [])).1
  have flushedLinks : flushed.ChildLinksCanonical parents :=
    foldLinks group.tasks (queue, [], []) links
  let current : State :=
    { flushed with
        groupNodes := flushed.groupNodes.filter
          (fun node => node.group.node.ref != group.group.node.ref)
        rootGroups := flushed.rootGroups.filter (· != group.group.node.ref) }
  have currentLinks : current.ChildLinksCanonical parents := by
    intro node member child childMember
    exact flushedLinks node (List.mem_filter.mp member).1 child childMember
  let children := group.childGroups.filterMap
    (fun ref => (current.groupNode? ref).map (fun node => node.group.node))
  change (current.pruneEmptyGroups children).1.ChildLinksCanonical parents
  exact currentLinks.pruneEmptyGroups children

/-- Failure closure only deletes group nodes. -/
theorem State.ChildLinksCanonical.finishGroupFailure
    {queue : State} {parents : Nat → NodeRefs}
    (links : queue.ChildLinksCanonical parents)
    (group : GroupNode) (errors : Nat)
    : (queue.finishGroupFailure group errors).1.ChildLinksCanonical parents := by
  unfold State.finishGroupFailure
  exact links.removeGroup group.group.node.ref

/-- Retained rejection and active-owner removal preserve canonical child links. -/
theorem State.ChildLinksCanonical.taskFailure
    {queue : State} {parents : Nat → NodeRefs}
    (links : queue.ChildLinksCanonical parents)
    (occurrence : Occurrence) (errors : Nat)
    : (queue.taskFailure occurrence errors).1.ChildLinksCanonical parents := by
  cases found : queue.taskNode? occurrence with
  | none => simpa [State.taskFailure, found] using links
  | some node =>
      rw [queue.taskFailure_eq occurrence errors node found]
      exact failureGroupFold_preserves (fun state => state.ChildLinksCanonical parents)
        (fun _ ref prior => prior.removeGroup ref) _ _ _ links

/-- Recursive drain steps preserve canonical child edges, including cached failures.
Witness: the generic drain induction transports success, activation, and removal facts.
-/
theorem State.ChildLinksCanonical.drainReadyGroups
    {queue : State} {parents : Nat → NodeRefs} (links : queue.ChildLinksCanonical parents)
    (available : List (Occurrence × Nat) := [])
    : (queue.drainReadyGroups available).1.ChildLinksCanonical parents :=
  State.drainReadyGroups_preserves (fun state => state.ChildLinksCanonical parents)
    (fun _ node prior _ _ _ => (prior.finishGroupSuccess node).startNewWork _ available)
    links

/-- Successful task settlement maintains child-edge coherence through child
integration, co-owner settlement, and sequential group release. -/
theorem State.ChildLinksCanonical.taskSuccess
    {queue : State} {parents : Nat → NodeRefs}
    (links : queue.ChildLinksCanonical parents)
    (occurrence : Occurrence) (result : TaskResult)
    (childrenCanonical
      : ∀ group ∈ result.work.groups, group.parent = (parents group.node.ref).head?)
    (available : List (Occurrence × Nat) := [])
    : (queue.taskSuccess occurrence result available).1.ChildLinksCanonical parents := by
  let settleStep (current : State) (group : Execution.DeliveryNode) : State :=
    match current.groupNode? group.ref with
    | none => current
    | some node => current.putGroupNode { node with pending := node.pending - 1 }
  have settleLinks (current : State) (group : Execution.DeliveryNode)
      (currentLinks : current.ChildLinksCanonical parents)
      : (settleStep current group).ChildLinksCanonical parents := by
    unfold settleStep
    split
    · exact currentLinks
    · rename_i node found
      exact currentLinks.putGroupNode _
        (currentLinks node (List.mem_of_find?_eq_some found))
  let releaseStep (acc : State × List WorkQueueEvent × NewWork)
      (group : Execution.DeliveryNode) :=
    let (current, events, released) := acc
    match current.groupNode? group.ref with
    | none => (current, events, released)
    | some node =>
        let node := { node with pending := node.pending - 1 }
        let current := current.putGroupNode node
        if current.rootGroups.contains group.ref && node.pending == 0 then
          let (next, finished, newWork) := current.finishGroupSuccess node
          (next, events ++ finished,
            ⟨released.newGroups ++ newWork.newGroups,
              released.newStreams ++ newWork.newStreams⟩)
        else (current, events, released)
  have releaseLinks (acc : State × List WorkQueueEvent × NewWork)
      (group : Execution.DeliveryNode)
      (currentLinks : acc.1.ChildLinksCanonical parents)
      : (releaseStep acc group).1.ChildLinksCanonical parents := by
    obtain ⟨current, events, released⟩ := acc
    dsimp only [releaseStep]
    split
    · exact currentLinks
    · rename_i node found
      have decremented : (current.putGroupNode
          { node with pending := node.pending - 1 }).ChildLinksCanonical parents := by
        simpa only [settleStep, found] using settleLinks current group currentLinks
      split
      · exact decremented.finishGroupSuccess _
      · exact decremented
  have releaseFold (groups : List Execution.DeliveryNode) :
      ∀ acc : State × List WorkQueueEvent × NewWork,
        acc.1.ChildLinksCanonical parents
          → (groups.foldl releaseStep acc).1.ChildLinksCanonical parents := by
    induction groups with
    | nil => intro acc currentLinks; exact currentLinks
    | cons group rest ih =>
        intro acc currentLinks
        exact ih (releaseStep acc group) (releaseLinks acc group currentLinks)
  unfold State.taskSuccess
  split
  · exact links
  · rename_i taskNode found
    let withValue := queue.putTaskNode { taskNode with value := some result.value }
    have withValueLinks : withValue.ChildLinksCanonical parents := links
    let integrated := (withValue.maybeIntegrateWork result.work (some occurrence)).1
    have integratedLinks : integrated.ChildLinksCanonical parents :=
      withValueLinks.maybeIntegrateWork result.work childrenCanonical
        (some occurrence)
    let released := taskNode.task.groups.foldl releaseStep (integrated, [], {})
    have releasedLinks : released.1.ChildLinksCanonical parents :=
      releaseFold taskNode.task.groups (integrated, [], {}) integratedLinks
    change ((released.1.startNewWork released.2.2 available).1.drainReadyGroups
      available).1.ChildLinksCanonical parents
    exact (releasedLinks.startNewWork released.2.2 available).drainReadyGroups available

/-- Each published stream item integrates canonically parented child work;
the batch fold therefore retains coherent child edges. -/
theorem State.ChildLinksCanonical.streamItems
    {queue : State} {parents : Nat → NodeRefs}
    (links : queue.ChildLinksCanonical parents)
    (stream : Execution.DeliveryNode) (items : List StreamItem)
    (childrenCanonical
      : ∀ item ∈ items,
        ∀ group ∈ item.work.groups, group.parent = (parents group.node.ref).head?)
    (available : List (Occurrence × Nat) := [])
    : (queue.streamItems stream items available).1.ChildLinksCanonical parents := by
  let step (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue × List GroupFailureEvent)
      (item : StreamItem) :=
    let (current, groups, streams, values, failures) := acc
    let (integrated, newWork) := current.maybeIntegrateWork item.work
    let (pruned, nonempty) := integrated.pruneEmptyGroups newWork.newGroups
    let (started, queued) := pruned.startNewWork { newWork with newGroups := nonempty } available
    (started, groups ++ nonempty, streams ++ newWork.newStreams,
      values ++ [item.value], failures ++ queued)
  have stepLinks (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue × List GroupFailureEvent)
      (item : StreamItem) (currentLinks : acc.1.ChildLinksCanonical parents)
      (itemMember : item ∈ items)
      : (step acc item).1.ChildLinksCanonical parents := by
    obtain ⟨current, groups, streams, values, failures⟩ := acc
    let integrated := current.maybeIntegrateWork item.work
    have integratedLinks : integrated.1.ChildLinksCanonical parents :=
      currentLinks.maybeIntegrateWork item.work
        (childrenCanonical item itemMember)
    let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
    have prunedLinks : pruned.1.ChildLinksCanonical parents :=
      integratedLinks.pruneEmptyGroups integrated.2.newGroups
    exact prunedLinks.startNewWork
      { integrated.2 with newGroups := pruned.2 } available
  have foldLinks (more : List StreamItem)
      (subset : ∀ item ∈ more, item ∈ items) :
      ∀ acc : State × List Execution.DeliveryNode
        × List Execution.DeliveryNode × List StreamItemValue × List GroupFailureEvent,
        acc.1.ChildLinksCanonical parents
          → (more.foldl step acc).1.ChildLinksCanonical parents := by
    induction more with
    | nil => intro acc currentLinks; exact currentLinks
    | cons item rest ih =>
        intro acc currentLinks
        have itemMember : item ∈ items := subset item (by simp)
        have restSubset : ∀ next ∈ rest, next ∈ items := by
          intro next nextMember
          exact subset next (by simp [nextMember])
        exact ih restSubset (step acc item)
          (stepLinks acc item currentLinks itemMember)
  unfold State.streamItems
  split
  · exact links
  · exact (foldLinks items (by intro item member; exact member)
      (queue, [], [], [], []) links).drainReadyGroups available

/-- Stream closure only removes the stream root, not group links. -/
theorem State.ChildLinksCanonical.streamSuccess
    {queue : State} {parents : Nat → NodeRefs}
    (links : queue.ChildLinksCanonical parents)
    (stream : Execution.DeliveryNode)
    : (queue.streamSuccess stream).1.ChildLinksCanonical parents := by
  unfold State.streamSuccess
  split <;> exact links

/-- Stream failure also leaves group links unchanged. -/
theorem State.ChildLinksCanonical.streamFailure
    {queue : State} {parents : Nat → NodeRefs}
    (links : queue.ChildLinksCanonical parents)
    (stream : Execution.DeliveryNode) (errors : Nat)
    : (queue.streamFailure stream errors).1.ChildLinksCanonical parents := by
  unfold State.streamFailure
  split <;> exact links

/-- A host event matching generated Work preserves coherent group child
edges, including edges created by newly revealed child Work. -/
theorem State.ChildLinksCanonical.handleGraphEvent
    {queue : State} {work : Execution.Work} {parents : Nat → NodeRefs}
    (links : queue.ChildLinksCanonical parents)
    (event : GraphEvent) (matching : event.MatchesWork work)
    (workCanonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (available : List (Occurrence × Nat) := [])
    : (queue.handleGraphEvent event available).1.ChildLinksCanonical parents := by
  have cached := links.cacheTaskFailures available
  cases event with
  | taskSuccess occurrence result =>
      exact cached.taskSuccess occurrence result
        (fun group member =>
          matching.taskChildGroups_parentCanonical workCanonical member) available
  | taskFailure occurrence errors => exact cached.taskFailure occurrence errors
  | groupFailure failure =>
      change ((queue.cacheTaskFailures available).groupFailure failure).1.ChildLinksCanonical parents
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

/-- The event-batch fold preserves coherent child links. -/
theorem State.ChildLinksCanonical.handleGraphEvents
    {queue : State} {work : Execution.Work} {parents : Nat → NodeRefs}
    (links : queue.ChildLinksCanonical parents)
    (batch : List GraphEvent)
    (allMatch : ∀ event ∈ batch, event.MatchesWork work)
    (workCanonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    : (queue.handleGraphEvents batch).1.ChildLinksCanonical parents := by
  let available := GraphEvent.availableFailures batch
  let step (acc : State × List WorkQueueEvent) (event : GraphEvent) :=
    let (next, produced) := acc.1.dispatchGraphEvent event available
    (next, acc.2 ++ produced)
  have foldLinks (events : List GraphEvent)
      (subset : ∀ event ∈ events, event ∈ batch) :
      ∀ acc : State × List WorkQueueEvent,
        acc.1.ChildLinksCanonical parents
          → (events.foldl step acc).1.ChildLinksCanonical parents := by
    induction events with
    | nil => intro acc currentLinks; exact currentLinks
    | cons event rest ih =>
        intro acc currentLinks
        have eventMatch : event.MatchesWork work := allMatch event (subset event (by simp))
        have restSubset : ∀ member ∈ rest, member ∈ batch := by
          intro member memberRest
          exact subset member (by simp [memberRest])
        obtain ⟨current, outputs⟩ := acc
        have nextLinks : (step (current, outputs) event).1.ChildLinksCanonical
            parents := currentLinks.handleGraphEvent event eventMatch workCanonical available
        exact ih restSubset (step (current, outputs) event) nextLinks
  unfold State.handleGraphEvents
  split
  · exact links
  · let folded := batch.foldl step (queue, [])
    have final : folded.1.ChildLinksCanonical parents :=
      foldLinks batch (fun _ member => member) (queue, []) links
    cases folded with
    | mk current outputs =>
        dsimp only at final ⊢
        split <;> exact final

/-- All finite matched-input replays preserve coherent child edges. -/
theorem State.ChildLinksCanonical.runNormalized
    {queue : State} {work : Execution.Work} {parents : Nat → NodeRefs}
    (links : queue.ChildLinksCanonical parents)
    (batches : List (List GraphEvent))
    (allMatch : ∀ batch ∈ batches, ∀ event ∈ batch, event.MatchesWork work)
    (workCanonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    : (queue.runNormalized batches).1.ChildLinksCanonical parents := by
  have stepLinks (acc : NormalizedAcc) (batch : List GraphEvent)
      (currentLinks : acc.1.ChildLinksCanonical parents)
      (batchMatch : ∀ event ∈ batch, event.MatchesWork work)
      : (normalizedStep acc batch).1.ChildLinksCanonical parents := by
    obtain ⟨current, publisher, outputs⟩ := acc
    unfold normalizedStep
    cases outcome : current.handleGraphEvents batch with
    | mk next raw =>
        have nextLinks : next.ChildLinksCanonical parents := by
          have handled := currentLinks.handleGraphEvents batch batchMatch
            workCanonical
          rw [outcome] at handled
          exact handled
        dsimp only
        simp only [outcome]
        split <;> exact nextLinks
  have foldLinks (more : List (List GraphEvent))
      (subset : ∀ batch ∈ more, batch ∈ batches) :
      ∀ acc : NormalizedAcc,
        acc.1.ChildLinksCanonical parents
          → (more.foldl normalizedStep acc).1.ChildLinksCanonical parents := by
    induction more with
    | nil => intro acc currentLinks; exact currentLinks
    | cons batch rest ih =>
        intro acc currentLinks
        have batchMatch : ∀ event ∈ batch, event.MatchesWork work :=
          allMatch batch (subset batch (by simp))
        have restSubset : ∀ later ∈ rest, later ∈ batches := by
          intro later member
          exact subset later (by simp [member])
        exact ih restSubset (normalizedStep acc batch)
          (stepLinks acc batch currentLinks batchMatch)
  let publisher : IncrementalPublisher :=
    { active := queue.initialGroups ++ queue.initialStreams }
  change (batches.foldl normalizedStep (queue, publisher, [])).1.ChildLinksCanonical
    parents
  exact foldLinks batches (fun _ member => member)
    (queue, publisher, []) links

/-- A generated replay of valid source events preserves canonical primary-parent edges.
Witness: the generated parent assignment, initial lowering, and handler preservation.
-/
theorem ExecutedWork.runNormalized_childLinksCanonical
    {work : Execution.Work} (generated : ExecutedWork work)
    (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work batches.flatten)
    : ∃ parents : Nat → NodeRefs,
        (((State.initialize (Work.fromExecution work)).runNormalized
            batches).1).ChildLinksCanonical
          parents := by
  obtain ⟨parents, workCanonical⟩ := generated.groupRecordsCanonical
  refine ⟨parents, ?_⟩
  have initial : (State.initialize (Work.fromExecution work)).ChildLinksCanonical
      parents :=
    createWorkQueue_childLinksCanonical (Work.fromExecution work) parents
      (by
        intro group member
        exact workFromSpec_groups_parentCanonical_root workCanonical member)
  apply initial.runNormalized batches
  · intro batch batchMember event eventMember
    exact valid.eachMatches
      (List.mem_flatten.mpr ⟨batch, batchMember, eventMember⟩)
  · exact workCanonical

/-- Generated replay supplies the canonical metadata needed by failure cleanup.
Witness: generated dependency uniqueness, initial lowering, and matched-event replay
preserve both source descriptors and child edges with one common parent assignment.
No output-admission or started-input premise is used.
-/
theorem ExecutedWork.runNormalized_groupMetadata
    {work : Execution.Work} (generated : ExecutedWork work)
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    : ∃ parents : Nat → NodeRefs,
        (∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
        ∧ ((State.initialize (Work.fromExecution work)).runNormalized
            batches).1.ChildLinksCanonical
            parents
        ∧ ((State.initialize (Work.fromExecution work)).runNormalized
            batches).1.GroupNodesMatchWork
            work := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have initial := createWorkQueue_childLinksCanonical (Work.fromExecution work) parents
    (fun _ member => workFromSpec_groups_parentCanonical_root canonical member)
  refine ⟨parents, canonical, initial.runNormalized batches ?_ canonical,
    valid.runNormalized_groupNodesMatchWork⟩
  intro batch batchMember event eventMember
  exact valid.eachMatches (List.mem_flatten.mpr ⟨batch, batchMember, eventMember⟩)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
