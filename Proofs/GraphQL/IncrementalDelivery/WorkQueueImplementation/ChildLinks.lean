import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupProvenance
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupRemoval
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.HealthyRegistration

/-! Canonical child links, ancestor order, and failure bookkeeping. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (
  ExecutionGroupValue StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- In generated Work, every live child link points to a strictly newer
delivery key. This rules out cycles in the executable queue's child links. -/
private theorem State.ChildLinksCanonical.childKeyGreater
    {queue : State} {work : Execution.Work} {parents : Nat → Keys}
    (generated : ExecutedWork work)
    (links : queue.ChildLinksCanonical parents)
    (matching : queue.GroupNodesMatchWork work)
    (workCanonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    {parent child : GroupNode}
    (parentMember : parent ∈ queue.groupNodes)
    (childMember : child ∈ queue.groupNodes)
    (linked : child.group.node.key ∈ parent.childGroups)
    : parent.group.node.key < child.group.node.key := by
  obtain ⟨dependencies, known⟩ := matching child childMember
  have head : dependencies.head? = some parent.group.node.key := by
    rw [workCanonical child.group.node dependencies known]
    exact links parent parentMember child.group.node.key linked
  cases dependencies with
  | nil => simp at head
  | cons first rest =>
      simp only [List.head?_cons] at head
      have firstEq : first = parent.group.node.key := Option.some.inj head
      subst first
      exact generated.groupRecordAncestorSmaller known (by simp)

/-- Replacing a group node preserves child-edge coherence when the replacement
retains coherent links. -/
theorem State.ChildLinksCanonical.putGroupNode
    {queue : State} {parents : Nat → Keys}
    (links : queue.ChildLinksCanonical parents) (updated : GroupNode)
    (updatedLinks
      : ∀ child ∈ updated.childGroups,
          (parents child).head? = some updated.group.node.key)
    : (queue.putGroupNode updated).ChildLinksCanonical parents := by
  intro node member child childMember
  change node ∈ queue.groupNodes.map
    (fun old => if old.group.node.key == updated.group.node.key then updated else old)
    at member
  obtain ⟨old, oldMember, same⟩ := List.mem_map.mp member
  split at same
  · subst node
    exact updatedLinks child childMember
  · subst node
    exact links old oldMember child childMember

/-- A new group has no child links until the second integration pass. -/
theorem State.ChildLinksCanonical.addGroup
    {queue : State} {parents : Nat → Keys}
    (links : queue.ChildLinksCanonical parents) (group : Group)
    : (queue.addGroup group).ChildLinksCanonical parents := by
  unfold State.addGroup
  split
  · exact links
  · split
    · exact links
    · intro node member child childMember
      rcases List.mem_append.mp member with old | added
      · exact links node old child childMember
      · have same : node = { group } := List.mem_singleton.mp added
        subst node
        cases childMember

/-- The group-integration link pass adds only the primary-parent edge supplied
by the generated descriptor; other stored edges are unchanged. -/
theorem State.ChildLinksCanonical.addGroups
    {queue : State} {parents : Nat → Keys}
    (links : queue.ChildLinksCanonical parents) (groups : List Group)
    (all : ∀ group ∈ groups, group.parent = (parents group.node.key).head?)
    : (queue.addGroups groups).1.ChildLinksCanonical parents := by
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
  have registerFold (more : List Group) :
      ∀ current, current.ChildLinksCanonical parents
        → (more.foldl State.addGroup current).ChildLinksCanonical parents := by
    induction more with
    | nil => intro current currentLinks; exact currentLinks
    | cons group rest ih =>
        intro current currentLinks
        exact ih (current.addGroup group) (currentLinks.addGroup group)
  have linkOne (current : State) (group : Group)
      (currentLinks : current.ChildLinksCanonical parents)
      (groupCanonical : group.parent = (parents group.node.key).head?)
      : (linkStep current group).ChildLinksCanonical parents := by
    unfold linkStep
    split
    · exact currentLinks
    · rename_i parent parentEq
      split
      · exact currentLinks
      · rename_i node found
        apply currentLinks.putGroupNode
        intro child childMember
        split at childMember
        · exact currentLinks node (List.mem_of_find?_eq_some found)
            child childMember
        · rcases List.mem_append.mp childMember with old | fresh
          · exact currentLinks node (List.mem_of_find?_eq_some found) child old
          · have childEq : child = group.node.key := List.mem_singleton.mp fresh
            subst child
            rw [← groupCanonical]
            simpa [State.groupNode?_key found] using parentEq
  have linkFold (more : List Group)
      (subset : ∀ group ∈ more, group ∈ groups) :
      ∀ current, current.ChildLinksCanonical parents
        → (more.foldl linkStep current).ChildLinksCanonical parents := by
    induction more with
    | nil => intro current currentLinks; exact currentLinks
    | cons group rest ih =>
        intro current currentLinks
        have nextSubset : ∀ next ∈ rest, next ∈ groups := by
          intro next member
          exact subset next (by simp [member])
        exact ih nextSubset (linkStep current group)
          (linkOne current group currentLinks (all group (subset group (by simp))))
  let fresh := groups.filter (fun group =>
    !queue.registeredGroups.contains group.node.key
      && (queue.groupNode? group.node.key).isNone)
  change (fresh.foldl linkStep
    (fresh.foldl State.addGroup queue)).ChildLinksCanonical parents
  exact linkFold fresh (fun _ member => (List.mem_filter.mp member).1) _
    (registerFold fresh queue links)

/-- Adding a task updates group memberships and counters, but no child edge. -/
theorem State.ChildLinksCanonical.addTask
    {queue : State} {parents : Nat → Keys}
    (links : queue.ChildLinksCanonical parents) (task : Task)
    : (queue.addTask task).ChildLinksCanonical parents := by
  let registered : State := { queue with tasks := queue.tasks ++ [task] }
  let step (current : State) (group : Execution.DeliveryNode) : State :=
    match current.groupNode? group.key with
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
  change (if task.groups.any (fun group => current.rootGroups.contains group.key)
      && (current.taskNode? task.occurrence).isNone then
    { current with taskNodes := current.taskNodes ++ [{ task }] }
    else current).ChildLinksCanonical parents
  split <;> exact currentLinks

/-- Stream registration changes no group child links. -/
theorem State.ChildLinksCanonical.addStreams
    {queue : State} {parents : Nat → Keys}
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
    {queue : State} {parents : Nat → Keys}
    (links : queue.ChildLinksCanonical parents) (work : Work)
    (groupsCanonical
      : ∀ group ∈ work.groups, group.parent = (parents group.node.key).head?)
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
    {queue : State} {parents : Nat → Keys}
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

/-- Starting released work changes no stored group edges. -/
theorem State.ChildLinksCanonical.startNewWork
    {queue : State} {parents : Nat → Keys}
    (links : queue.ChildLinksCanonical parents) (newWork : NewWork)
    : (queue.startNewWork newWork).ChildLinksCanonical parents := by
  intro node member child childMember
  have same := (queue.startNewWork_groupCore newWork).1
  rw [same] at member
  exact links node member child childMember

/-- Removing a group preserves all edges on remaining nodes. -/
theorem State.ChildLinksCanonical.removeGroup
    {queue : State} {parents : Nat → Keys}
    (links : queue.ChildLinksCanonical parents) (key : Nat)
    : (queue.removeGroup key).ChildLinksCanonical parents := by
  intro node member child childMember
  unfold State.removeGroup at member
  exact links node (List.mem_filter.mp member).1 child childMember

/-- Removing a task changes memberships, not child edges. -/
theorem State.ChildLinksCanonical.removeTask
    {queue : State} {parents : Nat → Keys}
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
subtree retention, and cache updates restricted to invalidated keys.
-/
theorem State.HealthyRegisteredTaskAccounting.taskFailure
    {queue : State} {work : Execution.Work} {parents : Nat → Keys}
    {settled failed : List Occurrence}
    (accounted : queue.HealthyRegisteredTaskAccounting work settled failed)
    (taskMatching : queue.RegisteredTasksMatch work)
    (generated : ExecutedWork work)
    (links : queue.ChildLinksCanonical parents)
    (matching : queue.GroupNodesMatchWork work)
    (workCanonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    (occurrence : Occurrence) (errors : Nat)
    (taskNode : TaskNode) (found : queue.taskNode? occurrence = some taskNode)
    (failedOwners
      : ∀ group ∈ taskNode.task.groups,
          GroupInvalidated work (occurrence :: failed) group.key)
    : (queue.taskFailure occurrence errors).1.HealthyRegisteredTaskAccounting
        work settled (occurrence :: failed) := by
  let step (acc : State × List WorkQueueEvent)
      (group : Execution.DeliveryNode) : State × List WorkQueueEvent :=
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
  have stepFacts (acc : State × List WorkQueueEvent)
      (group : Execution.DeliveryNode)
      (groupFailed : GroupInvalidated work (occurrence :: failed) group.key)
      (currentAccounting : acc.1.HealthyRegisteredTaskAccounting
        work settled (occurrence :: failed))
      (currentLinks : acc.1.ChildLinksCanonical parents)
      (currentMatching : acc.1.GroupNodesMatchWork work)
      (currentTasks : acc.1.RegisteredTasksMatch work)
      : (step acc group).1.HealthyRegisteredTaskAccounting
          work settled (occurrence :: failed)
        ∧ (step acc group).1.ChildLinksCanonical parents
        ∧ (step acc group).1.GroupNodesMatchWork work
        ∧ (step acc group).1.RegisteredTasksMatch work := by
    obtain ⟨current, events⟩ := acc
    dsimp only [step]
    cases nodeFound : current.groupNode? group.key with
    | none => exact ⟨currentAccounting, currentLinks, currentMatching, currentTasks⟩
    | some node =>
        have nodeKey : node.group.node.key = group.key :=
          current.groupNode?_key nodeFound
        have removeFacts :
            (current.removeGroup group.key).HealthyRegisteredTaskAccounting
              work settled (occurrence :: failed)
            ∧ (current.removeGroup group.key).ChildLinksCanonical parents
            ∧ (current.removeGroup group.key).GroupNodesMatchWork work
            ∧ (current.removeGroup group.key).RegisteredTasksMatch work := by
          exact ⟨currentAccounting.removeInvalidatedGroup currentTasks generated currentLinks
              currentMatching workCanonical group.key groupFailed.toRecordInvalidated,
            currentLinks.removeGroup group.key,
            currentMatching.removeGroup group.key, currentTasks.removeGroup group.key⟩
        cases active : current.rootGroups.contains group.key with
        | false =>
            simp only [Bool.false_eq_true, ite_false]
            exact ⟨currentAccounting.putInvalidatedGroup _ (nodeKey.symm ▸ groupFailed),
              currentLinks.putGroupNode _
                (currentLinks node (List.mem_of_find?_eq_some nodeFound)),
              currentMatching.putGroupNode _
                (currentMatching node (List.mem_of_find?_eq_some nodeFound)),
              currentTasks.putGroupNode _⟩
        | true =>
            simpa [active, State.finishGroupFailure, nodeKey] using removeFacts
  have foldFacts (more : List Execution.DeliveryNode)
      (subset : ∀ group ∈ more, group ∈ taskNode.task.groups) :
      ∀ acc : State × List WorkQueueEvent,
        acc.1.HealthyRegisteredTaskAccounting
          work settled (occurrence :: failed)
        → acc.1.ChildLinksCanonical parents
        → acc.1.GroupNodesMatchWork work
        → acc.1.RegisteredTasksMatch work
        → (more.foldl step acc).1.HealthyRegisteredTaskAccounting
            work settled (occurrence :: failed)
          ∧ (more.foldl step acc).1.ChildLinksCanonical parents
          ∧ (more.foldl step acc).1.GroupNodesMatchWork work
          ∧ (more.foldl step acc).1.RegisteredTasksMatch work := by
    induction more with
    | nil =>
        intro acc currentAccounting currentLinks currentMatching currentTasks
        exact ⟨currentAccounting, currentLinks, currentMatching, currentTasks⟩
    | cons group rest ih =>
        intro acc currentAccounting currentLinks currentMatching currentTasks
        have groupFailed := failedOwners group (subset group (by simp))
        obtain ⟨nextAccounting, nextLinks, nextMatching, nextTasks⟩ :=
          stepFacts acc group groupFailed currentAccounting
            currentLinks currentMatching currentTasks
        have restSubset : ∀ candidate ∈ rest,
            candidate ∈ taskNode.task.groups := by
          intro candidate member
          exact subset candidate (by simp [member])
        exact ih restSubset (step acc group) nextAccounting nextLinks nextMatching
          nextTasks
  let current := queue.removeTask occurrence
  have enlarged := accounted.weakenFailures (after := occurrence :: failed)
    (by intro item member; simp [member])
  have currentAccounting : current.HealthyRegisteredTaskAccounting
      work settled (occurrence :: failed) :=
    enlarged.removeFailedTask taskMatching occurrence (by simp)
  have currentLinks : current.ChildLinksCanonical parents := links.removeTask occurrence
  have currentMatching : current.GroupNodesMatchWork work := matching.removeTask occurrence
  unfold State.taskFailure
  simp only [found]
  split
  · exact currentAccounting
  · exact (foldFacts taskNode.task.groups (fun _ member => member)
      (current, []) currentAccounting currentLinks currentMatching
      (taskMatching.removeTask occurrence)).1

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
        GroupInvalidated work (occurrence :: failed) group.key := by
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
      (taskNode.task.groups.map Execution.DeliveryNode.key) :=
    ⟨producer, payload, taskAt⟩
  have owner : group.key ∈ taskNode.task.groups.map Execution.DeliveryNode.key :=
    List.mem_map.mpr ⟨group, groupMember, rfl⟩
  have failedMember : taskNode.task.occurrence ∈ occurrence :: failed := by
    simp [occurrenceEq]
  exact GroupInvalidated.task owners owner failedMember

/-- Registered task provenance and canonical child links make task-failure
preservation unconditional on any extra owner-failure assumption. -/
private theorem State.HealthyRegisteredTaskAccounting.taskFailure_registered
    {queue : State} {work : Execution.Work} {parents : Nat → Keys}
    {settled failed : List Occurrence}
    (accounted : queue.HealthyRegisteredTaskAccounting work settled failed)
    (generated : ExecutedWork work)
    (links : queue.ChildLinksCanonical parents)
    (groupMatching : queue.GroupNodesMatchWork work)
    (workCanonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
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
    {queue : State} {work : Execution.Work} {parents : Nat → Keys}
    {settled failed : List Occurrence}
    (accounted : queue.HealthyRegisteredTaskAccounting work settled failed)
    (generated : ExecutedWork work)
    (links : queue.ChildLinksCanonical parents)
    (groupMatching : queue.GroupNodesMatchWork work)
    (workCanonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
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
    (initialWork : Work) (parents : Nat → Keys)
    (all : ∀ group ∈ initialWork.groups, group.parent = (parents group.node.key).head?)
    : (State.initialize initialWork).ChildLinksCanonical parents := by
  let integrated := (({} : State).maybeIntegrateWork initialWork).1
  let newWork := (({} : State).maybeIntegrateWork initialWork).2
  let pruned := (integrated.pruneEmptyGroups newWork.newGroups).1
  let groups := (integrated.pruneEmptyGroups newWork.newGroups).2
  let roots := { newWork with newGroups := groups }
  let started := pruned.startNewWork roots
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
links, even when a group key has multiple execution occurrences. -/
private theorem ExecutedWork.initialQueueChildLinksCanonical
    {work : Execution.Work} (generated : ExecutedWork work)
    : ∃ parents : Nat → Keys,
        (State.initialize (Work.fromExecution work)).ChildLinksCanonical parents := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  refine ⟨parents, createWorkQueue_childLinksCanonical
    (Work.fromExecution work) parents ?_⟩
  intro group member
  exact workFromSpec_groups_parentCanonical
    (Located.root (root := work)) canonical member

/-- Flushing a group deletes task memberships and group nodes without
changing any child edge on a surviving node. -/
theorem State.ChildLinksCanonical.finishGroupSuccess
    {queue : State} {parents : Nat → Keys}
    (links : queue.ChildLinksCanonical parents) (group : GroupNode)
    : (queue.finishGroupSuccess group).1.ChildLinksCanonical parents := by
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
  have stepLinks (acc : State × List ExecutionGroupValue × Keys)
      (occurrence : Occurrence)
      (currentLinks : acc.1.ChildLinksCanonical parents)
      : (step acc occurrence).1.ChildLinksCanonical parents := by
    obtain ⟨current, values, streams⟩ := acc
    dsimp only [step]
    split
    · exact currentLinks
    · exact currentLinks.removeTask occurrence
  have foldLinks (tasks : List Occurrence) :
      ∀ acc : State × List ExecutionGroupValue × Keys,
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
          (fun node => node.group.node.key != group.group.node.key)
        rootGroups := flushed.rootGroups.filter (· != group.group.node.key) }
  have currentLinks : current.ChildLinksCanonical parents := by
    intro node member child childMember
    exact flushedLinks node (List.mem_filter.mp member).1 child childMember
  let children := group.childGroups.filterMap
    (fun key => (current.groupNode? key).map (fun node => node.group.node))
  change (current.pruneEmptyGroups children).1.ChildLinksCanonical parents
  exact currentLinks.pruneEmptyGroups children

/-- Failure closure only deletes group nodes. -/
theorem State.ChildLinksCanonical.finishGroupFailure
    {queue : State} {parents : Nat → Keys}
    (links : queue.ChildLinksCanonical parents)
    (group : GroupNode) (errors : Nat)
    : (queue.finishGroupFailure group errors).1.ChildLinksCanonical parents := by
  unfold State.finishGroupFailure
  exact links.removeGroup group.group.node.key

/-- Recursive drain steps preserve canonical child edges, including cached failures.
Witness: the generic drain induction transports success, activation, and removal facts.
-/
theorem State.ChildLinksCanonical.drainReadyGroups
    {queue : State} {parents : Nat → Keys} (links : queue.ChildLinksCanonical parents)
    : queue.drainReadyGroups.1.ChildLinksCanonical parents := by
  exact State.drainReadyGroups_preserves (fun state => state.ChildLinksCanonical parents)
    (fun _ node prior _ _ _ _ => (prior.finishGroupSuccess node).startNewWork _)
    (fun _ node errors prior _ _ _ => prior.finishGroupFailure node errors) links

/-- Task failure preserves child edges through active removal and latent caching.
Witness: the contributor fold changes counters and failures but no surviving child list.
-/
theorem State.ChildLinksCanonical.taskFailure
    {queue : State} {parents : Nat → Keys}
    (links : queue.ChildLinksCanonical parents)
    (occurrence : Occurrence) (errors : Nat)
    : (queue.taskFailure occurrence errors).1.ChildLinksCanonical parents := by
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
  have stepLinks (acc : State × List WorkQueueEvent)
      (group : Execution.DeliveryNode)
      (currentLinks : acc.1.ChildLinksCanonical parents)
      : (step acc group).1.ChildLinksCanonical parents := by
    obtain ⟨current, events⟩ := acc
    dsimp only [step]
    split
    · exact currentLinks
    · rename_i node found
      split
      · exact currentLinks.finishGroupFailure _ errors
      · exact currentLinks.putGroupNode _
          (currentLinks node (List.mem_of_find?_eq_some found))
  have foldLinks (groups : List Execution.DeliveryNode) :
      ∀ acc : State × List WorkQueueEvent,
        acc.1.ChildLinksCanonical parents
          → (groups.foldl step acc).1.ChildLinksCanonical parents := by
    induction groups with
    | nil => intro acc currentLinks; exact currentLinks
    | cons group rest ih =>
        intro acc currentLinks
        exact ih (step acc group) (stepLinks acc group currentLinks)
  unfold State.taskFailure
  split
  · exact links
  · rename_i taskNode found
    let current := queue.removeTask occurrence
    have currentLinks : current.ChildLinksCanonical parents := links.removeTask occurrence
    split
    · exact currentLinks
    change (taskNode.task.groups.foldl step (current, [])).1.ChildLinksCanonical
      parents
    exact foldLinks taskNode.task.groups (current, []) currentLinks

/-- Successful task settlement maintains child-edge coherence through child
integration, co-owner settlement, and sequential group release. -/
theorem State.ChildLinksCanonical.taskSuccess
    {queue : State} {parents : Nat → Keys}
    (links : queue.ChildLinksCanonical parents)
    (occurrence : Occurrence) (result : TaskResult)
    (childrenCanonical
      : ∀ group ∈ result.work.groups, group.parent = (parents group.node.key).head?)
    : (queue.taskSuccess occurrence result).1.ChildLinksCanonical parents := by
  let settleStep (current : State) (group : Execution.DeliveryNode) : State :=
    match current.groupNode? group.key with
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
    split
    · exact links.removeTask occurrence
    let withValue := queue.putTaskNode { taskNode with value := some result.value }
    have withValueLinks : withValue.ChildLinksCanonical parents := links
    let integrated := (withValue.maybeIntegrateWork result.work (some occurrence)).1
    have integratedLinks : integrated.ChildLinksCanonical parents :=
      withValueLinks.maybeIntegrateWork result.work childrenCanonical
        (some occurrence)
    let released := taskNode.task.groups.foldl releaseStep (integrated, [], {})
    have releasedLinks : released.1.ChildLinksCanonical parents :=
      releaseFold taskNode.task.groups (integrated, [], {}) integratedLinks
    change (released.1.startNewWork released.2.2).drainReadyGroups.1.ChildLinksCanonical parents
    exact (releasedLinks.startNewWork released.2.2).drainReadyGroups

/-- Each published stream item integrates canonically parented child work;
the batch fold therefore retains coherent child edges. -/
theorem State.ChildLinksCanonical.streamItems
    {queue : State} {parents : Nat → Keys}
    (links : queue.ChildLinksCanonical parents)
    (stream : Execution.DeliveryNode) (items : List StreamItem)
    (childrenCanonical
      : ∀ item ∈ items,
        ∀ group ∈ item.work.groups, group.parent = (parents group.node.key).head?)
    : (queue.streamItems stream items).1.ChildLinksCanonical parents := by
  let step (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue)
      (item : StreamItem) :=
    let (current, groups, streams, values) := acc
    let (integrated, newWork) := current.maybeIntegrateWork item.work
    let (pruned, nonempty) := integrated.pruneEmptyGroups newWork.newGroups
    (pruned.startNewWork { newWork with newGroups := nonempty },
      groups ++ nonempty, streams ++ newWork.newStreams,
      values ++ [item.value])
  have stepLinks (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue)
      (item : StreamItem) (currentLinks : acc.1.ChildLinksCanonical parents)
      (itemMember : item ∈ items)
      : (step acc item).1.ChildLinksCanonical parents := by
    obtain ⟨current, groups, streams, values⟩ := acc
    let integrated := current.maybeIntegrateWork item.work
    have integratedLinks : integrated.1.ChildLinksCanonical parents :=
      currentLinks.maybeIntegrateWork item.work
        (childrenCanonical item itemMember)
    let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
    have prunedLinks : pruned.1.ChildLinksCanonical parents :=
      integratedLinks.pruneEmptyGroups integrated.2.newGroups
    exact prunedLinks.startNewWork
      { integrated.2 with newGroups := pruned.2 }
  have foldLinks (more : List StreamItem)
      (subset : ∀ item ∈ more, item ∈ items) :
      ∀ acc : State × List Execution.DeliveryNode
        × List Execution.DeliveryNode × List StreamItemValue,
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
      (queue, [], [], []) links).drainReadyGroups

/-- Stream closure only removes the stream root, not group links. -/
theorem State.ChildLinksCanonical.streamSuccess
    {queue : State} {parents : Nat → Keys}
    (links : queue.ChildLinksCanonical parents)
    (stream : Execution.DeliveryNode)
    : (queue.streamSuccess stream).1.ChildLinksCanonical parents := by
  unfold State.streamSuccess
  split <;> exact links

/-- Stream failure also leaves group links unchanged. -/
theorem State.ChildLinksCanonical.streamFailure
    {queue : State} {parents : Nat → Keys}
    (links : queue.ChildLinksCanonical parents)
    (stream : Execution.DeliveryNode) (errors : Nat)
    : (queue.streamFailure stream errors).1.ChildLinksCanonical parents := by
  unfold State.streamFailure
  split <;> exact links

/-- A host event matching generated Work preserves coherent group child
edges, including edges created by newly revealed child Work. -/
theorem State.ChildLinksCanonical.handleGraphEvent
    {queue : State} {work : Execution.Work} {parents : Nat → Keys}
    (links : queue.ChildLinksCanonical parents)
    (event : GraphEvent) (matching : event.MatchesWork work)
    (workCanonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    : (queue.handleGraphEvent event).1.ChildLinksCanonical parents := by
  cases event with
  | taskSuccess occurrence result =>
      exact links.taskSuccess occurrence result
        (fun group member =>
          matching.taskChildGroups_parentCanonical workCanonical member)
  | taskFailure occurrence errors => exact links.taskFailure occurrence errors
  | streamItems stream items =>
      exact links.streamItems stream items
        (fun item itemMember group groupMember =>
          matching.streamItem_childGroups_parentCanonical workCanonical
            itemMember groupMember)
  | streamSuccess stream => exact links.streamSuccess stream
  | streamFailure stream errors => exact links.streamFailure stream errors

/-- The event-batch fold preserves coherent child links. -/
theorem State.ChildLinksCanonical.handleGraphEvents
    {queue : State} {work : Execution.Work} {parents : Nat → Keys}
    (links : queue.ChildLinksCanonical parents)
    (batch : List GraphEvent)
    (allMatch : ∀ event ∈ batch, event.MatchesWork work)
    (workCanonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    : (queue.handleGraphEvents batch).1.ChildLinksCanonical parents := by
  let step (acc : State × List WorkQueueEvent) (event : GraphEvent) :=
    let (current, outputs) := acc
    let (next, produced) := current.handleGraphEvent event
    (next, outputs ++ produced)
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
            parents := currentLinks.handleGraphEvent event eventMatch workCanonical
        exact ih restSubset (step (current, outputs) event) nextLinks
  unfold State.handleGraphEvents
  split
  · exact links
  · cases outcome : batch.foldl step (queue, []) with
    | mk current outputs =>
        have currentLinks : current.ChildLinksCanonical parents := by
          have folded := foldLinks batch (fun _ member => member)
            (queue, []) links
          rw [outcome] at folded
          exact folded
        dsimp only
        split <;> exact currentLinks

/-- All finite matched-input replays preserve coherent child edges. -/
theorem State.ChildLinksCanonical.runNormalized
    {queue : State} {work : Execution.Work} {parents : Nat → Keys}
    (links : queue.ChildLinksCanonical parents)
    (batches : List (List GraphEvent))
    (allMatch : ∀ batch ∈ batches, ∀ event ∈ batch, event.MatchesWork work)
    (workCanonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
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
    : ∃ parents : Nat → Keys,
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
        exact workFromSpec_groups_parentCanonical
          (Located.root (root := work)) workCanonical member)
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
    : ∃ parents : Nat → Keys,
        (∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
        ∧ ((State.initialize (Work.fromExecution work)).runNormalized
            batches).1.ChildLinksCanonical
            parents
        ∧ ((State.initialize (Work.fromExecution work)).runNormalized
            batches).1.GroupNodesMatchWork
            work := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have initial := createWorkQueue_childLinksCanonical (Work.fromExecution work) parents
    (fun _ member => workFromSpec_groups_parentCanonical
      (Located.root (root := work)) canonical member)
  refine ⟨parents, canonical, initial.runNormalized batches ?_ canonical,
    valid.runNormalized_groupNodesMatchWork⟩
  intro batch batchMember event eventMember
  exact valid.eachMatches (List.mem_flatten.mpr ⟨batch, batchMember, eventMember⟩)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
