import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RootLinks

/-! Task links during work activation and successful release. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (ExecutionGroupValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Every started task is linked to each of its active root contributors. -/
def State.ActiveTaskLinks (queue : State) : Prop :=
  ∀ taskNode ∈ queue.taskNodes,
    queue.RootTaskLinkedOn taskNode.task.occurrence
      (taskNode.task.groups.map Execution.DeliveryNode.ref)

/-- Starting released work leaves the registered group and task maps unchanged;
only the root set grows by the refs being activated. -/
theorem State.startNewWork_groupCore (queue : State) (newWork : NewWork)
    : (queue.startNewWork newWork).groupNodes = queue.groupNodes
      ∧ (queue.startNewWork newWork).tasks = queue.tasks
      ∧ (queue.startNewWork newWork).rootGroups
        = queue.rootGroups ++ newWork.newGroups.map Execution.DeliveryNode.ref := by
  have taskCore (state : State) (occurrence : Occurrence) :
      (state.startTask occurrence).groupNodes = state.groupNodes
      ∧ (state.startTask occurrence).tasks = state.tasks
      ∧ (state.startTask occurrence).rootGroups = state.rootGroups := by
    unfold State.startTask
    split
    · exact ⟨rfl, rfl, rfl⟩
    · split <;> exact ⟨rfl, rfl, rfl⟩
  have groupCore (state : State) (ref : NodeRef) :
      (state.startGroup ref).groupNodes = state.groupNodes
      ∧ (state.startGroup ref).tasks = state.tasks
      ∧ (state.startGroup ref).rootGroups = state.rootGroups := by
    unfold State.startGroup
    split
    · exact ⟨rfl, rfl, rfl⟩
    · rename_i node found
      have foldCore (more : List Occurrence) :
          ∀ current : State,
            (more.foldl State.startTask current).groupNodes = current.groupNodes
            ∧ (more.foldl State.startTask current).tasks = current.tasks
            ∧ (more.foldl State.startTask current).rootGroups = current.rootGroups := by
        induction more with
        | nil => intro current; exact ⟨rfl, rfl, rfl⟩
        | cons occurrence rest ih =>
            intro current
            obtain ⟨groups, tasks, roots⟩ := ih (current.startTask occurrence)
            obtain ⟨taskGroups, taskTasks, taskRoots⟩ := taskCore current occurrence
            exact ⟨groups.trans taskGroups, tasks.trans taskTasks, roots.trans taskRoots⟩
      split
      · exact ⟨rfl, rfl, rfl⟩
      · exact foldCore node.tasks state
  have streamCore (state : State) (ref : NodeRef) :
      (state.startStream ref).groupNodes = state.groupNodes
      ∧ (state.startStream ref).tasks = state.tasks
      ∧ (state.startStream ref).rootGroups = state.rootGroups := by
    unfold State.startStream
    split <;> exact ⟨rfl, rfl, rfl⟩
  have groupFold (more : NodeRefs) :
      ∀ current : State,
        (more.foldl State.startGroup current).groupNodes = current.groupNodes
        ∧ (more.foldl State.startGroup current).tasks = current.tasks
        ∧ (more.foldl State.startGroup current).rootGroups = current.rootGroups := by
    induction more with
    | nil => intro current; exact ⟨rfl, rfl, rfl⟩
    | cons ref rest ih =>
        intro current
        obtain ⟨groups, tasks, roots⟩ := ih (current.startGroup ref)
        obtain ⟨oneGroups, oneTasks, oneRoots⟩ := groupCore current ref
        exact ⟨groups.trans oneGroups, tasks.trans oneTasks, roots.trans oneRoots⟩
  have streamFold (more : NodeRefs) :
      ∀ current : State,
        (more.foldl State.startStream current).groupNodes = current.groupNodes
        ∧ (more.foldl State.startStream current).tasks = current.tasks
        ∧ (more.foldl State.startStream current).rootGroups = current.rootGroups := by
    induction more with
    | nil => intro current; exact ⟨rfl, rfl, rfl⟩
    | cons ref rest ih =>
        intro current
        obtain ⟨groups, tasks, roots⟩ := ih (current.startStream ref)
        obtain ⟨oneGroups, oneTasks, oneRoots⟩ := streamCore current ref
        exact ⟨groups.trans oneGroups, tasks.trans oneTasks, roots.trans oneRoots⟩
  let groups := newWork.newGroups.map Execution.DeliveryNode.ref
  let streams := newWork.newStreams.map Execution.DeliveryNode.ref
  let current : State := { queue with rootGroups := queue.rootGroups ++ groups }
  let started := groups.foldl State.startGroup current
  obtain ⟨groupNodes, groupTasks, groupRoots⟩ := groupFold groups current
  obtain ⟨streamNodes, streamTasks, streamRoots⟩ := streamFold streams started
  change (streams.foldl State.startStream started).groupNodes = queue.groupNodes
    ∧ (streams.foldl State.startStream started).tasks = queue.tasks
    ∧ (streams.foldl State.startStream started).rootGroups =
        queue.rootGroups ++ groups
  exact ⟨streamNodes.trans groupNodes, streamTasks.trans groupTasks,
    streamRoots.trans groupRoots⟩

/-- Activating group refs preserves root presence when each released ref still
has a live group node. The queue's release and pruning stages must establish
the latter condition. -/
theorem State.RootGroupsPresent.startNewWork
    {queue : State} (present : queue.RootGroupsPresent)
    (newWork : NewWork)
    (released
      : ∀ ref ∈ newWork.newGroups.map Execution.DeliveryNode.ref,
          ref ∈ queue.groupNodes.map (fun node => node.group.node.ref))
    : (queue.startNewWork newWork).RootGroupsPresent := by
  intro ref rootMember
  obtain ⟨sameGroups, _, newRoots⟩ := queue.startNewWork_groupCore newWork
  rw [newRoots] at rootMember
  rw [sameGroups]
  rcases List.mem_append.mp rootMember with old | fresh
  · exact present ref old
  · exact released ref fresh

/-- Task occurrences requested by the newly activated group roots. -/
def State.releaseRequests (queue : State) (newWork : NewWork) : List Occurrence :=
  queue.groupNodes.flatMap
    fun node =>
      if node.group.node.ref ∈ newWork.newGroups.map Execution.DeliveryNode.ref then
        node.tasks
      else
        []

/-- Starting one task keeps prior task nodes or adds a node for the requested
occurrence. -/
private theorem State.startTask_oldOrRequested
    (queue : State) (occurrence : Occurrence)
    {node : TaskNode} (member : node ∈ (queue.startTask occurrence).taskNodes)
    : node ∈ queue.taskNodes ∨ node.task.occurrence = occurrence := by
  unfold State.startTask at member
  split at member
  · exact Or.inl member
  · split at member
    · exact Or.inl member
    · rename_i task found
      rcases List.mem_append.mp member with old | added
      · exact Or.inl old
      · right
        have same : node = { task } := List.mem_singleton.mp added
        subst node
        have selected := List.find?_some
          (p := fun candidate : Task => candidate.occurrence == occurrence)
          (by simpa [State.task?] using found)
        exact (occurrence_beq_iff_eq _ _).mp selected

/-- A group starts only its listed task occurrences. -/
private theorem State.startGroup_oldOrRequested
    (queue : State) (ref : NodeRef)
    {taskNode : TaskNode} (member : taskNode ∈ (queue.startGroup ref).taskNodes)
    : taskNode ∈ queue.taskNodes
      ∨ ∃ groupNode,
          queue.groupNode? ref = some groupNode
          ∧ taskNode.task.occurrence ∈ groupNode.tasks := by
  have foldTasks (more : List Occurrence) :
      ∀ current : State, ∀ node : TaskNode,
        node ∈ (more.foldl State.startTask current).taskNodes
          → node ∈ current.taskNodes ∨ node.task.occurrence ∈ more := by
    induction more with
    | nil =>
        intro current node nodeMember
        exact Or.inl nodeMember
    | cons occurrence rest ih =>
        intro current node nodeMember
        rcases ih (current.startTask occurrence) node nodeMember with old | later
        · rcases current.startTask_oldOrRequested occurrence old with earlier | now
          · exact Or.inl earlier
          · exact Or.inr (List.mem_cons.mpr (Or.inl now))
        · exact Or.inr (List.mem_cons.mpr (Or.inr later))
  unfold State.startGroup at member
  split at member
  · exact Or.inl member
  · rename_i groupNode found
    split at member
    · exact Or.inl member
    · rcases foldTasks groupNode.tasks queue taskNode member with old | requested
      · exact Or.inl old
      · exact Or.inr ⟨groupNode, found, requested⟩

/-- Task and group activation do not mutate the group-node map. -/
private theorem State.startGroup_groupNodes (queue : State) (ref : NodeRef)
    : (queue.startGroup ref).groupNodes = queue.groupNodes := by
  have startTaskNodes (current : State) (occurrence : Occurrence) :
      (current.startTask occurrence).groupNodes = current.groupNodes := by
    unfold State.startTask
    split
    · rfl
    · split <;> rfl
  have foldNodes (more : List Occurrence) :
      ∀ current, (more.foldl State.startTask current).groupNodes
        = current.groupNodes := by
    induction more with
    | nil => intro current; rfl
    | cons occurrence rest ih =>
        intro current
        simp only [List.foldl_cons, ih, startTaskNodes]
  unfold State.startGroup
  split
  · rfl
  · rename_i groupNode found
    split
    · rfl
    · exact foldNodes groupNode.tasks queue

/-- No started task can be introduced by group release unless an activated
group requested its occurrence. -/
theorem State.startNewWork_oldOrRequested
    (queue : State) (newWork : NewWork)
    {taskNode : TaskNode}
    (member : taskNode ∈ (queue.startNewWork newWork).taskNodes)
    : taskNode ∈ queue.taskNodes
      ∨ taskNode.task.occurrence ∈ queue.releaseRequests newWork := by
  let groups := newWork.newGroups.map Execution.DeliveryNode.ref
  let streams := newWork.newStreams.map Execution.DeliveryNode.ref
  let initial : State := { queue with rootGroups := queue.rootGroups ++ groups }
  have streamNodes (current : State) (ref : NodeRef) :
      (current.startStream ref).taskNodes = current.taskNodes := by
    unfold State.startStream
    split <;> rfl
  have streamFold (more : NodeRefs) :
      ∀ current, (more.foldl State.startStream current).taskNodes
        = current.taskNodes := by
    induction more with
    | nil => intro current; rfl
    | cons ref rest ih =>
        intro current
        simp only [List.foldl_cons, ih, streamNodes]
  have groupFold (more : NodeRefs)
      (subset : ∀ ref ∈ more, ref ∈ groups) :
      ∀ current : State, current.groupNodes = queue.groupNodes
        → ∀ node : TaskNode,
          node ∈ (more.foldl State.startGroup current).taskNodes
            → node ∈ current.taskNodes
              ∨ node.task.occurrence ∈ queue.releaseRequests newWork := by
    induction more with
    | nil =>
        intro current _ node nodeMember
        exact Or.inl nodeMember
    | cons ref rest ih =>
        intro current sameGroups node nodeMember
        have nextGroups : (current.startGroup ref).groupNodes = queue.groupNodes :=
          (current.startGroup_groupNodes ref).trans sameGroups
        have restSubset : ∀ next ∈ rest, next ∈ groups := by
          intro next nextMember
          exact subset next (by simp [nextMember])
        rcases ih restSubset (current.startGroup ref) nextGroups node nodeMember with
          inStartGroup | alreadyRequested
        · rcases current.startGroup_oldOrRequested ref inStartGroup with
            old | requested
          · exact Or.inl old
          · obtain ⟨groupNode, found, requested⟩ := requested
            right
            have foundQueue : queue.groupNode? ref = some groupNode := by
              simpa [State.groupNode?, sameGroups] using found
            have groupMember : groupNode ∈ queue.groupNodes :=
              List.mem_of_find?_eq_some foundQueue
            have refMember : groupNode.group.node.ref ∈ groups := by
              rw [queue.groupNode?_ref foundQueue]
              exact subset ref (by simp)
            unfold State.releaseRequests
            apply List.mem_flatMap.mpr
            refine ⟨groupNode, groupMember, ?_⟩
            change groupNode.group.node.ref ∈
              newWork.newGroups.map Execution.DeliveryNode.ref at refMember
            simpa [refMember] using requested
        · exact Or.inr alreadyRequested
  unfold State.startNewWork at member
  change taskNode ∈
    (streams.foldl State.startStream
      (groups.foldl State.startGroup initial)).taskNodes at member
  rw [streamFold streams] at member
  rcases groupFold groups (by intro ref refMember; exact refMember) initial rfl
      taskNode member with old | requested
  · exact Or.inl old
  · exact Or.inr requested

/-- Activation never removes an already started task node. -/
private theorem State.startNewWork_preservesTaskNodes
    (queue : State) (newWork : NewWork)
    {node : TaskNode} (member : node ∈ queue.taskNodes)
    : node ∈ (queue.startNewWork newWork).taskNodes := by
  have startTaskPreserves (current : State) (occurrence : Occurrence)
      {node : TaskNode} (member : node ∈ current.taskNodes)
      : node ∈ (current.startTask occurrence).taskNodes := by
    unfold State.startTask
    split
    · exact member
    · split
      · exact member
      · exact List.mem_append.mpr (Or.inl member)
  have startGroupPreserves (current : State) (ref : NodeRef)
      {node : TaskNode} (member : node ∈ current.taskNodes)
      : node ∈ (current.startGroup ref).taskNodes := by
    unfold State.startGroup
    split
    · exact member
    · rename_i groupNode found
      have foldTasks (more : List Occurrence) :
          ∀ current : State, ∀ node : TaskNode,
            node ∈ current.taskNodes
              → node ∈ (more.foldl State.startTask current).taskNodes := by
        induction more with
        | nil => intro current node old; exact old
        | cons occurrence rest ih =>
            intro current node old
            exact ih (current.startTask occurrence) node
              (startTaskPreserves current occurrence old)
      split
      · exact member
      · exact foldTasks groupNode.tasks current node member
  have groupFold (more : NodeRefs) :
      ∀ current : State, ∀ node : TaskNode,
        node ∈ current.taskNodes
          → node ∈ (more.foldl State.startGroup current).taskNodes := by
    induction more with
    | nil => intro current node old; exact old
    | cons ref rest ih =>
        intro current node old
        exact ih (current.startGroup ref) node
          (startGroupPreserves current ref old)
  have streamFold (more : NodeRefs) :
      ∀ current : State, (more.foldl State.startStream current).taskNodes
        = current.taskNodes := by
    induction more with
    | nil => intro current; rfl
    | cons ref rest ih =>
        intro current
        have one : (current.startStream ref).taskNodes = current.taskNodes := by
          unfold State.startStream
          split <;> rfl
        simp only [List.foldl_cons, ih, one]
  let groups := newWork.newGroups.map Execution.DeliveryNode.ref
  let streams := newWork.newStreams.map Execution.DeliveryNode.ref
  let initial : State := { queue with rootGroups := queue.rootGroups ++ groups }
  unfold State.startNewWork
  change node ∈
    (streams.foldl State.startStream
      (groups.foldl State.startGroup initial)).taskNodes
  rw [streamFold streams]
  exact groupFold groups initial node member

/-- The registration of pre-activation nodes follows from their registration
after activation, because activation only adds task nodes and changes no task
definitions. -/
theorem State.StartedTasksRegistered.beforeStartNewWork
    {queue : State} {newWork : NewWork}
    (registered : (queue.startNewWork newWork).StartedTasksRegistered)
    : queue.StartedTasksRegistered := by
  intro node member
  have finalMember : node ∈ (queue.startNewWork newWork).taskNodes :=
    queue.startNewWork_preservesTaskNodes newWork member
  have finalTask : node.task ∈ (queue.startNewWork newWork).tasks :=
    registered node finalMember
  rw [(queue.startNewWork_groupCore newWork).2.1] at finalTask
  exact finalTask

/-- Static membership condition at a release boundary. It covers only tasks
already started or requested by newly active groups. Settled tasks can remain
registered after their group membership has been removed. -/
private def State.ReleaseTaskLinks (queue : State) (newWork : NewWork) : Prop :=
  ∀ task ∈ queue.tasks,
  ∀ node ∈ queue.groupNodes,
    (task.occurrence ∈ queue.taskNodes.map (fun started => started.task.occurrence)
      ∨ task.occurrence ∈ queue.releaseRequests newWork)
    → node.group.node.ref
      ∈ queue.rootGroups ++ newWork.newGroups.map Execution.DeliveryNode.ref
    → node.group.node.ref ∈ task.groups.map Execution.DeliveryNode.ref
    → task.occurrence ∈ node.tasks

/-- Releasing groups preserves active task links when the registered task/group
memberships are ready before activation. -/
theorem State.ActiveTaskLinks.startNewWork
    {queue : State} (registered : queue.StartedTasksRegistered)
    (newWork : NewWork) (ready : queue.ReleaseTaskLinks newWork)
    : (queue.startNewWork newWork).ActiveTaskLinks := by
  let final := queue.startNewWork newWork
  obtain ⟨sameGroups, sameTasks, roots⟩ := queue.startNewWork_groupCore newWork
  have finalRegistered : final.StartedTasksRegistered :=
    registered.startNewWork newWork
  intro taskNode member node groupMember rootMember refMember
  have taskMember : taskNode.task ∈ queue.tasks := by
    rw [← sameTasks]
    exact finalRegistered taskNode member
  have originalGroup : node ∈ queue.groupNodes := by
    rw [← sameGroups]
    exact groupMember
  have originalRoot : node.group.node.ref ∈
      queue.rootGroups ++ newWork.newGroups.map Execution.DeliveryNode.ref := by
    rw [← roots]
    exact rootMember
  have requested : taskNode.task.occurrence ∈
      queue.taskNodes.map (fun started => started.task.occurrence)
        ∨ taskNode.task.occurrence ∈ queue.releaseRequests newWork := by
    rcases queue.startNewWork_oldOrRequested newWork member with old | released
    · exact Or.inl (List.mem_map.mpr ⟨taskNode, old, rfl⟩)
    · exact Or.inr released
  exact ready taskNode.task taskMember node originalGroup requested originalRoot
    refMember

/-- Before a queue begins processing events, every registered task is linked to
every live group in its contributor list. This stronger base invariant may be
lost after failure and must not be assumed for arbitrary replay states. -/
def State.InitialTaskLinks (queue : State) : Prop :=
  ∀ task ∈ queue.tasks,
    queue.TaskLinkedOn task.occurrence (task.groups.map Execution.DeliveryNode.ref)

/-- Registering one task appends its definition and changes no older task
definitions. -/
theorem State.addTask_tasks (queue : State) (task : Task)
    : (queue.addTask task).tasks = queue.tasks ++ [task] := by
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
  have stepTasks (current : State) (group : Execution.DeliveryNode) :
      (step current group).tasks = current.tasks := by
    unfold step
    split
    · rfl
    · split <;> rfl
  have foldTasks (groups : List Execution.DeliveryNode) :
      ∀ current, (groups.foldl step current).tasks = current.tasks := by
    induction groups with
    | nil => intro current; rfl
    | cons group rest ih =>
        intro current
        simp only [List.foldl_cons, ih, stepTasks]
  let current := task.groups.foldl step registered
  have currentTasks : current.tasks = queue.tasks ++ [task] :=
    foldTasks task.groups registered
  change (if task.groups.any (fun group => current.rootGroups.contains group.ref)
      && (current.taskNode? task.occurrence).isNone then
      { current with taskNodes := current.taskNodes ++ [{ task }] }
    else current).tasks = queue.tasks ++ [task]
  split <;> exact currentTasks

/-- Task registration establishes its own links and preserves earlier task
links while the group-ref registry remains unique. -/
theorem State.InitialTaskLinks.addTask
    {queue : State} (unique : queue.GroupRefsUnique)
    (links : queue.InitialTaskLinks) (task : Task)
    : (queue.addTask task).InitialTaskLinks := by
  intro registered member
  rw [queue.addTask_tasks task] at member
  rcases List.mem_append.mp member with old | new
  · exact (links registered old).addTask unique task
  · have same : registered = task := List.mem_singleton.mp new
    subst registered
    exact queue.addTask_links unique task

/-- Group registration and parent-link installation do not register tasks. -/
theorem State.addGroups_tasks (queue : State) (groups : List Group)
    : (queue.addGroups groups).1.tasks = queue.tasks := by
  let linkStep (current : State) (group : Group) : State :=
    match group.parent with
    | none => current
    | some parent =>
        match current.groupNode? parent with
        | none => current
        | some node =>
            let children :=
              if node.childGroups.contains group.node.ref then
                node.childGroups
              else
                node.childGroups ++ [group.node.ref]
            current.putGroupNode { node with childGroups := children }
  have registerStep (current : State) (group : Group) :
      (current.addGroup group).tasks = current.tasks := by
    unfold State.addGroup
    split
    · rfl
    · split <;> rfl
  have registerFold (more : List Group) :
      ∀ current, (more.foldl State.addGroup current).tasks = current.tasks := by
    induction more with
    | nil => intro current; rfl
    | cons group rest ih =>
        intro current
        simp only [List.foldl_cons, ih, registerStep]
  have linkStepTasks (current : State) (group : Group) :
      (linkStep current group).tasks = current.tasks := by
    unfold linkStep
    split
    · rfl
    · split <;> rfl
  have linkFold (more : List Group) :
      ∀ current, (more.foldl linkStep current).tasks = current.tasks := by
    induction more with
    | nil => intro current; rfl
    | cons group rest ih =>
        intro current
        simp only [List.foldl_cons, ih, linkStepTasks]
  let fresh := groups.filter (fun group =>
    !queue.registeredGroups.contains group.node.ref
      && (queue.groupNode? group.node.ref).isNone)
  change (fresh.foldl linkStep
    (fresh.foldl State.addGroup queue)).tasks = queue.tasks
  rw [linkFold, registerFold]

/-- Adding stream descriptors does not change registered task definitions. -/
theorem State.addStreams_tasks (queue : State) (streams : List Stream)
    (parentTask : Option Occurrence)
    : (queue.addStreams streams parentTask).1.tasks = queue.tasks := by
  unfold State.addStreams
  split
  · rfl
  · dsimp
    split <;> rfl

/-- A stream-registration pass preserves links for registered tasks. -/
theorem State.InitialTaskLinks.addStreams
    {queue : State} (links : queue.InitialTaskLinks)
    (streams : List Stream) (parentTask : Option Occurrence)
    : (queue.addStreams streams parentTask).1.InitialTaskLinks := by
  intro task member
  have old : task ∈ queue.tasks := by
    rw [← queue.addStreams_tasks streams parentTask]
    exact member
  exact (links task old).addStreams streams parentTask

/-- Pruning group shells never changes the registered task-definition list. -/
theorem State.pruneEmptyGroups_tasks (queue : State)
    (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.tasks = queue.tasks := by
  have loop (fuel : Nat) (current : State)
      (remaining kept : List Execution.DeliveryNode) :
      (State.pruneEmptyGroups.go fuel current remaining kept).1.tasks =
        current.tasks := by
    induction fuel generalizing current remaining kept with
    | zero => rfl
    | succ fuel ih =>
        cases remaining with
        | nil => rfl
        | cons group rest =>
            unfold State.pruneEmptyGroups.go
            split
            · exact ih _ _ _
            · split
              · exact ih _ _ _
              · exact ih _ _ _
  exact loop _ queue groups []

/-- Pruning preserves every initial registered task's live contributor links. -/
theorem State.InitialTaskLinks.pruneEmptyGroups
    {queue : State} (links : queue.InitialTaskLinks)
    (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.InitialTaskLinks := by
  intro task member
  have old : task ∈ queue.tasks := by
    rw [← queue.pruneEmptyGroups_tasks groups]
    exact member
  exact (links task old).pruneEmptyGroups groups

/-- Integrating all initial groups before their tasks establishes global
registered-task links before any failure can make a shell inert. -/
theorem State.initialWorkTaskLinks (work : Work)
    : (({} : State).maybeIntegrateWork work).1.InitialTaskLinks := by
  let grouped := (({} : State).addGroups work.groups).1
  let tasked := work.tasks.foldl State.addTask grouped
  have groupedEmpty : grouped.tasks = [] := by
    change (({} : State).addGroups work.groups).1.tasks = []
    exact ({} : State).addGroups_tasks work.groups
  have groupedLinks : grouped.InitialTaskLinks := by
    intro task member
    rw [groupedEmpty] at member
    cases member
  have groupedUnique : grouped.GroupRefsUnique := by
    have emptyUnique : ({} : State).GroupRefsUnique := by
      simp [State.GroupRefsUnique]
    exact emptyUnique.addGroups work.groups
  have taskFold (more : List Task) :
      ∀ current, current.GroupRefsUnique → current.InitialTaskLinks
        → (more.foldl State.addTask current).InitialTaskLinks := by
    induction more with
    | nil => intro current _ links; exact links
    | cons task rest ih =>
        intro current unique links
        exact ih (current.addTask task) (unique.addTask task)
          (links.addTask unique task)
  have taskedLinks : tasked.InitialTaskLinks :=
    taskFold work.tasks grouped groupedUnique groupedLinks
  change (tasked.addStreams work.streams none).1.InitialTaskLinks
  exact taskedLinks.addStreams work.streams none

/-- Initially started tasks are linked to every active root contributor.
Failure/reintroduction later requires the narrower active invariant. -/
private theorem createWorkQueue_activeTaskLinks (work : Work)
    : (State.initialize work).ActiveTaskLinks := by
  let integrated := (({} : State).maybeIntegrateWork work).1
  let newWork := (({} : State).maybeIntegrateWork work).2
  let pruned := (integrated.pruneEmptyGroups newWork.newGroups).1
  let groups := (integrated.pruneEmptyGroups newWork.newGroups).2
  let roots := { newWork with newGroups := groups }
  let started := pruned.startNewWork roots
  have integratedLinks : integrated.InitialTaskLinks :=
    State.initialWorkTaskLinks work
  have prunedLinks : pruned.InitialTaskLinks :=
    integratedLinks.pruneEmptyGroups newWork.newGroups
  have emptyRegistered : ({} : State).StartedTasksRegistered := by
    intro node member
    cases member
  have registered : pruned.StartedTasksRegistered :=
    (emptyRegistered.maybeIntegrateWork work).pruneEmptyGroups newWork.newGroups
  have ready : pruned.ReleaseTaskLinks roots := by
    intro task taskMember node nodeMember _ _ refMember
    exact prunedLinks task taskMember node nodeMember refMember
  have startedLinks : started.ActiveTaskLinks :=
    State.ActiveTaskLinks.startNewWork registered roots ready
  change State.ActiveTaskLinks
    { started with initialGroups := groups, initialStreams := roots.newStreams }
  exact startedLinks

/-- Replacing the mutable value or stream slots of a started task leaves its
contributor links unchanged. -/
theorem State.ActiveTaskLinks.putTaskNodeSameTask
    {queue : State} (links : queue.ActiveTaskLinks)
    (source : TaskNode) (sourceMember : source ∈ queue.taskNodes)
    (updated : TaskNode) (sameTask : updated.task = source.task)
    : (queue.putTaskNode updated).ActiveTaskLinks := by
  intro node member
  change node ∈ queue.taskNodes.map
    (fun old => if old.task.occurrence == updated.task.occurrence then
      updated else old) at member
  obtain ⟨old, oldMember, same⟩ := List.mem_map.mp member
  split at same
  · subst node
    rw [sameTask]
    exact links source sourceMember
  · subst node
    exact links old oldMember

/-- Updating a unique group node's pending count leaves task links intact. -/
theorem State.ActiveTaskLinks.putGroupNodeSameTasks
    {queue : State} (unique : queue.GroupRefsUnique)
    (links : queue.ActiveTaskLinks)
    (node : GroupNode) (member : node ∈ queue.groupNodes)
    (updated : GroupNode)
    (sameRef : updated.group.node.ref = node.group.node.ref)
    (sameTasks : updated.tasks = node.tasks)
    : (queue.putGroupNode updated).ActiveTaskLinks := by
  intro taskNode taskMember
  have old : taskNode ∈ queue.taskNodes := taskMember
  have fixed := (links taskNode old).activeRefs
  have updatedLinks := fixed.putGroupNodeSameTasks unique node member updated
    sameRef sameTasks
  exact updatedLinks.ofActiveRefs rfl

/-- Decrementing the pending counters of several contributing groups never
changes the active task-membership links. -/
theorem State.ActiveTaskLinks.settleTaskGroups
    {queue : State} (unique : queue.GroupRefsUnique)
    (links : queue.ActiveTaskLinks)
    (groups : List Execution.DeliveryNode)
    : (groups.foldl
        (fun current group =>
          match current.groupNode? group.ref with
          | none => current
          | some node => current.putGroupNode { node with pending := node.pending - 1 })
        queue).ActiveTaskLinks := by
  let step (current : State) (group : Execution.DeliveryNode) : State :=
    match current.groupNode? group.ref with
    | none => current
    | some node => current.putGroupNode { node with pending := node.pending - 1 }
  have stepFacts (current : State) (group : Execution.DeliveryNode)
      (currentUnique : current.GroupRefsUnique)
      (currentLinks : current.ActiveTaskLinks)
      : (step current group).GroupRefsUnique
        ∧ (step current group).ActiveTaskLinks := by
    unfold step
    split
    · exact ⟨currentUnique, currentLinks⟩
    · rename_i node found
      have member := List.mem_of_find?_eq_some found
      exact ⟨currentUnique.putGroupNode _,
        currentLinks.putGroupNodeSameTasks currentUnique node member
          { node with pending := node.pending - 1 } rfl rfl⟩
  have foldFacts (more : List Execution.DeliveryNode) :
      ∀ current, current.GroupRefsUnique → current.ActiveTaskLinks
        → (more.foldl step current).ActiveTaskLinks := by
    induction more with
    | nil => intro current _ currentLinks; exact currentLinks
    | cons group rest ih =>
        intro current currentUnique currentLinks
        obtain ⟨nextUnique, nextLinks⟩ :=
          stepFacts current group currentUnique currentLinks
        exact ih (step current group) nextUnique nextLinks
  exact foldFacts groups queue unique links

/-- Stream registration changes only stream records and a producing task's
child-stream list, never its contributor links. -/
theorem State.ActiveTaskLinks.addStreams
    {queue : State} (links : queue.ActiveTaskLinks)
    (streams : List Stream) (parentTask : Option Occurrence)
    : (queue.addStreams streams parentTask).1.ActiveTaskLinks := by
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
  have currentLinks : current.ActiveTaskLinks := links
  cases parentTask with
  | none => exact currentLinks
  | some occurrence =>
      simp only [State.addStreams]
      split
      · exact currentLinks
      · rename_i node found
        have member : node ∈ current.taskNodes :=
          List.mem_of_find?_eq_some found
        exact currentLinks.putTaskNodeSameTask node member
          { node with childStreams := node.childStreams ++
              fresh.map (fun stream => stream.node.ref) } rfl

/-- Group integration updates group nodes only; it cannot start a task until
the subsequent task-registration phase. -/
theorem State.addGroups_taskNodes (queue : State) (groups : List Group)
    : (queue.addGroups groups).1.taskNodes = queue.taskNodes := by
  let linkStep (current : State) (group : Group) : State :=
    match group.parent with
    | none => current
    | some parent =>
        match current.groupNode? parent with
        | none => current
        | some node =>
            let children :=
              if node.childGroups.contains group.node.ref then
                node.childGroups
              else
                node.childGroups ++ [group.node.ref]
            current.putGroupNode { node with childGroups := children }
  have registerStep (current : State) (group : Group) :
      (current.addGroup group).taskNodes = current.taskNodes := by
    unfold State.addGroup
    split
    · rfl
    · split <;> rfl
  have registerFold (more : List Group) :
      ∀ current, (more.foldl State.addGroup current).taskNodes
        = current.taskNodes := by
    induction more with
    | nil => intro current; rfl
    | cons group rest ih =>
        intro current
        simp only [List.foldl_cons, ih, registerStep]
  have linkStepNodes (current : State) (group : Group) :
      (linkStep current group).taskNodes = current.taskNodes := by
    unfold linkStep
    split
    · rfl
    · split <;> rfl
  have linkFold (more : List Group) :
      ∀ current, (more.foldl linkStep current).taskNodes
        = current.taskNodes := by
    induction more with
    | nil => intro current; rfl
    | cons group rest ih =>
        intro current
        simp only [List.foldl_cons, ih, linkStepNodes]
  let fresh := groups.filter (fun group =>
    !queue.registeredGroups.contains group.node.ref
      && (queue.groupNode? group.node.ref).isNone)
  change (fresh.foldl linkStep
    (fresh.foldl State.addGroup queue)).taskNodes = queue.taskNodes
  rw [linkFold, registerFold]

/-- New, not-yet-started group shells do not break the root links of started
tasks. The root-presence premise excludes orphaned active groups.
-/
theorem State.ActiveTaskLinks.addGroups
    {queue : State} (unique : queue.GroupRefsUnique)
    (rootsPresent : queue.RootGroupsPresent)
    (links : queue.ActiveTaskLinks) (groups : List Group)
    : (queue.addGroups groups).1.ActiveTaskLinks := by
  intro taskNode member
  have old : taskNode ∈ queue.taskNodes := by
    rw [queue.addGroups_taskNodes groups] at member
    exact member
  have preserved := (links taskNode old).maybeIntegrateWork unique rootsPresent
    { groups } none
  simpa [State.maybeIntegrateWork, State.addStreams] using preserved

/-- Task registration preserves all old active links and establishes the new
task's links to every live contributor group.
-/
theorem State.ActiveTaskLinks.addTask
    {queue : State} (unique : queue.GroupRefsUnique)
    (links : queue.ActiveTaskLinks) (task : Task)
    : (queue.addTask task).ActiveTaskLinks := by
  intro taskNode member
  rcases queue.addTask_startedOldOrNew task member with old | new
  · exact (links taskNode old).addTask unique task
  · subst taskNode
    intro groupNode groupMember _ refMember
    exact queue.addTask_links unique task groupNode groupMember refMember

/-- Integrating child Work preserves links for old started tasks and every
new task started under an already active root group.
-/
theorem State.ActiveTaskLinks.maybeIntegrateWork
    {queue : State} (unique : queue.GroupRefsUnique)
    (rootsPresent : queue.RootGroupsPresent)
    (links : queue.ActiveTaskLinks)
    (newWork : Work) (parentTask : Option Occurrence)
    : (queue.maybeIntegrateWork newWork parentTask).1.ActiveTaskLinks := by
  let withGroups := (queue.addGroups newWork.groups).1
  let withTasks := newWork.tasks.foldl State.addTask withGroups
  have groupLinks : withGroups.ActiveTaskLinks :=
    links.addGroups unique rootsPresent newWork.groups
  have groupUnique : withGroups.GroupRefsUnique := unique.addGroups newWork.groups
  have taskFold (tasks : List Task) :
      ∀ current, current.GroupRefsUnique
        → current.ActiveTaskLinks
        → (tasks.foldl State.addTask current).ActiveTaskLinks := by
    induction tasks with
    | nil => intro current _ currentLinks; exact currentLinks
    | cons task rest ih =>
        intro current currentUnique currentLinks
        exact ih (current.addTask task) (currentUnique.addTask task)
          (State.ActiveTaskLinks.addTask currentUnique currentLinks task)
  have taskLinks : withTasks.ActiveTaskLinks :=
    taskFold newWork.tasks withGroups groupUnique groupLinks
  change (withTasks.addStreams newWork.streams parentTask).1.ActiveTaskLinks
  exact taskLinks.addStreams newWork.streams parentTask

/-- Removing one task node and its group memberships preserves the active
links of every other task node that remains started.
-/
theorem State.ActiveTaskLinks.removeTask
    {queue : State} (links : queue.ActiveTaskLinks)
    (removed : Occurrence)
    : (queue.removeTask removed).ActiveTaskLinks := by
  intro taskNode member
  have old : taskNode ∈ queue.taskNodes := (List.mem_filter.mp member).1
  have different : taskNode.task.occurrence ≠ removed := by
    intro same
    have kept := (List.mem_filter.mp member).2
    simp only [same] at kept
    have equalBool : (removed == removed) = true :=
      (occurrence_beq_iff_eq _ _).mpr rfl
    simp [bne, equalBool] at kept
  have static := (links taskNode old).activeRefs
  have afterStatic := static.removeOtherTask removed different
  exact afterStatic.ofActiveRefs rfl

/-- Pruning removes group nodes only; active links of surviving task nodes
remain valid even if a separate invariant must show roots still have nodes.
-/
theorem State.ActiveTaskLinks.pruneEmptyGroups
    {queue : State} (links : queue.ActiveTaskLinks)
    (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.ActiveTaskLinks := by
  have loop (fuel : Nat) (current : State)
      (remaining kept : List Execution.DeliveryNode)
      (currentLinks : current.ActiveTaskLinks)
      : (State.pruneEmptyGroups.go fuel current remaining kept).1.ActiveTaskLinks := by
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
                intro taskNode taskMember groupNode groupMember rootMember refMember
                exact currentLinks taskNode taskMember groupNode
                  (List.mem_filter.mp groupMember).1 rootMember refMember
              · exact ih _ _ _ currentLinks
  exact loop _ queue groups [] links

/-- A group flush removes completed task nodes and the group being closed;
it does not disturb links belonging to surviving started tasks.
-/
theorem State.ActiveTaskLinks.finishGroupSuccess
    {queue : State} (links : queue.ActiveTaskLinks) (group : GroupNode)
    : (queue.finishGroupSuccess group).1.ActiveTaskLinks := by
  let step (acc : State × List ExecutionGroupValue × NodeRefs)
      (task : Occurrence) :=
    let (current, values, streams) := acc
    match current.taskNode? task with
    | none => (current, values, streams)
    | some taskNode =>
        let values :=
          match taskNode.value with
          | none => values
          | some value => values ++ [value]
        (current.removeTask task, values, streams ++ taskNode.childStreams)
  have stepLinks (acc : State × List ExecutionGroupValue × NodeRefs)
      (task : Occurrence) (currentLinks : acc.1.ActiveTaskLinks)
      : (step acc task).1.ActiveTaskLinks := by
    obtain ⟨current, values, streams⟩ := acc
    dsimp only [step]
    split
    · exact currentLinks
    · exact currentLinks.removeTask task
  have foldLinks (tasks : List Occurrence) :
      ∀ acc : State × List ExecutionGroupValue × NodeRefs,
        acc.1.ActiveTaskLinks
          → (tasks.foldl step acc).1.ActiveTaskLinks := by
    induction tasks with
    | nil => intro acc currentLinks; exact currentLinks
    | cons task rest ih =>
        intro acc currentLinks
        exact ih (step acc task) (stepLinks acc task currentLinks)
  let flushed := (group.tasks.foldl step (queue, [], [])).1
  have flushedLinks : flushed.ActiveTaskLinks :=
    foldLinks group.tasks (queue, [], []) links
  let current : State :=
    { flushed with
        groupNodes := flushed.groupNodes.filter
          (fun node => node.group.node.ref != group.group.node.ref)
        rootGroups := flushed.rootGroups.filter (· != group.group.node.ref) }
  have currentLinks : current.ActiveTaskLinks := by
    intro taskNode taskMember groupNode groupMember rootMember refMember
    exact flushedLinks taskNode taskMember groupNode
      (List.mem_filter.mp groupMember).1
      (List.mem_filter.mp rootMember).1 refMember
  let children := group.childGroups.filterMap
    (fun ref => (current.groupNode? ref).map (fun node => node.group.node))
  change (current.pruneEmptyGroups children).1.ActiveTaskLinks
  exact currentLinks.pruneEmptyGroups children

/-- Failure preserves the active links of every started task that survives. -/
theorem State.ActiveTaskLinks.taskFailure
    {queue : State} (links : queue.ActiveTaskLinks)
    (failed : Occurrence) (errors : Nat)
    : (queue.taskFailure failed errors).1.ActiveTaskLinks := by
  intro taskNode member
  obtain ⟨original, different⟩ := queue.taskFailure_startedSurvivor failed errors member
  exact (links taskNode original).taskFailure failed errors different

/-- Finishing any zero-pending contributor preserves links of task nodes that
remain started in surviving groups. -/
theorem State.ActiveTaskLinks.releaseTaskGroups
    {queue : State} (links : queue.ActiveTaskLinks)
    (groups : List Execution.DeliveryNode)
    : (groups.foldl
        (fun (acc : State × List WorkQueueEvent × NewWork) group =>
          let (current, events, released) := acc
          match current.groupNode? group.ref with
          | none => (current, events, released)
          | some node =>
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
                (current, events, released))
        (queue, [], {})).1.ActiveTaskLinks := by
  let step (acc : State × List WorkQueueEvent × NewWork)
      (group : Execution.DeliveryNode) : State × List WorkQueueEvent × NewWork :=
    let (current, events, released) := acc
    match current.groupNode? group.ref with
    | none => (current, events, released)
    | some node =>
        if current.rootGroups.contains group.ref && node.pending == 0 then
          let (next, finished, newWork) := current.finishGroupSuccess node
          (next, events ++ finished,
            ⟨released.newGroups ++ newWork.newGroups,
              released.newStreams ++ newWork.newStreams⟩)
        else
          (current, events, released)
  have stepLinks (acc : State × List WorkQueueEvent × NewWork)
      (group : Execution.DeliveryNode)
      (currentLinks : acc.1.ActiveTaskLinks)
      : (step acc group).1.ActiveTaskLinks := by
    obtain ⟨current, events, released⟩ := acc
    dsimp only [step]
    split
    · exact currentLinks
    · split
      · exact currentLinks.finishGroupSuccess _
      · exact currentLinks
  have foldLinks (more : List Execution.DeliveryNode) :
      ∀ acc : State × List WorkQueueEvent × NewWork,
        acc.1.ActiveTaskLinks
          → (more.foldl step acc).1.ActiveTaskLinks := by
    induction more with
    | nil => intro acc currentLinks; exact currentLinks
    | cons group rest ih =>
        intro acc currentLinks
        exact ih (step acc group) (stepLinks acc group currentLinks)
  exact foldLinks groups (queue, [], {}) links

/-- The first success-release boundary has active task links when its requests are
linked. Witness: forward registration preservation through the owner fold and activation.
This local boundary lemma does not cover later recursive drain releases.
-/
theorem State.ActiveTaskLinks.taskSuccess_release
    {queue : State}
    (registered : queue.StartedTasksRegistered)
    (occurrence : Occurrence) (result : TaskResult)
    (taskNode : TaskNode) (found : queue.taskNode? occurrence = some taskNode)
    (releasedReady
      : let withValue := queue.putTaskNode { taskNode with value := some result.value }
        let integrated := (withValue.maybeIntegrateWork result.work (some occurrence)).1
        let released := taskNode.task.groups.foldl successGroupStep (integrated, [], {})
        released.1.ReleaseTaskLinks released.2.2)
    : let withValue := queue.putTaskNode { taskNode with value := some result.value }
      let integrated := (withValue.maybeIntegrateWork result.work (some occurrence)).1
      let released := taskNode.task.groups.foldl successGroupStep (integrated, [], {})
      (released.1.startNewWork released.2.2).ActiveTaskLinks := by
  have stored := registered.putTaskNode { taskNode with value := some result.value }
    (registered taskNode (List.mem_of_find?_eq_some found))
  have integrated := stored.maybeIntegrateWork result.work (some occurrence)
  have released := State.StartedTasksRegistered.successGroupFold
    taskNode.task.groups (_, [], {}) integrated
  exact State.ActiveTaskLinks.startNewWork released _ releasedReady

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
