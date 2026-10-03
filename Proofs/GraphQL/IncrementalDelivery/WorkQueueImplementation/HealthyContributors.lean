import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.HealthyPending
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CancellationRegistration

/-! Healthy contributor presence, task links, and release. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (ExecutionGroupValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- During a shared-task settlement, each uninvalidated group has its own
temporary settlement coordinate until all owner refs have been visited. -/
def State.HealthyPendingTracksByGroup (queue : State) (work : Execution.Work)
    (settled : Nat → List Occurrence) (failed : List Occurrence)
    : Prop :=
  ∀ node ∈ queue.groupNodes,
    ¬GroupInvalidated work failed node.group.node.ref
    → node.PendingTracks (settled node.group.node.ref)

/-- A healthy group's stored task membership agrees with the settled task's
contributor refs, including latent groups. -/
def State.HealthyOwnedExactlyBy (queue : State) (work : Execution.Work)
    (failed : List Occurrence) (occurrence : Occurrence) (refs : NodeRefs)
    : Prop :=
  ∀ node ∈ queue.groupNodes,
    ¬GroupInvalidated work failed node.group.node.ref
    → (occurrence ∈ node.tasks ↔ node.group.node.ref ∈ refs)

/-- Every unsettled started task is linked to each uninvalidated group in its
contributor list. The success-only ledger need not track removed failed-task links. -/
def State.HealthyTaskLinks (queue : State) (work : Execution.Work)
    (settled failed : List Occurrence)
    : Prop :=
  ∀ taskNode ∈ queue.taskNodes,
    taskNode.task.occurrence ∉ settled
    → ∀ groupNode ∈ queue.groupNodes,
        ¬GroupInvalidated work failed groupNode.group.node.ref
        → groupNode.group.node.ref ∈ taskNode.task.groups.map Execution.DeliveryNode.ref
        → taskNode.task.occurrence ∈ groupNode.tasks

/-- An unsettled started task retains each uninvalidated contributor's
live group node. This separates existence from membership in that node. -/
def State.HealthyContributorGroupsPresent (queue : State) (work : Execution.Work)
    (settled failed : List Occurrence)
    : Prop :=
  ∀ taskNode ∈ queue.taskNodes,
    taskNode.task.occurrence ∉ settled
    → ∀ ref ∈ taskNode.task.groups.map Execution.DeliveryNode.ref,
        ¬GroupInvalidated work failed ref
        → ∃ node ∈ queue.groupNodes, node.group.node.ref = ref

/-- A registered, unsettled task has a live membership in every healthy
contributor group, even before the task node is started. This one invariant
implies the two started-task facts and both release conditions. -/
def State.HealthyRegisteredTaskAccounting (queue : State) (work : Execution.Work)
    (settled failed : List Occurrence)
    : Prop :=
  ∀ task ∈ queue.tasks,
    task.occurrence ∉ settled
    → ∀ ref ∈ task.groups.map Execution.DeliveryNode.ref,
        ¬GroupInvalidated work failed ref
        → ∃ node ∈ queue.groupNodes,
            node.group.node.ref = ref ∧ task.occurrence ∈ node.tasks

/-- Registered-task accounting implies contributor presence for started
tasks when every started descriptor remains in the task registry. -/
private theorem State.HealthyRegisteredTaskAccounting.toStartedPresence
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (accounted : queue.HealthyRegisteredTaskAccounting work settled failed)
    (registered : queue.StartedTasksRegistered)
    : queue.HealthyContributorGroupsPresent work settled failed := by
  intro taskNode taskMember fresh ref contributor healthy
  obtain ⟨node, member, same, _⟩ :=
    accounted taskNode.task (registered taskNode taskMember)
      fresh ref contributor healthy
  exact ⟨node, member, same⟩

/-- The same registered-task invariant also supplies all healthy group links
of started tasks. -/
private theorem State.HealthyRegisteredTaskAccounting.toStartedLinks
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (accounted : queue.HealthyRegisteredTaskAccounting work settled failed)
    (registered : queue.StartedTasksRegistered)
    (unique : queue.GroupRefsUnique)
    : queue.HealthyTaskLinks work settled failed := by
  intro taskNode taskMember fresh groupNode groupMember healthy contributor
  obtain ⟨node, member, same, linked⟩ :=
    accounted taskNode.task (registered taskNode taskMember)
      fresh groupNode.group.node.ref contributor healthy
  have equal : node = groupNode :=
    unique.sameNode member groupMember same
  exact equal ▸ linked

/-- Immediate lowering installs each task's contributor group in the same
Work collection as the task, before queue initialization registers tasks. -/
theorem workFromSpec_immediateGroupsCoverTasks (work : Execution.Work) (address : Address)
    : ∀ task ∈ (Work.fromExecution work address).tasks,
      ∀ ref ∈ task.groups.map Execution.DeliveryNode.ref,
        ∃ group ∈ (Work.fromExecution work address).groups, group.node.ref = ref := by
  cases work with
  | empty => simp [Work.fromExecution]
  | combine left right =>
      intro task member ref contributor
      simp only [Work.fromExecution, Work.combine, List.mem_append] at member ⊢
      rcases member with inLeft | inRight
      · obtain ⟨group, groupMember, same⟩ :=
          workFromSpec_immediateGroupsCoverTasks left (address ++ [0])
            task inLeft ref contributor
        exact ⟨group, Or.inl groupMember, same⟩
      · obtain ⟨group, groupMember, same⟩ :=
          workFromSpec_immediateGroupsCoverTasks right (address ++ [1])
            task inRight ref contributor
        exact ⟨group, Or.inr groupMember, same⟩
  | executionGroup fragments path result children =>
      intro task member ref contributor
      simp only [Work.fromExecution, List.mem_singleton] at member
      subst task
      simp only [List.map_map, Function.comp_def] at contributor
      obtain ⟨fragment, fragmentMember, fragmentRef⟩ :=
        List.mem_map.mp contributor
      let group : Group :=
        ⟨fragment.node, fragment.ancestors.head?.map Execution.DeliveryNode.ref⟩
      have groupMember : group ∈ (Work.fromExecution
          (.executionGroup fragments path result children) address).groups := by
        exact List.mem_flatMap.mpr
          ⟨fragment, fragmentMember, workFromSpec_groupChain_self _ _⟩
      exact ⟨group, groupMember, fragmentRef⟩
  | stream node items => simp [Work.fromExecution]
termination_by sizeOf work
decreasing_by
  all_goals simp_wf
  all_goals subst work
  all_goals simp [sizeOf, Execution.Work._sizeOf_1]
  all_goals omega

/-- A matched task-success event releases a lowered child Work chunk whose
tasks all have their contributor groups registered in that same chunk. -/
theorem GraphEvent.MatchesWork.childTasksCovered
    {work : Execution.Work} {occurrence : Occurrence} {result : TaskResult}
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    : ∀ task ∈ result.work.tasks,
      ∀ ref ∈ task.groups.map Execution.DeliveryNode.ref,
        ∃ group ∈ result.work.groups, group.node.ref = ref := by
  obtain ⟨owners, producer, known, _, childrenWork⟩ := matching
  cases occurrence with
  | item address index =>
      simp only [taskChildWork?] at childrenWork
      cases childrenWork
  | executionGroup address =>
      obtain ⟨groups, path, outcome, children, enclosing,
        located, _, _⟩ := known
      change locateWork work address = some
        ⟨.executionGroup groups path outcome children, producer, enclosing⟩
        at located
      have childLowering : result.work =
          Work.fromExecution children (address ++ [0]) := by
        simpa [taskChildWork?, located] using childrenWork.symm
      rw [childLowering]
      exact workFromSpec_immediateGroupsCoverTasks children (address ++ [0])

/-- Each matched stream item's child Work registers the contributor groups
of every child task before the queue activates the item. -/
theorem GraphEvent.MatchesWork.streamItem_childTasksCovered
    {work : Execution.Work} {stream : Execution.DeliveryNode} {items : List StreamItem}
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    {item : StreamItem} (itemMember : item ∈ items)
    : ∀ task ∈ item.work.tasks,
      ∀ ref ∈ task.groups.map Execution.DeliveryNode.ref,
        ∃ group ∈ item.work.groups, group.node.ref = ref := by
  cases item with
  | mk itemOccurrence itemValue itemWork =>
      obtain ⟨owners, producer, known, childrenWork⟩ := matching _ itemMember
      cases itemOccurrence with
      | executionGroup address =>
          simp only [streamItemWork?] at childrenWork
          cases childrenWork
      | item address index =>
          obtain ⟨node, entries, enclosing, result, children, located, entry,
            _, _⟩ := known
          change locateWork work address = some
            ⟨.stream node entries, producer, enclosing⟩ at located
          have childLowering : itemWork =
              Work.fromExecution children (address ++ [index]) := by
            simpa [streamItemWork?, located, entry] using childrenWork.symm
          rw [childLowering]
          exact workFromSpec_immediateGroupsCoverTasks children (address ++ [index])

/-- A group can participate in registration when it is already live or its ref has
never been registered. Retired refs deliberately do not satisfy this predicate. -/
def State.GroupAvailable (queue : State) (ref : NodeRef) : Prop :=
  ref ∈ queue.groupNodes.map (fun node => node.group.node.ref)
  ∨ ref ∉ queue.registeredGroups

/-- Unavailable refs are exactly retired refs, not merely absent live nodes.
Witness: the two alternatives of availability and the permanent-registry definition. -/
theorem State.groupUnavailable_iff_retired (queue : State) (ref : NodeRef)
    : ¬queue.GroupAvailable ref ↔ queue.RetiredGroup ref := by
  classical
  simp [State.GroupAvailable, State.RetiredGroup, not_or, and_comm]

/-- A future replay cannot make a retired contributor available again.
Witness: retirement preservation, used contrapositively. This connects the general
implementation invariant to the remaining healthy-registration proof obligation.
-/
theorem State.GroupAvailable.beforeReplay {queue : State} {ref : NodeRef}
    (batches : List (List GraphEvent))
    (available : (queue.runNormalized batches).1.GroupAvailable ref)
    : queue.GroupAvailable ref := by
  classical
  by_cases initial : queue.GroupAvailable ref
  · exact initial
  · have retired := (queue.groupUnavailable_iff_retired ref).mp initial
    exact False.elim
      (((queue.runNormalized batches).1.groupUnavailable_iff_retired ref).mpr
        (retired.runNormalized batches) available)

/-- Each healthy contributor of a newly integrated task is live or never registered.
This is a proof obligation for the concrete replay, not a host-source assumption. -/
def State.ChildGroupsAvailable (queue : State) (work : Execution.Work)
    (failed : List Occurrence) (newWork : Work)
    : Prop :=
  ∀ task ∈ newWork.tasks,
  ∀ ref ∈ task.groups.map Execution.DeliveryNode.ref,
    ¬GroupInvalidated work failed ref → queue.GroupAvailable ref

/-- Registering a candidate preserves availability unless the ref is cancelled.
Witness: an uncancelled fresh ref either stays fresh or acquires its live node. -/
private theorem State.GroupAvailable.addGroup {queue : State} {ref : NodeRef}
    (available : queue.GroupAvailable ref) (group : Group)
    (uncancelled : ref ∉ (queue.addGroup group).cancelledGroups)
    : (queue.addGroup group).GroupAvailable ref := by
  unfold State.addGroup
  split
  · exact available
  · rename_i freshGroup
    split
    · rename_i blocked
      have different : ref ≠ group.node.ref := by
        intro same
        simp only [State.addGroup, freshGroup, blocked, ite_true] at uncancelled
        exact uncancelled (List.mem_append_right _ (by simp [same]))
      rcases available with live | fresh
      · exact Or.inl live
      · exact Or.inr (by simpa using And.intro fresh different)
    · rcases available with live | fresh
      · exact Or.inl (by simpa only [List.map_append, List.map_cons, List.map_nil] using
          List.mem_append_left [group.node.ref] live)
      · by_cases same : ref = group.node.ref
        · subst ref
          exact Or.inl (by simp)
        · exact Or.inr (by simpa using And.intro fresh same)

/-- An available, uncancelled ref is live after its registration.
Witness: reuse an old live node; refusal would contradict the cancellation exclusion. -/
private theorem State.addGroup_registersRef (queue : State) (group : Group)
    (available : queue.GroupAvailable group.node.ref)
    (uncancelled : group.node.ref ∉ (queue.addGroup group).cancelledGroups)
    : group.node.ref
      ∈ (queue.addGroup group).groupNodes.map (fun node => node.group.node.ref) := by
  unfold State.addGroup
  cases found : queue.groupNode? group.node.ref with
  | some node =>
      simp only [Option.isSome_some, Bool.or_true, ite_true]
      have member : node ∈ queue.groupNodes :=
        List.mem_of_find?_eq_some found
      have same := queue.groupNode?_ref found
      exact List.mem_map.mpr ⟨node, member, same⟩
  | none =>
      have fresh : group.node.ref ∉ queue.registeredGroups := by
        rcases available with live | fresh
        · obtain ⟨node, member, same⟩ := List.mem_map.mp live
          exact False.elim ((List.find?_eq_none.mp found) node member
            (by simpa using same))
        · exact fresh
      simp only [Option.isSome_none, Bool.or_false]
      simp only [show queue.registeredGroups.contains group.node.ref = false by
        simpa using fresh, Bool.false_eq_true, ite_false]
      split
      · rename_i blocked
        have freshCheck : queue.registeredGroups.contains group.node.ref = false := by
          simpa using fresh
        simp only [State.addGroup, freshCheck, found, Option.isSome_none, Bool.or_self,
          Bool.false_eq_true, ite_false, blocked, ite_true] at uncancelled
        exact False.elim (uncancelled (List.mem_append_right _ (by simp)))
      · apply List.mem_map.mpr
        exact ⟨{ group }, List.mem_append.mpr (Or.inr (by simp)), rfl⟩

/-- Available requested refs are live unless the registration batch cancels them.
Witness: cancellation history grows monotonically, and parent linking preserves live refs.
-/
theorem State.addGroups_registersRefs (queue : State) (groups : List Group)
    : ∀ group ∈ groups,
        queue.GroupAvailable group.node.ref
        → group.node.ref ∉ (queue.addGroups groups).1.cancelledGroups
        → group.node.ref
          ∈ (queue.addGroups groups).1.groupNodes.map
              (fun node => node.group.node.ref) := by
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
  have linkStepRefs (current : State) (group : Group) :
      (linkStep current group).groupNodes.map (fun node => node.group.node.ref)
        = current.groupNodes.map (fun node => node.group.node.ref) := by
    unfold linkStep
    split
    · rfl
    · split
      · rfl
      · exact current.putGroupNode_refs _
  have linkFold (more : List Group) :
      ∀ current : State,
        (more.foldl linkStep current).groupNodes.map (fun node => node.group.node.ref)
          = current.groupNodes.map (fun node => node.group.node.ref) := by
    induction more with
    | nil => intro current; rfl
    | cons group rest ih =>
        intro current
        rw [List.foldl_cons, ih, linkStepRefs]
  have registerIncluded (more : List Group) :
      ∀ current : State,
        current.GroupRefsIncluded (more.foldl State.addGroup current) := by
    induction more with
    | nil => intro current ref member; exact member
    | cons group rest ih =>
        intro current
        exact (current.addGroup_includesRefs group).trans
          (ih (current.addGroup group))
  have registerRefs (more : List Group) :
      ∀ current : State, ∀ group ∈ more,
        current.GroupAvailable group.node.ref →
        group.node.ref ∉ (more.foldl State.addGroup current).cancelledGroups →
        group.node.ref ∈ (more.foldl State.addGroup current).groupNodes.map
          (fun node => node.group.node.ref) := by
    induction more with
    | nil => intro current group member; cases member
    | cons first rest ih =>
        intro current group member available uncancelled
        have unblocked : group.node.ref ∉ (current.addGroup first).cancelledGroups := by
          intro member
          exact uncancelled ((current.addGroup first).foldAddGroup_cancelledGroups_subset
            rest member)
        rcases List.mem_cons.mp member with same | later
        · subst group
          exact registerIncluded rest (current.addGroup first) first.node.ref
            (current.addGroup_registersRef first available unblocked)
        · exact ih (current.addGroup first) group later
            (available.addGroup first unblocked) uncancelled
  intro group member available uncancelled
  let fresh := groups.filter (fun group =>
    !queue.registeredGroups.contains group.node.ref
      && (queue.groupNode? group.node.ref).isNone)
  change group.node.ref ∈
    (fresh.foldl linkStep (fresh.foldl State.addGroup queue)).groupNodes.map
      (fun node => node.group.node.ref)
  rw [linkFold]
  rw [State.addGroups_cancelledGroups] at uncancelled
  rcases available with live | new
  · exact registerIncluded fresh queue group.node.ref live
  · cases found : queue.groupNode? group.node.ref with
    | some node =>
        exact registerIncluded fresh queue group.node.ref
          (List.mem_map.mpr ⟨node, List.mem_of_find?_eq_some found,
            queue.groupNode?_ref found⟩)
    | none =>
        have memberFresh : group ∈ fresh := by simp [fresh, member, new, found]
        exact registerRefs fresh queue group memberFresh (Or.inr new) uncancelled

/-- Integration retains every available candidate not cancelled during registration.
Witness: group registration supplies live nodes; task and stream integration retain them.
-/
theorem State.maybeIntegrateWork_registersRefs
    (queue : State) (newWork : Work) (parentTask : Option Occurrence)
    : ∀ group ∈ newWork.groups,
        queue.GroupAvailable group.node.ref
        → group.node.ref ∉ (queue.addGroups newWork.groups).1.cancelledGroups
        → group.node.ref
          ∈ (queue.maybeIntegrateWork newWork parentTask).1.groupNodes.map
              (fun node => node.group.node.ref) := by
  let withGroups := (queue.addGroups newWork.groups).1
  let withTasks := newWork.tasks.foldl State.addTask withGroups
  have taskFold (more : List Task) :
      ∀ current : State,
        current.GroupRefsIncluded (more.foldl State.addTask current) := by
    induction more with
    | nil => intro current ref member; exact member
    | cons task rest ih =>
        intro current
        exact (current.addTask_includesRefs task).trans
          (ih (current.addTask task))
  have taskIncluded : withGroups.GroupRefsIncluded withTasks :=
    taskFold newWork.tasks withGroups
  have streamIncluded : withTasks.GroupRefsIncluded
      (withTasks.addStreams newWork.streams parentTask).1 := by
    intro ref member
    unfold State.addStreams
    split
    · exact member
    · dsimp
      split <;> exact member
  intro group member available uncancelled
  change group.node.ref ∈
    (withTasks.addStreams newWork.streams parentTask).1.groupNodes.map
      (fun node => node.group.node.ref)
  exact (taskIncluded.trans streamIncluded) group.node.ref
    (queue.addGroups_registersRefs newWork.groups group member available uncancelled)

/-- Integrating immediate Work appends precisely its task descriptors. -/
theorem State.maybeIntegrateWork_tasks_append
    (queue : State) (newWork : Work) (parentTask : Option Occurrence)
    : (queue.maybeIntegrateWork newWork parentTask).1.tasks
      = queue.tasks ++ newWork.tasks := by
  have taskFold (more : List Task) :
      ∀ current : State,
        (more.foldl State.addTask current).tasks = current.tasks ++ more := by
    induction more with
    | nil => intro current; simp
    | cons task rest ih =>
        intro current
        rw [List.foldl_cons, ih, State.addTask_tasks]
        simp [List.append_assoc]
  let withGroups := (queue.addGroups newWork.groups).1
  let withTasks := newWork.tasks.foldl State.addTask withGroups
  change (withTasks.addStreams newWork.streams parentTask).1.tasks
      = queue.tasks ++ newWork.tasks
  rw [State.addStreams_tasks, taskFold, State.addGroups_tasks]

/-- Immediately integrated root tasks have every contributor group live,
provided the Work chunk lists those groups beside the tasks. -/
theorem initialIntegration_taskGroupsPresent
    (work : Work)
    (covered
      : ∀ task ∈ work.tasks,
        ∀ ref ∈ task.groups.map Execution.DeliveryNode.ref,
          ∃ group ∈ work.groups, group.node.ref = ref)
    : ∀ task ∈ (({} : State).maybeIntegrateWork work).1.tasks,
      ∀ ref ∈ task.groups.map Execution.DeliveryNode.ref,
        ∃ node ∈ (({} : State).maybeIntegrateWork work).1.groupNodes,
          node.group.node.ref = ref := by
  intro task member ref contributor
  have taskMember : task ∈ work.tasks := by
    rw [State.maybeIntegrateWork_tasks_append] at member
    simpa using member
  obtain ⟨group, groupMember, same⟩ :=
    covered task taskMember ref contributor
  have refMember := ({} : State).maybeIntegrateWork_registersRefs
    work none group groupMember (Or.inr (by simp))
    (by rw [State.addGroups_cancelledGroups_empty rfl]; simp)
  rw [same] at refMember
  obtain ⟨node, nodeMember, nodeRef⟩ := List.mem_map.mp refMember
  exact ⟨node, nodeMember, nodeRef⟩

/-- Contributor presence discharges the only old-task condition needed when
new child groups are integrated. -/
theorem State.HealthyContributorGroupsPresent.relevantExisting
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (present : queue.HealthyContributorGroupsPresent work settled failed)
    (groups : List Group)
    : ∀ taskNode ∈ queue.taskNodes,
        taskNode.task.occurrence ∉ settled
        → ∀ group ∈ groups,
            group.node.ref ∈ taskNode.task.groups.map Execution.DeliveryNode.ref
            → ¬GroupInvalidated work failed group.node.ref
            → ∃ node ∈ queue.groupNodes, node.group.node.ref = group.node.ref := by
  intro taskNode member fresh group _ contributor healthy
  exact present taskNode member fresh group.node.ref contributor healthy

/-- Group integration retains every node required by an older started task. -/
theorem State.HealthyContributorGroupsPresent.addGroups
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (present : queue.HealthyContributorGroupsPresent work settled failed)
    (groups : List Group)
    : (queue.addGroups groups).1.HealthyContributorGroupsPresent work settled failed := by
  intro taskNode taskMember fresh ref contributor healthy
  have oldTask : taskNode ∈ queue.taskNodes := by
    rw [queue.addGroups_taskNodes groups] at taskMember
    exact taskMember
  obtain ⟨node, oldNode, same⟩ := present taskNode oldTask fresh ref contributor healthy
  have refMember : ref ∈ queue.groupNodes.map
      (fun node => node.group.node.ref) :=
    List.mem_map.mpr ⟨node, oldNode, same⟩
  obtain ⟨next, nextMember, nextRef⟩ := List.mem_map.mp
    (queue.addGroups_includesRefs groups ref refMember)
  exact ⟨next, nextMember, nextRef⟩

/-- Updating one started task's mutable value preserves its contributor
descriptors and the live group map. -/
theorem State.HealthyContributorGroupsPresent.putTaskNodeSameTask
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (present : queue.HealthyContributorGroupsPresent work settled failed)
    (source : TaskNode) (sourceMember : source ∈ queue.taskNodes)
    (updated : TaskNode) (sameTask : updated.task = source.task)
    : (queue.putTaskNode updated).HealthyContributorGroupsPresent
        work settled failed := by
  intro taskNode member fresh ref contributor healthy
  change taskNode ∈ queue.taskNodes.map
    (fun old => if old.task.occurrence == updated.task.occurrence then
      updated else old) at member
  obtain ⟨old, oldMember, same⟩ := List.mem_map.mp member
  split at same
  · subst taskNode
    rw [sameTask] at fresh contributor
    exact present source sourceMember fresh ref contributor healthy
  · subst taskNode
    exact present old oldMember fresh ref contributor healthy

/-- Stream integration changes no live groups and only updates the producing
task's child-stream list. -/
theorem State.HealthyContributorGroupsPresent.addStreams
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (present : queue.HealthyContributorGroupsPresent work settled failed)
    (streams : List Stream) (parentTask : Option Occurrence)
    : (queue.addStreams streams parentTask).1.HealthyContributorGroupsPresent
        work settled failed := by
  let fresh :=
    streams.foldl
      (fun selected stream =>
        if (queue.stream? stream.node.ref).isSome
            || selected.any (fun known => known.node.ref == stream.node.ref) then
          selected
        else selected ++ [stream])
      []
  let current : State := { queue with streams := queue.streams ++ fresh }
  have currentPresent : current.HealthyContributorGroupsPresent
      work settled failed := present
  cases parentTask with
  | none => exact currentPresent
  | some occurrence =>
      simp only [State.addStreams]
      split
      · exact currentPresent
      · rename_i node found
        have member : node ∈ current.taskNodes :=
          List.mem_of_find?_eq_some found
        exact currentPresent.putTaskNodeSameTask node member
          { node with childStreams := node.childStreams ++
              fresh.map (fun stream => stream.node.ref) } rfl

/-- A newly started task has contributor nodes when they were already
registered before its task descriptor was installed. -/
theorem State.HealthyContributorGroupsPresent.addTask
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (present : queue.HealthyContributorGroupsPresent work settled failed)
    (task : Task)
    (taskGroupsPresent
      : ∀ ref ∈ task.groups.map Execution.DeliveryNode.ref,
          ¬GroupInvalidated work failed ref
          → ∃ node ∈ queue.groupNodes, node.group.node.ref = ref)
    : (queue.addTask task).HealthyContributorGroupsPresent work settled failed := by
  intro taskNode member fresh ref contributor healthy
  rcases queue.addTask_startedOldOrNew task member with old | new
  · obtain ⟨node, oldMember, same⟩ :=
      present taskNode old fresh ref contributor healthy
    have refMember : ref ∈ queue.groupNodes.map
        (fun node => node.group.node.ref) :=
      List.mem_map.mpr ⟨node, oldMember, same⟩
    obtain ⟨next, nextMember, nextRef⟩ := List.mem_map.mp
      (queue.addTask_includesRefs task ref refMember)
    exact ⟨next, nextMember, nextRef⟩
  · subst taskNode
    obtain ⟨node, oldMember, same⟩ := taskGroupsPresent ref contributor healthy
    have refMember : ref ∈ queue.groupNodes.map
        (fun node => node.group.node.ref) :=
      List.mem_map.mpr ⟨node, oldMember, same⟩
    obtain ⟨next, nextMember, nextRef⟩ := List.mem_map.mp
      (queue.addTask_includesRefs task ref refMember)
    exact ⟨next, nextMember, nextRef⟩

/-- Child integration preserves healthy contributors when cancellation has causal support.
Witness: registration cannot refuse a healthy descriptor, and old live refs persist. -/
theorem State.HealthyContributorGroupsPresent.maybeIntegrateWork
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (present : queue.HealthyContributorGroupsPresent work settled failed)
    (newWork : Work) (parentTask : Option Occurrence)
    (covered
      : ∀ task ∈ newWork.tasks,
        ∀ ref ∈ task.groups.map Execution.DeliveryNode.ref,
          ∃ group ∈ newWork.groups, group.node.ref = ref)
    (available : queue.ChildGroupsAvailable work failed newWork)
    (cancelled : queue.CancelledGroupsSupported work failed)
    (descriptors
      : ∀ group ∈ newWork.groups,
          ∃ dependencies producer,
            NodeAt work group.node .group dependencies producer
            ∧ group.parent = dependencies.head?)
    : (queue.maybeIntegrateWork newWork parentTask).1.HealthyContributorGroupsPresent
        work settled failed := by
  let withGroups := (queue.addGroups newWork.groups).1
  let withTasks := newWork.tasks.foldl State.addTask withGroups
  have groupedPresent : withGroups.HealthyContributorGroupsPresent
      work settled failed := present.addGroups newWork.groups
  have taskFold (more : List Task)
      (subset : ∀ task ∈ more, task ∈ newWork.tasks) :
      ∀ current : State,
        current.HealthyContributorGroupsPresent work settled failed
        → withGroups.GroupRefsIncluded current
        → (more.foldl State.addTask current).HealthyContributorGroupsPresent
            work settled failed := by
    induction more with
    | nil => intro current currentPresent _; exact currentPresent
    | cons task rest ih =>
        intro current currentPresent included
        have taskCovered := covered task (subset task (by simp))
        have taskPresent : ∀ ref ∈ task.groups.map Execution.DeliveryNode.ref,
            ¬GroupInvalidated work failed ref
            → ∃ node ∈ current.groupNodes, node.group.node.ref = ref := by
          intro ref contributor healthy
          obtain ⟨group, groupMember, same⟩ :=
            taskCovered ref contributor
          have groupRef : group.node.ref ∈ withGroups.groupNodes.map
              (fun node => node.group.node.ref) :=
            queue.addGroups_registersRefs newWork.groups group groupMember
              (same ▸ available task (subset task (by simp)) ref contributor healthy)
              ((cancelled.addGroups newWork.groups descriptors).healthy_not_mem
                (same ▸ healthy))
          rw [same] at groupRef
          obtain ⟨node, nodeMember, nodeRef⟩ := List.mem_map.mp
            (included ref groupRef)
          exact ⟨node, nodeMember, nodeRef⟩
        have tailSubset : ∀ next ∈ rest, next ∈ newWork.tasks := by
          intro next member
          exact subset next (by simp [member])
        exact ih tailSubset (current.addTask task)
          (currentPresent.addTask task taskPresent)
          (included.trans (current.addTask_includesRefs task))
  have taskPresent : withTasks.HealthyContributorGroupsPresent
      work settled failed :=
    taskFold newWork.tasks (fun _ member => member) withGroups groupedPresent
      (by intro ref member; exact member)
  change State.HealthyContributorGroupsPresent
    (withTasks.addStreams newWork.streams parentTask).1 work settled failed
  exact taskPresent.addStreams newWork.streams parentTask

/-- Replacing one group node leaves the set of live group refs unchanged. -/
theorem State.HealthyContributorGroupsPresent.putGroupNode
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (present : queue.HealthyContributorGroupsPresent work settled failed)
    (updated : GroupNode)
    : (queue.putGroupNode updated).HealthyContributorGroupsPresent
        work settled failed := by
  intro taskNode taskMember fresh ref contributor healthy
  obtain ⟨node, oldMember, same⟩ :=
    present taskNode taskMember fresh ref contributor healthy
  have refMember : ref ∈ queue.groupNodes.map
      (fun node => node.group.node.ref) :=
    List.mem_map.mpr ⟨node, oldMember, same⟩
  rw [← queue.putGroupNode_refs updated] at refMember
  obtain ⟨next, nextMember, nextRef⟩ := List.mem_map.mp refMember
  exact ⟨next, nextMember, nextRef⟩

/-- Decrementing group pending counts leaves contributor-node presence
unchanged, since the group ref map is unchanged. -/
theorem State.HealthyContributorGroupsPresent.settleTaskGroups
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (present : queue.HealthyContributorGroupsPresent work settled failed)
    (groups : List Execution.DeliveryNode)
    : (groups.foldl
        (fun current group =>
          match current.groupNode? group.ref with
          | none => current
          | some node => current.putGroupNode { node with pending := node.pending - 1 })
        queue).HealthyContributorGroupsPresent
        work settled failed := by
  let step (current : State) (group : Execution.DeliveryNode) : State :=
    match current.groupNode? group.ref with
    | none => current
    | some node => current.putGroupNode { node with pending := node.pending - 1 }
  have stepPresent (current : State) (group : Execution.DeliveryNode)
      (currentPresent : current.HealthyContributorGroupsPresent
        work settled failed)
      : (step current group).HealthyContributorGroupsPresent
          work settled failed := by
    unfold step
    split
    · exact currentPresent
    · exact currentPresent.putGroupNode _
  have foldPresent (more : List Execution.DeliveryNode) :
      ∀ current : State,
        current.HealthyContributorGroupsPresent work settled failed
        → (more.foldl step current).HealthyContributorGroupsPresent
            work settled failed := by
    induction more with
    | nil => intro current currentPresent; exact currentPresent
    | cons group rest ih =>
        intro current currentPresent
        exact ih (step current group) (stepPresent current group currentPresent)
  exact foldPresent groups queue present

/-- Enlarging the settled-task prefix only weakens the contributor-presence
obligation. -/
theorem State.HealthyContributorGroupsPresent.weakenSettled
    {queue : State} {work : Execution.Work} {before after failed : List Occurrence}
    (present : queue.HealthyContributorGroupsPresent work before failed)
    (included : before.Subset after)
    : queue.HealthyContributorGroupsPresent work after failed := by
  intro taskNode taskMember fresh ref contributor healthy
  exact present taskNode taskMember
    (by
      intro prior
      exact fresh (included prior))
    ref contributor healthy

/-- Removing a settled task node filters group memberships but retains all
other started task nodes and every live group ref. -/
theorem State.HealthyContributorGroupsPresent.removeTask
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (present : queue.HealthyContributorGroupsPresent work settled failed)
    (occurrence : Occurrence)
    : (queue.removeTask occurrence).HealthyContributorGroupsPresent
        work settled failed := by
  intro taskNode taskMember fresh ref contributor healthy
  have oldTask : taskNode ∈ queue.taskNodes :=
    (List.mem_filter.mp taskMember).1
  obtain ⟨node, oldMember, same⟩ :=
    present taskNode oldTask fresh ref contributor healthy
  let retained : GroupNode :=
    { node with tasks := node.tasks.filter (· != occurrence) }
  have retainedMember : retained ∈ (queue.removeTask occurrence).groupNodes :=
    List.mem_map.mpr ⟨node, oldMember, rfl⟩
  exact ⟨retained, retainedMember, same⟩

/-- A closed group ref can be removed after no unsettled started task names
it as a contributor. Other group nodes remain unchanged. -/
theorem State.HealthyContributorGroupsPresent.filterGroupRef
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (present : queue.HealthyContributorGroupsPresent work settled failed)
    (closedRef : Nat)
    (noFreshContributor
      : ∀ taskNode ∈ queue.taskNodes,
          taskNode.task.occurrence ∉ settled
          → closedRef ∉ taskNode.task.groups.map Execution.DeliveryNode.ref)
    : State.HealthyContributorGroupsPresent
        ({
          queue with
            groupNodes :=
              queue.groupNodes.filter (fun node => node.group.node.ref != closedRef)
            rootGroups := queue.rootGroups.filter (· != closedRef)
        })
        work settled failed := by
  intro taskNode taskMember fresh ref contributor healthy
  obtain ⟨node, nodeMember, same⟩ :=
    present taskNode taskMember fresh ref contributor healthy
  have different : node.group.node.ref ≠ closedRef := by
    intro equal
    have closed := noFreshContributor taskNode taskMember fresh
    exact closed (equal ▸ (same ▸ contributor))
  have retained : node ∈ queue.groupNodes.filter
      (fun candidate => candidate.group.node.ref != closedRef) := by
    exact List.mem_filter.mpr ⟨nodeMember, by simp [different]⟩
  exact ⟨node, retained, same⟩

/-- Activating groups changes no group refs. Each newly requested fresh task
must already have the contributor nodes it names. -/
theorem State.HealthyContributorGroupsPresent.startNewWork
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (present : queue.HealthyContributorGroupsPresent work settled failed)
    (registered : queue.StartedTasksRegistered)
    (newWork : NewWork)
    (requestedPresent
      : ∀ task ∈ queue.tasks,
          task.occurrence ∈ queue.releaseRequests newWork
          → task.occurrence ∉ settled
          → ∀ ref ∈ task.groups.map Execution.DeliveryNode.ref,
              ¬GroupInvalidated work failed ref
              → ∃ node ∈ queue.groupNodes, node.group.node.ref = ref)
    : (queue.startNewWork newWork).HealthyContributorGroupsPresent
        work settled failed := by
  let final := queue.startNewWork newWork
  obtain ⟨sameGroups, sameTasks, _⟩ := queue.startNewWork_groupCore newWork
  have finalRegistered : final.StartedTasksRegistered :=
    registered.startNewWork newWork
  intro taskNode taskMember fresh ref contributor healthy
  have taskDef : taskNode.task ∈ queue.tasks := by
    rw [← sameTasks]
    exact finalRegistered taskNode taskMember
  rcases queue.startNewWork_oldOrRequested newWork taskMember with old | requested
  · obtain ⟨node, oldMember, same⟩ :=
      present taskNode old fresh ref contributor healthy
    have finalMember : node ∈ final.groupNodes := by
      rw [sameGroups]
      exact oldMember
    exact ⟨node, finalMember, same⟩
  · obtain ⟨node, oldMember, same⟩ :=
      requestedPresent taskNode.task taskDef requested fresh ref contributor healthy
    have finalMember : node ∈ final.groupNodes := by
      rw [sameGroups]
      exact oldMember
    exact ⟨node, finalMember, same⟩

/-- Pruning never removes a live group node with remaining task memberships.
Witness: the actual membership-based pruning guard and unique live refs.
-/
theorem State.pruneEmptyGroups_preservesNonempty
    (queue : State) (groups : List Execution.DeliveryNode)
    (unique : queue.GroupRefsUnique)
    {ref : NodeRef}
    (present : ∃ node ∈ queue.groupNodes, node.group.node.ref = ref ∧ node.tasks ≠ [])
    : ∃ node ∈ (queue.pruneEmptyGroups groups).1.groupNodes,
        node.group.node.ref = ref ∧ node.tasks ≠ [] := by
  have loop (fuel : Nat) (current : State)
      (remaining kept : List Execution.DeliveryNode)
      (currentUnique : current.GroupRefsUnique)
      (currentPresent : ∃ node ∈ current.groupNodes,
        node.group.node.ref = ref ∧ node.tasks ≠ [])
      : ∃ node ∈ (State.pruneEmptyGroups.go fuel current remaining kept).1.groupNodes,
          node.group.node.ref = ref ∧ node.tasks ≠ [] := by
    induction fuel generalizing current remaining kept with
    | zero => exact currentPresent
    | succ fuel ih =>
        cases remaining with
        | nil => exact currentPresent
        | cons group rest =>
            unfold State.pruneEmptyGroups.go
            cases found : current.groupNode? group.ref with
            | none => exact ih _ _ _ currentUnique currentPresent
            | some node =>
                dsimp only
                split
                · rename_i prunable
                  obtain ⟨target, targetMember, targetRef, targetNonempty⟩ :=
                    currentPresent
                  have nodeMember : node ∈ current.groupNodes :=
                    List.mem_of_find?_eq_some found
                  have nodeRef : node.group.node.ref = group.ref :=
                    current.groupNode?_ref found
                  have different : target.group.node.ref ≠ group.ref := by
                    intro same
                    have equal : target = node :=
                      currentUnique.sameNode targetMember nodeMember
                        (same.trans nodeRef.symm)
                    subst target
                    exact targetNonempty
                      (List.isEmpty_iff.mp (Bool.and_eq_true_iff.mp prunable).1)
                  have retained : target ∈ current.groupNodes.filter
                      (fun entry => entry.group.node.ref != group.ref) := by
                    apply List.mem_filter.mpr
                    exact ⟨targetMember, by simp [different]⟩
                  let next : State :=
                    { current with
                        groupNodes := current.groupNodes.filter
                          (fun entry => entry.group.node.ref != group.ref) }
                  have nextUnique : next.GroupRefsUnique := by
                    change ((current.groupNodes.filter
                      (fun entry => entry.group.node.ref != group.ref)).map
                        (fun entry => entry.group.node.ref)).Nodup
                    have mapped :
                        (current.groupNodes.filter
                          (fun entry => entry.group.node.ref != group.ref)).map
                            (fun entry => entry.group.node.ref)
                          = (current.groupNodes.map
                            (fun entry => entry.group.node.ref)).filter
                              (fun ref => ref != group.ref) :=
                      (List.filter_map
                        (p := fun ref => ref != group.ref)
                        (f := fun entry : GroupNode => entry.group.node.ref)).symm
                    rw [mapped]
                    exact currentUnique.filter _
                  exact ih _ _ _ nextUnique
                    ⟨target, retained, targetRef, targetNonempty⟩
                · exact ih _ _ _ currentUnique currentPresent
  exact loop _ queue groups [] unique present

/-- Proof-only filter retaining a task's currently healthy contributor refs.
This is not stored by the executable queue. -/
noncomputable def healthyContributorRefs
    (work : Execution.Work) (failed : List Occurrence) (refs : NodeRefs)
    : NodeRefs := by
  classical
  exact refs.filter (fun ref => decide (¬GroupInvalidated work failed ref))

theorem mem_healthyContributorRefs_iff
    {work : Execution.Work} {failed : List Occurrence} {refs : NodeRefs} {ref : NodeRef}
    : ref ∈ healthyContributorRefs work failed refs
      ↔ ref ∈ refs ∧ ¬GroupInvalidated work failed ref := by
  classical
  simp [healthyContributorRefs]

/-- A fresh registered task's accounting yields its links to every currently
live healthy contributor group. -/
theorem State.HealthyRegisteredTaskAccounting.taskLinkedOn
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (accounted : queue.HealthyRegisteredTaskAccounting work settled failed)
    (unique : queue.GroupRefsUnique)
    {task : Task} (taskMember : task ∈ queue.tasks)
    (fresh : task.occurrence ∉ settled)
    : queue.TaskLinkedOn task.occurrence
        (healthyContributorRefs work failed
          (task.groups.map Execution.DeliveryNode.ref)) := by
  intro node nodeMember refMember
  obtain ⟨contributor, healthy⟩ := mem_healthyContributorRefs_iff.mp refMember
  obtain ⟨owner, ownerMember, same, linked⟩ :=
    accounted task taskMember fresh node.group.node.ref contributor healthy
  have equal : owner = node := unique.sameNode ownerMember nodeMember same
  exact equal ▸ linked

/-- A fresh started task's healthy links can be handled by the existing
single-task `TaskLinkedOn` lemmas after filtering its contributor refs. -/
theorem State.HealthyTaskLinks.toTaskLinkedOn
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (links : queue.HealthyTaskLinks work settled failed)
    {taskNode : TaskNode} (member : taskNode ∈ queue.taskNodes)
    (fresh : taskNode.task.occurrence ∉ settled)
    : queue.TaskLinkedOn taskNode.task.occurrence
        (healthyContributorRefs work failed
          (taskNode.task.groups.map Execution.DeliveryNode.ref)) := by
  intro node nodeMember refMember
  obtain ⟨contributor, healthy⟩ := mem_healthyContributorRefs_iff.mp refMember
  exact links taskNode member fresh node nodeMember healthy contributor

/-- Conversely, filtered single-task links for all fresh started tasks give
the healthy-link invariant. -/
theorem State.HealthyTaskLinks.ofFilteredLinks
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (filtered
      : ∀ taskNode ∈ queue.taskNodes,
          taskNode.task.occurrence ∉ settled
          → queue.TaskLinkedOn taskNode.task.occurrence
              (healthyContributorRefs work failed
                (taskNode.task.groups.map Execution.DeliveryNode.ref)))
    : queue.HealthyTaskLinks work settled failed := by
  intro taskNode taskMember fresh node nodeMember healthy contributor
  exact filtered taskNode taskMember fresh node nodeMember
    (mem_healthyContributorRefs_iff.mpr ⟨contributor, healthy⟩)

/-- Failure removes started nodes and groups, never starts new work, and
shrinks the set of uninvalidated contributor refs. -/
theorem State.HealthyTaskLinks.taskFailure
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (links : queue.HealthyTaskLinks work settled failed)
    (occurrence : Occurrence) (errors : Nat)
    : (queue.taskFailure occurrence errors).1.HealthyTaskLinks
        work settled (occurrence :: failed) := by
  intro taskNode taskMember fresh groupNode groupMember healthy contributor
  obtain ⟨priorMember, different⟩ :=
    queue.taskFailure_startedSurvivor occurrence errors taskMember
  have priorHealthy : ¬GroupInvalidated work failed groupNode.group.node.ref := by
    intro failure
    exact healthy (GroupInvalidated.mono failure
      (by intro earlier member; simp [member]))
  have priorLinks := (links.toTaskLinkedOn priorMember fresh).taskFailure
    occurrence errors different
  apply priorLinks groupNode groupMember
  exact mem_healthyContributorRefs_iff.mpr ⟨contributor, priorHealthy⟩

/-- Removing a task already in the settled prefix cannot break the healthy
links of any remaining unsettled started task. -/
theorem State.HealthyTaskLinks.removeSettledTask
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (links : queue.HealthyTaskLinks work settled failed)
    (occurrence : Occurrence) (already : occurrence ∈ settled)
    : (queue.removeTask occurrence).HealthyTaskLinks work settled failed := by
  intro taskNode taskMember fresh groupNode groupMember healthy contributor
  have oldTask : taskNode ∈ queue.taskNodes :=
    (List.mem_filter.mp taskMember).1
  have different : taskNode.task.occurrence ≠ occurrence := by
    intro same
    exact fresh (same ▸ already)
  have prior := (links.toTaskLinkedOn oldTask fresh).removeOtherTask
    occurrence different
  exact prior groupNode groupMember
    (mem_healthyContributorRefs_iff.mpr ⟨contributor, healthy⟩)

/-- More completed occurrences only weaken the fresh-task link condition. -/
theorem State.HealthyTaskLinks.weakenSettled
    {queue : State} {work : Execution.Work} {before after failed : List Occurrence}
    (links : queue.HealthyTaskLinks work before failed)
    (included : before.Subset after)
    : queue.HealthyTaskLinks work after failed := by
  intro taskNode taskMember fresh node nodeMember healthy contributor
  exact links taskNode taskMember
    (by
      intro prior
      exact fresh (included prior))
    node nodeMember healthy contributor

/-- Pruning group shells changes no started-task node. -/
private theorem State.pruneEmptyGroups_taskNodes
    (queue : State) (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.taskNodes = queue.taskNodes := by
  have loop (fuel : Nat) (current : State)
      (remaining kept : List Execution.DeliveryNode)
      : (State.pruneEmptyGroups.go fuel current remaining kept).1.taskNodes
          = current.taskNodes := by
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

/-- A fresh task's linked contributor has nonempty membership, so pruning retains it.
Witness: the membership guard; the former pending-bound premise is retained for callers.
-/
theorem State.HealthyContributorGroupsPresent.pruneEmptyGroups_ofPendingBound
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (present : queue.HealthyContributorGroupsPresent work settled failed)
    (links : queue.HealthyTaskLinks work settled failed)
    (_tracks : queue.HealthyPendingBound work settled failed)
    (unique : queue.GroupRefsUnique)
    (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.HealthyContributorGroupsPresent
        work settled failed := by
  intro taskNode taskMember fresh ref contributor healthy
  have oldTask : taskNode ∈ queue.taskNodes := by
    rw [State.pruneEmptyGroups_taskNodes] at taskMember
    exact taskMember
  obtain ⟨node, nodeMember, nodeRef⟩ :=
    present taskNode oldTask fresh ref contributor healthy
  have nodeHealthy : ¬GroupInvalidated work failed node.group.node.ref := by
    rw [nodeRef]
    exact healthy
  have nodeContributor : node.group.node.ref ∈
      taskNode.task.groups.map Execution.DeliveryNode.ref := by
    rw [nodeRef]
    exact contributor
  have linked : taskNode.task.occurrence ∈ node.tasks :=
    links taskNode oldTask fresh node nodeMember nodeHealthy nodeContributor
  have nonempty : node.tasks ≠ [] := List.ne_nil_of_mem linked
  obtain ⟨retained, retainedMember, retainedRef, _⟩ :=
    queue.pruneEmptyGroups_preservesNonempty groups unique
      ⟨node, nodeMember, nodeRef, nonempty⟩
  exact ⟨retained, retainedMember, retainedRef⟩

/-- The exact-ledger specialization follows from the lower-bound preservation witness. -/
theorem State.HealthyContributorGroupsPresent.pruneEmptyGroups
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (present : queue.HealthyContributorGroupsPresent work settled failed)
    (links : queue.HealthyTaskLinks work settled failed)
    (tracks : queue.HealthyPendingTracks work settled failed)
    (unique : queue.GroupRefsUnique)
    (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.HealthyContributorGroupsPresent
        work settled failed := by
  exact present.pruneEmptyGroups_ofPendingBound links tracks.toBound unique groups

/-- Group closure may remove settled started tasks, but never introduces a
new task node. -/
private theorem State.finishGroupSuccess_startedSubset
    (queue : State) (group : GroupNode)
    {taskNode : TaskNode}
    (member : taskNode ∈ (queue.finishGroupSuccess group).1.taskNodes)
    : taskNode ∈ queue.taskNodes := by
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
  have stepSubset (acc : State × List ExecutionGroupValue × NodeRefs)
      (occurrence : Occurrence)
      {node : TaskNode}
      (nodeMember : node ∈ (step acc occurrence).1.taskNodes)
      : node ∈ acc.1.taskNodes := by
    obtain ⟨current, values, streams⟩ := acc
    dsimp only [step] at nodeMember
    split at nodeMember
    · exact nodeMember
    · exact (List.mem_filter.mp nodeMember).1
  have foldSubset (tasks : List Occurrence) :
      ∀ acc : State × List ExecutionGroupValue × NodeRefs,
        ∀ {node : TaskNode},
          node ∈ (tasks.foldl step acc).1.taskNodes
          → node ∈ acc.1.taskNodes := by
    induction tasks with
    | nil => intro acc node nodeMember; exact nodeMember
    | cons occurrence rest ih =>
        intro acc node nodeMember
        exact stepSubset acc occurrence (ih (step acc occurrence) nodeMember)
  let flushed := (group.tasks.foldl step (queue, [], [])).1
  let current : State :=
    { flushed with
        groupNodes := flushed.groupNodes.filter
          (fun node => node.group.node.ref != group.group.node.ref)
        rootGroups := flushed.rootGroups.filter (· != group.group.node.ref) }
  let children := group.childGroups.filterMap
    (fun ref => (current.groupNode? ref).map (fun node => node.group.node))
  change taskNode ∈ (current.pruneEmptyGroups children).1.taskNodes at member
  rw [State.pruneEmptyGroups_taskNodes] at member
  exact foldSubset group.tasks (queue, [], []) member

/-- A group success cannot erase a fresh task's healthy link: all flushed
task occurrences have already settled. -/
theorem State.HealthyTaskLinks.finishGroupSuccess
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (links : queue.HealthyTaskLinks work settled failed)
    (group : GroupNode)
    (all : ∀ occurrence ∈ group.tasks, occurrence ∈ settled)
    : (queue.finishGroupSuccess group).1.HealthyTaskLinks work settled failed := by
  intro taskNode taskMember fresh node nodeMember healthy contributor
  have priorMember : taskNode ∈ queue.taskNodes :=
    queue.finishGroupSuccess_startedSubset group taskMember
  have outside : taskNode.task.occurrence ∉ group.tasks := by
    intro member
    exact fresh (all taskNode.task.occurrence member)
  have linked := (links.toTaskLinkedOn priorMember fresh).finishOtherGroupSuccess
    group outside
  exact linked node nodeMember
    (mem_healthyContributorRefs_iff.mpr ⟨contributor, healthy⟩)

/-- Flushing a healthy completed group cannot erase the contributor node of
an unsettled task. The closed ref has no such task; pruning preserves all
others because their linked memberships keep pending counts positive. -/
theorem State.HealthyContributorGroupsPresent.finishGroupSuccess_ofPendingBound
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (present : queue.HealthyContributorGroupsPresent work settled failed)
    (links : queue.HealthyTaskLinks work settled failed)
    (tracks : queue.HealthyPendingBound work settled failed)
    (unique : queue.GroupRefsUnique)
    (group : GroupNode) (groupMember : group ∈ queue.groupNodes)
    (healthy : ¬GroupInvalidated work failed group.group.node.ref)
    (all : ∀ occurrence ∈ group.tasks, occurrence ∈ settled)
    : (queue.finishGroupSuccess group).1.HealthyContributorGroupsPresent
        work settled failed := by
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
  have stepFacts (acc : State × List ExecutionGroupValue × NodeRefs)
      (occurrence : Occurrence) (already : occurrence ∈ settled)
      (currentPresent : acc.1.HealthyContributorGroupsPresent work settled failed)
      (currentLinks : acc.1.HealthyTaskLinks work settled failed)
      (currentTracks : acc.1.HealthyPendingBound work settled failed)
      (currentUnique : acc.1.GroupRefsUnique)
      : (step acc occurrence).1.HealthyContributorGroupsPresent work settled failed
        ∧ (step acc occurrence).1.HealthyTaskLinks work settled failed
        ∧ (step acc occurrence).1.HealthyPendingBound work settled failed
        ∧ (step acc occurrence).1.GroupRefsUnique
        ∧ (step acc occurrence).1.taskNodes ⊆ acc.1.taskNodes := by
    obtain ⟨current, values, streams⟩ := acc
    dsimp only [step]
    split
    · exact ⟨currentPresent, currentLinks, currentTracks, currentUnique,
        fun _ member => member⟩
    · exact ⟨currentPresent.removeTask occurrence,
        currentLinks.removeSettledTask occurrence already,
        currentTracks.removeTask occurrence already,
        currentUnique.removeTask occurrence,
        fun _ member => (List.mem_filter.mp member).1⟩
  have foldFacts (more : List Occurrence)
      (all : ∀ occurrence ∈ more, occurrence ∈ settled) :
      ∀ acc : State × List ExecutionGroupValue × NodeRefs,
        acc.1.HealthyContributorGroupsPresent work settled failed
        → acc.1.HealthyTaskLinks work settled failed
        → acc.1.HealthyPendingBound work settled failed
        → acc.1.GroupRefsUnique
        → (more.foldl step acc).1.HealthyContributorGroupsPresent
            work settled failed
          ∧ (more.foldl step acc).1.HealthyTaskLinks work settled failed
          ∧ (more.foldl step acc).1.HealthyPendingBound work settled failed
          ∧ (more.foldl step acc).1.GroupRefsUnique
          ∧ (more.foldl step acc).1.taskNodes ⊆ acc.1.taskNodes := by
    induction more with
    | nil =>
        intro acc currentPresent currentLinks currentTracks currentUnique
        exact ⟨currentPresent, currentLinks, currentTracks, currentUnique,
          fun _ member => member⟩
    | cons occurrence rest ih =>
        intro acc currentPresent currentLinks currentTracks currentUnique
        have head : occurrence ∈ settled := all occurrence (by simp)
        have tail : ∀ task ∈ rest, task ∈ settled := by
          intro task member
          exact all task (by simp [member])
        obtain ⟨nextPresent, nextLinks, nextTracks, nextUnique, nextSubset⟩ :=
          stepFacts acc occurrence head currentPresent currentLinks
            currentTracks currentUnique
        obtain ⟨finalPresent, finalLinks, finalTracks, finalUnique, finalSubset⟩ :=
          ih tail (step acc occurrence) nextPresent nextLinks nextTracks nextUnique
        exact ⟨finalPresent, finalLinks, finalTracks, finalUnique,
          fun task member => nextSubset (finalSubset member)⟩
  let flushed := (group.tasks.foldl step (queue, [], [])).1
  obtain ⟨flushedPresent, flushedLinks, flushedTracks, flushedUnique,
    flushedSubset⟩ := foldFacts group.tasks all (queue, [], [])
      present links tracks unique
  let current : State :=
    { flushed with
        groupNodes := flushed.groupNodes.filter
          (fun node => node.group.node.ref != group.group.node.ref)
        rootGroups := flushed.rootGroups.filter (· != group.group.node.ref) }
  have noFreshContributor : ∀ taskNode ∈ flushed.taskNodes,
      taskNode.task.occurrence ∉ settled
      → group.group.node.ref ∉ taskNode.task.groups.map Execution.DeliveryNode.ref := by
    intro taskNode taskMember fresh contributor
    have prior : taskNode ∈ queue.taskNodes := flushedSubset taskMember
    have linked : taskNode.task.occurrence ∈ group.tasks :=
      links taskNode prior fresh group groupMember healthy contributor
    exact fresh (all taskNode.task.occurrence linked)
  have currentPresent : current.HealthyContributorGroupsPresent
      work settled failed :=
    flushedPresent.filterGroupRef group.group.node.ref noFreshContributor
  have currentLinks : current.HealthyTaskLinks work settled failed := by
    intro taskNode taskMember fresh node nodeMember nodeHealthy contributor
    exact flushedLinks taskNode taskMember fresh node
      (List.mem_filter.mp nodeMember).1 nodeHealthy contributor
  have currentTracks : current.HealthyPendingBound work settled failed := by
    intro node nodeMember nodeHealthy
    exact flushedTracks node (List.mem_filter.mp nodeMember).1 nodeHealthy
  have currentUnique : current.GroupRefsUnique :=
    flushedUnique.filterGroupNodes _
  let children := group.childGroups.filterMap
    (fun ref => (current.groupNode? ref).map (fun node => node.group.node))
  change (current.pruneEmptyGroups children).1.HealthyContributorGroupsPresent
    work settled failed
  exact currentPresent.pruneEmptyGroups_ofPendingBound currentLinks currentTracks
    currentUnique children

/-- The exact-ledger specialization follows from the lower-bound preservation witness. -/
theorem State.HealthyContributorGroupsPresent.finishGroupSuccess
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (present : queue.HealthyContributorGroupsPresent work settled failed)
    (links : queue.HealthyTaskLinks work settled failed)
    (tracks : queue.HealthyPendingTracks work settled failed)
    (unique : queue.GroupRefsUnique)
    (group : GroupNode) (groupMember : group ∈ queue.groupNodes)
    (healthy : ¬GroupInvalidated work failed group.group.node.ref)
    (all : ∀ occurrence ∈ group.tasks, occurrence ∈ settled)
    : (queue.finishGroupSuccess group).1.HealthyContributorGroupsPresent
        work settled failed := by
  exact present.finishGroupSuccess_ofPendingBound links tracks.toBound unique
    group groupMember healthy all

/-- Sequential group release retains healthy links for all tasks that have
not already settled. The zero-counter certificate covers each flush. -/
theorem State.HealthyTaskLinks.releaseTaskGroups
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (links : queue.HealthyTaskLinks work settled failed)
    (tracks : queue.HealthyPendingTracks work settled failed)
    (rootsHealthy : queue.RootGroupsHealthy work failed)
    (groups : List Execution.DeliveryNode)
    : let final :=
        groups.foldl
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
          (queue, [], {})
      final.1.HealthyTaskLinks work settled failed := by
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
        else (current, events, released)
  have stepFacts (acc : State × List WorkQueueEvent × NewWork)
      (group : Execution.DeliveryNode)
      (currentLinks : acc.1.HealthyTaskLinks work settled failed)
      (currentTracks : acc.1.HealthyPendingTracks work settled failed)
      (currentRoots : acc.1.RootGroupsHealthy work failed)
      : (step acc group).1.HealthyTaskLinks work settled failed
        ∧ (step acc group).1.HealthyPendingTracks work settled failed
        ∧ (step acc group).1.RootGroupsHealthy work failed := by
    obtain ⟨current, events, released⟩ := acc
    dsimp only [step]
    split
    · exact ⟨currentLinks, currentTracks, currentRoots⟩
    · rename_i node found
      split
      · rename_i ready
        have active : node.group.node.ref ∈ current.rootGroups := by
          have root := (Bool.and_eq_true_iff.mp ready).1
          rw [current.groupNode?_ref found]
          exact List.contains_iff_mem.mp root
        have zero : node.pending = 0 := by
          exact beq_iff_eq.mp (Bool.and_eq_true_iff.mp ready).2
        have nodeMember : node ∈ current.groupNodes :=
          List.mem_of_find?_eq_some found
        have all := GroupNode.PendingTracks.allSettled node settled
          (currentTracks node nodeMember (currentRoots node.group.node.ref active)) zero
        exact ⟨currentLinks.finishGroupSuccess node all,
          currentTracks.finishGroupSuccess node all,
          currentRoots.finishGroupSuccess node⟩
      · exact ⟨currentLinks, currentTracks, currentRoots⟩
  have foldFacts (more : List Execution.DeliveryNode) :
      ∀ acc : State × List WorkQueueEvent × NewWork,
        acc.1.HealthyTaskLinks work settled failed
        → acc.1.HealthyPendingTracks work settled failed
        → acc.1.RootGroupsHealthy work failed
        → (more.foldl step acc).1.HealthyTaskLinks work settled failed
          ∧ (more.foldl step acc).1.HealthyPendingTracks work settled failed
          ∧ (more.foldl step acc).1.RootGroupsHealthy work failed := by
    induction more with
    | nil =>
        intro acc currentLinks currentTracks currentRoots
        exact ⟨currentLinks, currentTracks, currentRoots⟩
    | cons group rest ih =>
        intro acc currentLinks currentTracks currentRoots
        obtain ⟨nextLinks, nextTracks, nextRoots⟩ :=
          stepFacts acc group currentLinks currentTracks currentRoots
        exact ih (step acc group) nextLinks nextTracks nextRoots
  exact (foldFacts groups (queue, [], {}) links tracks rootsHealthy).1

/-- Sequential release preserves each healthy contributor node. The pending
ledger shows that a zero-counter root may flush only settled tasks. -/
theorem State.HealthyContributorGroupsPresent.releaseTaskGroups
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (present : queue.HealthyContributorGroupsPresent work settled failed)
    (links : queue.HealthyTaskLinks work settled failed)
    (tracks : queue.HealthyPendingTracks work settled failed)
    (rootsHealthy : queue.RootGroupsHealthy work failed)
    (unique : queue.GroupRefsUnique)
    (groups : List Execution.DeliveryNode)
    : let final :=
        groups.foldl
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
          (queue, [], {})
      final.1.HealthyContributorGroupsPresent work settled failed := by
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
        else (current, events, released)
  have stepFacts (acc : State × List WorkQueueEvent × NewWork)
      (group : Execution.DeliveryNode)
      (currentPresent : acc.1.HealthyContributorGroupsPresent work settled failed)
      (currentLinks : acc.1.HealthyTaskLinks work settled failed)
      (currentTracks : acc.1.HealthyPendingTracks work settled failed)
      (currentRoots : acc.1.RootGroupsHealthy work failed)
      (currentUnique : acc.1.GroupRefsUnique)
      : (step acc group).1.HealthyContributorGroupsPresent work settled failed
        ∧ (step acc group).1.HealthyTaskLinks work settled failed
        ∧ (step acc group).1.HealthyPendingTracks work settled failed
        ∧ (step acc group).1.RootGroupsHealthy work failed
        ∧ (step acc group).1.GroupRefsUnique := by
    obtain ⟨current, events, released⟩ := acc
    dsimp only [step]
    split
    · exact ⟨currentPresent, currentLinks, currentTracks,
        currentRoots, currentUnique⟩
    · rename_i node found
      split
      · rename_i ready
        have active : node.group.node.ref ∈ current.rootGroups := by
          have root := (Bool.and_eq_true_iff.mp ready).1
          rw [current.groupNode?_ref found]
          exact List.contains_iff_mem.mp root
        have zero : node.pending = 0 :=
          beq_iff_eq.mp (Bool.and_eq_true_iff.mp ready).2
        have nodeMember : node ∈ current.groupNodes :=
          List.mem_of_find?_eq_some found
        have healthy : ¬GroupInvalidated work failed node.group.node.ref :=
          currentRoots node.group.node.ref active
        have all := GroupNode.PendingTracks.allSettled node settled
          (currentTracks node nodeMember healthy) zero
        exact ⟨currentPresent.finishGroupSuccess currentLinks currentTracks
            currentUnique node nodeMember healthy all,
          currentLinks.finishGroupSuccess node all,
          currentTracks.finishGroupSuccess node all,
          currentRoots.finishGroupSuccess node,
          currentUnique.finishGroupSuccess node⟩
      · exact ⟨currentPresent, currentLinks, currentTracks,
          currentRoots, currentUnique⟩
  have foldFacts (more : List Execution.DeliveryNode) :
      ∀ acc : State × List WorkQueueEvent × NewWork,
        acc.1.HealthyContributorGroupsPresent work settled failed
        → acc.1.HealthyTaskLinks work settled failed
        → acc.1.HealthyPendingTracks work settled failed
        → acc.1.RootGroupsHealthy work failed
        → acc.1.GroupRefsUnique
        → (more.foldl step acc).1.HealthyContributorGroupsPresent
            work settled failed
          ∧ (more.foldl step acc).1.HealthyTaskLinks work settled failed
          ∧ (more.foldl step acc).1.HealthyPendingTracks work settled failed
          ∧ (more.foldl step acc).1.RootGroupsHealthy work failed
          ∧ (more.foldl step acc).1.GroupRefsUnique := by
    induction more with
    | nil =>
        intro acc currentPresent currentLinks currentTracks currentRoots
          currentUnique
        exact ⟨currentPresent, currentLinks, currentTracks,
          currentRoots, currentUnique⟩
    | cons group rest ih =>
        intro acc currentPresent currentLinks currentTracks currentRoots
          currentUnique
        obtain ⟨nextPresent, nextLinks, nextTracks, nextRoots, nextUnique⟩ :=
          stepFacts acc group currentPresent currentLinks currentTracks
            currentRoots currentUnique
        exact ih (step acc group) nextPresent nextLinks nextTracks nextRoots nextUnique
  exact (foldFacts groups (queue, [], {}) present links tracks rootsHealthy unique).1

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
