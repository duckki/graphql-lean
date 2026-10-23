import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RegistrationSupport
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.HealthyPending
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.DeclarationLowering
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RegistrationProvenance
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

/-- Certified root work declares all initial task contributors in the same integration. -/
theorem workFromSpec_immediateGroupsCoverTasks (work : Execution.Work) (address : Address)
    (certified : DeclarationCoverage.Certified [] work)
    : ∀ task ∈ (Work.fromExecution work address).tasks,
      ∀ ref ∈ task.groups.map Execution.DeliveryNode.ref,
        ∃ group ∈ (Work.fromExecution work address).groups, group.node.ref = ref := by
  intro task member ref contributor
  have covered := certified.immediate address member contributor
  exact List.mem_map.mp ((List.mem_append.mp covered).resolve_left (by simp))

/-- A stream item's fresh context declares all of its immediate task contributors. -/
theorem GraphEvent.MatchesWork.streamItem_childTasksCovered
    {work : Execution.Work} {stream : Execution.DeliveryNode} {items : List StreamItem}
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (certified : DeclarationCoverage.Certified [] work)
    {item : StreamItem} (itemMember : item ∈ items)
    : ∀ task ∈ item.work.tasks,
      ∀ ref ∈ task.groups.map Execution.DeliveryNode.ref,
        ∃ group ∈ item.work.groups, group.node.ref = ref := by
  intro task member ref contributes
  have covered := (certified.sourceStreamItem matching itemMember []).contributors task member ref contributes
  exact covered.resolve_left (by simp)

/-- A group can participate in registration when it is already live or its ref has
never been registered. Retired refs deliberately do not satisfy this predicate. -/
def State.GroupAvailable (queue : State) (ref : NodeRef) : Prop :=
  ref ∈ queue.groupNodes.map (fun node => node.group.node.ref)
  ∨ ref ∉ queue.registeredGroups

/-- Registration support implies ordinary live-or-fresh availability. -/
theorem State.GroupRegistrationSupported.available {queue work ref}
    (supported : State.GroupRegistrationSupported queue work ref)
    : queue.GroupAvailable ref := by
  cases supported with
  | live member => exact Or.inl member
  | fresh absent _ => exact Or.inr absent

/-- Unavailable refs are exactly retired refs, not merely absent live nodes.
Witness: the two alternatives of availability and the permanent-registry definition. -/
theorem State.groupUnavailable_iff_retired (queue : State) (ref : NodeRef)
    : ¬queue.GroupAvailable ref ↔ queue.RetiredGroup ref := by
  classical
  simp [State.GroupAvailable, State.RetiredGroup, not_or, and_comm]

/-- An unsettled registered task retains a live group for each healthy contributor. -/
theorem State.HealthyRegisteredTaskAccounting.groupAvailable
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (accounted : queue.HealthyRegisteredTaskAccounting work settled failed)
    {task : Task} (member : task ∈ queue.tasks) (fresh : task.occurrence ∉ settled)
    {ref : NodeRef} (contributor : ref ∈ task.groups.map Execution.DeliveryNode.ref)
    (healthy : ¬GroupInvalidated work failed ref)
    : queue.GroupAvailable ref := by
  obtain ⟨node, nodeMember, sameRef, _⟩ := accounted task member fresh ref contributor healthy
  exact Or.inl (List.mem_map.mpr ⟨node, nodeMember, sameRef⟩)

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

/-- Every healthy new contributor has a fresh parent chain ending at a live record or root.
This is derived proof evidence about replay, not a host-source assumption. -/
def State.ChildGroupsAvailable (queue : State) (work : Execution.Work)
    (failed : List Occurrence) (newWork : Work)
    : Prop :=
  ∀ task ∈ newWork.tasks,
  ∀ ref ∈ task.groups.map Execution.DeliveryNode.ref,
    ¬GroupInvalidated work failed ref → queue.GroupRegistrationSupported work ref

/-- Supported candidates acquire live records through parent-first registration. -/
theorem State.addGroups_registersRefs {work : Execution.Work}
    (queue : State) (groups : List Group) (generated : ExecutedWork work)
    (coverage : queue.LiveGroupsRegistered)
    (matching
      : ∀ group ∈ groups,
          ∃ dependencies,
            GroupRecordAt work group.node dependencies
            ∧ group.parent = dependencies.head?)
    (closed
      : ∀ group ∈ groups,
          ∀ parent,
            group.parent = some parent
            → parent ∈ queue.registeredGroups ++ groups.map (fun group => group.node.ref))
    : ∀ group ∈ groups,
        queue.GroupRegistrationSupported work group.node.ref
        → group.node.ref
          ∈ (queue.addGroups groups).1.groupNodes.map
              (fun node => node.group.node.ref) := by
  intro group member supported
  exact queue.addGroups_supported_live supported generated coverage groups matching closed
    (List.mem_map.mpr ⟨group, member, rfl⟩)

/-- Integration retains every supported candidate.
Witness: parent-first registration supplies live nodes; task and stream integration retain them.
-/
theorem State.maybeIntegrateWork_registersRefs (queue : State) (newWork : Work)
    (parentTask : Option Occurrence) {work : Execution.Work}
    (generated : ExecutedWork work) (coverage : queue.LiveGroupsRegistered)
    (matching
      : ∀ group ∈ newWork.groups,
          ∃ dependencies,
            GroupRecordAt work group.node dependencies
            ∧ group.parent = dependencies.head?)
    (closed
      : ∀ group ∈ newWork.groups,
          ∀ parent,
            group.parent = some parent
            → parent
              ∈ queue.registeredGroups
                ++ newWork.groups.map (fun group => group.node.ref))
    : ∀ group ∈ newWork.groups,
        queue.GroupRegistrationSupported work group.node.ref
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
  intro group member supported
  change group.node.ref ∈
    (withTasks.addStreams newWork.streams parentTask).1.groupNodes.map
      (fun node => node.group.node.ref)
  exact (taskIncluded.trans streamIncluded) group.node.ref
    (queue.addGroups_registersRefs newWork.groups generated coverage matching closed group
      member supported)

/-- Generated initial tasks have all contributor records live before pruning. -/
theorem initialIntegration_taskGroupsPresent (work : Execution.Work)
    (generated : ExecutedWork work)
    : ∀ task ∈ (({} : State).maybeIntegrateWork (Work.fromExecution work)).1.tasks,
      ∀ ref ∈ task.groups.map Execution.DeliveryNode.ref,
        ∃ node ∈ (({} : State).maybeIntegrateWork (Work.fromExecution work)).1.groupNodes,
          node.group.node.ref = ref := by
  intro task member ref contributor
  have taskMember : task ∈ (Work.fromExecution work).tasks := by
    rw [State.maybeIntegrateWork_tasks_append] at member
    simpa using member
  obtain ⟨group, groupMember, same⟩ :=
    workFromSpec_immediateGroupsCoverTasks work [] generated.declarations task taskMember ref contributor
  have live := ({} : State).maybeIntegrateWork_registersRefs (Work.fromExecution work) none
    generated (by intro node member; cases member)
    (fun _ member => workFromSpec_groups_recordAt_root member)
    (fun group member parent parentEq =>
      generated.declarations.parents [] member parentEq)
    group groupMember (generated.empty_registrationSupported group.node.ref)
  rw [same] at live
  exact List.mem_map.mp live

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
    (generated : ExecutedWork work) (coverage : queue.LiveGroupsRegistered)
    (descriptors
      : ∀ group ∈ newWork.groups,
          ∃ dependencies,
            GroupRecordAt work group.node dependencies
            ∧ group.parent = dependencies.head?)
    (closed
      : ∀ group ∈ newWork.groups,
          ∀ parent,
            group.parent = some parent
            → parent
              ∈ queue.registeredGroups
                ++ newWork.groups.map (fun group => group.node.ref))
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
            queue.addGroups_registersRefs newWork.groups generated coverage descriptors closed group groupMember
              (same ▸ available task (subset task (by simp)) ref contributor healthy)
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

/-- Without cached rejections, activation retains each fresh task's healthy contributors.
Newly requested tasks must already have the contributor nodes they name. -/
theorem State.HealthyContributorGroupsPresent.startNewWork_of_no_cached_failures
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (present : queue.HealthyContributorGroupsPresent work settled failed)
    (registered : queue.StartedTasksRegistered)
    (newWork : NewWork)
    (unrejected : ∀ node ∈ queue.taskNodes, node.rejection = none)
    (requestedPresent
      : ∀ task ∈ queue.tasks,
          task.occurrence ∈ queue.releaseRequests newWork
          → task.occurrence ∉ settled
          → ∀ ref ∈ task.groups.map Execution.DeliveryNode.ref,
              ¬GroupInvalidated work failed ref
              → ∃ node ∈ queue.groupNodes, node.group.node.ref = ref)
    : (queue.startNewWork newWork).1.HealthyContributorGroupsPresent
        work settled failed := by
  let final := (queue.startNewWork newWork).1
  have sameGroups := (queue.startNewWork_groupCore_of_no_cached_failures newWork unrejected).1
  have sameTasks := queue.startNewWork_tasks newWork []
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
                      (List.isEmpty_iff.mp prunable)
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
  obtain ⟨prior, priorMember, sameTask⟩ :=
    queue.taskFailure_startedSurvivor occurrence errors taskMember
  have priorHealthy : ¬GroupInvalidated work failed groupNode.group.node.ref := by
    intro failure
    exact healthy (GroupInvalidated.mono failure
      (by intro earlier member; simp [member]))
  have priorFresh : prior.task.occurrence ∉ settled := sameTask.symm ▸ fresh
  have priorLinks := (links.toTaskLinkedOn priorMember priorFresh).taskFailure_preserves
    occurrence errors
  rw [sameTask] at priorLinks
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
