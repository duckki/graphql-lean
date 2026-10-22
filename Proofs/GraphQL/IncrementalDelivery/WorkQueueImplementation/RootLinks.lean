import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RegistrationLinks

/-! Root-group presence and root-restricted task links. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Root-restricted task links
-----------------------------------------------------------------------------------------

/-- Every active root ref still has a group node. Inert group shells need not be roots. -/
def State.RootGroupsPresent (queue : State) : Prop :=
  ∀ ref ∈ queue.rootGroups, ref ∈ queue.groupNodes.map (fun node => node.group.node.ref)

/-- A registered task is linked to each of its currently active root owners. -/
def State.RootTaskLinkedOn (queue : State) (occurrence : Occurrence) (refs : NodeRefs)
    : Prop :=
  ∀ node ∈ queue.groupNodes,
    node.group.node.ref ∈ queue.rootGroups
    → node.group.node.ref ∈ refs
    → occurrence ∈ node.tasks

private theorem State.addGroup_rootGroups (queue : State) (group : Group)
    : (queue.addGroup group).rootGroups = queue.rootGroups := by
  unfold State.addGroup
  split
  · rfl
  · split
    · rfl
    · split
      · split <;> rfl
      · rfl

/-- Recursive registration leaves active roots unchanged. -/
theorem State.addGroups_rootGroups (queue : State) (groups : List Group)
    : (queue.addGroups groups).1.rootGroups = queue.rootGroups := by
  exact State.addGroups_projection State.rootGroups State.addGroup_rootGroups queue groups

/-- Registering a task can start its node but never activates a contributing group.
Witness: membership updates and the optional task-node insertion both preserve roots.
-/
theorem State.addTask_rootGroups (queue : State) (task : Task)
    : (queue.addTask task).rootGroups = queue.rootGroups := by
  let step (current : State) (group : Execution.DeliveryNode) : State :=
    match current.groupNode? group.ref with
    | none => current
    | some node =>
        if node.tasks.contains task.occurrence then
          current
        else
          current.putGroupNode
            { node with
              tasks := node.tasks ++ [task.occurrence],
              pending := node.pending + 1 }
  have stepRoots (current : State) (group : Execution.DeliveryNode) :
      (step current group).rootGroups = current.rootGroups := by
    unfold step
    split
    · rfl
    · split <;> rfl
  have foldRoots (more : List Execution.DeliveryNode) :
      ∀ current, (more.foldl step current).rootGroups = current.rootGroups := by
    induction more with
    | nil => intro current; rfl
    | cons group rest ih =>
        intro current
        simp only [List.foldl_cons, ih, stepRoots]
  let registered : State := { queue with tasks := queue.tasks ++ [task] }
  let current := task.groups.foldl step registered
  have currentRoots : current.rootGroups = queue.rootGroups :=
    foldRoots task.groups registered
  change (if task.groups.any (fun group => current.rootGroups.contains group.ref)
      && (current.taskNode? task.occurrence).isNone then
      { current with taskNodes := current.taskNodes ++ [{ task }] }
    else current).rootGroups = queue.rootGroups
  split <;> exact currentRoots

private theorem State.addStreams_rootGroups (queue : State) (streams : List Stream)
    (parentTask : Option Occurrence)
    : (queue.addStreams streams parentTask).1.rootGroups = queue.rootGroups := by
  unfold State.addStreams
  split
  · rfl
  · dsimp
    split <;> rfl

theorem State.maybeIntegrateWork_rootGroups (queue : State) (newWork : Work)
    (parentTask : Option Occurrence)
    : (queue.maybeIntegrateWork newWork parentTask).1.rootGroups = queue.rootGroups := by
  let withGroups := (queue.addGroups newWork.groups).1
  let withTasks := newWork.tasks.foldl State.addTask withGroups
  have taskFold (more : List Task) :
      ∀ current, (more.foldl State.addTask current).rootGroups
        = current.rootGroups := by
    induction more with
    | nil => intro current; rfl
    | cons task rest ih =>
        intro current
        simp only [List.foldl_cons, ih, State.addTask_rootGroups]
  change (withTasks.addStreams newWork.streams parentTask).1.rootGroups
    = queue.rootGroups
  rw [State.addStreams_rootGroups, taskFold, State.addGroups_rootGroups]

/-- The new state retains every previously live group ref. This relation is
about ref presence, not task ownership or whether a group is active.
-/
def State.GroupRefsIncluded (before after : State) : Prop :=
  ∀ ref ∈ before.groupNodes.map (fun node => node.group.node.ref),
    ref ∈ after.groupNodes.map (fun node => node.group.node.ref)

theorem State.GroupRefsIncluded.trans {first second third : State}
    (left : first.GroupRefsIncluded second)
    (right : second.GroupRefsIncluded third)
    : first.GroupRefsIncluded third := by
  intro ref member
  exact right ref (left ref member)

theorem State.addGroup_includesRefs (queue : State) (group : Group)
    : queue.GroupRefsIncluded (queue.addGroup group) := by
  exact queue.addGroup_refs_subset group

theorem State.addGroups_includesRefs (queue : State) (groups : List Group)
    : queue.GroupRefsIncluded (queue.addGroups groups).1 := by
  exact State.addGroups_preserves (fun current => queue.GroupRefsIncluded current) groups
    (fun current group _ earlier => earlier.trans (current.addGroup_includesRefs group))
    queue (fun _ member => member)

theorem State.addTask_includesRefs (queue : State) (task : Task)
    : queue.GroupRefsIncluded (queue.addTask task) := by
  let step (current : State) (group : Execution.DeliveryNode) : State :=
    match current.groupNode? group.ref with
    | none => current
    | some node =>
        if node.tasks.contains task.occurrence then
          current
        else
          current.putGroupNode
            { node with
              tasks := node.tasks ++ [task.occurrence], pending := node.pending + 1 }
  have stepRefs (current : State) (group : Execution.DeliveryNode) :
      current.GroupRefsIncluded (step current group) := by
    unfold step
    split
    · intro ref member; exact member
    · split
      · intro ref member; exact member
      · intro ref member
        rw [State.putGroupNode_refs]
        exact member
  have foldRefs (more : List Execution.DeliveryNode) :
      ∀ current : State, current.GroupRefsIncluded (more.foldl step current) := by
    induction more with
    | nil => intro current ref member; exact member
    | cons group rest ih =>
        intro current
        exact (stepRefs current group).trans (ih (step current group))
  let registered : State := { queue with tasks := queue.tasks ++ [task] }
  let current := task.groups.foldl step registered
  have linked : queue.GroupRefsIncluded current := foldRefs task.groups registered
  change queue.GroupRefsIncluded
    (if task.groups.any (fun group => current.rootGroups.contains group.ref)
        && (current.taskNode? task.occurrence).isNone then
      { current with taskNodes := current.taskNodes ++ [{ task }] }
    else current)
  split <;> exact linked

/-- Integration retains every previously live group ref.
Witness: group registration appends records, task registration changes memberships only,
and stream attachment leaves the group map unchanged.
-/
theorem State.maybeIntegrateWork_includesRefs (queue : State)
    (newWork : Work) (parentTask : Option Occurrence)
    : queue.GroupRefsIncluded (queue.maybeIntegrateWork newWork parentTask).1 := by
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
  have groupIncluded : queue.GroupRefsIncluded withGroups :=
    queue.addGroups_includesRefs newWork.groups
  have taskIncluded : withGroups.GroupRefsIncluded withTasks :=
    taskFold newWork.tasks withGroups
  change queue.GroupRefsIncluded
    (withTasks.addStreams newWork.streams parentTask).1
  exact (groupIncluded.trans taskIncluded).trans (by
    intro ref member
    unfold State.addStreams
    split
    · exact member
    · dsimp
      split <;> exact member)

/-- Child-work integration cannot orphan an already active root group. -/
theorem State.RootGroupsPresent.maybeIntegrateWork
    {queue : State} (present : queue.RootGroupsPresent)
    (newWork : Work) (parentTask : Option Occurrence)
    : (queue.maybeIntegrateWork newWork parentTask).1.RootGroupsPresent := by
  intro ref rootMember
  have unchanged := State.maybeIntegrateWork_rootGroups queue newWork parentTask
  rw [unchanged] at rootMember
  exact (queue.maybeIntegrateWork_includesRefs newWork parentTask)
    ref (present ref rootMember)

/-- Restrict root links to a fixed list of the currently active contributor
refs, so the general task-link lemmas can be reused.
-/
theorem State.RootTaskLinkedOn.activeRefs
    {queue : State} {occurrence : Occurrence} {refs : NodeRefs}
    (linked : queue.RootTaskLinkedOn occurrence refs)
    : queue.TaskLinkedOn occurrence
        (refs.filter (fun ref => queue.rootGroups.contains ref)) := by
  intro node member refMember
  have inRefs : node.group.node.ref ∈ refs := (List.mem_filter.mp refMember).1
  have inRoots : node.group.node.ref ∈ queue.rootGroups := by
    have contained := (List.mem_filter.mp refMember).2
    obtain ⟨candidate, prior, same⟩ :=
      List.contains_iff_exists_mem_beq.mp contained
    have equal := beq_iff_eq.mp same
    exact equal.symm ▸ prior
  exact linked node member inRoots inRefs

/-- Convert a fixed active-ref link back to the state-indexed root predicate
when an operation has not changed the root ref list.
-/
theorem State.TaskLinkedOn.ofActiveRefs
    {before after : State} {occurrence : Occurrence} {refs : NodeRefs}
    (linked
      : after.TaskLinkedOn occurrence
          (refs.filter (fun ref => before.rootGroups.contains ref)))
    (sameRoots : after.rootGroups = before.rootGroups)
    : after.RootTaskLinkedOn occurrence refs := by
  intro node member inRoots inRefs
  rw [sameRoots] at inRoots
  exact linked node member
    (List.mem_filter.mpr
      ⟨
        inRefs,
        (List.contains_iff_exists_mem_beq).mpr ⟨node.group.node.ref, inRoots, by simp⟩
      ⟩)

/-- Registering another task adds memberships but does not disturb the
active-root links of an already registered task.
-/
theorem State.RootTaskLinkedOn.addTask
    {queue : State} (unique : queue.GroupRefsUnique)
    {occurrence : Occurrence} {refs : NodeRefs}
    (linked : queue.RootTaskLinkedOn occurrence refs) (task : Task)
    : (queue.addTask task).RootTaskLinkedOn occurrence refs :=
  ((linked.activeRefs).addTask unique task).ofActiveRefs
    (State.addTask_rootGroups queue task)

/-- Integrating child work preserves links to active roots without ruling out
re-creation of failed, nonroot shells. The only premise is that active root
refs still have live nodes before the integration.
-/
theorem State.RootTaskLinkedOn.maybeIntegrateWork
    {queue : State} (unique : queue.GroupRefsUnique)
    (rootsPresent : queue.RootGroupsPresent)
    {occurrence : Occurrence} {refs : NodeRefs}
    (linked : queue.RootTaskLinkedOn occurrence refs)
    (newWork : Work) (parentTask : Option Occurrence)
    : (queue.maybeIntegrateWork newWork parentTask).1.RootTaskLinkedOn
        occurrence refs := by
  let activeRefs := refs.filter (fun ref => queue.rootGroups.contains ref)
  have activeLinked : queue.TaskLinkedOn occurrence activeRefs :=
    linked.activeRefs
  have relevantExisting :
      ∀ group ∈ newWork.groups, group.node.ref ∈ activeRefs
        → ∃ node ∈ queue.groupNodes, node.group.node.ref = group.node.ref := by
    intro group _ member
    have inRoots : group.node.ref ∈ queue.rootGroups := by
      have contained := (List.mem_filter.mp member).2
      obtain ⟨candidate, prior, same⟩ :=
        List.contains_iff_exists_mem_beq.mp contained
      have equal := beq_iff_eq.mp same
      exact equal.symm ▸ prior
    exact List.mem_map.mp (rootsPresent group.node.ref inRoots)
  have afterLinked := activeLinked.maybeIntegrateWork unique newWork parentTask
    relevantExisting
  exact afterLinked.ofActiveRefs
    (State.maybeIntegrateWork_rootGroups queue newWork parentTask)

/-- Removing a failed group also removes it from active roots, preserving
root-restricted task links for every remaining group.
-/
theorem State.RootTaskLinkedOn.removeGroup
    {queue : State} {occurrence : Occurrence} {refs : NodeRefs}
    (linked : queue.RootTaskLinkedOn occurrence refs) (ref : NodeRef)
    : (queue.removeGroup ref).RootTaskLinkedOn occurrence refs := by
  intro node nodeMember rootMember refMember
  unfold State.removeGroup at nodeMember rootMember
  exact linked node (List.mem_filter.mp nodeMember).1
    (List.mem_filter.mp rootMember).1 refMember

/-- Group removal filters the same refs from the root list and node map. -/
theorem State.RootGroupsPresent.removeGroup
    {queue : State} (present : queue.RootGroupsPresent) (ref : NodeRef)
    : (queue.removeGroup ref).RootGroupsPresent := by
  intro root rootMember
  unfold State.removeGroup at rootMember ⊢
  obtain ⟨node, nodeMember, same⟩ :=
    List.mem_map.mp (present root (List.mem_filter.mp rootMember).1)
  exact List.mem_map.mpr
    ⟨
      node,
      List.mem_filter.mpr
        ⟨nodeMember, by simpa only [same] using (List.mem_filter.mp rootMember).2⟩,
      same
    ⟩

/-- Failure retains existing task links on every surviving active owner. -/
theorem State.RootTaskLinkedOn.taskFailure_preserves
    {queue : State} {occurrence : Occurrence} {refs : NodeRefs}
    (linked : queue.RootTaskLinkedOn occurrence refs)
    (failed : Occurrence) (errors : Nat)
    : (queue.taskFailure failed errors).1.RootTaskLinkedOn occurrence refs := by
  cases found : queue.taskNode? failed with
  | none => simpa [State.taskFailure, found] using linked
  | some node =>
      rw [queue.taskFailure_eq failed errors node found]
      exact failureGroupFold_preserves (fun state => state.RootTaskLinkedOn occurrence refs)
        (fun _ ref prior => prior.removeGroup ref) _ _ _ linked

/-- In particular, failure preserves every different task's active-owner links. -/
theorem State.RootTaskLinkedOn.taskFailure
    {queue : State} {occurrence : Occurrence} {refs : NodeRefs}
    (linked : queue.RootTaskLinkedOn occurrence refs)
    (failed : Occurrence) (errors : Nat) (_different : occurrence ≠ failed)
    : (queue.taskFailure failed errors).1.RootTaskLinkedOn occurrence refs :=
  linked.taskFailure_preserves failed errors

/-- Failure settlement cannot orphan the root groups that survive it. -/
theorem State.RootGroupsPresent.taskFailure
    {queue : State} (present : queue.RootGroupsPresent)
    (failed : Occurrence) (errors : Nat)
    : (queue.taskFailure failed errors).1.RootGroupsPresent := by
  cases found : queue.taskNode? failed with
  | none => simpa [State.taskFailure, found] using present
  | some node =>
      rw [queue.taskFailure_eq failed errors node found]
      exact failureGroupFold_preserves State.RootGroupsPresent
        (fun _ ref prior => prior.removeGroup ref) _ _ _ present

/-- A surviving task node retains an old task definition after rejection replacement.
Witness: failure-owner cleanup only deletes nodes; the preceding update changes the
selected computation's rejection without changing its task definition.
-/
theorem State.taskFailure_startedSurvivor (queue : State)
    (failed : Occurrence) (errors : Nat)
    {taskNode : TaskNode}
    (member : taskNode ∈ (queue.taskFailure failed errors).1.taskNodes)
    : ∃ old ∈ queue.taskNodes, old.task = taskNode.task := by
  cases found : queue.taskNode? failed with
  | none => exact ⟨taskNode, by simpa [State.taskFailure, found] using member, rfl⟩
  | some node =>
      rw [queue.taskFailure_eq failed errors node found] at member
      have updated := failureGroupFold_taskNodes_subset errors node.task.groups
        (queue.putTaskNode { node with rejection := some errors }, []) member
      obtain ⟨old, oldMember, same⟩ := List.mem_map.mp updated
      split at same
      · subst taskNode
        exact ⟨node, List.mem_of_find?_eq_some found, rfl⟩
      · subst taskNode
        exact ⟨old, oldMember, rfl⟩

/-- Failure handling introduces no new started task definition. -/
theorem State.taskFailure_startedSubset (queue : State)
    (failed : Occurrence) (errors : Nat)
    {taskNode : TaskNode}
    (member : taskNode ∈ (queue.taskFailure failed errors).1.taskNodes)
    : taskNode.task ∈ queue.taskNodes.map TaskNode.task := by
  obtain ⟨old, earlier, same⟩ := queue.taskFailure_startedSurvivor failed errors member
  exact List.mem_map.mpr ⟨old, earlier, same⟩

/-- Registering one task either retains an old started node or appends that
task's fresh node; group membership updates do not rewrite task nodes.
-/
theorem State.addTask_startedOldOrNew (queue : State) (task : Task)
    {taskNode : TaskNode} (member : taskNode ∈ (queue.addTask task).taskNodes)
    : taskNode ∈ queue.taskNodes ∨ taskNode = { task } := by
  let step (current : State) (group : Execution.DeliveryNode) : State :=
    match current.groupNode? group.ref with
    | none => current
    | some node =>
        if node.tasks.contains task.occurrence then
          current
        else
          current.putGroupNode
            { node with
              tasks := node.tasks ++ [task.occurrence], pending := node.pending + 1 }
  have stepNodes (current : State) (group : Execution.DeliveryNode) :
      (step current group).taskNodes = current.taskNodes := by
    unfold step
    split
    · rfl
    · split <;> rfl
  have foldNodes (more : List Execution.DeliveryNode) :
      ∀ current, (more.foldl step current).taskNodes = current.taskNodes := by
    induction more with
    | nil => intro current; rfl
    | cons group rest ih =>
        intro current
        simp only [List.foldl_cons, ih, stepNodes]
  let registered : State := { queue with tasks := queue.tasks ++ [task] }
  let current := task.groups.foldl step registered
  have currentNodes : current.taskNodes = queue.taskNodes :=
    foldNodes task.groups registered
  unfold State.addTask at member
  change taskNode ∈
    (if task.groups.any (fun group => current.rootGroups.contains group.ref)
        && (current.taskNode? task.occurrence).isNone then
      { current with taskNodes := current.taskNodes ++ [{ task }] }
    else current).taskNodes at member
  split at member
  · rcases List.mem_append.mp member with old | new
    · exact Or.inl (currentNodes ▸ old)
    · exact Or.inr (List.mem_singleton.mp new)
  · exact Or.inl (currentNodes ▸ member)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
