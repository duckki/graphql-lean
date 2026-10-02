import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RegistrationLinks

/-! Root-group presence and root-restricted task links. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Root-restricted task links
-----------------------------------------------------------------------------------------

/-- Every active root key still has a group node. Inert group shells need not be roots. -/
def State.RootGroupsPresent (queue : State) : Prop :=
  ∀ key ∈ queue.rootGroups, key ∈ queue.groupNodes.map (fun node => node.group.node.key)

/-- A registered task is linked to each of its currently active root owners. -/
def State.RootTaskLinkedOn (queue : State) (occurrence : Occurrence) (keys : Keys)
    : Prop :=
  ∀ node ∈ queue.groupNodes,
    node.group.node.key ∈ queue.rootGroups
    → node.group.node.key ∈ keys
    → occurrence ∈ node.tasks

private theorem State.addGroup_rootGroups (queue : State) (group : Group)
    : (queue.addGroup group).rootGroups = queue.rootGroups := by
  unfold State.addGroup
  split
  · rfl
  · split <;> rfl

/-- Registering groups and their parent links leaves active roots unchanged.
Witness: both registration folds update only the group-node map and key registry.
-/
theorem State.addGroups_rootGroups (queue : State) (groups : List Group)
    : (queue.addGroups groups).1.rootGroups = queue.rootGroups := by
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
              else
                node.childGroups ++ [group.node.key]
            current.putGroupNode { node with childGroups := children }
  have registrationFold (more : List Group) :
      ∀ current, (more.foldl State.addGroup current).rootGroups
        = current.rootGroups := by
    induction more with
    | nil => intro current; rfl
    | cons group rest ih =>
        intro current
        simp only [List.foldl_cons, ih, State.addGroup_rootGroups]
  have linkStepRoots (current : State) (group : Group) :
      (linkStep current group).rootGroups = current.rootGroups := by
    unfold linkStep
    split
    · rfl
    · split <;> rfl
  have linkFold (more : List Group) :
      ∀ current, (more.foldl linkStep current).rootGroups
        = current.rootGroups := by
    induction more with
    | nil => intro current; rfl
    | cons group rest ih =>
        intro current
        simp only [List.foldl_cons, ih, linkStepRoots]
  let fresh := groups.filter (fun group =>
    !queue.registeredGroups.contains group.node.key
      && (queue.groupNode? group.node.key).isNone)
  change (fresh.foldl linkStep
    (fresh.foldl State.addGroup queue)).rootGroups = queue.rootGroups
  rw [linkFold, registrationFold]

/-- Registering a task can start its node but never activates a contributing group.
Witness: membership updates and the optional task-node insertion both preserve roots.
-/
theorem State.addTask_rootGroups (queue : State) (task : Task)
    : (queue.addTask task).rootGroups = queue.rootGroups := by
  let step (current : State) (group : Execution.DeliveryNode) : State :=
    match current.groupNode? group.key with
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
  change (if task.groups.any (fun group => current.rootGroups.contains group.key)
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

/-- The new state retains every previously live group key. This relation is
about key presence, not task ownership or whether a group is active.
-/
def State.GroupKeysIncluded (before after : State) : Prop :=
  ∀ key ∈ before.groupNodes.map (fun node => node.group.node.key),
    key ∈ after.groupNodes.map (fun node => node.group.node.key)

theorem State.GroupKeysIncluded.trans {first second third : State}
    (left : first.GroupKeysIncluded second)
    (right : second.GroupKeysIncluded third)
    : first.GroupKeysIncluded third := by
  intro key member
  exact right key (left key member)

theorem State.addGroup_includesKeys (queue : State) (group : Group)
    : queue.GroupKeysIncluded (queue.addGroup group) := by
  intro key member
  obtain ⟨node, nodeMember, same⟩ := List.mem_map.mp member
  exact List.mem_map.mpr
    ⟨node, queue.addGroup_preservesExisting group nodeMember, same⟩

theorem State.addGroups_includesKeys (queue : State) (groups : List Group)
    : queue.GroupKeysIncluded (queue.addGroups groups).1 := by
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
              else
                node.childGroups ++ [group.node.key]
            current.putGroupNode { node with childGroups := children }
  have registrationFold (more : List Group) :
      ∀ current : State,
        current.GroupKeysIncluded (more.foldl State.addGroup current) := by
    induction more with
    | nil => intro current key member; exact member
    | cons group rest ih =>
        intro current
        exact (current.addGroup_includesKeys group).trans
          (ih (current.addGroup group))
  have linkStepKeys (current : State) (group : Group) :
      current.GroupKeysIncluded (linkStep current group) := by
    unfold linkStep
    split
    · intro key member; exact member
    · split
      · intro key member; exact member
      · rename_i node found
        intro key member
        rw [State.putGroupNode_keys]
        exact member
  have linkFold (more : List Group) :
      ∀ current : State, current.GroupKeysIncluded (more.foldl linkStep current) := by
    induction more with
    | nil => intro current key member; exact member
    | cons group rest ih =>
        intro current
        exact (linkStepKeys current group).trans
          (ih (linkStep current group))
  let fresh := groups.filter (fun group =>
    !queue.registeredGroups.contains group.node.key
      && (queue.groupNode? group.node.key).isNone)
  change queue.GroupKeysIncluded
    (fresh.foldl linkStep (fresh.foldl State.addGroup queue))
  exact (registrationFold fresh queue).trans
    (linkFold fresh (fresh.foldl State.addGroup queue))

theorem State.addTask_includesKeys (queue : State) (task : Task)
    : queue.GroupKeysIncluded (queue.addTask task) := by
  let step (current : State) (group : Execution.DeliveryNode) : State :=
    match current.groupNode? group.key with
    | none => current
    | some node =>
        if node.tasks.contains task.occurrence then
          current
        else
          current.putGroupNode
            { node with
              tasks := node.tasks ++ [task.occurrence], pending := node.pending + 1 }
  have stepKeys (current : State) (group : Execution.DeliveryNode) :
      current.GroupKeysIncluded (step current group) := by
    unfold step
    split
    · intro key member; exact member
    · split
      · intro key member; exact member
      · intro key member
        rw [State.putGroupNode_keys]
        exact member
  have foldKeys (more : List Execution.DeliveryNode) :
      ∀ current : State, current.GroupKeysIncluded (more.foldl step current) := by
    induction more with
    | nil => intro current key member; exact member
    | cons group rest ih =>
        intro current
        exact (stepKeys current group).trans (ih (step current group))
  let registered : State := { queue with tasks := queue.tasks ++ [task] }
  let current := task.groups.foldl step registered
  have linked : queue.GroupKeysIncluded current := foldKeys task.groups registered
  change queue.GroupKeysIncluded
    (if task.groups.any (fun group => current.rootGroups.contains group.key)
        && (current.taskNode? task.occurrence).isNone then
      { current with taskNodes := current.taskNodes ++ [{ task }] }
    else current)
  split <;> exact linked

/-- Integration retains every previously live group key.
Witness: group registration appends records, task registration changes memberships only,
and stream attachment leaves the group map unchanged.
-/
theorem State.maybeIntegrateWork_includesKeys (queue : State)
    (newWork : Work) (parentTask : Option Occurrence)
    : queue.GroupKeysIncluded (queue.maybeIntegrateWork newWork parentTask).1 := by
  let withGroups := (queue.addGroups newWork.groups).1
  let withTasks := newWork.tasks.foldl State.addTask withGroups
  have taskFold (more : List Task) :
      ∀ current : State,
        current.GroupKeysIncluded (more.foldl State.addTask current) := by
    induction more with
    | nil => intro current key member; exact member
    | cons task rest ih =>
        intro current
        exact (current.addTask_includesKeys task).trans
          (ih (current.addTask task))
  have groupIncluded : queue.GroupKeysIncluded withGroups :=
    queue.addGroups_includesKeys newWork.groups
  have taskIncluded : withGroups.GroupKeysIncluded withTasks :=
    taskFold newWork.tasks withGroups
  change queue.GroupKeysIncluded
    (withTasks.addStreams newWork.streams parentTask).1
  exact (groupIncluded.trans taskIncluded).trans (by
    intro key member
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
  intro key rootMember
  have unchanged := State.maybeIntegrateWork_rootGroups queue newWork parentTask
  rw [unchanged] at rootMember
  exact (queue.maybeIntegrateWork_includesKeys newWork parentTask)
    key (present key rootMember)

/-- Restrict root links to a fixed list of the currently active contributor
keys, so the general task-link lemmas can be reused.
-/
theorem State.RootTaskLinkedOn.activeKeys
    {queue : State} {occurrence : Occurrence} {keys : Keys}
    (linked : queue.RootTaskLinkedOn occurrence keys)
    : queue.TaskLinkedOn occurrence
        (keys.filter (fun key => queue.rootGroups.contains key)) := by
  intro node member keyMember
  have inKeys : node.group.node.key ∈ keys := (List.mem_filter.mp keyMember).1
  have inRoots : node.group.node.key ∈ queue.rootGroups := by
    have contained := (List.mem_filter.mp keyMember).2
    obtain ⟨candidate, prior, same⟩ :=
      List.contains_iff_exists_mem_beq.mp contained
    have equal := beq_iff_eq.mp same
    exact equal.symm ▸ prior
  exact linked node member inRoots inKeys

/-- Convert a fixed active-key link back to the state-indexed root predicate
when an operation has not changed the root key list.
-/
theorem State.TaskLinkedOn.ofActiveKeys
    {before after : State} {occurrence : Occurrence} {keys : Keys}
    (linked
      : after.TaskLinkedOn occurrence
          (keys.filter (fun key => before.rootGroups.contains key)))
    (sameRoots : after.rootGroups = before.rootGroups)
    : after.RootTaskLinkedOn occurrence keys := by
  intro node member inRoots inKeys
  rw [sameRoots] at inRoots
  exact linked node member
    (List.mem_filter.mpr
      ⟨
        inKeys,
        (List.contains_iff_exists_mem_beq).mpr ⟨node.group.node.key, inRoots, by simp⟩
      ⟩)

/-- Registering another task adds memberships but does not disturb the
active-root links of an already registered task.
-/
theorem State.RootTaskLinkedOn.addTask
    {queue : State} (unique : queue.GroupKeysUnique)
    {occurrence : Occurrence} {keys : Keys}
    (linked : queue.RootTaskLinkedOn occurrence keys) (task : Task)
    : (queue.addTask task).RootTaskLinkedOn occurrence keys :=
  ((linked.activeKeys).addTask unique task).ofActiveKeys
    (State.addTask_rootGroups queue task)

/-- Integrating child work preserves links to active roots without ruling out
re-creation of failed, nonroot shells. The only premise is that active root
keys still have live nodes before the integration.
-/
theorem State.RootTaskLinkedOn.maybeIntegrateWork
    {queue : State} (unique : queue.GroupKeysUnique)
    (rootsPresent : queue.RootGroupsPresent)
    {occurrence : Occurrence} {keys : Keys}
    (linked : queue.RootTaskLinkedOn occurrence keys)
    (newWork : Work) (parentTask : Option Occurrence)
    : (queue.maybeIntegrateWork newWork parentTask).1.RootTaskLinkedOn
        occurrence keys := by
  let activeKeys := keys.filter (fun key => queue.rootGroups.contains key)
  have activeLinked : queue.TaskLinkedOn occurrence activeKeys :=
    linked.activeKeys
  have relevantExisting :
      ∀ group ∈ newWork.groups, group.node.key ∈ activeKeys
        → ∃ node ∈ queue.groupNodes, node.group.node.key = group.node.key := by
    intro group _ member
    have inRoots : group.node.key ∈ queue.rootGroups := by
      have contained := (List.mem_filter.mp member).2
      obtain ⟨candidate, prior, same⟩ :=
        List.contains_iff_exists_mem_beq.mp contained
      have equal := beq_iff_eq.mp same
      exact equal.symm ▸ prior
    exact List.mem_map.mp (rootsPresent group.node.key inRoots)
  have afterLinked := activeLinked.maybeIntegrateWork unique newWork parentTask
    relevantExisting
  exact afterLinked.ofActiveKeys
    (State.maybeIntegrateWork_rootGroups queue newWork parentTask)

/-- Removing a failed group also removes it from active roots, preserving
root-restricted task links for every remaining group.
-/
theorem State.RootTaskLinkedOn.removeGroup
    {queue : State} {occurrence : Occurrence} {keys : Keys}
    (linked : queue.RootTaskLinkedOn occurrence keys) (key : Nat)
    : (queue.removeGroup key).RootTaskLinkedOn occurrence keys := by
  intro node nodeMember rootMember keyMember
  unfold State.removeGroup at nodeMember rootMember
  exact linked node (List.mem_filter.mp nodeMember).1
    (List.mem_filter.mp rootMember).1 keyMember

/-- Group removal filters the same keys from the root list and node map. -/
theorem State.RootGroupsPresent.removeGroup
    {queue : State} (present : queue.RootGroupsPresent) (key : Nat)
    : (queue.removeGroup key).RootGroupsPresent := by
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

/-- Failure settlement preserves active-root links of a different task.
Witness: the failed membership is removed, while latent error updates retain all other
memberships and active failures remove entire nodes.
-/
theorem State.RootTaskLinkedOn.taskFailure
    {queue : State} {occurrence : Occurrence} {keys : Keys}
    (linked : queue.RootTaskLinkedOn occurrence keys)
    (failed : Occurrence) (errors : Nat) (different : occurrence ≠ failed)
    : (queue.taskFailure failed errors).1.RootTaskLinkedOn occurrence keys := by
  let step (acc : State × List WorkQueueEvent)
      (group : Execution.DeliveryNode) :=
    let (current, events) := acc
    match current.groupNode? group.key with
    | none => (current, events)
    | some node =>
        if current.rootGroups.contains group.key then
          let (next, failure) := current.finishGroupFailure node errors
          (next, events ++ [failure])
        else
          (current.putGroupNode
            { node with
                pending := node.pending - 1
                failure := some (node.failure.getD 0 + errors) }, events)
  have stepLinked (acc : State × List WorkQueueEvent)
      (group : Execution.DeliveryNode)
      (currentLinked : acc.1.RootTaskLinkedOn occurrence keys)
      : (step acc group).1.RootTaskLinkedOn occurrence keys := by
    obtain ⟨current, events⟩ := acc
    dsimp only [step]
    split
    · exact currentLinked
    · rename_i node found
      split
      · rw [State.finishGroupFailure, State.groupNode?_key found]
        exact currentLinked.removeGroup group.key
      · intro target targetMember rootMember keyMember
        obtain ⟨old, oldMember, same⟩ := List.mem_map.mp targetMember
        split at same
        · subst target
          exact currentLinked node (List.mem_of_find?_eq_some found) rootMember keyMember
        · subst target
          exact currentLinked old oldMember rootMember keyMember
  have foldLinked (groups : List Execution.DeliveryNode) :
      ∀ acc : State × List WorkQueueEvent,
        acc.1.RootTaskLinkedOn occurrence keys
          → (groups.foldl step acc).1.RootTaskLinkedOn occurrence keys := by
    induction groups with
    | nil => intro acc currentLinked; exact currentLinked
    | cons group rest ih =>
        intro acc currentLinked
        exact ih (step acc group) (stepLinked acc group currentLinked)
  unfold State.taskFailure
  split
  · exact linked
  · rename_i taskNode found
    let current := queue.removeTask failed
    have currentLinked : current.RootTaskLinkedOn occurrence keys :=
      (linked.activeKeys.removeOtherTask failed different).ofActiveKeys rfl
    split <;> try exact currentLinked
    change (taskNode.task.groups.foldl step (current, [])).1.RootTaskLinkedOn
      occurrence keys
    exact foldLinked taskNode.task.groups (current, []) currentLinked

/-- Failure settlement cannot orphan the root groups that survive it. -/
theorem State.RootGroupsPresent.taskFailure
    {queue : State} (present : queue.RootGroupsPresent)
    (failed : Occurrence) (errors : Nat)
    : (queue.taskFailure failed errors).1.RootGroupsPresent := by
  let step (acc : State × List WorkQueueEvent)
      (group : Execution.DeliveryNode) :=
    let (current, events) := acc
    match current.groupNode? group.key with
    | none => (current, events)
    | some node =>
        if current.rootGroups.contains group.key then
          let (next, failure) := current.finishGroupFailure node errors
          (next, events ++ [failure])
        else
          (current.putGroupNode
            { node with
                pending := node.pending - 1
                failure := some (node.failure.getD 0 + errors) }, events)
  have stepPresent (acc : State × List WorkQueueEvent)
      (group : Execution.DeliveryNode)
      (currentPresent : acc.1.RootGroupsPresent)
      : (step acc group).1.RootGroupsPresent := by
    obtain ⟨current, events⟩ := acc
    dsimp only [step]
    split
    · exact currentPresent
    · rename_i node found
      split
      · rw [State.finishGroupFailure, State.groupNode?_key found]
        exact currentPresent.removeGroup group.key
      · intro key rootMember
        rw [State.putGroupNode_keys]
        exact currentPresent key rootMember
  have foldPresent (groups : List Execution.DeliveryNode) :
      ∀ acc : State × List WorkQueueEvent,
        acc.1.RootGroupsPresent
          → (groups.foldl step acc).1.RootGroupsPresent := by
    induction groups with
    | nil => intro acc currentPresent; exact currentPresent
    | cons group rest ih =>
        intro acc currentPresent
        exact ih (step acc group) (stepPresent acc group currentPresent)
  unfold State.taskFailure
  split
  · exact present
  · rename_i taskNode found
    let current := queue.removeTask failed
    have currentPresent : current.RootGroupsPresent := by
      simpa [current, State.RootGroupsPresent, State.removeTask, List.map_map]
        using present
    split <;> try exact currentPresent
    change (taskNode.task.groups.foldl step (current, [])).1.RootGroupsPresent
    exact foldPresent taskNode.task.groups (current, []) currentPresent

/-- Surviving started nodes were already present and do not name the failed task.
Witness: the initial task filter followed by deletion-only failure-owner processing.
-/
theorem State.taskFailure_startedSurvivor (queue : State)
    (failed : Occurrence) (errors : Nat)
    {taskNode : TaskNode}
    (member : taskNode ∈ (queue.taskFailure failed errors).1.taskNodes)
    : taskNode ∈ queue.taskNodes ∧ taskNode.task.occurrence ≠ failed := by
  let step (acc : State × List WorkQueueEvent)
      (group : Execution.DeliveryNode) :=
    let (current, events) := acc
    match current.groupNode? group.key with
    | none => (current, events)
    | some node =>
        if current.rootGroups.contains group.key then
          let (next, failure) := current.finishGroupFailure node errors
          (next, events ++ [failure])
        else
          (current.putGroupNode
            { node with
                pending := node.pending - 1
                failure := some (node.failure.getD 0 + errors) }, events)
  have stepSubset (acc : State × List WorkQueueEvent)
      (group : Execution.DeliveryNode)
      {node : TaskNode} (nodeMember : node ∈ (step acc group).1.taskNodes)
      : node ∈ acc.1.taskNodes := by
    obtain ⟨current, events⟩ := acc
    dsimp only [step] at nodeMember
    split at nodeMember
    · exact nodeMember
    · rename_i groupNode found
      split at nodeMember
      · unfold State.finishGroupFailure at nodeMember
        exact (List.mem_filter.mp nodeMember).1
      · exact nodeMember
  have foldSubset (groups : List Execution.DeliveryNode) :
      ∀ acc : State × List WorkQueueEvent,
        ∀ {node : TaskNode},
          node ∈ (groups.foldl step acc).1.taskNodes
            → node ∈ acc.1.taskNodes := by
    induction groups with
    | nil => intro acc node nodeMember; exact nodeMember
    | cons group rest ih =>
        intro acc node nodeMember
        exact stepSubset acc group (ih (step acc group) nodeMember)
  unfold State.taskFailure at member
  split at member
  · rename_i found
    refine ⟨member, ?_⟩
    intro same
    exact (List.find?_eq_none.mp found) taskNode member
      ((occurrence_beq_iff_eq _ _).mpr same)
  · rename_i failedNode found
    have original : taskNode ∈ (queue.removeTask failed).taskNodes := by
      split at member
      · exact member
      · exact foldSubset failedNode.task.groups (queue.removeTask failed, []) member
    obtain ⟨old, kept⟩ := List.mem_filter.mp original
    refine ⟨old, ?_⟩
    intro same
    have equal := (occurrence_beq_iff_eq _ _).mpr same
    simp [bne, equal] at kept

/-- Failure handling starts no new task nodes. Witness: the survivor theorem. -/
theorem State.taskFailure_startedSubset (queue : State)
    (failed : Occurrence) (errors : Nat)
    {taskNode : TaskNode}
    (member : taskNode ∈ (queue.taskFailure failed errors).1.taskNodes)
    : taskNode ∈ queue.taskNodes :=
  (queue.taskFailure_startedSurvivor failed errors member).1

/-- Registering one task either retains an old started node or appends that
task's fresh node; group membership updates do not rewrite task nodes.
-/
theorem State.addTask_startedOldOrNew (queue : State) (task : Task)
    {taskNode : TaskNode} (member : taskNode ∈ (queue.addTask task).taskNodes)
    : taskNode ∈ queue.taskNodes ∨ taskNode = { task } := by
  let step (current : State) (group : Execution.DeliveryNode) : State :=
    match current.groupNode? group.key with
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
    (if task.groups.any (fun group => current.rootGroups.contains group.key)
        && (current.taskNode? task.occurrence).isNone then
      { current with taskNodes := current.taskNodes ++ [{ task }] }
    else current).taskNodes at member
  split at member
  · rcases List.mem_append.mp member with old | new
    · exact Or.inl (currentNodes ▸ old)
    · exact Or.inr (List.mem_singleton.mp new)
  · exact Or.inl (currentNodes ▸ member)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
