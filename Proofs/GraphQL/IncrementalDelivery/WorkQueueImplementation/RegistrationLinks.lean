import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.MembershipSoundness

/-! Completeness and preservation of registration links. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (ExecutionGroupValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Completeness of links installed by one task registration
-----------------------------------------------------------------------------------------

/-- These refs, when present as live group nodes, already list the task
occurrence. This is the converse membership direction for one task.
-/
def State.TaskLinkedOn (queue : State) (occurrence : Occurrence) (refs : NodeRefs)
    : Prop :=
  ∀ node ∈ queue.groupNodes, node.group.node.ref ∈ refs → occurrence ∈ node.tasks

/-- Linking a task to every listed group establishes membership in every
currently live contributor group. This local fact does not yet say that later
queue transitions preserve the link.
-/
theorem State.addTask_links (queue : State) (unique : queue.GroupRefsUnique) (task : Task)
    : (queue.addTask task).TaskLinkedOn task.occurrence
        (task.groups.map Execution.DeliveryNode.ref) := by
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
  have stepLink (current : State) (group : Execution.DeliveryNode)
      (processed : NodeRefs)
      (currentUnique : current.GroupRefsUnique)
      (linked : current.TaskLinkedOn task.occurrence processed)
      : (step current group).GroupRefsUnique
        ∧ (step current group).TaskLinkedOn task.occurrence
            (processed ++ [group.ref]) := by
    dsimp only [step]
    cases found : current.groupNode? group.ref with
    | none =>
        refine ⟨currentUnique, ?_⟩
        intro node member refMember
        rcases List.mem_append.mp refMember with old | latest
        · exact linked node member old
        · simp only [List.mem_singleton] at latest
          have noMatch := (List.find?_eq_none.mp
            (show current.groupNodes.find?
              (fun candidate => candidate.group.node.ref == group.ref) = none
              from found)) node member
          exact False.elim (noMatch (beq_iff_eq.mpr latest))
    | some node =>
        simp only
        by_cases present : node.tasks.contains task.occurrence = true
        · simp only [present, ite_true]
          refine ⟨currentUnique, ?_⟩
          intro target targetMember refMember
          rcases List.mem_append.mp refMember with old | latest
          · exact linked target targetMember old
          · simp only [List.mem_singleton] at latest
            have sameNode : target = node :=
              currentUnique.sameNode targetMember
                (List.mem_of_find?_eq_some found)
                (latest.trans (State.groupNode?_ref found).symm)
            subst target
            obtain ⟨candidate, candidateMember, same⟩ :=
              List.contains_iff_exists_mem_beq.mp present
            have equal : task.occurrence = candidate :=
              (occurrence_beq_iff_eq _ _).mp same
            exact equal.symm ▸ candidateMember
        · simp only [present]
          have nextUnique := currentUnique.putGroupNode
            { node with tasks := node.tasks ++ [task.occurrence], pending := node.pending + 1 }
          refine ⟨nextUnique, ?_⟩
          intro target targetMember refMember
          let updated : GroupNode :=
            { node with tasks := node.tasks ++ [task.occurrence], pending := node.pending + 1 }
          simp only [Bool.false_eq_true, ite_false] at targetMember
          change target ∈ current.groupNodes.map
            (fun old => if old.group.node.ref == updated.group.node.ref then
              updated else old) at targetMember
          obtain ⟨old, oldMember, same⟩ := List.mem_map.mp targetMember
          by_cases equalRef : (old.group.node.ref == node.group.node.ref) = true
          · simp only [updated, equalRef, ite_true] at same
            subst target
            simp
          · simp only [updated, equalRef] at same
            subst target
            rcases List.mem_append.mp refMember with oldRef | newRef
            · exact linked old oldMember oldRef
            · simp only [List.mem_singleton] at newRef
              have equal : old.group.node.ref = node.group.node.ref :=
                newRef.trans (State.groupNode?_ref found).symm
              exact False.elim (equalRef (beq_iff_eq.mpr equal))
  have foldLink (more : List Execution.DeliveryNode) :
      ∀ current processed, current.GroupRefsUnique
        → current.TaskLinkedOn task.occurrence processed
        → (more.foldl step current).GroupRefsUnique
          ∧ (more.foldl step current).TaskLinkedOn task.occurrence
              (processed ++ more.map Execution.DeliveryNode.ref) := by
    induction more with
    | nil =>
        intro current processed currentUnique linked
        exact ⟨currentUnique, by simpa using linked⟩
    | cons group rest ih =>
        intro current processed currentUnique linked
        obtain ⟨nextUnique, nextLinked⟩ :=
          stepLink current group processed currentUnique linked
        have final := ih (step current group) (processed ++ [group.ref])
          nextUnique nextLinked
        simpa only [List.foldl_cons, List.map_cons, List.append_assoc,
          List.singleton_append] using final
  have registeredUnique : registered.GroupRefsUnique := unique
  have emptyLinked : registered.TaskLinkedOn task.occurrence [] := by
    intro node member impossible
    cases impossible
  let current := task.groups.foldl step registered
  have currentLinked : current.TaskLinkedOn task.occurrence
      (task.groups.map Execution.DeliveryNode.ref) := by
    have final := (foldLink task.groups registered [] registeredUnique emptyLinked).2
    simpa using final
  change (if task.groups.any (fun group => current.rootGroups.contains group.ref)
      && (current.taskNode? task.occurrence).isNone then
      { current with taskNodes := current.taskNodes ++ [{ task }] }
    else current).TaskLinkedOn task.occurrence
      (task.groups.map Execution.DeliveryNode.ref)
  split <;> exact currentLinked

/-- Registering another task never removes an existing task's links when live
group refs are unique; it only appends memberships to group task lists.
-/
theorem State.TaskLinkedOn.addTask
    {queue : State} (unique : queue.GroupRefsUnique)
    {occurrence : Occurrence} {refs : NodeRefs}
    (linked : queue.TaskLinkedOn occurrence refs) (task : Task)
    : (queue.addTask task).TaskLinkedOn occurrence refs := by
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
  have stepPreserve (current : State) (group : Execution.DeliveryNode)
      (currentUnique : current.GroupRefsUnique)
      (currentLinked : current.TaskLinkedOn occurrence refs)
      : (step current group).GroupRefsUnique
        ∧ (step current group).TaskLinkedOn occurrence refs := by
    dsimp only [step]
    cases found : current.groupNode? group.ref with
    | none => exact ⟨currentUnique, currentLinked⟩
    | some node =>
        simp only
        by_cases present : node.tasks.contains task.occurrence = true
        · simp only [present, ite_true]
          exact ⟨currentUnique, currentLinked⟩
        · simp only [present]
          let updated : GroupNode :=
            { node with tasks := node.tasks ++ [task.occurrence], pending := node.pending + 1 }
          have nextUnique : (current.putGroupNode updated).GroupRefsUnique :=
            currentUnique.putGroupNode updated
          refine ⟨nextUnique, ?_⟩
          intro target targetMember refMember
          simp only [Bool.false_eq_true, ite_false] at targetMember
          change target ∈ current.groupNodes.map
            (fun old => if old.group.node.ref == updated.group.node.ref then
              updated else old) at targetMember
          obtain ⟨old, oldMember, same⟩ := List.mem_map.mp targetMember
          by_cases equalRef : (old.group.node.ref == node.group.node.ref) = true
          · simp only [updated, equalRef, ite_true] at same
            subst target
            have oldEq : old = node :=
              currentUnique.sameNode oldMember
                (List.mem_of_find?_eq_some found)
                (beq_iff_eq.mp equalRef)
            subst old
            exact List.mem_append.mpr
              (Or.inl (currentLinked node
                (List.mem_of_find?_eq_some found) refMember))
          · simp only [updated, equalRef] at same
            subst target
            exact currentLinked old oldMember refMember
  have foldPreserve (more : List Execution.DeliveryNode) :
      ∀ current, current.GroupRefsUnique
        → current.TaskLinkedOn occurrence refs
        → (more.foldl step current).GroupRefsUnique
          ∧ (more.foldl step current).TaskLinkedOn occurrence refs := by
    induction more with
    | nil =>
        intro current currentUnique currentLinked
        exact ⟨currentUnique, currentLinked⟩
    | cons group rest ih =>
        intro current currentUnique currentLinked
        obtain ⟨nextUnique, nextLinked⟩ :=
          stepPreserve current group currentUnique currentLinked
        exact ih (step current group) nextUnique nextLinked
  have registeredUnique : registered.GroupRefsUnique := unique
  have registeredLinked : registered.TaskLinkedOn occurrence refs := linked
  let current := task.groups.foldl step registered
  have currentLinked : current.TaskLinkedOn occurrence refs :=
    (foldPreserve task.groups registered registeredUnique registeredLinked).2
  change (if task.groups.any (fun group => current.rootGroups.contains group.ref)
      && (current.taskNode? task.occurrence).isNone then
      { current with taskNodes := current.taskNodes ++ [{ task }] }
    else current).TaskLinkedOn occurrence refs
  split <;> exact currentLinked

/-- Registering a group preserves an existing task link exactly when a newly
created group cannot be a previously missing contributor of that task.
-/
theorem State.TaskLinkedOn.addGroup
    {queue : State} {occurrence : Occurrence} {refs : NodeRefs}
    (linked : queue.TaskLinkedOn occurrence refs) (group : Group)
    (noRelevantNewGroup : queue.groupNode? group.node.ref = none → group.node.ref ∉ refs)
    : (queue.addGroup group).TaskLinkedOn occurrence refs := by
  unfold State.addGroup
  split
  · exact linked
  · rename_i fresh
    have found : queue.groupNode? group.node.ref = none :=
      (by simpa using fresh : group.node.ref ∉ queue.registeredGroups
        ∧ queue.groupNode? group.node.ref = none).2
    split
    · exact linked
    · intro current member refMember
      rcases List.mem_append.mp member with earlier | added
      · exact linked current earlier refMember
      · simp only [List.mem_singleton] at added
        subst current
        exact False.elim (noRelevantNewGroup found refMember)

/-- Updating non-membership metadata of a unique live group preserves every
existing task link. The replacement keeps that group's ref and task list.
-/
theorem State.TaskLinkedOn.putGroupNodeSameTasks
    {queue : State} (unique : queue.GroupRefsUnique)
    {occurrence : Occurrence} {refs : NodeRefs}
    (linked : queue.TaskLinkedOn occurrence refs)
    (node : GroupNode) (member : node ∈ queue.groupNodes)
    (updated : GroupNode)
    (sameRef : updated.group.node.ref = node.group.node.ref)
    (sameTasks : updated.tasks = node.tasks)
    : (queue.putGroupNode updated).TaskLinkedOn occurrence refs := by
  intro target targetMember refMember
  change target ∈ queue.groupNodes.map
    (fun old => if old.group.node.ref == updated.group.node.ref then updated else old)
    at targetMember
  obtain ⟨old, oldMember, same⟩ := List.mem_map.mp targetMember
  by_cases equalRef : (old.group.node.ref == updated.group.node.ref) = true
  · simp only [equalRef, ite_true] at same
    subst target
    have oldEq : old = node :=
      unique.sameNode oldMember member
        ((beq_iff_eq.mp equalRef).trans sameRef)
    subst old
    rw [sameTasks]
    exact linked node member (sameRef ▸ refMember)
  · simp only [equalRef] at same
    subst target
    exact linked old oldMember refMember

/-- Group registration never removes a preexisting live group node. -/
theorem State.addGroup_preservesExisting
    (queue : State) (group : Group)
    {node : GroupNode} (member : node ∈ queue.groupNodes)
    : node ∈ (queue.addGroup group).groupNodes := by
  unfold State.addGroup
  split
  · exact member
  · split
    · exact member
    · exact List.mem_append.mpr (Or.inl member)

/-- Adding a whole group collection preserves existing task links provided
each relevant group descriptor already has a live node before integration.
This isolates the no-late-reintroduction premise needed for queue replay.
-/
theorem State.TaskLinkedOn.addGroups
    {queue : State} (unique : queue.GroupRefsUnique)
    {occurrence : Occurrence} {refs : NodeRefs}
    (linked : queue.TaskLinkedOn occurrence refs)
    (groups : List Group)
    (relevantExisting
      : ∀ group ∈ groups,
          group.node.ref ∈ refs
          → ∃ node ∈ queue.groupNodes, node.group.node.ref = group.node.ref)
    : (queue.addGroups groups).1.TaskLinkedOn occurrence refs := by
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
  have registrationFold (more : List Group)
      (subset : ∀ group ∈ more, group ∈ groups) :
      ∀ current,
        current.GroupRefsUnique
        → current.TaskLinkedOn occurrence refs
        → (∀ node ∈ queue.groupNodes, node ∈ current.groupNodes)
        → (more.foldl State.addGroup current).GroupRefsUnique
          ∧ (more.foldl State.addGroup current).TaskLinkedOn occurrence refs := by
    induction more with
    | nil =>
        intro current currentUnique currentLinked _
        exact ⟨currentUnique, currentLinked⟩
    | cons group rest ih =>
        intro current currentUnique currentLinked priorPreserved
        have groupMember : group ∈ groups := subset group (by simp)
        have noRelevantNew : current.groupNode? group.node.ref = none
            → group.node.ref ∉ refs := by
          intro missing refMember
          obtain ⟨node, original, sameRef⟩ :=
            relevantExisting group groupMember refMember
          have live : node ∈ current.groupNodes := priorPreserved node original
          have noMatch := (List.find?_eq_none.mp
            (show current.groupNodes.find?
              (fun candidate => candidate.group.node.ref == group.node.ref) = none
              from missing)) node live
          exact noMatch (beq_iff_eq.mpr sameRef)
        have nextUnique : (current.addGroup group).GroupRefsUnique :=
          currentUnique.addGroup group
        have nextLinked : (current.addGroup group).TaskLinkedOn occurrence refs :=
          currentLinked.addGroup group noRelevantNew
        have nextPreserved : ∀ node ∈ queue.groupNodes,
            node ∈ (current.addGroup group).groupNodes := by
          intro node original
          exact current.addGroup_preservesExisting group
            (priorPreserved node original)
        have restSubset : ∀ candidate ∈ rest, candidate ∈ groups := by
          intro candidate member
          exact subset candidate (by simp [member])
        simpa only [List.foldl_cons]
          using ih restSubset (current.addGroup group) nextUnique nextLinked nextPreserved
  let fresh := groups.filter (fun group =>
    !queue.registeredGroups.contains group.node.ref
      && (queue.groupNode? group.node.ref).isNone)
  have registered : (fresh.foldl State.addGroup queue).GroupRefsUnique
      ∧ (fresh.foldl State.addGroup queue).TaskLinkedOn occurrence refs :=
    registrationFold fresh (fun _ member => (List.mem_filter.mp member).1) queue unique linked
      (fun _ member => member)
  have linkPreserve (current : State) (group : Group)
      (currentUnique : current.GroupRefsUnique)
      (currentLinked : current.TaskLinkedOn occurrence refs)
      : (linkStep current group).GroupRefsUnique
        ∧ (linkStep current group).TaskLinkedOn occurrence refs := by
    unfold linkStep
    cases parentEq : group.parent with
    | none => simpa only [parentEq] using And.intro currentUnique currentLinked
    | some parent =>
        cases found : current.groupNode? parent with
        | none =>
            simpa only [parentEq, found] using And.intro currentUnique currentLinked
        | some node =>
            simp only [found]
            have member : node ∈ current.groupNodes := List.mem_of_find?_eq_some found
            exact ⟨currentUnique.putGroupNode _,
              currentLinked.putGroupNodeSameTasks currentUnique node member _ rfl rfl⟩
  have linkFold (more : List Group) :
      ∀ current, current.GroupRefsUnique
        → current.TaskLinkedOn occurrence refs
        → (more.foldl linkStep current).TaskLinkedOn occurrence refs := by
    induction more with
    | nil => intro current _ currentLinked; exact currentLinked
    | cons group rest ih =>
        intro current currentUnique currentLinked
        obtain ⟨nextUnique, nextLinked⟩ :=
          linkPreserve current group currentUnique currentLinked
        exact ih (linkStep current group) nextUnique nextLinked
  change (fresh.foldl linkStep
    (fresh.foldl State.addGroup queue)).TaskLinkedOn occurrence refs
  exact linkFold fresh _ registered.1 registered.2

/-- Stream registration cannot change any group task membership. -/
theorem State.TaskLinkedOn.addStreams
    {queue : State} {occurrence : Occurrence} {refs : NodeRefs}
    (linked : queue.TaskLinkedOn occurrence refs)
    (streams : List Stream) (parentTask : Option Occurrence)
    : (queue.addStreams streams parentTask).1.TaskLinkedOn occurrence refs := by
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
  have currentLinked : current.TaskLinkedOn occurrence refs := linked
  cases parentTask with
  | none => exact currentLinked
  | some parent =>
      simp only [State.addStreams]
      split <;> exact currentLinked

/-- Child Work integration preserves an older task's links if it never
introduces a group newly relevant to that task. Task registration itself only
adds links; the freshness condition is confined to group introduction.
-/
theorem State.TaskLinkedOn.maybeIntegrateWork
    {queue : State} (unique : queue.GroupRefsUnique)
    {occurrence : Occurrence} {refs : NodeRefs}
    (linked : queue.TaskLinkedOn occurrence refs)
    (newWork : Work) (parentTask : Option Occurrence)
    (relevantExisting
      : ∀ group ∈ newWork.groups,
          group.node.ref ∈ refs
          → ∃ node ∈ queue.groupNodes, node.group.node.ref = group.node.ref)
    : (queue.maybeIntegrateWork newWork parentTask).1.TaskLinkedOn occurrence refs := by
  let withGroups := (queue.addGroups newWork.groups).1
  let withTasks := newWork.tasks.foldl State.addTask withGroups
  have groupLinked : withGroups.TaskLinkedOn occurrence refs :=
    linked.addGroups unique newWork.groups relevantExisting
  have groupUnique : withGroups.GroupRefsUnique :=
    unique.addGroups newWork.groups
  have taskFold (tasks : List Task) :
      ∀ current, current.GroupRefsUnique
        → current.TaskLinkedOn occurrence refs
        → (tasks.foldl State.addTask current).TaskLinkedOn occurrence refs := by
    induction tasks with
    | nil => intro current _ currentLinked; exact currentLinked
    | cons task rest ih =>
        intro current currentUnique currentLinked
        exact ih (current.addTask task) (currentUnique.addTask task)
          (currentLinked.addTask currentUnique task)
  have taskLinked : withTasks.TaskLinkedOn occurrence refs :=
    taskFold newWork.tasks withGroups groupUnique groupLinked
  change (withTasks.addStreams newWork.streams parentTask).1.TaskLinkedOn
    occurrence refs
  exact taskLinked.addStreams newWork.streams parentTask

/-- Removing group nodes cannot break a link in any group node that remains. -/
theorem State.TaskLinkedOn.removeGroup
    {queue : State} {occurrence : Occurrence} {refs : NodeRefs}
    (linked : queue.TaskLinkedOn occurrence refs) (ref : NodeRef)
    : (queue.removeGroup ref).TaskLinkedOn occurrence refs := by
  intro node member refMember
  unfold State.removeGroup at member
  have oldMember : node ∈ queue.groupNodes :=
    (List.mem_filter.mp member).1
  exact linked node oldMember refMember

/-- Removing a different task does not disturb this task's group links. -/
theorem State.TaskLinkedOn.removeOtherTask
    {queue : State} {occurrence : Occurrence} {refs : NodeRefs}
    (linked : queue.TaskLinkedOn occurrence refs)
    (other : Occurrence) (different : occurrence ≠ other)
    : (queue.removeTask other).TaskLinkedOn occurrence refs := by
  intro node member refMember
  change node ∈ queue.groupNodes.map
    (fun prior => { prior with tasks := prior.tasks.filter (· != other) })
    at member
  obtain ⟨prior, priorMember, same⟩ := List.mem_map.mp member
  subst node
  have listed : occurrence ∈ prior.tasks := linked prior priorMember refMember
  exact List.mem_filter.mpr
    ⟨
      listed,
      by
        cases equal : occurrence == other with
        | false => simp [bne, equal]
        | true => exact False.elim (different ((occurrence_beq_iff_eq _ _).mp equal))
    ⟩

/-- A change to non-group state leaves every task membership assertion intact. -/
private theorem State.TaskLinkedOn.of_sameGroupNodes
    {queue next : State} {occurrence : Occurrence} {refs : NodeRefs}
    (linked : queue.TaskLinkedOn occurrence refs)
    (same : next.groupNodes = queue.groupNodes)
    : next.TaskLinkedOn occurrence refs := by
  intro node member refMember
  exact linked node (same ▸ member) refMember

/-- Pruning removes only group shells; links in surviving groups remain valid. -/
theorem State.TaskLinkedOn.pruneEmptyGroups
    {queue : State} {occurrence : Occurrence} {refs : NodeRefs}
    (linked : queue.TaskLinkedOn occurrence refs)
    (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.TaskLinkedOn occurrence refs := by
  have loop (fuel : Nat) (current : State)
      (remaining kept : List Execution.DeliveryNode)
      (currentLinked : current.TaskLinkedOn occurrence refs)
      : (State.pruneEmptyGroups.go fuel current remaining kept).1.TaskLinkedOn
          occurrence refs := by
    induction fuel generalizing current remaining kept with
    | zero => exact currentLinked
    | succ fuel ih =>
        cases remaining with
        | nil => exact currentLinked
        | cons group rest =>
            unfold State.pruneEmptyGroups.go
            split
            · exact ih _ _ _ currentLinked
            · split
              · apply ih
                intro node member refMember
                exact currentLinked node (List.mem_filter.mp member).1 refMember
              · exact ih _ _ _ currentLinked
  exact loop _ queue groups [] linked

/-- Starting an already registered task leaves the group-node map untouched. -/
theorem State.TaskLinkedOn.startTask
    {queue : State} {occurrence : Occurrence} {refs : NodeRefs}
    (linked : queue.TaskLinkedOn occurrence refs) (task : Occurrence)
    : (queue.startTask task).TaskLinkedOn occurrence refs := by
  unfold State.startTask
  split <;> (first | exact linked | split <;> exact linked)

/-- Starting all tasks under a group preserves the existing group links. -/
theorem State.TaskLinkedOn.startGroup
    {queue : State} {occurrence : Occurrence} {refs : NodeRefs}
    (linked : queue.TaskLinkedOn occurrence refs) (ref : NodeRef)
    : (queue.startGroup ref).TaskLinkedOn occurrence refs := by
  unfold State.startGroup
  split
  · exact linked
  · rename_i node found
    have foldStart (tasks : List Occurrence) :
        ∀ current, current.TaskLinkedOn occurrence refs
          → (tasks.foldl State.startTask current).TaskLinkedOn occurrence refs := by
      induction tasks with
      | nil => intro current currentLinked; exact currentLinked
      | cons task rest ih =>
          intro current currentLinked
          exact ih (current.startTask task) (currentLinked.startTask task)
    split
    · exact linked
    · exact foldStart node.tasks queue linked

theorem State.TaskLinkedOn.startStream
    {queue : State} {occurrence : Occurrence} {refs : NodeRefs}
    (linked : queue.TaskLinkedOn occurrence refs) (ref : NodeRef)
    : (queue.startStream ref).TaskLinkedOn occurrence refs := by
  unfold State.startStream
  split <;> exact linked

/-- Activating roots changes no group task lists. -/
theorem State.TaskLinkedOn.startNewWork
    {queue : State} {occurrence : Occurrence} {refs : NodeRefs}
    (linked : queue.TaskLinkedOn occurrence refs) (newWork : NewWork)
    : (queue.startNewWork newWork).TaskLinkedOn occurrence refs := by
  let groups := newWork.newGroups.map Execution.DeliveryNode.ref
  let streams := newWork.newStreams.map Execution.DeliveryNode.ref
  let current : State := { queue with rootGroups := queue.rootGroups ++ groups }
  have currentLinked : current.TaskLinkedOn occurrence refs := linked
  have groupFold (more : NodeRefs) :
      ∀ state, state.TaskLinkedOn occurrence refs
        → (more.foldl State.startGroup state).TaskLinkedOn occurrence refs := by
    induction more with
    | nil => intro state stateLinked; exact stateLinked
    | cons ref rest ih =>
        intro state stateLinked
        exact ih (state.startGroup ref) (stateLinked.startGroup ref)
  have streamFold (more : NodeRefs) :
      ∀ state, state.TaskLinkedOn occurrence refs
        → (more.foldl State.startStream state).TaskLinkedOn occurrence refs := by
    induction more with
    | nil => intro state stateLinked; exact stateLinked
    | cons ref rest ih =>
        intro state stateLinked
        exact ih (state.startStream ref) (stateLinked.startStream ref)
  change (streams.foldl State.startStream
    (groups.foldl State.startGroup current)).TaskLinkedOn occurrence refs
  exact streamFold streams _ (groupFold groups current currentLinked)

/-- Flushing a group preserves the links of a task outside that group's
membership list. The flushed tasks themselves are removed from live nodes.
-/
theorem State.TaskLinkedOn.finishOtherGroupSuccess
    {queue : State} {occurrence : Occurrence} {refs : NodeRefs}
    (linked : queue.TaskLinkedOn occurrence refs)
    (group : GroupNode) (outside : occurrence ∉ group.tasks)
    : (queue.finishGroupSuccess group).1.TaskLinkedOn occurrence refs := by
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
  have stepLinked (acc : State × List ExecutionGroupValue × NodeRefs)
      (task : Occurrence) (different : occurrence ≠ task)
      (currentLinked : acc.1.TaskLinkedOn occurrence refs)
      : (step acc task).1.TaskLinkedOn occurrence refs := by
    obtain ⟨current, values, streams⟩ := acc
    dsimp only [step]
    split
    · exact currentLinked
    · exact currentLinked.removeOtherTask task different
  have foldLinked (remaining : List Occurrence)
      (subset : ∀ task ∈ remaining, task ∈ group.tasks) :
      ∀ acc : State × List ExecutionGroupValue × NodeRefs,
        acc.1.TaskLinkedOn occurrence refs
          → (remaining.foldl step acc).1.TaskLinkedOn occurrence refs := by
    induction remaining with
    | nil => intro acc currentLinked; exact currentLinked
    | cons task rest ih =>
        intro acc currentLinked
        have different : occurrence ≠ task := by
          intro same
          exact outside (same ▸ subset task (by simp))
        have restSubset : ∀ candidate ∈ rest, candidate ∈ group.tasks := by
          intro candidate member
          exact subset candidate (by simp [member])
        exact ih restSubset (step acc task)
          (stepLinked acc task different currentLinked)
  let flushed := (group.tasks.foldl step (queue, [], [])).1
  have flushedLinked : flushed.TaskLinkedOn occurrence refs :=
    foldLinked group.tasks (fun _ member => member) (queue, [], []) linked
  let current : State :=
    { flushed with
        groupNodes := flushed.groupNodes.filter
          (fun node => node.group.node.ref != group.group.node.ref)
        rootGroups := flushed.rootGroups.filter (· != group.group.node.ref) }
  have currentLinked : current.TaskLinkedOn occurrence refs := by
    intro node member refMember
    exact flushedLinked node (List.mem_filter.mp member).1 refMember
  let children := group.childGroups.filterMap
    (fun ref => (current.groupNode? ref).map (fun node => node.group.node))
  change (current.pruneEmptyGroups children).1.TaskLinkedOn occurrence refs
  exact currentLinked.pruneEmptyGroups children

/-- Replacing a live group's counter and failure cache preserves another task's
links. Witness: the replacement keeps the found node's ref and task list.
-/
private theorem State.TaskLinkedOn.retainFailure
    {queue : State} {occurrence : Occurrence} {refs : NodeRefs}
    (linked : queue.TaskLinkedOn occurrence refs)
    (node : GroupNode) (member : node ∈ queue.groupNodes) (errors : Nat)
    : (queue.putGroupNode
        {
          node with
            pending := node.pending - 1
            failure := some (node.failure.getD 0 + errors)
        }).TaskLinkedOn
        occurrence refs := by
  intro target targetMember relevant
  obtain ⟨old, oldMember, same⟩ := List.mem_map.mp targetMember
  split at same
  · subst target
    exact linked node member relevant
  · subst target
    exact linked old oldMember relevant

/-- A failed task preserves a different task's links in all surviving owners.
Witness: membership removal affects only the failed occurrence; the owner fold either
removes nodes or changes only counters and cached errors.
-/
theorem State.TaskLinkedOn.taskFailure
    {queue : State} {occurrence : Occurrence} {refs : NodeRefs}
    (linked : queue.TaskLinkedOn occurrence refs)
    (failed : Occurrence) (errors : Nat) (different : occurrence ≠ failed)
    : (queue.taskFailure failed errors).1.TaskLinkedOn occurrence refs := by
  let step (acc : State × List WorkQueueEvent)
      (group : Execution.DeliveryNode) :=
    let (current, events) := acc
    match current.groupNode? group.ref with
    | none => (current, events)
    | some node =>
        if current.rootGroups.contains group.ref then
          let (next, failure) := current.finishGroupFailure node errors
          (next, events ++ [failure])
        else
          (current.putGroupNode
            { node with
                pending := node.pending - 1
                failure := some (node.failure.getD 0 + errors) }, events)
  have stepLinked (acc : State × List WorkQueueEvent)
      (group : Execution.DeliveryNode)
      (currentLinked : acc.1.TaskLinkedOn occurrence refs)
      : (step acc group).1.TaskLinkedOn occurrence refs := by
    obtain ⟨current, events⟩ := acc
    dsimp only [step]
    split
    · exact currentLinked
    · rename_i node found
      split
      · rw [State.finishGroupFailure, State.groupNode?_ref found]
        exact currentLinked.removeGroup group.ref
      · exact currentLinked.retainFailure node (List.mem_of_find?_eq_some found) errors
  have foldLinked (groups : List Execution.DeliveryNode) :
      ∀ acc : State × List WorkQueueEvent,
        acc.1.TaskLinkedOn occurrence refs
          → (groups.foldl step acc).1.TaskLinkedOn occurrence refs := by
    induction groups with
    | nil => intro acc currentLinked; exact currentLinked
    | cons group rest ih =>
        intro acc currentLinked
        exact ih (step acc group) (stepLinked acc group currentLinked)
  unfold State.taskFailure
  split
  · exact linked
  · rename_i taskNode found
    split <;> try exact linked.removeOtherTask failed different
    let current := queue.removeTask failed
    have currentLinked : current.TaskLinkedOn occurrence refs :=
      linked.removeOtherTask failed different
    change (taskNode.task.groups.foldl step (current, [])).1.TaskLinkedOn
      occurrence refs
    exact foldLinked taskNode.task.groups (current, []) currentLinked

/-- Stream closure does not change group nodes or their task memberships. -/
theorem State.TaskLinkedOn.streamSuccess
    {queue : State} {occurrence : Occurrence} {refs : NodeRefs}
    (linked : queue.TaskLinkedOn occurrence refs)
    (stream : Execution.DeliveryNode)
    : (queue.streamSuccess stream).1.TaskLinkedOn occurrence refs := by
  unfold State.streamSuccess
  split <;> exact linked

theorem State.TaskLinkedOn.streamFailure
    {queue : State} {occurrence : Occurrence} {refs : NodeRefs}
    (linked : queue.TaskLinkedOn occurrence refs)
    (stream : Execution.DeliveryNode) (errors : Nat)
    : (queue.streamFailure stream errors).1.TaskLinkedOn occurrence refs := by
  unfold State.streamFailure
  split <;> exact linked

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
