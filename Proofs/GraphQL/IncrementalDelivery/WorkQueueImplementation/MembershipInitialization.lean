import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialCounts

/-! Unique task membership during queue initialization. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Every live group's membership list names each task at most once. -/
def State.TaskMembershipsUnique (queue : State) : Prop :=
  ∀ node ∈ queue.groupNodes, node.tasks.Nodup

/-- Replacing a group node preserves unique memberships when the new node has them. -/
theorem State.TaskMembershipsUnique.putGroupNode {queue : State}
    (unique : queue.TaskMembershipsUnique) (updated : GroupNode)
    (updatedUnique : updated.tasks.Nodup)
    : (queue.putGroupNode updated).TaskMembershipsUnique := by
  intro node member
  change node ∈ queue.groupNodes.map
    (fun old => if old.group.node.key == updated.group.node.key then updated else old)
    at member
  obtain ⟨old, oldMember, same⟩ := List.mem_map.mp member
  split at same
  · subst node
    exact updatedUnique
  · subst node
    exact unique old oldMember

/-- Registering an empty group preserves unique task memberships. -/
theorem State.TaskMembershipsUnique.addGroup {queue : State}
    (unique : queue.TaskMembershipsUnique) (group : Group)
    : (queue.addGroup group).TaskMembershipsUnique := by
  unfold State.addGroup
  split
  · exact unique
  · split
    · exact unique
    · intro node member
      simp only [List.mem_append, List.mem_singleton] at member
      rcases member with earlier | new
      · exact unique node earlier
      · subst node
        simp

/-- Parent-link registration leaves every group's task list unchanged. -/
theorem State.TaskMembershipsUnique.addGroups {queue : State}
    (unique : queue.TaskMembershipsUnique) (groups : List Group)
    : (queue.addGroups groups).1.TaskMembershipsUnique := by
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
  have linkUnique (current : State) (group : Group)
      (currentUnique : current.TaskMembershipsUnique)
      : (linkStep current group).TaskMembershipsUnique := by
    unfold linkStep
    cases parent : group.parent with
    | none => simpa only [parent] using currentUnique
    | some key =>
        cases found : current.groupNode? key with
        | none => simpa only [parent, found] using currentUnique
        | some node =>
            simp only [found]
            apply currentUnique.putGroupNode
            exact currentUnique node (List.mem_of_find?_eq_some found)
  have foldUnique (more : List Group) :
      ∀ current, current.TaskMembershipsUnique
        → (more.foldl linkStep current).TaskMembershipsUnique := by
    induction more with
    | nil => intro current currentUnique; exact currentUnique
    | cons group rest ih =>
        intro current currentUnique
        exact ih (linkStep current group) (linkUnique current group currentUnique)
  have registeredUnique (more : List Group)
      : (more.foldl State.addGroup queue).TaskMembershipsUnique := by
    induction more generalizing queue with
    | nil => exact unique
    | cons group rest ih =>
        simpa only [List.foldl_cons]
          using ih (queue := queue.addGroup group) (unique.addGroup group)
  let fresh := groups.filter (fun group =>
    !queue.registeredGroups.contains group.node.key
      && (queue.groupNode? group.node.key).isNone)
  change (fresh.foldl linkStep (fresh.foldl State.addGroup queue)).TaskMembershipsUnique
  exact foldUnique fresh _ (registeredUnique fresh)

/-- Adding a task checks membership before appending it, so group lists stay unique. -/
theorem State.TaskMembershipsUnique.addTask {queue : State}
    (unique : queue.TaskMembershipsUnique) (task : Task)
    : (queue.addTask task).TaskMembershipsUnique := by
  let registered : State := { queue with tasks := queue.tasks ++ [task] }
  let step (current : State) (group : Execution.DeliveryNode) : State :=
    match current.groupNode? group.key with
    | none => current
    | some node =>
        if node.tasks.contains task.occurrence then
          current
        else
          current.putGroupNode
            { node with tasks := node.tasks ++ [task.occurrence], pending := node.pending + 1 }
  have stepUnique (current : State) (group : Execution.DeliveryNode)
      (currentUnique : current.TaskMembershipsUnique)
      : (step current group).TaskMembershipsUnique := by
    unfold step
    split
    · exact currentUnique
    · rename_i node found
      split
      · exact currentUnique
      · rename_i absent
        have priorUnique : node.tasks.Nodup :=
          currentUnique node (List.mem_of_find?_eq_some found)
        apply currentUnique.putGroupNode
        apply List.nodup_append.mpr
        refine ⟨priorUnique, by simp, ?_⟩
        intro occurrence member singleMember singleMem
        simp only [List.mem_singleton] at singleMem
        subst singleMember
        intro equal
        subst occurrence
        have reflexive : (task.occurrence == task.occurrence) = true := by
          cases task.occurrence with
          | executionGroup address =>
              change (address == address) = true
              exact BEq.rfl
          | item address index =>
              change ((address == address) && (index == index)) = true
              simp [BEq.rfl]
        exact absent ((List.contains_iff_exists_mem_beq).mpr
          ⟨task.occurrence, member, reflexive⟩)
  have foldUnique (groups : List Execution.DeliveryNode) :
      ∀ current, current.TaskMembershipsUnique
        → (groups.foldl step current).TaskMembershipsUnique := by
    induction groups with
    | nil => intro current currentUnique; exact currentUnique
    | cons group rest ih =>
        intro current currentUnique
        exact ih (step current group) (stepUnique current group currentUnique)
  let current := task.groups.foldl step registered
  have currentUnique : current.TaskMembershipsUnique :=
    foldUnique task.groups registered unique
  change (if task.groups.any (fun group => current.rootGroups.contains group.key)
      && (current.taskNode? task.occurrence).isNone then
      { current with taskNodes := current.taskNodes ++ [{ task }] }
    else current).TaskMembershipsUnique
  split <;> exact currentUnique

/-- Stream registration changes no group membership list. -/
theorem State.TaskMembershipsUnique.addStreams {queue : State}
    (unique : queue.TaskMembershipsUnique) (streams : List Stream)
    (parentTask : Option Occurrence)
    : (queue.addStreams streams parentTask).1.TaskMembershipsUnique := by
  let fresh :=
    streams.foldl
      (fun selected stream =>
        if (queue.stream? stream.node.key).isSome
            || selected.any (fun known => known.node.key == stream.node.key) then
          selected
        else
          selected ++ [stream])
      []
  let current : State := { queue with streams := queue.streams ++ fresh }
  have currentUnique : current.TaskMembershipsUnique := unique
  cases parentTask with
  | none => exact currentUnique
  | some occurrence =>
      simp only [State.addStreams]
      split <;> exact currentUnique

/-- Every freshly integrated work fragment has unique task memberships. -/
theorem State.TaskMembershipsUnique.maybeIntegrateWork {queue : State}
    (unique : queue.TaskMembershipsUnique) (work : Work)
    (parentTask : Option Occurrence := none)
    : (queue.maybeIntegrateWork work parentTask).1.TaskMembershipsUnique := by
  let withGroups := (queue.addGroups work.groups).1
  let withTasks := work.tasks.foldl State.addTask withGroups
  have taskFold (tasks : List Task) :
      ∀ current, current.TaskMembershipsUnique
        → (tasks.foldl State.addTask current).TaskMembershipsUnique := by
    induction tasks with
    | nil => intro current currentUnique; exact currentUnique
    | cons task rest ih =>
        intro current currentUnique
        exact ih (current.addTask task) (currentUnique.addTask task)
  have taskUnique : withTasks.TaskMembershipsUnique :=
    taskFold work.tasks withGroups (unique.addGroups work.groups)
  change (withTasks.addStreams work.streams parentTask).1.TaskMembershipsUnique
  exact taskUnique.addStreams work.streams parentTask

/-- Pruning removes group nodes but never adds task memberships. -/
theorem State.TaskMembershipsUnique.pruneEmptyGroups {queue : State}
    (unique : queue.TaskMembershipsUnique)
    (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.TaskMembershipsUnique := by
  have loop (fuel : Nat) (current : State)
      (remaining kept : List Execution.DeliveryNode)
      (currentUnique : current.TaskMembershipsUnique)
      : (State.pruneEmptyGroups.go fuel current remaining kept).1.TaskMembershipsUnique := by
    induction fuel generalizing current remaining kept with
    | zero => exact currentUnique
    | succ fuel ih =>
        cases remaining with
        | nil => exact currentUnique
        | cons group rest =>
            unfold State.pruneEmptyGroups.go
            split
            · exact ih _ _ _ currentUnique
            · split
              · apply ih _ _ _
                intro node member
                exact currentUnique node (List.mem_filter.mp member).1
              · exact ih _ _ _ currentUnique
  exact loop _ queue groups [] unique

/-- Starting tasks, groups, and streams leaves their group membership lists intact. -/
theorem State.TaskMembershipsUnique.startNewWork {queue : State}
    (unique : queue.TaskMembershipsUnique) (newWork : NewWork)
    : (queue.startNewWork newWork).TaskMembershipsUnique := by
  let groups := newWork.newGroups.map Execution.DeliveryNode.key
  let streams := newWork.newStreams.map Execution.DeliveryNode.key
  let current : State := { queue with rootGroups := queue.rootGroups ++ groups }
  have taskStart (state : State) (task : Occurrence)
      (currentUnique : state.TaskMembershipsUnique)
      : (state.startTask task).TaskMembershipsUnique := by
    unfold State.startTask
    split
    · exact currentUnique
    · split <;> exact currentUnique
  have taskFold (tasks : List Occurrence) :
      ∀ state, state.TaskMembershipsUnique
        → (tasks.foldl State.startTask state).TaskMembershipsUnique := by
    induction tasks with
    | nil => intro state currentUnique; exact currentUnique
    | cons task rest ih =>
        intro state currentUnique
        exact ih (state.startTask task) (taskStart state task currentUnique)
  have groupStart (state : State) (key : Nat)
      (currentUnique : state.TaskMembershipsUnique)
      : (state.startGroup key).TaskMembershipsUnique := by
    unfold State.startGroup
    split
    · exact currentUnique
    · rename_i node found
      split
      · exact currentUnique
      · exact taskFold node.tasks state currentUnique
  have groupFold (keys : Keys) :
      ∀ state, state.TaskMembershipsUnique
        → (keys.foldl State.startGroup state).TaskMembershipsUnique := by
    induction keys with
    | nil => intro state currentUnique; exact currentUnique
    | cons key rest ih =>
        intro state currentUnique
        exact ih (state.startGroup key) (groupStart state key currentUnique)
  have streamFold (keys : Keys) :
      ∀ state, state.TaskMembershipsUnique
        → (keys.foldl State.startStream state).TaskMembershipsUnique := by
    induction keys with
    | nil => intro state currentUnique; exact currentUnique
    | cons key rest ih =>
        intro state currentUnique
        apply ih (state.startStream key)
        unfold State.startStream
        split <;> exact currentUnique
  change (streams.foldl State.startStream
    (groups.foldl State.startGroup current)).TaskMembershipsUnique
  exact streamFold streams _ (groupFold groups current unique)

/-- Queue creation gives every live group a duplicate-free task membership list.
Witness: registration checks membership, while pruning and activation preserve it.
-/
theorem createWorkQueue_taskMembershipsUnique (initialWork : Work)
    : (State.initialize initialWork).TaskMembershipsUnique := by
  let integrated := (({} : State).maybeIntegrateWork initialWork).1
  let newWork := (({} : State).maybeIntegrateWork initialWork).2
  let pruned := (integrated.pruneEmptyGroups newWork.newGroups).1
  let groups := (integrated.pruneEmptyGroups newWork.newGroups).2
  let roots := { newWork with newGroups := groups }
  let started := pruned.startNewWork roots
  have emptyUnique : ({} : State).TaskMembershipsUnique := by
    intro node member
    cases member
  have integratedUnique : integrated.TaskMembershipsUnique :=
    emptyUnique.maybeIntegrateWork initialWork
  have prunedUnique : pruned.TaskMembershipsUnique :=
    integratedUnique.pruneEmptyGroups newWork.newGroups
  have startedUnique : started.TaskMembershipsUnique := prunedUnique.startNewWork roots
  change State.TaskMembershipsUnique
    { started with initialGroups := groups, initialStreams := roots.newStreams }
  exact startedUnique

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
