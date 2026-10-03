import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.HealthyRegistration

/-! Healthy task links and contributor presence after success. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Replacing a started task's mutable value or child-stream slots leaves its
task descriptor and all healthy links unchanged. -/
theorem State.HealthyTaskLinks.putTaskNodeSameTask
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (links : queue.HealthyTaskLinks work settled failed)
    (source : TaskNode) (sourceMember : source ∈ queue.taskNodes)
    (updated : TaskNode) (sameTask : updated.task = source.task)
    : (queue.putTaskNode updated).HealthyTaskLinks work settled failed := by
  intro taskNode member fresh groupNode groupMember healthy contributor
  change taskNode ∈ queue.taskNodes.map
    (fun old => if old.task.occurrence == updated.task.occurrence then
      updated else old) at member
  obtain ⟨old, oldMember, same⟩ := List.mem_map.mp member
  split at same
  · subst taskNode
    rw [sameTask] at fresh contributor ⊢
    exact links source sourceMember fresh groupNode groupMember healthy contributor
  · subst taskNode
    exact links old oldMember fresh groupNode groupMember healthy contributor

/-- Updating a group's pending count preserves healthy task links when its ref
and membership list remain unchanged. -/
theorem State.HealthyTaskLinks.putGroupNodeSameTasks
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (unique : queue.GroupRefsUnique)
    (links : queue.HealthyTaskLinks work settled failed)
    (node : GroupNode) (member : node ∈ queue.groupNodes)
    (updated : GroupNode)
    (sameRef : updated.group.node.ref = node.group.node.ref)
    (sameTasks : updated.tasks = node.tasks)
    : (queue.putGroupNode updated).HealthyTaskLinks work settled failed := by
  apply State.HealthyTaskLinks.ofFilteredLinks
  intro taskNode taskMember fresh
  have prior := (links.toTaskLinkedOn taskMember fresh).putGroupNodeSameTasks
    unique node member updated sameRef sameTasks
  exact prior

/-- Settling a task changes group pending counts but not its healthy links. -/
theorem State.HealthyTaskLinks.settleTaskGroups
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (unique : queue.GroupRefsUnique)
    (links : queue.HealthyTaskLinks work settled failed)
    (groups : List Execution.DeliveryNode)
    : (groups.foldl
        (fun current group =>
          match current.groupNode? group.ref with
          | none => current
          | some node => current.putGroupNode { node with pending := node.pending - 1 })
        queue).HealthyTaskLinks
        work settled failed := by
  let step (current : State) (group : Execution.DeliveryNode) : State :=
    match current.groupNode? group.ref with
    | none => current
    | some node => current.putGroupNode { node with pending := node.pending - 1 }
  have stepFacts (current : State) (group : Execution.DeliveryNode)
      (currentUnique : current.GroupRefsUnique)
      (currentLinks : current.HealthyTaskLinks work settled failed)
      : (step current group).GroupRefsUnique
        ∧ (step current group).HealthyTaskLinks work settled failed := by
    unfold step
    split
    · exact ⟨currentUnique, currentLinks⟩
    · rename_i node found
      have member := List.mem_of_find?_eq_some found
      exact ⟨currentUnique.putGroupNode _,
        currentLinks.putGroupNodeSameTasks currentUnique node member
          { node with pending := node.pending - 1 } rfl rfl⟩
  have foldFacts (more : List Execution.DeliveryNode) :
      ∀ current, current.GroupRefsUnique
        → current.HealthyTaskLinks work settled failed
        → (more.foldl step current).HealthyTaskLinks work settled failed := by
    induction more with
    | nil => intro current _ currentLinks; exact currentLinks
    | cons group rest ih =>
        intro current currentUnique currentLinks
        obtain ⟨nextUnique, nextLinks⟩ :=
          stepFacts current group currentUnique currentLinks
        exact ih (step current group) nextUnique nextLinks
  exact foldFacts groups queue unique links

/-- Integrating streams changes no group memberships; it may only extend a
started producer task's child-stream list. -/
theorem State.HealthyTaskLinks.addStreams
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (links : queue.HealthyTaskLinks work settled failed)
    (streams : List Stream) (parentTask : Option Occurrence)
    : (queue.addStreams streams parentTask).1.HealthyTaskLinks work settled failed := by
  let fresh :=
    streams.foldl
      (fun selected stream =>
        if (queue.stream? stream.node.ref).isSome
            || selected.any (fun known => known.node.ref == stream.node.ref) then
          selected
        else selected ++ [stream])
      []
  let current : State := { queue with streams := queue.streams ++ fresh }
  have currentLinks : current.HealthyTaskLinks work settled failed := links
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

/-- Child Work integration preserves healthy links provided each new group
relevant to an older fresh started task was already registered. -/
theorem State.HealthyTaskLinks.maybeIntegrateWork
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (unique : queue.GroupRefsUnique)
    (links : queue.HealthyTaskLinks work settled failed)
    (newWork : Work) (parentTask : Option Occurrence)
    (relevantExisting
      : ∀ taskNode ∈ queue.taskNodes,
          taskNode.task.occurrence ∉ settled
          → ∀ group ∈ newWork.groups,
              group.node.ref ∈ taskNode.task.groups.map Execution.DeliveryNode.ref
              → ¬GroupInvalidated work failed group.node.ref
              → ∃ node ∈ queue.groupNodes, node.group.node.ref = group.node.ref)
    : (queue.maybeIntegrateWork newWork parentTask).1.HealthyTaskLinks
        work settled failed := by
  let withGroups := (queue.addGroups newWork.groups).1
  let withTasks := newWork.tasks.foldl State.addTask withGroups
  have groupLinks : withGroups.HealthyTaskLinks work settled failed :=
    links.addGroups unique newWork.groups relevantExisting
  have groupUnique : withGroups.GroupRefsUnique :=
    unique.addGroups newWork.groups
  have taskFold (more : List Task) :
      ∀ current, current.GroupRefsUnique
        → current.HealthyTaskLinks work settled failed
        → (more.foldl State.addTask current).HealthyTaskLinks
            work settled failed := by
    induction more with
    | nil => intro current _ currentLinks; exact currentLinks
    | cons task rest ih =>
        intro current currentUnique currentLinks
        exact ih (current.addTask task) (currentUnique.addTask task)
          (currentLinks.addTask currentUnique task)
  have taskLinks : withTasks.HealthyTaskLinks work settled failed :=
    taskFold newWork.tasks withGroups groupUnique groupLinks
  change (withTasks.addStreams newWork.streams parentTask).1.HealthyTaskLinks
    work settled failed
  exact taskLinks.addStreams newWork.streams parentTask

/-- Newly requested fresh tasks must already have their healthy contributor
memberships before the queue starts them. This is a proof-side release condition. -/
private def State.HealthyReleaseTaskLinks (queue : State) (work : Execution.Work)
    (settled failed : List Occurrence) (newWork : NewWork)
    : Prop :=
  ∀ task ∈ queue.tasks,
    task.occurrence ∉ settled
    → task.occurrence ∈ queue.releaseRequests newWork
    → ∀ node ∈ queue.groupNodes,
        ¬GroupInvalidated work failed node.group.node.ref
        → node.group.node.ref ∈ task.groups.map Execution.DeliveryNode.ref
        → task.occurrence ∈ node.tasks

/-- Registered-task accounting directly supplies the healthy links needed
when latent groups start their tasks. -/
private theorem State.HealthyRegisteredTaskAccounting.releaseTaskLinks
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (accounted : queue.HealthyRegisteredTaskAccounting work settled failed)
    (unique : queue.GroupRefsUnique)
    (newWork : NewWork)
    : queue.HealthyReleaseTaskLinks work settled failed newWork := by
  intro task taskMember fresh _ node nodeMember healthy contributor
  obtain ⟨owner, ownerMember, same, linked⟩ :=
    accounted task taskMember fresh node.group.node.ref contributor healthy
  have equal : owner = node :=
    unique.sameNode ownerMember nodeMember same
  exact equal ▸ linked

/-- Registered-task accounting also supplies the corresponding live-node
condition at a release boundary. -/
private theorem State.HealthyRegisteredTaskAccounting.releaseGroupsPresent
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (accounted : queue.HealthyRegisteredTaskAccounting work settled failed)
    (newWork : NewWork)
    : ∀ task ∈ queue.tasks,
        task.occurrence ∈ queue.releaseRequests newWork
        → task.occurrence ∉ settled
        → ∀ ref ∈ task.groups.map Execution.DeliveryNode.ref,
            ¬GroupInvalidated work failed ref
            → ∃ node ∈ queue.groupNodes, node.group.node.ref = ref := by
  intro task taskMember _ fresh ref contributor healthy
  obtain ⟨node, nodeMember, same, _⟩ :=
    accounted task taskMember fresh ref contributor healthy
  exact ⟨node, nodeMember, same⟩

/-- Root activation leaves old healthy links intact; the release condition
supplies links for the newly started task nodes. -/
theorem State.HealthyTaskLinks.startNewWork
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (registered : queue.StartedTasksRegistered)
    (links : queue.HealthyTaskLinks work settled failed)
    (newWork : NewWork)
    (ready : queue.HealthyReleaseTaskLinks work settled failed newWork)
    : (queue.startNewWork newWork).HealthyTaskLinks work settled failed := by
  let final := queue.startNewWork newWork
  obtain ⟨sameGroups, sameTasks, _⟩ := queue.startNewWork_groupCore newWork
  have finalRegistered : final.StartedTasksRegistered :=
    registered.startNewWork newWork
  intro taskNode taskMember fresh groupNode groupMember healthy contributor
  have taskDef : taskNode.task ∈ queue.tasks := by
    rw [← sameTasks]
    exact finalRegistered taskNode taskMember
  have oldGroup : groupNode ∈ queue.groupNodes := by
    rw [← sameGroups]
    exact groupMember
  rcases queue.startNewWork_oldOrRequested newWork taskMember with old | requested
  · exact links taskNode old fresh groupNode oldGroup healthy contributor
  · exact ready taskNode.task taskDef fresh requested groupNode oldGroup
      healthy contributor

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
