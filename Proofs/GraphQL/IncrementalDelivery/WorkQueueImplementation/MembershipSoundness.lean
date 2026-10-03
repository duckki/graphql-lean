import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartedTasks

/-! Soundness of task memberships in live groups. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (
  ExecutionGroupValue StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Soundness of live group task memberships
-----------------------------------------------------------------------------------------

/-- Every occurrence in a live group's task list belongs to a registered task
that actually names the group. The registry may also contain settled tasks, so
this is only the soundness direction of queue ownership.
-/
def State.GroupMembershipSound (queue : State) : Prop :=
  ∀ node ∈ queue.groupNodes,
  ∀ occurrence ∈ node.tasks,
    ∃ task ∈ queue.tasks,
      task.occurrence = occurrence
      ∧ node.group.node.ref ∈ task.groups.map Execution.DeliveryNode.ref

/-- Replacing group metadata preserves sound memberships when the replacement
is sound relative to the unchanged registered-task list.
-/
theorem State.GroupMembershipSound.putGroupNode
    {queue : State} (sound : queue.GroupMembershipSound)
    (updated : GroupNode)
    (updatedSound
      : ∀ occurrence ∈ updated.tasks,
          ∃ task ∈ queue.tasks,
            task.occurrence = occurrence
            ∧ updated.group.node.ref ∈ task.groups.map Execution.DeliveryNode.ref)
    : (queue.putGroupNode updated).GroupMembershipSound := by
  intro node member occurrence occurrenceMember
  change node ∈ queue.groupNodes.map
    (fun old => if old.group.node.ref == updated.group.node.ref then updated else old)
    at member
  obtain ⟨old, oldMember, same⟩ := List.mem_map.mp member
  split at same
  · subst node
    exact updatedSound occurrence occurrenceMember
  · subst node
    exact sound old oldMember occurrence occurrenceMember

/-- Registering an empty group cannot add an unsupported membership. -/
theorem State.GroupMembershipSound.addGroup
    {queue : State} (sound : queue.GroupMembershipSound) (group : Group)
    : (queue.addGroup group).GroupMembershipSound := by
  unfold State.addGroup
  split
  · exact sound
  · split
    · exact sound
    · intro node member occurrence occurrenceMember
      rcases List.mem_append.mp member with earlier | added
      · exact sound node earlier occurrence occurrenceMember
      · simp only [List.mem_singleton] at added
        subst node
        cases occurrenceMember

/-- Parent-link registration does not change any group's task membership. -/
theorem State.GroupMembershipSound.addGroups
    {queue : State} (sound : queue.GroupMembershipSound)
    (groups : List Group)
    : (queue.addGroups groups).1.GroupMembershipSound := by
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
  have linkSound (current : State) (group : Group)
      (currentSound : current.GroupMembershipSound)
      : (linkStep current group).GroupMembershipSound := by
    unfold linkStep
    cases parentEq : group.parent with
    | none => simpa only [parentEq] using currentSound
    | some parent =>
        cases found : current.groupNode? parent with
        | none => simpa only [parentEq, found] using currentSound
        | some node =>
            simp only [found]
            apply currentSound.putGroupNode
            exact currentSound node (List.mem_of_find?_eq_some found)
  have foldLink (more : List Group) :
      ∀ current, current.GroupMembershipSound
        → (more.foldl linkStep current).GroupMembershipSound := by
    induction more with
    | nil => intro current currentSound; exact currentSound
    | cons group rest ih =>
        intro current currentSound
        exact ih (linkStep current group) (linkSound current group currentSound)
  have registered (more : List Group) : (more.foldl State.addGroup queue).GroupMembershipSound := by
    induction more generalizing queue with
    | nil => exact sound
    | cons group rest ih =>
        simpa only [List.foldl_cons]
          using ih (queue := queue.addGroup group) (sound.addGroup group)
  let fresh := groups.filter (fun group =>
    !queue.registeredGroups.contains group.node.ref
      && (queue.groupNode? group.node.ref).isNone)
  change (fresh.foldl linkStep (fresh.foldl State.addGroup queue)).GroupMembershipSound
  exact foldLink fresh _ (registered fresh)

/-- Linking a new task to its listed groups preserves membership soundness;
each appended occurrence is witnessed by the just-registered task.
-/
theorem State.GroupMembershipSound.addTask
    {queue : State} (sound : queue.GroupMembershipSound) (task : Task)
    : (queue.addTask task).GroupMembershipSound := by
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
  have stepSound (current : State) (group : Execution.DeliveryNode)
      (groupMember : group ∈ task.groups)
      (currentSound : current.GroupMembershipSound)
      (taskMember : task ∈ current.tasks)
      : (step current group).GroupMembershipSound := by
    unfold step
    cases found : current.groupNode? group.ref with
    | none => exact currentSound
    | some node =>
        simp only
        by_cases present : node.tasks.contains task.occurrence = true
        · simp only [present, ite_true]
          exact currentSound
        · simp only [present]
          apply currentSound.putGroupNode
          intro occurrence member
          rcases List.mem_append.mp member with earlier | new
          · exact currentSound node (List.mem_of_find?_eq_some found)
              occurrence earlier
          · simp only [List.mem_singleton] at new
            subst occurrence
            refine ⟨task, taskMember, rfl, ?_⟩
            rw [State.groupNode?_ref found]
            exact List.mem_map.mpr ⟨group, groupMember, rfl⟩
  have foldSound (groups : List Execution.DeliveryNode)
      (subset : ∀ group ∈ groups, group ∈ task.groups) :
      ∀ current, current.GroupMembershipSound → task ∈ current.tasks
        → (groups.foldl step current).GroupMembershipSound
          ∧ task ∈ (groups.foldl step current).tasks := by
    induction groups with
    | nil =>
        intro current currentSound taskMember
        exact ⟨currentSound, taskMember⟩
    | cons group rest ih =>
        intro current currentSound taskMember
        have headMember : group ∈ task.groups := subset group (by simp)
        have tailSubset : ∀ candidate ∈ rest, candidate ∈ task.groups := by
          intro candidate member
          exact subset candidate (by simp [member])
        have nextSound := stepSound current group headMember currentSound taskMember
        have nextMember : task ∈ (step current group).tasks := by
          unfold step
          split
          · exact taskMember
          · split <;> exact taskMember
        exact ih tailSubset (step current group) nextSound nextMember
  have registeredSound : registered.GroupMembershipSound := by
    intro node member occurrence occurrenceMember
    obtain ⟨known, knownMember, occurrenceEq, ownerMember⟩ :=
      sound node member occurrence occurrenceMember
    exact ⟨known, List.mem_append.mpr (Or.inl knownMember),
      occurrenceEq, ownerMember⟩
  have taskMember : task ∈ registered.tasks := by simp [registered]
  let current := task.groups.foldl step registered
  have currentSound : current.GroupMembershipSound :=
    (foldSound task.groups (fun _ member => member)
      registered registeredSound taskMember).1
  change (if task.groups.any (fun group => current.rootGroups.contains group.ref)
      && (current.taskNode? task.occurrence).isNone then
      { current with taskNodes := current.taskNodes ++ [{ task }] }
    else current).GroupMembershipSound
  split <;> exact currentSound

/-- Stream registration changes neither group memberships nor task definitions. -/
theorem State.GroupMembershipSound.addStreams
    {queue : State} (sound : queue.GroupMembershipSound)
    (streams : List Stream) (parentTask : Option Occurrence)
    : (queue.addStreams streams parentTask).1.GroupMembershipSound := by
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
  have currentSound : current.GroupMembershipSound := sound
  cases parentTask with
  | none => exact currentSound
  | some occurrence =>
      simp only [State.addStreams]
      split <;> exact currentSound

/-- Integration cannot create an unsupported group membership: it registers
groups first and appends every new task before linking it to those groups.
-/
theorem State.GroupMembershipSound.maybeIntegrateWork
    {queue : State} (sound : queue.GroupMembershipSound)
    (newWork : Work) (parentTask : Option Occurrence := none)
    : (queue.maybeIntegrateWork newWork parentTask).1.GroupMembershipSound := by
  let withGroups := (queue.addGroups newWork.groups).1
  let withTasks := newWork.tasks.foldl State.addTask withGroups
  have taskFold (tasks : List Task) :
      ∀ current, current.GroupMembershipSound
        → (tasks.foldl State.addTask current).GroupMembershipSound := by
    induction tasks with
    | nil => intro current currentSound; exact currentSound
    | cons task rest ih =>
        intro current currentSound
        exact ih (current.addTask task) (currentSound.addTask task)
  have withTasksSound : withTasks.GroupMembershipSound :=
    taskFold newWork.tasks withGroups (sound.addGroups newWork.groups)
  change (withTasks.addStreams newWork.streams parentTask).1.GroupMembershipSound
  exact withTasksSound.addStreams newWork.streams parentTask

/-- Pruning drops group shells but does not change surviving task lists. -/
theorem State.GroupMembershipSound.pruneEmptyGroups
    {queue : State} (sound : queue.GroupMembershipSound)
    (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.GroupMembershipSound := by
  have loop (fuel : Nat) (current : State)
      (remaining kept : List Execution.DeliveryNode)
      (currentSound : current.GroupMembershipSound)
      : (State.pruneEmptyGroups.go fuel current remaining kept).1.GroupMembershipSound := by
    induction fuel generalizing current remaining kept with
    | zero => exact currentSound
    | succ fuel ih =>
        cases remaining with
        | nil => exact currentSound
        | cons group rest =>
            unfold State.pruneEmptyGroups.go
            split
            · exact ih _ _ _ currentSound
            · split
              · apply ih
                intro node member occurrence occurrenceMember
                exact currentSound node (List.mem_filter.mp member).1
                  occurrence occurrenceMember
              · exact ih _ _ _ currentSound
  exact loop _ queue groups [] sound

/-- Starting tasks and streams affects active nodes, not the group task lists. -/
theorem State.GroupMembershipSound.startTask
    {queue : State} (sound : queue.GroupMembershipSound)
    (occurrence : Occurrence)
    : (queue.startTask occurrence).GroupMembershipSound := by
  unfold State.startTask
  split
  · exact sound
  · split <;> exact sound

theorem State.GroupMembershipSound.startGroup
    {queue : State} (sound : queue.GroupMembershipSound) (ref : NodeRef)
    : (queue.startGroup ref).GroupMembershipSound := by
  unfold State.startGroup
  split
  · exact sound
  · rename_i node found
    have foldStart (tasks : List Occurrence) :
        ∀ current, current.GroupMembershipSound
          → (tasks.foldl State.startTask current).GroupMembershipSound := by
      induction tasks with
      | nil => intro current currentSound; exact currentSound
      | cons task rest ih =>
          intro current currentSound
          exact ih (current.startTask task) (currentSound.startTask task)
    split
    · exact sound
    · exact foldStart node.tasks queue sound

theorem State.GroupMembershipSound.startStream
    {queue : State} (sound : queue.GroupMembershipSound) (ref : NodeRef)
    : (queue.startStream ref).GroupMembershipSound := by
  unfold State.startStream
  split <;> exact sound

theorem State.GroupMembershipSound.startNewWork
    {queue : State} (sound : queue.GroupMembershipSound)
    (newWork : NewWork)
    : (queue.startNewWork newWork).GroupMembershipSound := by
  let groups := newWork.newGroups.map Execution.DeliveryNode.ref
  let streams := newWork.newStreams.map Execution.DeliveryNode.ref
  let current : State := { queue with rootGroups := queue.rootGroups ++ groups }
  have currentSound : current.GroupMembershipSound := sound
  have groupFold (refs : NodeRefs) :
      ∀ state, state.GroupMembershipSound
        → (refs.foldl State.startGroup state).GroupMembershipSound := by
    induction refs with
    | nil => intro state stateSound; exact stateSound
    | cons ref rest ih =>
        intro state stateSound
        exact ih (state.startGroup ref) (stateSound.startGroup ref)
  have streamFold (refs : NodeRefs) :
      ∀ state, state.GroupMembershipSound
        → (refs.foldl State.startStream state).GroupMembershipSound := by
    induction refs with
    | nil => intro state stateSound; exact stateSound
    | cons ref rest ih =>
        intro state stateSound
        exact ih (state.startStream ref) (stateSound.startStream ref)
  change (streams.foldl State.startStream
    (groups.foldl State.startGroup current)).GroupMembershipSound
  exact streamFold streams _ (groupFold groups current currentSound)

/-- Initial queue creation records only sound group/task links. -/
theorem createWorkQueue_groupMembershipSound (initialWork : Work)
    : (State.initialize initialWork).GroupMembershipSound := by
  let integrated := (({} : State).maybeIntegrateWork initialWork).1
  let newWork := (({} : State).maybeIntegrateWork initialWork).2
  let pruned := (integrated.pruneEmptyGroups newWork.newGroups).1
  let groups := (integrated.pruneEmptyGroups newWork.newGroups).2
  let roots := { newWork with newGroups := groups }
  let started := pruned.startNewWork roots
  have emptySound : ({} : State).GroupMembershipSound := by
    intro node member occurrence occurrenceMember
    cases member
  have integratedSound : integrated.GroupMembershipSound :=
    emptySound.maybeIntegrateWork initialWork
  have prunedSound : pruned.GroupMembershipSound :=
    integratedSound.pruneEmptyGroups newWork.newGroups
  have startedSound : started.GroupMembershipSound :=
    prunedSound.startNewWork roots
  change State.GroupMembershipSound
    { started with initialGroups := groups, initialStreams := roots.newStreams }
  exact startedSound

/-- Removing a settled task only filters group membership lists. -/
theorem State.GroupMembershipSound.removeTask
    {queue : State} (sound : queue.GroupMembershipSound)
    (occurrence : Occurrence)
    : (queue.removeTask occurrence).GroupMembershipSound := by
  intro node member taskOccurrence taskMember
  change node ∈ queue.groupNodes.map
    (fun old => { old with tasks := old.tasks.filter (· != occurrence) }) at member
  obtain ⟨old, oldMember, same⟩ := List.mem_map.mp member
  subst node
  exact sound old oldMember taskOccurrence (List.mem_filter.mp taskMember).1

/-- Removing a failed group retains a subset of previously sound group nodes. -/
theorem State.GroupMembershipSound.removeGroup
    {queue : State} (sound : queue.GroupMembershipSound) (ref : NodeRef)
    : (queue.removeGroup ref).GroupMembershipSound := by
  intro node member taskOccurrence taskMember
  exact sound node (List.mem_filter.mp member).1 taskOccurrence taskMember

/-- Group flushes remove task memberships and empty group shells; both
operations preserve soundness of every surviving membership.
-/
theorem State.GroupMembershipSound.finishGroupSuccess
    {queue : State} (sound : queue.GroupMembershipSound) (group : GroupNode)
    : (queue.finishGroupSuccess group).1.GroupMembershipSound := by
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
  have stepSound (acc : State × List ExecutionGroupValue × NodeRefs)
      (occurrence : Occurrence) (currentSound : acc.1.GroupMembershipSound)
      : (step acc occurrence).1.GroupMembershipSound := by
    obtain ⟨current, values, streams⟩ := acc
    dsimp only [step]
    split
    · exact currentSound
    · exact currentSound.removeTask occurrence
  have foldSound (tasks : List Occurrence) :
      ∀ acc : State × List ExecutionGroupValue × NodeRefs,
        acc.1.GroupMembershipSound
          → (tasks.foldl step acc).1.GroupMembershipSound := by
    induction tasks with
    | nil => intro acc currentSound; exact currentSound
    | cons occurrence rest ih =>
        intro acc currentSound
        exact ih (step acc occurrence) (stepSound acc occurrence currentSound)
  let flushed := (group.tasks.foldl step (queue, [], [])).1
  have flushedSound : flushed.GroupMembershipSound :=
    foldSound group.tasks (queue, [], []) sound
  let current : State :=
    { flushed with
        groupNodes := flushed.groupNodes.filter
          (fun node => node.group.node.ref != group.group.node.ref)
        rootGroups := flushed.rootGroups.filter (· != group.group.node.ref) }
  have currentSound : current.GroupMembershipSound := by
    intro node member taskOccurrence taskMember
    exact flushedSound node (List.mem_filter.mp member).1
      taskOccurrence taskMember
  let children := group.childGroups.filterMap
    (fun ref => (current.groupNode? ref).map (fun node => node.group.node))
  change (current.pruneEmptyGroups children).1.GroupMembershipSound
  exact currentSound.pruneEmptyGroups children

theorem State.GroupMembershipSound.finishGroupFailure
    {queue : State} (sound : queue.GroupMembershipSound)
    (group : GroupNode) (errors : Nat)
    : (queue.finishGroupFailure group errors).1.GroupMembershipSound :=
  sound.removeGroup group.group.node.ref

/-- Draining ready roots preserves sound task memberships.
Witness: closure removes memberships, while activation introduces no new ones.
-/
theorem State.GroupMembershipSound.drainReadyGroups
    {queue : State} (sound : queue.GroupMembershipSound)
    : queue.drainReadyGroups.1.GroupMembershipSound := by
  apply State.drainReadyGroups_preserves State.GroupMembershipSound (valid := sound)
  · intro current node currentSound _ _ _ _
    exact (currentSound.finishGroupSuccess node).startNewWork _
  · intro current node errors currentSound _ _ _
    exact currentSound.finishGroupFailure node errors

/-- Successful settlement only changes pending counters before flushing
completed groups; newly integrated child memberships are sound by registration.
-/
theorem State.GroupMembershipSound.taskSuccess
    {queue : State} (sound : queue.GroupMembershipSound)
    (occurrence : Occurrence) (result : TaskResult)
    : (queue.taskSuccess occurrence result).1.GroupMembershipSound := by
  let settleStep (current : State) (group : Execution.DeliveryNode) : State :=
    match current.groupNode? group.ref with
    | none => current
    | some node => current.putGroupNode { node with pending := node.pending - 1 }
  have settleSound (current : State) (group : Execution.DeliveryNode)
      (currentSound : current.GroupMembershipSound)
      : (settleStep current group).GroupMembershipSound := by
    unfold settleStep
    split
    · exact currentSound
    · rename_i node found
      apply currentSound.putGroupNode
      exact currentSound node (List.mem_of_find?_eq_some found)
  let releaseStep (acc : State × List WorkQueueEvent × NewWork)
      (group : Execution.DeliveryNode) : State × List WorkQueueEvent × NewWork :=
    let (current, events, released) := acc
    match current.groupNode? group.ref with
    | none => (current, events, released)
    | some node =>
        let node := { node with pending := node.pending - 1 }
        let current := current.putGroupNode node
        if current.rootGroups.contains group.ref && node.pending == 0
            && node.failure.isNone then
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
          (current, events, released)
  have releaseSound (acc : State × List WorkQueueEvent × NewWork)
      (group : Execution.DeliveryNode) (currentSound : acc.1.GroupMembershipSound)
      : (releaseStep acc group).1.GroupMembershipSound := by
    obtain ⟨current, events, released⟩ := acc
    dsimp only [releaseStep]
    split
    · exact currentSound
    · rename_i node found
      have decremented : (current.putGroupNode
          { node with pending := node.pending - 1 }).GroupMembershipSound := by
        simpa only [settleStep, found] using settleSound current group currentSound
      split
      · exact decremented.finishGroupSuccess _
      · exact decremented
  have releaseFold (groups : List Execution.DeliveryNode) :
      ∀ acc : State × List WorkQueueEvent × NewWork,
        acc.1.GroupMembershipSound
          → (groups.foldl releaseStep acc).1.GroupMembershipSound := by
    induction groups with
    | nil => intro acc currentSound; exact currentSound
    | cons group rest ih =>
        intro acc currentSound
        exact ih (releaseStep acc group) (releaseSound acc group currentSound)
  unfold State.taskSuccess
  split
  · exact sound
  · rename_i taskNode found
    split <;> try exact sound.removeTask occurrence
    let withValue := queue.putTaskNode { taskNode with value := some result.value }
    have withValueSound : withValue.GroupMembershipSound := sound
    let integrated := (withValue.maybeIntegrateWork result.work (some occurrence)).1
    have integratedSound : integrated.GroupMembershipSound :=
      withValueSound.maybeIntegrateWork result.work (some occurrence)
    let finished := taskNode.task.groups.foldl releaseStep (integrated, [], {})
    have finishedSound : finished.1.GroupMembershipSound :=
      releaseFold taskNode.task.groups (integrated, [], {}) integratedSound
    change (finished.1.startNewWork finished.2.2).drainReadyGroups.1.GroupMembershipSound
    exact (finishedSound.startNewWork finished.2.2).drainReadyGroups

/-- Task failure filters memberships and closes active owners; retained latent
owners keep only sound memberships. Witness: the actual retained-failure fold.
-/
theorem State.GroupMembershipSound.taskFailure
    {queue : State} (sound : queue.GroupMembershipSound)
    (occurrence : Occurrence) (errors : Nat)
    : (queue.taskFailure occurrence errors).1.GroupMembershipSound := by
  let step (acc : State × List WorkQueueEvent)
      (group : Execution.DeliveryNode) : State × List WorkQueueEvent :=
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
  have stepSound (acc : State × List WorkQueueEvent)
      (group : Execution.DeliveryNode)
      (currentSound : acc.1.GroupMembershipSound)
      : (step acc group).1.GroupMembershipSound := by
    obtain ⟨current, events⟩ := acc
    change (match current.groupNode? group.ref with
      | none => (current, events)
      | some node =>
          if current.rootGroups.contains group.ref then
            let (next, failure) := current.finishGroupFailure node errors
            (next, events ++ [failure])
          else
            (current.putGroupNode
              { node with
                  pending := node.pending - 1
                  failure := some (node.failure.getD 0 + errors) }, events)).1.GroupMembershipSound
    cases found : current.groupNode? group.ref with
    | none => exact currentSound
    | some node =>
        by_cases started : current.rootGroups.contains group.ref = true
        · simp only [started, ite_true]
          exact currentSound.finishGroupFailure node errors
        · simp only [started]
          apply currentSound.putGroupNode
          exact currentSound node (List.mem_of_find?_eq_some found)
  have foldSound (groups : List Execution.DeliveryNode) :
      ∀ acc : State × List WorkQueueEvent,
        acc.1.GroupMembershipSound
          → (groups.foldl step acc).1.GroupMembershipSound := by
    induction groups with
    | nil => intro acc currentSound; exact currentSound
    | cons group rest ih =>
        intro acc currentSound
        exact ih (step acc group) (stepSound acc group currentSound)
  unfold State.taskFailure
  split
  · exact sound
  · rename_i taskNode found
    split <;> try exact sound.removeTask occurrence
    let current := queue.removeTask occurrence
    have currentSound : current.GroupMembershipSound := sound.removeTask occurrence
    change (taskNode.task.groups.foldl step (current, [])).1.GroupMembershipSound
    exact foldSound taskNode.task.groups (current, []) currentSound

/-- Stream items register their child work before publishing values, so any
new group task memberships have registered task witnesses.
-/
theorem State.GroupMembershipSound.streamItems
    {queue : State} (sound : queue.GroupMembershipSound)
    (stream : Execution.DeliveryNode) (items : List StreamItem)
    : (queue.streamItems stream items).1.GroupMembershipSound := by
  let step (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue)
      (item : StreamItem) :=
    let (current, groups, streams, values) := acc
    let (integrated, newWork) := current.maybeIntegrateWork item.work
    let (pruned, nonempty) := integrated.pruneEmptyGroups newWork.newGroups
    (
      pruned.startNewWork { newWork with newGroups := nonempty },
      groups ++ nonempty,
      streams ++ newWork.newStreams,
      values ++ [item.value]
    )
  have stepSound (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue)
      (item : StreamItem) (currentSound : acc.1.GroupMembershipSound)
      : (step acc item).1.GroupMembershipSound := by
    obtain ⟨current, groups, streams, values⟩ := acc
    let integrated := current.maybeIntegrateWork item.work
    have integratedSound : integrated.1.GroupMembershipSound :=
      currentSound.maybeIntegrateWork item.work
    let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
    have prunedSound : pruned.1.GroupMembershipSound :=
      integratedSound.pruneEmptyGroups integrated.2.newGroups
    exact prunedSound.startNewWork { integrated.2 with newGroups := pruned.2 }
  have foldSound (more : List StreamItem) :
      ∀ acc : State × List Execution.DeliveryNode
        × List Execution.DeliveryNode × List StreamItemValue,
        acc.1.GroupMembershipSound
          → (more.foldl step acc).1.GroupMembershipSound := by
    induction more with
    | nil => intro acc currentSound; exact currentSound
    | cons item rest ih =>
        intro acc currentSound
        exact ih (step acc item) (stepSound acc item currentSound)
  dsimp only [State.streamItems]
  split
  · exact sound
  · exact (foldSound items (queue, [], [], []) sound).drainReadyGroups

theorem State.GroupMembershipSound.streamSuccess
    {queue : State} (sound : queue.GroupMembershipSound)
    (stream : Execution.DeliveryNode)
    : (queue.streamSuccess stream).1.GroupMembershipSound := by
  unfold State.streamSuccess
  split <;> exact sound

theorem State.GroupMembershipSound.streamFailure
    {queue : State} (sound : queue.GroupMembershipSound)
    (stream : Execution.DeliveryNode) (errors : Nat)
    : (queue.streamFailure stream errors).1.GroupMembershipSound := by
  unfold State.streamFailure
  split <;> exact sound

/-- Membership soundness is preserved by each executable graph-event handler. -/
theorem State.GroupMembershipSound.handleGraphEvent
    {queue : State} (sound : queue.GroupMembershipSound)
    (event : GraphEvent)
    : (queue.handleGraphEvent event).1.GroupMembershipSound := by
  cases event with
  | taskSuccess occurrence result => exact sound.taskSuccess occurrence result
  | taskFailure occurrence errors => exact sound.taskFailure occurrence errors
  | streamItems stream items => exact sound.streamItems stream items
  | streamSuccess stream => exact sound.streamSuccess stream
  | streamFailure stream errors => exact sound.streamFailure stream errors

theorem State.GroupMembershipSound.handleGraphEvents
    {queue : State} (sound : queue.GroupMembershipSound)
    (batch : List GraphEvent)
    : (queue.handleGraphEvents batch).1.GroupMembershipSound := by
  let step (acc : State × List WorkQueueEvent) (event : GraphEvent) :=
    let (current, outputs) := acc
    let (next, produced) := current.handleGraphEvent event
    (next, outputs ++ produced)
  have foldSound (events : List GraphEvent) :
      ∀ acc : State × List WorkQueueEvent,
        acc.1.GroupMembershipSound
          → (events.foldl step acc).1.GroupMembershipSound := by
    induction events with
    | nil => intro acc currentSound; exact currentSound
    | cons event rest ih =>
        intro acc currentSound
        obtain ⟨current, outputs⟩ := acc
        have nextSound : (step (current, outputs) event).1.GroupMembershipSound :=
          currentSound.handleGraphEvent event
        exact ih (step (current, outputs) event) nextSound
  unfold State.handleGraphEvents
  split
  · exact sound
  · let folded := batch.foldl step (queue, [])
    have foldedSound : folded.1.GroupMembershipSound :=
      foldSound batch (queue, []) sound
    cases folded with
    | mk current outputs =>
        dsimp only at foldedSound ⊢
        split <;> exact foldedSound

/-- All finite queue replays retain sound group memberships, even if the host
inputs are not themselves admitted by the spec-facing event-source contract.
-/
private theorem State.runNormalized_groupMembershipSound
    {queue : State} (sound : queue.GroupMembershipSound)
    (batches : List (List GraphEvent))
    : (queue.runNormalized batches).1.GroupMembershipSound := by
  have stepSound (acc : NormalizedAcc) (batch : List GraphEvent)
      (currentSound : acc.1.GroupMembershipSound)
      : (normalizedStep acc batch).1.GroupMembershipSound := by
    obtain ⟨current, publisher, outputs⟩ := acc
    unfold normalizedStep
    cases outcome : current.handleGraphEvents batch with
    | mk next raw =>
        have nextSound : next.GroupMembershipSound := by
          have handled := currentSound.handleGraphEvents batch
          rw [outcome] at handled
          exact handled
        dsimp only
        simp only [outcome]
        split <;> exact nextSound
  have foldSound (more : List (List GraphEvent)) :
      ∀ acc : NormalizedAcc, acc.1.GroupMembershipSound
        → (more.foldl normalizedStep acc).1.GroupMembershipSound := by
    induction more with
    | nil => intro acc currentSound; exact currentSound
    | cons batch rest ih =>
        intro acc currentSound
        exact ih (normalizedStep acc batch) (stepSound acc batch currentSound)
  let publisher : IncrementalPublisher :=
    { active := queue.initialGroups ++ queue.initialStreams }
  change (batches.foldl normalizedStep
    (queue, publisher, [])).1.GroupMembershipSound
  exact foldSound batches (queue, publisher, []) sound

/-- Soundness of each live group membership holds after every finite replay
from the reference queue's initial state.
-/
private theorem createWorkQueue_runNormalized_groupMembershipSound
    (work : Work) (batches : List (List GraphEvent))
    : ((State.initialize work).runNormalized batches).1.GroupMembershipSound :=
  State.runNormalized_groupMembershipSound
    (createWorkQueue_groupMembershipSound work) batches

/-- If a live group lists a started task, its ref is among that task's
contributors. Exact spec Work lookup equates the registered witness with the
started node even if the registry contains multiple copies of an occurrence.
-/
theorem State.GroupMembershipSound.startedOwner
    {queue : State} {work : Execution.Work}
    (sound : queue.GroupMembershipSound)
    (registered : queue.StartedTasksRegistered)
    (matching : queue.RegisteredTasksMatch work)
    {taskNode : TaskNode} (taskMember : taskNode ∈ queue.taskNodes)
    {groupNode : GroupNode} (groupMember : groupNode ∈ queue.groupNodes)
    (listed : taskNode.task.occurrence ∈ groupNode.tasks)
    : groupNode.group.node.ref ∈ taskNode.task.groups.map Execution.DeliveryNode.ref := by
  obtain ⟨witness, witnessMember, sameOccurrence, ownerMember⟩ :=
    sound groupNode groupMember taskNode.task.occurrence listed
  have witnessExact := (matching witness witnessMember).2
  have nodeExact := (matching taskNode.task
    (registered taskNode taskMember)).2
  rw [sameOccurrence] at witnessExact
  have sameGroups : witness.groups = taskNode.task.groups :=
    Option.some.inj (witnessExact.symm.trans nodeExact)
  simpa only [sameGroups] using ownerMember

/-- Every admitted generated-work replay satisfies the sound half of live
task ownership: group membership never names a noncontributing owner.
-/
private theorem createWorkQueue_runNormalized_startedOwnerSound
    {work : Execution.Work} {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten)
    {taskNode : TaskNode}
    (taskMember
      : taskNode
        ∈ ((State.initialize (Work.fromExecution work)).runNormalized
            batches).1.taskNodes)
    {groupNode : GroupNode}
    (groupMember
      : groupNode
        ∈ ((State.initialize (Work.fromExecution work)).runNormalized
            batches).1.groupNodes)
    (listed : taskNode.task.occurrence ∈ groupNode.tasks)
    : groupNode.group.node.ref ∈ taskNode.task.groups.map Execution.DeliveryNode.ref := by
  let queue := State.initialize (Work.fromExecution work)
  let current := (queue.runNormalized batches).1
  have sound : current.GroupMembershipSound :=
    createWorkQueue_runNormalized_groupMembershipSound (Work.fromExecution work) batches
  have registered : current.StartedTasksRegistered :=
    State.runNormalized_startedTasksRegistered
      (createWorkQueue_startedTasksRegistered (Work.fromExecution work)) batches
  have matching : current.RegisteredTasksMatch work :=
    createWorkQueue_runNormalized_registeredTasksMatch valid
  exact sound.startedOwner registered matching taskMember groupMember listed

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
