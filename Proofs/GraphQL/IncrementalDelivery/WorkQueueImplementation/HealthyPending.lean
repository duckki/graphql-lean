import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ActiveLinks
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupInvalidation

/-! Pending counts for healthy groups and root-health preservation. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (ExecutionGroupValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Pending counts of active groups
-----------------------------------------------------------------------------------------

/-- Pending-count equations restricted to active roots. This proof-side projection
does not itself exclude transient failed roots during recursive release.
-/
def State.ActivePendingTracks (queue : State) (settled : List Occurrence) : Prop :=
  ∀ node ∈ queue.groupNodes,
    node.group.node.ref ∈ queue.rootGroups → node.PendingTracks settled

/-- Pending-count equations restricted to groups not invalidated by observed task failures.
With a success-only settlement list, retained failed groups must be excluded because
their failure settlements also decrement counters. -/
def State.HealthyPendingTracks (queue : State) (work : Execution.Work)
    (settled failed : List Occurrence)
    : Prop :=
  ∀ node ∈ queue.groupNodes,
    ¬GroupInvalidated work failed node.group.node.ref → node.PendingTracks settled

/-- Healthy counters may temporarily overcount by unprocessed contributor decrements.
This proof-only bound is sufficient to protect unsettled memberships from pruning.
-/
abbrev State.HealthyPendingBound (queue : State) (work : Execution.Work)
    (settled failed : List Occurrence)
    : Prop :=
  queue.PendingBound (fun ref => ¬GroupInvalidated work failed ref) settled

/-- Exact healthy accounting implies its lower-bound form. Witness: equality implies
the required inequality at each healthy live node.
-/
theorem State.HealthyPendingTracks.toBound {queue : State} {work settled failed}
    (tracks : queue.HealthyPendingTracks work settled failed)
    : queue.HealthyPendingBound work settled failed := by
  intro node member healthy
  exact Nat.le_of_eq (tracks node member healthy).symm

/-- No active root has been invalidated by task failure or defer ancestry.
Latent failed group shells need not satisfy this property. -/
def State.RootGroupsHealthy (queue : State) (work : Execution.Work)
    (failed : List Occurrence)
    : Prop :=
  ∀ ref ∈ queue.rootGroups, ¬GroupInvalidated work failed ref

/-- With no failed host occurrence, cleanup invalidation has no finite witness. -/
theorem createWorkQueue_rootGroupsHealthy (work : Execution.Work)
    : (State.initialize (Work.fromExecution work)).RootGroupsHealthy work [] := by
  intro ref member failed
  exact (GroupInvalidated.nonempty failed) rfl

/-- Pruning shells changes the group-node map, not the set of started root
group refs. -/
theorem State.pruneEmptyGroups_rootGroups
    (queue : State) (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.rootGroups = queue.rootGroups := by
  have loop (fuel : Nat) (current : State)
      (remaining kept : List Execution.DeliveryNode)
      : (State.pruneEmptyGroups.go fuel current remaining kept).1.rootGroups
          = current.rootGroups := by
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

/-- Initialization activates exactly the group refs it announces. Witness: integration
and pruning leave the initially empty root set unchanged; activation appends notices.
-/
theorem createWorkQueue_rootGroups (work : Work)
    : (State.initialize work).rootGroups
      = (State.initialize work).initialGroups.map Execution.DeliveryNode.ref := by
  let integrated := ({} : State).maybeIntegrateWork work
  let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
  have empty : pruned.1.rootGroups = [] := by
    rw [State.pruneEmptyGroups_rootGroups, State.maybeIntegrateWork_rootGroups]
  change (pruned.1.startNewWork
    { integrated.2 with newGroups := pruned.2 }).rootGroups = _
  rw [(pruned.1.startNewWork_groupCore _).2.2, empty]
  rfl

/-- Every initial root has a live group node. Witness: pruning retains only present
groups, and starting them leaves the group-node map unchanged.
-/
theorem createWorkQueue_rootGroupsPresent (work : Work)
    : (State.initialize work).RootGroupsPresent := by
  let integrated := ({} : State).maybeIntegrateWork work
  let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
  have unique : integrated.1.GroupRefsUnique :=
    State.GroupRefsUnique.maybeIntegrateWork (by simp [State.GroupRefsUnique]) work none
  have present := integrated.1.pruneEmptyGroups_keptPresent
    integrated.2.newGroups unique
  intro ref member
  rw [createWorkQueue_rootGroups] at member
  change ref ∈ (pruned.1.startNewWork
    { integrated.2 with newGroups := pruned.2 }).groupNodes.map _
  rw [(pruned.1.startNewWork_groupCore _).1]
  exact present ref member

/-- Successful group closure only removes a root; it does not activate its
children until the caller explicitly starts the released Work. -/
theorem State.finishGroupSuccess_rootGroups (queue : State) (group : GroupNode)
    : (queue.finishGroupSuccess group).1.rootGroups
      = queue.rootGroups.filter (· != group.group.node.ref) := by
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
  have stepRoots (acc : State × List ExecutionGroupValue × NodeRefs)
      (occurrence : Occurrence)
      : (step acc occurrence).1.rootGroups = acc.1.rootGroups := by
    obtain ⟨current, values, streams⟩ := acc
    dsimp only [step]
    split <;> rfl
  have foldRoots (tasks : List Occurrence) :
      ∀ acc : State × List ExecutionGroupValue × NodeRefs,
        (tasks.foldl step acc).1.rootGroups = acc.1.rootGroups := by
    induction tasks with
    | nil => intro acc; rfl
    | cons occurrence rest ih =>
        intro acc
        rw [List.foldl_cons, ih, stepRoots]
  let flushed := (group.tasks.foldl step (queue, [], [])).1
  have flushedRoots : flushed.rootGroups = queue.rootGroups :=
    foldRoots group.tasks (queue, [], [])
  let current : State :=
    { flushed with
        groupNodes := flushed.groupNodes.filter
          (fun node => node.group.node.ref != group.group.node.ref)
        rootGroups := flushed.rootGroups.filter (· != group.group.node.ref) }
  let children := group.childGroups.filterMap
    (fun ref => (current.groupNode? ref).map (fun node => node.group.node))
  have prunedRoots := current.pruneEmptyGroups_rootGroups children
  change (current.pruneEmptyGroups children).1.rootGroups
    = queue.rootGroups.filter (· != group.group.node.ref)
  rw [prunedRoots]
  exact congrArg (List.filter (· != group.group.node.ref)) flushedRoots

/-- Successful closure only removes the completed root from the active set.
Witness: the exact root-filter equation; activation is performed by the caller. -/
theorem State.finishGroupSuccess_rootsSubset (queue : State) (group : GroupNode)
    : (queue.finishGroupSuccess group).1.rootGroups.Subset queue.rootGroups := by
  intro ref member
  rw [queue.finishGroupSuccess_rootGroups group] at member
  exact (List.mem_filter.mp member).1

/-- A successful closure cannot turn any surviving root into a failed one. -/
theorem State.RootGroupsHealthy.finishGroupSuccess
    {queue : State} {work : Execution.Work} {failed : List Occurrence}
    (healthy : queue.RootGroupsHealthy work failed) (group : GroupNode)
    : (queue.finishGroupSuccess group).1.RootGroupsHealthy work failed := by
  intro ref member
  exact healthy ref (queue.finishGroupSuccess_rootsSubset group member)

/-- Recursive group removal cannot create an active root. -/
theorem State.removeGroup_rootsSubset (queue : State) (ref : NodeRef)
    : (queue.removeGroup ref).rootGroups.Subset queue.rootGroups := by
  intro root member
  unfold State.removeGroup at member
  exact (List.mem_filter.mp member).1

/-- Both stream-closure variants leave the active group-root set unchanged. -/
theorem State.RootGroupsHealthy.streamSuccess
    {queue : State} {work : Execution.Work} {failed : List Occurrence}
    (healthy : queue.RootGroupsHealthy work failed)
    (stream : Execution.DeliveryNode)
    : (queue.streamSuccess stream).1.RootGroupsHealthy work failed := by
  unfold State.streamSuccess
  split <;> exact healthy

theorem State.RootGroupsHealthy.streamFailure
    {queue : State} {work : Execution.Work} {failed : List Occurrence}
    (healthy : queue.RootGroupsHealthy work failed)
    (stream : Execution.DeliveryNode) (errors : Nat)
    : (queue.streamFailure stream errors).1.RootGroupsHealthy work failed := by
  unfold State.streamFailure
  split <;> exact healthy

/-- Processing a failed task only removes active groups; it never reopens a
root during the failure fold. -/
theorem State.taskFailure_rootsSubset
    (queue : State) (occurrence : Occurrence) (errors : Nat)
    : (queue.taskFailure occurrence errors).1.rootGroups.Subset queue.rootGroups := by
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
  have one (acc : State × List WorkQueueEvent)
      (group : Execution.DeliveryNode)
      : (step acc group).1.rootGroups.Subset acc.1.rootGroups := by
    obtain ⟨current, events⟩ := acc
    dsimp only [step]
    split
    · exact List.Subset.refl _
    · rename_i node found
      split
      · simpa [State.finishGroupFailure] using current.removeGroup_rootsSubset
          node.group.node.ref
      · exact List.Subset.refl _
  have fold (groups : List Execution.DeliveryNode) :
      ∀ acc : State × List WorkQueueEvent,
        (groups.foldl step acc).1.rootGroups.Subset acc.1.rootGroups := by
    induction groups with
    | nil => intro acc; exact List.Subset.refl _
    | cons group rest ih =>
        intro acc
        exact (ih (step acc group)).trans (one acc group)
  unfold State.taskFailure
  split
  · exact List.Subset.refl _
  · rename_i taskNode found
    split <;> try exact List.Subset.refl _
    let current := queue.removeTask occurrence
    change (taskNode.task.groups.foldl step (current, [])).1.rootGroups.Subset
      queue.rootGroups
    exact fold taskNode.task.groups (current, [])

/-- Newly activated groups preserve root health when each released group is
uninvalidated; streams do not affect this group-root predicate. -/
theorem State.RootGroupsHealthy.startNewWork
    {queue : State} {work : Execution.Work} {failed : List Occurrence}
    (healthy : queue.RootGroupsHealthy work failed) (newWork : NewWork)
    (releasedHealthy
      : ∀ group ∈ newWork.newGroups, ¬GroupInvalidated work failed group.ref)
    : (queue.startNewWork newWork).RootGroupsHealthy work failed := by
  intro ref member
  have roots := (queue.startNewWork_groupCore newWork).2.2
  rw [roots] at member
  rcases List.mem_append.mp member with old | new
  · exact healthy ref old
  · obtain ⟨group, groupMember, refEq⟩ := List.mem_map.mp new
    subst ref
    exact releasedHealthy group groupMember

/-- At initialization every group counter equals its full task list, and no
task has settled yet. -/
theorem createWorkQueue_healthyPendingTracks (work : Execution.Work)
    : (State.initialize (Work.fromExecution work)).HealthyPendingTracks work [] [] := by
  intro node member _
  have count := createWorkQueue_initialCounts (Work.fromExecution work) node member
  classical
  have filtered :
      (node.tasks.filter
        (fun task => decide (task ∉ ([] : List Occurrence)))) = node.tasks := by
    simp
  simpa only [GroupNode.PendingTracks, unsettledCount, filtered] using count

/-- A healthy-ledger invariant gives the active ledger whenever active roots
have not failed. -/
private theorem State.HealthyPendingTracks.toActive
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (tracks : queue.HealthyPendingTracks work settled failed)
    (rootsHealthy : ∀ ref ∈ queue.rootGroups, ¬GroupInvalidated work failed ref)
    : queue.ActivePendingTracks settled := by
  intro node member active
  exact tracks node member (rootsHealthy node.group.node.ref active)

/-- Replacing one group node preserves the healthy ledger when the updated
counter is balanced for any healthy ref. -/
theorem State.HealthyPendingTracks.putGroupNode
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (tracks : queue.HealthyPendingTracks work settled failed)
    (updated : GroupNode)
    (balanced
      : ¬GroupInvalidated work failed updated.group.node.ref
        → updated.PendingTracks settled)
    : (queue.putGroupNode updated).HealthyPendingTracks work settled failed := by
  intro node member healthy
  change node ∈ queue.groupNodes.map
    (fun old => if old.group.node.ref == updated.group.node.ref then updated else old)
    at member
  obtain ⟨old, oldMember, same⟩ := List.mem_map.mp member
  split at same
  · subst node
    exact balanced healthy
  · subst node
    exact tracks old oldMember healthy

/-- A newly registered group has zero pending tasks and therefore starts
balanced independently of its cleanup health. -/
theorem State.HealthyPendingTracks.addGroup
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (tracks : queue.HealthyPendingTracks work settled failed) (group : Group)
    : (queue.addGroup group).HealthyPendingTracks work settled failed := by
  unfold State.addGroup
  split
  · exact tracks
  · split
    · exact tracks
    · intro node member healthy
      rcases List.mem_append.mp member with old | added
      · exact tracks node old healthy
      · have same : node = { group } := List.mem_singleton.mp added
        subst node
        simp [GroupNode.PendingTracks, unsettledCount]

/-- Installing parent-child links leaves every pending counter unchanged. -/
theorem State.HealthyPendingTracks.addGroups
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (tracks : queue.HealthyPendingTracks work settled failed)
    (groups : List Group)
    : (queue.addGroups groups).1.HealthyPendingTracks work settled failed := by
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
              else node.childGroups ++ [group.node.ref]
            current.putGroupNode { node with childGroups := children }
  have registerFold (more : List Group) :
      ∀ current, current.HealthyPendingTracks work settled failed
        → (more.foldl State.addGroup current).HealthyPendingTracks work settled failed := by
    induction more with
    | nil => intro current currentTracks; exact currentTracks
    | cons group rest ih =>
        intro current currentTracks
        exact ih (current.addGroup group) (currentTracks.addGroup group)
  have linkStepTracks (current : State) (group : Group)
      (currentTracks : current.HealthyPendingTracks work settled failed)
      : (linkStep current group).HealthyPendingTracks work settled failed := by
    unfold linkStep
    split
    · exact currentTracks
    · rename_i node found
      split
      · exact currentTracks
      · rename_i node found
        apply currentTracks.putGroupNode
        exact currentTracks node (List.mem_of_find?_eq_some found)
  have linkFold (more : List Group) :
      ∀ current, current.HealthyPendingTracks work settled failed
        → (more.foldl linkStep current).HealthyPendingTracks work settled failed := by
    induction more with
    | nil => intro current currentTracks; exact currentTracks
    | cons group rest ih =>
        intro current currentTracks
        exact ih (linkStep current group) (linkStepTracks current group currentTracks)
  let fresh := groups.filter (fun group =>
    !queue.registeredGroups.contains group.node.ref
      && (queue.groupNode? group.node.ref).isNone)
  change (fresh.foldl linkStep
    (fresh.foldl State.addGroup queue)).HealthyPendingTracks work settled failed
  exact linkFold fresh _
    (registerFold fresh queue tracks)

/-- Integrating a task with a fresh occurrence adds one membership and one
pending token to every group that newly links it. -/
theorem State.HealthyPendingTracks.addTask
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (tracks : queue.HealthyPendingTracks work settled failed)
    (task : Task) (fresh : task.occurrence ∉ settled)
    : (queue.addTask task).HealthyPendingTracks work settled failed := by
  let registered : State := { queue with tasks := queue.tasks ++ [task] }
  let step (current : State) (group : Execution.DeliveryNode) : State :=
    match current.groupNode? group.ref with
    | none => current
    | some node =>
        if node.tasks.contains task.occurrence then current
        else current.putGroupNode
          { node with tasks := node.tasks ++ [task.occurrence], pending := node.pending + 1 }
  have stepTracks (current : State) (group : Execution.DeliveryNode)
      (currentTracks : current.HealthyPendingTracks work settled failed)
      : (step current group).HealthyPendingTracks work settled failed := by
    unfold step
    split
    · exact currentTracks
    · rename_i node found
      split
      · exact currentTracks
      · apply currentTracks.putGroupNode
        intro healthy
        exact GroupNode.PendingTracks.register node settled task.occurrence
          (currentTracks node (List.mem_of_find?_eq_some found) healthy) fresh
  have foldTracks (groups : List Execution.DeliveryNode) :
      ∀ current, current.HealthyPendingTracks work settled failed
        → (groups.foldl step current).HealthyPendingTracks work settled failed := by
    induction groups with
    | nil => intro current currentTracks; exact currentTracks
    | cons group rest ih =>
        intro current currentTracks
        exact ih (step current group) (stepTracks current group currentTracks)
  let current := task.groups.foldl step registered
  have currentTracks : current.HealthyPendingTracks work settled failed :=
    foldTracks task.groups registered tracks
  change (if task.groups.any (fun group => current.rootGroups.contains group.ref)
      && (current.taskNode? task.occurrence).isNone then
    { current with taskNodes := current.taskNodes ++ [{ task }] }
    else current).HealthyPendingTracks work settled failed
  split <;> exact currentTracks

/-- Registering streams touches no group pending counters. -/
theorem State.HealthyPendingTracks.addStreams
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (tracks : queue.HealthyPendingTracks work settled failed)
    (streams : List Stream) (parentTask : Option Occurrence)
    : (queue.addStreams streams parentTask).1.HealthyPendingTracks
        work settled failed := by
  unfold State.addStreams
  split
  · exact tracks
  · dsimp
    split <;> exact tracks

/-- Child Work integration preserves the ledger for all healthy groups when
each newly registered task occurrence is fresh relative to settlements. -/
theorem State.HealthyPendingTracks.maybeIntegrateWork
    {queue : State} {specWork : Execution.Work} {settled failed : List Occurrence}
    (tracks : queue.HealthyPendingTracks specWork settled failed)
    (newWork : Work)
    (fresh : ∀ task ∈ newWork.tasks, task.occurrence ∉ settled)
    (parentTask : Option Occurrence := none)
    : (queue.maybeIntegrateWork newWork parentTask).1.HealthyPendingTracks
        specWork settled failed := by
  let withGroups := (queue.addGroups newWork.groups).1
  let withTasks := newWork.tasks.foldl State.addTask withGroups
  have groupTracks : withGroups.HealthyPendingTracks specWork settled failed :=
    tracks.addGroups newWork.groups
  have taskFold (more : List Task)
      (subset : ∀ task ∈ more, task ∈ newWork.tasks) :
      ∀ current, current.HealthyPendingTracks specWork settled failed
        → (more.foldl State.addTask current).HealthyPendingTracks
            specWork settled failed := by
    induction more with
    | nil => intro current currentTracks; exact currentTracks
    | cons task rest ih =>
        intro current currentTracks
        have restSubset : ∀ later ∈ rest, later ∈ newWork.tasks := by
          intro later member
          exact subset later (by simp [member])
        exact ih restSubset (current.addTask task)
          (currentTracks.addTask task (fresh task (subset task (by simp))))
  have taskTracks : withTasks.HealthyPendingTracks specWork settled failed :=
    taskFold newWork.tasks (fun _ member => member) withGroups groupTracks
  change (withTasks.addStreams newWork.streams parentTask).1.HealthyPendingTracks
    specWork settled failed
  exact taskTracks.addStreams newWork.streams parentTask

/-- Pruning, activation, and group deletion only discard group nodes or
change task/root registries; surviving healthy counters remain balanced. -/
theorem State.HealthyPendingTracks.pruneEmptyGroups
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (tracks : queue.HealthyPendingTracks work settled failed)
    (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.HealthyPendingTracks work settled failed := by
  have loop (fuel : Nat) (current : State)
      (remaining kept : List Execution.DeliveryNode)
      (currentTracks : current.HealthyPendingTracks work settled failed)
      : (State.pruneEmptyGroups.go fuel current remaining kept).1.HealthyPendingTracks
          work settled failed := by
    induction fuel generalizing current remaining kept with
    | zero => exact currentTracks
    | succ fuel ih =>
        cases remaining with
        | nil => exact currentTracks
        | cons group rest =>
            unfold State.pruneEmptyGroups.go
            split
            · exact ih _ _ _ currentTracks
            · split
              · apply ih
                intro node member healthy
                exact currentTracks node (List.mem_filter.mp member).1 healthy
              · exact ih _ _ _ currentTracks
  exact loop _ queue groups [] tracks

theorem State.HealthyPendingTracks.startNewWork
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (tracks : queue.HealthyPendingTracks work settled failed)
    (newWork : NewWork)
    : (queue.startNewWork newWork).HealthyPendingTracks work settled failed := by
  intro node member healthy
  have same := (queue.startNewWork_groupCore newWork).1
  rw [same] at member
  exact tracks node member healthy

theorem State.HealthyPendingTracks.removeGroup
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (tracks : queue.HealthyPendingTracks work settled failed) (ref : NodeRef)
    : (queue.removeGroup ref).HealthyPendingTracks work settled failed := by
  intro node member healthy
  unfold State.removeGroup at member
  exact tracks node (List.mem_filter.mp member).1 healthy

/-- Once more host failures have been observed, fewer group refs remain
healthy, so a previously valid ledger remains valid. -/
theorem State.HealthyPendingTracks.weakenFailures
    {queue : State} {work : Execution.Work} {settled before after : List Occurrence}
    (tracks : queue.HealthyPendingTracks work settled before)
    (included : before.Subset after)
    : queue.HealthyPendingTracks work settled after := by
  intro node member healthy
  apply tracks node member
  intro failedBefore
  exact healthy (GroupInvalidated.mono failedBefore included)

/-- A failed task changes memberships and counters only in newly invalidated owners.
Witness: registration provenance and membership soundness identify those owners;
the actual failure fold therefore preserves every still-healthy ledger.
-/
theorem State.HealthyPendingTracks.taskFailure
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (tracks : queue.HealthyPendingTracks work settled failed)
    (registered : queue.StartedTasksRegistered)
    (matching : queue.RegisteredTasksMatch work)
    (sound : queue.GroupMembershipSound)
    (occurrence : Occurrence) (errors : Nat)
    : (queue.taskFailure occurrence errors).1.HealthyPendingTracks
        work settled (occurrence :: failed) := by
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
  have stepTracks (acc : State × List WorkQueueEvent)
      (group : Execution.DeliveryNode)
      (invalid : GroupInvalidated work (occurrence :: failed) group.ref)
      (currentTracks : acc.1.HealthyPendingTracks work settled (occurrence :: failed))
      : (step acc group).1.HealthyPendingTracks
          work settled (occurrence :: failed) := by
    obtain ⟨current, events⟩ := acc
    dsimp only [step]
    split
    · exact currentTracks
    · rename_i node found
      split
      · rw [State.finishGroupFailure, State.groupNode?_ref found]
        exact currentTracks.removeGroup group.ref
      · apply currentTracks.putGroupNode
        intro healthy
        exact (healthy ((current.groupNode?_ref found).symm ▸ invalid)).elim
  have foldTracks (groups : List Execution.DeliveryNode) :
      (∀ group ∈ groups, GroupInvalidated work (occurrence :: failed) group.ref) →
      ∀ acc : State × List WorkQueueEvent,
        acc.1.HealthyPendingTracks work settled (occurrence :: failed)
          → (groups.foldl step acc).1.HealthyPendingTracks
              work settled (occurrence :: failed) := by
    induction groups with
    | nil => intro _ acc currentTracks; exact currentTracks
    | cons group rest ih =>
        intro invalid acc currentTracks
        exact ih (fun item member => invalid item (List.mem_cons_of_mem _ member))
          (step acc group) (stepTracks acc group (invalid group List.mem_cons_self) currentTracks)
  unfold State.taskFailure
  split
  · exact tracks.weakenFailures (by intro item member; simp [member])
  · rename_i taskNode found
    have member := List.mem_of_find?_eq_some found
    have same : taskNode.task.occurrence = occurrence :=
      (occurrence_beq_iff_eq _ _).mp
        (List.find?_some (p := fun node : TaskNode => node.task.occurrence == occurrence) found)
    obtain ⟨_, payload, producer, _, known⟩ :=
      (matching taskNode.task (registered taskNode member)).1
    have owners : TaskHasOwners work occurrence
        (taskNode.task.groups.map Execution.DeliveryNode.ref) :=
      ⟨producer, payload, same ▸ known⟩
    have invalid (group : Execution.DeliveryNode) (inGroups : group ∈ taskNode.task.groups)
        : GroupInvalidated work (occurrence :: failed) group.ref :=
      .task owners (List.mem_map.mpr ⟨group, inGroups, rfl⟩) List.mem_cons_self
    let current := queue.removeTask occurrence
    have currentTracks : current.HealthyPendingTracks
        work settled (occurrence :: failed) := by
      intro node nodeMember healthy
      obtain ⟨old, oldMember, equal⟩ := List.mem_map.mp nodeMember
      subst node
      have absent : occurrence ∉ old.tasks := by
        intro listed
        exact healthy (.task owners
          (sound.startedOwner registered matching (groupNode := old)
            member oldMember (same.symm ▸ listed))
          List.mem_cons_self)
      have unchanged : old.tasks.filter (· != occurrence) = old.tasks := by
        apply List.filter_eq_self.mpr
        intro task taskMember
        have different : (task == occurrence) = false := by
          cases equal : task == occurrence with
          | false => rfl
          | true =>
              exact (absent ((occurrence_beq_iff_eq _ _).mp equal ▸ taskMember)).elim
        simp [bne, different]
      change old.pending = unsettledCount (old.tasks.filter (· != occurrence)) settled
      rw [unchanged]
      exact (tracks.weakenFailures (by intro item itemMember; simp [itemMember]))
        old oldMember healthy
    split <;> try exact currentTracks
    change (taskNode.task.groups.foldl step (current, [])).1.HealthyPendingTracks
      work settled (occurrence :: failed)
    exact foldTracks taskNode.task.groups invalid (current, []) currentTracks

/-- Flushing a task already present in the settlement prefix changes no
healthy pending count, even for latent groups that share the task. -/
theorem State.HealthyPendingTracks.removeTask
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (tracks : queue.HealthyPendingTracks work settled failed)
    (occurrence : Occurrence) (already : occurrence ∈ settled)
    : (queue.removeTask occurrence).HealthyPendingTracks work settled failed := by
  intro node member healthy
  change node ∈ queue.groupNodes.map
    (fun prior => { prior with tasks := prior.tasks.filter (· != occurrence) })
    at member
  obtain ⟨prior, priorMember, same⟩ := List.mem_map.mp member
  subst node
  change prior.pending = unsettledCount
    (prior.tasks.filter (· != occurrence)) settled
  rw [unsettledCount_remove_settled prior.tasks settled occurrence already]
  exact tracks prior priorMember healthy

/-- A completed group whose stored tasks have all settled can flush their
values without disturbing any surviving healthy group ledger. -/
theorem State.HealthyPendingTracks.finishGroupSuccess
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (tracks : queue.HealthyPendingTracks work settled failed)
    (group : GroupNode) (all : ∀ occurrence ∈ group.tasks, occurrence ∈ settled)
    : (queue.finishGroupSuccess group).1.HealthyPendingTracks work settled failed := by
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
  have stepTracks (acc : State × List ExecutionGroupValue × NodeRefs)
      (occurrence : Occurrence)
      (currentTracks : acc.1.HealthyPendingTracks work settled failed)
      (already : occurrence ∈ settled)
      : (step acc occurrence).1.HealthyPendingTracks work settled failed := by
    obtain ⟨current, values, streams⟩ := acc
    dsimp only [step]
    split
    · exact currentTracks
    · exact currentTracks.removeTask occurrence already
  have foldTracks (tasks : List Occurrence)
      (all : ∀ occurrence ∈ tasks, occurrence ∈ settled) :
      ∀ acc : State × List ExecutionGroupValue × NodeRefs,
        acc.1.HealthyPendingTracks work settled failed
          → (tasks.foldl step acc).1.HealthyPendingTracks
              work settled failed := by
    induction tasks with
    | nil => intro acc currentTracks; exact currentTracks
    | cons occurrence rest ih =>
        intro acc currentTracks
        have head : occurrence ∈ settled := all occurrence (by simp)
        have tail : ∀ task ∈ rest, task ∈ settled := by
          intro task member
          exact all task (by simp [member])
        exact ih tail (step acc occurrence)
          (stepTracks acc occurrence currentTracks head)
  let flushed := (group.tasks.foldl step (queue, [], [])).1
  have flushedTracks : flushed.HealthyPendingTracks work settled failed :=
    foldTracks group.tasks all (queue, [], []) tracks
  let current : State :=
    { flushed with
        groupNodes := flushed.groupNodes.filter
          (fun node => node.group.node.ref != group.group.node.ref)
        rootGroups := flushed.rootGroups.filter (· != group.group.node.ref) }
  have currentTracks : current.HealthyPendingTracks work settled failed := by
    intro node member healthy
    exact flushedTracks node (List.mem_filter.mp member).1 healthy
  let children := group.childGroups.filterMap
    (fun ref => (current.groupNode? ref).map (fun node => node.group.node))
  change (current.pruneEmptyGroups children).1.HealthyPendingTracks work settled failed
  exact currentTracks.pruneEmptyGroups children

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
