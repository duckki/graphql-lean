import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.HealthyContributors
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskSupport

/-! Permanent registration has a supporting task, possibly through a taskless ancestor. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (
  ExecutionGroupValue StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Parametric task support separates registration from direct contribution
-----------------------------------------------------------------------------------------

/-- Each candidate has an immediate task satisfying the specified ref-support relation. -/
def Work.GroupsSupportedBy (work : Work) (support : Task → Nat → Prop) : Prop :=
  ∀ group ∈ work.groups, ∃ task ∈ work.tasks, support task group.node.ref

/-- Direct-contributor specialization for conditional task-bearing-group lemmas.
Arbitrary lowered work need not satisfy this: taskless ancestor candidates have support,
but no direct contributing task.
-/
abbrev Work.GroupsHaveTasks (work : Work) : Prop :=
  work.GroupsSupportedBy
    (fun task ref => ref ∈ task.groups.map Execution.DeliveryNode.ref)

/-- Each permanent registration has a permanent task satisfying `support`.
The supporting task need not be started, unsettled, successful, or currently live.
-/
def State.RegistrationsSupportedBy (queue : State) (support : Task → Nat → Prop) : Prop :=
  ∀ ref ∈ queue.registeredGroups, ∃ task ∈ queue.tasks, support task ref

/-- Conditional direct-contributor specialization; not an invariant of arbitrary replay. -/
abbrev State.RegistrationsHaveTasks (queue : State) : Prop :=
  queue.RegistrationsSupportedBy
    (fun task ref => ref ∈ task.groups.map Execution.DeliveryNode.ref)

/-- A preserved state predicate extends through a finite fold.
Witness: induction over inputs, threading the actual accumulator. -/
private theorem fold_preserves {α β : Type} (step : β → α → β) (property : β → Prop)
    (preserved : ∀ state item, property state → property (step state item))
    (items : List α) (state : β) (initial : property state)
    : property (items.foldl step state) := by
  induction items generalizing state with
  | nil => exact initial
  | cons item rest ih => exact ih (step state item) (preserved state item initial)

/-- Group integration adds no ref outside the old registry and supplied candidates.
Witness: registration only appends a candidate; linking changes neither registry nor tasks.
-/
theorem State.addGroups_registeredGroups_subset (queue : State) (groups : List Group)
    : (queue.addGroups groups).1.registeredGroups.Subset
        (queue.registeredGroups ++ groups.map (fun group => group.node.ref)) := by
  let allowed := queue.registeredGroups ++ groups.map (fun group => group.node.ref)
  let property (current : State) := current.registeredGroups.Subset allowed
  let fresh := groups.filter (fun group =>
    !queue.registeredGroups.contains group.node.ref
      && (queue.groupNode? group.node.ref).isNone)
  have registered (more : List Group) (included : more.Subset groups)
      (current : State) (prior : property current)
      : property (more.foldl State.addGroup current) := by
    induction more generalizing current with
    | nil => exact prior
    | cons group rest ih =>
        apply ih (fun candidate member => included (List.mem_cons_of_mem _ member))
        unfold State.addGroup
        split
        · exact prior
        · dsimp only
          split <;> intro ref member
          all_goals
          rcases List.mem_append.mp member with old | new
          · exact prior old
          · have same : ref = group.node.ref := List.mem_singleton.mp new
            exact List.mem_append_right _ (List.mem_map.mpr
              ⟨group, included List.mem_cons_self, same.symm⟩)
  let link (current : State) (group : Group) : State :=
    match group.parent with
    | none => current
    | some parent =>
        match current.groupNode? parent with
        | none => current
        | some node =>
            let children := if node.childGroups.contains group.node.ref then
              node.childGroups else node.childGroups ++ [group.node.ref]
            current.putGroupNode { node with childGroups := children }
  have linked (current : State) (group : Group) (prior : property current)
      : property (link current group) := by
    unfold link
    split
    · exact prior
    · split <;> exact prior
  exact fold_preserves link property linked fresh _
    (registered fresh (fun _ member => (List.mem_filter.mp member).1) queue
      (fun _ member => List.mem_append_left _ member))

/-- Registering a task leaves group registration history unchanged.
Witness: every membership update replaces an existing group node. -/
theorem State.addTask_registeredGroups (queue : State) (task : Task)
    : (queue.addTask task).registeredGroups = queue.registeredGroups := by
  let registered : State := { queue with tasks := queue.tasks ++ [task] }
  let step (current : State) (group : Execution.DeliveryNode) : State :=
    match current.groupNode? group.ref with
    | none => current
    | some node =>
        if node.tasks.contains task.occurrence then current
        else current.putGroupNode
          { node with tasks := node.tasks ++ [task.occurrence], pending := node.pending + 1 }
  have preserved (current : State) (group : Execution.DeliveryNode)
      (prior : current.registeredGroups = queue.registeredGroups)
      : (step current group).registeredGroups = queue.registeredGroups := by
    unfold step
    split
    · exact prior
    · split <;> exact prior
  let current := task.groups.foldl step registered
  have unchanged : current.registeredGroups = queue.registeredGroups :=
    fold_preserves step (fun state => state.registeredGroups = queue.registeredGroups)
      preserved task.groups registered rfl
  change (if task.groups.any (fun group => current.rootGroups.contains group.ref)
      && (current.taskNode? task.occurrence).isNone then
      { current with taskNodes := current.taskNodes ++ [{ task }] }
    else current).registeredGroups = queue.registeredGroups
  split <;> exact unchanged

/-- Integration registers only old refs or candidates supported by immediate tasks.
Witness: group-ref inclusion and the exact append-only task registry equation. -/
theorem State.RegistrationsSupportedBy.maybeIntegrateWork {queue : State}
    {support : Task → Nat → Prop} (covered : queue.RegistrationsSupportedBy support)
    (work : Work) (workCovered : work.GroupsSupportedBy support)
    (parentTask : Option Occurrence := none)
    : (queue.maybeIntegrateWork work parentTask).1.RegistrationsSupportedBy support := by
  let grouped := (queue.addGroups work.groups).1
  let tasked := work.tasks.foldl State.addTask grouped
  have taskedSame : tasked.registeredGroups = grouped.registeredGroups :=
    fold_preserves State.addTask
      (fun state => state.registeredGroups = grouped.registeredGroups)
      (fun state task prior => (state.addTask_registeredGroups task).trans prior)
      work.tasks grouped rfl
  have same : (queue.maybeIntegrateWork work parentTask).1.registeredGroups
      = grouped.registeredGroups := by
    change (tasked.addStreams work.streams parentTask).1.registeredGroups = _
    unfold State.addStreams
    split
    · exact taskedSame
    · dsimp
      split <;> exact taskedSame
  intro ref member
  rw [same] at member
  have included := queue.addGroups_registeredGroups_subset work.groups member
  rw [State.maybeIntegrateWork_tasks_append]
  rcases List.mem_append.mp included with old | new
  · obtain ⟨task, taskMember, contributor⟩ := covered ref old
    exact ⟨task, List.mem_append_left _ taskMember, contributor⟩
  · obtain ⟨group, groupMember, sameRef⟩ := List.mem_map.mp new
    obtain ⟨task, taskMember, contributor⟩ := workCovered group groupMember
    exact ⟨task, List.mem_append_right _ taskMember, sameRef ▸ contributor⟩

-----------------------------------------------------------------------------------------
-- Cleanup and activation preserve the permanent task witness
-----------------------------------------------------------------------------------------

/-- Pruning deletes live nodes, not their permanent registration/task evidence.
Witness: induction over the actual pruning traversal. -/
theorem State.RegistrationsSupportedBy.pruneEmptyGroups {queue : State}
    {support : Task → Nat → Prop} (covered : queue.RegistrationsSupportedBy support)
    (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.RegistrationsSupportedBy support := by
  have loop (fuel : Nat) (current : State) (remaining kept : List Execution.DeliveryNode)
      (prior : current.RegistrationsSupportedBy support)
      : (State.pruneEmptyGroups.go fuel current remaining kept).1.RegistrationsSupportedBy
          support := by
    induction fuel generalizing current remaining kept with
    | zero => exact prior
    | succ fuel ih =>
        cases remaining with
        | nil => exact prior
        | cons group rest =>
            unfold State.pruneEmptyGroups.go
            split
            · exact ih _ _ _ prior
            · split <;> exact ih _ _ _ prior
  exact loop _ queue groups [] covered

/-- Activation touches neither permanent registry.
Witness: task and stream starts only change live task nodes or root lists. -/
theorem State.RegistrationsSupportedBy.startNewWork {queue : State}
    {support : Task → Nat → Prop} (covered : queue.RegistrationsSupportedBy support)
    (work : NewWork)
    : (queue.startNewWork work).RegistrationsSupportedBy support := by
  have taskStep (current : State) (occurrence : Occurrence)
      (prior : current.RegistrationsSupportedBy support)
      : (current.startTask occurrence).RegistrationsSupportedBy support := by
    unfold State.startTask
    split
    · exact prior
    · split <;> exact prior
  have groupStep (current : State) (ref : NodeRef) (prior : current.RegistrationsSupportedBy support)
      : (current.startGroup ref).RegistrationsSupportedBy support := by
    unfold State.startGroup
    split
    · exact prior
    · split
      · exact prior
      · exact fold_preserves State.startTask (fun state => state.RegistrationsSupportedBy support)
          taskStep _ current prior
  have streamStep (current : State) (ref : NodeRef) (prior : current.RegistrationsSupportedBy support)
      : (current.startStream ref).RegistrationsSupportedBy support := by
    unfold State.startStream
    split <;> exact prior
  exact fold_preserves State.startStream
    (fun state => state.RegistrationsSupportedBy support) streamStep _ _
    (fold_preserves State.startGroup (fun state => state.RegistrationsSupportedBy support)
      groupStep _ _ covered)

/-- Every initial candidate has a permanent supporting task, even after pruning.
Witness: full-chain lowering support and support-parametric integration preservation.
-/
theorem createWorkQueue_fromSpec_registrationsSupported (work : Execution.Work)
    : (State.initialize (Work.fromExecution work)).RegistrationsSupportedBy
        (Task.SupportsGroup work) := by
  have empty : ({} : State).RegistrationsSupportedBy (Task.SupportsGroup work) := by
    intro ref member
    cases member
  exact ((empty.maybeIntegrateWork (Work.fromExecution work)
    (fun _ member => workFromSpec_groups_taskSupport (Located.root (root := work)) member)
    ).pruneEmptyGroups _).startNewWork _

/-- Successful publication preserves registration witnesses, including removed tasks.
Witness: the flush removes live task nodes/memberships but retains task definitions. -/
theorem State.RegistrationsSupportedBy.finishGroupSuccess {queue : State}
    {support : Task → Nat → Prop} (covered : queue.RegistrationsSupportedBy support)
    (group : GroupNode)
    : (queue.finishGroupSuccess group).1.RegistrationsSupportedBy support := by
  let step (acc : State × List ExecutionGroupValue × NodeRefs) (task : Occurrence) :=
    let (current, values, streams) := acc
    match current.taskNode? task with
    | none => (current, values, streams)
    | some taskNode =>
        let values := match taskNode.value with
          | none => values
          | some value => values ++ [value]
        (current.removeTask task, values, streams ++ taskNode.childStreams)
  have preserved (acc : State × List ExecutionGroupValue × NodeRefs) (task : Occurrence)
      (prior : acc.1.RegistrationsSupportedBy support)
      : (step acc task).1.RegistrationsSupportedBy support := by
    obtain ⟨current, values, streams⟩ := acc
    unfold step
    dsimp only
    split <;> exact prior
  have flushed := fold_preserves step (fun acc => acc.1.RegistrationsSupportedBy support)
    preserved group.tasks (queue, [], []) covered
  let flushedState := (group.tasks.foldl step (queue, [], [])).1
  let current : State :=
    { flushedState with
      groupNodes := flushedState.groupNodes.filter
        (fun node => node.group.node.ref != group.group.node.ref)
      rootGroups := flushedState.rootGroups.filter (· != group.group.node.ref) }
  have currentCovered : current.RegistrationsSupportedBy support := flushed
  exact currentCovered.pruneEmptyGroups _

/-- Recursive draining retains the task witnesses for every permanent registration.
Witness: both closure paths retain the registries, and activation also preserves them.
-/
theorem State.RegistrationsSupportedBy.drainReadyGroups {queue : State}
    {support : Task → Nat → Prop} (covered : queue.RegistrationsSupportedBy support)
    : queue.drainReadyGroups.1.RegistrationsSupportedBy support := by
  apply State.drainReadyGroups_preserves
    (fun state => state.RegistrationsSupportedBy support) (valid := covered)
  · intro current node prior _ _ _ _
    exact (prior.finishGroupSuccess node).startNewWork _
  · intro current node errors prior _ _ _
    exact prior

/-- One successful task preserves permanent registration provenance.
Witness: covered child integration followed by the single-pass contributor fold. -/
theorem State.RegistrationsSupportedBy.taskSuccess {queue : State}
    {support : Task → Nat → Prop} (covered : queue.RegistrationsSupportedBy support)
    (task : Occurrence) (result : TaskResult)
    (children : result.work.GroupsSupportedBy support)
    : (queue.taskSuccess task result).1.RegistrationsSupportedBy support := by
  cases found : queue.taskNode? task with
  | none => simpa [State.taskSuccess, found] using covered
  | some node =>
      rw [queue.taskSuccess_eq task result node found]
      split <;> try exact covered
      have stored : (queue.putTaskNode { node with value := some result.value
          }).RegistrationsSupportedBy support := covered
      have integrated := stored.maybeIntegrateWork result.work children (some task)
      have preserved (acc : State × List WorkQueueEvent × NewWork)
          (group : Execution.DeliveryNode) (prior : acc.1.RegistrationsSupportedBy support)
          : (successGroupStep acc group).1.RegistrationsSupportedBy support := by
        obtain ⟨current, events, released⟩ := acc
        unfold successGroupStep
        dsimp only
        split
        · exact prior
        · rename_i groupNode found
          have updated : (current.putGroupNode
              { groupNode with pending := groupNode.pending - 1 }).RegistrationsSupportedBy
                support := prior
          split
          · exact updated.finishGroupSuccess _
          · exact prior
      exact ((fold_preserves successGroupStep
                (fun acc => acc.1.RegistrationsSupportedBy support) preserved
                node.task.groups (_, [], {}) integrated).startNewWork
              _).drainReadyGroups

/-- Task failure never deletes permanent registration witnesses.
Witness: owner removal and latent error retention leave the registries unchanged. -/
theorem State.RegistrationsSupportedBy.taskFailure {queue : State}
    {support : Task → Nat → Prop} (covered : queue.RegistrationsSupportedBy support)
    (task : Occurrence) (errors : Nat)
    : (queue.taskFailure task errors).1.RegistrationsSupportedBy support := by
  let step (acc : State × List WorkQueueEvent) (group : Execution.DeliveryNode) :=
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
  have preserved (acc : State × List WorkQueueEvent) (group : Execution.DeliveryNode)
      (prior : acc.1.RegistrationsSupportedBy support)
      : (step acc group).1.RegistrationsSupportedBy support := by
    obtain ⟨current, events⟩ := acc
    unfold step
    dsimp only
    split
    · exact prior
    · split <;> exact prior
  unfold State.taskFailure
  split
  · exact covered
  · split <;> try exact covered
    exact fold_preserves step (fun acc => acc.1.RegistrationsSupportedBy support)
      preserved _ _ covered

/-- Stream-item child work preserves provenance at each successive integration state.
Witness: induction through integration, pruning, and activation for the actual item fold. -/
theorem State.RegistrationsSupportedBy.streamItems {queue : State}
    {support : Task → Nat → Prop} (covered : queue.RegistrationsSupportedBy support)
    (stream : Execution.DeliveryNode) (items : List StreamItem)
    (children : ∀ item ∈ items, item.work.GroupsSupportedBy support)
    : (queue.streamItems stream items).1.RegistrationsSupportedBy support := by
  let step (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue) (item : StreamItem) :=
    let (current, groups, streams, values) := acc
    let (integrated, newWork) := current.maybeIntegrateWork item.work
    let (pruned, nonempty) := integrated.pruneEmptyGroups newWork.newGroups
    (pruned.startNewWork { newWork with newGroups := nonempty },
      groups ++ nonempty, streams ++ newWork.newStreams, values ++ [item.value])
  have loop (more : List StreamItem) (included : more.Subset items)
      (acc : State × List Execution.DeliveryNode
        × List Execution.DeliveryNode × List StreamItemValue)
      (prior : acc.1.RegistrationsSupportedBy support)
      : (more.foldl step acc).1.RegistrationsSupportedBy support := by
    induction more generalizing acc with
    | nil => exact prior
    | cons item rest ih =>
        apply ih (fun _ member => included (List.mem_cons_of_mem _ member))
        exact ((prior.maybeIntegrateWork item.work
          (children item (included List.mem_cons_self))).pruneEmptyGroups _).startNewWork _
  unfold State.streamItems
  split
  · exact covered
  · exact (loop items (fun _ member => member) (queue, [], [], []) covered).drainReadyGroups

-----------------------------------------------------------------------------------------
-- Matching source replay supplies registration provenance without scheduling premises
-----------------------------------------------------------------------------------------

/-- Matching the finite source outcomes suffices to preserve registration provenance.
Witness: source matching supplies covered child work to the success handlers. -/
theorem State.RegistrationsSupportedBy.handleGraphEvent {queue : State}
    {work : Execution.Work}
    (covered : queue.RegistrationsSupportedBy (Task.SupportsGroup work))
    (event : GraphEvent) (matching : event.MatchesWork work)
    : (queue.handleGraphEvent event).1.RegistrationsSupportedBy
        (Task.SupportsGroup work) := by
  cases event with
  | taskSuccess task result =>
      exact covered.taskSuccess task result (fun _ member => matching.childGroupsSupported member)
  | taskFailure task errors => exact covered.taskFailure task errors
  | streamItems stream items =>
      exact covered.streamItems stream items
        (fun _ member _ groupMember => matching.streamItem_groupsSupported member groupMember)
  | streamSuccess stream =>
      change (queue.streamSuccess stream).1.RegistrationsSupportedBy (Task.SupportsGroup work)
      unfold State.streamSuccess
      split <;> exact covered
  | streamFailure stream errors =>
      change (queue.streamFailure stream errors).1.RegistrationsSupportedBy
        (Task.SupportsGroup work)
      unfold State.streamFailure
      split <;> exact covered

/-- Batch handling retains provenance, including ignored post-termination batches.
Witness: eventwise preservation and the fact that termination changes neither registry. -/
theorem State.RegistrationsSupportedBy.handleGraphEvents {queue : State}
    {work : Execution.Work}
    (covered : queue.RegistrationsSupportedBy (Task.SupportsGroup work))
    (events : List GraphEvent) (matching : ∀ event ∈ events, event.MatchesWork work)
    : (queue.handleGraphEvents events).1.RegistrationsSupportedBy
        (Task.SupportsGroup work) := by
  let step (acc : State × List WorkQueueEvent) (event : GraphEvent) :=
    let (current, outputs) := acc
    let (next, produced) := current.handleGraphEvent event
    (next, outputs ++ produced)
  have loop (more : List GraphEvent) (included : more.Subset events)
      (acc : State × List WorkQueueEvent)
      (prior : acc.1.RegistrationsSupportedBy (Task.SupportsGroup work))
      : (more.foldl step acc).1.RegistrationsSupportedBy (Task.SupportsGroup work) := by
    induction more generalizing acc with
    | nil => exact prior
    | cons event rest ih =>
        exact ih (fun _ member => included (List.mem_cons_of_mem _ member)) _
          (prior.handleGraphEvent event (matching event (included List.mem_cons_self)))
  have folded := loop events (fun _ member => member) (queue, []) covered
  unfold State.handleGraphEvents
  split
  · exact covered
  · dsimp only
    split <;> exact folded

/-- Publisher normalization leaves provenance intact across all matching input batches.
Witness: induction over the executable normalized fold; no start or health premise. -/
theorem State.RegistrationsSupportedBy.runNormalized {queue : State}
    {work : Execution.Work}
    (covered : queue.RegistrationsSupportedBy (Task.SupportsGroup work))
    (batches : List (List GraphEvent))
    (matching : ∀ batch ∈ batches, ∀ event ∈ batch, event.MatchesWork work)
    : (queue.runNormalized batches).1.RegistrationsSupportedBy
        (Task.SupportsGroup work) := by
  have stepCovered (acc : NormalizedAcc) (batch : List GraphEvent)
      (batchMatch : ∀ event ∈ batch, event.MatchesWork work)
      (prior : acc.1.RegistrationsSupportedBy (Task.SupportsGroup work))
      : (normalizedStep acc batch).1.RegistrationsSupportedBy (Task.SupportsGroup work) := by
    obtain ⟨current, publisher, outputs⟩ := acc
    have next := prior.handleGraphEvents batch batchMatch
    unfold normalizedStep
    dsimp only
    split <;> exact next
  have loop (more : List (List GraphEvent)) (included : more.Subset batches)
      (acc : NormalizedAcc) (prior : acc.1.RegistrationsSupportedBy (Task.SupportsGroup work))
      : (more.foldl normalizedStep acc).1.RegistrationsSupportedBy (Task.SupportsGroup work) := by
    induction more generalizing acc with
    | nil => exact prior
    | cons batch rest ih =>
        exact ih (fun _ member => included (List.mem_cons_of_mem _ member)) _
          (stepCovered acc batch (matching batch (included List.mem_cons_self)) prior)
  exact loop batches (fun _ member => member)
    (queue, { active := queue.initialGroups ++ queue.initialStreams }, []) covered

/-- Every registration in valid replay has a permanent full-chain supporting task.
Witness: initialization and matching-event preservation; generated-work and queue
acceptance premises are unnecessary for this independent implementation invariant. -/
theorem createWorkQueue_runNormalized_registrationsSupported
    {work : Execution.Work} {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten)
    : ((State.initialize (Work.fromExecution work)).runNormalized
        batches).1.RegistrationsSupportedBy
        (Task.SupportsGroup work) :=
  (createWorkQueue_fromSpec_registrationsSupported work).runNormalized batches
    (fun _ batchMember _ eventMember =>
      valid.eachMatches (List.mem_flatten.mpr ⟨_, batchMember, eventMember⟩))

-----------------------------------------------------------------------------------------
-- Reduce healthy registration availability to old contributor accounting
-----------------------------------------------------------------------------------------

/-- A ref not referenced by any integrated task is available for first registration.
Witness: registration provenance excludes the permanent-registry obstruction. -/
theorem State.RegistrationsHaveTasks.available_of_unreferenced
    {queue : State} (covered : queue.RegistrationsHaveTasks) {ref : NodeRef}
    (unreferenced
      : ∀ task ∈ queue.tasks, ref ∉ task.groups.map Execution.DeliveryNode.ref)
    : queue.GroupAvailable ref := by
  right
  intro registered
  obtain ⟨task, member, contributor⟩ := covered ref registered
  exact unreferenced task member contributor

/-- An unsettled registered contributor protects each healthy group from retirement.
Witness: healthy task accounting supplies a live node, independently of registration age. -/
theorem State.HealthyRegisteredTaskAccounting.groupAvailable
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (accounted : queue.HealthyRegisteredTaskAccounting work settled failed)
    {task : Task} (member : task ∈ queue.tasks) (fresh : task.occurrence ∉ settled)
    {ref : NodeRef} (contributor : ref ∈ task.groups.map Execution.DeliveryNode.ref)
    (healthy : ¬GroupInvalidated work failed ref)
    : queue.GroupAvailable ref := by
  obtain ⟨node, nodeMember, sameRef, _⟩ :=
    accounted task member fresh ref contributor healthy
  exact Or.inl (List.mem_map.mpr ⟨node, nodeMember, sameRef⟩)

/-- An unavailable healthy group must have old contributors, all already settled.
Witness: provenance supplies one contributor; any unsettled contributor would keep the
group live. This isolates the remaining generated-work obligation, without assuming it. -/
theorem State.RegistrationsHaveTasks.unavailable_healthy_contributors_settled
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (covered : queue.RegistrationsHaveTasks)
    (accounted : queue.HealthyRegisteredTaskAccounting work settled failed)
    {ref : NodeRef} (unavailable : ¬queue.GroupAvailable ref)
    (healthy : ¬GroupInvalidated work failed ref)
    : (∃ task ∈ queue.tasks, ref ∈ task.groups.map Execution.DeliveryNode.ref)
      ∧ ∀ task ∈ queue.tasks,
          ref ∈ task.groups.map Execution.DeliveryNode.ref
          → task.occurrence ∈ settled := by
  have retired := (queue.groupUnavailable_iff_retired ref).mp unavailable
  refine ⟨covered ref retired.1, ?_⟩
  intro task member contributor
  by_cases settledTask : task.occurrence ∈ settled
  · exact settledTask
  · exact False.elim
      (unavailable (accounted.groupAvailable member settledTask contributor healthy))

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
