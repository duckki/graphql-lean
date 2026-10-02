import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ParentRegistration

/-! Parent-closed permanent registration throughout actual matched replay. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Initialization and registry-neutral transitions
-----------------------------------------------------------------------------------------

/-- Initialization permanently registers each lowered group's assigned parent.
Witness: full-chain candidate coverage, followed by registry-neutral pruning and start.
-/
theorem createWorkQueue_parentRegistryClosed {work : Execution.Work} {parents}
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    : (State.initialize (Work.fromExecution work)).ParentRegistryClosed parents := by
  have empty : ({} : State).ParentRegistryClosed parents := by
    intro key member
    cases member
  have closure := empty.maybeIntegrateWork (by intro node member; cases member)
    (Work.fromExecution work)
    (fun _ member => workFromSpec_groups_parentCanonical Located.root canonical member)
    (workFromSpec_parentsCovered work)
  have registered := State.maybeIntegrateWork_registration
    (queue := {}) (by intro node member; cases member)
    (by intro task member; cases member) (Work.fromExecution work)
    (workFromSpec_immediateGroupsCoverTasks work [])
  have pruned := State.pruneEmptyGroups_registration registered.1 registered.2.1
    (({} : State).maybeIntegrateWork (Work.fromExecution work)).2.newGroups
  exact (closure.of_sameRegistry pruned.2.2).of_sameRegistry
    (State.startNewWork_registeredGroups _ _)

/-- Successful closure preserves parent-registry closure despite retiring live shells.
Witness: flushing and pruning retain the exact permanent registry.
-/
theorem State.ParentRegistryClosed.finishGroupSuccess {queue : State} {parents}
    (prior : queue.ParentRegistryClosed parents) (live : queue.LiveGroupsRegistered)
    (tasks : queue.TaskGroupsRegistered) (group : GroupNode)
    : (queue.finishGroupSuccess group).1.ParentRegistryClosed parents :=
  prior.of_sameRegistry (queue.finishGroupSuccess_registration live tasks group).2.2

/-- The recursive drain preserves parent-registry closure through either outcome.
Witness: the existing registry-equality theorem covers closure, promotion, and activation.
-/
theorem State.ParentRegistryClosed.drainReadyGroups {queue : State} {parents}
    (prior : queue.ParentRegistryClosed parents) (live : queue.LiveGroupsRegistered)
    (tasks : queue.TaskGroupsRegistered)
    : queue.drainReadyGroups.1.ParentRegistryClosed parents :=
  prior.of_sameRegistry (queue.drainReadyGroups_registration live tasks).2.2

-----------------------------------------------------------------------------------------
-- Successful settlements introduce complete child chains before publishing
-----------------------------------------------------------------------------------------

/-- Matched object success preserves parent-registry closure across the single-pass fold.
Witness: child lowering registers complete chains; each contributor step retains that
registry, as do final activation and draining. No health or admission premise is used.
-/
theorem State.ParentRegistryClosed.taskSuccess {queue : State} {work parents}
    (prior : queue.ParentRegistryClosed parents) (live : queue.LiveGroupsRegistered)
    (tasks : queue.TaskGroupsRegistered) (occurrence : Occurrence) (result : TaskResult)
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    : (queue.taskSuccess occurrence result).1.ParentRegistryClosed parents := by
  let property (current : State) := current.LiveGroupsRegistered
    ∧ current.TaskGroupsRegistered ∧ current.ParentRegistryClosed parents
  have step (acc : State × List WorkQueueEvent × NewWork) (group : Execution.DeliveryNode)
      (invariant : property acc.1) : property (successGroupStep acc group).1 := by
    obtain ⟨current, events, released⟩ := acc
    dsimp only [successGroupStep]
    split
    · exact invariant
    · rename_i node found
      have updated : property (current.putGroupNode
          { node with pending := node.pending - 1 }) :=
        ⟨invariant.1.putGroupNode _
          (invariant.1 node (List.mem_of_find?_eq_some found)), invariant.2⟩
      split
      · have registered := State.finishGroupSuccess_registration updated.1 updated.2.1
          { node with pending := node.pending - 1 }
        exact ⟨registered.1, registered.2.1,
          updated.2.2.of_sameRegistry registered.2.2⟩
      · exact updated
  have loop (groups : List Execution.DeliveryNode)
      (acc : State × List WorkQueueEvent × NewWork) (invariant : property acc.1)
      : property (groups.foldl successGroupStep acc).1 := by
    induction groups generalizing acc with
    | nil => exact invariant
    | cons group rest ih => exact ih _ (step acc group invariant)
  cases found : queue.taskNode? occurrence with
  | none => simpa [State.taskSuccess, found] using prior
  | some node =>
      rw [queue.taskSuccess_eq occurrence result node found]
      split
      · exact prior
      · let stored := queue.putTaskNode { node with value := some result.value }
        have storedPrior : stored.ParentRegistryClosed parents := prior
        have registered := stored.maybeIntegrateWork_registration live tasks result.work
          matching.childTasksCovered (some occurrence)
        have integrated := storedPrior.maybeIntegrateWork live result.work
          (fun _ member => matching.taskChildGroups_parentCanonical canonical member)
          matching.childParentsCovered (some occurrence)
        have folded := loop node.task.groups (_, [], {})
          ⟨registered.1, registered.2.1, integrated⟩
        let finished := node.task.groups.foldl successGroupStep
          ((stored.maybeIntegrateWork result.work (some occurrence)).1, [], {})
        have started := State.startNewWork_registration folded.1 folded.2.1 finished.2.2
        exact (folded.2.2.of_sameRegistry
          (State.startNewWork_registeredGroups _ finished.2.2)
          ).drainReadyGroups started.1 started.2

/-- Each matched stream item preserves the parent-closed registry before the final drain.
Witness: child registration covers all parents; taskless pruning and activation retain it.
-/
theorem State.ParentRegistryClosed.integrateStreamItem {queue : State} {work parents}
    (prior : queue.ParentRegistryClosed parents) (live : queue.LiveGroupsRegistered)
    (tasks : queue.TaskGroupsRegistered) {stream items}
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    {item : StreamItem} (member : item ∈ items)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    : (queue.integrateStreamItem item).ParentRegistryClosed parents := by
  have registered := queue.maybeIntegrateWork_registration live tasks item.work
    (matching.streamItem_childTasksCovered member)
  have integrated := prior.maybeIntegrateWork live item.work
    (fun _ group => matching.streamItem_childGroups_parentCanonical canonical member group)
    (matching.streamItem_parentsCovered member)
  have pruned := State.pruneEmptyGroups_registration registered.1 registered.2.1
    (queue.maybeIntegrateWork item.work).2.newGroups
  exact (integrated.of_sameRegistry pruned.2.2).of_sameRegistry
    (State.startNewWork_registeredGroups _ _)

/-- Any matched stream-item batch preserves primary-parent registry closure.
Witness: thread the actual item-integration states and retain closure through draining.
-/
theorem State.ParentRegistryClosed.streamItems {queue : State} {work parents}
    (prior : queue.ParentRegistryClosed parents) (live : queue.LiveGroupsRegistered)
    (tasks : queue.TaskGroupsRegistered) (stream : Execution.DeliveryNode)
    (items : List StreamItem)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    : (queue.streamItems stream items).1.ParentRegistryClosed parents := by
  let step (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue) (item : StreamItem) :=
    let (current, groups, streams, values) := acc
    let (integrated, released) := current.maybeIntegrateWork item.work
    let (pruned, nonempty) := integrated.pruneEmptyGroups released.newGroups
    (pruned.startNewWork { released with newGroups := nonempty },
      groups ++ nonempty, streams ++ released.newStreams, values ++ [item.value])
  let property (current : State) := current.LiveGroupsRegistered
    ∧ current.TaskGroupsRegistered ∧ current.ParentRegistryClosed parents
  have loop (more : List StreamItem) (included : more.Subset items)
      (acc : State × List Execution.DeliveryNode
        × List Execution.DeliveryNode × List StreamItemValue)
      (invariant : property acc.1) : property (more.foldl step acc).1 := by
    induction more generalizing acc with
    | nil => exact invariant
    | cons item rest ih =>
        have member := included List.mem_cons_self
        have registered := acc.1.integrateStreamItem_registration
          invariant.1 invariant.2.1 matching member
        have closure := invariant.2.2.integrateStreamItem invariant.1 invariant.2.1
          matching member canonical
        exact ih (fun _ inRest => included (List.mem_cons_of_mem _ inRest)) _
          ⟨registered.1, registered.2.1, closure⟩
  unfold State.streamItems
  split
  · exact prior
  · have final := loop items (fun _ member => member) (queue, [], [], [])
      ⟨live, tasks, prior⟩
    exact final.2.2.drainReadyGroups final.1 final.2.1

-----------------------------------------------------------------------------------------
-- The actual event and normalized-batch boundaries
-----------------------------------------------------------------------------------------

/-- Matched event processing preserves the parent-closed registry for every event kind.
Witness: successful events integrate complete chains; failure and stream closure retain
the old registry, including ignored-event branches.
-/
theorem State.ParentRegistryClosed.handleGraphEvent {queue : State} {work parents}
    (prior : queue.ParentRegistryClosed parents) (live : queue.LiveGroupsRegistered)
    (tasks : queue.TaskGroupsRegistered) (event : GraphEvent)
    (matching : event.MatchesWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    : (queue.handleGraphEvent event).1.ParentRegistryClosed parents := by
  cases event with
  | taskSuccess occurrence result =>
      exact prior.taskSuccess live tasks occurrence result matching canonical
  | taskFailure occurrence errors =>
      exact prior.of_sameRegistry
        (queue.taskFailure_registration live tasks occurrence errors).2.2
  | streamItems stream items =>
      exact prior.streamItems live tasks stream items matching canonical
  | streamSuccess stream =>
      change (queue.streamSuccess stream).1.ParentRegistryClosed parents
      unfold State.streamSuccess
      split <;> exact prior
  | streamFailure stream errors =>
      change (queue.streamFailure stream errors).1.ParentRegistryClosed parents
      unfold State.streamFailure
      split <;> exact prior

/-- Matched host batches preserve closure while keeping all live/task keys registered.
Witness: fold over actual handler states and preserve the final done-flag update.
-/
theorem State.ParentRegistryClosed.handleGraphEvents {queue : State} {work parents}
    (prior : queue.ParentRegistryClosed parents) (live : queue.LiveGroupsRegistered)
    (tasks : queue.TaskGroupsRegistered) (events : List GraphEvent)
    (matching : ∀ event ∈ events, event.MatchesWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    : (queue.handleGraphEvents events).1.ParentRegistryClosed parents := by
  let step (acc : State × List WorkQueueEvent) (event : GraphEvent) :=
    let (current, outputs) := acc
    let (next, produced) := current.handleGraphEvent event
    (next, outputs ++ produced)
  let property (current : State) := current.LiveGroupsRegistered
    ∧ current.TaskGroupsRegistered ∧ current.ParentRegistryClosed parents
  have loop (more : List GraphEvent) (included : more.Subset events)
      (acc : State × List WorkQueueEvent) (invariant : property acc.1)
      : property (more.foldl step acc).1 := by
    induction more generalizing acc with
    | nil => exact invariant
    | cons event rest ih =>
        have matched := matching event (included List.mem_cons_self)
        have registered := acc.1.handleGraphEvent_registration invariant.1 invariant.2.1
          event matched
        exact ih (fun _ member => included (List.mem_cons_of_mem _ member)) _
          ⟨registered.1, registered.2.1,
            invariant.2.2.handleGraphEvent invariant.1 invariant.2.1 event matched canonical⟩
  unfold State.handleGraphEvents
  split
  · exact prior
  · have final := (loop events (fun _ member => member) (queue, []) ⟨live, tasks, prior⟩).2.2
    dsimp only
    split <;> exact final

/-- Parent registry closure survives every supplied normalized replay prefix.
Witness: fold over matched batches; publisher state and batching do not affect the registry.
-/
theorem State.ParentRegistryClosed.runNormalized {queue : State} {work parents}
    (prior : queue.ParentRegistryClosed parents) (live : queue.LiveGroupsRegistered)
    (tasks : queue.TaskGroupsRegistered) (batches : List (List GraphEvent))
    (matching : ∀ batch ∈ batches, ∀ event ∈ batch, event.MatchesWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    : (queue.runNormalized batches).1.ParentRegistryClosed parents := by
  let property (current : State) := current.LiveGroupsRegistered
    ∧ current.TaskGroupsRegistered ∧ current.ParentRegistryClosed parents
  have step (acc : NormalizedAcc) (batch : List GraphEvent)
      (matched : ∀ event ∈ batch, event.MatchesWork work) (invariant : property acc.1)
      : property (normalizedStep acc batch).1 := by
    have registered := acc.1.handleGraphEvents_registration invariant.1 invariant.2.1
      batch matched
    have closure := invariant.2.2.handleGraphEvents invariant.1 invariant.2.1 batch
      matched canonical
    unfold normalizedStep
    dsimp only
    split <;> exact ⟨registered.1, registered.2.1, closure⟩
  have loop (more : List (List GraphEvent)) (included : more.Subset batches)
      (acc : NormalizedAcc) (invariant : property acc.1)
      : property (more.foldl normalizedStep acc).1 := by
    induction more generalizing acc with
    | nil => exact invariant
    | cons batch rest ih =>
        exact ih (fun _ member => included (List.mem_cons_of_mem _ member)) _
          (step acc batch (matching batch (included List.mem_cons_self)) invariant)
  exact (loop batches (fun _ member => member)
    (queue, { active := queue.initialGroups ++ queue.initialStreams }, [])
    ⟨live, tasks, prior⟩).2.2

/-- Every generated valid replay has permanently registered parents for its live groups.
Witness: canonical full-chain lowering, registry closure throughout replay, and the live
descriptor's canonical parent. An absent parent was registered, rather than never seen.
-/
theorem ExecutedWork.runNormalized_parentsRegistered {work : Execution.Work}
    (generated : ExecutedWork work) {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten)
    : let queue := ((State.initialize (Work.fromExecution work)).runNormalized batches).1
      ∀ node ∈ queue.groupNodes,
        ∀ parent, node.group.parent = some parent → parent ∈ queue.registeredGroups := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have matched : ∀ batch ∈ batches, ∀ event ∈ batch, event.MatchesWork work :=
    fun _ batch _ event => valid.eachMatches (List.mem_flatten.mpr ⟨_, batch, event⟩)
  have initial := createWorkQueue_registration work
  have registered := createWorkQueue_runNormalized_registration valid
  have closure := (createWorkQueue_parentRegistryClosed canonical).runNormalized
    initial.1 initial.2 batches matched canonical
  have parentFields := (createWorkQueue_groupParentsCanonical (Work.fromExecution work) parents
    (fun _ member => workFromSpec_groups_parentCanonical Located.root canonical member)
    ).runNormalized batches matched canonical
  dsimp only
  intro node member parent parentEq
  exact closure.parent_registered registered.1 parentFields member parentEq

/-- An absent primary parent in generated replay is a permanently retired group.
Witness: replay registers every live record's parent, and missing lookup supplies absence.
This does not yet assert that the parent's task-bearing ancestors have retired.
-/
theorem ExecutedWork.runNormalized_missingParentRetired {work : Execution.Work}
    (generated : ExecutedWork work) {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten)
    : let queue := ((State.initialize (Work.fromExecution work)).runNormalized batches).1
      ∀ node ∈ queue.groupNodes,
        ∀ parent,
          node.group.parent = some parent
          → queue.groupNode? parent = none
          → queue.RetiredGroup parent := by
  dsimp only
  intro node member parent parentEq missing
  exact .of_lookup_none
    (generated.runNormalized_parentsRegistered valid node member parent parentEq) missing

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
