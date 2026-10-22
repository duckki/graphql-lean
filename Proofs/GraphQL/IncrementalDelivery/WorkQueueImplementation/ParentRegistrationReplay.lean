import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ParentRegistration
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamPreparation

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
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (certified : DeclarationCoverage.Certified [] work)
    : (State.initialize (Work.fromExecution work)).ParentRegistryClosed parents := by
  have empty : ({} : State).ParentRegistryClosed parents := by
    intro ref member
    cases member
  have closure := empty.maybeIntegrateWork (by intro node member; cases member)
    (Work.fromExecution work)
    (fun _ member => workFromSpec_groups_parentCanonical_root canonical member)
    (workFromSpec_parentsCovered work certified)
  have registered := State.maybeIntegrateWork_registration
    (queue := {}) (by intro node member; cases member)
    (by intro task member; cases member) (Work.fromExecution work)
    (by
      intro task member ref contributor
      exact Or.inr (workFromSpec_immediateGroupsCoverTasks work [] certified
        task member ref contributor))
  have pruned := State.pruneEmptyGroups_registration registered.1 registered.2.1
    (({} : State).maybeIntegrateWork (Work.fromExecution work)).2.newGroups
  exact (closure.of_sameRegistry pruned.2.2).of_sameRegistry
    (State.startNewWork_registeredGroups _ _ [])

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
    (available : List (Occurrence × Nat) := [])
    : (queue.drainReadyGroups available).1.ParentRegistryClosed parents :=
  prior.of_sameRegistry (queue.drainReadyGroups_registration live tasks available).2.2

-----------------------------------------------------------------------------------------
-- Successful settlements introduce complete child chains before publishing
-----------------------------------------------------------------------------------------

/-- Matched object success preserves parent-registry closure across the single-pass fold.
Witness: child lowering registers complete chains; each contributor step retains that
registry, as do final activation and draining. No health or admission premise is used.
-/
theorem State.ParentRegistryClosed.taskSuccess {queue : State} {work parents}
    (prior : queue.ParentRegistryClosed parents) (live : queue.LiveGroupsRegistered)
    (tasks : queue.TaskGroupsRegistered)
    (frame : queue.RegistrationFrame work) (occurrence : Occurrence) (result : TaskResult)
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (available : List (Occurrence × Nat) := [])
    : (queue.taskSuccess occurrence result available).1.ParentRegistryClosed parents := by
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
      rw [queue.taskSuccess_eq occurrence result node found available]
      let stored := queue.putTaskNode { node with value := some result.value }
      have storedPrior : stored.ParentRegistryClosed parents := prior
      have producerRegistered := frame.started node (List.mem_of_find?_eq_some found)
      have same : node.task.occurrence = occurrence :=
        (occurrence_beq_iff_eq _ _).mp (List.find?_some
          (p := fun candidate : TaskNode => candidate.task.occurrence == occurrence) found)
      have certificate := (frame.children node.task producerRegistered).sourceChild same matching
      have registered := stored.maybeIntegrateWork_registration live tasks result.work
        certificate.contributors (some occurrence)
      have integrated := storedPrior.maybeIntegrateWork live result.work
        (fun _ member => matching.taskChildGroups_parentCanonical canonical member)
        certificate.parents (some occurrence)
      have folded := loop node.task.groups (_, [], {})
        ⟨registered.1, registered.2.1, integrated⟩
      let finished := node.task.groups.foldl successGroupStep
        ((stored.maybeIntegrateWork result.work (some occurrence)).1, [], {})
      have started := State.startNewWork_registration folded.1 folded.2.1 finished.2.2 available
      exact (folded.2.2.of_sameRegistry
        (State.startNewWork_registeredGroups _ finished.2.2 available)
        ).drainReadyGroups started.1 started.2 available

/-- Each matched stream item preserves the parent-closed registry before the final drain.
Witness: child registration covers all parents; taskless pruning and activation retain it.
-/
theorem State.ParentRegistryClosed.integrateStreamItem {queue : State} {work parents}
    (prior : queue.ParentRegistryClosed parents) (live : queue.LiveGroupsRegistered)
    (tasks : queue.TaskGroupsRegistered)
    (frame : queue.RegistrationFrame work) {stream items}
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    {item : StreamItem} (member : item ∈ items)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (available : List (Occurrence × Nat) := [])
    : (queue.integrateStreamItem item available).ParentRegistryClosed parents := by
  have certificate := frame.source.sourceStreamItem matching member queue.registeredGroups
  have registered := queue.maybeIntegrateWork_registration live tasks item.work
    certificate.contributors
  have integrated := prior.maybeIntegrateWork live item.work
    (fun _ group => matching.streamItem_childGroups_parentCanonical canonical member group)
    certificate.parents
  have pruned := State.pruneEmptyGroups_registration registered.1 registered.2.1
    (queue.maybeIntegrateWork item.work).2.newGroups
  exact (integrated.of_sameRegistry pruned.2.2).of_sameRegistry
    (State.startNewWork_registeredGroups _ _ available)

/-- Any matched stream-item batch preserves primary-parent registry closure.
Witness: thread the actual item-integration states and retain closure through draining.
-/
theorem State.ParentRegistryClosed.streamItems {queue : State} {work parents}
    (prior : queue.ParentRegistryClosed parents) (_live : queue.LiveGroupsRegistered)
    (_tasks : queue.TaskGroupsRegistered)
    (frame : queue.RegistrationFrame work) (stream : Execution.DeliveryNode)
    (items : List StreamItem)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (available : List (Occurrence × Nat) := [])
    : (queue.streamItems stream items available).1.ParentRegistryClosed parents := by
  rw [queue.streamItems_eq stream items available]
  split
  · exact prior
  · let property (current : State) :=
      current.RegistrationFrame work ∧ current.ParentRegistryClosed parents
    have step (current : State) (item : StreamItem) (member : item ∈ items)
        (invariant : property current) : property (current.integrateStreamItem item available) :=
      ⟨(invariant.1.integrateStreamItem matching member available).1,
        invariant.2.integrateStreamItem invariant.1.live invariant.1.tasks invariant.1
          matching member canonical available⟩
    have final := State.preparedStreamItems_preserves property ⟨frame, prior⟩ items available step
    exact final.2.drainReadyGroups final.1.live final.1.tasks available

-----------------------------------------------------------------------------------------
-- The actual event and normalized-batch boundaries
-----------------------------------------------------------------------------------------

/-- Matched event processing preserves the parent-closed registry for every event kind.
Witness: successful events integrate complete chains; failure and stream closure retain
the old registry, including ignored-event branches.
-/
theorem State.ParentRegistryClosed.handleGraphEvent {queue : State} {work parents}
    (prior : queue.ParentRegistryClosed parents) (live : queue.LiveGroupsRegistered)
    (tasks : queue.TaskGroupsRegistered)
    (frame : queue.RegistrationFrame work) (event : GraphEvent)
    (matching : event.MatchesWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (available : List (Occurrence × Nat) := [])
    : (queue.handleGraphEvent event available).1.ParentRegistryClosed parents := by
  have cached := prior.of_sameRegistry (queue.cacheTaskFailures_registeredGroups available)
  have registration := queue.cacheTaskFailures_registration live tasks available
  cases event with
  | taskSuccess occurrence result =>
      exact cached.taskSuccess registration.1 registration.2 (frame.cacheTaskFailures available) occurrence result matching canonical
        available
  | taskFailure occurrence errors =>
      exact cached.of_sameRegistry
        ((queue.cacheTaskFailures available).taskFailure_registration
          registration.1 registration.2 occurrence errors).2.2
  | streamItems stream items =>
      exact cached.streamItems registration.1 registration.2 (frame.cacheTaskFailures available) stream items matching canonical
        available
  | streamSuccess stream =>
      change ((queue.cacheTaskFailures available).streamSuccess
        stream).1.ParentRegistryClosed parents
      unfold State.streamSuccess
      split <;> exact cached
  | streamFailure stream errors =>
      change ((queue.cacheTaskFailures available).streamFailure
        stream errors).1.ParentRegistryClosed parents
      unfold State.streamFailure
      split <;> exact cached

  | groupFailure notice =>
      change ((queue.cacheTaskFailures available).groupFailure notice).1.ParentRegistryClosed parents
      unfold State.groupFailure
      split
      · exact cached
      · split <;> exact cached

/-- Matched host batches preserve closure while keeping all live/task refs registered.
Witness: fold over actual handler states and preserve the final done-flag update.
-/
theorem State.ParentRegistryClosed.handleGraphEvents {queue : State} {work parents}
    (prior : queue.ParentRegistryClosed parents) (_live : queue.LiveGroupsRegistered)
    (_tasks : queue.TaskGroupsRegistered)
    (frame : queue.RegistrationFrame work) (events : List GraphEvent)
    (matching : ∀ event ∈ events, event.MatchesWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    : (queue.handleGraphEvents events).1.ParentRegistryClosed parents := by
  let available := GraphEvent.availableFailures events
  have loop (more : List GraphEvent) (included : more.Subset events)
      (current : State) (registered : current.RegistrationFrame work)
      (closed : current.ParentRegistryClosed parents)
      : (current.replayGraphEvents more available).ParentRegistryClosed parents := by
    induction more generalizing current with
    | nil => exact closed
    | cons event rest ih =>
        have source := matching event (included List.mem_cons_self)
        have handled := closed.handleGraphEvent registered.live registered.tasks registered
          event source canonical available
        have next : (current.dispatchGraphEvent event available).1.ParentRegistryClosed parents := handled
        exact ih (fun _ member => included (List.mem_cons_of_mem _ member))
          (current.dispatchGraphEvent event available).1
          (registered.dispatchGraphEvent event source available).1 next
  cases running : queue.terminated with
  | true => simpa only [State.handleGraphEvents, running, ↓reduceIte] using prior
  | false =>
      obtain ⟨terminal, same⟩ := queue.handleGraphEvents_stateCore events running
      rw [same]
      exact loop events (fun _ member => member) queue frame prior

/-- Parent registry closure survives every supplied normalized replay prefix.
Witness: fold over matched batches; publisher state and batching do not affect the registry.
-/
theorem State.ParentRegistryClosed.runNormalized {queue : State} {work parents}
    (prior : queue.ParentRegistryClosed parents) (live : queue.LiveGroupsRegistered)
    (tasks : queue.TaskGroupsRegistered)
    (frame : queue.RegistrationFrame work) (batches : List (List GraphEvent))
    (matching : ∀ batch ∈ batches, ∀ event ∈ batch, event.MatchesWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    : (queue.runNormalized batches).1.ParentRegistryClosed parents := by
  rw [State.runNormalized_replayBatches]
  induction batches generalizing queue with
  | nil => exact prior
  | cons batch rest ih =>
      have matched := matching batch List.mem_cons_self
      exact ih
        (prior.handleGraphEvents live tasks frame batch matched canonical)
        (frame.handleGraphEvents batch matched).1.live
        (frame.handleGraphEvents batch matched).1.tasks
        (frame.handleGraphEvents batch matched).1
        (fun more member => matching more (List.mem_cons_of_mem _ member))

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
  have initial := createWorkQueue_registration work generated.declarations
  have registered := createWorkQueue_runNormalized_registration valid generated.declarations
  have closure := (createWorkQueue_parentRegistryClosed canonical generated.declarations).runNormalized
    initial.1 initial.2 (State.initialize_registrationFrame generated.declarations) batches matched canonical
  have parentFields := (createWorkQueue_groupParentsCanonical (Work.fromExecution work) parents
    (fun _ member => workFromSpec_groups_parentCanonical_root canonical member)
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
