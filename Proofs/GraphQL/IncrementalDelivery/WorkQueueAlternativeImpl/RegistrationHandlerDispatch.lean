import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationStreamReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationTaskReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedFailureProjection

/-! The actual live dispatch bridge over valid accepted generated source prefixes. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue

/-- An uninterrupted state is its exact shared kernel with the running guard. -/
theorem State.eq_queue_of_running (state : State) (running : state.stopped = false)
    : state = { queue := state.queue } := by
  cases state with
  | mk queue stopped =>
      change stopped = false at running
      subst stopped
      rfl

-----------------------------------------------------------------------------------------
-- The reader guard is invariant during a single live graph dispatch
-----------------------------------------------------------------------------------------

/-- Successful task registration/settlement never retires or reopens the graph reader. -/
theorem State.taskSuccess_stopped (state : State)
    (occurrence : WorkQueueSemantics.Occurrence) (result : ReferenceWorkQueue.TaskResult)
    (available : List (WorkQueueSemantics.Occurrence × Nat) := [])
    : (state.taskSuccess occurrence result available).1.stopped = state.stopped := by
  cases found : state.queue.taskNode? occurrence with
  | none => simp only [State.taskSuccess, found]
  | some node =>
      rw [state.taskSuccess_eq occurrence result node found available]
      dsimp only
      rw [State.drainReadyGroups_stopped _ _ available,
        State.startNewWork_stopped _ _ _ _ available]
      exact State.maybeIntegrateWork_stopped
        { state with queue := state.queue.putTaskNode { node with value := some result.value } }
        result.work (some occurrence)

/-- A stream receipt's actual item fold preserves the reader guard, including ignored input. -/
theorem State.streamItems_stopped (state : State) (stream : Execution.DeliveryNode)
    (items : List ReferenceWorkQueue.StreamItem)
    (available : List (WorkQueueSemantics.Occurrence × Nat) := [])
    : (state.streamItems stream items available).1.stopped = state.stopped := by
  have loop (items : List ReferenceWorkQueue.StreamItem) (acc : StreamRegistrationAcc)
      : (items.foldl (fun acc item => streamRegistrationStep acc item available)
          acc).1.stopped
        = acc.1.stopped := by
    induction items generalizing acc with
    | nil => rfl
    | cons item rest ih =>
        rw [List.foldl_cons, ih, streamRegistrationStep_stopped _ _ available]
  unfold State.streamItems
  split
  · rfl
  · rw [State.drainReadyGroups_stopped _ _ available]
    change (items.foldl (fun acc item => streamRegistrationStep acc item available)
      (state, [], [], [], [], [], [])).1.stopped
      = state.stopped
    exact loop items (state, [], [], [], [], [], [])

/-- Single graph dispatch only changes queue accounting and its inline observations. -/
theorem State.handleGraphEvent_stopped (state : State) (event : GraphEvent)
    (available : List (WorkQueueSemantics.Occurrence × Nat) := [])
    : (state.handleGraphEvent event available).1.stopped = state.stopped := by
  let current : State := { state with queue := state.queue.cacheTaskFailures available }
  cases event with
  | taskSuccess occurrence result =>
      exact current.taskSuccess_stopped occurrence result available
  | streamItems stream items => exact current.streamItems_stopped stream items available
  | taskFailure occurrence errors => exact current.taskFailure_stopped occurrence errors
  | groupFailure | streamSuccess | streamFailure => rfl

-----------------------------------------------------------------------------------------
-- The source contract supplies every live-handler bridge premise
-----------------------------------------------------------------------------------------

/-- Cache-aware dispatch agrees with the reference after common exposure and in both outputs.
Witness: structural queue certificates supply concrete startup/drain frames; valid source
freshness supplies only the settlement and child-freshness facts used by task success.
-/
theorem State.handleGraphEvent_cacheProjection {state : State} {work : Work}
    {parents : Nat → WorkQueueSemantics.NodeRefs}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          ReferenceWorkQueue.GroupRecordAt work node dependencies
          → dependencies = parents node.ref)
    (roots : ReferenceWorkQueue.LiveRootFrame state.queue work parents)
    (retired : state.queue.UncancelledRetiredAncestors work)
    (owners : state.queue.TaskOwnerFrame work) (children : state.queue.ChildGroupsUnique)
    (keys : state.queue.TaskNodeKeysUnique)
    (before : List GraphEvent) (event : GraphEvent)
    (accounted
      : state.queue.PendingAccounting work
          (ReferenceWorkQueue.GraphEvent.taskSettlements before))
    (valid : ReferenceWorkQueue.ValidGraphEvents work (before ++ [event]))
    (running : state.stopped = false)
    (available : List (WorkQueueSemantics.Occurrence × Nat))
    : (
        (state.handleGraphEvent event available).1.queue.cacheTaskFailures available,
        (state.handleGraphEvent event available).2.1,
        (state.handleGraphEvent event available).2.2.2
      )
      = (
        (state.queue.handleGraphEvent event available).1.cacheTaskFailures available,
        (state.queue.handleGraphEvent event available).2
      ) := by
  let current : State := { state with queue := state.queue.cacheTaskFailures available }
  have currentRoots := (roots.cacheTaskFailures retired available).1
  have currentRetired := retired.cacheTaskFailures available
  have currentOwners := owners.cacheTaskFailures available
  have currentChildren := children.cacheTaskFailures available
  have currentKeys := keys.cacheTaskFailures available
  have currentAccounting := accounted.cacheTaskFailures available
  obtain ⟨prior, matched, freshEvent⟩ := ReferenceWorkQueue.validGraphEvents_last valid
  cases event with
  | taskSuccess occurrence result =>
      cases found : current.queue.taskNode? occurrence with
      | none =>
          change ((current.taskSuccess occurrence result available).1.queue.cacheTaskFailures
              available, (current.taskSuccess occurrence result available).2.1,
              (current.taskSuccess occurrence result available).2.2.2)
            = ((current.queue.taskSuccess occurrence result available).1.cacheTaskFailures
              available, (current.queue.taskSuccess occurrence result available).2)
          simp only [State.taskSuccess, ReferenceWorkQueue.State.taskSuccess, found]
      | some node =>
          have fresh : occurrence ∉ ReferenceWorkQueue.GraphEvent.taskSettlements before := by
            intro settled
            exact freshEvent.2.2.1 occurrence List.mem_cons_self
              (ReferenceWorkQueue.GraphEvent.taskSettlements_subsetIdentities before settled)
          have known : ∀ task ∈ result.work.tasks, ReferenceWorkQueue.TaskMatches work task := by
            intro task member
            obtain ⟨address, payload, same, located⟩ := matched.childTask_producer member
            exact ⟨⟨address, payload, some occurrence, same, located⟩,
              matched.childTask_groupsExact member⟩
          have childFresh : ∀ task ∈ result.work.tasks,
              task.occurrence ∉ occurrence :: ReferenceWorkQueue.GraphEvent.taskSettlements
                before := by
            intro task member settled
            rcases List.mem_cons.mp settled with now | earlier
            · exact matched.childTasks_not_success member (List.mem_cons.mpr (.inl now))
            · exact matched.childTasks_unsettled prior freshEvent member
                (ReferenceWorkQueue.GraphEvent.taskSettlements_subsetIdentities before earlier)
          have frames := taskSuccess_startFrames generated currentAccounting.registration canonical currentRoots currentRetired
            currentOwners currentChildren occurrence result matched node found
          exact current.taskSuccess_cacheProjection generated currentRoots.present
            currentAccounting currentKeys occurrence result node found fresh known
            childFresh running available ⟨parents, frames⟩
  | streamItems stream items =>
      have known : ∀ item ∈ items,
          ∀ task ∈ item.work.tasks, ReferenceWorkQueue.TaskMatches work task := by
        intro item member task supplied
        obtain ⟨address, payload, same, located⟩ :=
          matched.streamItem_childTask_producer member supplied
        exact ⟨⟨address, payload, some item.occurrence, same, located⟩,
          matched.streamItem_childTask_groupsExact member supplied⟩
      apply current.streamItems_cacheProjection currentKeys stream items known running
        available
      · intro earlier item later partition
        have included : earlier.Subset items := by
          intro supplied member
          rw [partition]
          exact List.mem_append_left _ member
        have member : item ∈ items := by
          rw [partition]
          exact List.mem_append_right _ List.mem_cons_self
        have partialMatch : (ReferenceWorkQueue.GraphEvent.streamItems stream earlier
            ).MatchesWork work := fun item member => matched item (included member)
        have preparedRoots := (currentRoots.prepareItems currentRetired generated canonical
          partialMatch available).1
        have preparedOwners := currentOwners.prepareItems_of_registered currentRoots.registered
          currentRoots.tasks currentRoots.present generated.declarations partialMatch available
        have preparedKeys : (current.queue.preparedStreamItems earlier available
            ).TaskNodeKeysUnique := by
          apply ReferenceWorkQueue.State.preparedStreamItems_preserves
            (fun queue => queue.TaskNodeKeysUnique) currentKeys earlier available
          intro queue item _ prior
          let registered := queue.maybeIntegrateWork item.work
          exact ((prior.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork
            { registered.2 with newGroups := (registered.1.pruneEmptyGroups
              registered.2.newGroups).2 } available
        have startup := streamItem_startFrames generated canonical currentRoots currentRetired
          currentOwners currentChildren stream items matched earlier included item member available
        exact ⟨preparedRoots.present, preparedOwners.matching, preparedKeys, parents, startup⟩
      · exact ⟨parents, streamItems_drainFrames generated canonical currentRoots currentRetired
          currentOwners currentChildren stream items matched available⟩
  | taskFailure occurrence errors =>
      have forest := ReferenceWorkQueue.State.RemovalForest.of_generated generated currentChildren
        currentRoots.links currentRoots.records canonical
      have projection := current.taskFailure_projection currentOwners forest occurrence errors
      have exposed := congrArg
        (fun pair : ReferenceWorkQueue.State × List Execution.WorkQueueEvent =>
          (pair.1.cacheTaskFailures available, pair.2,
            ([] : List ReferenceWorkQueue.GroupFailureEvent))) projection
      exact exposed
  | groupFailure failure =>
      simp only [State.handleGraphEvent, ReferenceWorkQueue.State.handleGraphEvent,
        ReferenceWorkQueue.State.cacheTaskFailures, List.foldl_nil]
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, ReferenceWorkQueue.State.handleGraphEvent,
        ReferenceWorkQueue.State.cacheTaskFailures, List.foldl_nil]
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, ReferenceWorkQueue.State.handleGraphEvent,
        ReferenceWorkQueue.State.cacheTaskFailures, List.foldl_nil]

/-- Dispatch has exact residual correspondence when every available failure is already consumed.
The currently dispatched failure may supply its own occurrence. Source freshness keeps
all newly introduced child tasks outside this snapshot, so delayed activation adds no
extra rejection slot before the common startup and drain.
-/
theorem State.handleGraphEvent_projection_of_consumedAvailability {state : State}
    {work : Work} {parents : Nat → WorkQueueSemantics.NodeRefs}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          ReferenceWorkQueue.GroupRecordAt work node dependencies
          → dependencies = parents node.ref)
    (roots : ReferenceWorkQueue.LiveRootFrame state.queue work parents)
    (retired : state.queue.UncancelledRetiredAncestors work)
    (owners : state.queue.TaskOwnerFrame work) (children : state.queue.ChildGroupsUnique)
    (keys : state.queue.TaskNodeKeysUnique) (before : List GraphEvent)
    (event : GraphEvent)
    (accounted
      : state.queue.PendingAccounting work
          (ReferenceWorkQueue.GraphEvent.taskSettlements before))
    (valid : ReferenceWorkQueue.ValidGraphEvents work (before ++ [event]))
    (running : state.stopped = false)
    (available : List (WorkQueueSemantics.Occurrence × Nat))
    (consumedSnapshot
      : ∀ occurrence errors,
          (occurrence, errors) ∈ available
          → occurrence ∈ ReferenceWorkQueue.GraphEvent.taskSettlements before
            ∨ event = .taskFailure occurrence errors)
    : (
        (state.handleGraphEvent event available).1.queue,
        (state.handleGraphEvent event available).2.1,
        (state.handleGraphEvent event available).2.2.2
      )
      = state.queue.handleGraphEvent event available := by
  let current : State := { state with queue := state.queue.cacheTaskFailures available }
  have currentRoots := (roots.cacheTaskFailures retired available).1
  have currentRetired := retired.cacheTaskFailures available
  have currentOwners := owners.cacheTaskFailures available
  have currentChildren := children.cacheTaskFailures available
  have currentKeys := keys.cacheTaskFailures available
  have currentAccounting := accounted.cacheTaskFailures available
  obtain ⟨prior, matched, freshEvent⟩ := ReferenceWorkQueue.validGraphEvents_last valid
  cases event with
  | taskSuccess occurrence result =>
      cases found : current.queue.taskNode? occurrence with
      | none =>
          change ((current.taskSuccess occurrence result available).1.queue,
              (current.taskSuccess occurrence result available).2.1,
              (current.taskSuccess occurrence result available).2.2.2)
            = current.queue.taskSuccess occurrence result available
          simp only [State.taskSuccess, ReferenceWorkQueue.State.taskSuccess, found]
      | some node =>
          have fresh : occurrence ∉ ReferenceWorkQueue.GraphEvent.taskSettlements before := by
            intro settled
            exact freshEvent.2.2.1 occurrence List.mem_cons_self
              (ReferenceWorkQueue.GraphEvent.taskSettlements_subsetIdentities before settled)
          have known : ∀ task ∈ result.work.tasks, ReferenceWorkQueue.TaskMatches work task := by
            intro task member
            obtain ⟨address, payload, same, located⟩ := matched.childTask_producer member
            exact ⟨⟨address, payload, some occurrence, same, located⟩,
              matched.childTask_groupsExact member⟩
          have childFresh : ∀ task ∈ result.work.tasks,
              task.occurrence ∉ occurrence :: ReferenceWorkQueue.GraphEvent.taskSettlements
                before := by
            intro task member settled
            rcases List.mem_cons.mp settled with now | earlier
            · exact matched.childTasks_not_success member (List.mem_cons.mpr (.inl now))
            · exact matched.childTasks_unsettled prior freshEvent member
                (ReferenceWorkQueue.GraphEvent.taskSettlements_subsetIdentities before earlier)
          have frames := taskSuccess_startFrames generated currentAccounting.registration canonical currentRoots currentRetired
            currentOwners currentChildren occurrence result matched node found
          have unavailable : ∀ task ∈ result.work.tasks,
              task.occurrence ∉ available.map Prod.fst := by
            intro task member cached
            obtain ⟨⟨other, errors⟩, included, same⟩ := List.mem_map.mp cached
            rcases consumedSnapshot other errors included with consumed | impossible
            · exact childFresh task member (List.mem_cons_of_mem _ (same ▸ consumed))
            · cases impossible
          exact current.taskSuccess_projection_of_unavailableChildren generated
            currentRoots.present currentAccounting occurrence result node found fresh
            known childFresh running available unavailable ⟨parents, frames⟩
  | streamItems stream items =>
      have known : ∀ item ∈ items,
          ∀ task ∈ item.work.tasks, ReferenceWorkQueue.TaskMatches work task := by
        intro item member task supplied
        obtain ⟨address, payload, same, located⟩ :=
          matched.streamItem_childTask_producer member supplied
        exact ⟨⟨address, payload, some item.occurrence, same, located⟩,
          matched.streamItem_childTask_groupsExact member supplied⟩
      have unavailable : ∀ item ∈ items,
          ∀ task ∈ item.work.tasks, task.occurrence ∉ available.map Prod.fst := by
        intro item member task supplied cached
        obtain ⟨⟨other, errors⟩, included, same⟩ := List.mem_map.mp cached
        rcases consumedSnapshot other errors included with consumed | impossible
        · exact matched.streamItem_childTasksFresh prior freshEvent member supplied
            (ReferenceWorkQueue.GraphEvent.taskSettlements_subsetIdentities before
              (same ▸ consumed))
        · cases impossible
      apply current.streamItems_projection_of_unavailableChildren stream items known
        running available unavailable
      · intro earlier item later partition
        have included : earlier.Subset items := by
          intro supplied member
          rw [partition]
          exact List.mem_append_left _ member
        have member : item ∈ items := by
          rw [partition]
          exact List.mem_append_right _ List.mem_cons_self
        have partialMatch : (ReferenceWorkQueue.GraphEvent.streamItems stream earlier
            ).MatchesWork work := fun item member => matched item (included member)
        have preparedRoots := (currentRoots.prepareItems currentRetired generated canonical
          partialMatch available).1
        have preparedOwners := currentOwners.prepareItems_of_registered currentRoots.registered
          currentRoots.tasks currentRoots.present generated.declarations partialMatch available
        have preparedKeys : (current.queue.preparedStreamItems earlier available
            ).TaskNodeKeysUnique := by
          apply ReferenceWorkQueue.State.preparedStreamItems_preserves
            (fun queue => queue.TaskNodeKeysUnique) currentKeys earlier available
          intro queue item _ prior
          let registered := queue.maybeIntegrateWork item.work
          exact ((prior.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork
            { registered.2 with newGroups := (registered.1.pruneEmptyGroups
              registered.2.newGroups).2 } available
        have startup := streamItem_startFrames generated canonical currentRoots currentRetired
          currentOwners currentChildren stream items matched earlier included item member available
        exact ⟨preparedRoots.present, preparedOwners.matching, preparedKeys, parents, startup⟩
      · exact ⟨parents, streamItems_drainFrames generated canonical currentRoots currentRetired
          currentOwners currentChildren stream items matched available⟩
  | taskFailure occurrence errors =>
      have forest := ReferenceWorkQueue.State.RemovalForest.of_generated generated currentChildren
        currentRoots.links currentRoots.records canonical
      have projection := current.taskFailure_projection currentOwners forest occurrence errors
      have exposed := congrArg
        (fun pair : ReferenceWorkQueue.State × List Execution.WorkQueueEvent =>
          (pair.1, pair.2,
            ([] : List ReferenceWorkQueue.GroupFailureEvent))) projection
      exact exposed
  | groupFailure failure =>
      simp only [State.handleGraphEvent, ReferenceWorkQueue.State.handleGraphEvent,
        ReferenceWorkQueue.State.cacheTaskFailures, List.foldl_nil]
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, ReferenceWorkQueue.State.handleGraphEvent,
        ReferenceWorkQueue.State.cacheTaskFailures, List.foldl_nil]
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, ReferenceWorkQueue.State.handleGraphEvent,
        ReferenceWorkQueue.State.cacheTaskFailures, List.foldl_nil]

/-- Common exposed inputs produce the same actual dispatch, including inline host effects.
Witness: dispatch exposes the supplied snapshot before selecting any handler, and the
running reader guard identifies the remaining state fields exactly.
-/
theorem State.handleGraphEvent_of_cache_eq (first second : State)
    (firstRunning : first.stopped = false) (secondRunning : second.stopped = false)
    (available : List (WorkQueueSemantics.Occurrence × Nat))
    (same
      : first.queue.cacheTaskFailures available
        = second.queue.cacheTaskFailures available)
    (event : GraphEvent)
    : first.handleGraphEvent event available
      = second.handleGraphEvent event available := by
  rw [first.eq_queue_of_running firstRunning, second.eq_queue_of_running secondRunning]
  simp only [State.handleGraphEvent, same]

/-- Dispatch at an actual batch/FIFO cut preserves exposed state and both reference outputs.
Witness: batch-prefix structural frames and the consumed-source pending ledger supply the
local handler proof. The current batch's full failure snapshot is retained throughout.
-/
theorem referenceBatchPrefix_handleGraphEvent_cacheProjection {work : Work}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (earlier : List (List GraphEvent)) (batch : List GraphEvent)
    (later : List (List GraphEvent)) (fifo : List GraphEvent) (event : GraphEvent)
    (tail : List GraphEvent) (partition : batch = fifo ++ event :: tail)
    (valid : ReferenceWorkQueue.ValidGraphEvents work (earlier ++ batch :: later).flatten)
    (started : ReferenceWorkQueue.inputsStarted work (earlier ++ batch :: later) = true)
    : let available := ReferenceWorkQueue.GraphEvent.availableFailures batch
      let queue :=
        ((ReferenceWorkQueue.State.initialize
            (ReferenceWorkQueue.Work.fromExecution work)).replayBatches
          earlier).replayGraphEvents
          fifo available
      let actual := ({ queue } : State).handleGraphEvent event available
      let reference := queue.handleGraphEvent event available
      (actual.1.queue.cacheTaskFailures available, actual.2.1, actual.2.2.2)
      = (reference.1.cacheTaskFailures available, reference.2) := by
  let initial := ReferenceWorkQueue.State.initialize (ReferenceWorkQueue.Work.fromExecution work)
  let available := ReferenceWorkQueue.GraphEvent.availableFailures batch
  have validEarlier : ReferenceWorkQueue.ValidGraphEvents work earlier.flatten :=
    valid.prefix ⟨(batch :: later).flatten, by simp [List.flatten_append]⟩
  have validStep : ReferenceWorkQueue.ValidGraphEvents work
      ((earlier.flatten ++ fifo) ++ [event]) := by
    apply valid.prefix
    refine ⟨tail ++ later.flatten, ?_⟩
    simp only [List.flatten_append, List.flatten_cons, partition, List.append_assoc,
      List.cons_append, List.nil_append]
  have matchingFifo : ∀ source ∈ fifo, source.MatchesWork work := by
    intro source member
    exact (validStep.prefix ⟨[event], rfl⟩).eachMatches
      (List.mem_append_right _ member)
  obtain ⟨parents, canonical, owners, roots, retired⟩ :=
    generated.batchPrefix_structuralFrames earlier fifo
      (fun _ member => validEarlier.eachMatches member) matchingFifo available
  have accounting := generated.pendingLedger_atBatchPrefix earlier batch later fifo valid started
    ⟨event :: tail, partition.symm⟩
  have children := (ReferenceWorkQueue.createWorkQueue_childGroupsUnique
    (ReferenceWorkQueue.Work.fromExecution work)).runNormalized earlier
  have keys := (ReferenceWorkQueue.createWorkQueue_taskNodeKeysUnique
    (ReferenceWorkQueue.Work.fromExecution work)).runNormalized earlier
  rw [ReferenceWorkQueue.State.runNormalized_replayBatches] at children keys
  exact State.handleGraphEvent_cacheProjection
    (state :=
      { queue := (initial.replayBatches earlier).replayGraphEvents fifo available })
    generated canonical roots retired owners (children.replayGraphEvents fifo available)
    (keys.replayGraphEvents fifo available) (earlier.flatten ++ fifo) event accounting
    validStep rfl available

/-- The last FIFO input gives exact residual correspondence at an actual batch boundary.
Witness: every failure in the fixed snapshot belongs to the consumed prefix or this last
input. Source freshness therefore excludes it from fresh child work.
-/
theorem referenceBatchLast_handleGraphEvent_projection {work : Work}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (earlier : List (List GraphEvent)) (batch : List GraphEvent)
    (later : List (List GraphEvent)) (fifo : List GraphEvent) (event : GraphEvent)
    (partition : batch = fifo ++ [event])
    (valid : ReferenceWorkQueue.ValidGraphEvents work (earlier ++ batch :: later).flatten)
    (started : ReferenceWorkQueue.inputsStarted work (earlier ++ batch :: later) = true)
    : let available := ReferenceWorkQueue.GraphEvent.availableFailures batch
      let queue :=
        ((ReferenceWorkQueue.State.initialize
            (ReferenceWorkQueue.Work.fromExecution work)).replayBatches
          earlier).replayGraphEvents
          fifo available
      let actual := ({ queue } : State).handleGraphEvent event available
      let reference := queue.handleGraphEvent event available
      (actual.1.queue, actual.2.1, actual.2.2.2) = reference := by
  let initial := ReferenceWorkQueue.State.initialize (ReferenceWorkQueue.Work.fromExecution work)
  let available := ReferenceWorkQueue.GraphEvent.availableFailures batch
  have validEarlier : ReferenceWorkQueue.ValidGraphEvents work earlier.flatten :=
    valid.prefix ⟨(batch :: later).flatten, by simp [List.flatten_append]⟩
  have validStep : ReferenceWorkQueue.ValidGraphEvents work
      ((earlier.flatten ++ fifo) ++ [event]) := by
    apply valid.prefix
    refine ⟨later.flatten, ?_⟩
    simp only [List.flatten_append, List.flatten_cons, partition, List.append_assoc,
      List.singleton_append]
  have matchingFifo : ∀ source ∈ fifo, source.MatchesWork work := by
    intro source member
    exact (validStep.prefix ⟨[event], rfl⟩).eachMatches
      (List.mem_append_right _ member)
  obtain ⟨parents, canonical, owners, roots, retired⟩ :=
    generated.batchPrefix_structuralFrames earlier fifo
      (fun _ member => validEarlier.eachMatches member) matchingFifo available
  have accounting := generated.pendingLedger_atBatchPrefix earlier batch later fifo valid started
    ⟨[event], partition.symm⟩
  have children := (ReferenceWorkQueue.createWorkQueue_childGroupsUnique
    (ReferenceWorkQueue.Work.fromExecution work)).runNormalized earlier
  have keys := (ReferenceWorkQueue.createWorkQueue_taskNodeKeysUnique
    (ReferenceWorkQueue.Work.fromExecution work)).runNormalized earlier
  rw [ReferenceWorkQueue.State.runNormalized_replayBatches] at children keys
  apply State.handleGraphEvent_projection_of_consumedAvailability
    (state :=
      { queue := (initial.replayBatches earlier).replayGraphEvents fifo available })
    generated canonical roots retired owners (children.replayGraphEvents fifo available)
    (keys.replayGraphEvents fifo available) (earlier.flatten ++ fifo) event accounting
    validStep rfl available
  intro occurrence errors cached
  obtain ⟨failure, member, outcome⟩ := List.mem_filterMap.mp cached
  cases failure <;> simp only [Option.some.injEq, reduceCtorEq, Prod.mk.injEq] at outcome
  obtain ⟨rfl, rfl⟩ := outcome
  rw [partition, List.mem_append, List.mem_singleton] at member
  rcases member with consumed | same
  · left
    apply ReferenceWorkQueue.GraphEvent.mem_taskSettlements.mpr
    right
    apply List.mem_reverse.mpr
    exact List.mem_flatMap.mpr ⟨.taskFailure _ _,
      List.mem_append_right _ consumed, List.mem_cons_self⟩
  · exact Or.inr same.symm

/-- Actual graph dispatch equals the reference accounting/events at every valid accepted prefix.
Witness: task success uses the derived all-owner debt, stream receipts use generated phase
frames, and the other handlers are shared literally. Inline host effects remain distinct.
-/
theorem referencePrefix_handleGraphEvent {work : Work}
    (generated : ReferenceWorkQueue.ExecutedWork work) (events : List GraphEvent)
    (event : GraphEvent)
    (valid : ReferenceWorkQueue.ValidGraphEvents work (events ++ [event]))
    (accepted
      : ReferenceWorkQueue.State.eventsStarted []
          (ReferenceWorkQueue.State.initialize
            (ReferenceWorkQueue.Work.fromExecution work)) events
        = true)
    : let queue :=
        (ReferenceWorkQueue.State.initialize
          (ReferenceWorkQueue.Work.fromExecution work)).replayGraphEvents
          events
      let alternative := ({ queue } : State).handleGraphEvent event
      (alternative.1.queue, alternative.2.1, alternative.2.2.2)
      = queue.handleGraphEvent event := by
  cases event with
  | taskSuccess occurrence result =>
      exact referencePrefix_taskSuccess generated events occurrence result valid accepted
  | streamItems stream items =>
      obtain ⟨prior, matched, _⟩ := ReferenceWorkQueue.validGraphEvents_last valid
      exact referencePrefix_streamItems generated events
        (fun event member => prior.eachMatches member)
        prior accepted stream items matched
  | taskFailure occurrence errors =>
      obtain ⟨prior, _, _⟩ := ReferenceWorkQueue.validGraphEvents_last valid
      obtain ⟨parents, forest⟩ := referencePrefix_removalForest generated events
        (fun _ member => prior.eachMatches member)
      have projected := State.taskFailure_projection
        (state := { queue := (ReferenceWorkQueue.State.initialize
          (ReferenceWorkQueue.Work.fromExecution work)).replayGraphEvents events })
        (generated.replayGraphEvents_taskOwnerFrame_of_matching events
          (fun _ member => prior.eachMatches member)) forest occurrence errors
      exact congrArg (fun pair : ReferenceWorkQueue.State × List Execution.WorkQueueEvent =>
        (pair.1, pair.2, [])) projected
  | groupFailure failure =>
      simp only [State.handleGraphEvent, ReferenceWorkQueue.State.handleGraphEvent,
        ReferenceWorkQueue.State.cacheTaskFailures, List.foldl_nil]
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, ReferenceWorkQueue.State.handleGraphEvent,
        ReferenceWorkQueue.State.cacheTaskFailures, List.foldl_nil]
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, ReferenceWorkQueue.State.handleGraphEvent,
        ReferenceWorkQueue.State.cacheTaskFailures, List.foldl_nil]

end GraphQL.IncrementalDelivery.AlternativeWorkQueue
