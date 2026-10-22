import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.OwnerReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.UncancelledRetirementReplay

/-! Close healthy-owner replay's contributor-availability obligation using retirement. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Generated started replay retains healthy owner accounting without an availability
callback. Witness: induction over actual source settlements; the already-proved structural
retirement invariant licenses object-child registration, and stream-region separation
licenses item-child registration. Accounting uses the full source failure ledger here,
not the smaller accepted-failure inventory needed by guard reflection.
-/
theorem ExecutedWork.replayGraphEvents_ownerAccounting_of_eachAccepted
    {work : Execution.Work} (generated : ExecutedWork work) {parents}
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    {events : List GraphEvent} (valid : ValidGraphEvents work events)
    (acceptedAt
      : ∀ before event,
          (before ++ [event]).IsPrefix events
          → ((State.initialize (Work.fromExecution work)).replayGraphEvents
              before).acceptsGraphEvent
              event
            = true)
    : ((State.initialize (Work.fromExecution work)).replayGraphEvents
        events).OwnerAccounting
        work parents events := by
  induction valid with
  | nil =>
      exact createWorkQueue_ownerAccounting work parents canonical generated
  | @append before event valid matching fresh ready ih =>
      have included := List.prefix_append before [event]
      have earlier := ih (fun past next prefixOfBefore =>
        acceptedAt past next (prefixOfBefore.trans included))
      have accepted := acceptedAt before event (List.prefix_refl _)
      have retirement := (generated.replayGraphEvents_healthyRetiredAncestors before valid
        ).mono_failures
          ((State.initialize (Work.fromExecution work)).objectFailureContributions_sublist
            before).subset
      have available : ((State.initialize (Work.fromExecution work)).replayGraphEvents
          before).RegistrationsAvailable work (GraphEvent.failureSettlements before) event := by
        cases event with
        | taskSuccess occurrence result =>
            exact earlier.taskSuccess_available generated retirement matching fresh accepted
        | streamItems stream items =>
            exact createWorkQueue_replay_streamRegistrationsAvailableAt generated
              (.append valid matching fresh ready) before stream items (List.prefix_refl _)
        | taskFailure | streamSuccess | streamFailure | groupFailure => trivial
      rw [State.replayGraphEvents_append]
      exact earlier.dispatchGraphEvent canonical generated valid event matching fresh
        accepted available

/-- A valid accepted source history has the full owner ledger at its actual final state.
Witness: the executable start checker supplies eventwise acceptance; retirement closes
all registration-availability obligations inside the induction.
-/
theorem ExecutedWork.replayGraphEvents_ownerAccounting_of_started
    {work : Execution.Work} (generated : ExecutedWork work) (events : List GraphEvent)
    (valid : ValidGraphEvents work events)
    (started
      : State.eventsStarted [] (State.initialize (Work.fromExecution work)) events = true)
    : ∃ parents : Nat → NodeRefs,
        (∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
        ∧ ((State.initialize (Work.fromExecution work)).replayGraphEvents
            events).OwnerAccounting
            work parents events := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  refine ⟨parents, canonical,
    generated.replayGraphEvents_ownerAccounting_of_eachAccepted canonical valid ?_⟩
  intro before event earlier
  obtain ⟨after, same⟩ := earlier
  apply State.eventsStarted_atPrefix _ before event after []
  simpa only [← same, List.append_assoc, List.singleton_append] using started

/-- Source-derived structural retirement closes healthy-owner registration obligations.
The failure inventory can include observations available before consumed notifications.
-/
structure ClosedOwnerAccounting (queue : State) (work : Execution.Work)
    (parents : Nat → NodeRefs) (before : List GraphEvent) (failed : List Occurrence)
    : Prop where
  owners : queue.OwnerAccountingInInventory work parents before failed
  live : queue.LiveGroupsRegistered
  roots : queue.RootAncestorsRetired work
  retired : queue.UncancelledRetiredAncestors work
  regions : queue.RegionInventory work (before.flatMap (fun event => event.identities.1))

theorem ClosedOwnerAccounting.weakenFailures {queue work parents before old next}
    (prior : ClosedOwnerAccounting queue work parents before old)
    (included : old.Subset next)
    : ClosedOwnerAccounting queue work parents before next :=
  ⟨
    prior.owners.weakenFailures included,
    prior.live,
    prior.roots,
    prior.retired,
    prior.regions
  ⟩

/-- Pending-notice bookkeeping preserves the closed structural and owner evidence. -/
theorem ClosedOwnerAccounting.withGroupFailures {queue work parents before failed}
    (prior : ClosedOwnerAccounting queue work parents before failed)
    (notices : List GroupFailureEvent)
    : ClosedOwnerAccounting {queue with groupFailureEvents := notices} work parents before
        failed :=
  ⟨
    prior.owners.withGroupFailures notices,
    prior.live,
    prior.roots,
    prior.retired,
    prior.regions.regions,
    prior.regions.matching,
    prior.regions.registrations,
    prior.regions.started
  ⟩

private theorem ClosedOwnerAccounting.cacheTaskFailures {queue work parents before failed}
    (prior : ClosedOwnerAccounting queue work parents before failed)
    (available : List (Occurrence × Nat))
    (recorded
      : ∀ occurrence errors, (occurrence, errors) ∈ available → occurrence ∈ failed)
    : ClosedOwnerAccounting (queue.cacheTaskFailures available) work parents before
        failed := by
  have coverage := queue.cacheTaskFailures_registration prior.live prior.owners.pending.taskGroups
    available
  refine ⟨prior.owners.cacheTaskFailures available recorded, coverage.1, ?_,
    prior.retired.cacheTaskFailures available, prior.regions.cacheTaskFailures available⟩
  intro ref active
  rw [State.cacheTaskFailures_rootGroups] at active
  exact (prior.roots ref active).mono (fun _ retired => retired.cacheTaskFailures available)

private theorem ClosedOwnerAccounting.handleGraphEvent {queue work parents before failed}
    (prior : ClosedOwnerAccounting queue work parents before failed)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (generated : ExecutedWork work) (valid : ValidGraphEvents work before)
    (event : GraphEvent) (matching : event.MatchesWork work) (fresh : event.Fresh before)
    (tracked
      : ∀ occurrence result,
          event = .taskSuccess occurrence result
          → queue.StartedTaskDisposition occurrence
            ∧ ∃ task ∈ queue.tasks, task.occurrence = occurrence)
    (available : List (Occurrence × Nat))
    (recorded
      : ∀ occurrence errors, (occurrence, errors) ∈ available → occurrence ∈ failed)
    (notified
      : ∀ occurrence errors,
          event = .taskFailure occurrence errors → (occurrence, errors) ∈ available)
    : ClosedOwnerAccounting (queue.handleGraphEvent event available).1 work parents
        (before ++ [event]) failed := by
  let current := queue.cacheTaskFailures available
  have cached := prior.cacheTaskFailures available recorded
  have ready : current.RegistrationsAvailable work failed event available := by
    cases event with
    | taskSuccess occurrence result =>
        exact State.OwnerAccountingInInventory.taskSuccess_available_of_registered
          cached.owners generated (cached.retired.healthy cached.owners.cancelled)
          matching fresh
          (by
            simpa only [current, State.cacheTaskFailures_tasks] using (tracked _ _ rfl).2)
    | streamItems stream items =>
        apply cached.regions.streamItems_available generated matching fresh.1
          (available := available)
        intro item member
        exact fresh.2.2.1 item.occurrence (List.mem_map_of_mem member)
    | taskFailure | streamSuccess | streamFailure | groupFailure => trivial
  have owners := prior.owners.handleGraphEvent_ofDisposition canonical generated valid event
    matching fresh
    available recorded notified ready (fun occurrence result same => (tracked _ _ same).1)
  have structural := queue.handleGraphEvent_structuralRetirement generated prior.owners.groups
    prior.owners.links canonical prior.live prior.owners.pending.taskGroups
    prior.owners.pending.registration prior.roots
    prior.retired event matching available
  refine ⟨owners, structural.1, structural.2.1, structural.2.2, ?_⟩
  simpa only [List.flatMap_append, List.flatMap_singleton]
    using prior.regions.handleGraphEvent event matching available

private theorem ClosedOwnerAccounting.dispatchGraphEvent
    {queue work parents before failed}
    (prior : ClosedOwnerAccounting queue work parents before failed)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (generated : ExecutedWork work) (valid : ValidGraphEvents work before)
    (event : GraphEvent) (matching : event.MatchesWork work) (fresh : event.Fresh before)
    (tracked
      : ∀ occurrence result,
          event = .taskSuccess occurrence result
          → queue.StartedTaskDisposition occurrence
            ∧ ∃ task ∈ queue.tasks, task.occurrence = occurrence)
    (available : List (Occurrence × Nat))
    (recorded
      : ∀ occurrence errors, (occurrence, errors) ∈ available → occurrence ∈ failed)
    (notified
      : ∀ occurrence errors,
          event = .taskFailure occurrence errors → (occurrence, errors) ∈ available)
    : ClosedOwnerAccounting (queue.dispatchGraphEvent event available).1 work parents
        (before ++ [event]) failed := by
  have next := prior.handleGraphEvent canonical generated valid event matching fresh tracked
    available recorded notified
  exact next.withGroupFailures _

theorem ClosedOwnerAccounting.replayGraphEvents
    {queue work parents before failed available}
    (prior : ClosedOwnerAccounting queue work parents before failed)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (generated : ExecutedWork work) (events : List GraphEvent)
    (valid : ValidGraphEvents work (before ++ events))
    (accepted : State.acceptsBatch.go (fun _ => false) available queue events = true)
    (recorded
      : ∀ occurrence errors, (occurrence, errors) ∈ available → occurrence ∈ failed)
    (notified
      : ∀ occurrence errors,
          .taskFailure occurrence errors ∈ events → (occurrence, errors) ∈ available)
    : ClosedOwnerAccounting (queue.replayGraphEvents events available) work parents
        (before ++ events) failed := by
  apply prefix_invariant events (fun fifo =>
    ClosedOwnerAccounting (queue.replayGraphEvents fifo available) work parents
      (before ++ fifo) failed)
  · simpa only [State.replayGraphEvents, List.foldl_nil, List.append_nil] using prior
  · intro fifo event rest split past
    have boundary : (before ++ fifo ++ [event]).IsPrefix (before ++ events) :=
      ⟨rest, by simp [split, List.append_assoc]⟩
    obtain ⟨validBefore, matching, fresh⟩ := validGraphEvents_last (valid.prefix boundary)
    have current := past fifo (List.prefix_refl _)
    have tracked : ∀ occurrence result, event = .taskSuccess occurrence result
        → (queue.replayGraphEvents fifo available).StartedTaskDisposition occurrence
          ∧ ∃ task ∈ (queue.replayGraphEvents fifo available).tasks,
              task.occurrence = occurrence := by
      intro occurrence result same
      subst event
      obtain ⟨seen, seenPrefix, eligible⟩ := queue.acceptsBatch_go_eachAccepted events fifo
        (.taskSuccess occurrence result) available accepted ⟨rest, by simp [split]⟩
      have frame := past seen seenPrefix
      cases found : (queue.replayGraphEvents seen available).taskNode? occurrence with
      | none => simp [State.acceptsGraphEvent, found] at eligible
      | some node =>
          obtain ⟨remaining, history⟩ := seenPrefix
          have disposition := frame.owners.pending.startedTaskDisposition_atPrefix found
            frame.owners.producers frame.owners.producerOrder remaining
            (by simpa [history, List.append_assoc] using validBefore) available
          rw [← history, State.replayGraphEvents_append queue seen remaining available]
          exact ⟨
            disposition,
            node.task,
            (queue.replayGraphEvents seen available).replayGraphEvents_tasks_subset
              remaining available
              (frame.owners.pending.started node (List.mem_of_find?_eq_some found)),
            (State.taskNode?_some found).2
          ⟩
    have next := current.dispatchGraphEvent canonical generated validBefore event matching fresh
      tracked available recorded (by
        intro occurrence errors same
        exact notified _ _ (same ▸ by simp [split]))
    simpa only [State.replayGraphEvents_append, State.replayGraphEvents,
      List.foldl_append, List.foldl_cons, List.foldl_nil, List.append_assoc]
      using next

theorem ClosedOwnerAccounting.withTerminated {queue work parents before failed}
    (prior : ClosedOwnerAccounting queue work parents before failed) (terminated : Bool)
    : ClosedOwnerAccounting {queue with terminated := terminated} work parents before
        failed :=
  ⟨
    prior.owners.withTerminated terminated,
    prior.live,
    prior.roots,
    prior.retired,
    prior.regions.withTerminated terminated
  ⟩

private theorem ClosedOwnerAccounting.handleGraphEvents {queue work parents before}
    (prior
      : ClosedOwnerAccounting queue work parents before
          (GraphEvent.failureSettlements before))
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (generated : ExecutedWork work) (events : List GraphEvent)
    (valid : ValidGraphEvents work (before ++ events))
    (running : queue.terminated = false) (accepted : queue.acceptsBatch events = true)
    : ClosedOwnerAccounting (queue.handleGraphEvents events).1 work parents
        (before ++ events) (GraphEvent.failureSettlements (before ++ events)) := by
  have included : (GraphEvent.failureSettlements before).Subset
      (GraphEvent.failureSettlements (before ++ events)) := by
    rw [GraphEvent.failureSettlements_append_list]
    exact List.subset_append_right _ _
  have recorded : ∀ occurrence errors,
      (occurrence, errors) ∈ GraphEvent.availableFailures events →
        occurrence ∈ GraphEvent.failureSettlements (before ++ events) := by
    intro occurrence errors member
    obtain ⟨event, inEvents, same⟩ := List.mem_filterMap.mp member
    cases event <;> simp only [Option.some.injEq, reduceCtorEq, Prod.mk.injEq] at same
    obtain ⟨rfl, rfl⟩ := same
    apply List.mem_reverse.mpr
    exact List.mem_flatMap.mpr ⟨.taskFailure _ _, List.mem_append_right before inEvents,
      by simp [GraphEvent.groupFailures]⟩
  have result := (prior.weakenFailures included).replayGraphEvents canonical generated events valid
    accepted recorded (by
      intro occurrence errors member
      exact List.mem_filterMap.mpr ⟨.taskFailure occurrence errors, member, rfl⟩)
  obtain ⟨terminal, same⟩ := queue.handleGraphEvents_stateCore events running
  rw [same]
  exact result.withTerminated terminal

private theorem ClosedOwnerAccounting.runNormalized {queue work parents before}
    (prior
      : ClosedOwnerAccounting queue work parents before
          (GraphEvent.failureSettlements before))
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (generated : ExecutedWork work) (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work (before ++ batches.flatten))
    (started : queue.batchesStarted batches = true)
    : ClosedOwnerAccounting (queue.runNormalized batches).1 work parents
        (before ++ batches.flatten)
        (GraphEvent.failureSettlements (before ++ batches.flatten)) := by
  rw [State.runNormalized_replayBatches]
  induction batches generalizing queue before with
  | nil => simpa [State.replayBatches] using prior
  | cons batch rest ih =>
      obtain ⟨running, accepted, restStarted⟩ := queue.batchesStarted_cons batch rest started
      have earlier : (before ++ batch).IsPrefix (before ++ (batch :: rest).flatten) :=
        ⟨rest.flatten, by simp [List.append_assoc]⟩
      have next := prior.handleGraphEvents canonical generated batch (valid.prefix earlier)
        running accepted
      have result := ih next (by simpa [List.append_assoc] using valid) restStarted
      simpa only [State.replayBatches, List.foldl_cons, List.flatten_cons,
        List.append_assoc]
        using result

/-- Started actual host batches preserve healthy ownership without an availability callback.
The joint induction derives object-child availability from structural retirement and
stream-item availability from exposed regions at each cache-aware FIFO transition.
-/
theorem ExecutedWork.runNormalized_ownerAccounting_of_started {work : Execution.Work}
    (generated : ExecutedWork work) (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    : ∃ parents : Nat → NodeRefs,
        (∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
        ∧ ((State.initialize (Work.fromExecution work)).runNormalized
            batches).1.OwnerAccounting
            work parents batches.flatten := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have initial : ClosedOwnerAccounting (State.initialize (Work.fromExecution work)) work
      parents [] [] :=
    ⟨createWorkQueue_ownerAccounting work parents canonical generated,
      (createWorkQueue_registration work generated.declarations).1, generated.initialRootAncestorsRetired,
      generated.initialUncancelledRetirement, createWorkQueue_regionInventory work⟩
  exact ⟨
    parents,
    canonical,
    (initial.runNormalized canonical generated batches valid
      (by rwa [inputsStarted_eq_batchesStarted] at started)).owners
  ⟩

/-- Every actual FIFO cut retains ownership under the selected host batch's full rejection
inventory. Earlier batches are replayed with their own snapshots; the consumed source
prefix and available failures remain separate proof coordinates.
-/
theorem ExecutedWork.ownerAccounting_atBatchPrefix {work : Execution.Work}
    (generated : ExecutedWork work) (earlier : List (List GraphEvent))
    (batch : List GraphEvent) (later : List (List GraphEvent)) (fifo : List GraphEvent)
    (valid : ValidGraphEvents work (earlier ++ batch :: later).flatten)
    (started : inputsStarted work (earlier ++ batch :: later) = true)
    (prefixOfBatch : fifo.IsPrefix batch)
    : let queue :=
        ((State.initialize (Work.fromExecution work)).replayBatches
          earlier).replayGraphEvents
          fifo (GraphEvent.availableFailures batch)
      let source := earlier.flatten ++ fifo
      let failed := GraphEvent.failureSettlements (earlier.flatten ++ batch)
      ∃ parents,
        (∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
        ∧ queue.OwnerAccountingInInventory work parents source failed
        ∧ queue.UncancelledRetiredAncestors work
        ∧ queue.RootAncestorsRetired work
        ∧ queue.RegionInventory work
            (source.flatMap (fun event => event.identities.1)) := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  let initial := State.initialize (Work.fromExecution work)
  have checked : initial.batchesStarted (earlier ++ batch :: later) = true := by
    rwa [← inputsStarted_eq_batchesStarted]
  rw [State.batchesStarted_append, Bool.and_eq_true] at checked
  have validEarlier : ValidGraphEvents work earlier.flatten :=
    valid.prefix ⟨(batch :: later).flatten, by simp [List.flatten_append]⟩
  have initialFrame : ClosedOwnerAccounting initial work parents [] [] :=
    ⟨createWorkQueue_ownerAccounting work parents canonical generated,
      (createWorkQueue_registration work generated.declarations).1, generated.initialRootAncestorsRetired,
      generated.initialUncancelledRetirement, createWorkQueue_regionInventory work⟩
  have before := initialFrame.runNormalized canonical generated earlier
    (by simpa only [List.nil_append] using validEarlier) checked.1
  rw [State.runNormalized_replayBatches] at before
  simp only [List.nil_append] at before
  obtain ⟨_, accepted, _⟩ :=
    (initial.replayBatches earlier).batchesStarted_cons batch later checked.2
  obtain ⟨tail, same⟩ := prefixOfBatch
  have fifoAccepted : State.acceptsBatch.go (fun _ => false)
      (GraphEvent.availableFailures batch) (initial.replayBatches earlier) fifo = true := by
    apply State.acceptsBatch_go_prefix (after := tail)
    simpa only [State.acceptsBatch, same] using accepted
  have validFifo : ValidGraphEvents work (earlier.flatten ++ fifo) := by
    apply valid.prefix
    refine ⟨tail ++ later.flatten, ?_⟩
    simp only [List.flatten_append, List.flatten_cons, ← same, List.append_assoc]
  have included : (GraphEvent.failureSettlements earlier.flatten).Subset
      (GraphEvent.failureSettlements (earlier.flatten ++ batch)) := by
    rw [GraphEvent.failureSettlements_append_list]
    exact List.subset_append_right _ _
  have recorded : ∀ occurrence errors, (occurrence, errors) ∈ GraphEvent.availableFailures batch
      → occurrence ∈ GraphEvent.failureSettlements (earlier.flatten ++ batch) := by
    intro occurrence errors member
    obtain ⟨event, inBatch, outcome⟩ := List.mem_filterMap.mp member
    cases event <;> simp only [Option.some.injEq, reduceCtorEq, Prod.mk.injEq] at outcome
    obtain ⟨rfl, rfl⟩ := outcome
    apply List.mem_reverse.mpr
    exact List.mem_flatMap.mpr ⟨.taskFailure _ _, List.mem_append_right _ inBatch,
      List.mem_cons_self⟩
  have replayed := (before.weakenFailures included).replayGraphEvents canonical generated fifo
    validFifo fifoAccepted recorded (by
      intro occurrence errors member
      exact List.mem_filterMap.mpr ⟨.taskFailure occurrence errors,
        (by rw [← same]; exact List.mem_append_left _ member), rfl⟩)
  exact ⟨
    parents,
    canonical,
    replayed.owners,
    replayed.retired,
    replayed.roots,
    replayed.regions
  ⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
