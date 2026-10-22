import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.OwnerAccounting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamAvailability

/-! Healthy-owner replay with separate consumed and available failure coordinates. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Internal replay evidence under one available-failure inventory. The consumed event
prefix determines counters; `failed` may include later notifications from the same batch.
This is proof evidence over the existing queue, not runtime bookkeeping.
-/
structure State.OwnerAccountingInInventory (queue : State) (work : Execution.Work)
    (parents : Nat → NodeRefs) (events : List GraphEvent) (failed : List Occurrence)
    : Prop
    extends queue.HealthyCounterAccounting work parents events failed where
  owners
    : queue.HealthyRegisteredTaskAccounting work (GraphEvent.taskSettlements events)
        failed
  links : queue.ChildLinksCanonical parents

/-- At a complete source boundary, consumed and available failure inventories coincide. -/
abbrev State.OwnerAccounting (queue : State) (work : Execution.Work)
    (parents : Nat → NodeRefs) (events : List GraphEvent)
    : Prop :=
  queue.OwnerAccountingInInventory work parents events
    (GraphEvent.failureSettlements events)

/-- Initial lowering establishes counters, source metadata and healthy owner links. -/
theorem createWorkQueue_ownerAccounting (work : Execution.Work) (parents : Nat → NodeRefs)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (generated : ExecutedWork work)
    : (State.initialize (Work.fromExecution work)).OwnerAccounting work parents [] :=
  ⟨
    createWorkQueue_healthyCounterAccounting work parents canonical
      generated.declarations,
    createWorkQueue_healthyRegisteredTaskAccounting work generated,
    createWorkQueue_childLinksCanonical (Work.fromExecution work) parents
      (fun _ member =>
        workFromSpec_groups_parentCanonical_root canonical member)
  ⟩

/-- Pending internal notices do not alter owner and counter evidence. -/
theorem State.OwnerAccountingInInventory.withGroupFailures
    {queue work parents events failed}
    (prior : State.OwnerAccountingInInventory queue work parents events failed)
    (notices : List GroupFailureEvent)
    : ({queue with groupFailureEvents := notices}).OwnerAccountingInInventory work parents
        events failed :=
  ⟨prior.toHealthyCounterAccounting.withGroupFailures notices, prior.owners, prior.links⟩

/-- More available failures shrink the healthy-owner obligation. -/
theorem State.OwnerAccountingInInventory.weakenFailures
    {queue work parents events before after}
    (prior : State.OwnerAccountingInInventory queue work parents events before)
    (included : before.Subset after)
    : queue.OwnerAccountingInInventory work parents events after :=
  ⟨
    prior.toHealthyCounterAccounting.weakenFailures included,
    prior.owners.weakenFailures included,
    prior.links
  ⟩

/-- Cache exposure preserves counters and healthy owner links before consuming an input. -/
theorem State.OwnerAccountingInInventory.cacheTaskFailures
    {queue work parents events failed}
    (prior : State.OwnerAccountingInInventory queue work parents events failed)
    (available : List (Occurrence × Nat))
    (recorded
      : ∀ occurrence errors, (occurrence, errors) ∈ available → occurrence ∈ failed)
    : (queue.cacheTaskFailures available).OwnerAccountingInInventory work parents events
        failed :=
  ⟨
    prior.toHealthyCounterAccounting.cacheTaskFailures available recorded,
    prior.owners.cacheTaskFailures available,
    prior.links.cacheTaskFailures available
  ⟩

/-- A disposition-tracked FIFO step preserves ownership under a fixed failure inventory. -/
theorem State.OwnerAccountingInInventory.handleGraphEvent_ofDisposition
    {queue work parents before failed}
    (prior : State.OwnerAccountingInInventory queue work parents before failed)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (generated : ExecutedWork work) (valid : ValidGraphEvents work before)
    (event : GraphEvent) (matching : event.MatchesWork work) (fresh : event.Fresh before)
    (available : List (Occurrence × Nat))
    (recorded
      : ∀ occurrence errors, (occurrence, errors) ∈ available → occurrence ∈ failed)
    (notified
      : ∀ occurrence errors,
          event = .taskFailure occurrence errors → (occurrence, errors) ∈ available)
    (ready
      : (queue.cacheTaskFailures available).RegistrationsAvailable work failed event
          available)
    (tracked
      : ∀ occurrence result,
          event = .taskSuccess occurrence result
          → queue.StartedTaskDisposition occurrence)
    : (queue.handleGraphEvent event available).1.OwnerAccountingInInventory work parents
        (before ++ [event]) failed := by
  have owners := prior.owners.handleGraphEvent_matching prior.pending prior.supported
    prior.cancelled prior.links prior.groups canonical generated valid event matching fresh
    available ready recorded
  have included : (event.groupFailures ++ failed).Subset failed := by
    intro task member
    rcases List.mem_append.mp member with current | old
    · cases event <;> simp only [GraphEvent.groupFailures, List.mem_singleton, List.not_mem_nil]
        at current
      subst task
      exact recorded _ _ (notified _ _ rfl)
    · exact old
  exact ⟨
    prior.toHealthyCounterAccounting.handleGraphEvent_inInventory_ofDisposition generated
      canonical valid event matching fresh available recorded notified tracked,
    owners.weakenFailures included,
    prior.links.handleGraphEvent event matching canonical available
  ⟩

/-- Current task eligibility specializes disposition-tracked owner accounting. -/
theorem State.OwnerAccountingInInventory.handleGraphEvent
    {queue work parents before failed}
    (prior : State.OwnerAccountingInInventory queue work parents before failed)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (generated : ExecutedWork work) (valid : ValidGraphEvents work before)
    (event : GraphEvent) (matching : event.MatchesWork work) (fresh : event.Fresh before)
    (accepted : queue.acceptsGraphEvent event = true)
    (available : List (Occurrence × Nat))
    (recorded
      : ∀ occurrence errors, (occurrence, errors) ∈ available → occurrence ∈ failed)
    (notified
      : ∀ occurrence errors,
          event = .taskFailure occurrence errors → (occurrence, errors) ∈ available)
    (ready
      : (queue.cacheTaskFailures available).RegistrationsAvailable work failed event
          available)
    : (queue.handleGraphEvent event available).1.OwnerAccountingInInventory work parents
        (before ++ [event]) failed := by
  apply prior.handleGraphEvent_ofDisposition canonical generated valid event matching
    fresh available recorded notified ready
  intro occurrence result same
  subst event
  cases found : queue.taskNode? occurrence with
  | none => simp [State.acceptsGraphEvent, found] at accepted
  | some node => exact .inl ⟨node, found⟩

/-- A control-flag update does not affect the owner/counter inventory. -/
theorem State.OwnerAccountingInInventory.withTerminated {queue work parents events failed}
    (prior : State.OwnerAccountingInInventory queue work parents events failed)
    (terminated : Bool)
    : ({queue with terminated := terminated}).OwnerAccountingInInventory work parents
        events failed :=
  ⟨prior.toHealthyCounterAccounting.withTerminated terminated, prior.owners, prior.links⟩

/-- Default eventwise replay advances its failure inventory only when consuming an input. -/
theorem State.OwnerAccounting.handleGraphEvent {queue work parents before}
    (prior : State.OwnerAccounting queue work parents before)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (generated : ExecutedWork work) (valid : ValidGraphEvents work before)
    (event : GraphEvent) (matching : event.MatchesWork work) (fresh : event.Fresh before)
    (accepted : queue.acceptsGraphEvent event = true)
    (available
      : queue.RegistrationsAvailable work (GraphEvent.failureSettlements before) event)
    : (queue.handleGraphEvent event).1.OwnerAccounting work parents
        (before ++ [event]) := by
  have owners := prior.owners.handleGraphEvent_ofPendingAccounting prior.pending prior.supported
    prior.cancelled prior.links prior.groups canonical generated valid event matching fresh
    accepted [] (by simpa only [State.cacheTaskFailures, List.foldl_nil] using available)
  rw [← GraphEvent.failureSettlements_append] at owners
  exact ⟨
    prior.toHealthyCounterAccounting.handleGraphEvent generated canonical valid event
      matching fresh accepted,
    owners,
    prior.links.handleGraphEvent event matching canonical
  ⟩

/-- Realizing enqueue effects preserves this handler certificate. -/
theorem State.OwnerAccountingInInventory.dispatchGraphEvent_ofDisposition
    {queue work parents before failed}
    (prior : State.OwnerAccountingInInventory queue work parents before failed)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (generated : ExecutedWork work) (valid : ValidGraphEvents work before)
    (event : GraphEvent) (matching : event.MatchesWork work) (fresh : event.Fresh before)
    (available : List (Occurrence × Nat))
    (recorded
      : ∀ occurrence errors, (occurrence, errors) ∈ available → occurrence ∈ failed)
    (notified
      : ∀ occurrence errors,
          event = .taskFailure occurrence errors → (occurrence, errors) ∈ available)
    (ready
      : (queue.cacheTaskFailures available).RegistrationsAvailable work failed event
          available)
    (tracked
      : ∀ occurrence result,
          event = .taskSuccess occurrence result
          → queue.StartedTaskDisposition occurrence)
    : (queue.dispatchGraphEvent event available).1.OwnerAccountingInInventory work parents
        (before ++ [event]) failed := by
  have next := prior.handleGraphEvent_ofDisposition canonical generated valid event matching fresh available recorded notified ready tracked
  exact next.withGroupFailures _

/-- Realizing enqueue effects preserves this handler certificate. -/
theorem State.OwnerAccountingInInventory.dispatchGraphEvent
    {queue work parents before failed}
    (prior : State.OwnerAccountingInInventory queue work parents before failed)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (generated : ExecutedWork work) (valid : ValidGraphEvents work before)
    (event : GraphEvent) (matching : event.MatchesWork work) (fresh : event.Fresh before)
    (accepted : queue.acceptsGraphEvent event = true)
    (available : List (Occurrence × Nat))
    (recorded
      : ∀ occurrence errors, (occurrence, errors) ∈ available → occurrence ∈ failed)
    (notified
      : ∀ occurrence errors,
          event = .taskFailure occurrence errors → (occurrence, errors) ∈ available)
    (ready
      : (queue.cacheTaskFailures available).RegistrationsAvailable work failed event
          available)
    : (queue.dispatchGraphEvent event available).1.OwnerAccountingInInventory work parents
        (before ++ [event]) failed := by
  have next := prior.handleGraphEvent canonical generated valid event matching fresh
    accepted available recorded notified ready
  exact next.withGroupFailures _

/-- Realizing enqueue effects preserves this handler certificate. -/
theorem State.OwnerAccounting.dispatchGraphEvent {queue work parents before}
    (prior : State.OwnerAccounting queue work parents before)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (generated : ExecutedWork work) (valid : ValidGraphEvents work before)
    (event : GraphEvent) (matching : event.MatchesWork work) (fresh : event.Fresh before)
    (accepted : queue.acceptsGraphEvent event = true)
    (available
      : queue.RegistrationsAvailable work (GraphEvent.failureSettlements before) event)
    : (queue.dispatchGraphEvent event).1.OwnerAccounting work parents
        (before ++ [event]) := by
  have next := prior.handleGraphEvent canonical generated valid event matching fresh accepted available
  exact next.withGroupFailures _

/-- A fixed-snapshot acceptance check licenses every actual within-batch prefix state. -/
theorem State.eventsStarted_atPrefix (queue : State) (before : List GraphEvent)
    (event : GraphEvent) (after : List GraphEvent)
    (available : List (Occurrence × Nat) := [])
    (accepted : State.eventsStarted available queue (before ++ event :: after) = true)
    : (queue.replayGraphEvents before available).acceptsGraphEvent event = true := by
  induction before generalizing queue with
  | nil =>
      have both : queue.acceptsGraphEvent event = true ∧
          State.eventsStarted available (queue.dispatchGraphEvent event available).1 after
            = true := by
        simpa only [List.nil_append, List.cons_append, State.eventsStarted,
          Bool.and_eq_true]
          using accepted
      exact both.1
  | cons head tail ih =>
      have both : queue.acceptsGraphEvent head = true ∧
          State.eventsStarted available (queue.dispatchGraphEvent head available).1
            (tail ++ event :: after) = true := by
        simpa only [List.nil_append, List.cons_append, State.eventsStarted,
          Bool.and_eq_true]
          using accepted
      exact ih (queue.dispatchGraphEvent head available).1 both.2

/-- Conditional eventwise ownership is useful for the empty-snapshot proof language.
Actual host batches are handled separately below.
-/
theorem State.OwnerAccounting.replayGraphEvents {queue work parents}
    (initial : State.OwnerAccounting queue work parents [])
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (generated : ExecutedWork work) {events : List GraphEvent}
    (valid : ValidGraphEvents work events)
    (acceptedAt
      : ∀ before event,
          (before ++ [event]).IsPrefix events
          → (queue.replayGraphEvents before).acceptsGraphEvent event = true)
    (availableAt
      : ∀ before event,
          (before ++ [event]).IsPrefix events
          → (queue.replayGraphEvents before).RegistrationsAvailable work
              (GraphEvent.failureSettlements before) event)
    : (queue.replayGraphEvents events).OwnerAccounting work parents events := by
  induction valid with
  | nil => exact initial
  | @append before event prior matching fresh ready ih =>
      have included := List.prefix_append before [event]
      have earlier := ih
        (fun past next prefixOfBefore => acceptedAt past next (prefixOfBefore.trans included))
        (fun past next prefixOfBefore => availableAt past next (prefixOfBefore.trans included))
      rw [State.replayGraphEvents_append]
      exact earlier.dispatchGraphEvent canonical generated prior event matching fresh
        (acceptedAt before event (List.prefix_refl _))
        (availableAt before event (List.prefix_refl _))

/-- Generated conditional eventwise replay has canonical owner evidence. -/
theorem ExecutedWork.replayGraphEvents_ownerAccounting {work : Execution.Work}
    (generated : ExecutedWork work) (events : List GraphEvent)
    (valid : ValidGraphEvents work events)
    (accepted
      : State.eventsStarted [] (State.initialize (Work.fromExecution work)) events = true)
    (availableAt
      : ∀ before event,
          (before ++ [event]).IsPrefix events
          → ((State.initialize (Work.fromExecution work)).replayGraphEvents
              before).RegistrationsAvailable
              work (GraphEvent.failureSettlements before) event)
    : ∃ parents : Nat → NodeRefs,
        (∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
        ∧ ((State.initialize (Work.fromExecution work)).replayGraphEvents
            events).OwnerAccounting
            work parents events := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  refine ⟨parents, canonical,
    (createWorkQueue_ownerAccounting work parents canonical generated).replayGraphEvents
      canonical generated valid ?_ availableAt⟩
  intro before event earlier
  obtain ⟨after, same⟩ := earlier
  apply State.eventsStarted_atPrefix _ before event after []
  simpa only [← same, List.append_assoc, List.singleton_append] using accepted

/-- Changing only the terminal flag preserves boundary owner accounting. -/
theorem State.OwnerAccounting.withTerminated {queue work parents events}
    (prior : State.OwnerAccounting queue work parents events) (terminated : Bool)
    : ({queue with terminated := terminated}).OwnerAccounting work parents events :=
  State.OwnerAccountingInInventory.withTerminated prior terminated

/-- Every within-batch integration has healthy contributors at its actual cached state. -/
def State.BatchOwnerAvailability (queue : State) (work : Execution.Work)
    (failed : List Occurrence) (events : List GraphEvent)
    (available : List (Occurrence × Nat))
    : Prop :=
  ∀ front event back,
    events = front ++ event :: back
    → ((queue.replayGraphEvents front available).cacheTaskFailures
        available).RegistrationsAvailable
        work failed event available

/-- Conditional ownership composes through one batch under its full failure snapshot. -/
theorem State.OwnerAccountingInInventory.replayGraphEvents
    {queue work parents before failed} {available : List (Occurrence × Nat)}
    (prior : State.OwnerAccountingInInventory queue work parents before failed)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (generated : ExecutedWork work) (events : List GraphEvent)
    (valid : ValidGraphEvents work (before ++ events))
    (accepted : State.eventsStarted available queue events = true)
    (recorded
      : ∀ occurrence errors, (occurrence, errors) ∈ available → occurrence ∈ failed)
    (notified
      : ∀ occurrence errors,
          .taskFailure occurrence errors ∈ events → (occurrence, errors) ∈ available)
    (ready : queue.BatchOwnerAvailability work failed events available)
    : (queue.replayGraphEvents events available).OwnerAccountingInInventory work parents
        (before ++ events) failed := by
  induction events generalizing queue before with
  | nil => simpa [State.replayGraphEvents] using prior
  | cons event rest ih =>
      have earlier : (before ++ [event]).IsPrefix (before ++ event :: rest) :=
        ⟨rest, by simp⟩
      obtain ⟨validBefore, matching, fresh⟩ := validGraphEvents_last (valid.prefix earlier)
      have accepts : queue.acceptsGraphEvent event = true ∧
          State.eventsStarted available (queue.dispatchGraphEvent event available).1 rest
            = true := by
        simpa only [List.nil_append, List.cons_append, State.eventsStarted,
          Bool.and_eq_true]
          using accepted
      have next := prior.dispatchGraphEvent canonical generated validBefore event matching fresh
        accepts.1 available recorded
        (by intro occurrence errors same; exact notified _ _ (same ▸ List.mem_cons_self))
        (ready [] event rest rfl)
      have remaining : (queue.dispatchGraphEvent event available).1.BatchOwnerAvailability
          work failed rest available := by
        intro front next back same
        simpa only [State.replayGraphEvents, List.foldl_cons]
          using ready (event :: front) next back (by simp [same])
      have result := ih next (by simpa [List.append_assoc] using valid) accepts.2
        (fun occurrence errors member => notified _ _ (List.mem_cons_of_mem _ member)) remaining
      simpa only [State.replayGraphEvents, List.foldl_cons, List.append_assoc,
        List.singleton_append]
        using result

/-- Buffered source replay keeps healthy owners using the disposition-aware counter frame.
Registered-owner preservation needs matching and freshness, including ignored successes;
public admission supplies initial eligibility only to the separate counter proof.
-/
theorem State.OwnerAccountingInInventory.replayGraphEvents_admitted
    {queue work parents before failed} {available : List (Occurrence × Nat)}
    (prior : State.OwnerAccountingInInventory queue work parents before failed)
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
    (ready : queue.BatchOwnerAvailability work failed events available)
    : (queue.replayGraphEvents events available).OwnerAccountingInInventory work parents
        (before ++ events) failed := by
  have counters (fifo : List GraphEvent) (earlier : fifo.IsPrefix events) :
      (queue.replayGraphEvents fifo available).HealthyCounterAccounting work parents
        (before ++ fifo) failed := by
    obtain ⟨tail, joined⟩ := earlier
    apply prior.toHealthyCounterAccounting.replayGraphEvents_admitted generated canonical
      fifo (valid.prefix ⟨tail, by rw [List.append_assoc, joined]⟩)
    · apply State.acceptsBatch_go_prefix (after := tail)
      simpa only [joined] using accepted
    · exact recorded
    · intro occurrence errors member
      exact notified _ _ (joined ▸ List.mem_append_left tail member)
  have loop (remaining fifo : List GraphEvent) (split : events = fifo ++ remaining)
      (current : (queue.replayGraphEvents fifo available).HealthyRegisteredTaskAccounting work
        (GraphEvent.taskSettlements (before ++ fifo)) failed)
      : (queue.replayGraphEvents events available).HealthyRegisteredTaskAccounting work
          (GraphEvent.taskSettlements (before ++ events)) failed := by
    induction remaining generalizing fifo with
    | nil =>
        have same : events = fifo := by simpa only [List.append_nil] using split
        simpa only [same] using current
    | cons event rest ih =>
        have prefixOfSource : fifo.IsPrefix events := ⟨event :: rest, split.symm⟩
        have snapshot := counters fifo prefixOfSource
        have boundary : (before ++ fifo ++ [event]).IsPrefix (before ++ events) :=
          ⟨rest, by simp [split, List.append_assoc]⟩
        obtain ⟨validBefore, matching, fresh⟩ := validGraphEvents_last (valid.prefix boundary)
        have next := current.handleGraphEvent_matching snapshot.pending snapshot.supported
          snapshot.cancelled snapshot.childLinks snapshot.groups canonical generated validBefore
          event matching fresh available (ready fifo event rest split) recorded
        have included : (event.groupFailures ++ failed).Subset failed := by
          intro task member
          rcases List.mem_append.mp member with recent | old
          · cases event <;> simp only [GraphEvent.groupFailures, List.mem_singleton,
              List.not_mem_nil] at recent
            rename_i occurrence errors
            subst task
            exact recorded occurrence errors (notified occurrence errors (by simp [split]))
          · exact old
        apply ih (fifo ++ [event]) (by simp [split, List.append_assoc])
        simpa only [State.replayGraphEvents_append, State.replayGraphEvents,
          List.foldl_append, List.foldl_cons, List.foldl_nil, List.append_assoc]
          using (show ((queue.replayGraphEvents fifo available).dispatchGraphEvent event
                        available).1.HealthyRegisteredTaskAccounting
                        work (GraphEvent.taskSettlements (before ++ fifo ++ [event]))
                        failed from next.weakenFailures included)
  have complete := counters events (List.prefix_refl _)
  exact ⟨
    complete,
    loop events [] (by simp)
      (by
        simpa only [State.replayGraphEvents, List.foldl_nil, List.append_nil]
          using prior.owners),
    complete.childLinks
  ⟩

/-- Whole batches expose their cache inventory before consuming individual inputs. -/
theorem State.OwnerAccounting.handleGraphEvents {queue work parents before}
    (prior : State.OwnerAccounting queue work parents before)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (generated : ExecutedWork work) (events : List GraphEvent)
    (valid : ValidGraphEvents work (before ++ events))
    (running : queue.terminated = false) (accepted : queue.acceptsBatch events = true)
    (ready
      : queue.BatchOwnerAvailability work
          (GraphEvent.failureSettlements (before ++ events)) events
          (GraphEvent.availableFailures events))
    : (queue.handleGraphEvents events).1.OwnerAccounting work parents
        (before ++ events) := by
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
  have replayed := (prior.weakenFailures included).replayGraphEvents_admitted
    canonical generated events
    valid accepted recorded (by
      intro occurrence errors member
      exact List.mem_filterMap.mpr ⟨.taskFailure occurrence errors, member, rfl⟩) ready
  obtain ⟨terminal, same⟩ := queue.handleGraphEvents_stateCore events running
  rw [same]
  exact replayed.withTerminated terminal

/-- Registration availability across actual host batches, including their own snapshots. -/
def State.OwnerAvailability (queue : State) (work : Execution.Work)
    (before : List GraphEvent)
    : List (List GraphEvent) → Prop
  | [] => True
  | batch :: rest =>
      queue.BatchOwnerAvailability work (GraphEvent.failureSettlements (before ++ batch))
        batch (GraphEvent.availableFailures batch)
      ∧ (queue.handleGraphEvents batch).1.OwnerAvailability work (before ++ batch) rest

/-- Conditional owner replay follows the actual normalized batch fold. -/
theorem State.OwnerAccounting.runNormalized {queue work parents before}
    (prior : State.OwnerAccounting queue work parents before)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (generated : ExecutedWork work) (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work (before ++ batches.flatten))
    (started : queue.batchesStarted batches = true)
    (ready : queue.OwnerAvailability work before batches)
    : (queue.runNormalized batches).1.OwnerAccounting work parents
        (before ++ batches.flatten) := by
  rw [State.runNormalized_replayBatches]
  induction batches generalizing queue before with
  | nil => simpa [State.replayBatches] using prior
  | cons batch rest ih =>
      obtain ⟨running, accepted, restStarted⟩ := queue.batchesStarted_cons batch rest started
      have earlier : (before ++ batch).IsPrefix (before ++ (batch :: rest).flatten) :=
        ⟨rest.flatten, by simp [List.append_assoc]⟩
      have next := prior.handleGraphEvents canonical generated batch (valid.prefix earlier)
        running accepted ready.1
      have result := ih next (by simpa [List.append_assoc] using valid) restStarted ready.2
      simpa only [State.replayBatches, List.foldl_cons, List.flatten_cons,
        List.append_assoc]
        using result

/-- Generated actual replay has canonical ownership when integration availability holds. -/
theorem ExecutedWork.runNormalized_ownerAccounting {work : Execution.Work}
    (generated : ExecutedWork work) (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    (ready
      : (State.initialize (Work.fromExecution work)).OwnerAvailability work [] batches)
    : ∃ parents : Nat → NodeRefs,
        (∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
        ∧ ((State.initialize (Work.fromExecution work)).runNormalized
            batches).1.OwnerAccounting
            work parents batches.flatten := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  exact ⟨
    parents,
    canonical,
    (createWorkQueue_ownerAccounting work parents canonical generated).runNormalized
      canonical generated batches valid
      (by rwa [inputsStarted_eq_batchesStarted] at started) ready
  ⟩

/-- The combined ledger also supplies ownership in successful-settlement coordinates. -/
theorem State.OwnerAccounting.healthyRegisteredTasks {queue work parents events}
    (prior : State.OwnerAccounting queue work parents events)
    : queue.HealthyRegisteredTaskAccounting work (GraphEvent.groupSettlements events)
        (GraphEvent.failureSettlements events) := by
  intro task member fresh ref contributor healthy
  have notFailed := (prior.pending.matching task member).not_failed_of_healthy contributor healthy
  apply prior.owners task member _ ref contributor healthy
  simp only [GraphEvent.mem_taskSettlements, fresh, notFailed, or_self, not_false_eq_true]

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
