import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.HandlerPublicationLedger
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StoredLinkReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.BatchPublicationCleanliness

/-! One source-replay ledger retains all handler-local closure certificates. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Replay certificates slice one already chosen ledger at exact handler value counts
-----------------------------------------------------------------------------------------

/-- Every input handler covers its buffered/prepared map on its slice of `published`.
`queue` is the replay's input state and `events` its source inputs. Each actual handler's
object-value count fixes the slice; recursive checks cannot choose independent labels.
-/
def State.ReplayClosuresCovered (queue : State) (events : List GraphEvent)
    (published : List ObjectPublication) (available : List (Occurrence × Nat) := [])
    : Prop :=
  match events with
  | [] => True
  | event :: rest =>
      let next := queue.dispatchGraphEvent event available
      let cached := queue.cacheTaskFailures available
      let count := (next.2.flatMap WorkQueueEvent.objectValues).length
      queue.BufferedClosuresCovered (published.take count) next.2
      ∧ cached.PreparedClosuresCovered event (published.take count) available
      ∧ queue.StoredValuesConserved (published.take count) next.1
      ∧ cached.PreparedValuesConserved event (published.take count) available
      ∧ queue.StoredOwnersConserved (published.take count) next.1
      ∧ cached.PreparedOwnersConserved event (published.take count) available
      ∧ cached.PreparedReleaseOwners event (published.take count) available
      ∧ cached.PreparedMembershipsCleared event (published.take count) available
      ∧ BlocksFollowRegistrations next.1.tasks (published.take count) next.2
      ∧ next.1.ReplayClosuresCovered rest (published.drop count) available

/-- Removing one source handler retains its continuation's exact ledger suffix.
Witness: project the recursive certificate after that handler's object-value count.
-/
theorem State.ReplayClosuresCovered.tail {queue : State}
    {available : List (Occurrence × Nat)} {event rest published}
    (covered : queue.ReplayClosuresCovered (event :: rest) published available)
    : (queue.dispatchGraphEvent event available).1.ReplayClosuresCovered rest
        (published.drop
          ((queue.dispatchGraphEvent event available).2.flatMap
            WorkQueueEvent.objectValues).length) available :=
  covered.2.2.2.2.2.2.2.2.2

/-- The next handler and remaining replay use disjoint consecutive ledger segments.
Witness: the next handler's exact payload projection fixes its segment length, so take
and drop recover the supplied labels without relying on uniqueness of payload values.
-/
theorem State.ReplayClosuresCovered.cons {queue : State}
    {available : List (Occurrence × Nat)} {event rest first later}
    (values
      : first.map Prod.snd
        = (queue.dispatchGraphEvent event available).2.flatMap
            WorkQueueEvent.objectValues)
    (buffered
      : queue.BufferedClosuresCovered first (queue.dispatchGraphEvent event available).2)
    (prepared
      : (queue.cacheTaskFailures available).PreparedClosuresCovered event first available)
    (conserved
      : queue.StoredValuesConserved first (queue.dispatchGraphEvent event available).1)
    (installed
      : (queue.cacheTaskFailures available).PreparedValuesConserved event first available)
    (owners
      : queue.StoredOwnersConserved first (queue.dispatchGraphEvent event available).1)
    (preparedOwners
      : (queue.cacheTaskFailures available).PreparedOwnersConserved event first available)
    (drainOwners
      : (queue.cacheTaskFailures available).PreparedReleaseOwners event first available)
    (drainCleared
      : (queue.cacheTaskFailures available).PreparedMembershipsCleared event first
          available)
    (ordered
      : BlocksFollowRegistrations (queue.dispatchGraphEvent event available).1.tasks first
          (queue.dispatchGraphEvent event available).2)
    (covered
      : (queue.dispatchGraphEvent event available).1.ReplayClosuresCovered rest later
          available)
    : queue.ReplayClosuresCovered (event :: rest) (first ++ later) available := by
  have size : first.length
      = ((queue.dispatchGraphEvent event available).2.flatMap
          WorkQueueEvent.objectValues).length := by
    simpa only [List.length_map] using congrArg List.length values
  simpa only [State.ReplayClosuresCovered, ← size, List.take_left, List.drop_left]
    using And.intro buffered
      (And.intro prepared
        (And.intro conserved
          (And.intro installed
            (And.intro owners
              (And.intro preparedOwners
                (And.intro drainOwners
                  (And.intro drainCleared (And.intro ordered covered))))))))

/-- Any source boundary recovers its certificates from the one full-replay ledger.
Witness: peel earlier handlers and add their exact object-value offsets; the actual queue
state follows the same source prefix. No later value can enter the selected local slice.
-/
theorem State.ReplayClosuresCovered.atPrefixWithConservation {queue : State}
    {available : List (Occurrence × Nat)} {published} (before : List GraphEvent)
    (event : GraphEvent) (after : List GraphEvent)
    (covered : queue.ReplayClosuresCovered (before ++ event :: after) published available)
    : let current := queue.replayGraphEvents before available
      let offset :=
        ((queue.rawEventReplay before available).2.flatMap
          WorkQueueEvent.objectValues).length
      let count :=
        ((current.dispatchGraphEvent event available).2.flatMap
          WorkQueueEvent.objectValues).length
      current.BufferedClosuresCovered ((published.drop offset).take count)
        (current.dispatchGraphEvent event available).2
      ∧ (current.cacheTaskFailures available).PreparedClosuresCovered event
          ((published.drop offset).take count) available
      ∧ current.StoredValuesConserved ((published.drop offset).take count)
          (current.dispatchGraphEvent event available).1
      ∧ (current.cacheTaskFailures available).PreparedValuesConserved event
          ((published.drop offset).take count) available := by
  induction before generalizing queue published with
  | nil => exact ⟨covered.1, covered.2.1, covered.2.2.1, covered.2.2.2.1⟩
  | cons first rest ih =>
      have selected := ih covered.tail
      simpa only [List.cons_append, State.replayGraphEvents, List.foldl_cons,
        State.rawEventReplay_cons, List.flatMap_append, List.length_append,
        List.drop_drop]
        using selected

/-- Any handler retains the original buffered/prepared coverage interface.
Witness: project the stronger source-boundary certificate, keeping its exact ledger slice.
-/
theorem State.ReplayClosuresCovered.atPrefix {queue : State}
    {available : List (Occurrence × Nat)} {published} (before : List GraphEvent)
    (event : GraphEvent) (after : List GraphEvent)
    (covered : queue.ReplayClosuresCovered (before ++ event :: after) published available)
    : let current := queue.replayGraphEvents before available
      let offset :=
        ((queue.rawEventReplay before available).2.flatMap
          WorkQueueEvent.objectValues).length
      let count :=
        ((current.dispatchGraphEvent event available).2.flatMap
          WorkQueueEvent.objectValues).length
      current.BufferedClosuresCovered ((published.drop offset).take count)
        (current.dispatchGraphEvent event available).2
      ∧ (current.cacheTaskFailures available).PreparedClosuresCovered event
          ((published.drop offset).take count) available := by
  have selected := covered.atPrefixWithConservation before event after
  exact ⟨selected.1, selected.2.1⟩

/-- Every source boundary retains buffered and prepared owner conservation on its slice.
Witness: peel earlier handlers, using the same source-state fold and object-count offsets
as closure coverage. Both certificates use the original full publication ledger.
-/
theorem State.ReplayClosuresCovered.atPrefixWithOwners {queue : State}
    {available : List (Occurrence × Nat)} {published} (before : List GraphEvent)
    (event : GraphEvent) (after : List GraphEvent)
    (covered : queue.ReplayClosuresCovered (before ++ event :: after) published available)
    : let current := queue.replayGraphEvents before available
      let offset :=
        ((queue.rawEventReplay before available).2.flatMap
          WorkQueueEvent.objectValues).length
      let count :=
        ((current.dispatchGraphEvent event available).2.flatMap
          WorkQueueEvent.objectValues).length
      current.StoredOwnersConserved ((published.drop offset).take count)
        (current.dispatchGraphEvent event available).1
      ∧ (current.cacheTaskFailures available).PreparedOwnersConserved event
          ((published.drop offset).take count) available := by
  induction before generalizing queue published with
  | nil => exact ⟨covered.2.2.2.2.1, covered.2.2.2.2.2.1⟩
  | cons first rest ih =>
      have selected := ih covered.tail
      simpa only [List.cons_append, State.replayGraphEvents, List.foldl_cons,
        State.rawEventReplay_cons, List.flatMap_append, List.length_append,
        List.drop_drop]
        using selected

/-- Every successful handler retains its internal drain evidence on the full replay ledger.
Witness: peel earlier source handlers and add their exact object-count offsets. The
selected prefix certificates use the same labels as buffered and prepared conservation.
-/
theorem State.ReplayClosuresCovered.atPrefixDrainOwners {queue : State}
    {available : List (Occurrence × Nat)} {published} (before : List GraphEvent)
    (event : GraphEvent) (after : List GraphEvent)
    (covered : queue.ReplayClosuresCovered (before ++ event :: after) published available)
    : let current := queue.replayGraphEvents before available
      let offset :=
        ((queue.rawEventReplay before available).2.flatMap
          WorkQueueEvent.objectValues).length
      let count :=
        ((current.dispatchGraphEvent event available).2.flatMap
          WorkQueueEvent.objectValues).length
      (current.cacheTaskFailures available).PreparedReleaseOwners event
        ((published.drop offset).take count) available := by
  induction before generalizing queue published with
  | nil => exact covered.2.2.2.2.2.2.1
  | cons first rest ih =>
      have selected := ih covered.tail
      simpa only [List.cons_append, State.replayGraphEvents, List.foldl_cons,
        State.rawEventReplay_cons, List.flatMap_append, List.length_append,
        List.drop_drop] using selected

-----------------------------------------------------------------------------------------
-- Existing source laws derive all state facts throughout the actual raw replay
-----------------------------------------------------------------------------------------

/-- Every handler retains release membership exclusion on its exact full-replay ledger slice.
Witness: peel source handlers using their actual object-value counts. This is the same
ledger used by producer and closure accounting, not another existential matching.
-/
theorem State.ReplayClosuresCovered.atPrefixMemberships {queue : State}
    {available : List (Occurrence × Nat)} {published} (before : List GraphEvent)
    (event : GraphEvent) (after : List GraphEvent)
    (covered : queue.ReplayClosuresCovered (before ++ event :: after) published available)
    : let current := queue.replayGraphEvents before available
      let offset :=
        ((queue.rawEventReplay before available).2.flatMap
          WorkQueueEvent.objectValues).length
      let count :=
        ((current.dispatchGraphEvent event available).2.flatMap
          WorkQueueEvent.objectValues).length
      (current.cacheTaskFailures available).PreparedMembershipsCleared event
        ((published.drop offset).take count) available := by
  induction before generalizing queue published with
  | nil => exact covered.2.2.2.2.2.2.2.1
  | cons first rest ih =>
      have selected := ih covered.tail
      simpa only [List.cons_append, State.replayGraphEvents, List.foldl_cons,
        State.rawEventReplay_cons, List.flatMap_append, List.length_append,
        List.drop_drop] using selected

/-- Permanent task registration grows as an ordered subsequence through actual replay.
Witness: each handler either leaves the registry unchanged or appends its child chunk.
-/
theorem State.replayGraphEvents_tasks_sublist (queue : State) (events : List GraphEvent)
    (available : List (Occurrence × Nat) := [])
    : queue.tasks.Sublist (queue.replayGraphEvents events available).tasks := by
  induction events generalizing queue with
  | nil => exact .refl _
  | cons event rest ih =>
      have first : queue.tasks.Sublist (queue.dispatchGraphEvent event available).1.tasks := by
        change queue.tasks.Sublist (queue.handleGraphEvent event available).1.tasks
        rcases queue.handleGraphEvent_taskChunk event available with same | appended
        · rw [same]; exact .refl _
        · rw [appended]; exact List.sublist_append_left _ _
      exact first.trans (ih _)

/-- Matching fresh source replay preserves one ledger for all closure and stream witnesses.
Witness: jointly replay the existing pending, membership, and child-stream invariants;
append each handler's common inventory and retain its certificates at the exact offsets.
The result concerns local buffered/prepared maps, not yet every structural contributor.
-/
theorem State.PublicationInventory.rawEventReplay_bufferedCoverage_ofMatching
    {queue : State} {work before published} {available : List (Occurrence × Nat)}
    (inventory : queue.PublicationInventory (ObjectValueFrom before) published)
    (generated : ExecutedWork work)
    (accounted : queue.PendingAccounting work (GraphEvent.taskSettlements before))
    (links : queue.StoredTaskLinks) (settled : queue.ChildStreamsSettled)
    (children : queue.ChildStreamsMatchWork work) (events : List GraphEvent)
    (valid : ValidGraphEvents work (before ++ events))
    (memberships : queue.GroupMembershipOrder) (cancelled : queue.CancellationsRetired)
    (clean
      : ∀ occurrence value,
          ObjectValueFrom (before ++ events) occurrence value
          → ∀ errors, (occurrence, errors) ∉ available)
    : ∃ added : List ObjectPublication,
        added.map Prod.snd
          = (queue.rawEventReplay events available).2.flatMap WorkQueueEvent.objectValues
        ∧ (queue.rawEventReplay events available).1.PublicationInventory
            (ObjectValueFrom (before ++ events)) (published ++ added)
        ∧ queue.ReplayClosuresCovered events added available
        ∧ StreamReleasePublications work added (queue.rawEventReplay events available).2
        ∧ BlocksFollowRegistrations (queue.rawEventReplay events available).1.tasks added
            (queue.rawEventReplay events available).2 := by
  induction events generalizing queue before published with
  | nil =>
      refine ⟨[], rfl, ?_, trivial, .nil work, .nil _ _⟩
      simpa only [List.append_nil, State.rawEventReplay, List.foldl_nil] using inventory
  | cons event rest ih =>
      have earlier : (before ++ [event]).IsPrefix (before ++ event :: rest) :=
        ⟨rest, by simp⟩
      obtain ⟨matching, fresh, _⟩ := valid.atPrefix earlier
      have included := GraphEvent.taskSettlements_subsetIdentities before
      obtain ⟨first, values, current, buffered, prepared, firstStreams, conserved, installed,
        firstOrder, firstOwners, preparedOwners, drainOwners, drainCleared⟩ :=
        inventory.dispatchGraphEvent_bufferedCoverage generated accounted included links settled
          children event matching fresh memberships cancelled available
          (fun occurrence value source => clean occurrence value (source.mono earlier.subset))
      have next := accounted.dispatchGraphEvent_ofMatching generated included event matching fresh
        available
      rw [← GraphEvent.taskSettlements_append] at next
      obtain ⟨later, laterValues, final, laterCoverage, laterStreams, laterOrder⟩ :=
        ih current next
          (links.handleGraphEvent accounted included event matching fresh available)
          (settled.handleGraphEvent event available) (children.handleGraphEvent matching available)
          (by simpa only [List.append_assoc, List.singleton_append] using valid)
          (memberships.dispatchGraphEvent event available)
          (cancelled.handleGraphEvent accounted.liveGroups accounted.taskGroups event matching
            available)
          (by simpa only [List.append_assoc, List.singleton_append] using clean)
      rw [State.rawEventReplay_cons queue event rest available]
      refine ⟨first ++ later, ?_, ?_,
        .cons values buffered prepared conserved installed firstOwners preparedOwners
          drainOwners drainCleared firstOrder laterCoverage,
        firstStreams.append laterStreams values, ?_⟩
      · simp only [List.map_append, List.flatMap_append, values, laterValues]
      · simpa only [List.append_assoc, List.singleton_append] using final
      · apply BlocksFollowRegistrations.append ?_ laterOrder
          (by simpa only [List.length_map] using congrArg List.length values)
        apply firstOrder.mono
        rw [State.rawEventReplay_state _ rest available]
        exact State.replayGraphEvents_tasks_sublist _ rest available

/-- Strict eventwise source checking specializes matching publication replay. -/
theorem State.PublicationInventory.rawEventReplay_bufferedCoverage {queue : State}
    {work before published} {available : List (Occurrence × Nat)}
    (inventory : queue.PublicationInventory (ObjectValueFrom before) published)
    (generated : ExecutedWork work)
    (accounted : queue.PendingAccounting work (GraphEvent.taskSettlements before))
    (links : queue.StoredTaskLinks) (settled : queue.ChildStreamsSettled)
    (children : queue.ChildStreamsMatchWork work) (events : List GraphEvent)
    (valid : ValidGraphEvents work (before ++ events))
    (_accepted : State.eventsStarted available queue events = true)
    (memberships : queue.GroupMembershipOrder) (cancelled : queue.CancellationsRetired)
    (clean
      : ∀ occurrence value,
          ObjectValueFrom (before ++ events) occurrence value
          → ∀ errors, (occurrence, errors) ∉ available)
    : ∃ added : List ObjectPublication,
        added.map Prod.snd
          = (queue.rawEventReplay events available).2.flatMap WorkQueueEvent.objectValues
        ∧ (queue.rawEventReplay events available).1.PublicationInventory
            (ObjectValueFrom (before ++ events)) (published ++ added)
        ∧ queue.ReplayClosuresCovered events added available
        ∧ StreamReleasePublications work added (queue.rawEventReplay events available).2
        ∧ BlocksFollowRegistrations (queue.rawEventReplay events available).1.tasks added
            (queue.rawEventReplay events available).2 :=
  inventory.rawEventReplay_bufferedCoverage_ofMatching generated accounted links settled
    children events valid memberships cancelled clean

/-- Generated accepted replay has the joint ledger without supplied queue invariants.
Witness: the raw replay theorem initialized with the empty publication inventory and the
already proved creation invariants. Arbitrary success/failure and item nesting is allowed.
-/
theorem ExecutedWork.rawEventReplay_bufferedCoverage {work : Execution.Work}
    (generated : ExecutedWork work) (events : List GraphEvent)
    (valid : ValidGraphEvents work events)
    (accepted
      : State.eventsStarted [] (State.initialize (Work.fromExecution work)) events = true)
    : ∃ published : List ObjectPublication,
        published.map Prod.snd
          = ((State.initialize (Work.fromExecution work)).rawEventReplay events).2.flatMap
              WorkQueueEvent.objectValues
        ∧ ((State.initialize (Work.fromExecution work)).rawEventReplay
            events).1.PublicationInventory
            (ObjectValueFrom events) published
        ∧ (State.initialize (Work.fromExecution work)).ReplayClosuresCovered events
            published
        ∧ StreamReleasePublications work published
            ((State.initialize (Work.fromExecution work)).rawEventReplay events).2
        ∧ BlocksFollowRegistrations
            ((State.initialize (Work.fromExecution work)).rawEventReplay events).1.tasks
            published
            ((State.initialize (Work.fromExecution work)).rawEventReplay events).2 := by
  have initial : (State.initialize (Work.fromExecution work)).PublicationInventory
      (ObjectValueFrom []) [] :=
    ⟨by simp, by simp, createWorkQueue_storedValues _ _⟩
  exact initial.rawEventReplay_bufferedCoverage generated
    (createWorkQueue_pendingAccounting work
      generated.declarations) (createWorkQueue_storedTaskLinks _)
    (createWorkQueue_childStreamsSettled _)
    (createWorkQueue_childStreamsMatchWork (Work.fromExecution work) work) events valid
    accepted (createWorkQueue_groupMembershipOrder _)
    (createWorkQueue_cancellationsRetired _)
    (by intro occurrence value source errors impossible; cases impossible)

-----------------------------------------------------------------------------------------
-- The outer batch wrapper changes termination control, not object-publication segments
-----------------------------------------------------------------------------------------

/-- A running accepted batch retains the raw replay's joint closure/release certificate.
Witness: the actual batch wrapper either keeps raw output or appends a terminal marker;
neither branch changes object labels or any source-handler boundary inside the batch.
-/
theorem State.PublicationInventory.handleGraphEvents_bufferedCoverage {queue : State}
    {work before published}
    (inventory : queue.PublicationInventory (ObjectValueFrom before) published)
    (generated : ExecutedWork work)
    (accounted : queue.PendingAccounting work (GraphEvent.taskSettlements before))
    (links : queue.StoredTaskLinks) (settled : queue.ChildStreamsSettled)
    (children : queue.ChildStreamsMatchWork work) (events : List GraphEvent)
    (valid : ValidGraphEvents work (before ++ events))
    (running : queue.terminated = false) (_accepted : queue.acceptsBatch events = true)
    (memberships : queue.GroupMembershipOrder) (cancelled : queue.CancellationsRetired)
    : ∃ added : List ObjectPublication,
        added.map Prod.snd
          = (queue.handleGraphEvents events).2.flatMap WorkQueueEvent.objectValues
        ∧ (queue.handleGraphEvents events).1.PublicationInventory
            (ObjectValueFrom (before ++ events)) (published ++ added)
        ∧ queue.ReplayClosuresCovered events added (GraphEvent.availableFailures events)
        ∧ StreamReleasePublications work added (queue.handleGraphEvents events).2
        ∧ BlocksFollowRegistrations
            (queue.handleGraphEvents events).1.tasks added
            (queue.handleGraphEvents events).2 := by
  let available := GraphEvent.availableFailures events
  let raw := queue.rawEventReplay events available
  obtain ⟨added, values, final, covered, supported, ordered⟩ :=
    inventory.rawEventReplay_bufferedCoverage_ofMatching
      (available := available) generated accounted links settled children
      events valid memberships cancelled
      (fun _ _ source => valid.objectValue_not_availableFailure
        (List.subset_append_right before events) source)
  rw [State.handleGraphEvents_eq_rawEventReplay queue events]
  simp only [running, Bool.false_eq_true, ↓reduceIte]
  change ∃ added, _
  split
  · have control : StreamReleasePublications work [] [.workQueueTermination] :=
      .of_noGroupSuccess (by intros; simp)
    refine ⟨added, ?_, ⟨final.unique, final.provenance, final.stored⟩, covered, ?_, ?_⟩
    · simpa only [List.flatMap_append, List.flatMap_singleton,
        WorkQueueEvent.objectValues, List.append_nil] using values
    · simpa only [List.append_nil] using supported.append control values
    · have terminal : BlocksFollowRegistrations raw.1.tasks [] [.workQueueTermination] :=
        (BlocksFollowRegistrations.nil _ []).control rfl
      simpa only [List.append_nil] using ordered.append terminal
        (by simpa only [List.length_map] using congrArg List.length values)
  · exact ⟨added, values, final, covered, supported, ordered⟩

/-- Each actual input batch uses its own consecutive slice of one publication ledger.
`queue` and `batches` determine each segment's length and next queue. Within that segment,
`ReplayClosuresCovered` fixes all source-handler slices; batching chooses no new labels.
-/
def State.BatchClosuresCovered (queue : State) (batches : List (List GraphEvent))
    (published : List ObjectPublication)
    : Prop :=
  match batches with
  | [] => True
  | batch :: rest =>
      let next := queue.handleGraphEvents batch
      let count := (next.2.flatMap WorkQueueEvent.objectValues).length
      queue.ReplayClosuresCovered batch (published.take count)
        (GraphEvent.availableFailures batch)
      ∧ BlocksFollowRegistrations next.1.tasks (published.take count) next.2
      ∧ next.1.BatchClosuresCovered rest (published.drop count)

/-- Consecutive batch certificates compose on their exact object-value segments.
Witness: payload erasure supplies the first length; take/drop recover the existing labels.
-/
theorem State.BatchClosuresCovered.cons {queue : State} {batch rest first later}
    (values
      : first.map Prod.snd
        = (queue.handleGraphEvents batch).2.flatMap WorkQueueEvent.objectValues)
    (covered
      : queue.ReplayClosuresCovered batch first (GraphEvent.availableFailures batch))
    (ordered
      : BlocksFollowRegistrations (queue.handleGraphEvents batch).1.tasks
          first (queue.handleGraphEvents batch).2)
    (remaining : (queue.handleGraphEvents batch).1.BatchClosuresCovered rest later)
    : queue.BatchClosuresCovered (batch :: rest) (first ++ later) := by
  have size : first.length
      = ((queue.handleGraphEvents batch).2.flatMap
          WorkQueueEvent.objectValues).length := by
    simpa only [List.length_map] using congrArg List.length values
  simpa only [State.BatchClosuresCovered, ← size, List.take_left, List.drop_left]
    using And.intro covered (And.intro ordered remaining)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
