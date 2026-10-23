import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.MembershipExclusionPersistence
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ReplayValueConservation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ClosureWitness
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.BatchOutputReplay

/-! The common replay ledger permanently excludes published memberships. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Each exact handler slice names registered tasks and clears its new memberships
-----------------------------------------------------------------------------------------

/-- Every label consumed by the raw output is a permanently registered task occurrence.
Witness: split the publication prefix at each raw event's exact object count, then use
that block's subsequence certificate. Equal payload values do not identify occurrences.
-/
theorem BlocksFollowRegistrations.registered {tasks published events}
    (ordered : BlocksFollowRegistrations tasks published events) {publication}
    (member
      : publication ∈ published.take (events.flatMap WorkQueueEvent.objectValues).length)
    : publication.1 ∈ tasks.map Task.occurrence := by
  induction events generalizing published with
  | nil => simp at member
  | cons event rest ih =>
      simp only [List.flatMap_cons, List.length_append, List.take_add] at member
      rcases List.mem_append.mp member with head | tail
      · exact ordered.1.subset (List.mem_map.mpr ⟨publication, head, rfl⟩)
      · exact ih ordered.2 tail

/-- Every object occurrence emitted by a handler has no live membership at its endpoint.
Witness: the full-budget internal drain certificate includes all owner-fold publications;
item handlers add no object offset before draining. Ignored inputs and other event kinds
emit no object values, so their exact consumed label prefix is empty.
-/
theorem State.PreparedMembershipsCleared.handler_membershipAbsent
    {queue : State} {event published publication} {available : List (Occurrence × Nat)}
    (cleared
      : (queue.cacheTaskFailures available).PreparedMembershipsCleared event published
          available)
    (member
      : publication
        ∈ published.take
            ((queue.handleGraphEvent event available).2.1.flatMap
              WorkQueueEvent.objectValues).length)
    : (queue.handleGraphEvent event available).1.TaskMembershipAbsent publication.1 := by
  let current := queue.cacheTaskFailures available
  cases event with
  | taskSuccess occurrence result =>
      change (current.taskSuccess occurrence result available).1.TaskMembershipAbsent publication.1
      change publication ∈ published.take
        ((current.taskSuccess occurrence result available).2.1.flatMap
          WorkQueueEvent.objectValues).length
        at member
      cases found : current.taskNode? occurrence with
      | none => simp [State.taskSuccess, found] at member
      | some node =>
          have ready := cleared node found
          let stored := current.putTaskNode { node with value := some result.value }
          let prepared := (stored.maybeIntegrateWork result.work (some occurrence)).1
          let released := node.task.groups.foldl successGroupStep (prepared, [], {})
          let active := (released.1.startNewWork released.2.2 available).1
          have final := ready.drain active.groupNodes.length (Nat.le_refl _) publication
          rw [current.taskSuccess_eq occurrence result node found available]
          apply final
          simpa only [current.taskSuccess_eq occurrence result node found available,
            State.drainReadyGroups, active, released, prepared, stored] using member
  | streamItems stream items =>
      change (current.streamItems stream items available).1.TaskMembershipAbsent publication.1
      change publication ∈ published.take
        ((current.streamItems stream items available).2.1.flatMap
          WorkQueueEvent.objectValues).length
        at member
      cases active : current.rootStreams.contains stream.ref with
      | false =>
          simp only [State.streamItems_eq, active, Bool.not_false, ite_true, List.flatMap_nil,
            List.length_nil, List.take_zero, List.not_mem_nil] at member
      | true =>
          have final := cleared.drain active
            (current.preparedStreamItems items available).groupNodes.length
            (Nat.le_refl _) publication
          rw [current.streamItems_eq stream items available]
          simp only [active, Bool.not_true, Bool.false_eq_true, ite_false]
          apply final
          simpa only [State.streamItems_eq, active, Bool.not_true, Bool.false_eq_true, ite_false,
            List.flatMap_cons, WorkQueueEvent.objectValues, List.nil_append,
            State.preparedStreamItems, State.drainReadyGroups] using member
  | taskFailure occurrence errors =>
      change publication ∈ published.take
        ((current.taskFailure occurrence errors).2.flatMap WorkQueueEvent.objectValues).length
        at member
      simp only [State.taskFailure_objectValues, List.length_nil, List.take_zero,
        List.not_mem_nil] at member
  | groupFailure failure =>
      simp only [State.handleGraphEvent, State.groupFailure] at member
      split at member
      · simp at member
      · split at member <;> simp [WorkQueueEvent.objectValues] at member
  | streamSuccess stream =>
      change publication ∈ published.take
        ((current.streamSuccess stream).2.flatMap WorkQueueEvent.objectValues).length at member
      simp only [State.streamSuccess] at member
      split at member <;> simp [WorkQueueEvent.objectValues] at member
  | streamFailure stream errors =>
      change publication ∈ published.take
        ((current.streamFailure stream errors).2.flatMap
          WorkQueueEvent.objectValues).length at member
      simp only [State.streamFailure] at member
      split at member <;> simp [WorkQueueEvent.objectValues] at member

-----------------------------------------------------------------------------------------
-- Later source handlers cannot restore any earlier occurrence on this same witness
-----------------------------------------------------------------------------------------

/-- Every consumed label on the supplied replay ledger is permanently registered.
Witness: each handler's block certificate registers its own slice, and subsequent handlers
only extend the permanent registry. No source-validity premise or new ledger is needed.
-/
theorem State.ReplayClosuresCovered.registered {queue : State} {events published}
    {available : List (Occurrence × Nat)}
    (covered : queue.ReplayClosuresCovered events published available)
    : ∀ publication ∈
        published.take
          ((queue.rawEventReplay events available).2.flatMap
            WorkQueueEvent.objectValues).length,
        publication.1
        ∈ (queue.replayGraphEvents events available).tasks.map Task.occurrence := by
  induction events generalizing queue published with
  | nil => simp [State.rawEventReplay]
  | cons event rest ih =>
      intro publication member
      simp only [State.rawEventReplay_cons, List.flatMap_append, List.length_append,
        List.take_add] at member
      rcases List.mem_append.mp member with head | tail
      · have registered :=
          covered.2.2.2.2.2.2.2.2.1.registered
            (by simpa only [List.take_take, Nat.min_self, State.dispatchGraphEvent] using head)
        obtain ⟨task, member, same⟩ := List.mem_map.mp registered
        exact List.mem_map.mpr
          ⟨
            task,
            State.replayGraphEvents_tasks_subset
              (queue.dispatchGraphEvent event available).1 rest available member,
            same
          ⟩
      · exact ih covered.tail publication tail

/-- Every consumed occurrence on a supplied common ledger is absent after replay.
Witness: a handler's drain certificate clears its exact label slice; its block-order
certificate registers those same occurrences. Source-ready registration then preserves
their exclusion through all remaining inputs. No replacement ledger is chosen.
-/
theorem State.ReplayClosuresCovered.membershipsAbsent {queue : State}
    {work before events published}
    {available : List (Occurrence × Nat)}
    (covered : queue.ReplayClosuresCovered events published available)
    (ready : TaskProducersSucceeded work queue.tasks before)
    (ordered : ProducerOrder work (queue.tasks.map Task.occurrence))
    (valid : ValidGraphEvents work (before ++ events))
    : ∀ publication ∈
        published.take
          ((queue.rawEventReplay events available).2.flatMap
            WorkQueueEvent.objectValues).length,
        (queue.replayGraphEvents events available).TaskMembershipAbsent
          publication.1 := by
  induction events generalizing queue before published with
  | nil => simp [State.rawEventReplay]
  | cons event rest ih =>
      have earlier : (before ++ [event]).IsPrefix (before ++ event :: rest) := ⟨rest, by simp⟩
      obtain ⟨matching, fresh, _⟩ := valid.atPrefix earlier
      have next := State.handleGraphEvent_producerOrder ready ordered
        (valid.prefix (List.prefix_append before (event :: rest))) matching fresh available
      have laterValid : ValidGraphEvents work ((before ++ [event]) ++ rest) := by
        simpa only [List.append_assoc, List.singleton_append] using valid
      intro publication member
      simp only [State.rawEventReplay_cons, List.flatMap_append, List.length_append,
        List.take_add] at member
      rcases List.mem_append.mp member with head | tail
      · have inSlice : publication ∈ (published.take
            ((queue.handleGraphEvent event available).2.1.flatMap
              WorkQueueEvent.objectValues).length).take
              ((queue.handleGraphEvent event available).2.1.flatMap
                WorkQueueEvent.objectValues).length := by
          simpa only [List.take_take, Nat.min_self, State.dispatchGraphEvent] using head
        have removed := covered.2.2.2.2.2.2.2.1.handler_membershipAbsent inSlice
        have registered := covered.2.2.2.2.2.2.2.2.1.registered inSlice
        have absent : (queue.dispatchGraphEvent event available).1.TaskMembershipAbsent
            publication.1 := removed
        exact absent.replayGraphEvents_registered registered next.1 next.2 rest
          laterValid available
      · exact ih covered.tail next.1 next.2 laterValid publication tail

/-- The chosen replay ledger excludes published memberships at every source prefix.
Witness: truncate only the source certificate, not its occurrence labels; initialization
supplies producer-ready registration, and the prefix theorem uses source validity alone.
-/
theorem createWorkQueue_replay_membershipsAbsent {work events published}
    {available : List (Occurrence × Nat)}
    (covered
      : (State.initialize (Work.fromExecution work)).ReplayClosuresCovered events
          published available)
    (valid : ValidGraphEvents work events) {before : List GraphEvent}
    (earlier : before.IsPrefix events)
    : ∀ publication ∈
        published.take
          (((State.initialize (Work.fromExecution work)).rawEventReplay before
              available).2.flatMap
            WorkQueueEvent.objectValues).length,
        ((State.initialize (Work.fromExecution work)).replayGraphEvents
          before available).TaskMembershipAbsent
          publication.1 := by
  obtain ⟨after, same⟩ := earlier
  have restricted := State.ReplayClosuresCovered.prefix before after (same.symm ▸ covered)
  exact restricted.membershipsAbsent (createWorkQueue_producerOrder work).1
    (createWorkQueue_producerOrder work).2 (valid.prefix ⟨after, same⟩)

/-- A batch's forwarding controls and terminal flag preserve an existing exclusion. -/
theorem State.TaskMembershipAbsent.handleGraphEvents_registered
    {queue : State} {work before occurrence}
    (absent : queue.TaskMembershipAbsent occurrence)
    (registered : occurrence ∈ queue.tasks.map Task.occurrence)
    (ready : TaskProducersSucceeded work queue.tasks before)
    (ordered : ProducerOrder work (queue.tasks.map Task.occurrence))
    (batch : List GraphEvent) (valid : ValidGraphEvents work (before ++ batch))
    (running : queue.terminated = false)
    : (queue.handleGraphEvents batch).1.TaskMembershipAbsent occurrence := by
  have kept := absent.replayGraphEvents_registered registered ready ordered batch valid
    (GraphEvent.availableFailures batch)
  obtain ⟨terminal, same⟩ := queue.handleGraphEvents_stateCore batch running
  rw [same]
  exact kept

/-- Actual batch replay preserves every earlier registered membership exclusion. -/
theorem State.TaskMembershipAbsent.rawBatches_registered {queue : State}
    {work before occurrence} (absent : queue.TaskMembershipAbsent occurrence)
    (registered : occurrence ∈ queue.tasks.map Task.occurrence)
    (ready : TaskProducersSucceeded work queue.tasks before)
    (ordered : ProducerOrder work (queue.tasks.map Task.occurrence))
    (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work (before ++ batches.flatten))
    (started : queue.batchesStarted batches = true)
    : (queue.rawBatches batches).1.TaskMembershipAbsent occurrence := by
  induction batches generalizing queue before with
  | nil => exact absent
  | cons batch rest ih =>
      obtain ⟨running, _, later⟩ := queue.batchesStarted_cons batch rest started
      have boundary : (before ++ batch).IsPrefix (before ++ (batch :: rest).flatten) :=
        ⟨rest.flatten, by simp [List.append_assoc]⟩
      have firstValid := valid.prefix boundary
      have kept := absent.handleGraphEvents_registered registered ready ordered batch firstValid
        running
      have registry := List.map_subset Task.occurrence
        (queue.handleGraphEvents_tasks_sublist batch).subset registered
      have replayed := queue.replayGraphEvents_producerOrder ready ordered batch firstValid
        (GraphEvent.availableFailures batch)
      obtain ⟨terminal, same⟩ := queue.handleGraphEvents_stateCore batch running
      have next : TaskProducersSucceeded work (queue.handleGraphEvents batch).1.tasks
          (before ++ batch)
          ∧ ProducerOrder work ((queue.handleGraphEvents batch).1.tasks.map Task.occurrence) := by
        rw [same]
        exact replayed
      exact ih kept registry next.1 next.2
        (by simpa only [List.flatten_cons, List.append_assoc] using valid) later

/-- Every consumed label in actual batches remains registered at their actual endpoint. -/
theorem State.BatchClosuresCovered.registered {queue : State} {batches published}
    (covered : queue.BatchClosuresCovered batches published)
    : ∀ publication ∈
        published.take
          ((queue.rawBatches batches).2.flatMap WorkQueueEvent.objectValues).length,
        publication.1 ∈ (queue.rawBatches batches).1.tasks.map Task.occurrence := by
  induction batches generalizing queue published with
  | nil => simp [State.rawBatches]
  | cons batch rest ih =>
      intro publication member
      simp only [State.rawBatches, List.flatMap_append, List.length_append, List.take_add] at member
      rcases List.mem_append.mp member with head | tail
      · have known := covered.2.1.registered
          (by simpa only [List.take_take, Nat.min_self, State.dispatchGraphEvent] using head)
        exact List.map_subset Task.occurrence
          ((queue.handleGraphEvents batch).1.rawBatches_tasks_sublist rest).subset known
      · exact ih covered.2.2 publication tail

/-- The same batch ledger clears every consumed occurrence at the actual batch endpoint. -/
theorem State.BatchClosuresCovered.membershipsAbsent {queue : State}
    {work before batches published}
    (covered : queue.BatchClosuresCovered batches published)
    (ready : TaskProducersSucceeded work queue.tasks before)
    (ordered : ProducerOrder work (queue.tasks.map Task.occurrence))
    (valid : ValidGraphEvents work (before ++ batches.flatten))
    (started : queue.batchesStarted batches = true)
    : ∀ publication ∈
        published.take
          ((queue.rawBatches batches).2.flatMap WorkQueueEvent.objectValues).length,
        (queue.rawBatches batches).1.TaskMembershipAbsent publication.1 := by
  induction batches generalizing queue before published with
  | nil => simp [State.rawBatches]
  | cons batch rest ih =>
      obtain ⟨running, _, later⟩ := queue.batchesStarted_cons batch rest started
      have boundary : (before ++ batch).IsPrefix (before ++ (batch :: rest).flatten) :=
        ⟨rest.flatten, by simp [List.append_assoc]⟩
      have firstValid := valid.prefix boundary
      have replayed := queue.replayGraphEvents_producerOrder ready ordered batch firstValid
        (GraphEvent.availableFailures batch)
      obtain ⟨terminal, same⟩ := queue.handleGraphEvents_stateCore batch running
      have next : TaskProducersSucceeded work (queue.handleGraphEvents batch).1.tasks
          (before ++ batch)
          ∧ ProducerOrder work ((queue.handleGraphEvents batch).1.tasks.map Task.occurrence) := by
        rw [same]
        exact replayed
      intro publication member
      simp only [State.rawBatches, List.flatMap_append, List.length_append, List.take_add] at member
      rcases List.mem_append.mp member with head | tail
      · have inSlice : publication ∈ (published.take
            ((queue.handleGraphEvents batch).2.flatMap WorkQueueEvent.objectValues).length).take
              ((queue.rawEventReplay batch (GraphEvent.availableFailures batch)).2.flatMap
                WorkQueueEvent.objectValues).length := by
          rw [← queue.handleGraphEvents_objectValues batch running]
          simpa only [List.take_take, Nat.min_self, State.dispatchGraphEvent] using head
        have removed := covered.1.membershipsAbsent ready ordered firstValid publication inSlice
        have absent : (queue.handleGraphEvents batch).1.TaskMembershipAbsent publication.1 := by
          rw [same]
          exact removed
        have registered := covered.2.1.registered
          (by simpa only [List.take_take, Nat.min_self, State.dispatchGraphEvent] using head)
        exact absent.rawBatches_registered registered next.1 next.2 rest
          (by simpa only [List.flatten_cons, List.append_assoc] using valid) later
      · exact ih covered.2.2 next.1 next.2
          (by simpa only [List.flatten_cons, List.append_assoc] using valid) later publication tail

/-- Truncating actual batches retains their original occurrence ledger and snapshots. -/
theorem State.BatchClosuresCovered.prefix {queue : State} {published}
    (before after : List (List GraphEvent))
    (covered : queue.BatchClosuresCovered (before ++ after) published)
    : queue.BatchClosuresCovered before published := by
  induction before generalizing queue published with
  | nil => trivial
  | cons batch rest ih => exact ⟨covered.1, covered.2.1, ih covered.2.2⟩

namespace ConformancePlan

/-- The common ledger excludes all published memberships at actual FIFO cuts.
Earlier host batches retain their real states and outputs. The selected FIFO fifo
uses its entire batch's cache snapshot and the corresponding consecutive ledger slice.
-/
theorem BufferedClosureLedger.membershipsAbsent {work inputs w}
    (ledger : BufferedClosureLedger work inputs w)
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    : ∃ published : List ObjectPublication,
        ObjectLedgerMatching work inputs w.events w.matching published
        ∧ ∀ earlier batch later fifo,
            inputs = earlier ++ batch :: later
            → fifo.IsPrefix batch
            → let current := (initialQueue work).replayBatches earlier
              let available := GraphEvent.availableFailures batch
              let offset :=
                (((initialQueue work).rawBatches earlier).2.flatMap
                  WorkQueueEvent.objectValues).length
              let count :=
                ((current.rawEventReplay fifo available).2.flatMap
                  WorkQueueEvent.objectValues).length
              ∀ publication ∈ published.take (offset + count),
                (current.replayGraphEvents fifo available).TaskMembershipAbsent
                  publication.1 := by
  obtain ⟨published, batches, matching, _⟩ := ledger
  let initial := initialQueue work
  have ready := createWorkQueue_producerOrder work
  refine ⟨published, matching, ?_⟩
  intro earlier batch later fifo inputEq prefixPart
  obtain ⟨suffix, batchEq⟩ := prefixPart
  let current := initial.replayBatches earlier
  let available := GraphEvent.availableFailures batch
  let offset := ((initial.rawBatches earlier).2.flatMap WorkQueueEvent.objectValues).length
  let count := ((current.handleGraphEvents batch).2.flatMap WorkQueueEvent.objectValues).length
  let localCount := ((current.rawEventReplay fifo available).2.flatMap
    WorkQueueEvent.objectValues).length
  have batchStarts : initial.batchesStarted (earlier ++ batch :: later) = true := by
    rw [← inputEq, ← inputsStarted_eq_batchesStarted]
    exact started
  rw [State.batchesStarted_append] at batchStarts
  have parts := Bool.and_eq_true_iff.mp batchStarts
  have running := (current.batchesStarted_cons batch later parts.2).1
  have priorValid : ValidGraphEvents work earlier.flatten := valid.prefix
    ⟨(batch :: later).flatten, by simp [inputEq]⟩
  have localValid : ValidGraphEvents work (earlier.flatten ++ fifo) := valid.prefix
    ⟨suffix ++ later.flatten, by simp [inputEq, ← batchEq, List.append_assoc]⟩
  have priorLedger := State.BatchClosuresCovered.prefix earlier (batch :: later)
    (inputEq ▸ batches)
  have atBatch := State.BatchClosuresCovered.atBatch earlier batch later (inputEq ▸ batches)
  have priorOrder := initial.rawBatches_producerOrder ready.1 ready.2 earlier
    (by simpa only [List.nil_append] using priorValid) parts.1
  simp only [State.rawBatches_state, List.nil_append] at priorOrder
  have prefixCovered := State.ReplayClosuresCovered.prefix fifo suffix
    (show current.ReplayClosuresCovered (fifo ++ suffix)
      ((published.drop offset).take count) available from by
        rw [batchEq]
        exact atBatch.1)
  have localLe : localCount ≤ count := by
    have same := congrArg (fun events => current.rawEventReplay events available) batchEq.symm
    have append := current.rawEventReplay_append fifo suffix available
    have lengths := congrArg (fun result : State × List WorkQueueEvent =>
      (result.2.flatMap WorkQueueEvent.objectValues).length) (same.trans append)
    have batchValues := congrArg List.length (current.handleGraphEvents_objectValues batch running)
    dsimp only [localCount, count, available]
    simp only [List.flatMap_append, List.length_append] at lengths
    dsimp only [available] at lengths
    omega
  dsimp only
  intro publication member
  change publication ∈ published.take (offset + localCount) at member
  rw [List.take_add] at member
  rcases List.mem_append.mp member with prior | fresh
  · have absent := priorLedger.membershipsAbsent ready.1 ready.2
      (by simpa only [List.nil_append] using priorValid) parts.1 publication prior
    have registered := priorLedger.registered publication prior
    rw [State.rawBatches_state] at absent registered
    exact absent.replayGraphEvents_registered registered priorOrder.1 priorOrder.2 fifo
      localValid available
  · apply prefixCovered.membershipsAbsent priorOrder.1 priorOrder.2 localValid publication
    change publication ∈ ((published.drop offset).take count).take localCount
    rw [List.take_take, Nat.min_eq_left localLe]
    exact fresh

end ConformancePlan

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
