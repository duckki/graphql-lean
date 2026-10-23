import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.BufferedProducerSupport
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PublicationReplay

/-! Source legality for batch-entry callback filtering. Producer support comes from the
entry registry; source stream activation preserves every item and its original FIFO cursor.
-/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.BufferedCallbacks

/-- Filtering at batch entry preserves the original work laws and every stream cursor.
The proof uses registry producers and enqueue-time stream activation, not output equality.
-/
theorem projectBatchAtEntry_work_valid {work : Work}
    (generated : ReferenceWorkQueue.ExecutedWork work) (queue : ReferenceWorkQueue.State)
    (before retained batch : List GraphEvent)
    (support : SourceSupport work queue retained)
    (valid : ReferenceWorkQueue.ValidGraphEvents work retained)
    (raw : ReferenceWorkQueue.ValidGraphEvents work (before ++ batch))
    (included : retained.Sublist before)
    (cursors
      : ∀ key,
          ReferenceWorkQueue.GraphEvent.itemsBefore retained key
          = ReferenceWorkQueue.GraphEvent.itemsBefore before key)
    (streams
      : ∀ event ∈ batch,
          ∀ action,
            event.streamAction = some action → queue.acceptsGraphEvent event = true)
    : ReferenceWorkQueue.ValidGraphEvents work
        (retained ++ projectBatchAtEntry queue batch)
      ∧ ∀ key,
          ReferenceWorkQueue.GraphEvent.itemsBefore
            (retained ++ projectBatchAtEntry queue batch) key
          = ReferenceWorkQueue.GraphEvent.itemsBefore (before ++ batch) key := by
  induction batch generalizing before retained with
  | nil =>
      simpa only [projectBatchAtEntry, List.filter_nil, List.append_nil]
        using And.intro valid cursors
  | cons event rest ih =>
      have laws := raw.atPrefix (before := before) (event := event)
        ⟨rest, by simp only [List.append_assoc, List.singleton_append]⟩
      have tailRaw : ReferenceWorkQueue.ValidGraphEvents work ((before ++ [event]) ++ rest) := by
        simpa only [List.append_assoc, List.singleton_append] using raw
      have tailStreams := fun current member => streams current (List.mem_cons_of_mem _ member)
      cases kept : queue.acceptsGraphEvent event with
      | true =>
          have nextValid := ReferenceWorkQueue.ValidGraphEvents.append valid laws.1
            (fresh_of_sublist laws.2.1 included)
            (support.ready generated laws.1 laws.2.2 kept included cursors)
          have nextCursors : ∀ key,
              ReferenceWorkQueue.GraphEvent.itemsBefore (retained ++ [event]) key
                = ReferenceWorkQueue.GraphEvent.itemsBefore (before ++ [event]) key := by
            intro key
            rw [ReferenceWorkQueue.GraphEvent.itemsBefore_append,
              ReferenceWorkQueue.GraphEvent.itemsBefore_append, cursors key]
          have next := ih (before ++ [event]) (retained ++ [event]) (support.extend [event])
            nextValid tailRaw (included.append (.refl [event])) nextCursors tailStreams
          simpa only [projectBatchAtEntry, List.filter_cons, kept, ↓reduceIte,
            List.append_assoc, List.singleton_append]
            using next
      | false =>
          have noItems (key : Nat)
              : ReferenceWorkQueue.GraphEvent.itemsBefore [event] key = [] := by
            cases event with
            | taskSuccess | taskFailure | streamSuccess | streamFailure | groupFailure =>
                rfl
            | streamItems stream items =>
                have accepted := streams _ List.mem_cons_self _ rfl
                rw [kept] at accepted
                cases accepted
          have nextCursors : ∀ key,
              ReferenceWorkQueue.GraphEvent.itemsBefore retained key
                = ReferenceWorkQueue.GraphEvent.itemsBefore (before ++ [event]) key := by
            intro key
            rw [ReferenceWorkQueue.GraphEvent.itemsBefore_append, noItems, List.append_nil]
            exact cursors key
          have next := ih (before ++ [event]) retained support valid tailRaw
            (included.trans (List.sublist_append_left _ _)) nextCursors tailStreams
          simpa only [projectBatchAtEntry, List.filter_cons, kept, Bool.false_eq_true,
            ↓reduceIte, List.append_assoc, List.singleton_append]
            using next

/-- Retained matching notifications construct source support along their actual cached fold. -/
theorem SourceSupport.replayGraphEvents {work queue before}
    (support : SourceSupport work queue before)
    (generated : ReferenceWorkQueue.ExecutedWork work) (events : List GraphEvent)
    (matching : ∀ event ∈ events, event.MatchesWork work)
    (available : List (WorkQueueSemantics.Occurrence × Nat))
    : SourceSupport work (queue.replayGraphEvents events available)
        (before ++ events) := by
  induction events generalizing queue before with
  | nil => simpa only [ReferenceWorkQueue.State.replayGraphEvents, List.foldl_nil,
      List.append_nil] using support
  | cons event rest ih =>
      have handled := support.handleGraphEvent generated (matching event List.mem_cons_self) available
      have next : SourceSupport work (queue.dispatchGraphEvent event available).1
          (before ++ [event]) := handled.withGroupFailures _
      simpa only [ReferenceWorkQueue.State.replayGraphEvents, List.foldl_cons, List.append_assoc,
        List.singleton_append] using ih next
          (fun current member => matching current (List.mem_cons_of_mem _ member))

/-- Batch termination changes no registry or producer-support observation. -/
theorem SourceSupport.handleGraphEvents {work queue before}
    (support : SourceSupport work queue before)
    (generated : ReferenceWorkQueue.ExecutedWork work) (events : List GraphEvent)
    (matching : ∀ event ∈ events, event.MatchesWork work)
    : SourceSupport work (queue.handleGraphEvents events).1 (before ++ events) := by
  cases ended : queue.terminated with
  | true =>
      rw [queue.handleGraphEvents_after_termination events ended]
      exact support.extend events
  | false =>
      obtain ⟨terminal, same⟩ := queue.handleGraphEvents_stateCore events ended
      rw [same]
      exact (support.replayGraphEvents generated events matching
        (ReferenceWorkQueue.GraphEvent.availableFailures events)).withTerminated terminal

/-- Source legality and exact batch replay derive producer support at the original raw
endpoint, with the retained success prefix. No output equivalence is an input premise.
-/
theorem BatchCallbackFrame.projectBatchAtEntry_source {work queue before batch retained}
    (frame : BatchCallbackFrame work queue before batch)
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (support : SourceSupport work queue retained)
    (valid : ReferenceWorkQueue.ValidGraphEvents work retained)
    (included : retained.Sublist before)
    (cursors
      : ∀ key,
          ReferenceWorkQueue.GraphEvent.itemsBefore retained key
          = ReferenceWorkQueue.GraphEvent.itemsBefore before key)
    : ReferenceWorkQueue.ValidGraphEvents work
        (retained ++ projectBatchAtEntry queue batch)
      ∧ SourceSupport work (queue.handleGraphEvents batch).1
          (retained ++ projectBatchAtEntry queue batch)
      ∧ ∀ key,
          ReferenceWorkQueue.GraphEvent.itemsBefore
            (retained ++ projectBatchAtEntry queue batch) key
          = ReferenceWorkQueue.GraphEvent.itemsBefore (before ++ batch) key := by
  obtain ⟨laws, items⟩ := projectBatchAtEntry_work_valid generated queue before retained batch
    support valid frame.valid included cursors frame.streams
  have next := support.handleGraphEvents generated (projectBatchAtEntry queue batch)
    (fun event member => laws.eachMatches (List.mem_append_right _ member))
  rw [frame.projectBatchAtEntry_exact laws] at next
  exact ⟨laws, next, items⟩

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.BufferedCallbacks
