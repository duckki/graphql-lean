import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ItemStreamRelease

/-! Raw replay preserves item-stream release support in the source's exact item inventory. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Concatenate inclusive publication support using exact item counts
-----------------------------------------------------------------------------------------

/-- Concatenating outputs retains item-release support under concatenated occurrence labels.
Witness: split carrier indices between the segments; exact earlier item erasure determines
the second segment's offset. A carrier may use its own items, but no later item label.
-/
theorem ItemStreamReleasePublications.append {work first second left right}
    (before : ItemStreamReleasePublications work first left)
    (after : ItemStreamReleasePublications work second right)
    (values : first.map Prod.snd = left.flatMap WorkQueueEvent.itemValues)
    : ItemStreamReleasePublications work (first ++ second) (left ++ right) := by
  have size : first.length = (left.flatMap WorkQueueEvent.itemValues).length := by
    simpa only [List.length_map] using congrArg List.length values
  intro index owner items groups streams atEvent child noticed
  by_cases earlier : index < left.length
  · have atLeft := (List.getElem?_append_left earlier).symm.trans atEvent
    obtain ⟨occurrence, known, source⟩ :=
      before index owner items groups streams atLeft child noticed
    have count : ((left.take (index + 1)).flatMap WorkQueueEvent.itemValues).length
        ≤ first.length := by
      have split := congrArg (fun events : List WorkQueueEvent =>
        (events.flatMap WorkQueueEvent.itemValues).length) (List.take_append_drop (index + 1) left)
      simp only [List.flatMap_append, List.length_append] at split
      omega
    refine ⟨occurrence, known, ?_⟩
    rw [List.take_append_of_le_length (by omega : index + 1 ≤ left.length),
      List.take_append_of_le_length count]
    exact source
  · have later : left.length ≤ index := by omega
    have atRight := (List.getElem?_append_right later).symm.trans atEvent
    obtain ⟨occurrence, known, source⟩ :=
      after (index - left.length) owner items groups streams atRight child noticed
    refine ⟨occurrence, known, ?_⟩
    rw [List.take_append (l₁ := left), List.take_of_length_le (by omega : left.length ≤ index + 1),
      show index + 1 - left.length = index - left.length + 1 by omega,
      List.flatMap_append, List.length_append, ← size, List.take_append (l₁ := first)]
    simp only [List.take_of_length_le (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
      List.map_append]
    exact List.mem_append_right _ source

-----------------------------------------------------------------------------------------
-- Accepted raw replay retains the supplied item order at every release carrier
-----------------------------------------------------------------------------------------

/-- Every accepted raw replay retains item-release support in its exact source item order.
Witness: per-handler producer support and exact item copying shift each later carrier's
inclusive prefix by precisely the number of earlier published input items.
-/
theorem State.rawEventReplay_itemStreamRelease {work : Execution.Work} (queue : State)
    (events : List GraphEvent)
    (matching : ∀ event ∈ events, event.MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    (accepted : State.eventsStarted available queue events = true)
    : ItemStreamReleasePublications work (events.flatMap GraphEvent.itemPublications)
        (queue.rawEventReplay events available).2 := by
  induction events generalizing queue with
  | nil => exact .nil work
  | cons event rest ih =>
      have both : queue.acceptsGraphEvent event = true
          ∧ State.eventsStarted available
              (queue.dispatchGraphEvent event available).1 rest = true := by
        simpa only [State.eventsStarted, Bool.and_eq_true] using accepted
      rw [State.rawEventReplay_cons _ _ _ available, List.flatMap_cons]
      exact (queue.handleGraphEvent_itemStreamRelease event
        (matching event List.mem_cons_self) available both.1).append
        (ih _ (fun next member => matching next (List.mem_cons_of_mem _ member)) both.2)
        (queue.handleGraphEvent_itemValues event both.1 available).symm

/-- Item release support only requires item callbacks to remain executable. Other buffered
callbacks can be ignored without changing source item offsets or release provenance.
-/
theorem State.rawEventReplay_itemStreamRelease_of_eachItemAccepted {work : Execution.Work}
    (queue : State) (events : List GraphEvent)
    (matching : ∀ event ∈ events, event.MatchesWork work)
    (available : List (Occurrence × Nat))
    (accepted
      : ∀ fifo stream items,
          (fifo ++ [GraphEvent.streamItems stream items]).IsPrefix events
          → (queue.replayGraphEvents fifo available).acceptsGraphEvent
              (.streamItems stream items)
            = true)
    : ItemStreamReleasePublications work (events.flatMap GraphEvent.itemPublications)
        (queue.rawEventReplay events available).2 := by
  induction events generalizing queue with
  | nil => exact .nil work
  | cons event rest ih =>
      have next : ∀ fifo stream items,
          (fifo ++ [GraphEvent.streamItems stream items]).IsPrefix rest
          → ((queue.dispatchGraphEvent event available).1.replayGraphEvents
              fifo available).acceptsGraphEvent (.streamItems stream items) = true := by
        intro fifo stream items earlier
        apply accepted (event :: fifo) stream items
        obtain ⟨tail, same⟩ := earlier
        exact ⟨tail, by simp [← same]⟩
      have current : ∀ stream items, event = .streamItems stream items
          → queue.acceptsGraphEvent (.streamItems stream items) = true := by
        intro stream items same
        subst event
        exact accepted [] stream items ⟨rest, rfl⟩
      rw [State.rawEventReplay_cons _ _ _ available, List.flatMap_cons]
      exact (queue.handleGraphEvent_itemStreamRelease_of_itemsStarted event
        (matching event List.mem_cons_self) available current).append
        (ih _ (fun next member => matching next (List.mem_cons_of_mem _ member)) next)
        (queue.handleGraphEvent_itemValues_of_itemsStarted event current available).symm

/-- The real batch wrapper retains the same source item inventory through queue termination.
Witness: accepted event replay supplies release support; a trailing termination event has
no carrier or item payload. The existing start law supplies the open entry state.
-/
theorem State.handleGraphEvents_itemStreamRelease {work : Execution.Work} (queue : State)
    (events : List GraphEvent)
    (matching : ∀ event ∈ events, event.MatchesWork work)
    {before : List GraphEvent} (valid : ValidGraphEvents work (before ++ events))
    (startOpen : queue.terminated = false) (accepted : queue.acceptsBatch events = true)
    : ItemStreamReleasePublications work (events.flatMap GraphEvent.itemPublications)
        (queue.handleGraphEvents events).2 := by
  rw [State.handleGraphEvents_eq_rawEventReplay]
  simp only [startOpen, Bool.false_eq_true, ite_false]
  have support := queue.rawEventReplay_itemStreamRelease_of_eachItemAccepted events matching
    (GraphEvent.availableFailures events) (fun _ _ _ earlier =>
      State.acceptsBatch_streamItems_live valid accepted earlier)
  split
  · have terminal : ItemStreamReleasePublications work [] [.workQueueTermination] :=
      .of_noStreamValues (by simp)
    simpa only [List.append_nil] using support.append terminal
      (queue.rawEventReplay_itemValues_admitted events valid accepted).symm
  · simpa only [List.append_nil] using support

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
