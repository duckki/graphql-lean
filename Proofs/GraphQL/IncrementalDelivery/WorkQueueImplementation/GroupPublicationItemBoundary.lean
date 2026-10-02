import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RawCarrierCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RawPublicationClosures

/-! Item producers precede object publications even inside one stream-item handler. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Stream items lead their handler's object outputs
-----------------------------------------------------------------------------------------

/-- A prefix of item-free raw output is also item-free.
Witness: split the full projection at the prefix; an empty concatenation has empty halves.
-/
private theorem no_items_prefix {events : List WorkQueueEvent}
    (empty : events.flatMap WorkQueueEvent.itemValues = []) (index : Nat)
    : (events.take index).flatMap WorkQueueEvent.itemValues = [] := by
  have same := congrArg (List.flatMap WorkQueueEvent.itemValues)
    (List.take_append_drop index events)
  rw [List.flatMap_append, empty] at same
  exact (List.append_eq_nil_iff.mp same).1

/-- Every item emitted by a handler precedes each of that handler's object blocks.
Witness: non-item handlers emit no items. The item handler emits its entire item batch
first, before its item-free group drain, including groups released by those same items.
-/
theorem State.handleGraphEvent_items_before_groupValues (queue : State)
    (event : GraphEvent) {index group values}
    (selected
      : (queue.handleGraphEvent event).2[index]? = some (.groupValues group values))
    : (((queue.handleGraphEvent event).2.take index).flatMap WorkQueueEvent.itemValues)
      = (queue.handleGraphEvent event).2.flatMap WorkQueueEvent.itemValues := by
  cases event with
  | taskSuccess occurrence result =>
      rw [State.handleGraphEvent, queue.taskSuccess_itemValues]
      exact no_items_prefix (queue.taskSuccess_itemValues occurrence result) index
  | taskFailure occurrence errors =>
      rw [State.handleGraphEvent, queue.taskFailure_itemValues]
      exact no_items_prefix (queue.taskFailure_itemValues occurrence errors) index
  | streamItems stream items =>
      change (queue.streamItems stream items).2[index]? = _ at selected
      change (((queue.streamItems stream items).2.take index).flatMap WorkQueueEvent.itemValues)
        = (queue.streamItems stream items).2.flatMap WorkQueueEvent.itemValues
      unfold State.streamItems at selected ⊢
      split at selected
      · simp only [List.getElem?_nil, reduceCtorEq] at selected
      · rename_i active
        simp only [active, Bool.false_eq_true, ite_false]
        cases index with
        | zero => cases selected
        | succ index =>
            simp only [List.take_succ_cons, List.flatMap_cons,
              State.drainReadyGroups_itemValues, List.append_nil]
            rw [no_items_prefix (State.drainReadyGroups_itemValues _) index, List.append_nil]
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess] at selected
      split at selected
      · have impossible := List.mem_of_getElem? selected
        simp at impossible
      · simp at selected
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure] at selected
      split at selected
      · have impossible := List.mem_of_getElem? selected
        simp at impossible
      · simp at selected

-----------------------------------------------------------------------------------------
-- Structural registration identifies the producing source item before that block
-----------------------------------------------------------------------------------------

/-- A raw object block's item-produced owner has its producer in the preceding item prefix.
Witness: recover the actual source handler and adjacent success carrier; its registered
group exposes the producer item. Exact accepted item projection and item-first handling
put every item through that handler strictly before this object block.
-/
theorem ExecutedWork.rawEventReplay_groupValues_itemProducer_prefix
    {work received index group values node dependencies source ordinal}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work received)
    (started : (State.initialize (Work.fromExecution work)).acceptsBatch received = true)
    (selected
      : ((State.initialize (Work.fromExecution work)).rawEventReplay received).2[index]?
        = some (.groupValues group values))
    (known : NodeAt work node .group dependencies (some (.item source ordinal)))
    (sameKey : node.key = group.key)
    : Occurrence.item source ordinal
      ∈ ((received.flatMap GraphEvent.itemPublications).map Prod.fst).take
          (((((State.initialize (Work.fromExecution work)).rawEventReplay received).2.take
              index).flatMap
              WorkQueueEvent.itemValues).length) := by
  let initial := State.initialize (Work.fromExecution work)
  obtain ⟨before, event, after, position, split, atEvent, count⟩ :=
    initial.rawEventReplay_output_projected_at WorkQueueEvent.itemValues received selected
  have prior : (before ++ [event]).IsPrefix received :=
    ⟨after, by simp [split, List.append_assoc]⟩
  have accepted : initial.acceptsBatch (before ++ [event]) = true := by
    apply State.acceptsBatch_prefix (after := after)
    simpa only [split, List.append_assoc, List.singleton_append] using started
  obtain ⟨groups, streams, carrier⟩ :=
    ((initial.replayGraphEvents before).handleGraphEvent_publicationPairs event).next atEvent
  obtain ⟨_, _, retired, _, _⟩ :=
    generated.replayGraphEvents_successfulCarrier_retiredHealthy (valid.prefix prior)
      (State.acceptsBatch_prefix accepted) (List.mem_of_getElem? carrier)
  have success := generated.registered_group_itemProducer_succeeded (valid.prefix prior)
    known (sameKey.symm ▸ retired.1)
  have observed := (valid.prefix prior).itemSuccess_publication success
  have exactItems := initial.rawEventReplay_itemValues (before ++ [event]) accepted
  have size : (((initial.rawEventReplay received).2.take index).flatMap
      WorkQueueEvent.itemValues).length
      = ((before ++ [event]).flatMap GraphEvent.itemPublications).length := by
    rw [count, (initial.replayGraphEvents before).handleGraphEvent_items_before_groupValues
      event atEvent]
    have lengths := congrArg List.length exactItems
    rw [State.rawEventReplay_append] at lengths
    dsimp only at lengths
    rw [State.rawEventReplay_state, State.rawEventReplay_cons] at lengths
    simpa only [show ∀ q : State, q.rawEventReplay [] = (q, []) from fun _ => rfl,
      List.flatMap_append, List.length_append, List.length_map, List.append_nil] using lengths
  change _ ∈ ((received.flatMap GraphEvent.itemPublications).map Prod.fst).take
    ((((initial.rawEventReplay received).2.take index).flatMap WorkQueueEvent.itemValues).length)
  rw [size]
  obtain ⟨later, same⟩ := prior
  rw [← same, List.flatMap_append (xs := before ++ [event]), List.map_append,
    ← List.length_map (f := Prod.fst),
    List.take_left]
  exact observed

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
