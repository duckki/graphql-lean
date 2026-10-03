import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NoticeRegistrationReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupPublicationItemBoundary

/-! Item-produced group notices use publications already visible at their carrier. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Every raw handler places its item publications at its first output
-----------------------------------------------------------------------------------------

/-- Every indexed handler output includes all that handler's items in its inclusive prefix.
Witness: only item handlers emit items, all in their leading event. Their subsequent
drain is item-free, as are every other handler's outputs.
-/
theorem State.handleGraphEvent_items_through_output (queue : State)
    (event : GraphEvent) {index output}
    (selected : (queue.handleGraphEvent event).2[index]? = some output)
    : (((queue.handleGraphEvent event).2.take (index + 1)).flatMap
        WorkQueueEvent.itemValues)
      = (queue.handleGraphEvent event).2.flatMap WorkQueueEvent.itemValues := by
  have noItems {events : List WorkQueueEvent}
      (empty : events.flatMap WorkQueueEvent.itemValues = []) (count : Nat)
      : (events.take count).flatMap WorkQueueEvent.itemValues = [] :=
    List.flatMap_eq_nil_iff.mpr (fun entry member =>
      List.flatMap_eq_nil_iff.mp empty entry (List.mem_of_mem_take member))
  cases event with
  | taskSuccess occurrence result =>
      rw [State.handleGraphEvent, queue.taskSuccess_itemValues]
      exact noItems (queue.taskSuccess_itemValues occurrence result) _
  | taskFailure occurrence errors =>
      rw [State.handleGraphEvent, queue.taskFailure_itemValues]
      exact noItems (queue.taskFailure_itemValues occurrence errors) _
  | streamItems stream items =>
      change (queue.streamItems stream items).2[index]? = _ at selected
      change (((queue.streamItems stream items).2.take (index + 1)).flatMap
                WorkQueueEvent.itemValues)
      = (queue.streamItems stream items).2.flatMap WorkQueueEvent.itemValues
      unfold State.streamItems at selected ⊢
      split at selected
      · simp only [List.getElem?_nil, reduceCtorEq] at selected
      · rename_i active
        simp only [active, Bool.false_eq_true, ite_false, List.take_succ_cons,
          List.flatMap_cons, State.drainReadyGroups_itemValues, List.append_nil]
        rw [noItems (State.drainReadyGroups_itemValues _) index, List.append_nil]
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess]
      split <;> simp [WorkQueueEvent.itemValues]
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> simp [WorkQueueEvent.itemValues]

/-- A registered-notice certificate includes each projected carried group ref.
Witness: invert the two notice-bearing constructors and their descriptor-ref maps.
-/
theorem
    _root_.GraphQL.IncrementalDelivery.Execution.WorkQueueEvent.GroupNoticesRegistered.ref
    {registered : NodeRefs}
    {event : WorkQueueEvent} (known : event.GroupNoticesRegistered registered) {ref}
    (noticed : ref ∈ rawGroupNoticeRefs event)
    : ref ∈ registered := by
  cases event <;> try cases noticed
  all_goals
    obtain ⟨group, member, rfl⟩ := List.mem_map.mp noticed
    exact known group member

-----------------------------------------------------------------------------------------
-- The handler-local registry fixes a successful source-item cutoff
-----------------------------------------------------------------------------------------

/-- Every noticed group's item producer belongs to the item prefix through that raw carrier.
Witness: recover the carrier's actual source input, prove registration by the end of that
handler, and use generated region separation to locate its producer in the received prefix.
Accepted item projection and item-first handling then give the exact output-prefix bound.
-/
theorem ExecutedWork.rawEventReplay_groupNotice_itemProducer_prefix
    {work received index output node dependencies source ordinal}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work received)
    (started : (State.initialize (Work.fromExecution work)).acceptsBatch received = true)
    (selected
      : ((State.initialize (Work.fromExecution work)).rawEventReplay received).2[index]?
        = some output)
    (known : NodeAt work node .group dependencies (some (.item source ordinal)))
    (noticed : node.ref ∈ rawGroupNoticeRefs output)
    : Occurrence.item source ordinal
      ∈ ((received.flatMap GraphEvent.itemPublications).map Prod.fst).take
          (((((State.initialize (Work.fromExecution work)).rawEventReplay received).2.take
              (index + 1)).flatMap
              WorkQueueEvent.itemValues).length) := by
  let initial := State.initialize (Work.fromExecution work)
  change (initial.rawEventReplay received).2[index]? = some output at selected
  obtain ⟨before, event, after, position, split, atEvent, count⟩ :=
    initial.rawEventReplay_output_projected_at WorkQueueEvent.itemValues received selected
  have prior : (before ++ [event]).IsPrefix received := ⟨after, by simp [split]⟩
  have beforePrefix : before.IsPrefix received := ⟨event :: after, split.symm⟩
  have accepted : initial.acceptsBatch (before ++ [event]) = true := by
    apply State.acceptsBatch_prefix (after := after)
    simpa only [split, List.append_assoc, List.singleton_append] using started
  have matching := valid.eachMatches (by simp [split] : event ∈ received)
  have registrations := initial.replayGraphEvents_registration
    (createWorkQueue_registration work).1 (createWorkQueue_registration work).2 before
    (fun _ member => (valid.prefix beforePrefix).eachMatches member)
  have refs (events : List GraphEvent) (queue : State) (unique : queue.GroupRefsUnique)
      : (queue.replayGraphEvents events).GroupRefsUnique := by
    induction events generalizing queue with
    | nil => exact unique
    | cons input rest ih => exact ih _ (unique.handleGraphEvent input)
  have registered := ((initial.replayGraphEvents before).handleGraphEvent_groupNoticesRegistered
    (refs before initial (createWorkQueue_groupRefsUnique _)) registrations.1 registrations.2.1
    event matching output (List.mem_of_getElem? atEvent)).ref noticed
  have success := generated.registered_group_itemProducer_succeeded (valid.prefix prior)
    known (by simpa only [State.replayGraphEvents, List.foldl_append, List.foldl_cons,
      List.foldl_nil] using registered)
  have observed := (valid.prefix prior).itemSuccess_publication success
  have exactItems := initial.rawEventReplay_itemValues (before ++ [event]) accepted
  have inclusive : ((((initial.rawEventReplay received).2.take (index + 1)).flatMap
      WorkQueueEvent.itemValues).length)
      = ((initial.rawEventReplay before).2.flatMap WorkQueueEvent.itemValues).length
        + (((((initial.replayGraphEvents before).handleGraphEvent event).2.take
            (position + 1)).flatMap WorkQueueEvent.itemValues).length) := by
    simp only [List.take_add_one, selected, atEvent, Option.toList_some,
      List.flatMap_append, List.flatMap_singleton, List.length_append, count, Nat.add_assoc]
  have size : (((initial.rawEventReplay received).2.take (index + 1)).flatMap
      WorkQueueEvent.itemValues).length
      = ((before ++ [event]).flatMap GraphEvent.itemPublications).length := by
    rw [inclusive, (initial.replayGraphEvents before).handleGraphEvent_items_through_output
      event atEvent]
    have lengths := congrArg List.length exactItems
    rw [State.rawEventReplay_append] at lengths
    dsimp only at lengths
    rw [State.rawEventReplay_state, State.rawEventReplay_cons] at lengths
    simpa only [show ∀ q : State, q.rawEventReplay [] = (q, []) from fun _ => rfl,
      List.flatMap_append, List.length_append, List.length_map, List.append_nil] using lengths
  change _ ∈ ((received.flatMap GraphEvent.itemPublications).map Prod.fst).take
    ((((initial.rawEventReplay received).2.take (index + 1)).flatMap
      WorkQueueEvent.itemValues).length)
  rw [size]
  obtain ⟨later, same⟩ := prior
  rw [← same, List.flatMap_append (xs := before ++ [event]), List.map_append,
    ← List.length_map (f := Prod.fst), List.take_left]
  exact observed

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
