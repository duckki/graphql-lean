import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupPublicationItemBoundary
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.BatchOutputReplay

/-! Item-leading output prefixes use the actual fixed rejection snapshot. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

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
theorem State.handleGraphEvent_items_before_groupValues_atSnapshot (queue : State)
    (event : GraphEvent) (available : List (Occurrence × Nat)) {index group values}
    (selected
      : (queue.handleGraphEvent event available).2.1[index]?
        = some (.groupValues group values))
    : (((queue.handleGraphEvent event available).2.1.take index).flatMap
        WorkQueueEvent.itemValues)
      = (queue.handleGraphEvent event available).2.1.flatMap
          WorkQueueEvent.itemValues := by
  let cached := queue.cacheTaskFailures available
  cases event with
  | taskSuccess occurrence result =>
      change ((cached.taskSuccess occurrence result available).2.1.take index).flatMap
        WorkQueueEvent.itemValues = (cached.taskSuccess occurrence result available).2.1.flatMap
          WorkQueueEvent.itemValues
      rw [cached.taskSuccess_itemValues occurrence result available]
      exact no_items_prefix (cached.taskSuccess_itemValues occurrence result available) index
  | taskFailure occurrence errors =>
      change ((cached.taskFailure occurrence errors).2.take index).flatMap
        WorkQueueEvent.itemValues = (cached.taskFailure occurrence errors).2.flatMap
          WorkQueueEvent.itemValues
      rw [State.taskFailure_itemValues]
      exact no_items_prefix (cached.taskFailure_itemValues occurrence errors) index
  | streamItems stream items =>
      change (cached.streamItems stream items available).2.1[index]? = _ at selected
      change (((cached.streamItems stream items available).2.1.take index).flatMap
          WorkQueueEvent.itemValues)
        = (cached.streamItems stream items available).2.1.flatMap WorkQueueEvent.itemValues
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
            rw [no_items_prefix (State.drainReadyGroups_itemValues _ available) index,
              List.append_nil]
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

  | groupFailure notice =>
      have member := List.mem_of_getElem? selected
      simp only [State.handleGraphEvent, State.groupFailure] at member
      split at member
      · cases member
      · split at member <;> simp at member

/-- Every indexed handler output includes all that handler's items in its inclusive prefix.
Witness: only item handlers emit items, all in their leading event. Their subsequent
drain is item-free, as are every other handler's outputs.
-/
theorem State.handleGraphEvent_items_through_output_atSnapshot (queue : State)
    (event : GraphEvent) (available : List (Occurrence × Nat)) {index output}
    (selected : (queue.handleGraphEvent event available).2.1[index]? = some output)
    : (((queue.handleGraphEvent event available).2.1.take (index + 1)).flatMap
        WorkQueueEvent.itemValues)
      = (queue.handleGraphEvent event available).2.1.flatMap
          WorkQueueEvent.itemValues := by
  let cached := queue.cacheTaskFailures available
  have noItems {events : List WorkQueueEvent}
      (empty : events.flatMap WorkQueueEvent.itemValues = []) (count : Nat)
      : (events.take count).flatMap WorkQueueEvent.itemValues = [] :=
    List.flatMap_eq_nil_iff.mpr (fun entry member =>
      List.flatMap_eq_nil_iff.mp empty entry (List.mem_of_mem_take member))
  cases event with
  | taskSuccess occurrence result =>
      change ((cached.taskSuccess occurrence result available).2.1.take (index + 1)).flatMap
        WorkQueueEvent.itemValues = (cached.taskSuccess occurrence result available).2.1.flatMap
          WorkQueueEvent.itemValues
      rw [cached.taskSuccess_itemValues occurrence result available]
      exact noItems (cached.taskSuccess_itemValues occurrence result available) _
  | taskFailure occurrence errors =>
      change ((cached.taskFailure occurrence errors).2.take (index + 1)).flatMap
        WorkQueueEvent.itemValues = (cached.taskFailure occurrence errors).2.flatMap
          WorkQueueEvent.itemValues
      rw [State.taskFailure_itemValues]
      exact noItems (cached.taskFailure_itemValues occurrence errors) _
  | streamItems stream items =>
      change (cached.streamItems stream items available).2.1[index]? = _ at selected
      change (((cached.streamItems stream items available).2.1.take (index + 1)).flatMap
                WorkQueueEvent.itemValues)
      = (cached.streamItems stream items available).2.1.flatMap WorkQueueEvent.itemValues
      unfold State.streamItems at selected ⊢
      split at selected
      · simp only [List.getElem?_nil, reduceCtorEq] at selected
      · rename_i active
        simp only [active, Bool.false_eq_true, ite_false, List.take_succ_cons,
          List.flatMap_cons, State.drainReadyGroups_itemValues, List.append_nil]
        rw [noItems (State.drainReadyGroups_itemValues _ available) index, List.append_nil]
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess]
      split <;> simp [WorkQueueEvent.itemValues]
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> simp [WorkQueueEvent.itemValues]

  | groupFailure notice =>
      change ((cached.groupFailure notice).2.take (index + 1)).flatMap WorkQueueEvent.itemValues
        = (cached.groupFailure notice).2.flatMap WorkQueueEvent.itemValues
      have empty : (cached.groupFailure notice).2.flatMap WorkQueueEvent.itemValues = [] := by
        unfold State.groupFailure
        split
        · rfl
        · split <;> simp [WorkQueueEvent.itemValues]
      rw [empty]
      exact noItems empty _

/-- Started actual batches emit exactly their successful source-item sequence. -/
theorem State.rawBatches_itemValues (queue : State) (batches : List (List GraphEvent))
    {work : Execution.Work} {before : List GraphEvent}
    (valid : ValidGraphEvents work (before ++ batches.flatten))
    (started : queue.batchesStarted batches = true)
    : (queue.rawBatches batches).2.flatMap WorkQueueEvent.itemValues
      = (batches.flatten.flatMap GraphEvent.itemPublications).map Prod.snd := by
  induction batches generalizing queue before with
  | nil => rfl
  | cons batch rest ih =>
      obtain ⟨running, accepted, remaining⟩ := queue.batchesStarted_cons batch rest started
      have validBatch : ValidGraphEvents work (before ++ batch) :=
        valid.prefix ⟨rest.flatten, by simp [List.append_assoc]⟩
      have validRest : ValidGraphEvents work ((before ++ batch) ++ rest.flatten) := by
        simpa [List.append_assoc] using valid
      simp only [State.rawBatches, List.flatMap_append,
        queue.handleGraphEvents_itemValues batch validBatch running accepted,
        ih _ validRest remaining, List.flatten_cons, List.map_append]

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
