import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RawNoticeCompletion

/-! Notice-ancestor completions retain their exact carrier in full raw source replay. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Preserve the entire strict prefix, including silent source handlers
-----------------------------------------------------------------------------------------

/-- A selected raw output retains its actual source handler and exact strict output prefix.
Witness: recurse by source position, subtracting each preceding handler's output length.
The resulting equality works for every projection simultaneously, not just value counts.
-/
theorem State.rawEventReplay_output_prefix_at (queue : State) (received : List GraphEvent)
    {index output} (selected : (queue.rawEventReplay received).2[index]? = some output)
    : ∃ before event after position,
        received = before ++ event :: after
        ∧ ((queue.replayGraphEvents before).handleGraphEvent event).2[position]?
          = some output
        ∧ (queue.rawEventReplay received).2.take index
          = (queue.rawEventReplay before).2
            ++ ((queue.replayGraphEvents before).handleGraphEvent event).2.take
                position := by
  induction received generalizing queue index with
  | nil => simp [State.rawEventReplay] at selected
  | cons event rest ih =>
      rw [State.rawEventReplay_cons] at selected ⊢
      by_cases earlier : index < (queue.handleGraphEvent event).2.length
      · refine ⟨[], event, rest, index, rfl,
          (List.getElem?_append_left earlier).symm.trans selected, ?_⟩
        rw [List.take_append_of_le_length (Nat.le_of_lt earlier)]
        rfl
      · have later : (queue.handleGraphEvent event).2.length ≤ index := by omega
        obtain ⟨before, next, after, position, same, atEvent, exactPrefix⟩ :=
          ih _ ((List.getElem?_append_right later).symm.trans selected)
        refine ⟨event :: before, next, after, position, by simp [same], atEvent, ?_⟩
        rw [List.take_append, List.take_of_length_le later, exactPrefix,
          State.rawEventReplay_cons, List.append_assoc]
        rfl

-----------------------------------------------------------------------------------------
-- Completion cuts compose without borrowing any later source output
-----------------------------------------------------------------------------------------

/-- A raw group notice completes any already-announced ancestor by its selected carrier.
Witness: locate the exact handler, restrict source validity and acceptance to that prefix,
and transport both notice and completion lists through the same strict-prefix equality.
-/
theorem ExecutedWork.rawEventReplay_groupNoticeAncestor_completed
    {work events index group groups streams child dependencies key}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work events)
    (started : (State.initialize (Work.fromExecution work)).acceptsBatch events = true)
    (selected
      : ((State.initialize (Work.fromExecution work)).rawEventReplay events).2[index]?
        = some (.groupSuccess group groups streams))
    (noticed : child ∈ groups) (known : GroupRecordAt work child dependencies)
    (ancestor : key ∈ dependencies)
    : let initial := State.initialize (Work.fromExecution work)
      let outputs := (initial.rawEventReplay events).2
      key ∈ initial.rootGroups ++ (outputs.take index).flatMap rawGroupNoticeKeys
      → key ∈ (outputs.take (index + 1)).flatMap rawGroupClosureKeys := by
  intro initial outputs announced
  change (initial.rawEventReplay events).2[index]?
    = some (.groupSuccess group groups streams) at selected
  obtain ⟨before, event, after, position, same, carrier, exactPrefix⟩ :=
    initial.rawEventReplay_output_prefix_at events selected
  have prior : (before ++ [event]).IsPrefix events :=
    ⟨after, by simp [same, List.append_assoc]⟩
  have accepted : initial.acceptsBatch before = true := by
    apply State.acceptsBatch_prefix (after := event :: after)
    simpa only [same] using started
  have inclusive : outputs.take (index + 1)
      = (initial.rawEventReplay before).2
        ++ ((initial.replayGraphEvents before).handleGraphEvent event).2.take
          (position + 1) := by
    dsimp only [outputs]
    simp only [List.take_add_one, selected, carrier, Option.toList_some, exactPrefix,
      List.append_assoc]
  rw [inclusive]
  apply generated.handleGraphEvent_groupNoticeAncestor_completed (valid.prefix prior)
    accepted known ancestor carrier noticed
  apply List.mem_append.mpr
  rcases List.mem_append.mp announced with root | earlier
  · exact .inl root
  · exact .inr (List.mem_flatMap.mpr (by
      obtain ⟨output, member, contains⟩ := List.mem_flatMap.mp earlier
      refine ⟨output, ?_, contains⟩
      rw [← inclusive]
      exact List.take_subset_take_left _ (Nat.le_succ index) member))

/-- A raw item notice's already-announced ancestor completes strictly before its carrier.
Witness: source inversion identifies the actual leading item handler. Its earlier-source
completion theorem uses precisely the strict prefix retained by that same inversion.
-/
theorem ExecutedWork.rawEventReplay_itemNoticeAncestor_completed
    {work events index stream values groups streams child dependencies key}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work events)
    (started : (State.initialize (Work.fromExecution work)).acceptsBatch events = true)
    (selected
      : ((State.initialize (Work.fromExecution work)).rawEventReplay events).2[index]?
        = some (.streamValues stream values groups streams))
    (noticed : child ∈ groups) (known : GroupRecordAt work child dependencies)
    (ancestor : key ∈ dependencies)
    : let initial := State.initialize (Work.fromExecution work)
      let outputs := (initial.rawEventReplay events).2
      key ∈ initial.rootGroups ++ (outputs.take index).flatMap rawGroupNoticeKeys
      → key ∈ (outputs.take index).flatMap rawGroupClosureKeys := by
  intro initial outputs announced
  obtain ⟨before, event, after, position, same, carrier, exactPrefix⟩ :=
    initial.rawEventReplay_output_prefix_at events selected
  have prior : (before ++ [event]).IsPrefix events :=
    ⟨after, by simp [same, List.append_assoc]⟩
  have accepted : initial.acceptsBatch before = true := by
    apply State.acceptsBatch_prefix (after := event :: after)
    simpa only [same] using started
  change key ∈ initial.rootGroups
    ++ ((initial.rawEventReplay events).2.take index).flatMap rawGroupNoticeKeys at announced
  change key ∈ ((initial.rawEventReplay events).2.take index).flatMap rawGroupClosureKeys
  rw [exactPrefix] at announced ⊢
  exact generated.handleGraphEvent_itemNoticeAncestor_completed (valid.prefix prior)
    accepted known ancestor carrier noticed announced

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
