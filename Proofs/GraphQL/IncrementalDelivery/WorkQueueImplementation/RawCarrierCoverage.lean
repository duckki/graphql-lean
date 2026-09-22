import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StructuralCarrierCoverage

/-! Structural group contributors are covered at indexed positions of the full raw replay. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Preserve object-prefix counts while recovering the actual source handler
-----------------------------------------------------------------------------------------

/-- Each indexed raw output retains its handler and exact preceding projection count.
Witness: source-list induction subtracts earlier handler lengths while preserving silent
handlers in the source prefix. Counts add independently of event or payload equality.
-/
theorem State.rawEventReplay_output_projected_at {α : Type}
    (project : WorkQueueEvent → List α) (queue : State) (received : List GraphEvent)
    {index output} (selected : (queue.rawEventReplay received).2[index]? = some output)
    : ∃ before event after position,
        received = before ++ event :: after
        ∧ ((queue.replayGraphEvents before).handleGraphEvent event).2[position]?
          = some output
        ∧ (((queue.rawEventReplay received).2.take index).flatMap project).length
          = ((queue.rawEventReplay before).2.flatMap project).length
            + ((((queue.replayGraphEvents before).handleGraphEvent event).2.take
                  position).flatMap
                project).length := by
  induction received generalizing queue index with
  | nil => simp [State.rawEventReplay] at selected
  | cons event rest ih =>
      rw [State.rawEventReplay_cons] at selected ⊢
      by_cases earlier : index < (queue.handleGraphEvent event).2.length
      · refine ⟨[], event, rest, index, rfl, ?_, ?_⟩
        · exact (List.getElem?_append_left earlier).symm.trans selected
        · rw [List.take_append_of_le_length (Nat.le_of_lt earlier)]
          simp [State.rawEventReplay, State.replayGraphEvents]
      · have later : (queue.handleGraphEvent event).2.length ≤ index := by omega
        obtain ⟨before, next, after, position, same, atEvent, count⟩ :=
          ih _ ((List.getElem?_append_right later).symm.trans selected)
        refine ⟨event :: before, next, after, position, by simp [same], atEvent, ?_⟩
        rw [List.take_append, List.take_of_length_le later, List.flatMap_append,
          List.length_append, count, State.rawEventReplay_cons]
        simp only [List.flatMap_append, List.length_append, Nat.add_assoc,
              State.replayGraphEvents, List.foldl_cons]

/-- Each raw output retains its source handler and strict object-publication count.
Witness: specialize the projection-count decomposition to object values.
-/
theorem State.rawEventReplay_output_at (queue : State) (received : List GraphEvent)
    {index output} (selected : (queue.rawEventReplay received).2[index]? = some output)
    : ∃ before event after position,
        received = before ++ event :: after
        ∧ ((queue.replayGraphEvents before).handleGraphEvent event).2[position]?
          = some output
        ∧ (((queue.rawEventReplay received).2.take index).flatMap
            WorkQueueEvent.objectValues).length
          = ((queue.rawEventReplay before).2.flatMap WorkQueueEvent.objectValues).length
            + ((((queue.replayGraphEvents before).handleGraphEvent event).2.take
                  position).flatMap
                WorkQueueEvent.objectValues).length :=
  queue.rawEventReplay_output_projected_at WorkQueueEvent.objectValues received selected

/-- All structural object contributors precede their carrier in the complete raw replay.
Witness: recover the handler's indexed carrier and apply structural coverage to the same
ledger restricted to that source prefix. Exact count equality transports its strict bound.
-/
theorem ExecutedWork.rawEventReplay_groupContributor_covered
    {work events published index group groups streams address owners producer payload}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work events)
    (started : (State.initialize (Work.fromExecution work)).acceptsBatch events = true)
    (covered
      : (State.initialize (Work.fromExecution work)).ReplayClosuresCovered events
          published)
    (selected
      : ((State.initialize (Work.fromExecution work)).rawEventReplay events).2[index]?
        = some (.groupSuccess group groups streams))
    (known : TaskAt work (.executionGroup address) owners producer payload)
    (contributes : group.key ∈ owners)
    : ∃ value,
        (Occurrence.executionGroup address, value)
        ∈ published.take
            ((((State.initialize (Work.fromExecution work)).rawEventReplay events).2.take
                index).flatMap
              WorkQueueEvent.objectValues).length := by
  obtain ⟨before, event, after, position, same, carrier, count⟩ :=
    (State.initialize (Work.fromExecution work)).rawEventReplay_output_at events selected
  have prior : (before ++ [event]).IsPrefix events :=
    ⟨after, by simp [same, List.append_assoc]⟩
  have accepted : (State.initialize (Work.fromExecution work)).acceptsBatch
      (before ++ [event]) = true := by
    apply State.acceptsBatch_prefix (after := after)
    simpa only [same, List.append_assoc, List.singleton_append] using started
  have ledger : (State.initialize (Work.fromExecution work)).ReplayClosuresCovered
      (before ++ [event]) published := by
    apply State.ReplayClosuresCovered.prefix (after := after)
    simpa only [same, List.append_assoc, List.singleton_append] using covered
  rw [count]
  exact generated.successfulCarrier_structuralContributor_covered (valid.prefix prior)
    accepted ledger carrier known contributes

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
