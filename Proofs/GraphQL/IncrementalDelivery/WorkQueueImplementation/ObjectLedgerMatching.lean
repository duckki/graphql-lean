import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RawValueLedger
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PublicationAnnotationOrder

/-! Exact raw-value identities connect the shared matching to contributor-bearing sources. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Preserve full values and the exact output-to-source index, not just wire data
-----------------------------------------------------------------------------------------

/-- One object ledger retains raw contributor-bearing values, their successful source
events, and the shared matching's exact occurrence at each atomic object position.
The history may be a nonterminal prefix of the full output; the ledger is unchanged.
-/
structure ObjectLedgerMatching (work : Execution.Work) (inputs : List (List GraphEvent))
    (events : List Execution.WorkQueueEvent) (matching : PublicationMatching)
    (published : List ObjectPublication)
    : Prop where
  rawValues
    : published.map Prod.snd
      = ((State.initialize (Work.fromExecution work)).rawEventReplay
          inputs.flatten).2.flatMap
          WorkQueueEvent.objectValues
  source
    : ∀ publication ∈ published,
        ∃ result,
          GraphEvent.taskSuccess publication.1 result ∈ inputs.flatten
          ∧ result.value = publication.2
          ∧ (GraphEvent.taskSuccess publication.1 result).MatchesWork work
  atObject
    : ∀ index group values,
        events[index]? = some (.groupValues group values)
        → (published.map Prod.fst)[((events.take index).flatMap
                                      normalizedObjectValues).length]?
          = some (matching index)

/-- Restricting the observed output prefix preserves exact object-ledger positions.
Witness: every retained index and strict prefix agree with the larger history.
-/
theorem ObjectLedgerMatching.prefix {work inputs events matching published before}
    (ledger : ObjectLedgerMatching work inputs events matching published)
    (initial : before.IsPrefix events)
    : ObjectLedgerMatching work inputs before matching published := by
  obtain ⟨after, rfl⟩ := initial
  refine ⟨ledger.rawValues, ledger.source, ?_⟩
  intro index group values selected
  have inside := (List.getElem?_eq_some_iff.mp selected).1
  have atFull := (List.getElem?_append_left (l₂ := after) inside).trans selected
  have full := ledger.atObject index group values atFull
  rwa [List.take_append_of_le_length (Nat.le_of_lt inside)] at full

/-- A raw value at an object's output rank has the shared matching's exact source input.
Witness: take both projections of the same indexed ledger entry. Equality of serialized
payloads is never used to select an occurrence or its contributor list.
-/
theorem ObjectLedgerMatching.source_at {work inputs events matching published}
    (ledger : ObjectLedgerMatching work inputs events matching published)
    {index group values value}
    (selected : events[index]? = some (.groupValues group values))
    (raw
      : let count := ((events.take index).flatMap normalizedObjectValues).length
        (((State.initialize (Work.fromExecution work)).rawEventReplay
            inputs.flatten).2.flatMap
          WorkQueueEvent.objectValues)[count]?
        = some value)
    : ∃ result,
        GraphEvent.taskSuccess (matching index) result ∈ inputs.flatten
        ∧ result.value = value
        ∧ (GraphEvent.taskSuccess (matching index) result).MatchesWork work := by
  have occurrence := ledger.atObject index group values selected
  dsimp only at raw
  rw [← ledger.rawValues] at raw
  rw [List.getElem?_map] at raw occurrence
  cases found
        : published[((events.take index).flatMap normalizedObjectValues).length]? with
  | none => simp only [found, Option.map_none, reduceCtorEq] at occurrence
  | some entry =>
      have sameOccurrence : entry.1 = matching index := by
        simpa only [found, Option.map_some, Option.some.injEq] using occurrence
      have sameValue : entry.2 = value := by
        simpa only [found, Option.map_some, Option.some.injEq] using raw
      obtain ⟨result, supplied, fullValue, sourceMatch⟩ :=
        ledger.source entry (List.mem_of_getElem? found)
      rw [sameOccurrence] at supplied sourceMatch
      exact ⟨result, supplied, fullValue.trans sameValue, sourceMatch⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
