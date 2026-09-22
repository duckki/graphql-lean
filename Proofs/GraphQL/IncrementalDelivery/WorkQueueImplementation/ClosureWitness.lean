import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ConformanceBatchShape
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ObjectLedgerMatching

/-! Buffered closure certificates use the canonical nonterminal witness's matching. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Keep the source ledger and its atomic prefix interpretation on one witness
-----------------------------------------------------------------------------------------

/-- The same `w` interprets every source-handler slice of one object-publication ledger.
`inputs` determines the concrete batch/handler states. A ledger prefix counted by a
bounded prefix of `w.events` consists of actual publications under `w.matching`.
The same matching also interprets source-item prefixes, including within one handler.
This derived certificate covers buffered/prepared maps, not absent structural tasks.
-/
def BufferedClosureLedger (work : Execution.Work) (inputs : List (List GraphEvent))
    (w : Witness)
    : Prop :=
  ∃ published : List ObjectPublication,
    (initialQueue work).BatchClosuresCovered inputs published
    ∧ ObjectLedgerMatching work inputs w.events w.matching published
    ∧ (∀ index,
        index ≤ w.events.length
        → ∀ occurrence,
            occurrence
              ∈ (published.map Prod.fst).take
                  ((w.events.take index).flatMap normalizedObjectValues).length
            → Published w.matching (w.events.take index) occurrence)
    ∧ ∀ index occurrence,
        occurrence
          ∈ ((inputs.flatten.flatMap GraphEvent.itemPublications).map Prod.fst).take
              ((w.events.take index).flatMap normalizedItemValues).length
        → Published w.matching (w.events.take index) occurrence

/-- Removing the optional terminal marker preserves the closure ledger's interpretation.
Witness: every bounded nonterminal prefix is exactly the full output's corresponding
prefix; retain the same object labels, input slices, and publication matching.
-/
theorem bufferedClosureLedger_nonterminal (work : Execution.Work)
    (inputs : List (List GraphEvent)) (published : List ObjectPublication)
    (matching : PublicationMatching) (failures : FailureCuts)
    (covered : (initialQueue work).BatchClosuresCovered inputs published)
    (ledger
      : ObjectLedgerMatching work inputs
          (((initialQueue work).runNormalized inputs).2.flatten.flatMap publicationAtoms)
          matching published)
    (prefixes
      : ∀ index occurrence,
          occurrence
            ∈ (published.map Prod.fst).take
                (((((initialQueue work).runNormalized inputs).2.flatten.flatMap
                    publicationAtoms).take
                    index).flatMap
                  normalizedObjectValues).length
          → Published matching
              ((((initialQueue work).runNormalized inputs).2.flatten.flatMap
                  publicationAtoms).take
                index) occurrence)
    (itemPrefixes
      : ∀ index occurrence,
          occurrence
            ∈ ((inputs.flatten.flatMap GraphEvent.itemPublications).map Prod.fst).take
                (((((initialQueue work).runNormalized inputs).2.flatten.flatMap
                    publicationAtoms).take
                    index).flatMap
                  normalizedItemValues).length
          → Published matching
              ((((initialQueue work).runNormalized inputs).2.flatten.flatMap
                  publicationAtoms).take
                index) occurrence)
    : BufferedClosureLedger work inputs
        {
          events := (initialQueue work).nonterminalAtoms inputs, matching, failures
        } := by
  refine ⟨published, covered, ?_, ?_, ?_⟩
  · apply ledger.prefix
    exact ⟨_, ((initialQueue work).runNormalized_terminalShape inputs
      (createWorkQueue_terminated _)).symm⟩
  · intro index bounded occurrence member
    have shape := (initialQueue work).runNormalized_terminalShape inputs
      (createWorkQueue_terminated _)
    have same := congrArg (List.take index) shape
    rw [List.take_append_of_le_length bounded] at same
    rw [← same] at member ⊢
    exact prefixes index occurrence member
  · intro index occurrence member
    let bound := min index ((initialQueue work).nonterminalAtoms inputs).length
    have sameTake : ((initialQueue work).nonterminalAtoms inputs).take index
        = ((initialQueue work).nonterminalAtoms inputs).take bound := by
      by_cases within : index ≤ ((initialQueue work).nonterminalAtoms inputs).length
      · rw [show bound = index from Nat.min_eq_left within]
      · have exceeded := Nat.le_of_not_ge within
        rw [show bound = _ from Nat.min_eq_right exceeded,
          List.take_length, List.take_of_length_le exceeded]
    have shape := (initialQueue work).runNormalized_terminalShape inputs
      (createWorkQueue_terminated _)
    have same := congrArg (List.take bound) shape
    rw [List.take_append_of_le_length (Nat.min_le_right _ _)] at same
    change _ ∈ ((inputs.flatten.flatMap GraphEvent.itemPublications).map Prod.fst).take
      (((initialQueue work).nonterminalAtoms inputs |>.take index).flatMap
        normalizedItemValues).length at member
    change Published matching (((initialQueue work).nonterminalAtoms inputs).take index) _
    rw [sameTake, ← same] at member ⊢
    exact itemPrefixes bound occurrence member

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
