import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureOriginReporting

/-! Every accepted object-failure invalidation has an observable terminal report origin. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Record invalidation at any actual source prefix has a positive report by termination.
Witness: source-prefix induction selects the first relevant accepted failure. Earlier
invalidations reuse their reports; a newly healthy contributor is forced to report by
root exhaustion and cache persistence. Full defer ancestry transports each origin.
This does not assume wire lifecycle, task coverage, or the strengthened terminal law.
-/
theorem terminal_prefixInvalidatedRecord_reported {work inputs} {w : Witness}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (ended : ((initialQueue work).runNormalized inputs).1.terminated = true)
    {before : List GraphEvent} (beforeValid : ValidGraphEvents work before)
    {after : List GraphEvent} (splitInputs : inputs.flatten = before ++ after)
    {node dependencies} (known : GroupRecordAt work node dependencies)
    (invalid
      : GroupRecordInvalidated work
          ((initialQueue work).objectFailureContributions before) node.ref)
    : GroupFailureReported w.events node dependencies := by
  induction beforeValid generalizing after node dependencies with
  | nil => exact False.elim (invalid.nonempty rfl)
  | @append before event beforeValid matching fresh ready ih =>
      have together : inputs.flatten = before ++ event :: after := by
        simpa only [List.append_assoc, List.singleton_append] using splitInputs
      have earlier
          : ∀ other ancestors,
              GroupRecordAt work other ancestors
              → GroupRecordInvalidated work
                  ((initialQueue work).objectFailureContributions before) other.ref
              → GroupFailureReported w.events other ancestors := by
        intro other ancestors record prior
        exact ih together record prior
      rw [State.objectFailureContributions_append] at invalid
      cases event with
      | taskSuccess occurrence result =>
          apply earlier node dependencies known
          simpa only [State.objectFailureContributions, State.objectFailureContribution,
            List.nil_append] using invalid
      | streamItems stream items =>
          apply earlier node dependencies known
          simpa only [State.objectFailureContributions, State.objectFailureContribution,
            List.nil_append] using invalid
      | streamSuccess stream =>
          apply earlier node dependencies known
          simpa only [State.objectFailureContributions, State.objectFailureContribution,
            List.nil_append] using invalid
      | streamFailure stream errors =>
          apply earlier node dependencies known
          simpa only [State.objectFailureContributions, State.objectFailureContribution,
            List.nil_append] using invalid
      | taskFailure occurrence errors =>
          cases found
                : ((initialQueue work).replayGraphEvents before).taskNode? occurrence with
          | none =>
              apply earlier node dependencies known
              simpa only [State.objectFailureContributions, State.objectFailureContribution,
                found, List.nil_append] using invalid
          | some task =>
              cases accepted
                    : ((initialQueue work).replayGraphEvents before).taskHasHealthyOwner
                        task.task with
              | false =>
                  apply earlier node dependencies known
                  simpa only [State.objectFailureContributions, State.objectFailureContribution,
                    found, accepted, Bool.false_eq_true, ↓reduceIte, List.nil_append] using invalid
              | true =>
                  apply terminal_acceptedFailure_reportsRecords generated valid started history
                    together ended found accepted earlier known
                  simpa only [State.objectFailureContributions, State.objectFailureContribution,
                    found, accepted, ↓reduceIte, List.nil_append,
                    List.singleton_append] using invalid

/-- Every record invalidated by the complete accepted inventory has a positive report.
Witness: specialize prefix-origin reporting to the full concrete source history. The
inventory is the guard-selected implementation inventory, not every host failure input.
-/
theorem terminal_invalidatedRecord_reported {work inputs} {w : Witness}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (ended : ((initialQueue work).runNormalized inputs).1.terminated = true)
    {node dependencies} (known : GroupRecordAt work node dependencies)
    (invalid
      : GroupRecordInvalidated work
          ((initialQueue work).objectFailureContributions inputs.flatten) node.ref)
    : GroupFailureReported w.events node dependencies :=
  terminal_prefixInvalidatedRecord_reported generated valid started history ended valid
    (after := []) (by simp) known invalid

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
