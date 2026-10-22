import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InformativeObjectFailureSafety

/-! Accepted object failures are safe at their original ordered mixed failure cuts. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

namespace ConformancePlan

/-- Every accepted object failure in `w` is uncancelled under its ordered predecessors.
This is the object-task part of `UncancelledFailures`; stream failures remain separate.
-/
def ObjectFailuresSafe (work : Execution.Work) (w : Witness) : Prop :=
  ∀ before cut address after,
    w.failures = before ++ (cut, .executionGroup address) :: after
    → ¬TaskCancelled work w.matching (w.events.take cut) before (.executionGroup address)

-----------------------------------------------------------------------------------------
-- General item safety closes the mixed causal gap in the actual object-settlement guard
-----------------------------------------------------------------------------------------

/-- Successful-item safety licenses the object-task part of the same mixed inventory.
Witness: recover the exact pre-settlement queue and ordered object ledger. Its accepting
owner guard implies historical health using item safety restricted from the common
witness. Cancellation of the settling object would fail that owner, even when its
successful producer is still buffered. No producer-publication premise is introduced.
-/
theorem objectFailuresSafe_of_successfulItems {work inputs w streams}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (announced : AnnouncedFailures work w)
    (safe : SuccessfulItemsSafe work inputs.flatten w)
    (cuts
      : StreamFailureCuts work
          (((initialQueue work).runNormalized inputs).2.flatten.flatMap publicationAtoms)
          streams)
    (exactCuts
      : let queue := initialQueue work
        let publisher : IncrementalPublisher :=
          { active := queue.initialGroups ++ queue.initialStreams }
        w.failures
        = mergeFailureCuts
            (informativeObjectFailureCuts work
              (queue.eligibleFailureBlocks (queue.sourceRunBlocks publisher inputs).2.2))
            streams)
    : ObjectFailuresSafe work w := by
  exact informativeObjectFailures_uncancelled generated valid started announced safe cuts exactCuts

-----------------------------------------------------------------------------------------
-- The derived safety uses the canonical witness, not a replacement inventory
-----------------------------------------------------------------------------------------

/-- Actual mixed replay has one witness protecting successful items and accepted objects.
Witness: retain the canonical matching and cut partition from the general item theorem,
then discharge object-failure cancellation on those same ordered predecessor cuts.
This projection does not assert stream-failure licensing, admission, or terminal accounting.
-/
theorem objectFailureCertificates {work : Execution.Work}
    {inputs : List (List GraphEvent)} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    : ∃ w : Witness,
        w.events = (initialQueue work).nonterminalAtoms inputs
        ∧ BatchShape work inputs w
        ∧ AnnouncedFailures work w
        ∧ SuccessfulItemsSafe work inputs.flatten w
        ∧ ObjectFailuresSafe work w := by
  obtain ⟨w, history, shape, announced, _, _, _, safe, streams, cuts, exactCuts⟩ :=
    successfulItemCertificates_with_cuts generated valid started
  exact ⟨w, history, shape, announced, safe,
    objectFailuresSafe_of_successfulItems generated valid started announced safe cuts exactCuts⟩

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
