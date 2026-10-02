import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamFailureSafety

/-! General generated replay has a licensed failure inventory on its actual history. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Both failure kinds share the original ordered predecessor inventory
-----------------------------------------------------------------------------------------

/-- Object and stream safety together exclude cancellation of every accepted failure.
Witness: the two occurrence constructors exhaust the shared failure inventory; neither
branch changes its predecessor cuts or publication matching.
-/
theorem uncancelledFailures_of_parts {work w}
    (objects : ObjectFailuresSafe work w) (streams : StreamFailuresSafe work w)
    : UncancelledFailures work w := by
  intro before cut occurrence after split
  cases occurrence with
  | executionGroup address => exact objects before cut address after split
  | item address ordinal => exact streams before cut address ordinal after split

/-- Three general construction leaves and item safety retain one canonical witness.
Witness: the general successful-item construction fixes batching, matching, and mixed
cuts; the object and stream arguments license exactly those cuts. Exact fresh ordered
publications, successful stream accounting, full stream publication readiness, and both
cut partitions remain available for the admission proof. Buffered/prepared closure
coverage uses the same publication ledger and matching, with no additional source law.
Full event admission and terminal task/node accounting are not asserted here.
-/
theorem mixed_failureCertificates_with_closureLedger {work : Execution.Work}
    {inputs : List (List GraphEvent)} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    : ∃ w : Witness,
        w.events = (initialQueue work).nonterminalAtoms inputs
        ∧ BatchShape work inputs w
        ∧ AnnouncedFailures work w
        ∧ UncancelledFailures work w
        ∧ (∀ index event,
            w.events[index]? = some event
            → IsValue event
            → PublicationAt work (w.matching index) event
              ∧ ¬Published w.matching (w.events.take index) (w.matching index)
              ∧ ∀ address first second,
                  w.matching index = .item address second
                  → first < second
                  → Published w.matching (w.events.take index) (.item address first))
        ∧ StreamSuccessesAccounted work w
        ∧ StreamValuesReady work w
        ∧ SuccessfulItemsSafe work inputs.flatten w
        ∧ BufferedClosureLedger work inputs w
        ∧ StreamNoticeProducers work w
        ∧ (let queue := initialQueue work
            let publisher : IncrementalPublisher :=
              { active := queue.initialGroups ++ queue.initialStreams }
            let objects :=
              sourceObjectFailureCuts 0
                (queue.eligibleFailureBlocks (queue.sourceRunBlocks publisher inputs).2.2)
            ∃ streams,
              StreamFailureCuts work
                ((queue.runNormalized inputs).2.flatten.flatMap publicationAtoms) streams
              ∧ w.failures = mergeFailureCuts objects streams) := by
  obtain ⟨w, history, shape, announced, values, accounted, ready, safe, closures, notices,
    streams, cuts, exactCuts⟩ :=
    successfulItemCertificates_with_closureLedger generated valid started
  have objects := objectFailuresSafe_of_successfulItems generated valid started
    announced safe cuts exactCuts
  have items := streamFailuresSafe_of_successfulItems generated valid started
    announced safe cuts exactCuts
  exact ⟨w, history, shape, announced, uncancelledFailures_of_parts objects items,
    values, accounted, ready, safe, closures, notices, streams, cuts, exactCuts⟩

/-- The existing cut-retaining interface projects the stronger shared-ledger construction.
Witness: discard only closure-ledger evidence, preserving every licensed failure cut,
publication occurrence, and previously established admission certificate.
-/
theorem mixed_failureCertificates_with_cuts {work : Execution.Work}
    {inputs : List (List GraphEvent)} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    : ∃ w : Witness,
        w.events = (initialQueue work).nonterminalAtoms inputs
        ∧ BatchShape work inputs w
        ∧ AnnouncedFailures work w
        ∧ UncancelledFailures work w
        ∧ (∀ index event,
            w.events[index]? = some event
            → IsValue event
            → PublicationAt work (w.matching index) event
              ∧ ¬Published w.matching (w.events.take index) (w.matching index)
              ∧ ∀ address first second,
                  w.matching index = .item address second
                  → first < second
                  → Published w.matching (w.events.take index) (.item address first))
        ∧ StreamSuccessesAccounted work w
        ∧ StreamValuesReady work w
        ∧ SuccessfulItemsSafe work inputs.flatten w
        ∧ (let queue := initialQueue work
            let publisher : IncrementalPublisher :=
              { active := queue.initialGroups ++ queue.initialStreams }
            let objects :=
              sourceObjectFailureCuts 0
                (queue.eligibleFailureBlocks (queue.sourceRunBlocks publisher inputs).2.2)
            ∃ streams,
              StreamFailureCuts work
                ((queue.runNormalized inputs).2.flatten.flatMap publicationAtoms) streams
              ∧ w.failures = mergeFailureCuts objects streams) := by
  obtain ⟨w, history, shape, announced, uncancelled, values, accounted, ready, safe,
    _, _, cuts⟩ :=
    mixed_failureCertificates_with_closureLedger generated valid started
  exact ⟨w, history, shape, announced, uncancelled, values, accounted, ready, safe, cuts⟩

/-- General mixed replay satisfies batching, announcements, and cancellation exclusion.
Witness: project the shared construction, without a defer-only or producer-shape premise.
-/
theorem mixed_failureCertificates {work : Execution.Work}
    {inputs : List (List GraphEvent)} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    : ∃ w : Witness,
        w.events = (initialQueue work).nonterminalAtoms inputs
        ∧ BatchShape work inputs w
        ∧ AnnouncedFailures work w
        ∧ UncancelledFailures work w := by
  obtain ⟨w, history, shape, announced, uncancelled, _⟩ :=
    mixed_failureCertificates_with_cuts generated valid started
  exact ⟨w, history, shape, announced, uncancelled⟩

/-- Actual mixed replay has a licensed failure witness at its original output cuts.
Witness: join prior announcements and cancellation exclusion from the same construction.
Equal-cut predecessors, ignored object failures, and actual host batching are retained.
-/
theorem mixed_failureWitness_exists {work : Execution.Work}
    {inputs : List (List GraphEvent)} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    : ∃ w : Witness,
        w.events = (initialQueue work).nonterminalAtoms inputs
        ∧ BatchShape work inputs w
        ∧ FailureWitness work (initialKeys work) w.matching w.events w.failures := by
  obtain ⟨w, history, shape, announced, uncancelled⟩ :=
    mixed_failureCertificates generated valid started
  exact ⟨w, history, shape, failureWitness announced uncancelled⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
