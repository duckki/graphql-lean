import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupFailureSafety

/-! Actual startup histories jointly satisfy the batching and both failure leaves. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- The shared startup witness has batching, announced reporting and uncancelled causal
failures. Exact values, successful-item safety, stream readiness, successful stream
accounting, source closure ledgers and carried producer support remain on that witness.
Full value/control admission and terminal accounting are separate obligations.
-/
theorem startup_failureCertificates {work : Execution.Work}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (matched : startup.MatchesWork work) {inputs : List (List GraphEvent)}
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    : let initial := State.initialize (Work.fromExecution work) startup
      ∃ w : Witness,
        w.events = initial.nonterminalAtoms inputs
        ∧ WorkBatching
            (w.events
              ++ if (initial.runNormalized inputs).1.terminated then
                    [.workQueueTermination]
                  else
                    [])
            (initial.runNormalized inputs).2
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
        ∧ BufferedClosureLedger work inputs w initial
        ∧ StreamNoticeProducers work w
        ∧ SuccessfulItemsSafe work inputs.flatten w
        ∧ StreamValuesReady work w
        ∧ StreamSuccessesAccounted work w
        ∧ (∃ streams,
            StreamFailureCuts work
              ((initial.runNormalized inputs).2.flatten.flatMap publicationAtoms) streams
            ∧ w.failures
              = mergeFailureCuts
                  (startup.informativeObjectFailureCuts work inputs) streams
            ∧ w.reported
              = mergeFailureCuts (startup.objectReportingCuts work inputs) streams) := by
  obtain ⟨w, history, shape, announced, values, ledger, producers, safe, ready, accounted,
    streams, cuts, causalEq, reportingEq⟩ :=
    startup_publicationCertificates generated startup matched valid started
  have licensed := startup_informativeFailureWitness generated startup matched valid started
    announced safe cuts causalEq
  refine ⟨w, history, shape, announced, ?_, values, ledger, producers, safe, ready, accounted,
    streams, cuts, causalEq, reportingEq⟩
  intro before cut occurrence after split
  exact (licensed before cut occurrence after split).2.2.2

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
