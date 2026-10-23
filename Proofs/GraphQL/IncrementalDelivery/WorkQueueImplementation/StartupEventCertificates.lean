import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupStreamAdmission
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupGroupOpenness

/-! Failure controls and stream admission share the actual startup conformance witness. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Actual failed group and stream controls are open, structurally exact and supported by
the same causal and complete diagnostic inventories. Initial reports retain their earlier
causal and reporting cuts; their diagnostic count is not used as a new primitive cause.
-/
theorem startup_failureAdmission_of_announced {work inputs w}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (history
      : w.events
        = (State.initialize (Work.fromExecution work) startup).nonterminalAtoms inputs)
    (announced : AnnouncedFailures work w)
    : FailureAdmission work w := by
  constructor
  · intro index group errors selected
    obtain ⟨atFull, beforeEq⟩ := Witness.startup_event startup history selected
    obtain ⟨dependencies, producer, known⟩ :=
      generated.startup_runNormalized_atomicGroupClosuresLocated startup valid _
        (List.mem_of_getElem? atFull)
    have opened := generated.startup_runNormalized_groupFailureOpenAt startup valid started atFull
    dsimp only at opened
    simp only [State.initializeWithStartup_initialGroups,
      State.initializeWithStartup_initialStreams] at opened
    rw [beforeEq] at opened
    have length : (w.events.take index).length = index :=
      List.length_take_of_le (Nat.le_of_lt (List.getElem?_eq_some_iff.mp selected).1)
    have invalid := announced.1.2.2.2.1 index group errors selected
    have reporting := announced.2.2.2.2
    have counts := reporting.2.2.2.1 index group errors selected
    have failed : NodeFailed work w.matching (w.events.take index) w.failures group.ref :=
      GroupInvalidated.nodeFailed (length.symm ▸ invalid)
    simp only [EventAllowed]
    rw [nodeFailed_filter (Nat.le_refl _), length]
    exact ⟨⟨dependencies, producer, known⟩, opened, failed, counts⟩
  · intro index stream errors selected
    exact startup_streamFailure_allowed generated startup valid history announced selected

/-- Batching, both failure leaves, all failure controls, successful stream controls and
stream wire-owner readiness hold on one actual startup witness. Source closure ledgers,
exact publications, successful-item safety and carried producer support remain available.
Successful group controls, full value/notice admission and terminal accounting are separate.
-/
theorem startup_eventCertificates {work : Execution.Work}
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
        ∧ FailureAdmission work w
        ∧ StreamSuccessAdmission work w
        ∧ StreamPublicationReady work w
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
  obtain ⟨w, history, shape, announced, uncancelled, values, ledger, producers, safe, ready,
    accounted, streams, cuts, causalEq, reportingEq⟩ :=
    startup_failureCertificates generated startup matched valid started
  exact ⟨w, history, shape, announced, uncancelled,
    startup_failureAdmission_of_announced generated startup valid started history announced,
    startup_streamSuccessAdmission_of_successfulItems generated startup matched valid started
      history announced accounted safe cuts causalEq,
    startup_streamPublicationReady_of_certificates generated startup matched
      generated.nodeRefCoherent
      valid started history announced ready safe cuts causalEq,
    values, ledger, producers, safe, ready, accounted, streams, cuts, causalEq, reportingEq⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
