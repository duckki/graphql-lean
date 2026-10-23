import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupGroupPublicationSupport
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupPublicationMatching

/-! Actual startup raw origins agree with the shared task matching and contributor list. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- The exact raw object value and source-ledger rank identify its task occurrence and
owner refs on the common startup witness. Equal payloads cannot choose an occurrence.
-/
theorem Witness.startup_groupPublication_taskAt {work inputs w index owner payload}
    (startup : InitialStartup)
    (_started : inputsStarted work inputs startup = true)
    (history
      : w.events
        = ((State.initialize (Work.fromExecution work) startup)).nonterminalAtoms inputs)
    (ledger
      : BufferedClosureLedger work inputs w
          (State.initialize (Work.fromExecution work) startup))
    (selected : w.events[index]? = some (.groupValues owner payload))
    (origin
      : GroupPublicationOrigin
          {
            active :=
              ((State.initialize (Work.fromExecution work) startup)).initialGroups
              ++ ((State.initialize (Work.fromExecution work) startup)).initialStreams
          }
          (((State.initialize (Work.fromExecution work) startup)).rawBatches inputs).2
          index owner payload)
    : ∃ producer,
        TaskAt work (w.matching index)
          (origin.value.deliveryGroups.map Execution.DeliveryNode.ref) producer
          (.object origin.value.path (.ok (origin.value.data, origin.value.errors))) := by
  obtain ⟨_, _, exactLedger, _⟩ := ledger
  have raw := origin.rawValue_atRank
  dsimp only at raw
  rw [(Witness.startup_rawBatches_canonical startup history selected).2] at raw
  obtain ⟨result, _, same, source⟩ := exactLedger.source_at selected raw
  obtain ⟨owners, producer, known, groups, _⟩ := source
  have refs := taskAt_owners_of_taskGroups known groups
  rw [same] at refs known
  exact ⟨producer, refs ▸ known⟩

/-- Every actual object publication has an available owner of its exact matched task.
Witness: combine raw contributor availability with indexed source-ledger agreement,
retaining the same origin, history, matching, and failure cuts in both arguments.
-/
theorem StartupGroupPublicationReleases.matched_available {work inputs w}
    {startup : InitialStartup}
    (releases : StartupGroupPublicationReleases work startup inputs w)
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (history
      : w.events
        = ((State.initialize (Work.fromExecution work) startup)).nonterminalAtoms inputs)
    (ledger
      : BufferedClosureLedger work inputs w
          (State.initialize (Work.fromExecution work) startup))
    {index owner payload}
    (selected : w.events[index]? = some (.groupValues owner payload))
    : ∃ origin
          : GroupPublicationOrigin
              {
                active :=
                  ((State.initialize (Work.fromExecution work) startup)).initialGroups
                  ++ ((State.initialize (Work.fromExecution work) startup)).initialStreams
              }
              (((State.initialize (Work.fromExecution work) startup)).rawBatches inputs).2
              index owner payload,
        (∃ producer,
          TaskAt work (w.matching index)
            (origin.value.deliveryGroups.map Execution.DeliveryNode.ref) producer
            (.object origin.value.path (.ok (origin.value.data, origin.value.errors))))
        ∧ HealthyOpenOwner work (initialRefs work) w.matching (w.events.take index)
            w.failures (origin.value.deliveryGroups.map Execution.DeliveryNode.ref)
            origin.group := by
  obtain ⟨origin, available⟩ := releases.available valid selected
  exact ⟨origin,
    Witness.startup_groupPublication_taskAt startup started history ledger selected origin,
    available⟩

/-- The exact matched object task succeeds and has a healthy contributing ref.
Witness: indexed full-value agreement and available raw release support. The remaining
`PublicationSupport` clause is earlier publication of the structural producer.
-/
theorem StartupGroupPublicationReleases.matching_healthy {work inputs w}
    {startup : InitialStartup}
    (releases : StartupGroupPublicationReleases work startup inputs w)
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (history
      : w.events
        = ((State.initialize (Work.fromExecution work) startup)).nonterminalAtoms inputs)
    (ledger
      : BufferedClosureLedger work inputs w
          (State.initialize (Work.fromExecution work) startup))
    {index owner values} (selected : w.events[index]? = some (.groupValues owner values))
    : ∃ owners producer payload ref,
        TaskAt work (w.matching index) owners producer payload
        ∧ payload.failure = none
        ∧ ref ∈ owners
        ∧ ¬NodeFailed work w.matching (w.events.take index) w.failures ref := by
  obtain ⟨origin, ⟨producer, known⟩, available⟩ :=
    releases.matched_available valid started history ledger selected
  exact ⟨_, producer, _, origin.group.ref, known, rfl, available.1.2.1, available.2⟩

/-- Healthy actual object release origins share the existing startup witness's matching,
source ledger and mixed cuts. Producer readiness, remapped wire ownership and carried
notice eligibility remain separate from this release-support certificate.
-/
theorem startup_groupReleaseCertificates {work : Execution.Work}
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
        ∧ GroupSuccessesHealthy work w
        ∧ GroupSuccessesAccounted work w
        ∧ StartupGroupPublicationReleases work startup inputs w
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
  obtain ⟨w, history, shape, announced, uncancelled, failures, successes, streamReady, healthy,
    accounted, values, ledger, producers, safe, ready, streamAccounted, streams, cuts,
    causalEq, reportingEq⟩ :=
    startup_groupAccountingCertificates generated startup matched valid started
  exact ⟨w, history, shape, announced, uncancelled, failures, successes, streamReady, healthy,
    accounted, startup_groupPublicationReleases_of_groupHealth generated startup valid started
      history healthy,
    values, ledger, producers, safe, ready, streamAccounted, streams, cuts, causalEq, reportingEq⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
