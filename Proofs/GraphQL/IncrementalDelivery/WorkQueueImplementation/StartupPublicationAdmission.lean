import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupObjectProducer
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupPublicationAdmission

/-! General object publication admission follows from the common producer-order witness. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Object and item publications jointly exclude cancellation revival
-----------------------------------------------------------------------------------------

/-- The shared object/item certificates supply support for every successful publication.
Witness: each exact object task has a healthy releasing contributor and an earlier
producer; stream readiness and its healthy owner already supply the corresponding facts.
This is derived without assuming event admission or absence of cancellation.
-/
theorem startup_publicationSupport_of_releaseCertificates {work inputs w}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (matched : startup.MatchesWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (history
      : w.events
        = ((State.initialize (Work.fromExecution work) startup)).nonterminalAtoms inputs)
    (ledger
      : BufferedClosureLedger work inputs w
          (State.initialize (Work.fromExecution work) startup))
    (releases : StartupGroupPublicationReleases work startup inputs w)
    (streams : StreamPublicationReady work w)
    : PublicationSupport work w.matching w.events w.failures := by
  intro index event selected value
  cases event with
  | groupValues owner payload =>
      obtain ⟨owners, producer, taskPayload, ref, known, success, member, healthy⟩ :=
        releases.matching_healthy valid started history ledger selected
      refine ⟨owners, producer, taskPayload, ref, known, success, member, healthy, ?_⟩
      intro parent same
      exact releases.producerPublished generated matched valid started history ledger selected
        ⟨owners, taskPayload, same ▸ known⟩
  | streamValues stream values groups children =>
      obtain ⟨item, producer, _, known, ready, owner⟩ :=
        streams index stream values groups children selected
      obtain ⟨supporter, available⟩ := owner.2.1
      exact ⟨[stream.ref], producer, .item stream (.ok (item.item, item.errors)), supporter.ref,
        known, rfl, available.1.2.1, available.2, ready.2.2.1⟩
  | groupSuccess | groupFailure | streamSuccess | streamFailure | workQueueTermination =>
      cases value

/-- Object admission follows from exact ownership, joint support, and fresh occurrences.
Witness: the support induction derives cancellation exclusion from successful provenance
and earlier producers. The existing readiness and owner filter lemmas restore the exact
event-start cutoff; neither cancellation safety nor admission is assumed.
-/
theorem startup_groupPublicationAdmission_of_certificates {work inputs w}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (matched : startup.MatchesWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (history
      : w.events
        = ((State.initialize (Work.fromExecution work) startup)).nonterminalAtoms inputs)
    (ledger
      : BufferedClosureLedger work inputs w
          (State.initialize (Work.fromExecution work) startup))
    (releases : StartupGroupPublicationReleases work startup inputs w)
    (streams : StreamPublicationReady work w)
    (announced : AnnouncedFailures work w)
    (fresh
      : ∀ index owner values,
          w.events[index]? = some (.groupValues owner values)
          → ¬Published w.matching (w.events.take index) (w.matching index))
    : GroupPublicationAdmission work w := by
  have support := startup_publicationSupport_of_releaseCertificates generated startup matched
    valid started history
    ledger releases streams
  have failedPayloads : ∀ cut occurrence, (cut, occurrence) ∈ w.failures
      → ∃ owners producer payload,
          TaskAt work occurrence owners producer payload ∧ payload.failure.isSome = true :=
    fun cut occurrence member => (announced.1.2.2.1 (cut, occurrence) member).2.2
  intro index owner values selected
  obtain ⟨owners, producer, value, known, singleton, ownerRule⟩ :=
    releases.matched_owner generated valid started history ledger selected
  have ready := support.canPublish failedPayloads selected trivial known
    (fresh index owner values selected) (by
      intro address first second same _
      rw [same] at known
      obtain ⟨_, _, _, _, _, _, _, _, impossible⟩ := known
      cases impossible)
  have length : (w.events.take index).length = index :=
    List.length_take_of_le (Nat.le_of_lt (List.getElem?_eq_some_iff.mp selected).1)
  simp only [EventAllowed, length]
  exact ⟨owners, producer, value, singleton, known,
    (canPublish_filter (Nat.le_of_eq length)).mpr ready,
    (owner_filter (Nat.le_of_eq length)).mpr ownerRule⟩

/-- Actual startup objects satisfy full admission on the original shared witness.
The support proof excludes cancellation revival using earlier successful producers;
carried notices and terminal accounting remain separate obligations.
-/
theorem startup_objectAdmissionCertificates {work : Execution.Work}
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
        ∧ PublicationSupport work w.matching w.events w.failures
        ∧ GroupPublicationAdmission work w
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
    accounted, releases, values, ledger, producers, safe, ready, streamAccounted, cuts⟩ :=
    startup_groupReleaseCertificates generated startup matched valid started
  exact ⟨w, history, shape, announced, uncancelled, failures, successes, streamReady, healthy,
    accounted, releases,
    startup_publicationSupport_of_releaseCertificates generated startup matched valid started
      history ledger releases streamReady,
    startup_groupPublicationAdmission_of_certificates generated startup matched valid started
      history ledger releases streamReady announced (fun index owner payload selected =>
        (values index (.groupValues owner payload) selected trivial).2.1),
    values, ledger, producers, safe, ready, streamAccounted, cuts⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
