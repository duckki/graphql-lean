import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupObjectProducer
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PublicationSafety

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
theorem publicationSupport_of_releaseCertificates {work inputs w}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (ledger : BufferedClosureLedger work inputs w)
    (releases : GroupPublicationReleases work inputs w)
    (streams : StreamPublicationReady work w)
    : PublicationSupport work w.matching w.events w.failures := by
  intro index event selected value
  cases event with
  | groupValues owner payload =>
      obtain ⟨owners, producer, taskPayload, key, known, success, member, healthy⟩ :=
        releases.matching_healthy valid started history ledger selected
      refine ⟨owners, producer, taskPayload, key, known, success, member, healthy, ?_⟩
      intro parent same
      exact releases.producerPublished generated valid started history ledger selected
        ⟨owners, taskPayload, same ▸ known⟩
  | streamValues stream values groups children =>
      obtain ⟨item, producer, _, known, ready, owner⟩ :=
        streams index stream values groups children selected
      obtain ⟨supporter, available⟩ := owner.2.1
      exact ⟨[stream.key], producer, .item stream (.ok (item.item, item.errors)), supporter.key,
        known, rfl, available.1.2.1, available.2, ready.2.2.1⟩
  | groupSuccess | groupFailure | streamSuccess | streamFailure | workQueueTermination =>
      cases value

/-- Every object atom satisfies the full WorkQueueSemantics event-admission predicate.
`w` fixes the original matching and cuts, including failed-owner wire remapping.
No carried notices occur on object-value atoms; those remain on their following carrier.
-/
def GroupPublicationAdmission (work : Execution.Work) (w : Witness) : Prop :=
  ∀ index owner values,
    w.events[index]? = some (.groupValues owner values)
    → EventAllowed work (initialKeys work) w.matching (w.events.take index) w.failures
        (.groupValues owner values)

/-- Object admission follows from exact ownership, joint support, and fresh occurrences.
Witness: the support induction derives cancellation exclusion from successful provenance
and earlier producers. The existing readiness and owner filter lemmas restore the exact
event-start cutoff; neither cancellation safety nor admission is assumed.
-/
theorem groupPublicationAdmission_of_certificates {work inputs w}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (ledger : BufferedClosureLedger work inputs w)
    (releases : GroupPublicationReleases work inputs w)
    (streams : StreamPublicationReady work w)
    (announced : AnnouncedFailures work w)
    (fresh
      : ∀ index owner values,
          w.events[index]? = some (.groupValues owner values)
          → ¬Published w.matching (w.events.take index) (w.matching index))
    : GroupPublicationAdmission work w := by
  have support := publicationSupport_of_releaseCertificates generated valid started history
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

-----------------------------------------------------------------------------------------
-- Retain the completed object rule on the same licensed mixed replay witness
-----------------------------------------------------------------------------------------

/-- General generated replay now satisfies full object publication admission.
Witness: retain the original mixed matching, freshness, and failure cuts, derive stream
readiness and healthy group releases, and apply the joint support argument. Successful
carrier notices, stream-item notices, and terminal accounting remain separate targets.
-/
theorem mixed_groupPublicationCertificates_with_noticeSafety {work inputs}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    : ∃ w : Witness,
        w.events = (initialQueue work).nonterminalAtoms inputs
        ∧ BatchShape work inputs w
        ∧ AnnouncedFailures work w
        ∧ UncancelledFailures work w
        ∧ FailureAdmission work w
        ∧ StreamSuccessAdmission work w
        ∧ StreamPublicationReady work w
        ∧ GroupSuccessesHealthy work w
        ∧ GroupSuccessesAccounted work w
        ∧ BufferedClosureLedger work inputs w
        ∧ GroupPublicationReleases work inputs w
        ∧ PublicationSupport work w.matching w.events w.failures
        ∧ StreamNoticeProducers work w
        ∧ GroupPublicationAdmission work w
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
    ledger, notices, streams, cuts, exactCuts⟩ :=
    mixed_failureCertificates_with_closureLedger generated valid started
  have streamReady := streamPublicationReady_of_certificates generated generated.nodeKeyCoherent
    valid started history announced ready safe cuts exactCuts
  have healthy := groupSuccessesHealthy_of_successfulItems generated valid started history
    announced safe cuts exactCuts
  have releases := groupPublicationReleases_of_groupHealth generated valid started history healthy
  exact ⟨w, history, shape, announced, uncancelled,
    failureAdmission_of_announced generated valid history announced,
    streamSuccessAdmission_of_successfulItems generated valid started history announced
      accounted safe cuts exactCuts,
    streamReady, healthy,
    fun _ _ _ _ selected => groupSuccess_nodeAccounted generated valid started history ledger
      selected,
    ledger, releases,
    publicationSupport_of_releaseCertificates generated valid started history ledger releases
      streamReady,
    notices,
    groupPublicationAdmission_of_certificates generated valid started history ledger releases
      streamReady announced (fun index owner payload selected =>
        (values index (.groupValues owner payload) selected trivial).2.1),
    safe, streams, cuts, exactCuts⟩

/-- The cut-retaining interface projects the stronger notice-safety construction.
Witness: discard only successful source-item safety; the original matching, exact failure
cuts, publication support, and full object admission remain unchanged.
-/
theorem mixed_groupPublicationCertificates_with_cuts {work inputs}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    : ∃ w : Witness,
        w.events = (initialQueue work).nonterminalAtoms inputs
        ∧ BatchShape work inputs w
        ∧ AnnouncedFailures work w
        ∧ UncancelledFailures work w
        ∧ FailureAdmission work w
        ∧ StreamSuccessAdmission work w
        ∧ StreamPublicationReady work w
        ∧ GroupSuccessesHealthy work w
        ∧ GroupSuccessesAccounted work w
        ∧ BufferedClosureLedger work inputs w
        ∧ GroupPublicationReleases work inputs w
        ∧ PublicationSupport work w.matching w.events w.failures
        ∧ StreamNoticeProducers work w
        ∧ GroupPublicationAdmission work w
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
  obtain ⟨w, history, shape, announced, uncancelled, failure, success, ready, healthy,
    accounted, ledger, releases, support, notices, admitted, _, cuts⟩ :=
    mixed_groupPublicationCertificates_with_noticeSafety generated valid started
  exact ⟨w, history, shape, announced, uncancelled, failure, success, ready, healthy,
    accounted, ledger, releases, support, notices, admitted, cuts⟩

/-- The existing object-admission interface projects the stronger cut-retaining witness.
Witness: discard only explicit cut-partition evidence; all other certificates retain the
same matching and failures. Callers needing exact handler cuts can use the stronger form.
-/
theorem mixed_groupPublicationCertificates {work inputs}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    : ∃ w : Witness,
        w.events = (initialQueue work).nonterminalAtoms inputs
        ∧ BatchShape work inputs w
        ∧ AnnouncedFailures work w
        ∧ UncancelledFailures work w
        ∧ FailureAdmission work w
        ∧ StreamSuccessAdmission work w
        ∧ StreamPublicationReady work w
        ∧ GroupSuccessesHealthy work w
        ∧ GroupSuccessesAccounted work w
        ∧ BufferedClosureLedger work inputs w
        ∧ GroupPublicationReleases work inputs w
        ∧ PublicationSupport work w.matching w.events w.failures
        ∧ StreamNoticeProducers work w
        ∧ GroupPublicationAdmission work w := by
  obtain ⟨w, history, shape, announced, uncancelled, failure, success, ready, healthy,
    accounted, ledger, releases, support, notices, admitted, _⟩ :=
    mixed_groupPublicationCertificates_with_cuts generated valid started
  exact ⟨w, history, shape, announced, uncancelled, failure, success, ready, healthy,
    accounted, ledger, releases, support, notices, admitted⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
