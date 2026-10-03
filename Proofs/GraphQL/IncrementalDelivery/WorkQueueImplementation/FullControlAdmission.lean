import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FullPublicationAdmission
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CanonicalGroupStreamFreshness

/-! Every actual nonterminal event satisfies admission on one shared conformance witness. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Successful group completion retains every actual child notice
-----------------------------------------------------------------------------------------

/-- Successful group controls satisfy full admission, including both child-notice kinds.
Witness: strict-prefix accounting and healthy open closure combine with actual retained
group contents, full notice eligibility, and combined group/stream ref uniqueness.
-/
theorem groupSuccessAllowed_of_certificates
    {work inputs w index group groups streams streamCuts} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (announced : AnnouncedFailures work w)
    (support : PublicationSupport work w.matching w.events w.failures)
    (safe : SuccessfulItemsSafe work inputs.flatten w)
    (healthy : GroupSuccessesHealthy work w) (accounted : GroupSuccessesAccounted work w)
    (successes : StreamSuccessAdmission work w) (failures : FailureAdmission work w)
    (ready : StreamPublicationReady work w) (ledger : BufferedClosureLedger work inputs w)
    (objects : GroupPublicationAdmission work w)
    (producers : StreamNoticeProducers work w)
    (cuts
      : StreamFailureCuts work
          (((initialQueue work).runNormalized inputs).2.flatten.flatMap publicationAtoms)
          streamCuts)
    (partition
      : let queue := initialQueue work
        let publisher : IncrementalPublisher :=
          { active := queue.initialGroups ++ queue.initialStreams }
        w.failures.Perm
          (streamCuts
            ++ sourceObjectFailureCuts 0
                (queue.eligibleFailureBlocks
                  (queue.sourceRunBlocks publisher inputs).2.2)))
    (selected : w.events[index]? = some (.groupSuccess group groups streams))
    : EventAllowed work (initialRefs work) w.matching (w.events.take index) w.failures
        (.groupSuccess group groups streams) := by
  apply (groupSuccessAllowed_iff_announcements generated valid started history healthy ledger
    selected).mpr
  refine ⟨groupCarrierNoticeRefs_nodup generated valid started history selected, ?_, ?_⟩
  · intro child noticed
    have contents := groupGroupNotice_unpublished generated valid started history ledger
      objects ready partition selected noticed
    obtain ⟨dependencies, birth, known⟩ :=
      createWorkQueue_runNormalized_atomicGroupNoticesLocated generated valid _
        (List.mem_of_getElem? (Witness.canonical_event history selected).1) child noticed
    obtain ⟨producer, descriptor, eligible⟩ := groupNotice_canAnnounce generated valid started
      history announced support safe accounted successes failures ready ledger cuts partition
      contents selected (List.mem_map_of_mem noticed) known
    exact ⟨dependencies, producer, descriptor, eligible⟩
  · intro child noticed
    exact groupStreamNotice_canAnnounce_of_replay generated valid started history announced
      support healthy producers selected noticed

-----------------------------------------------------------------------------------------
-- All five nonterminal construction leaves share one witness
-----------------------------------------------------------------------------------------

/-- Generated valid started replay has batching, licensed failures, and full event admission.
Witness: retain the existing full-publication witness and discharge successful-group
controls using concrete notice consumption. Only terminal structural node accounting
remains as an independent construction; no scheduler or host premise has been added.
-/
theorem mixed_admissionCertificates {work inputs}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    : ∃ w : Witness,
        w.events = (initialQueue work).nonterminalAtoms inputs
        ∧ BatchShape work inputs w
        ∧ AnnouncedFailures work w
        ∧ UncancelledFailures work w
        ∧ PublicationAdmission work w
        ∧ ControlAdmission work w
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
  obtain ⟨w, history, shape, announced, uncancelled, publications, failures, successes,
    ready, healthy, accounted, ledger, releases, support, producers, objects, safe,
    streams, cuts, exactCuts⟩ := mixed_publicationCertificates generated valid started
  have partition := exactCuts ▸ mergeFailureCuts_partition _ streams
  refine ⟨w, history, shape, announced, uncancelled, publications, ?_, failures, successes,
    ready, healthy, accounted, ledger, releases, support, producers, objects, safe,
    streams, cuts, exactCuts⟩
  apply (controlAdmission_iff_groupSuccess history failures successes).mpr
  intro index group groups streams selected
  exact groupSuccessAllowed_of_certificates generated valid started history announced
    support safe healthy accounted successes failures ready ledger objects producers cuts
    partition selected

/-- Every submitted input satisfying the unchanged premises has an explained actual history.
Witness: all five constructed nonterminal leaves share one matching and failure inventory;
the existing initialization premise completes the abstract explanation. This does not yet
assert terminal accounting for a queue whose concrete terminal flag is true.
-/
theorem mixed_explanation {work inputs} (premises : ReplayPremises work inputs)
    : ∃ w : Witness,
        w.events = (initialQueue work).nonterminalAtoms inputs
        ∧ BatchShape work inputs w
        ∧ Explains work (initialQueue work).initialGroups
            (initialQueue work).initialStreams w.events w.matching w.failures := by
  obtain ⟨w, history, shape, announced, uncancelled, publications, controls, _⟩ :=
    mixed_admissionCertificates premises.generated premises.valid premises.started
  exact ⟨w, history, shape,
    explains premises.initialized announced uncancelled publications controls⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
