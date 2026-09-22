import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CanonicalItemStreamFreshness
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FreshGroupNoticeAdmission
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.AtomicItemNoticeContents

/-! Both value kinds satisfy full admission on the existing joint conformance witness. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Stream payloads retain their actual child notices rather than dropping them
-----------------------------------------------------------------------------------------

/-- All stream-value atoms satisfy admission, including both kinds of carried child notice.
Witness: stream readiness supplies the value/owner clauses; actual notice contents and
freshness supply full eligibility, and the combined carrier list has unique keys.
Every premise is an already constructed certificate on the same matching and failure cuts.
-/
theorem streamValueAllowed_of_certificates
    {work inputs w index owner values groups streams streamCuts}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (announced : AnnouncedFailures work w)
    (support : PublicationSupport work w.matching w.events w.failures)
    (safe : SuccessfulItemsSafe work inputs.flatten w)
    (accounted : GroupSuccessesAccounted work w)
    (successes : StreamSuccessAdmission work w) (failures : FailureAdmission work w)
    (ready : StreamPublicationReady work w)
    (ledger : BufferedClosureLedger work inputs w)
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
    (selected : w.events[index]? = some (.streamValues owner values groups streams))
    : EventAllowed work (initialKeys work) w.matching (w.events.take index) w.failures
        (.streamValues owner values groups streams) := by
  apply (streamValueAllowed_iff_announcements ready selected).mpr
  refine ⟨itemNoticeKeys_nodup generated valid started history selected, ?_, ?_⟩
  · intro child noticed
    have contents := itemGroupNotice_contents generated valid started history ledger
      objects ready partition selected noticed
    obtain ⟨dependencies, birth, known⟩ :=
      createWorkQueue_runNormalized_atomicGroupNoticesLocated generated valid _
        (List.mem_of_getElem? (Witness.canonical_event history selected).1) child noticed
    obtain ⟨producer, descriptor, eligible⟩ := groupNotice_canAnnounce generated valid started
      history announced support safe accounted successes failures ready ledger cuts partition
      contents selected (List.mem_map_of_mem noticed) known
    exact ⟨dependencies, producer, descriptor, eligible⟩
  · intro child noticed
    obtain ⟨producer, descriptor, eligible⟩ := itemStreamNotice_canAnnounce_of_replay
      generated valid started history announced support producers selected noticed
    exact ⟨[], producer, descriptor, eligible⟩

-----------------------------------------------------------------------------------------
-- Four complete construction leaves now share the exact canonical witness
-----------------------------------------------------------------------------------------

/-- Generated valid started replay has batching, licensed failures, and full value admission.
Witness: retain the previously constructed joint object/item witness and all its auxiliary
certificates; the new stream theorem discharges carried notices without any source law.
Control admission and latent terminal accounting remain independent unfinished branches.
-/
theorem mixed_publicationCertificates {work inputs}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    : ∃ w : Witness,
        w.events = (initialQueue work).nonterminalAtoms inputs
        ∧ BatchShape work inputs w
        ∧ AnnouncedFailures work w
        ∧ UncancelledFailures work w
        ∧ PublicationAdmission work w
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
  obtain ⟨w, history, shape, announced, uncancelled, failures, successes, ready, healthy,
    accounted, ledger, releases, support, producers, objects, safe, streams, cuts, exactCuts⟩ :=
    mixed_groupPublicationCertificates_with_noticeSafety generated valid started
  have partition := exactCuts ▸ mergeFailureCuts_partition _ streams
  refine ⟨
    w,
    history,
    shape,
    announced,
    uncancelled,
    ?_,
    failures,
    successes,
    ready,
    healthy,
    accounted,
    ledger,
    releases,
    support,
    producers,
    objects,
    safe,
    streams,
    cuts,
    exactCuts
  ⟩
  intro index event selected value
  cases event with
  | groupValues owner values => exact objects index owner values selected
  | streamValues owner values groups streams =>
      exact streamValueAllowed_of_certificates generated valid started history announced
        support safe accounted successes failures ready ledger objects producers cuts
        partition selected
  | groupSuccess | groupFailure | streamSuccess | streamFailure | workQueueTermination =>
      cases value

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
