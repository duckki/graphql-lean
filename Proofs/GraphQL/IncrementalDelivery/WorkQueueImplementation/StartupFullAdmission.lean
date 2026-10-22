import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupNoticeContents
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupGroupNoticeAdmission
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupStreamNoticeFreshness
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupPublicationAdmission

/-! All actual startup values and controls satisfy admission on one shared failure witness. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- All stream-value atoms satisfy admission, including both kinds of carried child notice.
Witness: stream readiness supplies the value/owner clauses; actual notice contents and
freshness supply full eligibility, and the combined carrier list has unique refs.
Every premise is an already constructed certificate on the same matching and failure cuts.
-/
theorem startup_streamValueAllowed_of_certificates
    {work inputs w index owner values groups streams}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (matched : startup.MatchesWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (history
      : w.events
        = ((State.initialize (Work.fromExecution work) startup)).nonterminalAtoms inputs)
    (announced : AnnouncedFailures work w)
    (support : PublicationSupport work w.matching w.events w.failures)
    (safe : SuccessfulItemsSafe work inputs.flatten w)
    (accounted : GroupSuccessesAccounted work w)
    (successes : StreamSuccessAdmission work w) (failures : FailureAdmission work w)
    (ready : StreamPublicationReady work w)
    (ledger
      : BufferedClosureLedger work inputs w
          (State.initialize (Work.fromExecution work) startup))
    (objects : GroupPublicationAdmission work w)
    (producers : StreamNoticeProducers work w)
    (selected : w.events[index]? = some (.streamValues owner values groups streams))
    : EventAllowed work (initialRefs work) w.matching (w.events.take index) w.failures
        (.streamValues owner values groups streams) := by
  apply (streamValueAllowed_iff_announcements ready selected).mpr
  refine ⟨startup_itemNoticeRefs_nodup generated startup matched valid started history selected,
    ?_, ?_⟩
  · intro child noticed
    have contents := startup_itemGroupNotice_contents generated startup matched valid started
      history ledger
      objects ready selected noticed
    obtain ⟨dependencies, birth, known⟩ :=
      State.startup_runNormalized_atomicGroupNoticesLocated generated startup valid _
        (List.mem_of_getElem? (Witness.startup_event startup history selected).1) child noticed
    obtain ⟨producer, descriptor, eligible⟩ := startup_groupNotice_canAnnounce generated startup
      matched valid started
      history announced support safe accounted successes failures ready ledger
      contents selected (List.mem_map_of_mem noticed) known
    exact ⟨dependencies, producer, descriptor, eligible⟩
  · intro child noticed
    obtain ⟨producer, descriptor, eligible⟩ := startup_itemStreamNotice_canAnnounce_of_replay
      generated startup valid started history announced support producers selected noticed
    exact ⟨[], producer, descriptor, eligible⟩

/-- Successful group controls satisfy full admission, including both child-notice kinds.
Witness: strict-prefix accounting and healthy open closure combine with actual retained
group contents, full notice eligibility, and combined group/stream ref uniqueness.
-/
theorem startup_groupSuccessAllowed_of_certificates
    {work inputs w index group groups streams} (generated : ExecutedWork work)
    (startup : InitialStartup) (matched : startup.MatchesWork work)
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (history
      : w.events
        = ((State.initialize (Work.fromExecution work) startup)).nonterminalAtoms inputs)
    (announced : AnnouncedFailures work w)
    (support : PublicationSupport work w.matching w.events w.failures)
    (safe : SuccessfulItemsSafe work inputs.flatten w)
    (healthy : GroupSuccessesHealthy work w) (accounted : GroupSuccessesAccounted work w)
    (successes : StreamSuccessAdmission work w) (failures : FailureAdmission work w)
    (ready : StreamPublicationReady work w)
    (ledger
      : BufferedClosureLedger work inputs w
          (State.initialize (Work.fromExecution work) startup))
    (objects : GroupPublicationAdmission work w)
    (producers : StreamNoticeProducers work w)
    (selected : w.events[index]? = some (.groupSuccess group groups streams))
    : EventAllowed work (initialRefs work) w.matching (w.events.take index) w.failures
        (.groupSuccess group groups streams) := by
  apply (startup_groupSuccessAllowed_iff_accounting_and_announcements generated startup valid
    started history healthy selected).mpr
  refine ⟨accounted index group groups streams selected, ?_⟩
  refine ⟨startup_groupCarrierNoticeRefs_nodup generated startup matched valid started history
    selected, ?_, ?_⟩
  · intro child noticed
    have contents := startup_groupGroupNotice_unpublished generated startup matched valid started
      history ledger
      objects ready selected noticed
    obtain ⟨dependencies, birth, known⟩ :=
      State.startup_runNormalized_atomicGroupNoticesLocated generated startup valid _
        (List.mem_of_getElem? (Witness.startup_event startup history selected).1) child noticed
    obtain ⟨producer, descriptor, eligible⟩ := startup_groupNotice_canAnnounce generated startup
      matched valid started
      history announced support safe accounted successes failures ready ledger
      contents selected (List.mem_map_of_mem noticed) known
    exact ⟨dependencies, producer, descriptor, eligible⟩
  · intro child noticed
    exact startup_groupStreamNotice_canAnnounce_of_replay generated startup valid started history
      announced
      support healthy producers selected noticed

/-- All actual startup nonterminal events satisfy full admission on the original shared
witness. Values and controls retain their exact carried notices, licensed causal failures
and aggregate reporting cuts. Only terminal accounting remains separate.
-/
theorem startup_admissionCertificates {work : Execution.Work}
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
        ∧ PublicationAdmission work w
        ∧ ControlAdmission work w
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
    accounted, releases, support, objects, values, ledger, producers, safe, ready,
    streamAccounted, cuts⟩ := startup_objectAdmissionCertificates generated startup matched valid
      started
  have publications : PublicationAdmission work w := by
    intro index event selected value
    cases event with
    | groupValues owner payload => exact objects index owner payload selected
    | streamValues owner payload groups children =>
        exact startup_streamValueAllowed_of_certificates generated startup matched valid started
          history announced support safe accounted successes failures streamReady ledger objects
          producers selected
    | groupSuccess | groupFailure | streamSuccess | streamFailure | workQueueTermination
      =>
        cases value
  have controls : ControlAdmission work w := by
    intro index event selected nonvalue
    cases event with
    | groupValues | streamValues => exact False.elim (nonvalue trivial)
    | groupSuccess node children streams =>
        exact startup_groupSuccessAllowed_of_certificates generated startup matched valid started
          history announced support safe healthy accounted successes failures streamReady ledger
          objects producers selected
    | groupFailure node errors => exact failures.1 index node errors selected
    | streamSuccess node => exact successes index node selected
    | streamFailure node errors => exact failures.2 index node errors selected
    | workQueueTermination =>
        exact False.elim (((State.initialize (Work.fromExecution work)
          startup)).nonterminalAtoms_noTermination inputs
            (history ▸ List.mem_of_getElem? selected))
  exact ⟨
    w,
    history,
    shape,
    announced,
    uncancelled,
    publications,
    controls,
    failures,
    successes,
    streamReady,
    healthy,
    accounted,
    releases,
    support,
    objects,
    values,
    ledger,
    producers,
    safe,
    ready,
    streamAccounted,
    cuts
  ⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
