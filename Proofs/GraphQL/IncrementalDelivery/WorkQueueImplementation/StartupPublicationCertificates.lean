import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupConformanceWitness
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupPublicationMatching
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SuccessfulItemCertificates
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupSuccessfulItemSafety
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupStreamProducerReadiness
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupStreamCompletionAccounting

/-! Startup publication and failure certificates share one actual nonterminal witness. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

namespace ConformancePlan

/-- A seeded replay's closure ledger keeps its source state and occurrence matching when
only the final termination marker is removed. This transport accepts the actual initial
queue; it does not replace startup replay by the ordinary initializer.
-/
theorem bufferedClosureLedger_startup_nonterminal {work : Execution.Work}
    {inputs : List (List GraphEvent)} {queue : State}
    (running : queue.terminated = false) {w : Witness}
    (history : w.events = queue.nonterminalAtoms inputs)
    {published : List ObjectPublication}
    (covered : queue.BatchClosuresCovered inputs published)
    (ledger
      : ObjectLedgerMatching work inputs
          ((queue.runNormalized inputs).2.flatten.flatMap publicationAtoms)
          w.matching published queue)
    (prefixes
      : ∀ index occurrence,
          occurrence
            ∈ (published.map Prod.fst).take
                ((((queue.runNormalized inputs).2.flatten.flatMap publicationAtoms).take
                    index).flatMap
                  normalizedObjectValues).length
          → Published w.matching
              (((queue.runNormalized inputs).2.flatten.flatMap publicationAtoms).take
                index) occurrence)
    (itemPrefixes
      : ∀ index occurrence,
          occurrence
            ∈ ((inputs.flatten.flatMap GraphEvent.itemPublications).map Prod.fst).take
                ((((queue.runNormalized inputs).2.flatten.flatMap publicationAtoms).take
                    index).flatMap
                  normalizedItemValues).length
          → Published w.matching
              (((queue.runNormalized inputs).2.flatten.flatMap publicationAtoms).take
                index) occurrence)
    : BufferedClosureLedger work inputs w queue := by
  refine ⟨published, covered, ?_, ?_, ?_⟩
  · apply ledger.prefix
    rw [history]
    exact ⟨_, (queue.runNormalized_terminalShape inputs running).symm⟩
  · intro index bounded occurrence member
    rw [history] at bounded member ⊢
    rw [← queue.nonterminalAtoms_startup_take inputs running bounded] at member ⊢
    exact prefixes index occurrence member
  · intro index occurrence member
    rw [history] at member ⊢
    let bound := min index (queue.nonterminalAtoms inputs).length
    have sameTake : (queue.nonterminalAtoms inputs).take index
        = (queue.nonterminalAtoms inputs).take bound := by
      by_cases within : index ≤ (queue.nonterminalAtoms inputs).length
      · rw [show bound = index from Nat.min_eq_left within]
      · have exceeded := Nat.le_of_not_ge within
        rw [show bound = _ from Nat.min_eq_right exceeded,
          List.take_length, List.take_of_length_le exceeded]
    rw [sameTake, ← queue.nonterminalAtoms_startup_take inputs running
      (cut := bound) (Nat.min_le_right _ _)] at member ⊢
    exact itemPrefixes bound occurrence member

/-- Exact values, closure ledgers, carried stream producers and licensed reporting use
the same startup history and matching. Successful items are uncancelled and stream values
have full publication readiness. Owner/notice admission, causal failure licensing and
terminal accounting remain separate.
-/
theorem startup_publicationCertificates {work : Execution.Work}
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
  dsimp only
  let initial := State.initialize (Work.fromExecution work) startup
  let atoms := (initial.runNormalized inputs).2.flatten.flatMap publicationAtoms
  have running : initial.terminated = false :=
    State.initializeWithStartup_terminated _ startup
  obtain ⟨published, matching, covered, _, _, values, objectPrefixes, itemPrefixes, itemsCovered,
    groupProducers, itemProducers, ledger⟩ :=
    generated.startup_runNormalized_matchingWithLedger startup valid started
  obtain ⟨w, history, sameMatching, shape, announced, streams, cuts, causalEq, reportingEq⟩ :=
    generated.startup_batchShape_and_announcedFailures startup matched valid started matching
  have notices : ∀ index event, atoms[index]? = some event
      → StreamNoticesSatisfy (fun child => ∃ dependencies producer,
          NodeAt work child .stream dependencies (some producer)
          ∧ Published matching (atoms.take (index + 1)) producer) event := by
    intro index event selected
    cases event with
    | groupSuccess group groups children =>
        intro child member
        obtain ⟨dependencies, producer, known, prior⟩ :=
          groupProducers index group groups children selected child member
        exact ⟨dependencies, producer, known, published_take_mono prior (Nat.le_succ _)⟩
    | streamValues stream items groups children =>
        intro child member
        obtain ⟨producer, known, prior⟩ :=
          itemProducers index stream items groups children selected child member
        exact ⟨[], producer, known, prior⟩
    | groupValues | groupFailure | streamSuccess | streamFailure | workQueueTermination =>
        trivial
  have ready : ∀ index event, atoms[index]? = some event
      → ∀ stream dependencies producer, stream.ref ∈ streamReferenceRefs event
        → NodeAt work stream .stream dependencies producer
        → ∀ parent, producer = some parent → Published matching (atoms.take index) parent := by
    intro index event selected stream dependencies producer reference known parent same
    exact generated.startup_streamReference_producerPublished startup valid matching notices
      selected reference known same
  have itemsSafe := generated.startup_publishedItems_safe_mixed startup matched valid started cuts
    (show w.failures.Perm (streams ++ startup.informativeObjectFailureCuts work inputs) by
      rw [causalEq]; exact mergeFailureCuts_partition _ _)
    (fun cut occurrence member => (announced.1.2.2.1 (cut, occurrence) member).2.2)
    (fun index event selected value => (values index event selected value).1)
    ready
    itemPrefixes
  have selectedFull {index : Nat} {event : Execution.WorkQueueEvent}
      (selected : w.events[index]? = some event)
      : atoms[index]? = some event := by
    have within := (List.getElem?_eq_some_iff.mp selected).1
    rw [history] at within selected
    rw [show atoms = _ from initial.runNormalized_terminalShape inputs running,
      List.getElem?_append_left within]
    exact selected
  have prefixEq {index : Nat} (bounded : index ≤ w.events.length)
      : atoms.take index = w.events.take index := by
    rw [history] at bounded ⊢
    exact initial.nonterminalAtoms_startup_take inputs running bounded
  refine ⟨w, history, shape, announced, ?_, ?_, ?_, ?_, ?_, ?_,
    streams, cuts, causalEq, reportingEq⟩
  · intro index event selected value
    obtain ⟨known, fresh, ordered⟩ := values index event (selectedFull selected) value
    have before := prefixEq (Nat.le_of_lt (List.getElem?_eq_some_iff.mp selected).1)
    rw [sameMatching, ← before]
    exact ⟨known, fresh, ordered⟩
  · apply bufferedClosureLedger_startup_nonterminal running history covered
    · simpa only [sameMatching] using ledger
    · simpa only [sameMatching] using objectPrefixes
    · simpa only [sameMatching] using itemPrefixes
  · intro index event selected
    have within := (List.getElem?_eq_some_iff.mp selected).1
    have before := prefixEq (index := index + 1) (by omega)
    rw [sameMatching, ← before]
    exact notices index event (selectedFull selected)
  · intro address ordinal succeeded cancelled
    apply itemsSafe address ordinal (itemsCovered _ (valid.itemSuccess_publication succeeded))
    change TaskCancelled work matching atoms w.failures (.item address ordinal)
    rw [show atoms = _ from initial.runNormalized_terminalShape inputs running,
      ← history, ← sameMatching]
    exact cancelled.append _
  · intro index stream items groups children selected
    have selectedFull := selectedFull selected
    have before := prefixEq (Nat.le_of_lt (List.getElem?_eq_some_iff.mp selected).1)
    obtain ⟨source, fresh, ordered⟩ := values index _ selectedFull trivial
    cases items with
    | nil => cases source
    | cons item rest =>
        cases rest with
        | cons next tail => cases source
        | nil =>
            obtain ⟨owners, producer, known⟩ := source
            refine ⟨item, producer, rfl, ?_, ?_⟩
            · rw [sameMatching]
              exact (itemTask_owner_nodeAt known).1 ▸ known
            · rw [sameMatching, ← before]
              apply (itemTask_canPublish_iff_not_cancelled known fresh ?_ ordered
                      w.failures).mpr
              · intro cancelled
                have atFull := cancelled.append (atoms.drop index)
                rw [List.take_append_drop] at atFull
                cases occurrenceEq : matching index with
                | executionGroup address =>
                    rw [occurrenceEq] at known
                    obtain ⟨_, _, _, _, _, _, _, impossible⟩ := known
                    cases impossible
                | item address ordinal =>
                    exact itemsSafe address ordinal
                      ⟨index, _, selectedFull, trivial, occurrenceEq⟩ (occurrenceEq ▸ atFull)
              · intro dependencies located parent same
                exact ready index _ selectedFull stream dependencies producer List.mem_cons_self
                  located parent same
  · intro index stream selected failures
    have before := prefixEq (Nat.le_of_lt (List.getElem?_eq_some_iff.mp selected).1)
    rw [sameMatching, ← before]
    exact ExecutedWork.startup_streamSuccess_accounted startup generated valid matching
      (fun index event selected value => (values index event selected value).1)
      itemsCovered (selectedFull selected) failures

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
