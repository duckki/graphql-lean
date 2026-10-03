import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SuccessfulItemSafety
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ConformanceFailureHistory
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamCompletionAccounting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ClosureWitness

/-! General successful-item safety shares the canonical batching and failure witness. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

namespace ConformancePlan

/-- Each carried stream notice has a producer published by its own carrier's position.
`w` fixes the same occurrence matching used for value admission and failure licensing;
the retained descriptor also supplies the stream's original dependencies and producer.
-/
def StreamNoticeProducers (work : Execution.Work) (w : Witness) : Prop :=
  ∀ index event,
    w.events[index]? = some event
    → StreamNoticesSatisfy
        (fun child =>
          ∃ dependencies producer,
            NodeAt work child .stream dependencies (some producer)
            ∧ Published w.matching (w.events.take (index + 1)) producer) event

/-- Each successful stream closure accounts for its items on the shared strict prefix.
The matching is fixed by `w`; accounting holds for any failure inventory because every
contributing item has already published. This is not terminal accounting for other nodes.
-/
def StreamSuccessesAccounted (work : Execution.Work) (w : Witness) : Prop :=
  ∀ index stream,
    w.events[index]? = some (.streamSuccess stream)
    → ∀ failures, NodeAccounted work w.matching (w.events.take index) failures stream.ref

/-- Every stream value has its exact item task and full publication readiness.
The same `w` supplies fresh occurrence labels, producer/predecessor publications, and
cancellation exclusion. Owner selection and carried notices remain separate obligations.
-/
def StreamValuesReady (work : Execution.Work) (w : Witness) : Prop :=
  ∀ index stream values groups children,
    w.events[index]? = some (.streamValues stream values groups children)
    → ∃ value producer,
        values = [value]
        ∧ TaskAt work (w.matching index) [stream.ref] producer
            (.item stream (.ok (value.item, value.errors)))
        ∧ CanPublish work w.matching (w.events.take index) w.failures (w.matching index)
            producer

/-- Every successful source item is uncancelled under the shared historical witness.
`received` identifies actual source successes; `w` retains the same events, matching, and
mixed cuts as the other conformance obligations. No producer-shape restriction remains.
-/
def SuccessfulItemsSafe (work : Execution.Work) (received : List GraphEvent) (w : Witness)
    : Prop :=
  ∀ source index,
    Occurrence.item source index ∈ received.flatMap GraphEvent.successes
    → ¬TaskCancelled work w.matching w.events w.failures (.item source index)

/-- General successful-item safety persists at earlier inputs, outputs, and cut subsets.
Witness: extend any earlier cancellation to the full witness at the same original cut;
its source item remains one of the full source's successful settlements.
-/
theorem SuccessfulItemsSafe.prefix {work received w}
    (safe : SuccessfulItemsSafe work received w)
    {earlier : List GraphEvent} (prior : earlier.IsPrefix received) (count : Nat)
    {failures : FailureCuts} (included : failures.Subset w.failures)
    : SuccessfulItemsSafe work earlier
        { w with events := w.events.take count, failures } := by
  intro source index success cancelled
  have observed : Occurrence.item source index ∈ received.flatMap GraphEvent.successes := by
    obtain ⟨event, member, settled⟩ := List.mem_flatMap.mp success
    exact List.mem_flatMap.mpr ⟨event, prior.subset member, settled⟩
  apply safe source index observed
  have atFull := cancelled.append (w.events.drop count)
  rw [List.take_append_drop] at atFull
  exact atFull.mono included

-----------------------------------------------------------------------------------------
-- One canonical witness protects all successful items, with the original cut partitions
-----------------------------------------------------------------------------------------

/-- Generated valid started replay has one witness with general successful-item safety.
Witness: retain exact source-label prefixes in the joint publication matching, construct
the original mixed announced inventory, and apply output-position induction. Only the
optional terminal suffix is removed. This closes successful-item safety, not accepted
failure licensing, full event admission, or terminal task/node accounting. Successful
stream closures retain strict-prefix item accounting, and stream values retain full
publication readiness on this same matching. The buffered/prepared closure ledger is
retained too, together with each carried stream's producer publication. Ownership, full
carried-notice eligibility, and structural task accounting remain separate.
-/
theorem successfulItemCertificates_with_closureLedger {work : Execution.Work}
    {inputs : List (List GraphEvent)} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    : ∃ w : Witness,
        w.events = (initialQueue work).nonterminalAtoms inputs
        ∧ BatchShape work inputs w
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
  let queue := initialQueue work
  let publisher : IncrementalPublisher :=
    { active := queue.initialGroups ++ queue.initialStreams }
  let objects := sourceObjectFailureCuts 0
    (queue.eligibleFailureBlocks (queue.sourceRunBlocks publisher inputs).2.2)
  let atoms := (queue.runNormalized inputs).2.flatten.flatMap publicationAtoms
  obtain ⟨published, matching, _, values, notices, covered, prefixes, closures,
    objectPrefixes, objectLedger⟩ :=
    createWorkQueue_runNormalized_streamProducerMatching_withClosureLedger generated valid started
  obtain ⟨streams, cuts, announced⟩ :=
    announcedFailures_with_cuts_exists generated valid started matching
  let failures := mergeFailureCuts objects streams
  let w : Witness := { events := queue.nonterminalAtoms inputs, matching, failures }
  have shape := queue.runNormalized_terminalShape inputs (createWorkQueue_terminated _)
  have itemsSafe := generated.publishedItems_safe_mixed valid started cuts
    (mergeFailureCuts_partition objects streams)
    (fun cut occurrence member => (announced.1.2.2.1 (cut, occurrence) member).2.2)
    (fun position event selected value => (values position event selected value).1)
    (fun position event selected stream dependencies producer reference known parent same =>
      createWorkQueue_runNormalized_streamReference_producerPublished generated valid
        matching notices selected reference known same)
    prefixes
  refine ⟨
    w,
    rfl,
    batchShape_holds valid matching failures,
    announced,
    ?_,
    ?_,
    ?_,
    ?_,
    bufferedClosureLedger_nonterminal work inputs published matching failures closures
      objectLedger objectPrefixes prefixes,
    ?_,
    streams,
    cuts,
    rfl
  ⟩
  · intro index event selected value
    have within := (List.getElem?_eq_some_iff.mp selected).1
    have selectedFull : atoms[index]? = some event := by
      rw [show atoms = _ from shape, List.getElem?_append_left within]
      exact selected
    have before : atoms.take index = w.events.take index := by
      rw [show atoms = _ from shape, List.take_append_of_le_length (Nat.le_of_lt within)]
    obtain ⟨source, fresh, ordered⟩ := values index event selectedFull value
    refine ⟨source, ?_, ?_⟩
    · rw [← before]
      exact fresh
    · intro address first second matched less
      rw [← before]
      exact ordered address first second matched less
  · intro index stream selected retained
    have within := (List.getElem?_eq_some_iff.mp selected).1
    have selectedFull : atoms[index]? = some (.streamSuccess stream) := by
      rw [show atoms = _ from shape, List.getElem?_append_left within]
      exact selected
    have accounted := createWorkQueue_runNormalized_streamSuccess_accounted generated valid
      matching (fun index event atEvent value => (values index event atEvent value).1)
      covered selectedFull retained
    rw [shape, List.take_append_of_le_length (Nat.le_of_lt within)] at accounted
    exact accounted
  · intro index stream items groups children selected
    have within := (List.getElem?_eq_some_iff.mp selected).1
    have selectedFull : atoms[index]? = some (.streamValues stream items groups children) := by
      rw [show atoms = _ from shape, List.getElem?_append_left within]
      exact selected
    have before : atoms.take index = w.events.take index := by
      rw [show atoms = _ from shape, List.take_append_of_le_length (Nat.le_of_lt within)]
    obtain ⟨source, fresh, ordered⟩ := values index _ selectedFull trivial
    cases items with
    | nil => cases source
    | cons item rest =>
        cases rest with
        | cons next tail => cases source
        | nil =>
            obtain ⟨owners, producer, known⟩ := source
            refine ⟨item, producer, rfl, (itemTask_owner_nodeAt known).1 ▸ known, ?_⟩
            rw [← before]
            apply (itemTask_canPublish_iff_not_cancelled known fresh ?_ ordered
                    failures).mpr
            · intro cancelled
              have atFull := cancelled.append (atoms.drop index)
              rw [List.take_append_drop] at atFull
              cases matched : matching index with
              | executionGroup address =>
                  rw [matched] at known
                  obtain ⟨_, _, _, _, _, _, _, impossible⟩ := known
                  cases impossible
              | item address ordinal =>
                  exact itemsSafe address ordinal ⟨index, _, selectedFull, trivial, matched⟩
                    (matched ▸ atFull)
            · intro dependencies located parent same
              exact createWorkQueue_runNormalized_streamReference_producerPublished
                generated valid matching notices selectedFull List.mem_cons_self located same
  · intro address ordinal success cancelled
    apply itemsSafe address ordinal (covered _ (valid.itemSuccess_publication success))
    rw [shape]
    exact cancelled.append _
  · intro index event selected
    have within := (List.getElem?_eq_some_iff.mp selected).1
    change index < (queue.nonterminalAtoms inputs).length at within
    have selectedFull : atoms[index]? = some event := by
      rw [show atoms = _ from shape, List.getElem?_append_left within]
      exact selected
    have before : atoms.take (index + 1) = w.events.take (index + 1) := by
      rw [show atoms = _ from shape, List.take_append_of_le_length (by omega)]
    have retained := notices index event selectedFull
    change StreamNoticesSatisfy
      (fun child => ∃ dependencies producer,
        NodeAt work child .stream dependencies (some producer)
        ∧ Published matching (atoms.take (index + 1)) producer) event at retained
    rw [before] at retained
    exact retained

/-- The previous cut-partition interface projects the stronger closure-ledger witness.
Witness: discard only buffered/prepared ledger evidence; matching, item safety, successful
stream accounting, and the original ordered failure cuts are retained unchanged.
-/
theorem successfulItemCertificates_with_cuts {work : Execution.Work}
    {inputs : List (List GraphEvent)} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    : ∃ w : Witness,
        w.events = (initialQueue work).nonterminalAtoms inputs
        ∧ BatchShape work inputs w
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
  obtain ⟨w, history, shape, announced, values, accounted, ready, safe, _, _, cuts⟩ :=
    successfulItemCertificates_with_closureLedger generated valid started
  exact ⟨w, history, shape, announced, values, accounted, ready, safe, cuts⟩

/-- All source items are safe on the same witness as batching and announced failures.
Witness: project the partition-retaining construction. Failure licensing is separate;
this theorem does not replace that obligation with item safety as a source assumption.
-/
theorem successfulItemCertificates {work : Execution.Work}
    {inputs : List (List GraphEvent)} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    : ∃ w : Witness,
        w.events = (initialQueue work).nonterminalAtoms inputs
        ∧ BatchShape work inputs w
        ∧ AnnouncedFailures work w
        ∧ SuccessfulItemsSafe work inputs.flatten w := by
  obtain ⟨w, history, shape, announced, _, _, _, safe, _⟩ :=
    successfulItemCertificates_with_cuts generated valid started
  exact ⟨w, history, shape, announced, safe⟩

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
