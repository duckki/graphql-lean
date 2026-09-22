import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamPublicationAdmission

/-! Successful group carriers remain historically healthy on the shared mixed witness. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Every object cut belongs to the actual accepted source ledger
-----------------------------------------------------------------------------------------

/-- Any visible object cut in the mixed inventory is an actual accepted source failure.
Witness: exclude stream-only cuts by payload uniqueness, then project the selected object
cuts to the exact full source ledger. The cutoff may be any output boundary; no admission
or failure licensing is assumed, and ignored settlements are not added to the ledger.
-/
theorem createWorkQueue_mixedFailureCuts_objectsRecorded {work : Execution.Work}
    {inputs : List (List GraphEvent)} {streams failures : FailureCuts}
    (started : inputsStarted work inputs = true)
    (cuts
      : StreamFailureCuts work
          (((State.initialize (Work.fromExecution work)).runNormalized
              inputs).2.flatten.flatMap
            publicationAtoms) streams)
    (partition
      : let queue := State.initialize (Work.fromExecution work)
        let publisher : IncrementalPublisher :=
          { active := queue.initialGroups ++ queue.initialStreams }
        failures.Perm
          (streams
            ++ sourceObjectFailureCuts 0
                (queue.eligibleFailureBlocks
                  (queue.sourceRunBlocks publisher inputs).2.2)))
    {count occurrence owners producer path result}
    (known : TaskAt work occurrence owners producer (.object path result))
    (recorded : occurrence ∈ failedBefore failures count)
    : occurrence
      ∈ (State.initialize (Work.fromExecution work)).objectFailureContributions
          inputs.flatten := by
  let queue := State.initialize (Work.fromExecution work)
  let publisher : IncrementalPublisher :=
    { active := queue.initialGroups ++ queue.initialStreams }
  have ledger := queue.eligibleObjectFailureCuts_ledger 0
    (queue.sourceRunBlocks publisher inputs).2.2
  rw [queue.sourceRunBlocks_inputs_of_started publisher
    (by rwa [← inputsStarted_eq_batchesStarted])] at ledger
  rw [← ledger, List.mem_reverse]
  obtain ⟨entry, kept, same⟩ := List.mem_map.mp ((cuts.object_mem_iff partition known).mp recorded)
  exact List.mem_map.mpr ⟨entry, (List.mem_filter.mp kept).1, same⟩

namespace ConformancePlan

-----------------------------------------------------------------------------------------
-- Successful retirement excludes failure even after later settlements
-----------------------------------------------------------------------------------------

/-- Every successfully completed group stays healthy throughout the full witness.
The selected event is an actual successful group closure. Health refers to all retained
cuts, not just those preceding that event; later failures cannot invalidate its retirement.
-/
def GroupSuccessesHealthy (work : Execution.Work) (w : Witness) : Prop :=
  ∀ (index : Nat) (group : Execution.DeliveryNode)
    (groups streams : List Execution.DeliveryNode),
    w.events[index]? = some (Execution.WorkQueueEvent.groupSuccess group groups streams)
    → ¬NodeFailed work w.matching w.events w.failures group.key

/-- Actual successful group carriers are historically healthy on the canonical inventory.
Witness: durable successful retirement supplies uncancelled record health in full replay.
Generated group provenance and mixed cut/ledger agreement translate it to historical
causality, using the already proved safety of all successful source items.
-/
theorem groupSuccessesHealthy_of_successfulItems {work inputs w streams}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (announced : AnnouncedFailures work w)
    (safe : SuccessfulItemsSafe work inputs.flatten w)
    (cuts
      : StreamFailureCuts work
          (((initialQueue work).runNormalized inputs).2.flatten.flatMap publicationAtoms)
          streams)
    (exactCuts
      : let queue := initialQueue work
        let publisher : IncrementalPublisher :=
          { active := queue.initialGroups ++ queue.initialStreams }
        w.failures
        = mergeFailureCuts
            (sourceObjectFailureCuts 0
              (queue.eligibleFailureBlocks (queue.sourceRunBlocks publisher inputs).2.2))
            streams)
    : GroupSuccessesHealthy work w := by
  let queue := initialQueue work
  let publisher : IncrementalPublisher :=
    { active := queue.initialGroups ++ queue.initialStreams }
  let objects := sourceObjectFailureCuts 0
    (queue.eligibleFailureBlocks (queue.sourceRunBlocks publisher inputs).2.2)
  have partition : w.failures.Perm (streams ++ objects) :=
    exactCuts ▸ mergeFailureCuts_partition objects streams
  intro index group groups children selected
  obtain ⟨atFull, _⟩ := Witness.canonical_event history selected
  obtain ⟨sourceIndex, atSource, _⟩ := publicationAtoms_groupSuccess_prefix _ atFull
  have carrier := List.mem_of_getElem? atSource
  obtain ⟨dependencies, producer, known⟩ :=
    createWorkQueue_runNormalized_groupClosuresLocated generated valid _ carrier
  obtain ⟨_, _, retired, _, uncancelled⟩ :=
    generated.runNormalized_successfulCarrier_retiredHealthy valid started carrier
  obtain ⟨terminal, queueEq⟩ := createWorkQueue_runNormalized_stateCore started
  rw [queueEq] at retired uncancelled
  have accepted := queue.batchesStarted_acceptsBatch inputs
    (by rwa [← inputsStarted_eq_batchesStarted])
  exact generated.replayGraphEvents_retiredGroupHealthy_of_itemSafety valid accepted known
    retired uncancelled
    (fun cut occurrence member => (announced.1.2.2.1 (cut, occurrence) member).2.2)
    (fun occurrence owners producer path result descriptor member =>
      createWorkQueue_mixedFailureCuts_objectsRecorded started cuts partition descriptor
        member)
    safe

/-- Successful group health holds at every shorter output prefix using the same cuts.
Witness: extend a hypothetical earlier failure to the full history and contradict durable
carrier health. This includes the strict completion boundary and the carrier-visible prefix.
-/
theorem GroupSuccessesHealthy.atPrefix {work w}
    (healthy : GroupSuccessesHealthy work w) {index : Nat} {group groups streams}
    (selected
      : w.events[index]?
        = some (Execution.WorkQueueEvent.groupSuccess group groups streams))
    (count : Nat)
    : ¬NodeFailed work w.matching (w.events.take count) w.failures group.key := by
  intro failed
  apply healthy index group groups streams selected
  simpa only [List.take_append_drop] using failed.append (w.events.drop count)

/-- Successful group admission leaves exactly task accounting and carried announcements.
Witness: actual closure provenance/openness and durable historical health supply the other
clauses. Filtering at the event boundary preserves accounting; child notices still see
the carrier and only the failure cuts already visible when that event began.
-/
theorem groupSuccessAllowed_iff_accounting_and_announcements
    {work inputs w index group groups streams}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (healthy : GroupSuccessesHealthy work w)
    (selected : w.events[index]? = some (.groupSuccess group groups streams))
    : EventAllowed work (initialKeys work) w.matching (w.events.take index) w.failures
        (.groupSuccess group groups streams)
      ↔ NodeAccounted work w.matching (w.events.take index) w.failures group.key
        ∧ Announcements work (initialKeys work) w.matching
            (w.events.take index ++ [.groupSuccess group [] []])
            (w.failures.filter (fun entry => entry.1 ≤ index)) groups streams := by
  obtain ⟨atFull, beforeEq⟩ := Witness.canonical_event history selected
  obtain ⟨dependencies, producer, known⟩ :=
    createWorkQueue_runNormalized_atomicGroupClosuresLocated generated valid _
      (List.mem_of_getElem? atFull)
  have opened := createWorkQueue_runNormalized_groupClosureOpenAt generated valid atFull
    List.mem_cons_self
  dsimp only at opened
  rw [beforeEq] at opened
  have length : (w.events.take index).length = index :=
    List.length_take_of_le (Nat.le_of_lt (List.getElem?_eq_some_iff.mp selected).1)
  simp only [EventAllowed, length]
  constructor
  · rintro ⟨_, _, _, accounted, announcements⟩
    exact ⟨(nodeAccounted_filter (Nat.le_of_eq length)).mp accounted, announcements⟩
  · rintro ⟨accounted, announcements⟩
    exact ⟨⟨dependencies, producer, known⟩, opened,
      (by rw [nodeFailed_filter (Nat.le_of_eq length)]; exact healthy.atPrefix selected index),
      (nodeAccounted_filter (Nat.le_of_eq length)).mpr accounted, announcements⟩

/-- Group health shares the witness used for licensed failures and stream event rules.
Witness: retain the canonical construction and its original cut partition, deriving
durable group health without choosing a new matching or changing any public premise.
The buffered/prepared closure ledger is retained on this same witness. Structural task
accounting and child announcements remain separate targets.
-/
theorem mixed_groupHealthCertificates_with_closureLedger {work inputs}
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
        ∧ BufferedClosureLedger work inputs w := by
  obtain ⟨w, history, shape, announced, uncancelled, _, accounted, ready, safe, closures, _,
    streams, cuts, exactCuts⟩ :=
    mixed_failureCertificates_with_closureLedger generated valid started
  exact ⟨w, history, shape, announced, uncancelled,
    failureAdmission_of_announced generated valid history announced,
    streamSuccessAdmission_of_successfulItems generated valid started history announced
      accounted safe cuts exactCuts,
    streamPublicationReady_of_certificates generated generated.nodeKeyCoherent valid started
      history announced ready safe cuts exactCuts,
    groupSuccessesHealthy_of_successfulItems generated valid started history announced safe
      cuts exactCuts, closures⟩

/-- The existing group-health interface retains the same canonical witness.
Witness: project the stronger construction, discarding only the buffered closure ledger.
-/
theorem mixed_groupHealthCertificates {work inputs}
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
        ∧ GroupSuccessesHealthy work w := by
  obtain ⟨w, history, shape, announced, uncancelled, failures, streams, ready, healthy, _⟩ :=
    mixed_groupHealthCertificates_with_closureLedger generated valid started
  exact ⟨w, history, shape, announced, uncancelled, failures, streams, ready, healthy⟩

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
