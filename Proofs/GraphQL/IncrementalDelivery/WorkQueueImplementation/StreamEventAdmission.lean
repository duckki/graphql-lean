import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureEventAdmission

/-! Successful stream controls obey event admission on the common mixed witness. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Successful source actions preserve stream health at their actual output boundary
-----------------------------------------------------------------------------------------

/-- Every actual nonfailure stream action is healthy under the canonical mixed inventory.
Witness: root and item-produced streams inherit producer safety; object-produced streams
retain their actual release support. Source action order excludes direct failure, and
earlier successful items remain safe on the exact strict output prefix.
-/
theorem streamAction_healthy_of_successfulItems
    {work inputs w streams index event stream dependencies producer closing}
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
    (known : NodeAt work stream .stream dependencies producer)
    (selected : w.events[index]? = some event)
    (action : streamAction event = some (stream.key, closing))
    (nonfailure : ∀ node errors, event ≠ .streamFailure node errors)
    : ¬NodeFailed work w.matching (w.events.take index) w.failures stream.key := by
  let queue := initialQueue work
  let publisher : IncrementalPublisher :=
    { active := queue.initialGroups ++ queue.initialStreams }
  let objects := sourceObjectFailureCuts 0
    (queue.eligibleFailureBlocks (queue.sourceRunBlocks publisher inputs).2.2)
  have partition : w.failures.Perm (streams ++ objects) :=
    exactCuts ▸ mergeFailureCuts_partition objects streams
  obtain ⟨atFull, beforeEq⟩ := Witness.canonical_event history selected
  have failedPayloads : ∀ cut occurrence,
      (cut, occurrence) ∈ w.failures
      → ∃ owners producer payload,
          TaskAt work occurrence owners producer payload ∧ payload.failure.isSome = true :=
    fun cut occurrence member => (announced.1.2.2.1 (cut, occurrence) member).2.2
  have objectKnown : ∀ entry ∈ objects,
      ∃ owners producer path errors,
        TaskAt work entry.2 owners producer (.object path (.error errors)) := by
    intro entry member
    obtain ⟨_, owners, producer, path, errors, descriptor, _⟩ :=
      createWorkQueue_eligibleObjectFailureCuts_origin generated valid entry member
    exact ⟨owners, producer, path, errors, descriptor⟩
  have length : (w.events.take index).length = index :=
    List.length_take_of_le (Nat.le_of_lt (List.getElem?_eq_some_iff.mp selected).1)
  have contributors : ∀ occurrence owners,
      TaskHasOwners work occurrence owners → stream.key ∈ owners
      → occurrence ∉ failedBefore w.failures (w.events.take index).length := by
    intro occurrence owners descriptor owner
    rw [length]
    exact cuts.no_failure_at_action_mixed partition objectKnown generated
      (createWorkQueue_runNormalized_atomicStreamActions_ordered valid)
      known atFull action nonfailure descriptor owner
  obtain ⟨received, input, later, sourceSplit, sameAction, _, _, _⟩ :=
    createWorkQueue_atomicStream_sourcePrefix started atFull action
  have sourcePrefix : (received ++ [input]).IsPrefix inputs.flatten :=
    ⟨later, by simp [sourceSplit, List.append_assoc]⟩
  have prior : received.IsPrefix inputs.flatten := ⟨input :: later, sourceSplit.symm⟩
  have localLaws := valid.atPrefix sourcePrefix
  have producerSucceeded := GraphEvent.Ready.streamProducer_succeeded
    localLaws.2.2 generated sameAction known
  have succeeded : ∀ source, producer = some source → TaskSucceeds work source :=
    fun source same => (valid.prefix prior).successes_succeed (producerSucceeded source same)
  have earlierSafe := safe.prefix prior index (List.Subset.refl w.failures)
  cases producer with
  | none =>
      have empty : dependencies = [] := by
        obtain ⟨_, _, atStream⟩ := known
        exact Correctness.located_producer_context atStream
      exact generated.streamHealthy_of_producerSafety failedPayloads known
        succeeded (by intro source impossible; cases impossible) contributors (.inl empty)
  | some parent =>
      cases parent with
      | item address ordinal =>
          have empty : dependencies = [] := by
            obtain ⟨_, _, atStream⟩ := known
            exact Correctness.located_producer_context atStream
          have parentSafe := earlierSafe address ordinal (producerSucceeded _ rfl)
          exact generated.streamHealthy_of_producerSafety failedPayloads known succeeded
            (by intro parent same; cases same; exact parentSafe) contributors (.inl empty)
      | executionGroup address =>
          obtain ⟨before, input, after, split, _, _, healthy⟩ :=
            generated.atomicObjectStreamHealthy_of_earlierItems valid started cuts partition
              known atFull action nonfailure
          rw [beforeEq] at healthy
          have beforePrefix : before.IsPrefix inputs.flatten :=
            ⟨input :: after, split.symm⟩
          exact (healthy (safe.prefix beforePrefix index (List.Subset.refl w.failures))).2

-----------------------------------------------------------------------------------------
-- The successful closure rule combines openness, health, and complete item publication
-----------------------------------------------------------------------------------------

/-- Each successful stream closure obeys the full local event-admission rule.
The shared witness fixes strict output prefixes, publication matching, and failure cuts.
-/
def StreamSuccessAdmission (work : Execution.Work) (w : Witness) : Prop :=
  ∀ index stream,
    w.events[index]? = some (.streamSuccess stream)
    → EventAllowed work (initialKeys work) w.matching (w.events.take index) w.failures
        (.streamSuccess stream)

/-- Actual successful stream completions are admitted on the mixed failure witness.
Witness: source metadata and open references combine with action health and exact item
accounting. Event-start filtering preserves health, and accounting holds for any cuts.
-/
theorem streamSuccessAdmission_of_successfulItems {work inputs w streams}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (announced : AnnouncedFailures work w)
    (accounted : StreamSuccessesAccounted work w)
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
    : StreamSuccessAdmission work w := by
  intro index stream selected
  obtain ⟨atFull, beforeEq⟩ := Witness.canonical_event history selected
  obtain ⟨⟨dependencies, producer, address, entries, located⟩, _⟩ :=
    createWorkQueue_runNormalized_streamSuccess_itemInventory generated valid
      (List.mem_of_getElem? atFull)
  have known : NodeAt work stream .stream dependencies producer := .stream located
  have opened := createWorkQueue_runNormalized_streamOpenAt generated valid atFull
    List.mem_cons_self
  dsimp only at opened
  rw [beforeEq] at opened
  have healthy := streamAction_healthy_of_successfulItems generated valid started history
    announced safe cuts exactCuts known selected rfl (by intros; intro impossible; cases impossible)
  simp only [EventAllowed]
  rw [nodeFailed_filter (Nat.le_refl _)]
  exact ⟨
    ⟨dependencies, producer, known⟩,
    opened,
    healthy,
    accounted index stream selected _
  ⟩

/-- Failed controls and successful stream closures are admitted on one canonical witness.
Witness: keep all three proved construction leaves and attach their local event rules.
Successful group controls, value publications, and terminal accounting remain separate.
-/
theorem streamAndFailureAdmission_certificates {work inputs}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    : ∃ w : Witness,
        w.events = (initialQueue work).nonterminalAtoms inputs
        ∧ BatchShape work inputs w
        ∧ AnnouncedFailures work w
        ∧ UncancelledFailures work w
        ∧ FailureAdmission work w
        ∧ StreamSuccessAdmission work w := by
  obtain ⟨w, history, shape, announced, uncancelled, _, accounted, _, safe,
    streams, cuts, exactCuts⟩ := mixed_failureCertificates_with_cuts generated valid started
  exact ⟨w, history, shape, announced, uncancelled,
    failureAdmission_of_announced generated valid history announced,
    streamSuccessAdmission_of_successfulItems generated valid started history announced
      accounted safe cuts exactCuts⟩

-----------------------------------------------------------------------------------------
-- The remaining control obligation is exactly successful group completion
-----------------------------------------------------------------------------------------

/-- With these proved cases, control admission is equivalent to successful group admission.
Witness: exhaust the work-event constructors; value atoms are outside this leaf and the
canonical history has no terminal marker. This reduction does not assume group admission
in any of the stream or failed-control proofs above.
-/
theorem controlAdmission_iff_groupSuccess {work inputs w}
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (failures : FailureAdmission work w) (streams : StreamSuccessAdmission work w)
    : ControlAdmission work w
      ↔ ∀ index node groups children,
          w.events[index]? = some (.groupSuccess node groups children)
          → EventAllowed work (initialKeys work) w.matching (w.events.take index)
              w.failures (.groupSuccess node groups children) := by
  constructor
  · intro admitted index node groups children selected
    exact admitted index _ selected (by simp [IsValue])
  · intro groups index event selected nonvalue
    cases event with
    | groupValues | streamValues => exact False.elim (nonvalue trivial)
    | groupSuccess node children streams =>
        exact groups index node children streams selected
    | groupFailure node errors => exact failures.1 index node errors selected
    | streamSuccess node => exact streams index node selected
    | streamFailure node errors => exact failures.2 index node errors selected
    | workQueueTermination =>
        exact False.elim ((initialQueue work).nonterminalAtoms_noTermination inputs
          (history ▸ List.mem_of_getElem? selected))

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
