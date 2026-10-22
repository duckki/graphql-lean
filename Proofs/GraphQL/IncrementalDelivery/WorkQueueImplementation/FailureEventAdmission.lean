import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.MixedFailureWitness
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupOpenness

/-! Actual failed-group and failed-stream controls satisfy the full event-admission rule. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Positive exact error totals exhibit a visible contributing failure
-----------------------------------------------------------------------------------------

/-- A reported task cause supplies a historical failure of its owning node. -/
theorem nodeFailureCause_nodeFailed {work matching events failures ref errors}
    (cause : NodeFailureCause work (failedBefore failures events.length) ref errors)
    : NodeFailed work matching events failures ref := by
  obtain ⟨occurrence, failed, owners, producer, payload, known, owner, _, _⟩ := cause
  exact NodeFailed.task known owner failed

/-- Every actual failed-group control reports a positive execution-error count.
Witness: its selected rejected task has the generated positive failure count.
-/
theorem createWorkQueue_atomicGroupFailure_positive {work group errors}
    {inputs : List (List GraphEvent)}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (emitted
      : Execution.WorkQueueEvent.groupFailure group errors
        ∈ ((ConformancePlan.initialQueue work).runNormalized inputs).2.flatten.flatMap
            publicationAtoms)
    : 0 < errors := by
  obtain ⟨_, _, _, _, _, known, _⟩ :=
    createWorkQueue_runNormalized_atomicGroupFailure_source generated valid emitted
  exact generated.taskFailure_positive known rfl

namespace ConformancePlan

-----------------------------------------------------------------------------------------
-- A canonical witness retains each atom's exact full-run position and strict prefix
-----------------------------------------------------------------------------------------

/-- A selected canonical atom and its strict prefix are unchanged in the full replay.
Witness: the only removed suffix is the optional terminal marker, after every selected
event. This transports local queue certificates without choosing a new matching or cuts.
-/
theorem Witness.canonical_event {work inputs index event} {w : Witness}
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (selected : w.events[index]? = some event)
    : let atoms :=
        ((initialQueue work).runNormalized inputs).2.flatten.flatMap publicationAtoms
      atoms[index]? = some event ∧ atoms.take index = w.events.take index := by
  let queue := initialQueue work
  have within := (List.getElem?_eq_some_iff.mp selected).1
  have bound : index < (queue.nonterminalAtoms inputs).length := history ▸ within
  constructor
  · rw [queue.runNormalized_terminalShape inputs (createWorkQueue_terminated _),
      List.getElem?_append_left bound, ← history]
    exact selected
  · rw [queue.nonterminalAtoms_take inputs (createWorkQueue_terminated _) (Nat.le_of_lt bound),
      ← history]

/-- Both kinds of failed completion obey their entire local `EventAllowed` rule.
The witness carries one event history, publication matching, and mixed failure inventory.
-/
def FailureAdmission (work : Execution.Work) (w : Witness) : Prop :=
  (∀ index group errors,
    w.events[index]? = some (.groupFailure group errors)
    → EventAllowed work (initialRefs work) w.matching (w.events.take index) w.failures
        (.groupFailure group errors))
  ∧ (∀ index stream errors,
      w.events[index]? = some (.streamFailure stream errors)
      → EventAllowed work (initialRefs work) w.matching (w.events.take index) w.failures
          (.streamFailure stream errors))

/-- Actual failed controls are admitted under the same complete announced inventory.
Witness: queue provenance supplies metadata and open references; exact positive error
totals supply causal failure at the event-start cutoff. No successful event is assumed
admitted, and the inventory need not be reconstructed or moved to notification cuts.
-/
theorem failureAdmission_of_announced {work inputs w}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (announced : AnnouncedFailures work w)
    : FailureAdmission work w := by
  constructor
  · intro index group errors selected
    obtain ⟨atFull, beforeEq⟩ := Witness.canonical_event history selected
    obtain ⟨dependencies, producer, known⟩ :=
      createWorkQueue_runNormalized_atomicGroupClosuresLocated generated valid _
        (List.mem_of_getElem? atFull)
    have opened := createWorkQueue_runNormalized_groupFailureOpenAt generated valid atFull
    dsimp only at opened
    rw [beforeEq] at opened
    have length : (w.events.take index).length = index :=
      List.length_take_of_le (Nat.le_of_lt (List.getElem?_eq_some_iff.mp selected).1)
    have counts := announced.1.2.2.2.1 index group errors selected
    have failed : NodeFailed work w.matching (w.events.take index) w.failures group.ref :=
      nodeFailureCause_nodeFailed (length.symm ▸ counts)
    simp only [EventAllowed]
    rw [nodeFailed_filter (Nat.le_refl _), failedBefore_filter _ (Nat.le_refl _), length]
    exact ⟨⟨dependencies, producer, known⟩, opened, failed, counts⟩
  · intro index stream errors selected
    obtain ⟨atFull, beforeEq⟩ := Witness.canonical_event history selected
    have source := createWorkQueue_runNormalized_streamCompletion_source
      (Work.fromExecution work) inputs
      (List.mem_of_getElem? atFull) rfl
    obtain ⟨address, ordinal, producer, task, _, _⟩ :=
      valid.streamFailure_itemInventory generated source
    obtain ⟨dependencies, known⟩ := (itemTask_owner_nodeAt task).2
    have opened := createWorkQueue_runNormalized_streamOpenAt generated valid atFull
      List.mem_cons_self
    dsimp only at opened
    rw [beforeEq] at opened
    have length : (w.events.take index).length = index :=
      List.length_take_of_le (Nat.le_of_lt (List.getElem?_eq_some_iff.mp selected).1)
    have counts := announced.1.2.2.2.2 index stream errors selected
    have failed : NodeFailed work w.matching (w.events.take index) w.failures stream.ref :=
      nodeFailureCause_nodeFailed (length.symm ▸ counts)
    simp only [EventAllowed]
    rw [nodeFailed_filter (Nat.le_refl _), failedBefore_filter _ (Nat.le_refl _), length]
    exact ⟨⟨dependencies, producer, known⟩, opened, failed, counts⟩

/-- The general mixed failure witness also admits both failed completion constructors.
Witness: preserve the existing shared batching/licensing construction and attach the
local failed-event proof. Successful controls and publications remain separate targets.
-/
theorem failureAdmission_certificates {work inputs}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    : ∃ w : Witness,
        w.events = (initialQueue work).nonterminalAtoms inputs
        ∧ BatchShape work inputs w
        ∧ AnnouncedFailures work w
        ∧ UncancelledFailures work w
        ∧ FailureAdmission work w := by
  obtain ⟨w, history, shape, announced, uncancelled⟩ :=
    mixed_failureCertificates generated valid started
  exact ⟨w, history, shape, announced, uncancelled,
    failureAdmission_of_announced generated valid history announced⟩

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
