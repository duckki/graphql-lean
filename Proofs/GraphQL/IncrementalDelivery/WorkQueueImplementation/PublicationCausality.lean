import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PublicationSafety
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.FailureExtension
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.TaskReadiness

/-! Historical causal snapshots from publication support, without assuming admission. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Prefix support and fixed failed payloads exclude every later revival
-----------------------------------------------------------------------------------------

/-- Publication support restricts to any observed prefix without changing matching or cuts.
Witness: each retained value has the same earlier prefix, producer, and healthy owner.
-/
theorem PublicationSupport.take {work matching events failures}
    (support : PublicationSupport work matching events failures) (count : Nat)
    : PublicationSupport work matching (events.take count) failures := by
  intro index event selected value
  have within : index < count := by
    have bound := (List.getElem?_eq_some_iff.mp selected).1
    simp only [List.length_take] at bound
    omega
  have atWhole := (List.getElem?_take_of_lt within).symm.trans selected
  simpa only [List.take_take, Nat.min_eq_left (Nat.le_of_lt within)]
    using support index event atWhole value

/-- One locally supported event extends the certificate without assuming event admission.
Witness: old positions keep their exact prefixes; only the last value needs new evidence.
For a control event the local implication is vacuous. Matching and cuts remain unchanged.
-/
theorem PublicationSupport.append_event {work matching events failures event}
    (support : PublicationSupport work matching events failures)
    (next
      : IsValue event
        → ∃ owners producer payload key,
            TaskAt work (matching events.length) owners producer payload
            ∧ payload.failure = none
            ∧ key ∈ owners
            ∧ ¬NodeFailed work matching events failures key
            ∧ ∀ parent, producer = some parent → Published matching events parent)
    : PublicationSupport work matching (events ++ [event]) failures := by
  intro index emitted selected value
  by_cases earlier : index < events.length
  · have original : events[index]? = some emitted := by
      simpa only [List.getElem?_append_left earlier] using selected
    simpa only [List.take_append_of_le_length (Nat.le_of_lt earlier)]
      using support index emitted original value
  · have bound := (List.getElem?_eq_some_iff.mp selected).1
    have sameIndex : index = events.length := by
      simp only [List.length_append, List.length_singleton] at bound
      omega
    subst index
    have sameEvent : emitted = event := by simpa using selected.symm
    subst emitted
    simpa using next value

/-- A next value's cancellation guard follows from support of the strict earlier prefix.
Witness: extend support with this value's genuine payload, healthy owner, and ready
producer, then apply the no-revival readiness theorem at its new index. This avoids
requiring a certificate for the entire future run while constructing event admission.
-/
theorem PublicationSupport.canPublish_next
    {work matching events failures event owners producer payload key}
    (support : PublicationSupport work matching events failures)
    (failedPayloads
      : ∀ cut occurrence,
          (cut, occurrence) ∈ failures
          → ∃ owners producer payload,
              TaskAt work occurrence owners producer payload
              ∧ payload.failure.isSome = true)
    (value : IsValue event)
    (known : TaskAt work (matching events.length) owners producer payload)
    (success : payload.failure = none) (owner : key ∈ owners)
    (healthy : ¬NodeFailed work matching events failures key)
    (ready : ∀ source, producer = some source → Published matching events source)
    (fresh : ¬Published matching events (matching events.length))
    (ordered
      : ∀ address first second,
          matching events.length = .item address second
          → first < second
          → Published matching events (.item address first))
    : CanPublish work matching events failures (matching events.length) producer := by
  have extended := support.append_event (event := event)
    (fun _ => ⟨owners, producer, payload, key, known, success, owner, healthy, ready⟩)
  have selected : (events ++ [event])[events.length]? = some event := by simp
  have observed : (events ++ [event]).take events.length = events := by simp
  simpa only [observed]
    using extended.canPublish failedPayloads selected value known
      (observed.symm ▸ fresh) (observed.symm ▸ ordered)

/-- A fixed failed task cannot be one of the supported successful publications.
Witness: both descriptors locate the same occurrence and therefore the same payload.
The cut may be future, unordered, or not yet licensed; only its real outcome is used.
-/
theorem PublicationSupport.failed_unpublished {work matching events failures}
    (support : PublicationSupport work matching events failures)
    (failedPayloads
      : ∀ cut occurrence,
          (cut, occurrence) ∈ failures
          → ∃ owners producer payload,
              TaskAt work occurrence owners producer payload
              ∧ payload.failure.isSome = true)
    {occurrence cut} (failed : occurrence ∈ failedBefore failures cut)
    : ¬Published matching events occurrence := by
  obtain ⟨entry, kept, same⟩ := List.mem_map.mp failed
  obtain ⟨owners, producer, payload, known, fails⟩ :=
    failedPayloads entry.1 entry.2 (List.mem_filter.mp kept).1
  rw [same] at known
  rintro ⟨index, event, selected, value, matched⟩
  obtain ⟨otherOwners, otherProducer, otherPayload, _, otherKnown, success, _⟩ :=
    support index event selected value
  rw [matched] at otherKnown
  have equal := (otherKnown.unique known).2.2
  rw [← equal, success] at fails
  contradiction

/-- A task with a healthy contributor and published producer cannot be cancelled.
Witness: inspect cancellation at its original cut. Owner cancellation contradicts
the healthy contributor; producer failure or cancellation contradicts the
producer's supported publication. The task itself need not have a successful outcome or
have settled, so this rule also applies to pending contents of a new group notice.
-/
theorem PublicationSupport.pendingTask_not_cancelled
    {work matching events failures occurrence owners producer payload key}
    (support : PublicationSupport work matching events failures)
    (failedPayloads
      : ∀ cut occurrence,
          (cut, occurrence) ∈ failures
          → ∃ owners producer payload,
              TaskAt work occurrence owners producer payload
              ∧ payload.failure.isSome = true)
    (known : TaskAt work occurrence owners producer payload) (owner : key ∈ owners)
    (healthy : ¬NodeFailed work matching events failures key)
    (ready : ∀ source, producer = some source → Published matching events source)
    : ¬TaskCancelled work matching events failures occurrence := by
  intro cancelled
  obtain ⟨cut, member, reached, cause⟩ := cancelled
  cases cause with
  | owners other _ _ invalid =>
      obtain ⟨parent, result, descriptor⟩ := other
      exact healthy ⟨cut, member, reached, invalid key ((known.unique descriptor).1 ▸ owner)⟩
  | producerFailed other _ failed =>
      obtain ⟨otherOwners, result, descriptor⟩ := other
      have published := ready _ (known.unique descriptor).2.1
      exact support.failed_unpublished failedPayloads failed published
  | producerCancelled other _ failure =>
      obtain ⟨otherOwners, result, descriptor⟩ := other
      exact support.cancelled_unpublished failedPayloads ⟨cut, member, reached, failure⟩
        (ready _ (known.unique descriptor).2.1)

/-- Historical node failure persists at the current supported publication snapshot.
Witness: advance its original cut using failed-payload provenance and the derived
no-revival theorem. EventAllowed and FailureWitness are not premises.
-/
theorem PublicationSupport.nodeFailed_snapshot {work matching events failures key}
    (support : PublicationSupport work matching events failures)
    (failedPayloads
      : ∀ cut occurrence,
          (cut, occurrence) ∈ failures
          → ∃ owners producer payload,
              TaskAt work occurrence owners producer payload
              ∧ payload.failure.isSome = true)
    (failure : NodeFailed work matching events failures key)
    : Causality.NodeFailed work (failedBefore failures events.length)
        (Published matching events) key := by
  obtain ⟨cut, member, reached, cause⟩ := failure
  exact cause.advance (failedBefore_subset failures reached)
    (fun _ failed => support.failed_unpublished failedPayloads failed)
    (fun _ cancelled => support.cancelled_unpublished failedPayloads
      ⟨cut, member, reached, cancelled⟩)

/-- Historical cancellation persists at the current supported publication snapshot.
Witness: advance the same reached cut without assuming that its failure was licensed.
-/
theorem PublicationSupport.taskCancelled_snapshot
    {work matching events failures occurrence}
    (support : PublicationSupport work matching events failures)
    (failedPayloads
      : ∀ cut occurrence,
          (cut, occurrence) ∈ failures
          → ∃ owners producer payload,
              TaskAt work occurrence owners producer payload
              ∧ payload.failure.isSome = true)
    (cancelled : TaskCancelled work matching events failures occurrence)
    : Causality.TaskCancelled work (failedBefore failures events.length)
        (Published matching events) occurrence := by
  obtain ⟨cut, member, reached, cause⟩ := cancelled
  exact cause.advance (failedBefore_subset failures reached)
    (fun _ failed => support.failed_unpublished failedPayloads failed)
    (fun _ cancelled => support.cancelled_unpublished failedPayloads
      ⟨cut, member, reached, cancelled⟩)

-----------------------------------------------------------------------------------------
-- A greatest reached cut suffices; ordering and future-cut licensing are unnecessary
-----------------------------------------------------------------------------------------

/-- A nonempty finite cut list has a greatest cut position, even if it is unsorted.
Witness: list induction retains the larger of the head and the tail's maximum.
-/
private theorem greatest_cut (failures : FailureCuts) (nonempty : failures ≠ [])
    : ∃ entry ∈ failures, ∀ other ∈ failures, other.1 ≤ entry.1 := by
  induction failures with
  | nil => exact False.elim (nonempty rfl)
  | cons entry rest ih =>
      by_cases empty : rest = []
      · subst rest
        exact ⟨entry, List.mem_cons_self, by simp⟩
      obtain ⟨last, member, greatest⟩ := ih empty
      by_cases before : entry.1 ≤ last.1
      · refine ⟨last, List.mem_cons_of_mem _ member, ?_⟩
        intro other included
        rcases List.mem_cons.mp included with same | later
        · exact same ▸ before
        · exact greatest other later
      · refine ⟨entry, List.mem_cons_self, ?_⟩
        intro other included
        rcases List.mem_cons.mp included with same | later
        · exact same ▸ Nat.le_refl _
        · exact Nat.le_trans (greatest other later) (Nat.le_of_not_ge before)

/-- All currently visible failures are visible at one greatest reached cut.
Witness: maximize the filtered cut list. Future or unordered cuts are retained in the
original list but cannot affect this boundary or its failure-occurrence projection.
-/
private theorem greatest_visible_cut (failures : FailureCuts) (bound : Nat)
    (nonempty : failedBefore failures bound ≠ [])
    : ∃ cut,
        cut ∈ failures.map Prod.fst
        ∧ cut ≤ bound
        ∧ failedBefore failures cut = failedBefore failures bound := by
  have retained : failures.filter (fun entry => decide (entry.1 ≤ bound)) ≠ [] := by
    intro empty
    exact nonempty (by simp [failedBefore, empty])
  obtain ⟨entry, member, greatest⟩ := greatest_cut _ retained
  obtain ⟨inCuts, reached⟩ := List.mem_filter.mp member
  have reached : entry.1 ≤ bound := by simpa using reached
  refine ⟨entry.1, List.mem_map.mpr ⟨entry, inCuts, rfl⟩, reached, ?_⟩
  unfold failedBefore
  congr 1
  apply List.filter_congr
  intro other included
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · exact fun before => Nat.le_trans before reached
  · intro before
    exact greatest other (List.mem_filter.mpr ⟨included, by simpa using before⟩)

/-- Current-snapshot node failure has a historical cut witness under publication support.
Witness: move back to the greatest reached cut; fewer publications cannot obstruct
causal failure. No ordering, bound on future cuts, or FailureWitness premise is needed.
-/
theorem PublicationSupport.snapshot_nodeFailed {work matching events failures key}
    (support : PublicationSupport work matching events failures)
    (failedPayloads
      : ∀ cut occurrence,
          (cut, occurrence) ∈ failures
          → ∃ owners producer payload,
              TaskAt work occurrence owners producer payload
              ∧ payload.failure.isSome = true)
    (failure
      : Causality.NodeFailed work (failedBefore failures events.length)
          (Published matching events) key)
    : NodeFailed work matching events failures key := by
  obtain ⟨cut, member, reached, same⟩ :=
    greatest_visible_cut failures events.length failure.nonempty
  refine ⟨cut, member, reached, ?_⟩
  rw [same]
  apply failure.advance (List.Subset.refl _)
  · intro occurrence failed published
    apply support.failed_unpublished failedPayloads failed
    simpa only [List.take_append_drop] using published.append (events.drop cut)
  · intro occurrence cancelled published
    apply cancelled.unpublished
    simpa only [List.take_append_drop] using published.append (events.drop cut)

/-- Current-snapshot cancellation has a historical witness without assuming admission.
Witness: the same greatest reached cut and backward publication transport.
-/
theorem PublicationSupport.snapshot_taskCancelled
    {work matching events failures occurrence}
    (support : PublicationSupport work matching events failures)
    (failedPayloads
      : ∀ cut occurrence,
          (cut, occurrence) ∈ failures
          → ∃ owners producer payload,
              TaskAt work occurrence owners producer payload
              ∧ payload.failure.isSome = true)
    (cancelled
      : Causality.TaskCancelled work (failedBefore failures events.length)
          (Published matching events) occurrence)
    : TaskCancelled work matching events failures occurrence := by
  obtain ⟨cut, member, reached, same⟩ :=
    greatest_visible_cut failures events.length cancelled.nonempty
  refine ⟨cut, member, reached, ?_⟩
  rw [same]
  apply cancelled.advance (List.Subset.refl _)
  · intro occurrence failed published
    apply support.failed_unpublished failedPayloads failed
    simpa only [List.take_append_drop] using published.append (events.drop cut)
  · intro occurrence cancelled published
    apply cancelled.unpublished
    simpa only [List.take_append_drop] using published.append (events.drop cut)

/-- Historical and current node failure agree on supported publications.
Witness: the two cut-preserving transports, independent of full history admission.
-/
theorem PublicationSupport.nodeFailed_iff_snapshot {work matching events failures key}
    (support : PublicationSupport work matching events failures)
    (failedPayloads
      : ∀ cut occurrence,
          (cut, occurrence) ∈ failures
          → ∃ owners producer payload,
              TaskAt work occurrence owners producer payload
              ∧ payload.failure.isSome = true)
    : NodeFailed work matching events failures key
      ↔ Causality.NodeFailed work (failedBefore failures events.length)
          (Published matching events) key :=
  ⟨support.nodeFailed_snapshot failedPayloads, support.snapshot_nodeFailed failedPayloads⟩

/-- Historical and current cancellation agree on supported publications.
Witness: the same pair of transports, retaining every supplied failure cut.
-/
theorem PublicationSupport.taskCancelled_iff_snapshot
    {work matching events failures occurrence}
    (support : PublicationSupport work matching events failures)
    (failedPayloads
      : ∀ cut occurrence,
          (cut, occurrence) ∈ failures
          → ∃ owners producer payload,
              TaskAt work occurrence owners producer payload
              ∧ payload.failure.isSome = true)
    : TaskCancelled work matching events failures occurrence
      ↔ Causality.TaskCancelled work (failedBefore failures events.length)
          (Published matching events) occurrence :=
  ⟨
    support.taskCancelled_snapshot failedPayloads,
    support.snapshot_taskCancelled failedPayloads
  ⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
