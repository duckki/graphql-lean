import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.PublicationOrder

/-! Derive publication cancellation safety from provenance, owner health, and producers.
These are proof interfaces, not additional host-source or public conformance premises.
-/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Earlier producers and healthy owners already prevent publication after cancellation
-----------------------------------------------------------------------------------------

/-- Each value atom has a successful task, a healthy contributing owner at its prefix,
and an earlier publication of its producer. This proof certificate omits cancellation
safety, freshness, notices, and item order; it does not assume event admission.
-/
def PublicationSupport (work : Work) (matching : PublicationMatching)
    (events : List WorkQueueEvent) (failures : FailureCuts)
    : Prop :=
  ∀ index event,
    events[index]? = some event
    → IsValue event
    → ∃ owners producer payload ref,
        TaskAt work (matching index) owners producer payload
        ∧ payload.failure = none
        ∧ ref ∈ owners
        ∧ ¬NodeFailed work matching (events.take index) failures ref
        ∧ ∀ parent, producer = some parent → Published matching (events.take index) parent

/-- Supported publications cannot revive historically cancelled tasks.
Witness: induction on publication position. Owner cancellation contradicts owner health;
a failed producer contradicts successful provenance; a cancelled producer contradicts
its earlier publication. A later cut protects a value already published before that cut.
Only failed-payload provenance is used, not FailureWitness or its cancellation guard.
-/
theorem PublicationSupport.cancelled_unpublished
    {work matching events failures}
    (support : PublicationSupport work matching events failures)
    (failedPayloads
      : ∀ cut occurrence,
          (cut, occurrence) ∈ failures
          → ∃ owners producer payload,
              TaskAt work occurrence owners producer payload
              ∧ payload.failure.isSome = true)
    {occurrence}
    (cancelled : TaskCancelled work matching events failures occurrence)
    : ¬Published matching events occurrence := by
  have noPublication (index : Nat) : ∀ event,
      events[index]? = some event → IsValue event
      → ¬TaskCancelled work matching events failures (matching index) := by
    induction index using Nat.strongRecOn with
    | ind index ih =>
        intro event selected value cancellation
        obtain ⟨cut, member, reached, cause⟩ := cancellation
        by_cases earlier : index < cut
        · exact cause.unpublished
            ⟨index, event, (List.getElem?_take_of_lt earlier).trans selected, value, rfl⟩
        have cutoff : cut ≤ index := Nat.le_of_not_gt earlier
        have inside := (List.getElem?_eq_some_iff.mp selected).1
        have length : (events.take index).length = index := by
          simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt inside)]
        obtain ⟨owners, producer, payload, ref, known, _, owns, healthy, parentReady⟩ :=
          support index event selected value
        cases cause with
        | owners other _ _ failed =>
            obtain ⟨otherProducer, otherPayload, otherKnown⟩ := other
            have same := (known.unique otherKnown).1
            apply healthy
            refine ⟨cut, member, by omega, ?_⟩
            simpa only [List.take_take, Nat.min_eq_left cutoff]
              using failed ref (same ▸ owns)
        | producerFailed other _ failure =>
            obtain ⟨otherOwners, otherPayload, otherKnown⟩ := other
            have same := (known.unique otherKnown).2.1
            obtain ⟨prior, previous, _, atPrior, isValue, matched⟩ :=
              (parentReady _ same).before
            obtain ⟨priorOwners, priorProducer, priorPayload, _, priorKnown,
              priorSuccess, _⟩ := support prior previous atPrior isValue
            obtain ⟨entry, kept, sameOccurrence⟩ := List.mem_map.mp failure
            obtain ⟨badOwners, badProducer, badPayload, badKnown, badFails⟩ :=
              failedPayloads entry.1 entry.2 (List.mem_filter.mp kept).1
            have equal := (priorKnown.unique
              (matched.symm ▸ sameOccurrence ▸ badKnown)).2.2
            rw [← equal, priorSuccess] at badFails
            contradiction
        | producerCancelled other _ previousCancellation =>
            obtain ⟨otherOwners, otherPayload, otherKnown⟩ := other
            have same := (known.unique otherKnown).2.1
            obtain ⟨prior, previous, before, atPrior, isValue, matched⟩ :=
              (parentReady _ same).before
            apply ih prior before previous atPrior isValue
            rw [matched]
            exact ⟨cut, member, reached, previousCancellation⟩
  rintro ⟨index, event, selected, value, same⟩
  exact noPublication index event selected value (same.symm ▸ cancelled)

/-- A supported value is uncancelled at its emitting prefix, retaining all supplied cuts.
Witness: extend any prefix cancellation to the full history and contradict the actual
publication. Failure cuts need only have genuine failing payloads.
-/
theorem PublicationSupport.not_cancelled_at
    {work matching events failures}
    (support : PublicationSupport work matching events failures)
    (failedPayloads
      : ∀ cut occurrence,
          (cut, occurrence) ∈ failures
          → ∃ owners producer payload,
              TaskAt work occurrence owners producer payload
              ∧ payload.failure.isSome = true)
    {index event} (selected : events[index]? = some event) (value : IsValue event)
    : ¬TaskCancelled work matching (events.take index) failures (matching index) := by
  intro cancelled
  have atWhole : TaskCancelled work matching events failures (matching index) := by
    simpa only [List.take_append_drop] using cancelled.append (events.drop index)
  exact support.cancelled_unpublished failedPayloads atWhole
    ⟨index, event, selected, value, rfl⟩

-----------------------------------------------------------------------------------------
-- Restore the unchanged public readiness predicate without a cancellation premise
-----------------------------------------------------------------------------------------

/-- Fresh, ordered, supported publications satisfy the existing CanPublish predicate.
Witness: derive cancellation safety above and identify the producer by task uniqueness.
This also covers object values; no new scheduler law or admission premise is introduced.
-/
theorem PublicationSupport.canPublish
    {work matching events failures}
    (support : PublicationSupport work matching events failures)
    (failedPayloads
      : ∀ cut occurrence,
          (cut, occurrence) ∈ failures
          → ∃ owners producer payload,
              TaskAt work occurrence owners producer payload
              ∧ payload.failure.isSome = true)
    {index event owners producer payload}
    (selected : events[index]? = some event) (value : IsValue event)
    (known : TaskAt work (matching index) owners producer payload)
    (fresh : ¬Published matching (events.take index) (matching index))
    (ordered
      : ∀ address first second,
          matching index = .item address second
          → first < second
          → Published matching (events.take index) (.item address first))
    : CanPublish work matching (events.take index) failures (matching index)
        producer := by
  obtain ⟨otherOwners, otherProducer, otherPayload, ref, otherKnown, _, _, _, ready⟩ :=
    support index event selected value
  have sameProducer := (known.unique otherKnown).2.1
  refine ⟨fresh, support.not_cancelled_at failedPayloads selected value, ?_, ?_⟩
  · exact fun parent same => ready parent (sameProducer.symm.trans same)
  · cases occurrence : matching index with
    | executionGroup => trivial
    | item address ordinal =>
        cases ordinal with
        | zero => trivial
        | succ ordinal =>
            exact ordered address ordinal (ordinal + 1) occurrence (by omega)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
