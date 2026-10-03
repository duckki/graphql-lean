import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RawPublicationClosures
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FlattenedOutputReplay

/-! Remapped object publications retain their raw successful release carrier. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (ExecutionGroupValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Recover the raw value and exact publisher at an atomic object position
-----------------------------------------------------------------------------------------

/-- Publisher-normalized object values already are atomic, even when their IDs differ.
Witness: each mapped value contains exactly one payload, so splitting is the identity.
-/
theorem IncrementalPublisher.groupValues_atoms (publisher : IncrementalPublisher)
    (group : Execution.DeliveryNode) (values : List ExecutionGroupValue)
    : ((publisher.handleWorkQueueEvent (.groupValues group values)).2.flatMap
        publicationAtoms)
      = (publisher.handleWorkQueueEvent (.groupValues group values)).2 := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
      simpa [IncrementalPublisher.handleWorkQueueEvent, publicationAtoms]
        using congrArg
          (Execution.WorkQueueEvent.groupValues
              (publisher.getBestIdAndSubPath group value) [value]
            :: ·)
          ih

/-- A stream atom cannot become an object publication.
Witness: every branch of stream splitting retains the stream constructor.
-/
theorem streamPublicationAtoms_not_groupValues
    (stream groups streams values owner payload)
    : Execution.WorkQueueEvent.groupValues owner payload
      ∉ streamPublicationAtoms stream groups streams values := by
  induction values using streamPublicationAtoms.induct with
  | case1 => simp [streamPublicationAtoms]
  | case2 => simp [streamPublicationAtoms]
  | case3 value next rest ih => simp [streamPublicationAtoms, ih]

/-- An object atom identifies its original raw value and the publisher's effective owner.
Witness: invert the actual handler and singleton expansion; no registry law is assumed.
-/
theorem IncrementalPublisher.handleWorkQueueEvent_atomicGroupValue_origin
    (publisher : IncrementalPublisher) (event : WorkQueueEvent) {index : Nat}
    {owner payload}
    (selected
      : ((publisher.handleWorkQueueEvent event).2.flatMap publicationAtoms)[index]?
        = some (Execution.WorkQueueEvent.groupValues owner payload))
    : ∃ group values value,
        event = .groupValues group values
        ∧ values[index]? = some value
        ∧ owner = publisher.getBestIdAndSubPath group value
        ∧ payload = [value] := by
  cases event with
  | groupValues group values =>
      rw [publisher.groupValues_atoms] at selected
      change (values.map _)[index]? = _ at selected
      rw [List.getElem?_map] at selected
      cases found : values[index]? with
      | none => simp [found] at selected
      | some value =>
          simp only [found, Option.map_some, Option.some.injEq,
            Execution.WorkQueueEvent.groupValues.injEq] at selected
          exact ⟨group, values, value, rfl, found, selected.1.symm, selected.2.symm⟩
  | streamValues stream values groups streams =>
      have member := List.mem_of_getElem? selected
      exact False.elim
        (streamPublicationAtoms_not_groupValues stream groups streams
          values
          owner payload
          (by simpa [IncrementalPublisher.handleWorkQueueEvent,
            publicationAtoms] using member))
  | groupSuccess | groupFailure | streamSuccess | streamFailure | workQueueTermination =>
      have member := List.mem_of_getElem? selected
      simp [IncrementalPublisher.handleWorkQueueEvent, publicationAtoms] at member

/-- Every atomic object publication retains its raw event position, value index, and exact
pre-event publisher. Earlier stream splitting affects only the prefix length.
Witness: invert the concatenated atomic output of each actual normalization step.
-/
theorem IncrementalPublisher.normalizeBatch_atomicGroupValue_origin
    (publisher : IncrementalPublisher) (raw : List WorkQueueEvent) {index owner payload}
    (selected
      : ((publisher.normalizeBatch raw).2.flatMap publicationAtoms)[index]?
        = some (.groupValues owner payload))
    : ∃ before group values after offset value,
        raw = before ++ .groupValues group values :: after
        ∧ values[offset]? = some value
        ∧ index
          = ((publisher.normalizeBatch before).2.flatMap publicationAtoms).length + offset
        ∧ owner = (publisher.normalizeBatch before).1.getBestIdAndSubPath group value
        ∧ payload = [value] := by
  induction raw generalizing publisher index with
  | nil => simp [IncrementalPublisher.normalizeBatch] at selected
  | cons event rest ih =>
      rw [IncrementalPublisher.normalizeBatch_cons] at selected
      dsimp only at selected
      rw [List.flatMap_append] at selected
      let head := publisher.handleWorkQueueEvent event
      by_cases earlier : index < (head.2.flatMap publicationAtoms).length
      · rw [List.getElem?_append_left earlier] at selected
        obtain ⟨group, values, value, same, found, ownerEq, payloadEq⟩ :=
          publisher.handleWorkQueueEvent_atomicGroupValue_origin event selected
        subst event
        exact ⟨[], group, values, rest, index, value, rfl, found,
          by simp [IncrementalPublisher.normalizeBatch], ownerEq, payloadEq⟩
      · have later : (head.2.flatMap publicationAtoms).length ≤ index := by omega
        rw [List.getElem?_append_right later] at selected
        obtain ⟨before, group, values, after, offset, value,
          rawEq, found, position, ownerEq, payloadEq⟩ := ih head.1 selected
        refine ⟨event :: before, group, values, after, offset, value,
          by simp [rawEq], found, ?_, ?_, payloadEq⟩
        · simp only [IncrementalPublisher.normalizeBatch_cons, List.flatMap_append,
            List.length_append]
          change index = (head.2.flatMap publicationAtoms).length
            + ((head.1.normalizeBatch before).2.flatMap publicationAtoms).length + offset
          omega
        · simpa only [IncrementalPublisher.normalizeBatch_cons] using ownerEq

-----------------------------------------------------------------------------------------
-- The very same raw block contains the successful release carrier
-----------------------------------------------------------------------------------------

/-- Exact evidence for one normalized object atom: its raw release block, value offset,
and effective owner. The publisher is the actual state before that raw block, not an
independently chosen owner-selection witness.
-/
structure GroupPublicationOrigin (publisher : IncrementalPublisher)
    (raw : List WorkQueueEvent) (index : Nat) (owner : Execution.DeliveryNode)
    (payload : List Execution.ExecutionGroupValue) where
  before : List WorkQueueEvent
  group : Execution.DeliveryNode
  values : List ExecutionGroupValue
  groups : List Execution.DeliveryNode
  streams : List Execution.DeliveryNode
  after : List WorkQueueEvent
  offset : Nat
  value : ExecutionGroupValue
  rawEq
    : raw
      = before ++ .groupValues group values :: .groupSuccess group groups streams :: after
  found : values[offset]? = some value
  position
    : index
      = ((publisher.normalizeBatch before).2.flatMap publicationAtoms).length + offset
  ownerEq : owner = (publisher.normalizeBatch before).1.getBestIdAndSubPath group value
  payloadEq : payload = [value]

/-- Normalized object atoms retain the raw triggering group and its adjacent success.
The effective owner need not equal that group. Neither source validity nor the scheduler
contract is assumed: this is an exact output decomposition of the executable publisher.
Witness: recover the raw publication, then use the queue's publication/closure pairing.
-/
theorem GroupPublicationPairs.normalized_origin {raw : List WorkQueueEvent}
    (pairs : GroupPublicationPairs raw) (publisher : IncrementalPublisher)
    {index owner payload}
    (selected
      : ((publisher.normalizeBatch raw).2.flatMap publicationAtoms)[index]?
        = some (.groupValues owner payload))
    : Nonempty (GroupPublicationOrigin publisher raw index owner payload) := by
  obtain ⟨before, group, values, after, offset, value,
    rawEq, found, position, ownerEq, payloadEq⟩ :=
    publisher.normalizeBatch_atomicGroupValue_origin raw selected
  have atRaw : raw[before.length]? = some (.groupValues group values) := by
    simp [rawEq]
  obtain ⟨groups, streams, atNext⟩ := pairs.next atRaw
  have afterHead : after[0]? = some (.groupSuccess group groups streams) := by
    rw [rawEq, List.getElem?_append_right (by omega)] at atNext
    simpa using atNext
  cases after with
  | nil => cases afterHead
  | cons event rest =>
      cases afterHead
      exact ⟨⟨before, group, values, groups, streams, rest, offset, value,
        rawEq, found, position, ownerEq, payloadEq⟩⟩

/-- The exact atomic output of a raw release pair consists of remapped values followed by
the original group's unchanged closure. Witness: factor the real publisher fold twice.
-/
theorem IncrementalPublisher.normalizeBatch_groupPair (publisher : IncrementalPublisher)
    (before : List WorkQueueEvent) (group : Execution.DeliveryNode)
    (values : List ExecutionGroupValue) (groups streams : List Execution.DeliveryNode)
    (after : List WorkQueueEvent)
    : let prior := publisher.normalizeBatch before
      let carrier := prior.1.handleWorkQueueEvent (.groupSuccess group groups streams)
      (publisher.normalizeBatch
        (before
          ++ .groupValues group values
              :: .groupSuccess group groups streams
              :: after)).2.flatMap
        publicationAtoms
      = prior.2.flatMap publicationAtoms
        ++ (prior.1.handleWorkQueueEvent (.groupValues group values)).2
        ++ .groupSuccess group groups streams
            :: (carrier.1.normalizeBatch after).2.flatMap publicationAtoms := by
  simp only [IncrementalPublisher.normalizeBatch_append,
    IncrementalPublisher.normalizeBatch_cons, List.flatMap_append]
  rw [IncrementalPublisher.groupValues_atoms]
  simp only [IncrementalPublisher.handleWorkQueueEvent, publicationAtoms,
    List.flatMap_singleton, List.singleton_append, List.append_assoc]

namespace GroupPublicationOrigin

/-- Atomic index of the raw triggering group's successful closure. -/
def carrierIndex {publisher raw index owner payload}
    (origin : GroupPublicationOrigin publisher raw index owner payload)
    : Nat :=
  ((publisher.normalizeBatch origin.before).2.flatMap publicationAtoms).length
  + origin.values.length

/-- The raw output and contributor-bearing value are retained by the origin witness.
Witness: membership in the exact raw block and its indexed value list.
-/
theorem members {publisher raw index owner payload}
    (origin : GroupPublicationOrigin publisher raw index owner payload)
    : Execution.WorkQueueEvent.groupValues origin.group origin.values ∈ raw
      ∧ origin.value ∈ origin.values := by
  exact ⟨by simp [origin.rawEq], List.mem_of_getElem? origin.found⟩

/-- Every remapped value strictly precedes its raw triggering group's successful closure.
Witness: the value offset is in bounds, while the carrier follows the whole value block.
-/
theorem before_carrier {publisher raw index owner payload}
    (origin : GroupPublicationOrigin publisher raw index owner payload)
    : index < origin.carrierIndex := by
  have bounded := (List.getElem?_eq_some_iff.mp origin.found).1
  simp only [carrierIndex, origin.position]
  omega

/-- The exact normalized history contains the original successful release carrier.
Witness: the pair equation and the lengths of its preceding atomic prefix and value map.
-/
theorem carrier {publisher raw index owner payload}
    (origin : GroupPublicationOrigin publisher raw index owner payload)
    : ((publisher.normalizeBatch raw).2.flatMap publicationAtoms)[origin.carrierIndex]?
      = some (.groupSuccess origin.group origin.groups origin.streams) := by
  have output := congrArg
    (fun raw => (publisher.normalizeBatch raw).2.flatMap publicationAtoms) origin.rawEq
  rw [publisher.normalizeBatch_groupPair] at output
  rw [output]
  rw [List.getElem?_append_right (by
    simp only [List.length_append, IncrementalPublisher.handleWorkQueueEvent,
      List.length_map, carrierIndex]
    exact Nat.le_refl _)]
  simp [carrierIndex, IncrementalPublisher.handleWorkQueueEvent]

/-- Any prefix of a normalized object block leaves notices and completions unchanged.
Witness: object publications contribute neither pending nor completed refs.
-/
theorem object_prefix_refs (publisher : IncrementalPublisher)
    (group : Execution.DeliveryNode) (values : List ExecutionGroupValue) (count : Nat)
    : pendingRefs
          ((publisher.handleWorkQueueEvent (.groupValues group values)).2.take count)
        = []
      ∧ completedRefs
          ((publisher.handleWorkQueueEvent (.groupValues group values)).2.take count)
        = [] := by
  simp [IncrementalPublisher.handleWorkQueueEvent, ← List.map_take,
    pendingRefs, completedRefs, List.flatMap_map, eventPending, eventCompleted]

/-- Notice state is identical before the selected value and its successful carrier.
Witness: both prefixes differ only by singleton object publications; no intervening
announcement or closure can explain a newly open supporter at the later boundary.
-/
theorem noticeState {publisher raw index owner payload}
    (origin : GroupPublicationOrigin publisher raw index owner payload)
    : let atoms := (publisher.normalizeBatch raw).2.flatMap publicationAtoms
      pendingRefs (atoms.take index) = pendingRefs (atoms.take origin.carrierIndex)
      ∧ completedRefs (atoms.take index)
        = completedRefs (atoms.take origin.carrierIndex) := by
  dsimp only
  let prior := publisher.normalizeBatch origin.before
  let objects := (prior.1.handleWorkQueueEvent (.groupValues origin.group origin.values)).2
  have size : objects.length = origin.values.length := by
    simp [objects, IncrementalPublisher.handleWorkQueueEvent]
  have bounded := (List.getElem?_eq_some_iff.mp origin.found).1
  have atIndex : index = (prior.2.flatMap publicationAtoms).length + origin.offset :=
    origin.position
  have atCarrier : origin.carrierIndex
      = (prior.2.flatMap publicationAtoms).length + objects.length := by
    simp only [carrierIndex, size, prior]
  have output := congrArg
    (fun raw => (publisher.normalizeBatch raw).2.flatMap publicationAtoms) origin.rawEq
  rw [publisher.normalizeBatch_groupPair] at output
  have takeEq (count : Nat) (bound : count ≤ objects.length)
      : ((publisher.normalizeBatch raw).2.flatMap publicationAtoms).take
          ((prior.2.flatMap publicationAtoms).length + count)
        = prior.2.flatMap publicationAtoms ++ objects.take count := by
    rw [output]
    change ((prior.2.flatMap publicationAtoms ++ objects) ++ _).take _ = _
    rw [List.take_append_of_le_length (by simp only [List.length_append]; omega)]
    simp only [List.take_append, List.take_of_length_le (Nat.le_add_right _ _),
      Nat.add_sub_cancel_left]
  have first := takeEq origin.offset (by omega)
  have last := takeEq objects.length (Nat.le_refl _)
  simp only [← atIndex] at first
  simp only [← atCarrier] at last
  rw [first, last]
  have selectedRefs := object_prefix_refs prior.1 origin.group origin.values origin.offset
  have allRefs := object_prefix_refs prior.1 origin.group origin.values objects.length
  change pendingRefs (prior.2.flatMap publicationAtoms ++ objects.take origin.offset)
        = pendingRefs (prior.2.flatMap publicationAtoms ++ objects.take objects.length)
    ∧ completedRefs (prior.2.flatMap publicationAtoms ++ objects.take origin.offset)
        = completedRefs (prior.2.flatMap publicationAtoms ++ objects.take objects.length)
  simp only [pendingRefs, completedRefs, List.flatMap_append] at selectedRefs allRefs ⊢
  exact ⟨by rw [selectedRefs.1, allRefs.1], by rw [selectedRefs.2, allRefs.2]⟩

-----------------------------------------------------------------------------------------
-- Recover the original full value at its object-only rank
-----------------------------------------------------------------------------------------

/-- The strict atomic prefix ends at the selected value's offset in its remapped block.
Witness: factor the actual raw pair and take only its preceding object values.
-/
theorem valuePrefix {publisher raw index owner payload}
    (origin : GroupPublicationOrigin publisher raw index owner payload)
    : let prior := publisher.normalizeBatch origin.before
      ((publisher.normalizeBatch raw).2.flatMap publicationAtoms).take index
      = prior.2.flatMap publicationAtoms
        ++ ((prior.1.handleWorkQueueEvent
              (.groupValues origin.group origin.values)).2.take
              origin.offset) := by
  let prior := publisher.normalizeBatch origin.before
  let objects := (prior.1.handleWorkQueueEvent (.groupValues origin.group origin.values)).2
  have size : objects.length = origin.values.length := by
    simp [objects, IncrementalPublisher.handleWorkQueueEvent]
  have inside := (List.getElem?_eq_some_iff.mp origin.found).1
  have position : index = (prior.2.flatMap publicationAtoms).length + origin.offset :=
    origin.position
  have output := congrArg
    (fun raw => (publisher.normalizeBatch raw).2.flatMap publicationAtoms) origin.rawEq
  rw [publisher.normalizeBatch_groupPair] at output
  rw [output]
  change ((prior.2.flatMap publicationAtoms ++ objects) ++ _).take index = _
  rw [List.take_append_of_le_length (by simp only [List.length_append, size]; omega)]
  simp only [position, List.take_append,
    List.take_of_length_le (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
  rfl

/-- Object-only rank is unchanged by publisher ID remapping and stream atomization.
Witness: count the complete normalized prefix and the selected raw block's value offset.
-/
theorem objectRank {publisher raw index owner payload}
    (origin : GroupPublicationOrigin publisher raw index owner payload)
    : ((((publisher.normalizeBatch raw).2.flatMap publicationAtoms).take index).flatMap
        normalizedObjectValues).length
      = (origin.before.flatMap WorkQueueEvent.objectValues).length + origin.offset := by
  have atomValues (events : List Execution.WorkQueueEvent)
      : (events.flatMap publicationAtoms).flatMap normalizedObjectValues
        = events.flatMap normalizedObjectValues := by
    induction events with
    | nil => rfl
    | cons event rest ih =>
        simp only [List.flatMap_cons, List.flatMap_append,
          (publicationAtoms_values event).1, ih]
  rw [origin.valuePrefix, List.flatMap_append, List.length_append, atomValues,
    IncrementalPublisher.normalizeBatch_objectValues]
  congr 1
  have inside := (List.getElem?_eq_some_iff.mp origin.found).1
  simp only [IncrementalPublisher.handleWorkQueueEvent, ← List.map_take,
    List.flatMap_map, normalizedObjectValues, ← List.map_eq_flatMap,
    List.length_map, List.length_take, Nat.min_eq_left (Nat.le_of_lt inside)]

/-- The full raw value at an object's normalized rank is its original contributing value.
Witness: raw prefix decomposition and the preserved object rank select the very same
indexed value. This remains valid when several distinct tasks have equal wire payloads.
-/
theorem rawValue_atRank {publisher raw index owner payload}
    (origin : GroupPublicationOrigin publisher raw index owner payload)
    : let count :=
        ((((publisher.normalizeBatch raw).2.flatMap publicationAtoms).take index).flatMap
          normalizedObjectValues).length
      (raw.flatMap WorkQueueEvent.objectValues)[count]? = some origin.value := by
  dsimp only
  rw [origin.objectRank]
  have output := congrArg (List.flatMap WorkQueueEvent.objectValues) origin.rawEq
  rw [output]
  simp only [List.flatMap_append, List.flatMap_cons, WorkQueueEvent.objectValues,
    List.nil_append]
  rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    List.getElem?_append_left (List.getElem?_eq_some_iff.mp origin.found).1]
  exact origin.found

end GroupPublicationOrigin

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
