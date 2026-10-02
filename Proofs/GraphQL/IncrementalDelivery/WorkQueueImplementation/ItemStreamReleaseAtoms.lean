import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NormalizedItemStreamRelease

/-! A child-stream notice on the final item atom retains its inclusive publication prefix. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- A stream notice survives only on the final atom of its item batch
-----------------------------------------------------------------------------------------

/-- An atom carrying a child-stream notice is the final atom of its original item batch.
Witness: all earlier atoms have empty notice lists; recursive item splitting retains the
original owner and child lists only on the last item.
-/
theorem streamPublicationAtoms_streamCarrier (stream groups streams values)
    {index owner items newGroups newStreams child}
    (atEvent
      : (streamPublicationAtoms stream groups streams values)[index]?
        = some (.streamValues owner items newGroups newStreams))
    (noticed : child ∈ newStreams)
    : owner = stream
      ∧ newGroups = groups
      ∧ newStreams = streams
      ∧ index + 1 = values.length := by
  induction values using streamPublicationAtoms.induct generalizing index with
  | case1 => simp [streamPublicationAtoms] at atEvent
  | case2 value =>
      cases index with
      | zero =>
          have same := Execution.WorkQueueEvent.streamValues.inj (Option.some.inj atEvent)
          exact ⟨same.1.symm, same.2.2.1.symm, same.2.2.2.symm, rfl⟩
      | succ index => simp [streamPublicationAtoms] at atEvent
  | case3 value next rest ih =>
      cases index with
      | zero =>
          have same := Execution.WorkQueueEvent.streamValues.inj (Option.some.inj atEvent)
          rw [← same.2.2.2] at noticed
          cases noticed
      | succ index =>
          obtain ⟨ownerSame, groupsSame, streamsSame, length⟩ := ih atEvent
          exact ⟨
            ownerSame,
            groupsSame,
            streamsSame,
            by simp only [List.length_cons] at *; omega
          ⟩

/-- A child-stream-carrying atom comes from a stream-value event and ends its expansion.
Witness: other event kinds cannot produce a stream atom; the item-splitting lemma identifies
the original carrier and its final position. Empty value lists cannot contain a carrier.
-/
theorem publicationAtoms_streamCarrier (event : Execution.WorkQueueEvent)
    {index owner items groups streams child}
    (atEvent
      : (publicationAtoms event)[index]?
        = some (.streamValues owner items groups streams))
    (noticed : child ∈ streams)
    : ∃ values,
        event = .streamValues owner values groups streams
        ∧ index + 1 = (publicationAtoms event).length := by
  have member := List.mem_of_getElem? atEvent
  cases event with
  | groupValues group values =>
      obtain ⟨value, _, impossible⟩ := List.mem_map.mp member
      cases impossible
  | streamValues stream values newGroups newStreams =>
      obtain ⟨rfl, rfl, rfl, size⟩ :=
        streamPublicationAtoms_streamCarrier stream newGroups newStreams values atEvent noticed
      exact ⟨values, rfl, size.trans (streamPublicationAtoms_length ..).symm⟩
  | groupSuccess | groupFailure | streamSuccess | streamFailure | workQueueTermination =>
      simp [publicationAtoms] at member

/-- An atomic stream-notice carrier keeps the inclusive item count of its original carrier.
Witness: the carrier is the final atom of its source event; every earlier expansion preserves
its complete item projection, including object events that contribute no item count.
-/
theorem publicationAtoms_streamCarrier_prefix (events : List Execution.WorkQueueEvent)
    {index owner items groups streams child}
    (atEvent
      : (events.flatMap publicationAtoms)[index]?
        = some (.streamValues owner items groups streams))
    (noticed : child ∈ streams)
    : ∃ sourceIndex values,
        events[sourceIndex]? = some (.streamValues owner values groups streams)
        ∧ (((events.flatMap publicationAtoms).take (index + 1)).flatMap
            normalizedItemValues).length
          = ((events.take (sourceIndex + 1)).flatMap normalizedItemValues).length := by
  induction events generalizing index with
  | nil => simp at atEvent
  | cons event rest ih =>
      rw [List.flatMap_cons] at atEvent ⊢
      by_cases earlier : index < (publicationAtoms event).length
      · have atHead := (List.getElem?_append_left earlier).symm.trans atEvent
        obtain ⟨values, same, endAt⟩ := publicationAtoms_streamCarrier event atHead noticed
        refine ⟨0, values, same ▸ rfl, ?_⟩
        rw [endAt, List.take_left, (publicationAtoms_values event).2]
        simp
      · have later : (publicationAtoms event).length ≤ index := by omega
        have atTail := (List.getElem?_append_right later).symm.trans atEvent
        obtain ⟨sourceIndex, values, sourceAt, count⟩ := ih atTail
        refine ⟨sourceIndex + 1, values, sourceAt, ?_⟩
        rw [List.take_append,
          List.take_of_length_le (by omega : (publicationAtoms event).length ≤ index + 1),
          show index + 1 - (publicationAtoms event).length
            = index - (publicationAtoms event).length + 1 by omega,
          List.flatMap_append, List.length_append, count, (publicationAtoms_values event).2]
        simp only [List.take_succ_cons, List.flatMap_cons, List.length_append]

/-- Item-release support survives atomization with the identical occurrence inventory.
Witness: each noticed child's carrier is final in its original item batch, so its inclusive
item-publication count and exact source occurrence prefix are unchanged.
-/
theorem NormalizedItemStreamReleasePublications.publicationAtoms {work published events}
    (supported : NormalizedItemStreamReleasePublications work published events)
    : NormalizedItemStreamReleasePublications work published
        (events.flatMap publicationAtoms) := by
  intro index owner items groups streams atEvent child noticed
  obtain ⟨sourceIndex, values, sourceAt, count⟩ :=
    publicationAtoms_streamCarrier_prefix events atEvent noticed
  rw [count]
  exact supported sourceIndex owner values groups streams sourceAt child noticed

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
