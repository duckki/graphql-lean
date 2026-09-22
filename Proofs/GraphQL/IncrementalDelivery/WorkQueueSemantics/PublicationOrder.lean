import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.Publication

/-! Publication dependencies constrain observations, without selecting a schedule. -/

namespace GraphQL.IncrementalDelivery.WorkQueueSemantics
open GraphQL.IncrementalDelivery.Execution

/-- A value event retains its producing task's readiness witness; extract the event rule.
-/
theorem EventAllowed.publicationReady {work initial matching before failed event}
    (allowed : EventAllowed work initial matching before failed event)
    (value : IsValue event)
    : ∃ owners producer payload,
        TaskAt work (matching before.length) owners producer payload
        ∧ CanPublish work matching before failed (matching before.length) producer := by
  cases event <;> try contradiction
  case groupValues node values =>
    simp only [EventAllowed, canPublish_filter (Nat.le_refl _)] at allowed
    obtain ⟨owners, producer, ⟨path, data, errors, deliveryGroups⟩, _, known, ready, _⟩ := allowed
    exact ⟨owners, producer, _, known, ready⟩
  case streamValues node values groups streams =>
    simp only [EventAllowed, canPublish_filter (Nat.le_refl _)] at allowed
    obtain ⟨owners, producer, ⟨item, errors⟩, _, known, ready, _⟩ := allowed
    exact ⟨owners, producer, _, known, ready⟩

/-- Publication in a prefix supplies a strictly earlier full-history index; witness:
the prefix lookup bound and preservation of lookups by take.
-/
theorem Published.before {matching occurrence cut} {events : List WorkQueueEvent}
    (published : Published matching (events.take cut) occurrence)
    : ∃ index event,
        index < cut
        ∧ events[index]? = some event
        ∧ IsValue event
        ∧ matching index = occurrence := by
  obtain ⟨index, event, selected, value, same⟩ := published
  have bound := (List.getElem?_eq_some_iff.mp selected).choose
  have earlier : index < cut := by simp only [List.length_take] at bound; omega
  exact ⟨index, event, earlier,
    (List.getElem?_take_of_lt earlier).symm.trans selected, value, same⟩

/-- An actually failed task cannot have a successful value publication.
Witness: failure licensing and published provenance refer to its same fixed payload.
-/
theorem Explains.failed_unpublished
    {work groups streams events matching failures occurrence cut}
    (explained : Explains work groups streams events matching failures)
    (failed : occurrence ∈ failedBefore failures cut)
    : ¬Published matching events occurrence := by
  obtain ⟨⟨boundary, task⟩, kept, same⟩ := List.mem_map.mp failed
  dsimp only at same
  subst task
  obtain ⟨before, after, equal⟩ := List.mem_iff_append.mp (List.mem_filter.mp kept).1
  obtain ⟨owners, producer, payload, known, fails, _⟩ :=
    (explained.2.1 before boundary occurrence after equal).2.2.1
  intro published
  have success := explained.published_succeeds known published
  simp only [success, Option.isSome_none, Bool.false_eq_true] at fails

/-- Admitted publication and historical cancellation are mutually exclusive.
Witness: publication before the cut contradicts its snapshot; publication after the
cut contradicts the emitting event's cancellation check.
-/
theorem Explains.cancelled_unpublished
    {work groups streams events matching failures occurrence}
    (explained : Explains work groups streams events matching failures)
    (cancelled : TaskCancelled work matching events failures occurrence)
    : ¬Published matching events occurrence := by
  obtain ⟨cut, member, reached, cause⟩ := cancelled
  rintro ⟨index, event, selected, value, same⟩
  by_cases earlier : index < cut
  · apply cause.unpublished
    exact ⟨index, event, by simpa only [List.getElem?_take_of_lt earlier] using selected,
      value, same⟩
  · have cutBefore : cut ≤ index := Nat.le_of_not_gt earlier
    have inside := (List.getElem?_eq_some_iff.mp selected).1
    obtain ⟨owners, producer, payload, known, ready⟩ :=
      (explained.2.2 index event selected).publicationReady value
    apply ready.2.1
    have length : (events.take index).length = index := by
      simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt inside)]
    rw [length, same]
    refine ⟨cut, member, by omega, ?_⟩
    simpa only [List.take_take, Nat.min_eq_left cutBefore] using cause

/-- A published child's generating task occurs earlier in the same history. Witness:
the task descriptor is unique, so its producer is the one required by CanPublish.
-/
theorem Explains.producer_before {work groups streams events matching failures}
    (explained : Explains work groups streams events matching failures)
    {index event owners producerOccurrence payload}
    (selected : events[index]? = some event) (value : IsValue event)
    (task : TaskAt work (matching index) owners (some producerOccurrence) payload)
    : ∃ earlier previous,
        earlier < index
        ∧ events[earlier]? = some previous
        ∧ IsValue previous
        ∧ matching earlier = producerOccurrence := by
  have bound := (List.getElem?_eq_some_iff.mp selected).choose
  have ready := (explained.2.2 index event selected).publicationReady value
  simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt bound)] at ready
  obtain ⟨otherOwners, producer, otherPayload, known, ready⟩ := ready
  have same := TaskAt.unique known task
  exact (ready.2.2.1 producerOccurrence same.2.1).before

/-- Publishing a noninitial stream item requires its predecessor earlier in the history.
Witness: the stream-specific readiness premise, independent of notices or owner ties.
-/
theorem Explains.item_predecessor {work groups streams events matching failures}
    (explained : Explains work groups streams events matching failures)
    {index event address ordinal}
    (selected : events[index]? = some event) (value : IsValue event)
    (same : matching index = .item address (ordinal + 1))
    : ∃ earlier previous,
        earlier < index
        ∧ events[earlier]? = some previous
        ∧ IsValue previous
        ∧ matching earlier = .item address ordinal := by
  have bound := (List.getElem?_eq_some_iff.mp selected).choose
  have ready := (explained.2.2 index event selected).publicationReady value
  simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt bound), same] at ready
  obtain ⟨_, _, _, _, ready⟩ := ready
  exact (show Published matching (events.take index) (.item address ordinal)
    from ready.2.2.2).before

/-- Every lower ordinal has an earlier publication when a stream item is published.
Witness: induction through predecessor publications; unrelated outputs may interleave.
-/
theorem Explains.item_earlier {work groups streams events matching failures}
    (explained : Explains work groups streams events matching failures)
    {index event address ordinal earlierOrdinal}
    (selected : events[index]? = some event) (value : IsValue event)
    (same : matching index = .item address ordinal) (less : earlierOrdinal < ordinal)
    : ∃ earlier previous,
        earlier < index
        ∧ events[earlier]? = some previous
        ∧ IsValue previous
        ∧ matching earlier = .item address earlierOrdinal := by
  induction ordinal generalizing index event with
  | zero => omega
  | succ ordinal ih =>
      obtain ⟨prior, previous, before, atPrior, isValue, predecessor⟩ :=
        explained.item_predecessor selected value same
      by_cases equal : earlierOrdinal = ordinal
      · subst earlierOrdinal
        exact ⟨prior, previous, before, atPrior, isValue, predecessor⟩
      · obtain ⟨earlier, first, beforePrior, atEarlier, firstValue, matched⟩ :=
          ih atPrior isValue predecessor (by omega)
        exact ⟨earlier, first, Nat.lt_trans beforePrior before, atEarlier, firstValue,
          matched⟩

/-- Stream ordinals and their publication indices have exactly the same strict order.
Witness: predecessor chains give earlier occurrences and one-shot publication identifies
their indices. This permits arbitrary interleaving of different streams.
-/
theorem Explains.item_order {work groups streams events matching failures}
    (explained : Explains work groups streams events matching failures)
    {left right first second address firstOrdinal secondOrdinal}
    (firstAt : events[left]? = some first) (firstValue : IsValue first)
    (firstTask : matching left = .item address firstOrdinal)
    (secondAt : events[right]? = some second) (secondValue : IsValue second)
    (secondTask : matching right = .item address secondOrdinal)
    : left < right ↔ firstOrdinal < secondOrdinal := by
  have ordered {a b i j x y}
      (atI : events[i]? = some x) (valueI : IsValue x)
      (taskI : matching i = .item address a)
      (atJ : events[j]? = some y) (valueJ : IsValue y)
      (taskJ : matching j = .item address b) (less : a < b) : i < j := by
    obtain ⟨earlier, previous, before, selected, value, same⟩ :=
      explained.item_earlier atJ valueJ taskJ less
    have equal := explained.publication_unique atI valueI selected value
      (taskI.trans same.symm)
    simpa only [equal] using before
  constructor
  · intro less
    by_cases equal : firstOrdinal = secondOrdinal
    · have same := explained.publication_unique firstAt firstValue secondAt secondValue
        (firstTask.trans (equal ▸ secondTask).symm)
      omega
    · by_cases reverse : secondOrdinal < firstOrdinal
      · have := ordered secondAt secondValue secondTask firstAt firstValue firstTask
          reverse
        omega
      · omega
  · exact ordered firstAt firstValue firstTask secondAt secondValue secondTask

end GraphQL.IncrementalDelivery.WorkQueueSemantics
