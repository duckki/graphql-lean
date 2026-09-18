import Proofs.GraphQL.IncrementalDelivery.WorkScheduler.HistoryExtension

/-! Extending the existential publication matching without changing past observations. -/

namespace GraphQL.IncrementalDelivery.WorkScheduler
open GraphQL.IncrementalDelivery.Execution

-----------------------------------------------------------------------------------------
-- Only observed matching entries matter
-----------------------------------------------------------------------------------------

/-- Publication facts depend only on matching entries inside the supplied output list.
Witness: each successful event lookup gives an index strictly below its length.
-/
theorem published_matching_eq {matching next : PublicationMatching}
    {events : List WorkEvent}
    (equal : ∀ index < events.length, matching index = next index)
    : Published matching events = Published next events := by
  funext occurrence
  apply propext
  constructor
  · rintro ⟨index, event, selected, value, same⟩
    exact ⟨index, event, selected, value,
      (equal index (List.getElem?_eq_some_iff.mp selected).1).symm.trans same⟩
  · rintro ⟨index, event, selected, value, same⟩
    exact ⟨index, event, selected, value,
      (equal index (List.getElem?_eq_some_iff.mp selected).1).trans same⟩

/-- Publication readiness depends only on already observed matching entries. Witness:
rewrite every previous-publication premise using prefix agreement.
-/
theorem canPublish_matching_eq {work matching next events failed occurrence producer}
    (equal : ∀ index < events.length, matching index = next index)
    : CanPublish work matching events failed occurrence producer
      = CanPublish work next events failed occurrence producer := by
  simp only [CanPublish, published_matching_eq equal]

/-- An event inspects past matching entries and, for a value, its current index only.
Witness: unfold the event rule and rewrite previous or carrier-inclusive publications.
-/
theorem eventAllowed_matching_eq {work initial matching next events failed event}
    (equal : ∀ index ≤ events.length, matching index = next index)
    : EventAllowed work initial matching events failed event
      = EventAllowed work initial next events failed event := by
  have past := published_matching_eq (events := events)
    (fun index before => equal index (Nat.le_of_lt before))
  have carrier (output : WorkEvent) : Published matching (events ++ [output])
      = Published next (events ++ [output]) := by
    apply published_matching_eq
    intro index before
    apply equal
    simp only [List.length_append, List.length_singleton] at before
    omega
  cases event <;> simp only [EventAllowed, CanPublish, NodeAccounted, Accounted,
    Announcements, CanAnnounce, DependencySatisfied, past, carrier,
    equal events.length (Nat.le_refl _)]

/-- Changing unobserved matching entries preserves an explained history. Witness:
each existing event uses only indices at or before its own index, all inside the prefix.
-/
theorem Explains.change_matching {work groups streams events matching next failures}
    (explained : Explains work groups streams events matching failures)
    (equal : ∀ index < events.length, matching index = next index)
    : Explains work groups streams events next failures := by
  refine ⟨explained.1, explained.2.1, ?_⟩
  intro index event selected
  have bound := (List.getElem?_eq_some_iff.mp selected).1
  rw [← eventAllowed_matching_eq (matching := matching) (next := next) (by
    intro earlier before
    simp only [List.length_take] at before
    exact equal earlier (by omega))]
  exact explained.2.2 index event selected

-----------------------------------------------------------------------------------------
-- Constructing fresh value publications
-----------------------------------------------------------------------------------------

/-- A final event either retains an earlier publication or publishes its own matched
occurrence. Witness: split the lookup index at the old history length.
-/
theorem published_append_singleton_iff {matching events event occurrence}
    : Published matching (events ++ [event]) occurrence
      ↔ Published matching events occurrence
        ∨ IsValue event ∧ matching events.length = occurrence := by
  constructor
  · rintro ⟨index, output, selected, value, same⟩
    by_cases earlier : index < events.length
    · exact Or.inl ⟨index, output,
        (List.getElem?_append_left earlier).symm.trans selected, value, same⟩
    · have bound := (List.getElem?_eq_some_iff.mp selected).1
      have last : index = events.length := by
        simp only [List.length_append, List.length_singleton] at bound
        omega
      subst index
      have equal : output = event := by simpa using selected.symm
      exact Or.inr ⟨equal ▸ value, same⟩
  · rintro (previous | ⟨value, same⟩)
    · exact previous.append [event]
    · exact ⟨events.length, event, by simp, value, same⟩

/-- Assign one new output index to its task without altering any existing publication.
This is a finite proof witness, not a selection of future scheduler observations.
-/
def matchNext (matching : PublicationMatching) (index : Nat) (occurrence : Occurrence)
    : PublicationMatching :=
  fun position => if position = index then occurrence else matching position

/-- The new assignment agrees with every earlier entry. Witness: a strict earlier index
cannot equal the assigned one.
-/
theorem matchNext_before (matching : PublicationMatching) (occurrence : Occurrence)
    {index position : Nat} (earlier : position < index)
    : matching position = matchNext matching index occurrence position := by
  simp only [matchNext, ite_eq_right (Nat.ne_of_lt earlier)]

/-- Appending a value at its assigned index publishes that occurrence. Witness: the last
event lookup and the new matching entry, regardless of earlier equal payload values.
-/
theorem published_matchNext {event : WorkEvent} (value : IsValue event)
    (matching : PublicationMatching) (events : List WorkEvent) (occurrence : Occurrence)
    : Published (matchNext matching events.length occurrence) (events ++ [event])
        occurrence := by exact ⟨events.length, event, by simp, value, by simp [matchNext]⟩

/-- Adding a newly matched event preserves every already accounted task. Witness:
unchanged cancellation or prefix-preserving publication lookup.
-/
theorem Accounted.matchNext_append {work matching events failed occurrence}
    (accounted : Accounted work matching events failed occurrence)
    (next : Occurrence) (event : WorkEvent)
    : Accounted work (matchNext matching events.length next) (events ++ [event])
        failed occurrence := by
  rcases accounted with cancelled | published
  · exact Or.inl cancelled
  · rw [published_matching_eq (fun _ before => matchNext_before matching next before)]
      at published
    exact Or.inr (published.append [event])

/-- A ready object task with a permitted owner can publish its fixed successful payload.
Witness: assign the next matching index and append exactly one group-value event.
-/
theorem Explains.publish_object
    {work groups streams events matching failures
      occurrence owners producer path data errors owner}
    (explained : Explains work groups streams events matching failures)
    (known : TaskAt work occurrence owners producer (.object path (.ok (data, errors))))
    (ready
      : CanPublish work matching events (failedBefore failures events.length)
          occurrence producer)
    (selected
      : Owner work ((groups ++ streams).map DeliveryNode.key) events
          (failedBefore failures events.length) owners owner)
    : Explains work groups streams
        (events ++ [.groupValues owner [{ path, data, errors }]])
        (matchNext matching events.length occurrence) failures := by
  have same := fun index before => matchNext_before matching occurrence
    (index := events.length) (position := index) before
  apply (explained.change_matching same).append_event
  refine ⟨owners, producer, path, data, errors, rfl, ?_, ?_, selected⟩
  · simpa only [matchNext, ↓reduceIte] using known
  · simpa only [matchNext, ↓reduceIte] using (canPublish_matching_eq same ▸ ready)

/-- A ready stream item with its permitted stream owner can publish its fixed payload.
Witness: assign the next matching index and emit one item without additional notices.
Notice-bearing steps can use the general append-event constructor instead.
-/
theorem Explains.publish_item
    {work groups streams events matching failures
      occurrence owners producer node item errors}
    (explained : Explains work groups streams events matching failures)
    (known : TaskAt work occurrence owners producer (.item node (.ok (item, errors))))
    (ready
      : CanPublish work matching events (failedBefore failures events.length)
          occurrence producer)
    (selected
      : Owner work ((groups ++ streams).map DeliveryNode.key) events
          (failedBefore failures events.length) owners node)
    : Explains work groups streams
        (events ++ [.streamValues node [{ item, errors }] [] []])
        (matchNext matching events.length occurrence) failures := by
  have same := fun index before => matchNext_before matching occurrence
    (index := events.length) (position := index) before
  apply (explained.change_matching same).append_event
  refine ⟨owners, producer, item, errors, rfl, ?_, ?_, selected, by simp [Announcements]⟩
  · simpa only [matchNext, ↓reduceIte] using known
  · simpa only [matchNext, ↓reduceIte] using (canPublish_matching_eq same ▸ ready)

end GraphQL.IncrementalDelivery.WorkScheduler
