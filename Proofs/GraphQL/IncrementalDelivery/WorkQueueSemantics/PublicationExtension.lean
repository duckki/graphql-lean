import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.HistoryExtension

/-! Extending the existential publication matching without changing past observations. -/

namespace GraphQL.IncrementalDelivery.WorkQueueSemantics
open GraphQL.IncrementalDelivery.Execution

-----------------------------------------------------------------------------------------
-- Only observed matching entries matter
-----------------------------------------------------------------------------------------

/-- Publication facts depend only on matching entries inside the supplied output list.
Witness: each successful event lookup gives an index strictly below its length.
-/
theorem published_matching_eq {matching next : PublicationMatching}
    {events : List WorkQueueEvent}
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

/-- Reached node-failure cuts inspect only matching entries in their output prefix.
Witness: every cut snapshot is a prefix of the supplied history.
-/
theorem nodeFailed_matching_eq {work matching next events failures}
    (equal : ∀ index < events.length, matching index = next index)
    : NodeFailed work matching events failures
      = NodeFailed work next events failures := by
  have snapshots (cut : Nat) : Published matching (events.take cut)
      = Published next (events.take cut) :=
    published_matching_eq (fun index before => equal index (by
      simp only [List.length_take] at before; omega))
  funext ref
  simp only [NodeFailed, snapshots]

/-- Reached cancellation cuts inspect only matching entries in their output prefix.
Witness: every cut snapshot is a prefix of the supplied history.
-/
theorem taskCancelled_matching_eq {work matching next events failures}
    (equal : ∀ index < events.length, matching index = next index)
    : TaskCancelled work matching events failures
      = TaskCancelled work next events failures := by
  have snapshots (cut : Nat) : Published matching (events.take cut)
      = Published next (events.take cut) :=
    published_matching_eq (fun index before => equal index (by
      simp only [List.length_take] at before; omega))
  funext occurrence
  simp only [TaskCancelled, snapshots]

/-- Failure licensing retains its original cuts when observed matching entries agree.
Witness: rewrite cancellation at each prefix, leaving structural and open-owner facts.
-/
theorem FailureWitness.change_matching {work initial matching next events failures}
    (witness : FailureWitness work initial matching events failures)
    (equal : ∀ index < events.length, matching index = next index)
    : FailureWitness work initial next events failures := by
  intro before cut occurrence after same
  obtain ⟨bounded, ordered, known, active⟩ := witness before cut occurrence after same
  refine ⟨bounded, ordered, known, ?_⟩
  rwa [← taskCancelled_matching_eq (matching := matching) (by
    intro index inside
    apply equal
    simp only [List.length_take] at inside; omega)]

/-- Publication readiness depends only on already observed matching entries. Witness:
rewrite every previous-publication premise using prefix agreement.
-/
theorem canPublish_matching_eq {work matching next events failed occurrence producer}
    (equal : ∀ index < events.length, matching index = next index)
    : CanPublish work matching events failed occurrence producer
      = CanPublish work next events failed occurrence producer := by
  simp only [CanPublish, published_matching_eq equal, taskCancelled_matching_eq equal]

/-- Effective owner selection depends only on observed matching entries.
Witness: rewrite the reached failure cuts for every candidate owner.
-/
theorem owner_matching_eq {work initial matching next events failed owners node}
    (equal : ∀ index < events.length, matching index = next index)
    : PublicationOwner work initial matching events failed owners node
      = PublicationOwner work initial next events failed owners node := by
  simp only [PublicationOwner, HealthyOpenOwner, nodeFailed_matching_eq equal]

/-- An event inspects past matching entries and, for a value, its current index only.
Witness: unfold the event rule and rewrite previous or carrier-inclusive publications.
-/
theorem eventAllowed_matching_eq {work initial matching next events failed event}
    (equal : ∀ index ≤ events.length, matching index = next index)
    : EventAllowed work initial matching events failed event
      = EventAllowed work initial next events failed event := by
  have past := published_matching_eq (events := events)
    (fun index before => equal index (Nat.le_of_lt before))
  have carrier (output : WorkQueueEvent) : Published matching (events ++ [output])
      = Published next (events ++ [output]) := by
    apply published_matching_eq
    intro index before
    apply equal
    simp only [List.length_append, List.length_singleton] at before
    omega
  have snapshots (observed : List WorkQueueEvent) (bound : observed.length ≤ events.length + 1)
      : (NodeFailed work matching observed
          (failed.filter (fun entry => entry.1 ≤ events.length))
          = NodeFailed work next observed
            (failed.filter (fun entry => entry.1 ≤ events.length)))
        ∧ (TaskCancelled work matching observed
          (failed.filter (fun entry => entry.1 ≤ events.length))
          = TaskCancelled work next observed
            (failed.filter (fun entry => entry.1 ≤ events.length))) := by
    have agree : ∀ index < observed.length, matching index = next index :=
      fun index inside => equal index (by omega)
    exact ⟨nodeFailed_matching_eq agree, taskCancelled_matching_eq agree⟩
  have prior := snapshots events (by omega)
  have after (output : WorkQueueEvent) := snapshots (events ++ [output]) (by simp)
  cases event <;> simp only [EventAllowed, CanPublish, PublicationOwner, HealthyOpenOwner,
    NodeAccounted, TaskAccounted, prior.1, prior.2, (after _).1, (after _).2,
    Announcements, CanAnnounce, DependencySatisfied, past, carrier,
    equal events.length (Nat.le_refl _)]

/-- Changing unobserved matching entries preserves an explained history. Witness:
each existing event uses only indices at or before its own index, all inside the prefix.
-/
theorem Explains.change_matching {work groups streams events matching next failures}
    (explained : Explains work groups streams events matching failures)
    (equal : ∀ index < events.length, matching index = next index)
    : Explains work groups streams events next failures := by
  refine ⟨explained.1, explained.2.1.change_matching equal, ?_⟩
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

/-- Appending outputs cannot change past failure snapshots when every supplied cut is
already reached. Witness: each cut takes the same original publication prefix.
-/
theorem causality_append_eq {work matching events failures}
    (bounded : ∀ entry ∈ failures, entry.1 ≤ events.length) (tail : List WorkQueueEvent)
    : NodeFailed work matching (events ++ tail) failures
        = NodeFailed work matching events failures
      ∧ TaskCancelled work matching (events ++ tail) failures
        = TaskCancelled work matching events failures := by
  constructor <;> funext ref <;> apply propext
  · constructor
    · rintro ⟨cut, member, _, cause⟩
      obtain ⟨entry, included, same⟩ := List.mem_map.mp member
      have reached : cut ≤ events.length := same ▸ bounded entry included
      exact ⟨cut, List.mem_map.mpr ⟨entry, included, same⟩, reached,
        by simpa only [List.take_append_of_le_length reached] using cause⟩
    · exact fun failed => failed.append tail
  · constructor
    · rintro ⟨cut, member, _, cause⟩
      obtain ⟨entry, included, same⟩ := List.mem_map.mp member
      have reached : cut ≤ events.length := same ▸ bounded entry included
      exact ⟨cut, List.mem_map.mpr ⟨entry, included, same⟩, reached,
        by simpa only [List.take_append_of_le_length reached] using cause⟩
    · exact fun cancelled => cancelled.append tail

/-- Changing only a carrier's notices or control payload preserves causal evidence.
Witness: equal value status yields identical publications at every failure cut.
-/
theorem causality_carrier_eq {work matching events failures left right}
    (sameValue : IsValue left ↔ IsValue right)
    : NodeFailed work matching (events ++ [left]) failures
        = NodeFailed work matching (events ++ [right]) failures
      ∧ TaskCancelled work matching (events ++ [left]) failures
        = TaskCancelled work matching (events ++ [right]) failures := by
  have snapshots (cut : Nat) :
      Published matching ((events ++ [left]).take cut)
        = Published matching ((events ++ [right]).take cut) := by
    by_cases earlier : cut ≤ events.length
    · simp only [List.take_append_of_le_length earlier]
    · have leftBound : (events ++ [left]).length ≤ cut := by
        simp only [List.length_append, List.length_singleton]; omega
      have rightBound : (events ++ [right]).length ≤ cut := by
        simp only [List.length_append, List.length_singleton]; omega
      simp only [List.take_of_length_le leftBound, List.take_of_length_le rightBound]
      funext occurrence
      apply propext
      simp only [published_append_singleton_iff, sameValue]
  constructor <;> funext ref <;>
    simp only [NodeFailed, TaskCancelled, List.length_append, List.length_singleton,
      snapshots]

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
theorem published_matchNext {event : WorkQueueEvent} (value : IsValue event)
    (matching : PublicationMatching) (events : List WorkQueueEvent)
    (occurrence : Occurrence)
    : Published (matchNext matching events.length occurrence) (events ++ [event])
        occurrence := by exact ⟨events.length, event, by simp, value, by simp [matchNext]⟩

/-- Adding a newly matched event preserves every already accounted task. Witness:
cancellation at the unchanged cut snapshot or prefix-preserving publication lookup.
-/
theorem TaskAccounted.matchNext_append {work matching events failed occurrence}
    (accounted : TaskAccounted work matching events failed occurrence)
    (next : Occurrence) (event : WorkQueueEvent)
    : TaskAccounted work (matchNext matching events.length next) (events ++ [event])
        failed occurrence := by
  rcases accounted with cancelled | published
  · rw [taskCancelled_matching_eq
      (fun _ before => matchNext_before matching next before)] at cancelled
    exact Or.inl (cancelled.append [event])
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
    (ready : CanPublish work matching events failures occurrence producer)
    (selected
      : PublicationOwner work ((groups ++ streams).map DeliveryNode.ref) matching events
          failures owners owner)
    : Explains work groups streams
        (events ++ [.groupValues owner [{ path, data, errors }]])
        (matchNext matching events.length occurrence) failures := by
  have same := fun index before => matchNext_before matching occurrence
    (index := events.length) (position := index) before
  apply (explained.change_matching same).append_event
  simp only [EventAllowed, canPublish_filter (Nat.le_refl _),
    owner_filter (Nat.le_refl _)]
  refine ⟨owners, producer, { path, data, errors }, rfl, ?_, ?_,
    owner_matching_eq same ▸ selected⟩
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
    (ready : CanPublish work matching events failures occurrence producer)
    (selected
      : PublicationOwner work ((groups ++ streams).map DeliveryNode.ref) matching events
          failures owners node)
    : Explains work groups streams
        (events ++ [.streamValues node [{ item, errors }] [] []])
        (matchNext matching events.length occurrence) failures := by
  have same := fun index before => matchNext_before matching occurrence
    (index := events.length) (position := index) before
  apply (explained.change_matching same).append_event
  simp only [EventAllowed, canPublish_filter (Nat.le_refl _),
    owner_filter (Nat.le_refl _)]
  refine ⟨
    owners,
    producer,
    { item, errors },
    rfl,
    ?_,
    ?_,
    owner_matching_eq same ▸ selected,
    by simp [Announcements]
  ⟩
  · simpa only [matchNext, ↓reduceIte] using known
  · simpa only [matchNext, ↓reduceIte] using (canPublish_matching_eq same ▸ ready)

end GraphQL.IncrementalDelivery.WorkQueueSemantics
