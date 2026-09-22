import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupProducerOrder

/-! Each raw value block retains its exact labels in permanent registration order. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Consecutive slices of one publication ledger, not independently chosen block labels
-----------------------------------------------------------------------------------------

/-- Every raw event's consecutive object-label slice follows the supplied task registry.
The raw event's payload count fixes the slice; control and stream events use empty slices.
This proof certificate does not require ordering between separate raw value blocks.
-/
def BlocksFollowRegistrations (tasks : List Task)
    : List ObjectPublication → List WorkQueueEvent → Prop
  | _, [] => True
  | published, event :: rest =>
      ((published.take event.objectValues.length).map Prod.fst).Sublist
        (tasks.map Task.occurrence)
      ∧ BlocksFollowRegistrations tasks (published.drop event.objectValues.length) rest

/-- Empty output has no block-order obligation. Witness: the defining empty case. -/
theorem BlocksFollowRegistrations.nil (tasks : List Task)
    (published : List ObjectPublication)
    : BlocksFollowRegistrations tasks published [] :=
  trivial

/-- A longer registry preserves each block's ordered subsequence.
Witness: compose each slice's subsequence with the permanent-registry extension.
-/
theorem BlocksFollowRegistrations.mono {before after published events}
    (ordered : BlocksFollowRegistrations before published events)
    (included : before.Sublist after)
    : BlocksFollowRegistrations after published events := by
  induction events generalizing published with
  | nil => trivial
  | cons event rest ih =>
      exact ⟨ordered.1.trans (included.map _), ih ordered.2⟩

/-- Concatenating raw outputs concatenates their exact occurrence-labelled slices.
Witness: induction through the first output, using its exact total payload count to
split take/drop at each event without identifying occurrences by payload equality.
-/
theorem BlocksFollowRegistrations.append {tasks first second left right}
    (before : BlocksFollowRegistrations tasks first left)
    (after : BlocksFollowRegistrations tasks second right)
    (size : first.length = (left.flatMap WorkQueueEvent.objectValues).length)
    : BlocksFollowRegistrations tasks (first ++ second) (left ++ right) := by
  induction left generalizing first with
  | nil =>
      have empty : first = [] := List.length_eq_zero_iff.mp size
      simpa only [empty, List.nil_append] using after
  | cons event rest ih =>
      have bound : event.objectValues.length ≤ first.length := by
        simp only [List.flatMap_cons, List.length_append] at size
        omega
      change ((List.take event.objectValues.length (first ++ second)).map Prod.fst).Sublist _
        ∧ BlocksFollowRegistrations tasks
          (List.drop event.objectValues.length (first ++ second)) (rest ++ right)
      rw [List.take_append_of_le_length bound, List.drop_append_of_le_length bound]
      refine ⟨before.1, ih before.2 ?_⟩
      simp only [List.length_drop, List.flatMap_cons, List.length_append] at size ⊢
      omega

/-- Raw concatenation splits one ledger at the first raw segment's exact value count.
Witness: peel the first segment and accumulate drop offsets; excess or missing trailing
labels do not affect this equivalence.
-/
theorem BlocksFollowRegistrations.append_iff {tasks published left right}
    : BlocksFollowRegistrations tasks published (left ++ right)
      ↔ BlocksFollowRegistrations tasks published left
        ∧ BlocksFollowRegistrations tasks
            (published.drop (left.flatMap WorkQueueEvent.objectValues).length) right := by
  induction left generalizing published with
  | nil => simp [BlocksFollowRegistrations]
  | cons event rest ih =>
      simp only [List.cons_append, BlocksFollowRegistrations, ih, List.flatMap_cons,
        List.length_append, List.drop_drop, and_assoc]

/-- A segment's block-order checks depend only on its own exact label prefix.
Witness: each event consumes its width and leaves the remaining bounded prefix.
-/
theorem BlocksFollowRegistrations.take_iff {tasks published events}
    : BlocksFollowRegistrations tasks
        (published.take (events.flatMap WorkQueueEvent.objectValues).length) events
      ↔ BlocksFollowRegistrations tasks published events := by
  induction events generalizing published with
  | nil => rfl
  | cons event rest ih =>
      simp only [List.flatMap_cons, List.length_append, BlocksFollowRegistrations,
        List.take_take, Nat.min_eq_left (Nat.le_add_right _ _), List.drop_take,
        Nat.add_sub_cancel_left, ih]

/-- A zero-object event contributes no ordering constraint and no ledger offset.
Witness: its take is empty and its drop leaves the entire label list intact.
-/
theorem BlocksFollowRegistrations.control {tasks published events event}
    (ordered : BlocksFollowRegistrations tasks published events)
    (empty : WorkQueueEvent.objectValues event = [])
    : BlocksFollowRegistrations tasks published (event :: events) := by
  simpa only [BlocksFollowRegistrations, empty, List.length_nil, List.take_zero,
    List.map_nil, List.drop_zero]
    using And.intro (List.nil_sublist _) ordered

/-- Outputs with no object values consume only empty label slices.
Witness: empty concatenation forces each event's object-value list to be empty.
-/
theorem BlocksFollowRegistrations.of_noObjectValues (tasks : List Task)
    (published : List ObjectPublication) {events : List WorkQueueEvent}
    (empty : events.flatMap WorkQueueEvent.objectValues = [])
    : BlocksFollowRegistrations tasks published events := by
  induction events with
  | nil => trivial
  | cons event rest ih =>
      obtain ⟨head, tail⟩ := List.append_eq_nil_iff.mp empty
      exact (ih tail).control head

/-- A successful flush's single optional value block inherits its label subsequence.
Witness: exact value erasure fixes the block width; the trailing closure consumes no label.
-/
theorem BlocksFollowRegistrations.flush {tasks added group groups streams}
    (ordered
      : (List.map (Prod.fst : ObjectPublication → Occurrence) added).Sublist
          (tasks.map Task.occurrence))
    : BlocksFollowRegistrations tasks added
        ((if (added.map Prod.snd).isEmpty then
            []
          else
            [.groupValues group (added.map Prod.snd)])
          ++ [.groupSuccess group groups streams]) := by
  split
  · exact (BlocksFollowRegistrations.nil tasks added).control rfl
  · change ((added.take (added.map Prod.snd).length).map Prod.fst).Sublist _ ∧ _
    simp only [WorkQueueEvent.objectValues, List.length_map, List.take_length, List.drop_length]
    exact ⟨ordered, (BlocksFollowRegistrations.nil tasks []).control rfl⟩

/-- An indexed raw event selects its exact consecutive ledger slice.
Witness: peel earlier raw events and add their object-value offsets.
-/
theorem BlocksFollowRegistrations.atEvent {tasks published events index event}
    (ordered : BlocksFollowRegistrations tasks published events)
    (selected : events[index]? = some event)
    : List.Sublist
        ((List.take event.objectValues.length
            (published.drop
              ((events.take index).flatMap WorkQueueEvent.objectValues).length)).map
          Prod.fst)
        (tasks.map Task.occurrence) := by
  induction events generalizing published index with
  | nil => simp at selected
  | cons head rest ih =>
      cases index with
      | zero => cases selected; exact ordered.1
      | succ index =>
          have later := ih ordered.2 selected
          simpa only [List.take_succ_cons, List.flatMap_cons, List.length_append,
            List.drop_drop] using later

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
