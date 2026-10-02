import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamPublication

/-! Atomic publication views preserve actual normalized batching and notice placement. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Split value lists without changing the queue or publisher
-----------------------------------------------------------------------------------------

/-- Value-bearing events contain a payload; control events need no such check. -/
def NonemptyValues : Execution.WorkQueueEvent → Prop
  | .groupValues _ values | .streamValues _ values _ _ => values ≠ []
  | _ => True

/-- A value atom contains one payload; control events are already atomic. -/
def AtomicValues : Execution.WorkQueueEvent → Prop
  | .groupValues _ values | .streamValues _ values _ _ => values.length = 1
  | _ => True

/-- Split a stream publication in item order, retaining all notices on its last item.
This is proof evidence for value grouping, not an implementation choice or admission law.
-/
def streamPublicationAtoms (stream : Execution.DeliveryNode)
    (groups streams : List Execution.DeliveryNode)
    : List Execution.StreamItemValue → List Execution.WorkQueueEvent
  | [] => []
  | [value] => [.streamValues stream [value] groups streams]
  | value :: next :: rest =>
      .streamValues stream [value] [] []
      :: streamPublicationAtoms stream groups streams (next :: rest)

/-- Expand value events into singleton payloads and retain every control event unchanged.
Empty value events have no atoms; the implementation proof separately excludes them.
-/
def publicationAtoms : Execution.WorkQueueEvent → List Execution.WorkQueueEvent
  | .groupValues group values => values.map (fun value => .groupValues group [value])
  | .streamValues stream values groups streams =>
      streamPublicationAtoms stream groups streams values
  | event => [event]

/-- Stream splitting gives one atom per item, including the final notice carrier.
Witness: induction over the exact item-list recursion. -/
theorem streamPublicationAtoms_length (stream groups streams values)
    : (streamPublicationAtoms stream groups streams values).length = values.length := by
  induction values using streamPublicationAtoms.induct with
  | case1 => rfl
  | case2 => rfl
  | case3 value next rest ih => simp [streamPublicationAtoms, ih]

/-- Every generated atom has one payload or is a control event.
Witness: singleton construction for values and unchanged control constructors. -/
theorem publicationAtoms_atomic (event : Execution.WorkQueueEvent)
    : ∀ atom ∈ publicationAtoms event, AtomicValues atom := by
  cases event with
  | groupValues group values =>
      simp [publicationAtoms, AtomicValues]
  | streamValues stream values groups streams =>
      induction values using streamPublicationAtoms.induct with
      | case1 => simp [publicationAtoms, streamPublicationAtoms]
      | case2 => simp [publicationAtoms, streamPublicationAtoms, AtomicValues]
      | case3 value next rest ih =>
          simpa [publicationAtoms, streamPublicationAtoms, AtomicValues] using ih
  | groupSuccess | groupFailure | streamSuccess | streamFailure | workQueueTermination =>
      simp [publicationAtoms, AtomicValues]

/-- Splitting stream items retains their exact descriptors, values, and error counts.
Witness: ordered singleton projection through the split list. -/
theorem streamPublicationAtoms_itemValues (stream groups streams values)
    : (streamPublicationAtoms stream groups streams values).flatMap normalizedItemValues
      = values.map (stream, ·) := by
  induction values using streamPublicationAtoms.induct with
  | case1 => rfl
  | case2 => rfl
  | case3 value next rest ih =>
      simp only [streamPublicationAtoms, List.flatMap_cons, normalizedItemValues,
        List.map_cons, List.map_nil, List.cons_append, List.nil_append, ih]

/-- Splitting preserves both independent payload sequences exactly.
Witness: object singleton mapping and the stream item projection lemma. -/
theorem publicationAtoms_values (event : Execution.WorkQueueEvent)
    : (publicationAtoms event).flatMap normalizedObjectValues
        = normalizedObjectValues event
      ∧ (publicationAtoms event).flatMap normalizedItemValues
        = normalizedItemValues event := by
  cases event with
  | groupValues group values =>
      simp [publicationAtoms, normalizedObjectValues, normalizedItemValues, List.flatMap_map]
  | streamValues stream values groups streams =>
      refine ⟨?_, streamPublicationAtoms_itemValues ..⟩
      induction values using streamPublicationAtoms.induct with
      | case1 => rfl
      | case2 => rfl
      | case3 value next rest ih =>
          simpa [publicationAtoms, streamPublicationAtoms, normalizedObjectValues] using ih
  | groupSuccess | groupFailure | streamSuccess | streamFailure | workQueueTermination =>
      exact ⟨rfl, rfl⟩

-----------------------------------------------------------------------------------------
-- The existing value-grouping relation recovers the exact emitted event
-----------------------------------------------------------------------------------------

/-- Nonempty stream items regroup into the original event, with identical notice lists.
Witness: adjacent equal-owner combines, with notices carried only by the last atom. -/
theorem streamPublicationAtoms_grouping (stream groups streams values)
    (nonempty : values ≠ [])
    : ValueGrouping (streamPublicationAtoms stream groups streams values)
        [.streamValues stream values groups streams] := by
  induction values using streamPublicationAtoms.induct with
  | case1 => exact False.elim (nonempty rfl)
  | case2 value => exact .separate _ .nil
  | case3 value next rest ih =>
      apply ValueGrouping.combine _ (ih (by simp))
      simp [combineValues]

/-- Every nonempty value event, or control event, is exactly a grouping of its atoms.
Witness: equal-owner object combines, stream grouping, or an unchanged control event. -/
theorem publicationAtoms_grouping (event : Execution.WorkQueueEvent)
    (nonempty : NonemptyValues event)
    : ValueGrouping (publicationAtoms event) [event] := by
  cases event with
  | groupValues group values =>
      induction values with
      | nil => exact False.elim (nonempty rfl)
      | cons value rest ih =>
          cases rest with
          | nil => exact .separate _ .nil
          | cons next rest =>
              apply ValueGrouping.combine _ (ih (by simp [NonemptyValues]))
              simp [combineValues]
  | streamValues stream values groups streams =>
      exact streamPublicationAtoms_grouping _ _ _ _ nonempty
  | groupSuccess | groupFailure | streamSuccess | streamFailure | workQueueTermination =>
      exact .separate _ .nil

/-- Concatenating two grouping derivations preserves both exact lists.
Witness: induction on the first grouping, retaining all combines and separators. -/
theorem valueGrouping_append {left right first second : List Execution.WorkQueueEvent}
    (before : ValueGrouping left first) (after : ValueGrouping right second)
    : ValueGrouping (left ++ right) (first ++ second) := by
  induction before with
  | nil => exact after
  | separate head rest ih => exact .separate head ih
  | combine head grouped compatible ih => exact .combine head ih compatible

/-- Splitting a whole event list preserves its exact grouping and event order.
Witness: concatenate the per-event grouping derivations. -/
theorem publicationAtoms_grouping_list (events : List Execution.WorkQueueEvent)
    (nonempty : ∀ event ∈ events, NonemptyValues event)
    : ValueGrouping (events.flatMap publicationAtoms) events := by
  induction events with
  | nil => exact .nil
  | cons event rest ih =>
      exact valueGrouping_append (publicationAtoms_grouping event (nonempty _ List.mem_cons_self))
        (ih (fun next member => nonempty next (List.mem_cons_of_mem _ member)))

/-- A retained event has at least one atom, so splitting cannot erase an output batch.
Witness: object list nonemptiness, stream length, and singleton control events. -/
theorem publicationAtoms_nonempty {event : Execution.WorkQueueEvent}
    (nonempty : NonemptyValues event)
    : publicationAtoms event ≠ [] := by
  cases event with
  | groupValues group values => simpa [publicationAtoms, NonemptyValues] using nonempty
  | streamValues stream values groups streams =>
      intro empty
      have length := streamPublicationAtoms_length stream groups streams values
      rw [show streamPublicationAtoms stream groups streams values = [] from empty] at length
      cases values with
      | nil => exact nonempty rfl
      | cons value rest => simp at length
  | groupSuccess | groupFailure | streamSuccess | streamFailure | workQueueTermination =>
      simp [publicationAtoms]

/-- Nonempty output batches are recovered with their original boundaries and values.
Witness: each batch's grouping derivation, without altering notices or termination.
This is a representation result only; it does not assert event admission. -/
theorem publicationAtoms_batching (batches : List (List Execution.WorkQueueEvent))
    (batchNonempty : ∀ batch ∈ batches, batch ≠ [])
    (valuesNonempty : ∀ event ∈ batches.flatten, NonemptyValues event)
    : WorkBatching (batches.flatten.flatMap publicationAtoms) batches := by
  induction batches with
  | nil => exact .nil
  | cons batch rest ih =>
      have nonempty : ∀ event ∈ batch, NonemptyValues event := by
        intro event member
        exact valuesNonempty event (List.mem_flatten.mpr ⟨batch, List.mem_cons_self, member⟩)
      have atomsNonempty : batch.flatMap publicationAtoms ≠ [] := by
        cases batch with
        | nil => exact False.elim (batchNonempty _ List.mem_cons_self rfl)
        | cons head tail =>
            have headNonempty := publicationAtoms_nonempty (nonempty head List.mem_cons_self)
            cases atoms : publicationAtoms head with
            | nil => exact False.elim (headNonempty atoms)
            | cons first more => simp [List.flatMap_cons, atoms]
      simpa only [List.flatten_cons, List.flatMap_append]
        using WorkBatching.cons atomsNonempty
          (publicationAtoms_grouping_list batch nonempty)
          (ih (fun next member => batchNonempty next (List.mem_cons_of_mem _ member))
            (fun event member => valuesNonempty event (by
              simp only [List.flatten_cons, List.mem_append]
              exact Or.inr member)))

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
