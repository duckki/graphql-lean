import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.OutputAtoms
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.EventLifecycle

/-! Grouping cannot hide a different explanation when every observed value is a singleton. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Coalescing nonempty payloads cannot preserve singleton output
-----------------------------------------------------------------------------------------

/-- A singleton value event is nonempty; every control event satisfies both predicates.
Witness: one-element length excludes an empty payload list.
-/
theorem AtomicValues.nonempty {event} (atomic : AtomicValues event)
    : NonemptyValues event := by
  cases event <;> try trivial
  all_goals
    intro empty
    simp [AtomicValues, empty] at atomic

/-- Combining a nonempty left value produces a nonempty value event.
Witness: the two supported constructors concatenate their payload lists.
-/
theorem combineValues_nonempty {left right merged}
    (compatible : combineValues left right = some merged) (nonempty : NonemptyValues left)
    : NonemptyValues merged := by
  cases left <;> cases right <;> simp only [combineValues] at compatible <;> try contradiction
  all_goals
    split at compatible <;> try contradiction
    cases compatible
    simp_all [NonemptyValues]

/-- Value grouping preserves nonempty payloads.
Witness: separate events inherit nonemptiness; a combined event retains its left payload.
-/
theorem ValueGrouping.nonemptyValues {events grouped}
    (grouping : ValueGrouping events grouped)
    (nonempty : ∀ event ∈ events, NonemptyValues event)
    : ∀ event ∈ grouped, NonemptyValues event := by
  induction grouping with
  | nil => simp
  | separate head rest ih =>
      intro event member
      rcases List.mem_cons.mp member with rfl | member
      · exact nonempty _ List.mem_cons_self
      · exact ih (fun _ included => nonempty _ (List.mem_cons_of_mem _ included)) event member
  | combine head rest compatible ih =>
      intro event member
      rcases List.mem_cons.mp member with rfl | member
      · exact combineValues_nonempty compatible (nonempty head List.mem_cons_self)
      · exact ih (fun _ included => nonempty _ (List.mem_cons_of_mem _ included)) event
          (List.mem_cons_of_mem _ member)

/-- Two nonempty compatible value events cannot combine into a singleton.
Witness: each payload contributes a positive length to their concatenation.
-/
theorem combineValues_not_atomic {left right merged}
    (compatible : combineValues left right = some merged)
    (leftNonempty : NonemptyValues left) (rightNonempty : NonemptyValues right)
    : ¬AtomicValues merged := by
  cases left <;> cases right <;> simp only [combineValues] at compatible <;> try contradiction
  all_goals
    split at compatible <;> try contradiction
    cases compatible
    simp only [NonemptyValues, ← List.length_pos_iff] at leftNonempty rightNonempty
    simp only [AtomicValues, List.length_append]
    omega

/-- Grouping between singleton-valued histories is the identity.
Witness: a combine step would produce at least two values; only separate steps remain.
-/
theorem ValueGrouping.atomic_eq {events grouped} (grouping : ValueGrouping events grouped)
    (source : ∀ event ∈ events, AtomicValues event)
    (target : ∀ event ∈ grouped, AtomicValues event)
    : events = grouped := by
  induction grouping with
  | nil => rfl
  | separate head rest ih =>
      exact congrArg (head :: ·) (ih
        (fun _ member => source _ (List.mem_cons_of_mem _ member))
        (fun _ member => target _ (List.mem_cons_of_mem _ member)))
  | combine head rest compatible _ =>
      have tailNonempty := ValueGrouping.nonemptyValues rest
        (fun _ member => (source _ (List.mem_cons_of_mem _ member)).nonempty)
      exact False.elim (combineValues_not_atomic compatible
        (source head List.mem_cons_self).nonempty
        (tailNonempty _ List.mem_cons_self) (target _ List.mem_cons_self))

/-- Batching singleton-valued histories changes only the outer list boundaries.
Witness: the identity grouping theorem applies inside each batch, followed by append.
-/
theorem WorkBatching.atomic_eq_flatten {events batches}
    (batching : WorkBatching events batches)
    (source : ∀ event ∈ events, AtomicValues event)
    (target : ∀ event ∈ batches.flatten, AtomicValues event)
    : events = batches.flatten := by
  induction batching with
  | nil => rfl
  | cons _ values _ ih =>
      have first := ValueGrouping.atomic_eq values
        (fun _ member => source _ (List.mem_append_left _ member))
        (fun _ member => target _ (List.mem_append_left _ member))
      have later := ih
        (fun _ member => source _ (List.mem_append_right _ member))
        (fun _ member => target _ (List.mem_append_right _ member))
      simp only [List.flatten_cons, first, later]

-----------------------------------------------------------------------------------------
-- Admission supplies the atomicity premise for arbitrary explanation witnesses
-----------------------------------------------------------------------------------------

/-- Admitted atoms carry singleton payloads; observable events may coalesce several atoms.
Witness: project the exact payload equality from either publication constructor.
-/
theorem EventAllowed.atomicValues {work initial matching before failures event}
    (allowed : EventAllowed work initial matching before failures event)
    : AtomicValues event := by
  cases event <;> try trivial
  case groupValues =>
    obtain ⟨_, _, _, same, _⟩ := allowed
    simp [AtomicValues, same]
  case streamValues =>
    obtain ⟨_, _, _, same, _⟩ := allowed
    simp [AtomicValues, same]

/-- Every event of an explained history is atomic.
Witness: select its index and apply the local admission's singleton-payload consequence.
-/
theorem Explains.atomicValues {work groups streams events matching failures}
    (explained : Explains work groups streams events matching failures)
    : ∀ event ∈ events, AtomicValues event := by
  intro event member
  obtain ⟨index, selected⟩ := List.mem_iff_getElem?.mp member
  exact EventAllowed.atomicValues (explained.2.2 index event selected)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
