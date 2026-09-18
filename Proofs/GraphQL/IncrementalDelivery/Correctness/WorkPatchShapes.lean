import Proofs.GraphQL.IncrementalDelivery.Correctness.WorkPositionAtoms

/-! Work provenance supplies exact object attachments and nonempty streamed patches. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open WorkScheduler
open Semantics

/-- Data events retain their source owner path; object subpaths are exact and stream
value lists are nonempty. These are derived facts, not extra admission constraints.
-/
def EventPatchShape (paths : Nat → ResponsePath) : WorkEvent → Prop
  | .groupValues node values =>
      paths node.key = node.path
      ∧ ∀ value ∈ values, node.path ++ value.path.drop node.path.length = value.path
  | .streamValues node values _ _ => paths node.key = node.path ∧ values ≠ []
  | _ => True

/-- Atomic data events have exact source attachments, by task provenance and owner
prefixes; streamed publications contain the single successful item from their rule.
-/
theorem eventAllowed_patchShape {paths bound work initial matching before failed event}
    (coherent : MixedOwnerPaths.WorkAt paths bound work)
    (allowed : EventAllowed work initial matching before failed event)
    : EventPatchShape paths event := by
  cases event <;> try trivial
  case groupValues node values =>
    obtain ⟨owners, producer, path, data, errors, rfl, known, _, owner⟩ := allowed
    obtain ⟨kind, parents, birth, nodeAt⟩ := owner.1.1
    refine ⟨(workAt_node coherent nodeAt).2, ?_⟩
    intro value member
    have same := List.mem_singleton.mp member
    subst value
    exact object_subPath_exact coherent known owner
  case streamValues node values groups streams =>
    obtain ⟨_, _, _, _, rfl, _, _, owner, _⟩ := allowed
    obtain ⟨kind, parents, birth, nodeAt⟩ := owner.1.1
    exact ⟨(workAt_node coherent nodeAt).2, by simp⟩

/-- Compatible value combination retains the exact attachment and nonempty-item facts.
Witness: equal keys have equal assigned paths, and appending preserves nonemptiness.
-/
theorem combineValues_patchShape {paths left right combined}
    (hl : EventPatchShape paths left) (hr : EventPatchShape paths right)
    (compatible : combineValues left right = some combined)
    : EventPatchShape paths combined := by
  cases left <;> cases right <;> simp [combineValues] at compatible
  case groupValues.groupValues node values other more =>
    obtain ⟨keys, rfl⟩ := compatible
    have same : node.path = other.path := hl.1.symm.trans (keys ▸ hr.1)
    refine ⟨hl.1, ?_⟩
    intro value member
    rcases List.mem_append.mp member with member | member
    · exact hl.2 value member
    · simpa only [same] using hr.2 value member
  case
    streamValues.streamValues node values groups streams other more moreGroups moreStreams
      =>
    obtain ⟨_, rfl⟩ := compatible
    exact ⟨hl.1, by simp [hl.2]⟩

/-- All optional value grouping preserves patch shapes, by grouping induction. -/
theorem valueGrouping_patchShapes {paths events grouped}
    (grouping : ValueGrouping events grouped)
    (shapes : ∀ event ∈ events, EventPatchShape paths event)
    : ∀ event ∈ grouped, EventPatchShape paths event := by
  induction grouping with
  | nil => simp
  | separate head rest ih =>
      intro event member
      rcases List.mem_cons.mp member with rfl | member
      · exact shapes event (by simp)
      · exact ih (fun event member => shapes event (by simp [member])) event member
  | @combine head tail first rest merged grouped compatible ih =>
      have remaining := ih (fun event member => shapes event (by simp [member]))
      intro event member
      rcases List.mem_cons.mp member with rfl | member
      · exact combineValues_patchShape (shapes head (by simp))
          (remaining first (by simp)) compatible
      · exact remaining event (by simp [member])

/-- Work batching retains patch shapes in each output batch, by partition induction. -/
theorem workBatching_patchShapes {paths events batches}
    (grouping : WorkBatching events batches)
    (shapes : ∀ event ∈ events, EventPatchShape paths event)
    : ∀ event ∈ batches.flatten, EventPatchShape paths event := by
  induction grouping with
  | nil => simp
  | cons nonempty values rest ih =>
      intro event member
      rcases List.mem_append.mp member with head | tail
      · exact valueGrouping_patchShapes values
          (fun event member => shapes event (List.mem_append_left _ member)) event head
      · exact ih (fun event member => shapes event (List.mem_append_right _ member)) event tail

/-- Every admitted batch has the patch-shape facts needed by actual wire encoding.
Witness: atomic event rules, generated owner paths, and arbitrary grouping preservation.
-/
theorem admitted_patchShapes {paths bound work history}
    (coherent : MixedOwnerPaths.WorkAt paths bound work)
    (admitted : AdmissiblePrefix work history ∨ AdmissibleRun work history)
    : ∀ event ∈ history.batches.flatten, EventPatchShape paths event := by
  have explainedShapes {events matching failures}
      (explained : Explains work history.initialGroups history.initialStreams events
        matching failures)
      : ∀ event ∈ events, EventPatchShape paths event := by
    intro event member
    obtain ⟨index, selected⟩ := List.mem_iff_getElem?.mp member
    exact eventAllowed_patchShape coherent (explained.2.2 index event selected)
  rcases admitted with ⟨events, matching, failures, explained, grouped⟩
    | ⟨events, matching, failures, explained, _, grouped⟩
  · exact workBatching_patchShapes grouped (explainedShapes explained)
  · apply workBatching_patchShapes grouped
    intro event member
    rcases List.mem_append.mp member with member | member
    · exact explainedShapes explained event member
    · have same := List.mem_singleton.mp member
      subst event
      trivial

end GraphQL.IncrementalDelivery.Correctness
