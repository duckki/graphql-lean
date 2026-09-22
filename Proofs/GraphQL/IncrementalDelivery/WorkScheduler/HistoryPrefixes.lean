import Proofs.GraphQL.IncrementalDelivery.WorkScheduler.Termination

/-! Prefix closure of independent work admission, including ordered hidden failure cuts. -/

namespace GraphQL.IncrementalDelivery.WorkScheduler
open GraphQL.IncrementalDelivery.Execution

/-- Restricting failure cuts to a later boundary preserves earlier failure observations;
witness: filter composition and transitivity of cut bounds.
-/
theorem failedBefore_filter (failures : FailureCuts) {index bound : Nat}
    (within : index ≤ bound)
    : failedBefore (failures.filter (fun entry => entry.1 ≤ bound)) index
      = failedBefore failures index := by
  unfold failedBefore
  rw [List.filter_filter]
  congr 1
  apply List.filter_congr
  intro entry _
  rw [← Bool.decide_and]
  have same : (entry.1 ≤ index ∧ entry.1 ≤ bound) ↔ entry.1 ≤ index := by omega
  simp only [same]

/-- An output prefix retains exactly the failures at or before its boundary. Ordered
cuts retain every earlier cause of each kept failure; witness: filter decomposition.
-/
theorem FailureWitness.prefix {work initial head tail failures}
    (h : FailureWitness work initial (head ++ tail) failures)
    : FailureWitness work initial head
        (failures.filter (fun entry => entry.1 ≤ head.length)) := by
  intro before cut occurrence after equal
  obtain ⟨left, right, original, keptLeft, keptRight⟩ :=
    List.filter_eq_append_iff.mp equal
  obtain ⟨gap, rest, rfl, dropped, kept, _⟩ := List.filter_eq_cons_iff.mp keptRight
  have facts := h (left ++ gap) cut occurrence rest
    (by simpa only [List.append_assoc] using original)
  have bounded : cut ≤ head.length := by simpa using kept
  have gapEmpty : gap = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro entry member
    have earlier := facts.2.1 entry (List.mem_append_right _ member)
    have rejected := dropped entry member
    simp only [decide_eq_true_eq] at rejected
    exact rejected (Nat.le_trans earlier bounded)
  subst gap
  simp only [List.append_nil] at facts original
  have leftKept : left.filter (fun entry => entry.1 ≤ head.length) = left := by
    apply List.filter_eq_self.mpr
    intro entry member
    simpa using Nat.le_trans (facts.2.1 entry member) bounded
  have same : left = before := leftKept.symm.trans keptLeft
  rw [← same]
  refine ⟨bounded, facts.2.1, ?_, facts.2.2.2⟩
  simpa only [List.take_append_of_le_length bounded] using facts.2.2.1

/-- Explained output histories restrict to any raw-event prefix. The publication
matching is unchanged and failure evidence is truncated at the boundary.
-/
theorem Explains.prefix {work groups streams head tail matching failures}
    (h : Explains work groups streams (head ++ tail) matching failures)
    : Explains work groups streams head matching
        (failures.filter (fun entry => entry.1 ≤ head.length)) := by
  refine ⟨h.1, h.2.1.prefix, ?_⟩
  intro index event selected
  have bound : index < head.length := List.getElem?_eq_some_iff.mp selected |>.1
  have original : (head ++ tail)[index]? = some event := by
    simpa only [List.getElem?_append_left bound] using selected
  have allowed := h.2.2 index event original
  simpa only [List.take_append_of_le_length (Nat.le_of_lt bound),
    failedBefore_filter failures (Nat.le_of_lt bound)]
    using allowed

/-- Splitting observed batches splits the underlying raw events at a batch boundary;
witness: induction over the requested batch prefix, retaining each grouping witness.
-/
theorem WorkBatching.split {events before after}
    (h : WorkBatching events (before ++ after))
    : ∃ head tail,
        events = head ++ tail ∧ WorkBatching head before ∧ WorkBatching tail after := by
  induction before generalizing events with
  | nil => exact ⟨[], events, rfl, .nil, h⟩
  | cons batch rest ih =>
      cases h with
      | @cons raw tail grouped later nonempty values subsequent =>
          obtain ⟨head, tail, equal, first, last⟩ := ih subsequent
          exact ⟨
            raw ++ head,
            tail,
            by simp [equal, List.append_assoc],
            .cons nonempty values first,
            last
          ⟩

/-- Admitted nonterminal histories admit every batch prefix; witness: split raw outputs
and restrict the same matching and ordered failure evidence.
-/
theorem AdmissiblePrefix.prefix {work groups streams before after}
    (h : AdmissiblePrefix work ⟨groups, streams, before ++ after⟩)
    : AdmissiblePrefix work ⟨groups, streams, before⟩ := by
  obtain ⟨events, matching, failures, explained, batching⟩ := h
  obtain ⟨head, tail, rfl, first, _⟩ := batching.split
  exact ⟨head, matching, _, explained.prefix, first⟩

/-- A proper batch prefix of a terminal run is an admitted nonterminal history;
witness: the nonempty raw suffix still contains the last termination marker.
-/
theorem AdmissibleRun.prefix {work groups streams before after}
    (h : AdmissibleRun work ⟨groups, streams, before ++ after⟩) (proper : after ≠ [])
    : AdmissiblePrefix work ⟨groups, streams, before⟩ := by
  obtain ⟨events, matching, failures, explained, _, batching⟩ := h
  obtain ⟨head, tail, equal, first, last⟩ := batching.split
  have tailNonempty : tail ≠ [] := fun empty => proper (last.nil_iff.mp empty)
  have lengths := congrArg List.length equal
  have positive : 0 < tail.length := List.length_pos_iff.mpr tailNonempty
  simp only [List.length_append, List.length_singleton] at lengths
  have bound : head.length ≤ events.length := by omega
  have rawPrefix : head.IsPrefix events :=
    List.prefix_of_prefix_length_le ⟨tail, equal.symm⟩ (List.prefix_append _ _) bound
  obtain ⟨rest, joined⟩ := rawPrefix
  rw [← joined] at explained
  exact ⟨head, matching, _, explained.prefix, first⟩

/-- The complete history language is prefix closed, by prefix/run case analysis; only
the unchanged full terminal history retains its terminal witness.
-/
theorem ValidHistory.prefix {work groups streams before after}
    (h : ValidHistory work ⟨groups, streams, before ++ after⟩)
    : ValidHistory work ⟨groups, streams, before⟩ := by
  rcases h with prefixRun | run
  · exact Or.inl prefixRun.prefix
  · by_cases empty : after = []
    · exact Or.inr (by simpa [empty] using run)
    · exact Or.inl (run.prefix empty)

/-- Every valid initialization admits the empty observation; witness: no outputs,
no hidden failures, and empty work batching.
-/
theorem Initializes.emptyHistory {work groups streams}
    (h : Initializes work groups streams)
    : AdmissiblePrefix work ⟨groups, streams, []⟩ := by
  refine ⟨[], (fun _ => .executionGroup []), [], ⟨h, ?_, ?_⟩, .nil⟩
  · simp [FailureWitness]
  · intro index event selected
    simp at selected

end GraphQL.IncrementalDelivery.WorkScheduler
