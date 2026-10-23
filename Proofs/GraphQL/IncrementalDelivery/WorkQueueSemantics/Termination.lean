import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.BatchLifecycle

/-! Termination occurs only in the last nonempty work batch, independently of closures. -/

namespace GraphQL.IncrementalDelivery.WorkQueueSemantics
open GraphQL.IncrementalDelivery.Execution

/-- A proof view of a history with one final termination event. -/
inductive Terminates : List WorkQueueEvent → Prop where
  | last : Terminates [.workQueueTermination]
  | cons {event rest} (ordinary : event ≠ .workQueueTermination) (tail : Terminates rest)
    : Terminates (event :: rest)

/-- A terminating sequence is nonempty, by inspecting its last/cons witness. -/
theorem Terminates.nonempty {events} (h : Terminates events) : events ≠ [] := by
  cases h <;> simp

/-- Termination membership follows by induction through ordinary outputs. -/
theorem Terminates.member {events} (h : Terminates events)
    : WorkQueueEvent.workQueueTermination ∈ events := by
  induction h with
  | last => simp
  | cons _ _ ih => exact List.mem_cons_of_mem _ ih

/-- Invert the final-marker witness without eliminating an unknown list append. -/
theorem terminates_cons_iff {event rest}
    : Terminates (event :: rest)
      ↔ (event = .workQueueTermination ∧ rest = [])
        ∨ (event ≠ .workQueueTermination ∧ Terminates rest) := by
  constructor
  · intro h
    cases h with
    | last => exact Or.inl ⟨rfl, rfl⟩
    | cons ordinary tail => exact Or.inr ⟨ordinary, tail⟩
  · rintro (⟨rfl, rfl⟩ | ⟨ordinary, tail⟩)
    · exact .last
    · exact .cons ordinary tail

/-- Any nonempty suffix retains termination, and its preceding outputs are ordinary;
witness: induction on the prefix and inversion of the terminal sequence.
-/
theorem Terminates.split {head tail} (h : Terminates (head ++ tail))
    (nonempty : tail ≠ [])
    : WorkQueueEvent.workQueueTermination ∉ head ∧ Terminates tail := by
  induction head with
  | nil => exact ⟨by simp, h⟩
  | cons event rest ih =>
      rcases terminates_cons_iff.mp h with ⟨_, empty⟩ | ⟨ordinary, later⟩
      · exact False.elim (nonempty (List.append_eq_nil_iff.mp empty).2)
      · obtain ⟨absent, terminal⟩ := ih later
        exact ⟨by simp [Ne.symm ordinary, absent], terminal⟩

/-- Appending termination to ordinary outputs gives the terminal sequence, by induction.
-/
theorem terminates_append {events : List WorkQueueEvent}
    (ordinary : WorkQueueEvent.workQueueTermination ∉ events)
    : Terminates (events ++ [.workQueueTermination]) := by
  induction events with
  | nil => exact .last
  | cons event rest ih =>
      simp only [List.mem_cons, not_or] at ordinary
      exact .cons (Ne.symm ordinary.1) (ih ordinary.2)

/-- Compatible coalescing involves only values, never termination, by event cases. -/
theorem combineValues_ordinary {left right combined}
    (h : combineValues left right = some combined)
    : left ≠ .workQueueTermination
      ∧ right ≠ .workQueueTermination
      ∧ combined ≠ .workQueueTermination := by
  cases left <;> cases right <;> simp [combineValues] at h
  all_goals obtain ⟨_, rfl⟩ := h; simp

/-- Grouping cannot erase all outputs from a nonempty input, by grouping induction. -/
theorem ValueGrouping.nil_iff {events grouped} (h : ValueGrouping events grouped)
    : grouped = [] ↔ events = [] := by
  cases h <;> simp_all

/-- Value grouping preserves termination membership, by separate/combine induction. -/
theorem ValueGrouping.termination_mem {events grouped} (h : ValueGrouping events grouped)
    : WorkQueueEvent.workQueueTermination ∈ grouped
      ↔ WorkQueueEvent.workQueueTermination ∈ events := by
  induction h with
  | nil => rfl
  | separate head _ ih =>
      simpa only [List.mem_cons]
        using or_congr (Iff.rfl : WorkQueueEvent.workQueueTermination = head ↔ _) ih
  | combine head _ compatible ih =>
      obtain ⟨left, right, merged⟩ := combineValues_ordinary compatible
      simpa [Ne.symm left, Ne.symm right, Ne.symm merged] using ih

/-- Grouping preserves a single final termination, by induction and ordinary coalescing.
-/
theorem ValueGrouping.terminates {events grouped} (h : ValueGrouping events grouped)
    (terminal : Terminates events)
    : Terminates grouped := by
  induction h with
  | nil => cases terminal
  | separate head tail ih =>
      cases terminal with
      | last =>
          have empty := tail.nil_iff.mpr rfl
          subst_vars
          exact .last
      | cons ordinary later => exact .cons ordinary (ih later)
  | combine head tail compatible ih =>
      obtain ⟨left, right, merged⟩ := combineValues_ordinary compatible
      cases terminal with
      | last => contradiction
      | cons _ later =>
          have grouped := ih later
          cases grouped with
          | last => contradiction
          | cons _ final => exact .cons merged final

/-- A batch history has ordinary earlier batches and one terminal last batch. -/
inductive TerminalBatches : List (List WorkQueueEvent) → Prop where
  | last {batch} (terminal : Terminates batch) : TerminalBatches [batch]
  | cons {batch rest} (ordinary : WorkQueueEvent.workQueueTermination ∉ batch)
    (tail : TerminalBatches rest)
    : TerminalBatches (batch :: rest)

/-- Work batching has no batches exactly when it has no input, by constructor cases. -/
theorem WorkBatching.nil_iff {events batches} (h : WorkBatching events batches)
    : events = [] ↔ batches = [] := by
  cases h <;> simp_all

/-- Work batching preserves termination membership, by partition and grouping induction.
-/
theorem WorkBatching.termination_mem {events batches} (h : WorkBatching events batches)
    : WorkQueueEvent.workQueueTermination ∈ batches.flatten
      ↔ WorkQueueEvent.workQueueTermination ∈ events := by
  induction h with
  | nil => simp
  | @cons batch tail grouped rest nonempty values subsequent ih =>
      simpa only [List.flatten_cons, List.mem_append]
        using or_congr values.termination_mem ih

/-- Work batching preserves a final termination marker, by splitting at batch boundaries.
-/
theorem WorkBatching.terminates {events batches} (h : WorkBatching events batches)
    (terminal : Terminates events)
    : TerminalBatches batches := by
  induction h with
  | nil => cases terminal
  | @cons batch tail grouped rest nonempty values subsequent ih =>
      by_cases empty : tail = []
      · subst tail
        have none := subsequent.nil_iff.mp rfl
        subst rest
        exact .last (values.terminates (by simpa using terminal))
      · obtain ⟨ordinary, later⟩ := terminal.split empty
        exact .cons (fun member => ordinary (values.termination_mem.mp member)) (ih later)

/-- Explained outputs never contain termination; event admission rejects that constructor.
-/
theorem Explains.noTermination {work groups streams events matching failures}
    (h : Explains work groups streams events matching failures)
    : WorkQueueEvent.workQueueTermination ∉ events := by
  intro member
  obtain ⟨index, selected⟩ := List.mem_iff_getElem?.mp member
  exact h.eventAllowed index _ selected

/-- An admitted prefix cannot also be a completed run of the same observable history.
Witness: prefix explanations exclude termination, while complete batching retains it.
-/
theorem AdmissiblePrefix.not_run {work history} (admitted : AdmissiblePrefix work history)
    : ¬AdmissibleRun work history := by
  obtain ⟨events, matching, failures, explained, batches⟩ := admitted
  intro finished
  obtain ⟨finalEvents, finalMatching, finalFailures, _, _, finalBatches⟩ := finished
  have marker := finalBatches.termination_mem.mpr
    (List.mem_append_right finalEvents List.mem_cons_self)
  exact explained.noTermination (batches.termination_mem.mp marker)

/-- Prefix-based next-batch admission is exactly valid, nonterminal extension.
Witness: disjointness of prefix and completed histories removes the redundant condition.
-/
theorem admissibleNext_iff_valid_nonterminal {work history batch}
    : AdmissibleNext work history batch
      ↔ ValidHistory work history
        ∧ ¬AdmissibleRun work history
        ∧ batch ≠ []
        ∧ ValidHistory work { history with batches := history.batches ++ [batch] } := by
  constructor
  · rintro ⟨admitted, nonempty, next⟩
    exact ⟨Or.inl admitted, admitted.not_run, nonempty, next⟩
  · rintro ⟨valid, unfinished, nonempty, next⟩
    rcases valid with admitted | finished
    · exact ⟨admitted, nonempty, next⟩
    · exact False.elim (unfinished finished)

/-- Every complete admitted run terminates only in its last work batch, using the unique
appended marker and grouping preservation.
-/
theorem AdmissibleRun.terminalBatches {work history} (h : AdmissibleRun work history)
    : TerminalBatches history.batches := by
  obtain ⟨events, matching, failures, explained, _, batching⟩ := h
  exact batching.terminates (terminates_append explained.noTermination)

end GraphQL.IncrementalDelivery.WorkQueueSemantics
