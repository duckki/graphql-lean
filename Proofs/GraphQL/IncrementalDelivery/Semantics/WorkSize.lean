import GraphQL.IncrementalDelivery.Execution

/-! Finite record measures for proofs, separate from public work emptiness. -/

namespace GraphQL.IncrementalDelivery.Execution

mutual
  /-- Count retained tasks, stream boundaries, items, and their future child work. -/
  def Work.size : Work → Nat
    | .empty => 0
    | .combine left right => left.size + right.size
    | .declareGroups _ tasks => tasks.size
    | .executionGroup _ _ _ children => 1 + children.size
    | .stream _ items => 1 + Work.itemsSize items

  /-- Count the finite item suffix and its child work. -/
  def Work.itemsSize : List (TaskOutcome ResponseValue × Work) → Nat
    | [] => 0
    | (_, work) :: rest => 1 + work.size + Work.itemsSize rest
end

/-- Direct emptiness agrees with zero total work, without inspecting child outcomes. -/
theorem Work.isEmpty_eq_true (work : Work) : work.isEmpty = true ↔ work.size = 0 := by
  cases work with
  | empty => simp [Work.isEmpty, Work.size]
  | combine left right =>
      simp only [Work.isEmpty, Work.size, Bool.and_eq_true_iff, Nat.add_eq_zero_iff]
      rw [Work.isEmpty_eq_true left, Work.isEmpty_eq_true right]
  | declareGroups groups tasks => exact Work.isEmpty_eq_true tasks
  | executionGroup groups path outcome children => simp [Work.isEmpty, Work.size]
  | stream node items => simp [Work.isEmpty, Work.size]
termination_by work

/-- The new executable check preserves the former count-based branch condition. -/
@[simp]
theorem Work.isEmpty_eq_size (work : Work) : work.isEmpty = (work.size == 0) := by
  have zero := Work.isEmpty_eq_true work
  cases empty : work.isEmpty <;> cases count : work.size <;> simp_all

/-- Public nonemptiness and positive finite-record accounting have the same domain. -/
@[simp]
theorem Work.isEmpty_eq_false (work : Work) : work.isEmpty = false ↔ work.size ≠ 0 := by
  simp

end GraphQL.IncrementalDelivery.Execution
