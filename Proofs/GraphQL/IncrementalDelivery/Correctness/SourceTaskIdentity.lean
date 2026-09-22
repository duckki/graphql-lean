import Proofs.GraphQL.IncrementalDelivery.Correctness.SourceTasks

/-! Source labels are indexed uniquely by structural occurrence, not payload equality. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open WorkScheduler

/-- The work-tree route of an occurrence, omitting a streamed item's local ordinal. -/
def occurrenceAddress : Occurrence → Address
  | .executionGroup address | .item address _ => address

/-- The occurrence lies at or below the supplied work-tree address. -/
def SourceTask.Under (address : Address) (task : SourceTask) : Prop :=
  ∃ suffix, occurrenceAddress task.occurrence = address ++ suffix

/-- A tail item is either a later item at this stream or inside a later item's child.
-/
def SourceTask.InItems (address : Address) (ordinal : Nat) (task : SourceTask) : Prop :=
  (∃ index, ordinal ≤ index ∧ task.occurrence = .item address index)
  ∨ ∃ index, ordinal ≤ index ∧ task.Under (address ++ [index])

/-- A descendant's route remains below each enclosing route, by append associativity. -/
theorem SourceTask.Under.parent {address : Address} {index task}
    (below : SourceTask.Under (address ++ [index]) task)
    : task.Under address := by
  obtain ⟨suffix, same⟩ := below
  exact ⟨index :: suffix, by simpa [List.append_assoc] using same⟩

mutual
  /-- All labels retain their enclosing work-tree route, by structural descent. -/
  theorem sourceTasks_under (address producer cursors work) {task : SourceTask}
      (member : task ∈ sourceTasks address producer cursors work)
      : task.Under address := by
    cases work with
    | empty => simp [sourceTasks] at member
    | combine left right =>
        rw [sourceTasks] at member
        rcases List.mem_append.mp member with member | member
        · exact (sourceTasks_under _ _ _ _ member).parent
        · exact (sourceTasks_under _ _ _ _ member).parent
    | executionGroup groups path result children =>
        rw [sourceTasks] at member
        rcases List.mem_cons.mp member with rfl | member
        · exact ⟨[], by simp [occurrenceAddress]⟩
        · exact (sourceTasks_under _ _ _ _ member).parent
    | stream node items =>
        rcases sourceItemTasks_scope address producer node _ 0 items member with
          ⟨index, _, same⟩ | ⟨index, _, below⟩
        · exact ⟨[], by simp [same, occurrenceAddress]⟩
        · exact below.parent
  termination_by sizeOf work

  /-- A stream tail's labels retain a lower bound on their originating item ordinal.
  Witness: the current item, its child subtree, or induction through the item tail.
  -/
  theorem sourceItemTasks_scope (address producer node index ordinal items)
      {task : SourceTask}
      (member : task ∈ sourceItemTasks address producer node index ordinal items)
      : task.InItems address ordinal := by
    cases items with
    | nil => simp [sourceItemTasks] at member
    | cons head rest =>
        cases head_eq : head with
        | mk result children =>
            rw [sourceItemTasks] at member
            rcases List.mem_cons.mp member with rfl | member
            · exact Or.inl ⟨ordinal, Nat.le_refl _, rfl⟩
            · rcases List.mem_append.mp member with member | member
              · exact Or.inr ⟨ordinal, Nat.le_refl _, sourceTasks_under _ _ _ _ member⟩
              · rcases sourceItemTasks_scope _ _ _ _ _ _ member with
                  ⟨next, lower, same⟩ | ⟨next, lower, below⟩
                · exact Or.inl ⟨next, by omega, same⟩
                · exact Or.inr ⟨next, by omega, below⟩
  termination_by sizeOf items
  decreasing_by all_goals simp_all; omega
end

/-- A child route cannot equal its parent, because descent increases route length. -/
theorem SourceTask.Under.not_parent {address : Address} {index task}
    (below : SourceTask.Under (address ++ [index]) task)
    : occurrenceAddress task.occurrence ≠ address := by
  obtain ⟨suffix, same⟩ := below
  intro equal
  have lengths := congrArg List.length (equal.symm.trans same)
  simp only [List.length_append, List.length_singleton] at lengths
  omega

/-- Different child routes cannot label the same occurrence; cancel the common prefix.
-/
theorem SourceTask.Under.separate {address : Address} {left right first second}
    (hl : SourceTask.Under (address ++ [left]) first)
    (hr : SourceTask.Under (address ++ [right]) second) (different : left ≠ right)
    : first.occurrence ≠ second.occurrence := by
  obtain ⟨ls, hl⟩ := hl
  obtain ⟨rs, hr⟩ := hr
  intro same
  have equal := hl.symm.trans ((congrArg occurrenceAddress same).trans hr)
  simp only [List.append_assoc, List.singleton_append, List.append_cancel_left_eq,
    List.cons.injEq] at equal
  exact different equal.1

/-- The current item is distinct from all tasks in its child subtree. -/
theorem SourceTask.Under.ne_item {address : Address} {ordinal child task}
    (below : SourceTask.Under (address ++ [child]) task)
    : task.occurrence ≠ .item address ordinal := by
  intro equal
  exact below.not_parent (congrArg occurrenceAddress equal)

/-- Tail items and their children never have the current item's occurrence. -/
theorem SourceTask.InItems.ne_previous {address : Address} {ordinal task}
    (later : SourceTask.InItems address (ordinal + 1) task)
    : task.occurrence ≠ .item address ordinal := by
  rcases later with ⟨index, lower, same⟩ | ⟨index, _, below⟩
  · intro equal
    have := Occurrence.item.inj (same.symm.trans equal)
    omega
  · exact below.ne_item

/-- The current item's children are distinct from every later item and its children.
Witness: strict child-route separation, or the parent/descendant length inequality.
-/
theorem SourceTask.Under.separate_tail {address : Address} {ordinal first second}
    (child : SourceTask.Under (address ++ [ordinal]) first)
    (later : SourceTask.InItems address (ordinal + 1) second)
    : first.occurrence ≠ second.occurrence := by
  rcases later with ⟨index, _, same⟩ | ⟨index, lower, below⟩
  · simpa only [same] using child.ne_item (ordinal := index)
  · exact child.separate below (by omega)

mutual
  /-- Structural occurrence labels are unique independently of source payloads and
  stream seeds. Witness: sibling-route separation and parent/descendant separation.
  -/
  theorem sourceTasks_unique (address producer cursors work)
      : (sourceTasks address producer cursors work).Pairwise
          (fun left right => left.occurrence ≠ right.occurrence) := by
    cases work with
    | empty => exact .nil
    | combine left right =>
        rw [sourceTasks, List.pairwise_append]
        refine ⟨sourceTasks_unique _ _ _ _, sourceTasks_unique _ _ _ _, ?_⟩
        intro first hf second hs
        exact (sourceTasks_under _ _ _ _ hf).separate
          (sourceTasks_under _ _ _ _ hs) (by decide)
    | executionGroup groups path result children =>
        rw [sourceTasks, List.pairwise_cons]
        refine ⟨?_, sourceTasks_unique _ _ _ _⟩
        intro task member equal
        exact (sourceTasks_under _ _ _ _ member).not_parent
          (congrArg occurrenceAddress equal.symm)
    | stream node items => exact sourceItemTasks_unique _ _ _ _ _ _
  termination_by sizeOf work

  /-- Item labels and their children are unique across the entire remaining stream.
  Witness: the ordinal lower bound separates each item and child subtree from the tail.
  -/
  theorem sourceItemTasks_unique (address producer node index ordinal items)
      : (sourceItemTasks address producer node index ordinal items).Pairwise
          (fun left right => left.occurrence ≠ right.occurrence) := by
    cases items with
    | nil => exact .nil
    | cons head rest =>
        rcases head with ⟨result, children⟩
        rw [sourceItemTasks, List.pairwise_cons, List.pairwise_append]
        refine ⟨?_, sourceTasks_unique _ _ _ _, sourceItemTasks_unique _ _ _ _ _ _, ?_⟩
        · intro task member equal
          rcases List.mem_append.mp member with member | member
          · exact (sourceTasks_under _ _ _ _ member).ne_item equal.symm
          · exact (sourceItemTasks_scope _ _ _ _ _ _ member).ne_previous equal.symm
        · intro first hf second hs
          exact (sourceTasks_under _ _ _ _ hf).separate_tail
            (sourceItemTasks_scope _ _ _ _ _ _ hs)
  termination_by sizeOf items
end

/-- Source inventory lookup by occurrence is functional. Witness: pairwise uniqueness
of occurrence projections, with no requirement that different payload values differ.
-/
theorem sourceTasks_same {address producer cursors work first second}
    (hf : first ∈ sourceTasks address producer cursors work)
    (hs : second ∈ sourceTasks address producer cursors work)
    (same : first.occurrence = second.occurrence)
    : first = second := by
  have unique := sourceTasks_unique address producer cursors work
  generalize sourceTasks address producer cursors work = tasks at unique hf hs
  induction tasks with
  | nil => simp at hf
  | cons head rest ih =>
      obtain ⟨separate, tail⟩ := List.pairwise_cons.mp unique
      rcases List.mem_cons.mp hf with rfl | firstTail
      · rcases List.mem_cons.mp hs with rfl | secondTail
        · rfl
        · exact False.elim (separate second secondTail same)
      · rcases List.mem_cons.mp hs with rfl | secondTail
        · exact False.elim (separate first firstTail same.symm)
        · exact ih tail firstTail secondTail

end GraphQL.IncrementalDelivery.Correctness
