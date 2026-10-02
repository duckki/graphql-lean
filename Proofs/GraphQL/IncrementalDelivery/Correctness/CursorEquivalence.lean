import Proofs.GraphQL.IncrementalDelivery.Correctness.SourceCursorReplay

/-! Cursor histories may retain different obsolete entries after stream coalescing;
only their observable path lookups matter to position decoding.
-/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open Semantics
open Semantics.MixedPaths

/-- Two cursor histories give the same next index for every response path. -/
def CursorEquivalent (left right : ResponsePositions.Cursors) : Prop :=
  ∀ path, ResponsePositions.cursorAt left path = ResponsePositions.cursorAt right path

/-- Cursor lookup in an appended history prefers a hit in its newer left part. -/
theorem cursorAt_append_eq (left right : ResponsePositions.Cursors) (path : ResponsePath)
    : ResponsePositions.cursorAt (left ++ right) path
      = match ResponsePositions.cursorAt left path with
        | some index => some index
        | none => ResponsePositions.cursorAt right path := by
  unfold ResponsePositions.cursorAt
  rw [List.find?_append]
  cases found : left.find? (fun entry => entry.1 == path) <;> simp

/-- Appending the same older history preserves cursor equivalence, by lookup cases. -/
theorem CursorEquivalent.append {left right : ResponsePositions.Cursors}
    (same : CursorEquivalent left right) (older : ResponsePositions.Cursors)
    : CursorEquivalent (left ++ older) (right ++ older) := by
  intro path
  simp only [cursorAt_append_eq, same path]

/-- Prepending the same newer writes preserves cursor equivalence, by lookup cases. -/
theorem CursorEquivalent.prepend {left right : ResponsePositions.Cursors}
    (same : CursorEquivalent left right) (newer : ResponsePositions.Cursors)
    : CursorEquivalent (newer ++ left) (newer ++ right) := by
  intro path
  simp only [cursorAt_append_eq, same path]

/-- Cursor equivalence composes pointwise; obsolete history remains unobservable. -/
theorem CursorEquivalent.trans {left middle right : ResponsePositions.Cursors}
    (first : CursorEquivalent left middle) (second : CursorEquivalent middle right)
    : CursorEquivalent left right :=
  fun path => (first path).trans (second path)

/-- Cursor equivalence is symmetric by symmetry of every lookup equality. -/
theorem CursorEquivalent.symm {left right : ResponsePositions.Cursors}
    (same : CursorEquivalent left right)
    : CursorEquivalent right left :=
  fun path => (same path).symm

/-- Reasserting the current value at a path does not change any cursor lookup. -/
theorem cursorEquivalent_reassert {current : ResponsePositions.Cursors} {path index}
    (cursor : ResponsePositions.cursorAt current path = some index)
    : CursorEquivalent ((path, index) :: current) current := by
  intro query
  rw [cursorAt_cons]
  split
  next same => simpa only [← same] using cursor.symm
  next => rfl

/-- Disjoint cursor contributions commute, since lookup cannot hit both at one path. -/
theorem cursorEquivalent_commute {left right : ResponsePositions.Cursors}
    (apart : ∀ first ∈ left, ∀ second ∈ right, first.1 ≠ second.1)
    : CursorEquivalent (left ++ right) (right ++ left) := by
  intro path
  simp only [cursorAt_append_eq]
  cases hl : ResponsePositions.cursorAt left path with
  | none => cases ResponsePositions.cursorAt right path <;> rfl
  | some first =>
      cases hr : ResponsePositions.cursorAt right path with
      | none => rfl
      | some second =>
          exact False.elim (apart _ (cursorAt_member hl) _ (cursorAt_member hr) rfl)

/-- List-item cursor paths lie under one of the indices at or beyond the starting offset.
Witness: cursor-scope descent for the head and increasing-index induction for the tail.
-/
theorem itemCursors_underItems (path : ResponsePath) (index : Nat)
    (items : List ResponseValue) {entry}
    (member : entry ∈ ResponsePositions.itemCursors path index items)
    : UnderItems path index entry.1 := by
  induction items generalizing index with
  | nil => simp [ResponsePositions.itemCursors] at member
  | cons head rest ih =>
      rcases List.mem_append.mp member with member | member
      · exact ⟨index, Nat.le_refl _, listCursors_below _ head member⟩
      · obtain ⟨next, lower, below⟩ := ih _ member
        exact ⟨next, by omega, below⟩

/-- Nested cursor writes never target the enclosing stream's list path. -/
theorem itemCursors_ne_path (path : ResponsePath) (index : Nat)
    (items : List ResponseValue)
    : ∀ entry ∈ ResponsePositions.itemCursors path index items, entry.1 ≠ path :=
  fun _ member => underItems_ne (itemCursors_underItems path index items member)

/-- The first item's nested cursors commute with all following items' nested cursors.
Witness: distinct indexed response subtrees cannot contain the same path.
-/
theorem itemCursors_commute (path : ResponsePath) (index : Nat)
    (head : ResponseValue) (tail : List ResponseValue)
    : CursorEquivalent
        (ResponsePositions.listCursors (path ++ [.index index]) head
          ++ ResponsePositions.itemCursors path (index + 1) tail)
        (ResponsePositions.itemCursors path (index + 1) tail
          ++ ResponsePositions.listCursors (path ++ [.index index]) head) := by
  apply cursorEquivalent_commute
  intro first firstMember second secondMember same
  exact underItems_disjoint (listCursors_below _ head firstMember)
    (same ▸ itemCursors_underItems path (index + 1) tail secondMember)

/-- A newer enclosing-list cursor makes an older write at that path redundant.
Witness: split lookup on the requested path; the first write shadows both histories.
-/
theorem cursorEquivalent_shadow (path : ResponsePath) (new old : Nat)
    (nested rest : ResponsePositions.Cursors)
    : CursorEquivalent ((path, new) :: nested ++ (path, old) :: rest)
        ((path, new) :: nested ++ rest) := by
  intro query
  by_cases same : path = query
  · simp only [List.cons_append, cursorAt_cons, ite_eq_left same]
  · simp only [List.cons_append, cursorAt_cons, ite_eq_right same, cursorAt_append_eq]

/-- Appending items preserves their introduced-position order, with shifted tail indices.
Witness: induction on the initial item list.
-/
theorem responseItems_append (containers : Bool) (path : ResponsePath) (index : Nat)
    (left right : List ResponseValue)
    : ResponsePositions.items containers path index (left ++ right)
      = ResponsePositions.items containers path index left
        ++ ResponsePositions.items containers path (index + left.length) right := by
  induction left generalizing index with
  | nil => simp [ResponsePositions.items]
  | cons head rest ih =>
      simp [ResponsePositions.items, ih, List.append_assoc,
        Nat.add_left_comm, Nat.add_comm]

/-- Appending items likewise appends their nested cursor contributions at shifted offsets.
Witness: induction through the same list positions.
-/
theorem itemCursors_append (path : ResponsePath) (index : Nat)
    (left right : List ResponseValue)
    : ResponsePositions.itemCursors path index (left ++ right)
      = ResponsePositions.itemCursors path index left
        ++ ResponsePositions.itemCursors path (index + left.length) right := by
  induction left generalizing index with
  | nil => simp [ResponsePositions.itemCursors]
  | cons head rest ih =>
      simp [ResponsePositions.itemCursors, ih, List.append_assoc,
        Nat.add_left_comm, Nat.add_comm]

end GraphQL.IncrementalDelivery.Correctness
