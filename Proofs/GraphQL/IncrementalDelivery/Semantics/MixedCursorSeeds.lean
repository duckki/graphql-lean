import Proofs.GraphQL.IncrementalDelivery.Semantics.MixedPathSlices
import Proofs.GraphQL.IncrementalDelivery.Semantics.StreamPositions

/-! Payload-seeded cursor certificates retain the exact source-slice offsets.
Children behind deferred payloads and streamed items receive the cursors of that
payload, rather than assuming their lists already occurred on the wire.
-/

namespace GraphQL.IncrementalDelivery.Semantics.MixedPaths

open GraphQL.IncrementalDelivery.Execution
open DeliveryPaths
open ResponsePositions (Cursors cursorAt listCursors fieldCursors itemCursors)

def resultCursors (cursors : α → Cursors) : Result α → Cursors
  | .error _ => []
  | .ok (data, _) => cursors data

def CursorExtends (before after : Cursors) : Prop :=
  ∀ path index, cursorAt before path = some index → cursorAt after path = some index

mutual
  inductive WorkCursorSeed : Cursors → Work → List (List ResponsePath) → Prop where
    | empty {cursors : Cursors} : WorkCursorSeed cursors .empty []
    | combine {cursors : Cursors} {left right : Work}
      {ls rs : List (List ResponsePath)}
      (hl : WorkCursorSeed cursors left ls) (hr : WorkCursorSeed cursors right rs)
      : WorkCursorSeed cursors (.combine left right) (ls ++ rs)
    | executionGroup {cursors : Cursors} {groups : List DeferredFragment}
      {path : ResponsePath} {completed : Result (List (Name × ResponseValue))}
      {children : Work} {slices : List (List ResponsePath)}
      (hc : WorkCursorSeed (resultCursors (fieldCursors path) completed) children slices)
      : WorkCursorSeed cursors (.executionGroup groups path completed children)
          (result (fields true path) completed :: slices)
    | stream {cursors : Cursors} {node : DeliveryNode}
      {items : List (Result ResponseValue × Work)} {index : Nat}
      {slices : List (List ResponsePath)}
      (hc : cursorAt cursors node.path = some index)
      (hi : ItemCursorSeed node.path index items slices)
      : WorkCursorSeed cursors (.stream node items) slices

  inductive ItemCursorSeed
      : ResponsePath → Nat → List (Result ResponseValue × Work) → List (List ResponsePath)
        → Prop where
    | nil {path : ResponsePath} {index : Nat} : ItemCursorSeed path index [] []
    | cons {path : ResponsePath} {index : Nat} {completed : Result ResponseValue}
      {children : Work} {tail : List (Result ResponseValue × Work)}
      {cs ts : List (List ResponsePath)}
      (hc
        : WorkCursorSeed (resultCursors (listCursors (path ++ [.index index])) completed)
            children cs)
      (ht : ItemCursorSeed path (index + 1) tail ts)
      : ItemCursorSeed path index ((completed, children) :: tail)
          (result (value true (path ++ [.index index])) completed :: (cs ++ ts))
end

mutual
  theorem WorkCursorSeed.slices {cursors : Cursors} {work : Work}
      {slices : List (List ResponsePath)} (h : WorkCursorSeed cursors work slices)
      : WorkSlices true work slices := by
    cases h with
    | empty => exact .empty
    | combine hl hr => exact .combine hl.slices hr.slices
    | executionGroup hc => exact .executionGroup hc.slices
    | stream _ hi => exact .stream hi.slices

  theorem ItemCursorSeed.slices {path : ResponsePath} {index : Nat}
      {items : List (Result ResponseValue × Work)} {slices : List (List ResponsePath)}
      (h : ItemCursorSeed path index items slices)
      : ItemSlices true path index items slices := by
    cases h with
    | nil => exact .nil
    | cons hc ht => exact .cons hc.slices ht.slices
end

theorem WorkCursorSeed.extend {before after : Cursors} {work : Work}
    {slices : List (List ResponsePath)} (h : WorkCursorSeed before work slices)
    (he : CursorExtends before after)
    : WorkCursorSeed after work slices := by
  cases work with
  | empty => cases h; exact .empty
  | combine left right =>
      cases h with
      | combine hl hr => exact .combine (hl.extend he) (hr.extend he)
  | executionGroup groups path completed children =>
      cases h with
      | executionGroup hc => exact .executionGroup hc
  | stream node items =>
      cases h with
      | stream hc hi => exact .stream (he _ _ hc) hi
termination_by sizeOf work

theorem cursorAt_append {left right : Cursors} {path : ResponsePath} {index : Nat}
    (h : cursorAt left path = some index)
    : cursorAt (left ++ right) path = some index := by
  unfold cursorAt at *
  rw [List.find?_append]
  cases hf : left.find? (fun entry => entry.1 == path) <;> simp_all

theorem CursorExtends.append_right (left right : Cursors)
    : CursorExtends left (left ++ right) := by
  intro path index h
  exact cursorAt_append h

theorem WorkCursorSeed.append_cursors {cursors : Cursors} {work : Work}
    {slices : List (List ResponsePath)} (h : WorkCursorSeed cursors work slices)
    (tail : Cursors)
    : WorkCursorSeed (cursors ++ tail) work slices :=
  h.extend (.append_right _ _)

theorem cursorAt_prepend {added cursors : Cursors} {path : ResponsePath}
    (h : ∀ entry ∈ added, entry.1 ≠ path)
    : cursorAt (added ++ cursors) path = cursorAt cursors path := by
  unfold cursorAt
  rw [List.find?_append]
  have hn : added.find? (fun entry => entry.1 == path) = none := by
    exact List.find?_eq_none.mpr (by simpa using h)
  simp [hn]

theorem CursorExtends.prepend {added cursors : Cursors}
    (h : ∀ entry ∈ added, ∀ index, cursorAt cursors entry.1 ≠ some index)
    : CursorExtends cursors (added ++ cursors) := by
  intro path index hc
  rw [cursorAt_prepend]
  · exact hc
  · intro entry he hp
    exact h entry he index (hp ▸ hc)

def CursorHistory (cursors : Cursors) (positions : List ResponsePath) : Prop :=
  ∀ entry ∈ cursors, entry.1 ∈ positions

mutual
  theorem listCursors_positions (path : ResponsePath) (data : ResponseValue)
      : CursorHistory (listCursors path data) (value true path data) := by
    cases data with
    | null => simp [CursorHistory, listCursors]
    | scalar _ => simp [CursorHistory, listCursors]
    | object data =>
        intro entry he
        exact List.mem_append_right _ (fieldCursors_positions path data entry he)
    | list data =>
        intro entry he
        simp only [listCursors, List.mem_cons] at he
        rcases he with rfl | he
        · simp [value]
        · exact List.mem_append_right _ (itemCursors_positions path 0 data entry he)

  theorem fieldCursors_positions (path : ResponsePath)
      (data : List (Name × ResponseValue))
      : CursorHistory (fieldCursors path data) (fields true path data) := by
    cases data with
    | nil => simp [CursorHistory, fieldCursors]
    | cons head tail =>
        intro entry he
        simp only [fieldCursors, List.mem_append] at he
        rcases he with he | he
        · exact List.mem_append_left _ (listCursors_positions _ head.2 entry he)
        · exact List.mem_append_right _ (fieldCursors_positions path tail entry he)

  theorem itemCursors_positions (path : ResponsePath) (index : Nat)
      (data : List ResponseValue)
      : CursorHistory (itemCursors path index data) (items true path index data) := by
    cases data with
    | nil => simp [CursorHistory, itemCursors]
    | cons head tail =>
        intro entry he
        simp only [itemCursors, List.mem_append] at he
        rcases he with he | he
        · exact List.mem_append_left _ (listCursors_positions _ head entry he)
        · exact List.mem_append_right _ (itemCursors_positions path (index + 1) tail entry he)
end

theorem cursorAt_member {cursors : Cursors} {path : ResponsePath} {index : Nat}
    (h : cursorAt cursors path = some index)
    : (path, index) ∈ cursors := by
  unfold cursorAt at h
  cases hf : cursors.find? (fun entry => entry.1 == path) with
  | none => simp [hf] at h
  | some entry =>
      have hp := List.find?_some hf
      have hi : entry.2 = index := by simpa [hf] using h
      have he : entry = (path, index) := Prod.ext (by simpa using hp) hi
      exact he ▸ List.mem_of_find?_eq_some hf

theorem CursorHistory.lookup {cursors : Cursors} {positions : List ResponsePath}
    (h : CursorHistory cursors positions) {path : ResponsePath} {index : Nat}
    (hc : cursorAt cursors path = some index)
    : path ∈ positions :=
  h _ (cursorAt_member hc)

theorem CursorHistory.append {left right : Cursors} {ls rs : List ResponsePath}
    (hl : CursorHistory left ls) (hr : CursorHistory right rs)
    : CursorHistory (left ++ right) (ls ++ rs) := by
  intro entry he
  rcases List.mem_append.mp he with he | he
  · exact List.mem_append_left _ (hl _ he)
  · exact List.mem_append_right _ (hr _ he)

theorem CursorHistory.mono {cursors : Cursors} {before after : List ResponsePath}
    (h : CursorHistory cursors before) (hs : before.Subset after)
    : CursorHistory cursors after :=
  fun entry he => hs (h entry he)

theorem CursorExtends.of_disjoint_history {before added : Cursors}
    {prior produced : List ResponsePath} (hb : CursorHistory before prior)
    (ha : CursorHistory added produced) (hn : (prior ++ produced).Nodup)
    : CursorExtends before (added ++ before) := by
  apply CursorExtends.prepend
  intro entry he index hc
  exact (List.nodup_append.mp hn).2.2 _ (hb.lookup hc) _ (ha entry he) rfl

theorem WorkCursorSeed.prepend_disjoint {cursors added : Cursors} {work : Work}
    {slices : List (List ResponsePath)} (h : WorkCursorSeed cursors work slices)
    {prior produced : List ResponsePath} (hc : CursorHistory cursors prior)
    (ha : CursorHistory added produced) (hn : (prior ++ produced).Nodup)
    : WorkCursorSeed (added ++ cursors) work slices :=
  h.extend (CursorExtends.of_disjoint_history hc ha hn)

mutual
  theorem WorkCursorSeed.unique {cursors : Cursors} {work : Work}
      {left right : List (List ResponsePath)}
      (hl : WorkCursorSeed cursors work left) (hr : WorkCursorSeed cursors work right)
      : left = right := by
    cases work with
    | empty => cases hl; cases hr; rfl
    | combine left right =>
        cases hl with
        | combine hll hlr =>
            cases hr with
            | combine hrl hrr => rw [hll.unique hrl, hlr.unique hrr]
    | executionGroup groups path completed children =>
        cases hl with
        | executionGroup hl =>
            cases hr with
            | executionGroup hr => rw [hl.unique hr]
    | stream node items =>
        cases hl with
        | stream hcl hil =>
            cases hr with
            | stream hcr hir =>
                have he := Option.some.inj (hcl.symm.trans hcr)
                subst_vars
                exact hil.unique hir
  termination_by sizeOf work

  theorem ItemCursorSeed.unique {path : ResponsePath} {index : Nat}
      {items : List (Result ResponseValue × Work)} {left right : List (List ResponsePath)}
      (hl : ItemCursorSeed path index items left)
      (hr : ItemCursorSeed path index items right)
      : left = right := by
    cases items with
    | nil => cases hl; cases hr; rfl
    | cons item tail =>
        cases hl with
        | cons hcl htl =>
            cases hr with
            | cons hcr htr => rw [hcl.unique hcr, htl.unique htr]
  termination_by sizeOf items
end

end GraphQL.IncrementalDelivery.Semantics.MixedPaths
