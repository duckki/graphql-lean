import Proofs.GraphQL.IncrementalDelivery.Semantics.PathOwnership

/-! Absolute introduced-position slices for exact mixed execution work. Stream
offsets are ghost witnesses because Work.stream does not retain its initial item
index. These relations describe source work, not causal decoding of wire patches.
One slice is retained per result, including empty slices for errors.
-/

namespace GraphQL.IncrementalDelivery.Semantics.MixedPaths

open GraphQL.IncrementalDelivery.Execution
open DeliveryPaths

mutual
  inductive WorkSlices (containers : Bool) : Work → List (List ResponsePath) → Prop where
    | empty : WorkSlices containers .empty []
    | append {left right : Work} {leftSlices rightSlices : List (List ResponsePath)}
      (hleft : WorkSlices containers left leftSlices)
      (hright : WorkSlices containers right rightSlices)
      : WorkSlices containers (.append left right) (leftSlices ++ rightSlices)
    | deferred {groups : List DeferredFragment} {path : ResponsePath}
      {completed : Result (List (Name × ResponseValue))} {children : Work}
      {slices : List (List ResponsePath)}
      (hchildren : WorkSlices containers children slices)
      : WorkSlices containers (.deferred groups path completed children)
          (result (fields containers path) completed :: slices)
    | stream {node : DeliveryNode} {items : List (Result ResponseValue × Work)}
      {index : Nat} {slices : List (List ResponsePath)}
      (hitems : ItemSlices containers node.path index items slices)
      : WorkSlices containers (.stream node items) slices

  inductive ItemSlices (containers : Bool)
      : ResponsePath → Nat → List (Result ResponseValue × Work) → List (List ResponsePath)
        → Prop where
    | nil {path : ResponsePath} {index : Nat} : ItemSlices containers path index [] []
    | cons {path : ResponsePath} {index : Nat} {completed : Result ResponseValue}
      {children : Work} {items : List (Result ResponseValue × Work)}
      {childSlices tailSlices : List (List ResponsePath)}
      (hchildren : WorkSlices containers children childSlices)
      (tail : ItemSlices containers path (index + 1) items tailSlices)
      : ItemSlices containers path index ((completed, children) :: items)
          (result (value containers (path ++ [.index index])) completed
            :: (childSlices ++ tailSlices))
end

def OwnsWork (containers : Bool) (scope : ResponsePath → Prop) (work : Work) : Prop :=
  ∃ slices, WorkSlices containers work slices ∧ Owns scope slices.flatten

def OwnsCompletion (containers : Bool) (paths : α → List ResponsePath)
    (scope : ResponsePath → Prop) (completed : Completion α)
    : Prop :=
  ∃ slices,
    WorkSlices containers completed.work slices
    ∧ Owns scope (result paths completed.result ++ slices.flatten)

def OwnsItems (containers : Bool) (path : ResponsePath) (index : Nat)
    (scope : ResponsePath → Prop) (items : List (Result ResponseValue × Work))
    : Prop :=
  ∃ slices, ItemSlices containers path index items slices ∧ Owns scope slices.flatten

def UnderItemRange (base : ResponsePath) (start finish : Nat) (path : ResponsePath)
    : Prop :=
  ∃ index, start ≤ index ∧ index < finish ∧ Below (base ++ [.index index]) path

theorem underItemRange_below {base path : ResponsePath} {start finish : Nat}
    (h : UnderItemRange base start finish path)
    : Below base path := by
  obtain ⟨_, _, _, hp⟩ := h
  exact below_child hp

theorem underItemRange_ne {base path : ResponsePath} {start finish : Nat}
    (h : UnderItemRange base start finish path)
    : path ≠ base := by
  obtain ⟨_, _, _, hp⟩ := h
  exact below_child_ne hp

theorem underItemRange_underItems {base path : ResponsePath} {start finish : Nat}
    (h : UnderItemRange base start finish path)
    : UnderItems base start path := by
  obtain ⟨index, hi, _, hp⟩ := h
  exact ⟨index, hi, hp⟩

theorem underItemRange_mono {base path : ResponsePath} {start finish lower upper : Nat}
    (h : UnderItemRange base start finish path) (hl : lower ≤ start) (hu : finish ≤ upper)
    : UnderItemRange base lower upper path := by
  obtain ⟨index, hi, hj, hp⟩ := h
  exact ⟨index, Nat.le_trans hl hi, Nat.lt_of_lt_of_le hj hu, hp⟩

theorem underItemRange_disjoint {base path : ResponsePath}
    {leftStart leftFinish rightStart rightFinish : Nat} (hgap : leftFinish ≤ rightStart)
    (hl : UnderItemRange base leftStart leftFinish path)
    (hr : UnderItemRange base rightStart rightFinish path)
    : False := by
  obtain ⟨left, _, hleft, hl⟩ := hl
  obtain ⟨right, hright, _, hr⟩ := hr
  have he := below_children_eq hl hr
  cases he
  omega

theorem below_item_underItemRange {base path : ResponsePath} {index start finish : Nat}
    (h : Below (base ++ [.index index]) path) (hl : start ≤ index) (hu : index < finish)
    : UnderItemRange base start finish path :=
  ⟨index, hl, hu, h⟩

theorem underItemRange_empty (base path : ResponsePath) (index : Nat)
    : ¬ UnderItemRange base index index path := by
  rintro ⟨_, hl, hu, _⟩
  omega

end GraphQL.IncrementalDelivery.Semantics.MixedPaths
