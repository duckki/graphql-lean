import Proofs.GraphQL.IncrementalDelivery.Correctness.TypedResponse

/-! Source-work success and typed slices; these are proof witnesses, not admission laws. -/

namespace GraphQL.IncrementalDelivery.Correctness.SourceReconstruction

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open TypedResponse

mutual
  /-- All deferred outcomes and streamed items in the finite work succeed with zero
  errors. -/
  def WorkSuccess : Work → Prop
    | .empty => True
    | .combine left right => WorkSuccess left ∧ WorkSuccess right
    | .executionGroup _ _ result children =>
        (∃ data, result = .ok (data, 0)) ∧ WorkSuccess children
    | .stream _ items => ItemsSuccess items

  /-- Each retained item has a zero-error value and successful nested work. -/
  def ItemsSuccess : List (Result ResponseValue × Work) → Prop
    | [] => True
    | (result, children) :: tail =>
        (∃ data, result = .ok (data, 0)) ∧ WorkSuccess children ∧ ItemsSuccess tail
end

/-- The immediate completion and every retained task succeed with zero errors. -/
def CompletionSuccess (completed : Completion α) : Prop :=
  (∃ data, completed.result = .ok (data, 0)) ∧ WorkSuccess completed.work

mutual
  /-- Typed source slices for work, with existential absolute stream offsets. -/
  inductive WorkEntries : Work → List (List Entry) → Prop where
    | empty : WorkEntries .empty []
    | combine {left right : Work} {ls rs : List (List Entry)}
      (hl : WorkEntries left ls) (hr : WorkEntries right rs)
      : WorkEntries (.combine left right) (ls ++ rs)
    | executionGroup {groups : List DeferredFragment} {path : ResponsePath}
      {completed : Result (List (Name × ResponseValue))} {children : Work}
      {slices : List (List Entry)} (hc : WorkEntries children slices)
      : WorkEntries (.executionGroup groups path completed children)
          (result (fields path) completed :: slices)
    | stream {node : DeliveryNode} {items : List (Result ResponseValue × Work)}
      {index : Nat} {slices : List (List Entry)}
      (hi : ItemEntries node.path index items slices)
      : WorkEntries (.stream node items) slices

  /-- Typed source slices for successive streamed items starting at the supplied index. -/
  inductive ItemEntries
      : ResponsePath → Nat → List (Result ResponseValue × Work) → List (List Entry)
        → Prop where
    | nil {path : ResponsePath} {index : Nat} : ItemEntries path index [] []
    | cons {path : ResponsePath} {index : Nat} {completed : Result ResponseValue}
      {children : Work} {tail : List (Result ResponseValue × Work)}
      {cs ts : List (List Entry)} (hc : WorkEntries children cs)
      (ht : ItemEntries path (index + 1) tail ts)
      : ItemEntries path index ((completed, children) :: tail)
          (result (value (path ++ [.index index])) completed :: (cs ++ ts))
end

end GraphQL.IncrementalDelivery.Correctness.SourceReconstruction
