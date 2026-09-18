import Proofs.GraphQL.IncrementalDelivery.Semantics.SeededPathOwnership
import Proofs.GraphQL.IncrementalDelivery.Correctness.TypedResponse

/-! Attachment witnesses use the same stream offsets as seeded source slices.
Existing ambient objects remain available across nested same-path deferrals.
-/

namespace GraphQL.IncrementalDelivery.Correctness.SourceAttachments

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open Semantics.MixedPaths
open DeliveryPaths
open ResponsePositions (Cursors cursorAt listCursors fieldCursors itemCursors)
open TypedResponse (Entry Atom)

mutual
  /-- Every work payload can attach to ambient entries or its producer's entries;
  the slices retain the same absolute stream offsets as the cursor seed. -/
  inductive WorkAttached : List Entry → Work → List (List ResponsePath) → Prop where
    | empty {available : List Entry} : WorkAttached available .empty []
    | append {available : List Entry} {left right : Work}
      {ls rs : List (List ResponsePath)} (hl : WorkAttached available left ls)
      (hr : WorkAttached available right rs)
      : WorkAttached available (.append left right) (ls ++ rs)
    | deferred {available : List Entry} {groups : List DeferredFragment}
      {path : ResponsePath} {completed : Result (List (Name × ResponseValue))}
      {children : Work} {slices : List (List ResponsePath)}
      (ha : (path, Atom.object) ∈ available)
      (hc
        : WorkAttached
            (available ++ TypedResponse.result (TypedResponse.fields path) completed)
            children slices)
      : WorkAttached available (.deferred groups path completed children)
          (result (fields true path) completed :: slices)
    | stream {available : List Entry} {node : DeliveryNode}
      {items : List (Result ResponseValue × Work)} {index : Nat}
      {slices : List (List ResponsePath)}
      (ha : (node.path, Atom.list) ∈ available)
      (hi : ItemsAttached available node.path index items slices)
      : WorkAttached available (.stream node items) slices

  /-- Stream items attach their children beneath their own value, starting at the
  given response index; sibling items share the original ambient entries. -/
  inductive ItemsAttached
      : List Entry → ResponsePath → Nat → List (Result ResponseValue × Work)
        → List (List ResponsePath) → Prop where
    | nil {available : List Entry} {path : ResponsePath} {index : Nat}
      : ItemsAttached available path index [] []
    | cons {available : List Entry} {path : ResponsePath} {index : Nat}
      {completed : Result ResponseValue} {children : Work}
      {tail : List (Result ResponseValue × Work)} {cs ts : List (List ResponsePath)}
      (hc
        : WorkAttached
            (available
              ++ TypedResponse.result
                  (TypedResponse.value (path ++ [.index index])) completed)
            children cs)
      (ht : ItemsAttached available path (index + 1) tail ts)
      : ItemsAttached available path index ((completed, children) :: tail)
          (result (value true (path ++ [.index index])) completed :: (cs ++ ts))
end

mutual
  /-- Adding ambient entries preserves work attachments, by mutual structural
  induction.
  -/
  theorem WorkAttached.mono {left right : List Entry} {work : Work}
      {slices : List (List ResponsePath)} (h : WorkAttached left work slices)
      (hm : ∀entry ∈ left, entry ∈ right)
      : WorkAttached right work slices := by
    cases h with
    | empty => exact .empty
    | append hl hr => exact .append (hl.mono hm) (hr.mono hm)
    | deferred ha hc =>
        refine .deferred (hm _ ha) (hc.mono ?_)
        intro entry he
        rcases List.mem_append.mp he with he | he
        · exact List.mem_append_left _ (hm _ he)
        · exact List.mem_append_right _ he
    | stream ha hi => exact .stream (hm _ ha) (hi.mono hm)

  /-- Adding ambient entries preserves item attachments, by induction through children. -/
  theorem ItemsAttached.mono {left right : List Entry} {path : ResponsePath} {index : Nat}
      {items : List (Result ResponseValue × Work)} {slices : List (List ResponsePath)}
      (h : ItemsAttached left path index items slices) (hm : ∀entry ∈ left, entry ∈ right)
      : ItemsAttached right path index items slices := by
    cases h with
    | nil => exact .nil
    | cons hc ht =>
        refine .cons (hc.mono ?_) (ht.mono hm)
        intro entry he
        rcases List.mem_append.mp he with he | he
        · exact List.mem_append_left _ (hm _ he)
        · exact List.mem_append_right _ he
end

/-- A completion has one shared cursor-seed and attachment witness, using its
immediate typed entries in addition to the ambient entries. -/
def AttachedCompletion (available : List Entry) (entries : α → List Entry)
    (cursors : α → Cursors) (completed : Completion α)
    : Prop :=
  ∃ slices,
    WorkCursorSeed (resultCursors cursors completed.result) completed.work slices
    ∧ WorkAttached (available ++ TypedResponse.result entries completed.result)
        completed.work slices

/-- A completion combines source ownership with attachments to available entries. -/
def OwnedAttachedCompletion (available : List Entry) (entries : α → List Entry)
    (paths : α → List ResponsePath) (cursors : α → Cursors)
    (scope : ResponsePath → Prop) (completed : Completion α)
    : Prop :=
  SeedOwnsCompletion paths cursors scope completed
  ∧ AttachedCompletion available entries cursors completed

/-- Work has owned slices with cursor-independent seeds and ambient attachments. -/
def OwnedAttachedWork (available : List Entry) (scope : ResponsePath → Prop) (work : Work)
    : Prop :=
  SeedOwnsWork scope work
  ∧ ∃ slices,
      (∀ cursors, WorkCursorSeed cursors work slices) ∧ WorkAttached available work slices

/-- Items have owned, attached slices at the supplied absolute starting index. -/
def OwnedAttachedItems (available : List Entry) (path : ResponsePath) (index : Nat)
    (scope : ResponsePath → Prop) (items : List (Result ResponseValue × Work))
    : Prop :=
  SeedOwnsItems path index scope items
  ∧ ∃ slices,
      ItemCursorSeed path index items slices
      ∧ ItemsAttached available path index items slices

/-- Any seed for this completion identifies its attachment slices, by seed uniqueness. -/
theorem AttachedCompletion.at {available : List Entry} {entries : α → List Entry}
    {cursors : α → Cursors} {completed : Completion α}
    (h : AttachedCompletion available entries cursors completed)
    {slices : List (List ResponsePath)}
    (hs : WorkCursorSeed (resultCursors cursors completed.result) completed.work slices)
    : WorkAttached (available ++ TypedResponse.result entries completed.result)
        completed.work slices := by
  obtain ⟨s, hw, ha⟩ := h
  exact hw.unique hs ▸ ha

/-- Widening the ownership scope preserves attachments, by ownership monotonicity. -/
theorem OwnedAttachedCompletion.mono {available : List Entry} {entries : α → List Entry}
    {paths : α → List ResponsePath} {cursors : α → Cursors}
    {left right : ResponsePath → Prop} {completed : Completion α}
    (h : OwnedAttachedCompletion available entries paths cursors left completed)
    (hs : ∀p, left p → right p)
    : OwnedAttachedCompletion available entries paths cursors right completed :=
  ⟨h.1.mono hs, h.2⟩

end GraphQL.IncrementalDelivery.Correctness.SourceAttachments
