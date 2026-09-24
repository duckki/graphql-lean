import Proofs.GraphQL.IncrementalDelivery.Correctness.SourceAttachments
import Proofs.GraphQL.IncrementalDelivery.Correctness.SourceTypedEntries

/-! Exact slice boundaries align typed payloads with their attachment witnesses. -/

namespace GraphQL.IncrementalDelivery.Correctness.SourceReconstruction
open GraphQL.IncrementalDelivery.Execution
open TypedResponse
open SourceAttachments

mutual
  /-- Typed work slices and attachment slices have the same count, by mutual work
  induction.
  -/
  theorem WorkEntries.attached_length {work : Work} {entries : List (List Entry)}
      {available : List Entry} {slices : List (List ResponsePath)}
      (h : WorkEntries work entries) (ha : WorkAttached available work slices)
      : entries.length = slices.length := by
    cases h with
    | empty =>
        cases ha; rfl
    | combine hl hr =>
        cases ha with
        | combine hal har =>
            simp only [List.length_append, hl.attached_length hal, hr.attached_length har]
    | executionGroup hc =>
        cases ha with
        | executionGroup _ hac => simp only [List.length_cons, hc.attached_length hac]
    | stream hi =>
        cases ha with
        | stream _ hai => exact hi.attached_length hai

  /-- Typed item slices and attachment slices have the same count, by mutual item
  induction.
  -/
  theorem ItemEntries.attached_length {path other : ResponsePath} {index next : Nat}
      {items : List (Result ResponseValue × Work)} {entries : List (List Entry)}
      {available : List Entry} {slices : List (List ResponsePath)}
      (h : ItemEntries path index items entries)
      (ha : ItemsAttached available other next items slices)
      : entries.length = slices.length := by
    cases h with
    | nil =>
        cases ha; rfl
    | cons hc ht =>
        cases ha with
        | cons hac hat => simp only [List.length_cons, List.length_append,
            hc.attached_length hac, ht.attached_length hat]
end

/-- A value's container-inclusive paths start at its own path, by constructor cases. -/
theorem value_paths_head (path : ResponsePath) (data : ResponseValue)
    : (DeliveryPaths.value true path data).head? = some path := by
  cases data <;> simp [DeliveryPaths.value]

/-- Nonempty successful item slices fix their starting index, by equating the
first item's root path in the typed and attachment witnesses. -/
theorem ItemsAttached.index_eq {available : List Entry} {path : ResponsePath}
    {left right : Nat} {items : List (Result ResponseValue × Work)}
    {entries : List (List Entry)} (h : ItemEntries path left items entries)
    (hs : ItemsSuccess items)
    (ha : ItemsAttached available path right items (entryPaths entries)) (hn : items ≠ [])
    : left = right := by
  cases h with
  | nil => exact (hn rfl).elim
  | @cons _ _ completed children tail cs ts hc ht =>
      obtain ⟨data, rfl⟩ := hs.1
      generalize he : entryPaths (result (value (path ++ [.index left])) (.ok (data, 0)) :: (cs ++ ts)) = slices at ha
      cases ha with
      | cons hac hat =>
          simp only [entryPaths, List.map_cons, List.map_append, result, value_paths, DeliveryPaths.result] at he
          have hh := congrArg List.head? (List.cons.inj he).1
          rw [value_paths_head, value_paths_head] at hh
          have heq := List.append_cancel_left (Option.some.inj hh)
          simpa using heq

end GraphQL.IncrementalDelivery.Correctness.SourceReconstruction
