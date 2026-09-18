import Proofs.GraphQL.IncrementalDelivery.Semantics.StreamPositions

/-! Removing container positions preserves causal wire decoding and disjointness.
Cursor updates depend on payloads, not on whether their containers are counted.
-/

namespace GraphQL.IncrementalDelivery.Semantics

open GraphQL.IncrementalDelivery.Execution
open ResponsePositions

mutual
  /-- Removing value-container roots retains a sublist, by mutual value induction. -/
  theorem leaf_value_sublist (path : ResponsePath) (data : ResponseValue)
      : (value false path data).Sublist (value true path data) := by
    cases data with
    | null | scalar _ => exact .refl _
    | object data => exact (leaf_fields_sublist path data).cons _
    | list data => exact (leaf_items_sublist path 0 data).cons _

  /-- Leaf-only field positions form a sublist, by mutual field induction. -/
  theorem leaf_fields_sublist (path : ResponsePath) (data : List (Name × ResponseValue))
      : (fields false path data).Sublist (fields true path data) := by
    cases data with
    | nil => exact .refl _
    | cons field rest =>
        exact (leaf_value_sublist (path ++ [.field field.1]) field.2).append
          (leaf_fields_sublist path rest)

  /-- Leaf-only item positions form a sublist, by mutual item induction. -/
  theorem leaf_items_sublist (path : ResponsePath) (index : Nat)
      (data : List ResponseValue)
      : (items false path index data).Sublist (items true path index data) := by
    cases data with
    | nil => exact .refl _
    | cons head rest =>
        exact (leaf_value_sublist (path ++ [.index index]) head).append
          (leaf_items_sublist path (index + 1) rest)
end

/-- Leaf-only patch decoding preserves cursors and removes only container positions,
by splitting the owner lookup and, for streamed items, the cursor lookup.
-/
theorem positionPatch_leaves {notices cursors patch positions final}
    (h : DeliveryTrace.decodePatch true notices cursors patch = some (positions, final))
    : ∃ leaves,
        DeliveryTrace.decodePatch false notices cursors patch = some (leaves, final)
        ∧ leaves.Sublist positions := by
  cases patch with
  | object id data errors subPath =>
      cases owner : notices.find? (fun pending => pending.id == id) with
      | none => simp [DeliveryTrace.decodePatch, IncrementalResult.id, owner] at h
      | some notice =>
          simp [DeliveryTrace.decodePatch, IncrementalResult.id, owner] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨_, DeliveryTrace.decodePatch_object owner, leaf_fields_sublist _ data⟩
  | list id data errors =>
      cases owner : notices.find? (fun pending => pending.id == id) with
      | none => simp [DeliveryTrace.decodePatch, IncrementalResult.id, owner] at h
      | some notice =>
          cases cursor : cursorAt cursors notice.path with
          | none =>
              simp [DeliveryTrace.decodePatch, IncrementalResult.id, owner, cursor] at h
          | some index =>
              simp [DeliveryTrace.decodePatch, IncrementalResult.id, owner, cursor] at h
              obtain ⟨rfl, rfl⟩ := h
              exact ⟨_, DeliveryTrace.decodePatch_list owner cursor, leaf_items_sublist _ index data⟩

/-- Patch-list decoding preserves the leaf sublist and residual cursors, by list
induction using the decoder's head/tail equation.
-/
theorem positionPatches_leaves {notices cursors patches slices final}
    (h : DeliveryTrace.decodePatches true notices cursors patches = some (slices, final))
    : ∃ leaves,
        DeliveryTrace.decodePatches false notices cursors patches = some (leaves, final)
        ∧ leaves.flatten.Sublist slices.flatten := by
  induction patches generalizing cursors slices final with
  | nil =>
      simp only [DeliveryTrace.decodePatches, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨[], rfl, .refl _⟩
  | cons patch rest ih =>
      obtain ⟨positions, middle, tail, head, rest, rfl⟩ :=
        DeliveryTrace.decodePatches_cons_iff.mp h
      obtain ⟨leaf, hl, hs⟩ := positionPatch_leaves head
      obtain ⟨leaves, ht, hts⟩ := ih rest
      exact ⟨leaf :: leaves, by simp [DeliveryTrace.decodePatches, hl, ht], hs.append hts⟩

/-- Update decoding preserves the leaf sublist and residual cursors, by response-list
induction with the same causal notice accumulation in both modes.
-/
theorem positionUpdates_leaves {notices cursors updates slices final}
    (h : DeliveryTrace.decodeUpdates true notices cursors updates = some (slices, final))
    : ∃ leaves,
        DeliveryTrace.decodeUpdates false notices cursors updates = some (leaves, final)
        ∧ leaves.flatten.Sublist slices.flatten := by
  induction updates generalizing notices cursors slices final with
  | nil =>
      simp only [DeliveryTrace.decodeUpdates, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨[], rfl, .refl _⟩
  | cons update rest ih =>
      obtain ⟨head, middle, tail, patches, subsequent, rfl⟩ :=
        DeliveryTrace.decodeUpdates_cons_iff.mp h
      obtain ⟨leaf, hl, hs⟩ := positionPatches_leaves patches
      obtain ⟨leaves, ht, hts⟩ := ih subsequent
      refine ⟨leaf ++ leaves, by simp [DeliveryTrace.decodeUpdates, hl, ht], ?_⟩
      simpa only [List.flatten_append] using hs.append hts

/-- Leaf-only query slices are a sublist of container-inclusive positions, by initial
value projection and the update-decoder projection theorem.
-/
theorem deliversSlices_leaves {result : QueryResult}
    {slices : List (List ResponsePath)} (h : result.DeliversSlices true slices)
    : ∃ leaves,
        result.DeliversSlices false leaves ∧ leaves.flatten.Sublist slices.flatten := by
  cases result with
  | single response =>
      have equal : [value true [] response.data] = slices := Option.some.inj h
      subst slices
      exact ⟨
        [value false [] response.data],
        rfl,
        by simpa using leaf_value_sublist [] response.data
      ⟩
  | incremental initial subsequent =>
      obtain ⟨tail, final, ht, rfl⟩ := QueryResult.deliversSlices_incremental_iff.mp h
      obtain ⟨leaves, hl, hs⟩ := positionUpdates_leaves ht
      refine ⟨value false [] initial.data :: leaves,
        QueryResult.deliversSlices_incremental_iff.mpr ⟨leaves, final, hl, rfl⟩, ?_⟩
      exact (leaf_value_sublist [] initial.data).append hs

/-- Leaf-only slices inherit global uniqueness from container-inclusive slices, by
the decoded-position sublist theorem.
-/
theorem deliversSlices_leaves_nodup {result : QueryResult}
    {slices : List (List ResponsePath)} (h : result.DeliversSlices true slices)
    (hn : slices.flatten.Nodup)
    : ∃ leaves, result.DeliversSlices false leaves ∧ leaves.flatten.Nodup := by
  obtain ⟨leaves, hl, hs⟩ := deliversSlices_leaves h
  exact ⟨leaves, hl, hs.nodup hn⟩

end GraphQL.IncrementalDelivery.Semantics
