import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.KeyRenamingCollection
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ScheduledWorkRefinement
import Proofs.GraphQL.IncrementalDelivery.Semantics.RefRegions

/-! Construct a compatible map from the current cut and eager supplies. Only the unused
tail is retargeted; every earlier key retains its existing image, including ancestors and
keys inside stream-item Work. This is the map-extension edge, not a general recursive
executor theorem or an independently chosen native identity correspondence. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.KeyRenaming

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics.RefRegions

-----------------------------------------------------------------------------------------
-- Retarget the unused tail at the actual two supply boundaries
-----------------------------------------------------------------------------------------

def PrefixBelow (keys : Nat → Nat) (cut target : Nat) : Prop :=
  ∀ key < cut, keys key < target

/-- Preserve all allocated images and start fresh consecutive images at `target`.
Unlike precomposition, this constructor takes the actual eager boundary directly. -/
def retargetTail (previous : Nat → Nat) (cut target : Nat) : Nat → Nat :=
  fun key => if key < cut then previous key else target + (key - cut)

theorem retargetTail_earlier (previous : Nat → Nat) {cut target key : Nat}
    (earlier : key < cut)
    : retargetTail previous cut target key = previous key := by
  simp only [retargetTail, earlier, ↓reduceIte]

theorem retargetTail_later (previous : Nat → Nat) {cut target key : Nat}
    (later : cut ≤ key)
    : retargetTail previous cut target key = target + (key - cut) := by
  simp only [retargetTail, Nat.not_lt.mpr later, ↓reduceIte]

theorem retargetTail_boundary (previous : Nat → Nat) (cut target : Nat)
    : retargetTail previous cut target cut = target := by
  simp only [retargetTail_later previous (Nat.le_refl _), Nat.sub_self, Nat.add_zero]

theorem retargetTail_injective {previous : Nat → Nat} {cut target : Nat}
    (injective : Function.Injective previous) (bounded : PrefixBelow previous cut target)
    : Function.Injective (retargetTail previous cut target) := by
  intro left right same
  by_cases earlierLeft : left < cut <;> by_cases earlierRight : right < cut
  · simp only [retargetTail_earlier previous earlierLeft,
      retargetTail_earlier previous earlierRight] at same
    exact injective same
  · have := bounded left earlierLeft
    have laterRight : cut ≤ right := by omega
    simp only [retargetTail_earlier previous earlierLeft,
      retargetTail_later previous laterRight] at same
    omega
  · have := bounded right earlierRight
    have laterLeft : cut ≤ left := by omega
    simp only [retargetTail_later previous laterLeft,
      retargetTail_earlier previous earlierRight] at same
    omega
  · have laterLeft : cut ≤ left := by omega
    have laterRight : cut ≤ right := by omega
    simp only [retargetTail_later previous laterLeft,
      retargetTail_later previous laterRight] at same
    omega

theorem retargetTail_fresh (previous : Nat → Nat) (cut target : Nat)
    : FreshTail (retargetTail previous cut target) cut := by
  intro offset
  rw [retargetTail_later previous (Nat.le_add_right _ _), retargetTail_boundary]
  omega

theorem retargetTail_prefix {previous : Nat → Nat} {cut target : Nat}
    (bounded : PrefixBelow previous cut target)
    : PrefixBelow (retargetTail previous cut target) cut target := by
  intro key earlier
  rw [retargetTail_earlier previous earlier]
  exact bounded key earlier

theorem PrefixBelow.advance {keys : Nat → Nat} {start finish : Nat}
    (bounded : PrefixBelow keys start (keys start)) (fresh : FreshTail keys start)
    (advanced : start ≤ finish)
    : PrefixBelow keys finish (keys finish) := by
  intro key earlier
  have endKey := fresh (finish - start)
  have base : start + (finish - start) = finish := by omega
  rw [base] at endKey
  by_cases old : key < start
  · have := bounded key old
    omega
  · have keyImage := fresh (key - start)
    have here : start + (key - start) = key := by omega
    rw [here] at keyImage
    omega

-----------------------------------------------------------------------------------------
-- Preserve metadata already allocated in the prefix
-----------------------------------------------------------------------------------------

theorem node_congr {before after : Nat → Nat} (original : DeliveryNode)
    (same : after original.ref = before original.ref)
    : node after original = node before original := by
  simp only [node, same]

theorem fragment_congr {before after : Nat → Nat} (original : DeferredFragment)
    (same : ∀ key ∈ Semantics.RefRoles.fragmentRefs original, after key = before key)
    : fragment after original = fragment before original := by
  have own := same original.node.ref (by simp [Semantics.RefRoles.fragmentRefs])
  have ancestors : original.ancestors.map (node after) = original.ancestors.map (node before)
      := by
    apply List.map_congr_left
    intro ancestor member
    exact node_congr ancestor (same ancestor.ref (by
      simp only [Semantics.RefRoles.fragmentRefs, List.mem_cons]
      exact Or.inr (List.mem_map.mpr ⟨ancestor, member, rfl⟩)))
  simp only [fragment, node_congr original.node own, ancestors]

theorem retargetTail_context (previous : Nat → Nat) (cut target : Nat)
    (context : DeferMap)
    (bounded : ∀ key ∈ context.flatMap Semantics.RefRoles.fragmentRefs, key < cut)
    : context.map (fragment (retargetTail previous cut target))
      = context.map (fragment previous) := by
  apply List.map_congr_left
  intro group member
  apply fragment_congr
  intro key used
  exact retargetTail_earlier previous
    (bounded key (List.mem_flatMap.mpr ⟨group, member, used⟩))

-----------------------------------------------------------------------------------------
-- All-key coverage includes every stream item and flattened ancestor placeholder
-----------------------------------------------------------------------------------------

private theorem child_group_keys (groups : List DeferredFragment) (path : ResponsePath)
    (result : Result (List (Name × ResponseValue))) (children : Work)
    : (allRefs children).Subset
        (allRefs (.executionGroup groups path result children)) := by
  intro key member
  simp only [allRefs, rootRefs, hiddenRegions, List.mem_append, or_assoc] at member ⊢
  exact Or.inr member

private theorem item_stream_keys (node : DeliveryNode)
    (items : List (Result ResponseValue × Work)) (item : Result ResponseValue × Work)
    (member : item ∈ items)
    : (allRefs item.2).Subset (allRefs (.stream node items)) := by
  intro key used
  rcases List.mem_append.mp used with used | used
  · apply hiddenRegion_subset_allRefs _ ?_ used
    simp only [hiddenRegions]
    exact List.mem_flatMap.mpr ⟨item, member, List.mem_cons.mpr (Or.inl rfl)⟩
  · obtain ⟨region, regionMember, used⟩ := List.mem_flatten.mp used
    apply hiddenRegion_subset_allRefs _ ?_ used
    simp only [hiddenRegions]
    exact List.mem_flatMap.mpr ⟨item, member, List.mem_cons.mpr (Or.inr regionMember)⟩

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.KeyRenaming

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.ScheduledWork

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics.RefRegions
open KeyRenaming

/-- Extending the map cannot invalidate earlier payload/ownership correspondence.
Agreement is required on every key, including hidden stream-item regions. -/
theorem WorkRefines.rekey {before after : Nat → Nat} {left right : Work}
    (related : WorkRefines before left right)
    (same : ∀ key ∈ allRefs left, after key = before key)
    : WorkRefines after left right := by
  revert same
  induction related
    using WorkRefines.rec
      (motive_2 :=
        fun left right _ =>
          (∀ item ∈ left, ∀ key ∈ allRefs item.2, after key = before key)
          → ItemsRefine after left right) with
  | empty => intro _; exact .empty
  | combine head tail first later =>
      intro same
      exact .combine
        (first (fun key member => same key
          ((mem_allRefs_combine _ _ _).mpr (Or.inl member))))
        (later (fun key member => same key
          ((mem_allRefs_combine _ _ _).mpr (Or.inr member))))
  | @executionGroup groups path result eagerResult children eagerChildren payload nested ih
    =>
      intro same
      have mapped : groups.map (fragment before) = groups.map (fragment after) := by
        apply List.map_congr_left
        intro group member
        symm
        apply fragment_congr
        intro key used
        exact same key (rootRefs_subset_allRefs _ (List.mem_append.mpr (Or.inl
          (List.mem_flatMap.mpr ⟨group, member, used⟩))))
      rw [mapped]
      exact .executionGroup payload (ih (fun key member => same key
        (child_group_keys groups path result children member)))
  | @stream descriptor items eagerItems nested ih =>
      intro same
      have mapped := node_congr descriptor (same descriptor.ref
        (rootRefs_subset_allRefs _ (by simp only [rootRefs, List.mem_singleton])))
      rw [← mapped]
      exact .stream (ih (fun item member key used => same key
        (item_stream_keys descriptor items item member used)))
  | nil => exact .nil
  | @cons result eagerResult children eagerChildren rest eagerRest payload nested tail head ih
    =>
      rename_i same
      exact .cons payload (head (same (result, children) (by simp)))
        (ih (fun item member => same item (List.mem_cons_of_mem _ member)))

theorem ItemsRefine.rekey {before after : Nat → Nat} {left right}
    (related : ItemsRefine before left right)
    (same : ∀ item ∈ left, ∀ key ∈ allRefs item.2, after key = before key)
    : ItemsRefine after left right := by
  induction left generalizing right with
  | nil => cases related; exact .nil
  | cons item rest ih =>
      rcases item with ⟨result, children⟩
      cases related with
      | cons payload nested tail =>
          exact .cons payload (nested.rekey (same (result, children) (by simp)))
            (ih tail (fun item member => same item (List.mem_cons_of_mem _ member)))

theorem CompletionRefines.rekey {before after : Nat → Nat} {left right : Completion α}
    (related : CompletionRefines before left right)
    (same : ∀ key ∈ allRefs left.work, after key = before key)
    : CompletionRefines after left right :=
  ⟨related.1, related.2.rekey same⟩

/-- Checked extension edge: construct the map from supply boundaries and preserve an
already related prefix using its actual key-region bound. The recursive executor still
has to construct the input relation and eager-bound premise from that same execution. -/
def PrefixWorkExtension : Prop :=
  ∀ (α : Type) previous cut target (left right : Completion α),
    Function.Injective previous
    → PrefixBelow previous cut target
    → (∀ key ∈ allRefs left.work, key < cut)
    → CompletionRefines previous left right
    → let next := retargetTail previous cut target
      Function.Injective next
      ∧ PrefixBelow next cut target
      ∧ next cut = target
      ∧ FreshTail next cut
      ∧ CompletionRefines next left right

theorem prefixWorkExtension_holds : PrefixWorkExtension := by
  intro α previous cut target left right injective images bounded related
  exact ⟨retargetTail_injective injective images, retargetTail_prefix images,
    retargetTail_boundary previous cut target, retargetTail_fresh previous cut target,
    related.rekey (fun key member => retargetTail_earlier previous (bounded key member))⟩

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.ScheduledWork
