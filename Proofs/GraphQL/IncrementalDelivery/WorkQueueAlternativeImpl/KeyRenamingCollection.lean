import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.KeyRenamingMetadata
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.CutKeySupply
import Proofs.GraphQL.IncrementalDelivery.Semantics.CollectedSupply

/-! Actual recursive object collection under one delivery-key map. A fresh tail couples
the two supplies; inherited metadata uses the same map without assuming its validity.
Collection allocates the same number of keys on both sides, even after earlier cuts have
left gaps. Planning and ancestor construction then consume this exact collected output. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.KeyRenaming

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

-----------------------------------------------------------------------------------------
-- The current unused tail stays consecutive; previously used keys may have gaps
-----------------------------------------------------------------------------------------

/-- Fresh allocations beginning here correspond in order. No global affine-map premise
is imposed on earlier inherited keys, which may span several cancellation gaps. -/
def FreshTail (keys : Nat → Nat) (start : Nat) : Prop :=
  ∀ offset, keys (start + offset) = keys start + offset

theorem FreshTail.advance {keys : Nat → Nat} {start finish : Nat}
    (fresh : FreshTail keys start) (advanced : start ≤ finish)
    : FreshTail keys finish := by
  intro offset
  have first := fresh (finish - start)
  have later := fresh (finish - start + offset)
  have base : start + (finish - start) = finish := by omega
  have shifted : start + (finish - start + offset) = finish + offset := by omega
  rw [base] at first
  rw [shifted] at later
  omega

theorem FreshTail.insertGap (boundary gap : Nat)
    : FreshTail (insertGap boundary gap) boundary := by
  intro offset
  rw [insertGap_later (Nat.le_add_right _ _), insertGap_later (Nat.le_refl _)]
  omega

theorem FreshTail.extendAtCut {previous : Nat → Nat} {boundary gap : Nat}
    (fresh : FreshTail previous (boundary + gap))
    : FreshTail (extendAtCut previous boundary gap) boundary := by
  intro offset
  rw [extendAtCut_later previous (Nat.le_add_right _ _),
    extendAtCut_later previous (Nat.le_refl _)]
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using fresh offset

private theorem parent_ancestors (keys : Nat → Nat) (parent : Option DeferUsage)
    : ((parent.map (usage keys)).map (fun value => value.ref :: value.ancestors)).getD []
      = ((parent.map (fun value => value.ref :: value.ancestors)).getD []).map keys := by
  cases parent <;> rfl

-----------------------------------------------------------------------------------------
-- Construct the correspondence from actual collection, not related-output premises
-----------------------------------------------------------------------------------------

mutual
  theorem collectSelection_maps (keys : Nat → Nat) (schema : Schema)
      (variables : VariableValues) (parentType : Name) (source : ResolverValue ObjectRef)
      (selection : Selection) (parent : Option DeferUsage) (start : Nat)
      (fresh : FreshTail keys start)
      : (collectSelection schema variables parentType source (parent.map (usage keys))
          selection).run
          (keys start)
        = (
          collection keys
            ((collectSelection schema variables parentType source parent selection).run
              start).1,
          keys
            ((collectSelection schema variables parentType source parent selection).run
              start).2
        ) := by
    cases selection with
    | field name fieldName arguments directives children =>
        cases allowed : selectionDirectivesAllowBool variables directives <;>
          simp [collectSelection, allowed, collection, fields, field]
    | inlineFragment condition directives children =>
        cases allowed : selectionDirectivesAllowBool variables directives
        · simp [collectSelection, allowed, collection, fields]
        · cases applies : condition.all (doesFragmentTypeApplyBool schema parentType source)
          · simp [collectSelection, allowed, applies, collection, fields]
          · cases deferred : activeDefer? variables directives with
            | none =>
                simpa [collectSelection, allowed, applies, deferred]
                  using collectFields_maps keys schema variables parentType source
                    children parent start fresh
            | some label =>
                let allocated : DeferUsage := {
                  ref := start, label := label,
                  ancestors := (parent.map (fun value => value.ref :: value.ancestors)).getD [] }
                have nested := collectFields_maps keys schema variables parentType source
                  children (some allocated) (start + 1)
                  (fresh.advance (Nat.le_succ _))
                simp only [Option.map_some] at nested
                simp only [collectSelection, allowed, Bool.not_true, Bool.false_eq_true,
                  ↓reduceIte, applies, deferred, freshNodeRef, run_bind,
                  StateT.run_pure, id_pure_eq, StateT.run_get, StateT.run_set,
                  parent_ancestors]
                rw [← fresh 1]
                change ((do
                  let collected ← collectFields schema variables parentType source children
                    (some (usage keys allocated))
                  return { collected with newDeferUsages := usage keys allocated :: collected.newDeferUsages }).run (keys (start + 1)))
                  = _
                simp only [run_bind, StateT.run_pure, id_pure_eq, nested]
                rfl
  termination_by sizeOf selection

  theorem collectFields_maps (keys : Nat → Nat) (schema : Schema)
      (variables : VariableValues) (parentType : Name) (source : ResolverValue ObjectRef)
      (selections : List Selection) (parent : Option DeferUsage) (start : Nat)
      (fresh : FreshTail keys start)
      : (collectFields schema variables parentType source selections
          (parent.map (usage keys))).run
          (keys start)
        = (
          collection keys
            ((collectFields schema variables parentType source selections parent).run
              start).1,
          keys
            ((collectFields schema variables parentType source selections parent).run
              start).2
        ) := by
    cases selections with
    | nil => simp [collectFields, collection, fields]
    | cons head tail =>
        have first := collectSelection_maps keys schema variables parentType source head
          parent start fresh
        have advanced := (OwnerPaths.collectSelection_supply schema variables parentType
          source head parent start).1
        have later := collectFields_maps keys schema variables parentType source tail parent
          ((collectSelection schema variables parentType source parent head).run start).2
          (fresh.advance advanced)
        simp only [collectFields, run_bind, StateT.run_pure, id_pure_eq, first, later,
          append_collection]
  termination_by sizeOf selections
end

theorem collectSubfields_maps (keys : Nat → Nat) (schema : Schema)
    (variables : VariableValues) (parentType : Name) (source : ResolverValue ObjectRef)
    (original : List FieldDetails) (start : Nat) (fresh : FreshTail keys start)
    : (collectSubfields schema variables parentType source
        (original.map (field keys))).run
        (keys start)
      = (
        collection keys
          ((collectSubfields schema variables parentType source original).run start).1,
        keys ((collectSubfields schema variables parentType source original).run start).2
      ) := by
  induction original generalizing start with
  | nil => simp [collectSubfields, collection, fields]
  | cons head tail ih =>
      have first := collectFields_maps keys schema variables parentType source
        head.selectionSet head.deferUsage start fresh
      have advanced := (OwnerPaths.collectFields_supply schema variables parentType source
        head.selectionSet head.deferUsage start).1
      have later := ih _ (fresh.advance advanced)
      simp only [List.map_cons, collectSubfields, field, run_bind, StateT.run_pure,
        id_pure_eq, first, later, append_collection]

/-- The object boundary uses its actual original collection, plan and growing context.
The fresh-tail premise concerns only unused allocations, not the desired output relation. -/
def ObjectCollectionRenaming : Prop :=
  ∀ (ObjectRef : Type) (keys : Nat → Nat) (schema : Schema) variables parentType
    (source : ResolverValue ObjectRef) (original : List FieldDetails) start parent path
    context,
    Function.Injective keys
    → FreshTail keys start
    → let before :=
        (collectSubfields schema variables parentType source original).run start
      let after :=
        (collectSubfields schema variables parentType source
          (original.map (field keys))).run
          (keys start)
      after = (collection keys before.1, keys before.2)
      ∧ FreshTail keys before.2
      ∧ buildExecutionPlan after.1.collectedFieldsMap (parent.map keys)
        = plan keys (buildExecutionPlan before.1.collectedFieldsMap parent)
      ∧ getNewDeferMap after.1.newDeferUsages path (context.map (fragment keys))
        = (getNewDeferMap before.1.newDeferUsages path context).map (fragment keys)

theorem objectCollectionRenaming_holds : ObjectCollectionRenaming := by
  intro ObjectRef keys schema variables parentType source original start parent path context
    injective fresh
  have actual := collectSubfields_maps keys schema variables parentType source original start
    fresh
  refine ⟨actual, fresh.advance (OwnerPaths.collectSubfields_supply schema variables
    parentType source original start).1, ?_⟩
  simp only [actual, collection]
  exact ⟨build_plan injective _ _, new_defer_map injective _ _ _⟩

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.KeyRenaming
