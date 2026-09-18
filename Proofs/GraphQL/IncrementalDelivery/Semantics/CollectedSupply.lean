import Proofs.GraphQL.IncrementalDelivery.Semantics.DeferKeys

/-! Allocation bounds independent of inherited usage validity. All new usages come from
the current fresh-key supply, even if the input usage is arbitrary proof context.
This weaker bound is sufficient to assign paths to new keys without aliasing old keys.
-/

namespace GraphQL.IncrementalDelivery.Semantics.OwnerPaths

open GraphQL.IncrementalDelivery.Execution

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

def SupplyBounds (start : Nat) (output : FieldCollection × Nat) : Prop :=
  start ≤ output.2
  ∧ ∀ usage ∈ output.1.newDeferUsages, start ≤ usage.key ∧ usage.key < output.2

theorem supplyBounds_append {start middle finish : Nat} {left right : FieldCollection}
    (hl : SupplyBounds start (left, middle)) (hr : SupplyBounds middle (right, finish))
    : SupplyBounds start (left.append right, finish) := by
  refine ⟨Nat.le_trans hl.1 hr.1, ?_⟩
  intro usage hu
  rcases List.mem_append.mp hu with hu | hu
  · have hh := hl.2 usage hu
    exact ⟨hh.1, Nat.lt_of_lt_of_le hh.2 hr.1⟩
  · have hh := hr.2 usage hu
    exact ⟨Nat.le_trans hl.1 hh.1, hh.2⟩

mutual
  theorem collectSelection_supply (schema : Schema) (variables : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectRef) (selection : Selection)
      (usage : Option DeferUsage) (state : Nat)
      : SupplyBounds state
          ((collectSelection schema variables parentType source usage selection).run
            state) := by
    cases selection with
    | field name fieldName arguments directives children =>
        cases ha : selectionDirectivesAllowBool variables directives <;>
          simp [collectSelection, ha, SupplyBounds]
    | inlineFragment condition directives children =>
        cases ha : selectionDirectivesAllowBool variables directives
        · simp [collectSelection, ha, SupplyBounds]
        · cases ht : condition.all (doesFragmentTypeApplyBool schema parentType source)
          · simp [collectSelection, ha, ht, SupplyBounds]
          · cases hd : activeDefer? variables directives with
            | none =>
                simpa [collectSelection, ha, ht, hd]
                  using collectFields_supply schema variables parentType source children
                    usage state
            | some label =>
                have hc := collectFields_supply schema variables parentType source children
                  (some {
                    key := state
                    label := label
                    ancestors := (usage.map (fun value => value.key :: value.ancestors)).getD [] }) (state + 1)
                simp only [collectSelection, ha, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                  ht, hd, freshExecutionKey, run_bind, StateT.run_pure, id_pure_eq,
                  StateT.run_get, StateT.run_set]
                refine ⟨by have := hc.1; omega, ?_⟩
                intro value hv
                rcases List.mem_cons.mp hv with rfl | hv
                · exact ⟨Nat.le_refl _, by have := hc.1; dsimp only; omega⟩
                · have hh := hc.2 value hv
                  exact ⟨by omega, hh.2⟩
  termination_by sizeOf selection

  theorem collectFields_supply (schema : Schema) (variables : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectRef) (selections : List Selection)
      (usage : Option DeferUsage) (state : Nat)
      : SupplyBounds state
          ((collectFields schema variables parentType source selections usage).run
            state) := by
    cases selections with
    | nil => simp [collectFields, SupplyBounds]
    | cons selection rest =>
        simp only [collectFields, run_bind, StateT.run_pure, id_pure_eq]
        exact supplyBounds_append
          (collectSelection_supply schema variables parentType source selection usage state)
          (collectFields_supply schema variables parentType source rest usage _)
  termination_by sizeOf selections
end

theorem collectSubfields_supply (schema : Schema) (variables : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectRef) (fields : List ExecutableField)
    (state : Nat)
    : SupplyBounds state
        ((collectSubfields schema variables parentType source fields).run state) := by
  induction fields generalizing state with
  | nil => simp [collectSubfields, SupplyBounds]
  | cons field rest ih =>
      simp only [collectSubfields, run_bind, StateT.run_pure, id_pure_eq]
      exact supplyBounds_append
        (collectFields_supply schema variables parentType source field.selectionSet field.deferUsage state)
        (ih _)

end GraphQL.IncrementalDelivery.Semantics.OwnerPaths
