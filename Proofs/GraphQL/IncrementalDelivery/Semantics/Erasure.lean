import Proofs.GraphQL.IncrementalDelivery.Semantics.Collection

/-! Field collection commutes with erasure, including active incremental directives. -/

namespace GraphQL.IncrementalDelivery.Semantics

open GraphQL.IncrementalDelivery.Execution

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

variable {ObjectRef : Type}

theorem selectionDirectivesAllowBool_erase (variables : VariableValues)
    (directives : List DirectiveApplication)
    : selectionDirectivesAllowBool variables directives
      = GraphQL.Execution.selectionDirectivesAllowBool variables
          (directives.filterMap DirectiveApplication.eraseIncremental?) := by
  induction directives with
  | nil => rfl
  | cons directive rest ih =>
      cases directive <;>
        simp_all [selectionDirectivesAllowBool, GraphQL.Execution.selectionDirectivesAllowBool,
          DirectiveApplication.eraseIncremental?, directiveAllowsSelectionBool,
          GraphQL.Execution.directiveAllowsSelectionBool] <;> rfl

mutual
  theorem collectSelection_erase (schema : Schema) (variables : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectRef) (usage : Option DeferUsage)
      (selection : Selection) (state : Nat)
      : eraseGroups
          ((collectSelection schema variables parentType source usage selection).run
            state).1.fields
        = GraphQL.Execution.collectSelection schema variables parentType source
            selection.eraseIncrementalDirectives := by
    cases selection with
    | field responseName fieldName arguments directives children =>
        cases ha : selectionDirectivesAllowBool variables directives <;>
          simp [collectSelection, GraphQL.Execution.collectSelection,
            Selection.eraseIncrementalDirectives, ← selectionDirectivesAllowBool_erase, ha,
            eraseGroups, eraseGroup, eraseField]
    | inlineFragment condition directives children =>
        have hc (nextUsage : Option DeferUsage) (nextState : Nat) :=
          collectFields_erase schema variables parentType source children nextUsage nextState
        cases ha : selectionDirectivesAllowBool variables directives
        · cases condition <;>
            simp [collectSelection, GraphQL.Execution.collectSelection,
              Selection.eraseIncrementalDirectives, ← selectionDirectivesAllowBool_erase, ha,
              eraseGroups]
        · cases condition with
          | none =>
              cases hd : activeDefer? variables directives <;>
                simp [collectSelection, GraphQL.Execution.collectSelection,
                  Selection.eraseIncrementalDirectives, ← selectionDirectivesAllowBool_erase,
                  ha, hd, freshExecutionKey, hc]
          | some condition =>
              cases ht : doesFragmentTypeApplyBool schema parentType source condition <;>
                cases hd : activeDefer? variables directives <;>
                simp [collectSelection, GraphQL.Execution.collectSelection,
                  Selection.eraseIncrementalDirectives, ← selectionDirectivesAllowBool_erase,
                  ha, ht, hd, freshExecutionKey, hc] <;> rfl
  termination_by sizeOf selection

  theorem collectFields_erase (schema : Schema) (variables : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectRef) (selections : List Selection)
      (usage : Option DeferUsage) (state : Nat)
      : eraseGroups
          ((collectFields schema variables parentType source selections usage).run
            state).1.fields
        = GraphQL.Execution.collectFields schema variables parentType source
            (SelectionSet.eraseIncrementalDirectives selections) := by
    cases selections with
    | nil => rfl
    | cons selection rest =>
        simp only [collectFields, run_bind, StateT.run_pure, id_pure_eq,
          FieldCollection.append, SelectionSet.eraseIncrementalDirectives,
          GraphQL.Execution.collectFields]
        rw [eraseGroups_merge, collectSelection_erase, collectFields_erase]
  termination_by sizeOf selections
end

theorem collectSubfields_erase (schema : Schema) (variables : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectRef) (fields : List ExecutableField)
    (state : Nat)
    : eraseGroups
        ((collectSubfields schema variables parentType source fields).run state).1.fields
      = GraphQL.Execution.collectSubfields schema variables parentType source
          (fields.map eraseField) := by
  induction fields generalizing state with
  | nil => rfl
  | cons field rest ih =>
      simp only [collectSubfields, run_bind, StateT.run_pure, id_pure_eq,
        FieldCollection.append, List.map_cons, GraphQL.Execution.collectSubfields, eraseField]
      rw [eraseGroups_merge, collectFields_erase, ih]

end GraphQL.IncrementalDelivery.Semantics
