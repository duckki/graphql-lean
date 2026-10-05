import Proofs.GraphQL.IncrementalDelivery.Semantics.Planning

/-! Propagate the client-coverage argument premise into collected execution fields. -/

namespace GraphQL.IncrementalDelivery.Correctness.ArgumentValidity
open GraphQL.IncrementalDelivery.Execution
open Semantics

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

-----------------------------------------------------------------------------------------
-- The modeled stream-argument error is excluded
-----------------------------------------------------------------------------------------

/-- Valid directive arguments exclude the stream hook's argument-error outcome.
Witness: directive-list induction; disabled streams return none and enabled streams have
a resolved count. This does not assume that item or resolver completion succeeds.
-/
theorem getStreamUsage_ok (variables : VariableValues)
    (directives : List DirectiveApplication)
    (valid
      : directives.all (DirectiveApplication.hasValidIncrementalArguments variables)
        = true)
    : ∃ usage, getStreamUsage variables directives = .ok usage := by
  induction directives with
  | nil => exact ⟨none, rfl⟩
  | cons directive rest ih =>
      simp only [List.all_cons, Bool.and_eq_true] at valid
      cases directive with
      | skip _ => exact ih valid.2
      | «include» _ => exact ih valid.2
      | defer _ _ => exact ih valid.2
      | stream condition label count =>
          by_cases disabled : inputValueBoolean? variables condition == some false
          · exact ⟨none, by simp [getStreamUsage, disabled]⟩
          · have countValid : (streamInitialCount? variables count).isSome = true := by
              simpa [DirectiveApplication.hasValidIncrementalArguments, disabled]
                using valid.1
            cases countResolved : streamInitialCount? variables count with
            | none => simp [countResolved] at countValid
            | some value =>
                exact ⟨
                  some { label := directiveLabel? label, initialCount := value },
                  by simp [getStreamUsage, disabled, countResolved]
                ⟩

/-- Proof-only field invariant retains both its own arguments and nested selection checks.
The inherited defer usage does not affect this invariant.
-/
def FieldArgumentsValid (variables : VariableValues) (field : FieldDetails) : Prop :=
  field.directives.all (DirectiveApplication.hasValidIncrementalArguments variables)
    = true
  ∧ SelectionSet.hasValidIncrementalArguments variables field.selectionSet = true

/-- A collected field list's stream hook cannot produce an argument error.
Witness: the first field retains valid directives; an empty list has no stream usage.
-/
theorem fields_getStreamUsage_ok (variables : VariableValues) (fields : List FieldDetails)
    (valid : ∀ field ∈ fields, FieldArgumentsValid variables field)
    : ∃ usage,
        getStreamUsage variables (fields.head?.map FieldDetails.directives |>.getD [])
        = .ok usage := by
  cases fields with
  | nil => exact ⟨none, rfl⟩
  | cons field rest =>
      exact getStreamUsage_ok variables field.directives (valid field (by simp)).1

-----------------------------------------------------------------------------------------
-- Collection preserves the recursively checked syntax
-----------------------------------------------------------------------------------------

mutual
  /-- Selection collection preserves argument validity under any inherited defer usage.
  Witness: syntax induction; ignored selections collect nothing and active fragments
  retain the child invariant even when allocating a fresh node reference.
  -/
  theorem collectSelection_valid (schema : Schema) (variables : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectRef) (selection : Selection)
      (valid : selection.hasValidIncrementalArguments variables = true)
      (usage : Option DeferUsage) (state : NodeRef)
      : GroupsSatisfy (FieldArgumentsValid variables)
          ((collectSelection schema variables parentType source usage selection).run
            state).1.collectedFieldsMap := by
    cases selection with
    | field responseName fieldName arguments directives children =>
        simp only [Selection.hasValidIncrementalArguments, Bool.and_eq_true] at valid
        cases allowed : selectionDirectivesAllowBool variables directives <;>
          simp [collectSelection, allowed, GroupsSatisfy, FieldArgumentsValid, valid]
        simpa only [List.all_eq_true] using valid.1
    | inlineFragment condition directives children =>
        simp only [Selection.hasValidIncrementalArguments, Bool.and_eq_true] at valid
        cases allowed : selectionDirectivesAllowBool variables directives
        · simp [collectSelection, allowed, GroupsSatisfy]
        · cases applies : condition.all (doesFragmentTypeApplyBool schema parentType source)
          · simp [collectSelection, allowed, applies, GroupsSatisfy]
          · cases active : activeDefer? variables directives with
            | none =>
                simpa [collectSelection, allowed, applies, active]
                  using collectFields_valid schema variables parentType source children
                    valid.2 usage state
            | some label =>
                simpa [collectSelection, allowed, applies, active, freshNodeRef]
                  using collectFields_valid schema variables parentType source children
                    valid.2
                    (some
                      {
                        ref := state
                        label := label
                        ancestors :=
                          usage.map (fun parent => parent.ref :: parent.ancestors)
                          |>.getD []
                      })
                    (state + 1)
  termination_by sizeOf selection

  /-- Grouping selections preserves every collected field's argument and child checks.
  Witness: syntax induction and the existing property-preserving map merge theorem;
  the tail is checked at the head's actual final fresh-reference supply.
  -/
  theorem collectFields_valid (schema : Schema) (variables : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectRef) (selections : List Selection)
      (valid : SelectionSet.hasValidIncrementalArguments variables selections = true)
      (usage : Option DeferUsage) (state : NodeRef)
      : GroupsSatisfy (FieldArgumentsValid variables)
          ((collectFields schema variables parentType source selections usage).run
            state).1.collectedFieldsMap := by
    cases selections with
    | nil => simp [collectFields, GroupsSatisfy]
    | cons selection rest =>
        simp only [SelectionSet.hasValidIncrementalArguments, Bool.and_eq_true] at valid
        have head := collectSelection_valid schema variables parentType source selection
          valid.1 usage state
        have tail := collectFields_valid schema variables parentType source rest valid.2
          usage ((collectSelection schema variables parentType source usage selection).run
            state).2
        simpa [collectFields, FieldCollection.append]
          using groupsSatisfy_merge (FieldArgumentsValid variables) _ _ head tail
  termination_by sizeOf selections
end

/-- Object subcollection preserves argument validity from all contributing field details.
Witness: field-list induction, child selection collection, and map-merge preservation.
This includes fields contributed by different overlapping defer usages.
-/
theorem collectSubfields_valid (schema : Schema) (variables : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectRef) (fields : List FieldDetails)
    (valid : ∀ field ∈ fields, FieldArgumentsValid variables field) (state : NodeRef)
    : GroupsSatisfy (FieldArgumentsValid variables)
        ((collectSubfields schema variables parentType source fields).run
          state).1.collectedFieldsMap := by
  induction fields generalizing state with
  | nil => simp [collectSubfields, GroupsSatisfy]
  | cons field rest ih =>
      have head := collectFields_valid schema variables parentType source field.selectionSet
        (valid field (by simp)).2 field.deferUsage state
      have tail := ih (fun field member => valid field (by simp [member]))
        ((collectFields schema variables parentType source field.selectionSet
          field.deferUsage).run state).2
      simpa [collectSubfields, FieldCollection.append]
        using groupsSatisfy_merge (FieldArgumentsValid variables) _ _ head tail

-----------------------------------------------------------------------------------------
-- Execution planning and the public query input premise
-----------------------------------------------------------------------------------------

/-- Both immediate and deferred plan partitions retain the collected argument invariant.
Witness: the existing generic property-preserving execution-plan partition theorem.
No scheduling or response-correctness assumption is added.
-/
theorem buildExecutionPlan_valid (variables : VariableValues)
    (groups : CollectedFieldsMap) (parent : WorkQueueSemantics.NodeRefs)
    (valid : GroupsSatisfy (FieldArgumentsValid variables) groups)
    : GroupsSatisfy (FieldArgumentsValid variables)
        (buildExecutionPlan groups parent).collectedFieldsMap
      ∧ ∀ partition ∈ (buildExecutionPlan groups parent).newCollectedFieldsMaps,
          GroupsSatisfy (FieldArgumentsValid variables) partition.2 :=
  buildExecutionPlan_preserves_property _ groups parent valid

/-- The public argument premise initializes the collected-field invariant for a query.
Witness: unfold the prepared-variable check and apply collection preservation.
Defaults are materialized once, exactly as in root execution.
-/
theorem Operation.collectFields_valid (schema : Schema) (operation : Operation)
    (variables : VariableValues) (source : ResolverValue ObjectRef)
    (valid : operation.incrementalArgumentsValid variables) (state : NodeRef)
    : GroupsSatisfy (FieldArgumentsValid (coerceVariableValues operation variables))
        ((collectFields schema (coerceVariableValues operation variables)
            (operation.rootType schema) source operation.selectionSet).run
          state).1.collectedFieldsMap :=
  ArgumentValidity.collectFields_valid schema _ _ source _ valid none state

end GraphQL.IncrementalDelivery.Correctness.ArgumentValidity
