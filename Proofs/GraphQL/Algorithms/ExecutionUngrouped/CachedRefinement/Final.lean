import Proofs.GraphQL.Algorithms.ExecutionUngrouped.CachedRefinement.TreeSoundness

/-!
Final refinement and correctness witnesses for cached ungrouped execution.

Valid operations erase exactly to uncached ungrouped execution. The public
correctness witnesses then reuse the uncached preservation theorems.
-/

namespace GraphQL

namespace Algorithms
namespace ExecutionUngrouped

open GraphQL.Execution

theorem executeRootSelectionSet_eq_uncached_of_globalCacheSound
    {ObjectRef : Type} (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (fuel : Nat) (parentType : Name)
    (source : ResolverValue ObjectRef) (selectionSet : List Selection)
    (hcache : GlobalFieldPreviousCacheSound schema resolvers variableValues)
    : executeRootSelectionSet schema resolvers variableValues fuel parentType
        source selectionSet
      = ExecutionUngroupedUncached.executeRootSelectionSet schema resolvers
          variableValues fuel parentType source selectionSet :=
  executeRootSelectionSet_eq_uncached_of_outputVisitResult schema resolvers
    variableValues fuel parentType source selectionSet
    (visitSubfields_output_eq_uncached_of_globalCacheSound schema resolvers
      variableValues hcache fuel parentType source selectionSet
      (FieldCacheValue.object source []))

theorem executeQueryWithFuel_eq_uncached_of_globalCacheSound
    {ObjectRef : Type} (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (operation : Operation) (fuel : Nat)
    (source : ResolverValue ObjectRef)
    (hcache
      : GlobalFieldPreviousCacheSound schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues))
    : executeQueryWithFuel schema resolvers variableValues operation fuel source
      = ExecutionUngroupedUncached.executeQueryWithFuel schema resolvers
          variableValues operation fuel source :=
  executeQueryWithFuel_eq_uncached_of_outputVisitResult schema resolvers
    variableValues operation fuel source
    (visitSubfields_output_eq_uncached_of_globalCacheSound schema resolvers
      (GraphQL.Execution.coerceVariableValues operation variableValues) hcache fuel
      (operation.rootType schema) source operation.selectionSet
      (FieldCacheValue.object source []))

theorem executeQueryWithFuel_eq_uncached_of_valid
    {ObjectRef : Type} (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (operation : Operation) (fuel : Nat)
    (source : ResolverValue ObjectRef)
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.operationDefinitionValid schema operation
      -> executeQueryWithFuel schema resolvers variableValues operation fuel source
          = ExecutionUngroupedUncached.executeQueryWithFuel schema resolvers
              variableValues operation fuel source := by
  intro hschema hvalid
  unfold executeQueryWithFuel ExecutionUngroupedUncached.executeQueryWithFuel
  by_cases hroot : rootSourceAppliesBool schema operation source = true
  · cases source with
    | null => simp [rootSourceAppliesBool, runtimeObjectType?] at hroot
    | scalar value => simp [rootSourceAppliesBool, runtimeObjectType?] at hroot
    | list values => simp [rootSourceAppliesBool, runtimeObjectType?] at hroot
    | object runtimeType ref =>
        let coercedVariableValues :=
          GraphQL.Execution.coerceVariableValues operation variableValues
        have hrootObject : schema.objectType (operation.rootType schema) := by
          have hrootEq := Validation.operationDefinitionValid_rootType_eq hvalid
          rw [hrootEq]
          exact hschema.2.1
        have hparentRuntime :
            ExecutionUngroupedUncached.Eager.ScopedParentRuntimeApplies schema
              runtimeType (operation.rootType schema) :=
          ExecutionUngroupedUncached.Eager.ScopedParentRuntimeApplies.of_rootSourceAppliesBool
            schema operation runtimeType ref hroot
        have hready :
            NormalForm.selectionSetSemanticsReady schema (operation.rootType schema)
              operation.selectionSet :=
          NormalForm.selectionSetSemanticsReady_of_selectionSetValid_object schema
            operation.variableDefinitions (operation.rootType schema) hschema
            hrootObject operation.selectionSet
            (Validation.operationDefinitionValid_selectionSetValid hvalid)
        have hmerge :
            FieldMerge.fieldsInSetCanMerge schema (operation.rootType schema)
              operation.selectionSet :=
          Validation.operationDefinitionValid_fieldsInSetCanMerge hvalid
        have hargumentsNodup :
            Execution.selectionSetArgumentsNodup operation.selectionSet :=
          Execution.selectionSetArgumentsNodup_of_selectionSetValid
            (Validation.operationDefinitionValid_selectionSetValid hvalid)
        have hwithin :
            SelectionSetFieldsWithin schema coercedVariableValues
              (operation.rootType schema) (.object runtimeType ref)
              (ExecutionUngroupedUncached.Eager.collectedExecutableFields
                (GraphQL.Execution.collectFields schema coercedVariableValues
                  (operation.rootType schema) (.object runtimeType ref)
                  operation.selectionSet))
              operation.selectionSet :=
          selectionSetFieldsWithin_collectFields schema coercedVariableValues
            (operation.rootType schema) (.object runtimeType ref)
            operation.selectionSet
        have hinitial :
            OutputCacheTreeSoundForGroups schema resolvers coercedVariableValues fuel
              (.object runtimeType ref)
              (GraphQL.Execution.collectFields schema coercedVariableValues
                (operation.rootType schema) (.object runtimeType ref)
                operation.selectionSet)
              (.object (.object runtimeType ref) []) :=
          OutputCacheTreeSoundForGroups.empty_object schema resolvers
            coercedVariableValues fuel (.object runtimeType ref)
            (.object runtimeType ref)
            (GraphQL.Execution.collectFields schema coercedVariableValues
              (operation.rootType schema) (.object runtimeType ref)
              operation.selectionSet)
        have hvisit :=
          (visitSubfields_output_eq_uncached_and_treeSound_object schema resolvers
            coercedVariableValues fuel (operation.rootType schema) runtimeType ref
            operation.selectionSet operation.selectionSet [] hschema hrootObject
            hparentRuntime hready hmerge hargumentsNodup hwithin hinitial).1
        have hrootExecution :=
          executeRootSelectionSet_eq_uncached_of_outputVisitResult schema resolvers
            coercedVariableValues fuel (operation.rootType schema)
            (.object runtimeType ref) operation.selectionSet hvisit
        simp [hroot, coercedVariableValues, hrootExecution]
  · have hfalse : rootSourceAppliesBool schema operation source = false := by
      cases h : rootSourceAppliesBool schema operation source
      · rfl
      · contradiction
    simp [hfalse]

theorem ungroupedExecutionPreservesSpecExecution_of_executeQueryWithFuel_eq_uncached
    (schema : Schema) (operation : Operation)
    (hbridge
      : SchemaWellFormedness.schemaWellFormed schema
        -> Validation.operationDefinitionValid schema operation
        -> ∀ {ObjectRef : Type} (resolvers : Resolvers ObjectRef)
              variableValues fuel (source : ResolverValue ObjectRef),
            NormalForm.operationBoolVarsComplete operation
              (GraphQL.Execution.coerceVariableValues operation variableValues)
            -> executeQueryWithFuel schema resolvers variableValues operation fuel source
                = ExecutionUngroupedUncached.executeQueryWithFuel schema resolvers
                    variableValues operation fuel source)
    : ungroupedExecutionPreservesSpecExecution schema operation := by
  intro hschema hvalid ObjectRef resolvers variableValues fuel source
    hcomplete
  have huncached :=
    ExecutionUngroupedUncached.ungroupedExecutionPreservesSpecExecution_proof
      schema operation hschema hvalid resolvers variableValues fuel source
      hcomplete
  rw [hbridge hschema hvalid resolvers variableValues fuel source hcomplete]
  simpa [responseDataAndErrorPresenceEquivalent,
    ExecutionUngroupedUncached.responseDataAndErrorPresenceEquivalent] using
    huncached

theorem
    ungroupedExecutionEquivalentToCancelingSiblingsExecution_of_executeQueryWithFuel_eq_uncached
    (schema : Schema) (operation : Operation)
    (hbridge
      : SchemaWellFormedness.schemaWellFormed schema
        -> Validation.operationDefinitionValid schema operation
        -> ∀ {ObjectRef : Type} (resolvers : Resolvers ObjectRef)
              variableValues fuel (source : ResolverValue ObjectRef),
            NormalForm.operationBoolVarsComplete operation
              (GraphQL.Execution.coerceVariableValues operation variableValues)
            -> executeQueryWithFuel schema resolvers variableValues operation fuel source
                = ExecutionUngroupedUncached.executeQueryWithFuel schema resolvers
                    variableValues operation fuel source)
    : ungroupedExecutionEquivalentToCancelingSiblingsExecution schema operation := by
  intro hschema hvalid ObjectRef resolvers variableValues fuel source
    hcomplete
  have huncached :=
    ExecutionUngroupedUncached.ungroupedExecutionEquivalentToCancelingSiblingsExecution_proof
      schema operation hschema hvalid resolvers variableValues fuel source
      hcomplete
  rw [hbridge hschema hvalid resolvers variableValues fuel source hcomplete]
  simpa [responseDataAndErrorPresenceEquivalent,
    ExecutionUngroupedUncached.responseDataAndErrorPresenceEquivalent] using
    huncached

theorem ungroupedExecutionPreservesSpecExecution_proof
    (schema : Schema) (operation : Operation)
    : ungroupedExecutionPreservesSpecExecution schema operation :=
  ungroupedExecutionPreservesSpecExecution_of_executeQueryWithFuel_eq_uncached schema
    operation
    (by
      intro hschema hvalid ObjectRef resolvers variableValues fuel source
        _hcomplete
      exact
        executeQueryWithFuel_eq_uncached_of_valid schema resolvers variableValues
          operation fuel source hschema hvalid)

theorem ungroupedExecutionEquivalentToCancelingSiblingsExecution_proof
    (schema : Schema) (operation : Operation)
    : ungroupedExecutionEquivalentToCancelingSiblingsExecution schema operation :=
  ungroupedExecutionEquivalentToCancelingSiblingsExecution_of_executeQueryWithFuel_eq_uncached
    schema operation
    (by
      intro hschema hvalid ObjectRef resolvers variableValues fuel source
        _hcomplete
      exact
        executeQueryWithFuel_eq_uncached_of_valid schema resolvers variableValues
          operation fuel source hschema hvalid)

end ExecutionUngrouped
end Algorithms

end GraphQL
