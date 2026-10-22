import Tests.GraphQL.Validation.FieldMerge
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.OperationSemantics
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.OperationSemantics
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.FieldProjection
import Proofs.GraphQL.Algorithms.Common.SyntaxEq

namespace GraphQL.Tests.NormalForm.RuntimeMergeSource

open GraphQL.NormalForm
open GraphQL.Tests.Validation.FieldMerge

theorem declaredReturnScope_runtimeSource
    : runtimeMergeSource returnScopeSchema "Query" returnScopeQuery.selectionSet := by
  apply runtimeMergeSource_of_valid returnScopeSchema [] (parentType := "Query")
  · exact ⟨{ name := "Query", fields := [{ name := "user", outputType := .named "User" }] }, rfl⟩
  · decide
  · exact GraphQL.Validation.operationDefinitionValid_selectionSetValid returnScopeQuery_valid
  · exact returnScopeQuery_canMerge

theorem declaredReturnScope_normalizationSnapshot
    : normalizeSelectionSet returnScopeSchema "Query" returnScopeQuery.selectionSet
      = [.field "user" "user" [] [] directName] := by
  exact Algorithms.selectionSetEqBool_eq (by native_decide)

theorem declaredReturnScope_normalizedCanMerge
    (hschema : SchemaWellFormedness.schemaWellFormed returnScopeSchema)
    (hshapes : operationFieldsSameOutputShape returnScopeSchema returnScopeQuery)
    : FieldMerge.fieldsInSetCanMerge returnScopeSchema "Query"
        (normalizeSelectionSet returnScopeSchema "Query"
          returnScopeQuery.selectionSet) := by
  have hobject : returnScopeSchema.objectType "Query" :=
    ⟨{ name := "Query", fields := [{ name := "user", outputType := .named "User" }] }, rfl⟩
  apply GroundTypeNormalization.normalizeSelectionSet_fieldsInSetCanMerge
    returnScopeSchema hschema hshapes hobject
  · simp [returnScopeQuery, directName, fragmentName, selectionSetDirectiveFree,
      selectionDirectiveFree]
  · exact selectionSetSemanticsReady_of_selectionSetValid_object returnScopeSchema [] "Query"
      hschema hobject returnScopeQuery.selectionSet
      (GraphQL.Validation.operationDefinitionValid_selectionSetValid returnScopeQuery_valid)
  · exact declaredReturnScope_runtimeSource

-- Both public semantics statements retain their existing assumptions. The
-- stronger runtime-source evidence is derived inside their proof witnesses.
theorem groundSemantics_contract (schema : Schema) (operation : Operation)
    : groundTypeNormalFormSemanticsPreservation schema operation :=
  GroundTypeNormalization.groundTypeNormalFormSemanticsPreservation schema operation

theorem completeSemantics_contract (schema : Schema) (operation : Operation)
    : completeNormalizationSemanticsPreserved schema operation :=
  CompleteNormalization.completeNormalizationSemanticsPreserved schema operation

private def skippedBody : List Selection :=
  [.field "user" "user" [] [] [.field "name" "name" [] [.skip (.boolean true)] []]]

private theorem skippedBody_declaredLookupReady
    : selectionSetDeclaredLookupReady returnScopeSchema "Query" skippedBody := by
  simp [skippedBody, returnScopeSchema, selectionSetDeclaredLookupReady,
    selectionDeclaredLookupReady, Schema.lookupField, Schema.lookupType, Schema.allTypes,
    Schema.builtinScalarDefinitions, TypeDefinition.name, TypeDefinition.fields?,
    BuiltinScalar.name, TypeRef.namedType]

theorem filteredCompositeBody_empty
    : filterSelectionSetBoolCase [] skippedBody = [.field "user" "user" [] [] []] := by
  simp [skippedBody, filterSelectionSetBoolCase, directivesAllowIn, directiveAllowsIn,
    inputValueBoolIn?, InputValue.staticBoolean?]

theorem filteredCompositeBody_lookupReady
    : selectionSetDeclaredLookupReady returnScopeSchema "Query"
        (filterSelectionSetBoolCase [] skippedBody) :=
  CompleteNormalization.selectionSetDeclaredLookupReady_filter returnScopeSchema []
    "Query" skippedBody skippedBody_declaredLookupReady

end GraphQL.Tests.NormalForm.RuntimeMergeSource
