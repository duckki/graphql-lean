import GraphQL.Theories.QueryInclusion
import Proofs.GraphQL.Theories.QueryInclusion.Support.Theories.NormalForm.Shared.SemanticReadiness.Readiness
import Proofs.GraphQL.Theories.QueryInclusion.Support.Validation.SelectionValidity

/-! Supporting lemmas extracted from commit `7797374fd` for the talk exercises. -/

namespace GraphQL.NormalForm.CompleteNormalization

theorem operation_root_object_of_valid {schema : Schema} {operation : Operation}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.operationDefinitionValid schema operation
      -> schema.objectType (operation.rootType schema) := by
  intro hschema hoperation
  have hqueryObject := hschema.2.1
  have hrootEq :=
    Validation.operationDefinitionValid_rootType_eq hoperation
  rw [hrootEq]
  exact hqueryObject

theorem operation_selectionSetSemanticsReady_of_valid
    {schema : Schema} {operation : Operation}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.operationDefinitionValid schema operation
      -> selectionSetSemanticsReady schema (operation.rootType schema)
          operation.selectionSet := by
  intro hschema hoperation
  exact selectionSetSemanticsReady_of_selectionSetValid_object schema
    operation.variableDefinitions (operation.rootType schema) hschema
    (operation_root_object_of_valid hschema hoperation)
    operation.selectionSet
    (Validation.operationDefinitionValid_selectionSetValid hoperation)

end GraphQL.NormalForm.CompleteNormalization
