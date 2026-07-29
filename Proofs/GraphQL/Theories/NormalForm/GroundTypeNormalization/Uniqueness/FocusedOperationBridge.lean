import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.FocusedTrace
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.OperationBridge

/-!
Operation-level bridge for the focused-trace uniqueness route.

This module keeps the focused trace dependency downstream of
`OperationBridge`, avoiding an import cycle through the existing probe modules.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

theorem
    normal_operations_semanticallyEquivalent_equalUpToReordering_of_valid_object_diff_trace_data_separates
    {schema : Schema} {left right : Operation}
    : (SchemaWellFormedness.schemaWellFormed schema
        -> Validation.selectionSetValid schema left.variableDefinitions
            (left.rootType schema) left.selectionSet
        -> Validation.selectionSetValid schema right.variableDefinitions
            (left.rootType schema) right.selectionSet
        -> selectionSetDirectiveFree left.selectionSet
        -> selectionSetDirectiveFree right.selectionSet
        -> selectionSetNormal schema (left.rootType schema) left.selectionSet
        -> selectionSetNormal schema (left.rootType schema) right.selectionSet
        -> objectTypeNameBool schema (left.rootType schema) = true
        -> ∀ responsePath,
            NormalSelectionSetDiffTrace schema (left.rootType schema) left.selectionSet
              right.selectionSet responsePath
            -> ¬ selectionSetsDataEquivalent schema (left.rootType schema)
                  left.selectionSet right.selectionSet)
      -> normalOperationsSemanticallyEquivalentEqualUpToReordering schema left right := by
  intro htraceSeparates
  exact
    normal_operations_semanticallyEquivalent_equalUpToReordering_of_valid_object_diff_data_separates
      (schema := schema) (left := left) (right := right)
      (by
        intro hschema hleftValid hrightValid hleftFree hrightFree
          hleftNormal hrightNormal hobject hdiff
        rcases
            normalSelectionSetDiffTrace_of_valid_normal_diff hleftValid
              hrightValid hleftNormal hrightNormal hdiff with
          ⟨responsePath, htrace⟩
        exact
          htraceSeparates hschema hleftValid hrightValid hleftFree
            hrightFree hleftNormal hrightNormal hobject responsePath
            htrace)

theorem
    normal_operations_semanticallyEquivalent_equalUpToReordering_of_valid_object_diff_observable_trace_data_separates
    {schema : Schema} {left right : Operation}
    : (SchemaWellFormedness.schemaWellFormed schema
        -> Validation.selectionSetValid schema left.variableDefinitions
            (left.rootType schema) left.selectionSet
        -> Validation.selectionSetValid schema right.variableDefinitions
            (left.rootType schema) right.selectionSet
        -> selectionSetDirectiveFree left.selectionSet
        -> selectionSetDirectiveFree right.selectionSet
        -> selectionSetNormal schema (left.rootType schema) left.selectionSet
        -> selectionSetNormal schema (left.rootType schema) right.selectionSet
        -> objectTypeNameBool schema (left.rootType schema) = true
        -> ∀ responsePath,
            NormalSelectionSetDiffObservableTrace schema (left.rootType schema)
              left.selectionSet right.selectionSet responsePath
            -> ¬ selectionSetsDataEquivalent schema (left.rootType schema)
                  left.selectionSet right.selectionSet)
      -> normalOperationsSemanticallyEquivalentEqualUpToReordering schema left right := by
  intro htraceSeparates
  exact
    normal_operations_semanticallyEquivalent_equalUpToReordering_of_valid_object_diff_data_separates
      (schema := schema) (left := left) (right := right)
      (by
        intro hschema hleftValid hrightValid hleftFree hrightFree
          hleftNormal hrightNormal hobject hdiff
        rcases
            normalSelectionSetDiffObservableTrace_of_valid_normal_diff
              hleftValid hrightValid hleftNormal hrightNormal hdiff with
          ⟨responsePath, htrace⟩
        exact
          htraceSeparates hschema hleftValid hrightValid hleftFree
            hrightFree hleftNormal hrightNormal hobject responsePath
            htrace)

end GroundTypeNormalization

end NormalForm

end GraphQL
