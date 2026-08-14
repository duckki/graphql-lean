import Proofs.GraphQL.Execution.ArgumentCoercion
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.Statements
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.SyntaxDiff
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Uniqueness.VariableIndependence

/-!
Operation-level wrappers for the selection-set uniqueness proof surface.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

theorem operation_rootType_eq_of_operationDefinitionValid
    {schema : Schema} {left right : Operation}
    : Validation.operationDefinitionValid schema left
      -> Validation.operationDefinitionValid schema right
      -> (left.rootType schema) = (right.rootType schema) := by
  intro hleft hright
  rw [Validation.operationDefinitionValid_rootType_eq hleft,
    Validation.operationDefinitionValid_rootType_eq hright]

theorem operation_root_objectTypeNameBool_of_wf_valid
    {schema : Schema} {operation : Operation}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.operationDefinitionValid schema operation
      -> objectTypeNameBool schema (operation.rootType schema) = true := by
  intro hschema hvalid
  have hroot : (operation.rootType schema) = schema.queryType :=
    Validation.operationDefinitionValid_rootType_eq hvalid
  have hrootObject : schema.objectType (operation.rootType schema) := by
    simpa [hroot] using hschema.2.1
  exact objectTypeNameBool_eq_true_of_objectType_forNormality schema
    hrootObject

theorem normalSelectionSetsSemanticallyEquivalent_equalUpToReordering_of_diff_separates
    {schema : Schema} {parentType : Name} {left right : List Selection}
    : (NormalSelectionSetDiff schema parentType left right
        -> ¬ selectionSetsSemanticallyEquivalent schema parentType left right)
      -> normalSelectionSetsSemanticallyEquivalentEqualUpToReordering schema
          parentType left right := by
  intro hdiffSeparates _hschema hleftFree hrightFree hleftNormal
    hrightNormal hsem
  by_cases hequal : SelectionSetEqualUpToReordering left right
  · exact hequal
  · have hdiff :
        NormalSelectionSetDiff schema parentType left right :=
      normalSelectionSetDiff_of_not_equalUpToReordering hleftFree hrightFree
        hleftNormal hrightNormal hequal
    exact False.elim ((hdiffSeparates hdiff) hsem)

theorem
    normalSelectionSetsSemanticallyEquivalent_equalUpToReordering_of_diff_data_separates
    {schema : Schema} {parentType : Name} {left right : List Selection}
    : (NormalSelectionSetDiff schema parentType left right
        -> ¬ selectionSetsDataEquivalent schema parentType left right)
      -> normalSelectionSetsSemanticallyEquivalentEqualUpToReordering schema
          parentType left right := by
  intro hdiffSeparates _hschema hleftFree hrightFree hleftNormal
    hrightNormal hsem
  by_cases hequal : SelectionSetEqualUpToReordering left right
  · exact hequal
  · have hdiff :
        NormalSelectionSetDiff schema parentType left right :=
      normalSelectionSetDiff_of_not_equalUpToReordering hleftFree hrightFree
        hleftNormal hrightNormal hequal
    exact False.elim
      ((hdiffSeparates hdiff)
        (selectionSetsDataEquivalent_of_selectionSetsSemanticallyEquivalent
          hsem))

theorem
    feasibleNormalSelectionSetsSemanticallyEquivalent_equalUpToReordering_of_diff_separates
    {schema : Schema} {parentType : Name} {left right : List Selection}
    : (selectionSetFeasibleInScope schema parentType left
        -> selectionSetFeasibleInScope schema parentType right
        -> NormalSelectionSetDiff schema parentType left right
        -> ¬ selectionSetsSemanticallyEquivalent schema parentType left right)
      -> feasibleNormalSelectionSetsSemanticallyEquivalentEqualUpToReordering
          schema parentType left right := by
  intro hdiffSeparates _hschema hleftFree hrightFree hleftNormal
    hrightNormal hleftFeasible hrightFeasible hsem
  by_cases hequal : SelectionSetEqualUpToReordering left right
  · exact hequal
  · have hdiff :
        NormalSelectionSetDiff schema parentType left right :=
      normalSelectionSetDiff_of_not_equalUpToReordering hleftFree hrightFree
        hleftNormal hrightNormal hequal
    exact False.elim
      ((hdiffSeparates hleftFeasible hrightFeasible hdiff) hsem)

theorem
    feasibleNormalSelectionSetsSemanticallyEquivalent_equalUpToReordering_of_diff_data_separates
    {schema : Schema} {parentType : Name} {left right : List Selection}
    : (selectionSetFeasibleInScope schema parentType left
        -> selectionSetFeasibleInScope schema parentType right
        -> NormalSelectionSetDiff schema parentType left right
        -> ¬ selectionSetsDataEquivalent schema parentType left right)
      -> feasibleNormalSelectionSetsSemanticallyEquivalentEqualUpToReordering
          schema parentType left right := by
  intro hdiffSeparates _hschema hleftFree hrightFree hleftNormal
    hrightNormal hleftFeasible hrightFeasible hsem
  by_cases hequal : SelectionSetEqualUpToReordering left right
  · exact hequal
  · have hdiff :
        NormalSelectionSetDiff schema parentType left right :=
      normalSelectionSetDiff_of_not_equalUpToReordering hleftFree hrightFree
        hleftNormal hrightNormal hequal
    exact False.elim
      ((hdiffSeparates hleftFeasible hrightFeasible hdiff)
        (selectionSetsDataEquivalent_of_selectionSetsSemanticallyEquivalent
          hsem))

theorem
    validNormalSelectionSetsSemanticallyEquivalent_equalUpToReordering_of_diff_separates
    {schema : Schema}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    {parentType : Name} {left right : List Selection}
    : (SchemaWellFormedness.schemaWellFormed schema
        -> Validation.selectionSetValid schema leftVariableDefinitions parentType left
        -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
        -> selectionSetDirectiveFree left
        -> selectionSetDirectiveFree right
        -> selectionSetNormal schema parentType left
        -> selectionSetNormal schema parentType right
        -> NormalSelectionSetDiff schema parentType left right
        -> ¬ selectionSetsSemanticallyEquivalent schema parentType left right)
      -> validNormalSelectionSetsSemanticallyEquivalentEqualUpToReordering schema
          leftVariableDefinitions rightVariableDefinitions parentType left right := by
  intro hdiffSeparates hschema hleftValid hrightValid hleftFree hrightFree
    hleftNormal hrightNormal hsem
  by_cases hequal : SelectionSetEqualUpToReordering left right
  · exact hequal
  · have hdiff :
        NormalSelectionSetDiff schema parentType left right :=
      normalSelectionSetDiff_of_not_equalUpToReordering hleftFree hrightFree
        hleftNormal hrightNormal hequal
    exact False.elim
      ((hdiffSeparates hschema hleftValid hrightValid hleftFree hrightFree
        hleftNormal hrightNormal hdiff) hsem)

theorem
    validNormalSelectionSetsSemanticallyEquivalent_equalUpToReordering_of_diff_data_separates
    {schema : Schema}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    {parentType : Name} {left right : List Selection}
    : (SchemaWellFormedness.schemaWellFormed schema
        -> Validation.selectionSetValid schema leftVariableDefinitions parentType left
        -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
        -> selectionSetDirectiveFree left
        -> selectionSetDirectiveFree right
        -> selectionSetNormal schema parentType left
        -> selectionSetNormal schema parentType right
        -> NormalSelectionSetDiff schema parentType left right
        -> ¬ selectionSetsDataEquivalent schema parentType left right)
      -> validNormalSelectionSetsSemanticallyEquivalentEqualUpToReordering schema
          leftVariableDefinitions rightVariableDefinitions parentType left right := by
  intro hdiffSeparates hschema hleftValid hrightValid hleftFree hrightFree
    hleftNormal hrightNormal hsem
  by_cases hequal : SelectionSetEqualUpToReordering left right
  · exact hequal
  · have hdiff :
        NormalSelectionSetDiff schema parentType left right :=
      normalSelectionSetDiff_of_not_equalUpToReordering hleftFree hrightFree
        hleftNormal hrightNormal hequal
    exact False.elim
      ((hdiffSeparates hschema hleftValid hrightValid hleftFree hrightFree
        hleftNormal hrightNormal hdiff)
        (selectionSetsDataEquivalent_of_selectionSetsSemanticallyEquivalent
          hsem))

end GroundTypeNormalization

end NormalForm

end GraphQL
