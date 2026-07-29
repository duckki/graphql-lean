import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.Statements
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.SyntaxDiff
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Uniqueness.VariableIndependence

/-!
Operation-level wrappers for the selection-set uniqueness proof surface.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

theorem selectionSetsSemanticallyEquivalent_of_operationsSemanticallyEquivalent
    {schema : Schema} {left right : Operation}
    : left.rootType = right.rootType
      -> selectionSetDirectiveFree left.selectionSet
      -> selectionSetDirectiveFree right.selectionSet
      -> operationsSemanticallyEquivalent schema left right
      -> selectionSetsSemanticallyEquivalent schema left.rootType
          left.selectionSet right.selectionSet := by
  intro hroot hleftFree hrightFree hsem ObjectRef resolvers variableValues fuel
    source hsource
  rcases hsource with ⟨runtimeType, _ref, hsourceEq, hinclude⟩
  have hleftRoot :
      Execution.rootSourceAppliesBool schema left source = true := by
    simp [Execution.rootSourceAppliesBool, Execution.runtimeObjectType?,
      hsourceEq, hinclude]
  have hrightInclude :
      schema.typeIncludesObjectBool right.rootType runtimeType = true := by
    simpa [← hroot] using hinclude
  have hrightRoot :
      Execution.rootSourceAppliesBool schema right source = true := by
    simp [Execution.rootSourceAppliesBool, Execution.runtimeObjectType?,
      hsourceEq, hrightInclude]
  have heffective :
      Execution.Response.semanticEquivalent
        (Execution.executeSelectionSetAsResponse schema resolvers
          (Execution.coerceVariableValues left variableValues) fuel
          left.rootType source left.selectionSet)
        (Execution.executeSelectionSetAsResponse schema resolvers
          (Execution.coerceVariableValues right variableValues) fuel
          left.rootType source right.selectionSet) := by
    simpa [Execution.executeQueryWithFuel, hleftRoot, hrightRoot,
      Execution.executeSelectionSetAsResponse,
      Execution.selectionSetResultToResponse, Execution.executeSelectionSet,
      hroot] using
        hsem resolvers variableValues fuel source
  have hleftValues :=
    CompleteNormalization.executeSelectionSet_eq_of_directiveFree_variableValues
      schema resolvers variableValues
      (Execution.coerceVariableValues left variableValues) fuel left.rootType
      source left.selectionSet hleftFree
  have hrightValues :=
    CompleteNormalization.executeSelectionSet_eq_of_directiveFree_variableValues
      schema resolvers variableValues
      (Execution.coerceVariableValues right variableValues) fuel left.rootType
      source right.selectionSet hrightFree
  simpa [Execution.executeSelectionSetAsResponse, hleftValues, hrightValues] using
    heffective

theorem selectionSetsDataEquivalent_of_operationsSemanticallyEquivalent
    {schema : Schema} {left right : Operation}
    : left.rootType = right.rootType
      -> selectionSetDirectiveFree left.selectionSet
      -> selectionSetDirectiveFree right.selectionSet
      -> operationsSemanticallyEquivalent schema left right
      -> selectionSetsDataEquivalent schema left.rootType
          left.selectionSet right.selectionSet := by
  intro hroot hleftFree hrightFree hsem
  exact selectionSetsDataEquivalent_of_selectionSetsSemanticallyEquivalent
    (selectionSetsSemanticallyEquivalent_of_operationsSemanticallyEquivalent
      hroot hleftFree hrightFree hsem)

theorem operation_rootType_eq_of_operationDefinitionValid
    {schema : Schema} {left right : Operation}
    : Validation.operationDefinitionValid schema left
      -> Validation.operationDefinitionValid schema right
      -> left.rootType = right.rootType := by
  intro hleft hright
  rw [Validation.operationDefinitionValid_rootType_eq hleft,
    Validation.operationDefinitionValid_rootType_eq hright]

theorem operation_root_objectTypeNameBool_of_wf_valid
    {schema : Schema} {operation : Operation}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.operationDefinitionValid schema operation
      -> objectTypeNameBool schema operation.rootType = true := by
  intro hschema hvalid
  have hroot : operation.rootType = schema.queryType :=
    Validation.operationDefinitionValid_rootType_eq hvalid
  have hrootObject : schema.objectType operation.rootType := by
    simpa [hroot] using hschema.2.1
  exact objectTypeNameBool_eq_true_of_objectType_forNormality schema
    hrootObject

theorem operationsEqualUpToReordering_of_selectionSet
    {schema : Schema} {left right : Operation}
    : Validation.operationDefinitionValid schema left
      -> Validation.operationDefinitionValid schema right
      -> SelectionSetEqualUpToReordering left.selectionSet right.selectionSet
      -> operationsEqualUpToReordering left right := by
  intro hleft hright hselectionSet
  exact
    ⟨operation_rootType_eq_of_operationDefinitionValid hleft hright,
      hselectionSet⟩

theorem normal_operations_semanticallyEquivalent_equalUpToReordering_of_selectionSet
    {schema : Schema} {left right : Operation}
    : normalSelectionSetsSemanticallyEquivalentEqualUpToReordering schema
        left.rootType left.selectionSet right.selectionSet
      -> normalOperationsSemanticallyEquivalentEqualUpToReordering schema left right := by
  intro hselection hschema hleftValid hrightValid hleftFree hrightFree
    hleftNormal hrightNormal hsem
  have hroot :
      left.rootType = right.rootType :=
    operation_rootType_eq_of_operationDefinitionValid hleftValid hrightValid
  have hrightSelectionNormal :
      selectionSetNormal schema left.rootType right.selectionSet := by
    simpa [operationNormal, hroot] using hrightNormal
  have hselectionSem :
      selectionSetsSemanticallyEquivalent schema left.rootType
        left.selectionSet right.selectionSet :=
    selectionSetsSemanticallyEquivalent_of_operationsSemanticallyEquivalent
      hroot hleftFree hrightFree hsem
  have hselectionSet :
      SelectionSetEqualUpToReordering left.selectionSet
        right.selectionSet :=
    hselection hschema hleftFree hrightFree hleftNormal
      hrightSelectionNormal hselectionSem
  exact operationsEqualUpToReordering_of_selectionSet hleftValid hrightValid
    hselectionSet

theorem normal_operations_semanticallyEquivalent_equalUpToReordering_of_valid_selectionSet
    {schema : Schema} {left right : Operation}
    : validNormalSelectionSetsSemanticallyEquivalentEqualUpToReordering schema
        left.variableDefinitions right.variableDefinitions left.rootType
        left.selectionSet right.selectionSet
      -> normalOperationsSemanticallyEquivalentEqualUpToReordering schema left right := by
  intro hselection hschema hleftValid hrightValid hleftFree hrightFree
    hleftNormal hrightNormal hsem
  have hroot :
      left.rootType = right.rootType :=
    operation_rootType_eq_of_operationDefinitionValid hleftValid hrightValid
  have hrightSelectionValid :
      Validation.selectionSetValid schema right.variableDefinitions
        left.rootType right.selectionSet := by
    simpa [hroot] using
      Validation.operationDefinitionValid_selectionSetValid hrightValid
  have hrightSelectionNormal :
      selectionSetNormal schema left.rootType right.selectionSet := by
    simpa [operationNormal, hroot] using hrightNormal
  have hselectionSem :
      selectionSetsSemanticallyEquivalent schema left.rootType
        left.selectionSet right.selectionSet :=
    selectionSetsSemanticallyEquivalent_of_operationsSemanticallyEquivalent
      hroot hleftFree hrightFree hsem
  have hselectionSet :
      SelectionSetEqualUpToReordering left.selectionSet
        right.selectionSet :=
    hselection hschema
      (Validation.operationDefinitionValid_selectionSetValid hleftValid)
      hrightSelectionValid hleftFree hrightFree hleftNormal
      hrightSelectionNormal hselectionSem
  exact operationsEqualUpToReordering_of_selectionSet hleftValid hrightValid
    hselectionSet

theorem normal_operations_semanticallyEquivalent_equalUpToReordering_of_valid_object_diff_data_separates
    {schema : Schema} {left right : Operation}
    : (SchemaWellFormedness.schemaWellFormed schema
        -> Validation.selectionSetValid schema left.variableDefinitions left.rootType
            left.selectionSet
        -> Validation.selectionSetValid schema right.variableDefinitions left.rootType
            right.selectionSet
        -> selectionSetDirectiveFree left.selectionSet
        -> selectionSetDirectiveFree right.selectionSet
        -> selectionSetNormal schema left.rootType left.selectionSet
        -> selectionSetNormal schema left.rootType right.selectionSet
        -> objectTypeNameBool schema left.rootType = true
        -> NormalSelectionSetDiff schema left.rootType left.selectionSet
            right.selectionSet
        -> ¬ selectionSetsDataEquivalent schema left.rootType left.selectionSet
              right.selectionSet)
      -> normalOperationsSemanticallyEquivalentEqualUpToReordering schema left right := by
  intro hdiffSeparates hschema hleftValid hrightValid hleftFree hrightFree
    hleftNormal hrightNormal hsem
  have hroot :
      left.rootType = right.rootType :=
    operation_rootType_eq_of_operationDefinitionValid hleftValid hrightValid
  have hrightSelectionValid :
      Validation.selectionSetValid schema right.variableDefinitions
        left.rootType right.selectionSet := by
    simpa [hroot] using
      Validation.operationDefinitionValid_selectionSetValid hrightValid
  have hrightSelectionNormal :
      selectionSetNormal schema left.rootType right.selectionSet := by
    simpa [operationNormal, hroot] using hrightNormal
  have hobject :
      objectTypeNameBool schema left.rootType = true :=
    operation_root_objectTypeNameBool_of_wf_valid hschema hleftValid
  by_cases hequal :
      SelectionSetEqualUpToReordering left.selectionSet right.selectionSet
  · exact operationsEqualUpToReordering_of_selectionSet hleftValid hrightValid
      hequal
  · have hdiff :
        NormalSelectionSetDiff schema left.rootType left.selectionSet
          right.selectionSet :=
      normalSelectionSetDiff_of_not_equalUpToReordering hleftFree hrightFree
        hleftNormal hrightSelectionNormal hequal
    have hdata :
        selectionSetsDataEquivalent schema left.rootType left.selectionSet
          right.selectionSet :=
      selectionSetsDataEquivalent_of_operationsSemanticallyEquivalent
        hroot hleftFree hrightFree hsem
    exact False.elim
      ((hdiffSeparates hschema
        (Validation.operationDefinitionValid_selectionSetValid hleftValid)
        hrightSelectionValid hleftFree hrightFree hleftNormal
        hrightSelectionNormal hobject hdiff) hdata)

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

theorem normalSelectionSetsSemanticallyEquivalent_equalUpToReordering_of_diff_data_separates
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

theorem feasibleNormalSelectionSetsSemanticallyEquivalent_equalUpToReordering_of_diff_separates
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

theorem feasibleNormalSelectionSetsSemanticallyEquivalent_equalUpToReordering_of_diff_data_separates
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

theorem validNormalSelectionSetsSemanticallyEquivalent_equalUpToReordering_of_diff_separates
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

theorem validNormalSelectionSetsSemanticallyEquivalent_equalUpToReordering_of_diff_data_separates
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
