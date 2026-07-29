import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Validity.Variables

/-! Operation-level validity preservation for ground-type normalization. -/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

theorem selectionSetInlineFragmentsNonempty_append {left right : List Selection}
    : selectionSetInlineFragmentsNonempty left
      -> selectionSetInlineFragmentsNonempty right
      -> selectionSetInlineFragmentsNonempty (left ++ right) := by
  intro hleft hright
  unfold selectionSetInlineFragmentsNonempty at hleft hright ⊢
  intro selection hselection
  rcases List.mem_append.mp hselection with hselection | hselection
  · exact hleft selection hselection
  · exact hright selection hselection

theorem selectionSetInlineFragmentsNonempty_tail
    {selection : Selection} {selectionSet : List Selection}
    : selectionSetInlineFragmentsNonempty (selection :: selectionSet)
      -> selectionSetInlineFragmentsNonempty selectionSet := by
  intro hnonempty
  unfold selectionSetInlineFragmentsNonempty at hnonempty ⊢
  intro candidate hcandidate
  exact hnonempty candidate (List.mem_cons_of_mem selection hcandidate)

theorem normalizeOperation_operationVariablesUsed
    (schema : Schema) (operation : Operation)
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.operationDefinitionValid schema operation
      -> operationDirectiveFree operation
      -> operationFieldsValidInPossibleTypes schema operation
      -> operationTypeConditionFeasible schema operation
      -> Validation.operationVariablesUsed (normalizeOperation schema operation) := by
  intro hschema hvalid hfree himplementation hfeasible
  have hrootEq :
      (operation.rootType schema) = schema.queryType :=
    Validation.operationDefinitionValid_rootType_eq hvalid
  have hrootObject :
      schema.objectType (operation.rootType schema) := by
    simpa [hrootEq] using hschema.2.1
  have hselectionValid :
      Validation.selectionSetValid schema operation.variableDefinitions
        (operation.rootType schema) operation.selectionSet :=
    Validation.operationDefinitionValid_selectionSetValid hvalid
  have hready :
      selectionSetSemanticsReady schema (operation.rootType schema)
        operation.selectionSet :=
    selectionSetSemanticsReady_of_selectionSetValid_object schema
      operation.variableDefinitions (operation.rootType schema) hschema hrootObject
      operation.selectionSet hselectionValid
  have hmerge :
      FieldMerge.fieldsInSetCanMerge schema (operation.rootType schema)
        operation.selectionSet :=
    Validation.operationDefinitionValid_fieldsInSetCanMerge hvalid
  have hrootStack :
      objectSatisfiesTypeConditionStack schema (operation.rootType schema)
        [(operation.rootType schema)] :=
    objectSatisfiesTypeConditionStack_singleton_of_object_forValidity
      schema hrootObject
  have hsourceVariablesUsed :
      Validation.operationVariablesUsed operation :=
    Validation.operationDefinitionValid_operationVariablesUsed hvalid
  intro variableDefinition hvariableDefinition
  have hsourceVariable :
      variableDefinition.name
        ∈ Validation.selectionSetVariables operation.selectionSet :=
    hsourceVariablesUsed variableDefinition (by
      simpa [normalizeOperation] using hvariableDefinition)
  change variableDefinition.name
    ∈ Validation.selectionSetVariables
        (normalizeSelectionSet schema (operation.rootType schema)
          operation.selectionSet)
  exact
    normalizeSelectionSet_variables_mem schema variableDefinition.name hschema
      (operation.rootType schema) operation.selectionSet
      [(operation.rootType schema)] hrootObject (by simp) hrootStack hready
      hmerge hfree hfeasible hsourceVariable

theorem normalizeOperation_valid_of_operationFieldsValid
    (schema : Schema) (operation : Operation)
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.operationDefinitionValid schema operation
      -> operationFieldsValidInPossibleTypes schema operation
      -> operationDirectiveFree operation
      -> selectionSetsTypeConditionFeasibleInEveryNormalizerScope schema
      -> normalizeSelectionSet schema (operation.rootType schema) operation.selectionSet
          ≠ []
      -> Validation.operationVariablesUsed (normalizeOperation schema operation)
      -> Validation.operationDefinitionValid schema
          (normalizeOperation schema operation) := by
  intro hschema hvalid himplementation hfree hfeasibleAll hnormalizedNonempty
    hvariablesUsed
  have hrootEq :
      (operation.rootType schema) = schema.queryType :=
    Validation.operationDefinitionValid_rootType_eq hvalid
  have hrootObject :
      schema.objectType (operation.rootType schema) := by
    simpa [hrootEq] using hschema.2.1
  have hselectionValid :
      Validation.selectionSetValid schema operation.variableDefinitions
        (operation.rootType schema) operation.selectionSet :=
    Validation.operationDefinitionValid_selectionSetValid hvalid
  have hready :
      selectionSetSemanticsReady schema (operation.rootType schema)
        operation.selectionSet :=
    selectionSetSemanticsReady_of_selectionSetValid_object schema
      operation.variableDefinitions (operation.rootType schema) hschema hrootObject
      operation.selectionSet hselectionValid
  have hmerge :
      FieldMerge.fieldsInSetCanMerge schema (operation.rootType schema)
        operation.selectionSet :=
    Validation.operationDefinitionValid_fieldsInSetCanMerge hvalid
  have hnormalizedSelectionSet :
      NormalizedSelectionSetValid schema operation.variableDefinitions
        (operation.rootType schema)
        (normalizeSelectionSet schema (operation.rootType schema)
          operation.selectionSet) :=
    normalizeSelectionSet_normalizedValid schema
      operation.variableDefinitions hschema hfeasibleAll (operation.rootType schema)
      operation.selectionSet hrootObject hready himplementation hmerge hfree
  exact ⟨
    by simp [normalizeOperation],
    by
      simpa [normalizeOperation, Operation.rootType, OperationType.rootType] using
        (Validation.operationDefinitionValid_rootTypeComposite
          (operation := operation) hvalid),
    (Validation.operationDefinitionValid_variableDefinitionsValid
      (operation := operation) hvalid),
    by simpa [normalizeOperation] using hnormalizedNonempty,
    by simpa [normalizeOperation, Operation.rootType, OperationType.rootType] using
      hnormalizedSelectionSet.selectionSetValid,
    by simpa [normalizeOperation, Operation.rootType, OperationType.rootType] using
      hnormalizedSelectionSet.fieldsCanMerge,
    hvariablesUsed⟩

theorem normalizeOperation_valid (schema : Schema) (operation : Operation)
    : NormalForm.normalizeOperationValid schema operation := by
  intro hschema hvalid hfree himplementation hfeasible
  have hrootEq :
      (operation.rootType schema) = schema.queryType :=
    Validation.operationDefinitionValid_rootType_eq hvalid
  have hrootObject :
      schema.objectType (operation.rootType schema) := by
    simpa [hrootEq] using hschema.2.1
  have hselectionValid :
      Validation.selectionSetValid schema operation.variableDefinitions
        (operation.rootType schema) operation.selectionSet :=
    Validation.operationDefinitionValid_selectionSetValid hvalid
  have hready :
      selectionSetSemanticsReady schema (operation.rootType schema)
        operation.selectionSet :=
    selectionSetSemanticsReady_of_selectionSetValid_object schema
      operation.variableDefinitions (operation.rootType schema) hschema hrootObject
      operation.selectionSet hselectionValid
  have hmerge :
      FieldMerge.fieldsInSetCanMerge schema (operation.rootType schema)
        operation.selectionSet :=
    Validation.operationDefinitionValid_fieldsInSetCanMerge hvalid
  have hrootContains :
      selectionSetContainsTypeConditionFeasibleField schema
        [(operation.rootType schema)] operation.selectionSet :=
    selectionSetContainsTypeConditionFeasibleField_of_feasible schema
      (operation.rootType schema) [(operation.rootType schema)] operation.selectionSet hfeasible
      (Validation.operationDefinitionValid_selectionSet_nonempty hvalid)
      (selectionSetInlineFragmentsNonempty_of_selectionSetValid schema
        operation.variableDefinitions (operation.rootType schema) operation.selectionSet
        hselectionValid)
  have hrootStack :
      objectSatisfiesTypeConditionStack schema (operation.rootType schema)
        [(operation.rootType schema)] :=
    objectSatisfiesTypeConditionStack_singleton_of_object_forValidity
      schema hrootObject
  have hnormalizedNonempty :
      normalizeSelectionSet schema (operation.rootType schema) operation.selectionSet ≠ [] :=
    normalizeSelectionSet_ne_nil_of_contains schema (operation.rootType schema)
      operation.selectionSet hrootObject hready
      hrootContains
  have hnormalizedSelectionSet :
      NormalizedSelectionSetValid schema operation.variableDefinitions
        (operation.rootType schema)
        (normalizeSelectionSet schema (operation.rootType schema)
          operation.selectionSet) :=
    normalizeSelectionSet_normalizedValid_of_typeConditionFeasible schema
      operation.variableDefinitions hschema (operation.rootType schema)
      operation.selectionSet [(operation.rootType schema)] hrootObject hrootStack
      hready himplementation hmerge hfree hfeasible
  have hvariablesUsed :
      Validation.operationVariablesUsed (normalizeOperation schema operation) :=
    normalizeOperation_operationVariablesUsed schema operation hschema hvalid
      hfree himplementation hfeasible
  exact ⟨
    by simp [normalizeOperation],
    by
      simpa [normalizeOperation, Operation.rootType, OperationType.rootType] using
        (Validation.operationDefinitionValid_rootTypeComposite
          (operation := operation) hvalid),
    (Validation.operationDefinitionValid_variableDefinitionsValid
      (operation := operation) hvalid),
    by simpa [normalizeOperation] using hnormalizedNonempty,
    by simpa [normalizeOperation, Operation.rootType, OperationType.rootType] using
      hnormalizedSelectionSet.selectionSetValid,
    by simpa [normalizeOperation, Operation.rootType, OperationType.rootType] using
      hnormalizedSelectionSet.fieldsCanMerge,
    hvariablesUsed⟩

end GroundTypeNormalization

end NormalForm

end GraphQL
