import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Validity.SelectionSet

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

theorem normalizeOperation_valid_of_operationFieldsValid
    (schema : Schema) (operation : Operation)
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.operationDefinitionValid schema operation
      -> operationFieldsValidInPossibleTypes schema operation
      -> operationDirectiveFree operation
      -> selectionSetsTypeConditionFeasibleInEveryNormalizerScope schema
      -> normalizeSelectionSet schema operation.rootType operation.selectionSet ≠ []
      -> Validation.operationDefinitionValid schema
          (normalizeOperation schema operation) := by
  intro hschema hvalid himplementation hfree hfeasibleAll hnormalizedNonempty
  have hrootEq :
      operation.rootType = schema.queryType :=
    Validation.operationDefinitionValid_rootType_eq hvalid
  have hrootObject :
      schema.objectType operation.rootType := by
    simpa [hrootEq] using hschema.2.1
  have hselectionValid :
      Validation.selectionSetValid schema operation.variableDefinitions
        operation.rootType operation.selectionSet :=
    Validation.operationDefinitionValid_selectionSetValid hvalid
  have hready :
      selectionSetSemanticsReady schema operation.rootType
        operation.selectionSet :=
    selectionSetSemanticsReady_of_selectionSetValid_object schema
      operation.variableDefinitions operation.rootType hschema hrootObject
      operation.selectionSet hselectionValid
  have hmerge :
      FieldMerge.fieldsInSetCanMerge schema operation.rootType
        operation.selectionSet :=
    Validation.operationDefinitionValid_fieldsInSetCanMerge hvalid
  have hnormalizedSelectionSet :
      NormalizedSelectionSetValid schema operation.variableDefinitions
        operation.rootType
        (normalizeSelectionSet schema operation.rootType
          operation.selectionSet) :=
    normalizeSelectionSet_normalizedValid schema
      operation.variableDefinitions hschema hfeasibleAll operation.rootType
      operation.selectionSet hrootObject hready himplementation hmerge hfree
  exact ⟨
    hrootEq,
    (Validation.operationDefinitionValid_rootTypeComposite
      (operation := operation) hvalid),
    (Validation.operationDefinitionValid_variableDefinitionsValid
      (operation := operation) hvalid),
    by simpa [normalizeOperation] using hnormalizedNonempty,
    by simpa [normalizeOperation] using
      hnormalizedSelectionSet.selectionSetValid,
    by simpa [normalizeOperation] using
      hnormalizedSelectionSet.fieldsCanMerge⟩

theorem normalizeOperation_valid (schema : Schema) (operation : Operation)
    : NormalForm.normalizeOperationValid schema operation := by
  intro hschema hvalid hfree himplementation hfeasible
  rcases hfeasible with ⟨hrootContains, hrootFeasible⟩
  have hrootEq :
      operation.rootType = schema.queryType :=
    Validation.operationDefinitionValid_rootType_eq hvalid
  have hrootObject :
      schema.objectType operation.rootType := by
    simpa [hrootEq] using hschema.2.1
  have hselectionValid :
      Validation.selectionSetValid schema operation.variableDefinitions
        operation.rootType operation.selectionSet :=
    Validation.operationDefinitionValid_selectionSetValid hvalid
  have hready :
      selectionSetSemanticsReady schema operation.rootType
        operation.selectionSet :=
    selectionSetSemanticsReady_of_selectionSetValid_object schema
      operation.variableDefinitions operation.rootType hschema hrootObject
      operation.selectionSet hselectionValid
  have hmerge :
      FieldMerge.fieldsInSetCanMerge schema operation.rootType
        operation.selectionSet :=
    Validation.operationDefinitionValid_fieldsInSetCanMerge hvalid
  have hrootStack :
      objectSatisfiesTypeConditionStack schema operation.rootType
        [operation.rootType] :=
    objectSatisfiesTypeConditionStack_singleton_of_object_forValidity
      schema hrootObject
  have hnormalizedNonempty :
      normalizeSelectionSet schema operation.rootType operation.selectionSet ≠ [] :=
    normalizeSelectionSet_ne_nil_of_contains schema operation.rootType
      operation.selectionSet hrootObject hready
      (selectionSetContainsTypeConditionFeasibleField_of_existsMode
        schema operation.rootType [operation.rootType]
        operation.selectionSet hrootContains)
  have hnormalizedSelectionSet :
      NormalizedSelectionSetValid schema operation.variableDefinitions
        operation.rootType
        (normalizeSelectionSet schema operation.rootType
          operation.selectionSet) :=
    normalizeSelectionSet_normalizedValid_of_typeConditionFeasible schema
      operation.variableDefinitions hschema operation.rootType
      operation.selectionSet [operation.rootType] hrootObject hrootStack
      hready himplementation hmerge hfree hrootFeasible
  exact ⟨
    hrootEq,
    (Validation.operationDefinitionValid_rootTypeComposite
      (operation := operation) hvalid),
    (Validation.operationDefinitionValid_variableDefinitionsValid
      (operation := operation) hvalid),
    by simpa [normalizeOperation] using hnormalizedNonempty,
    by simpa [normalizeOperation] using
      hnormalizedSelectionSet.selectionSetValid,
    by simpa [normalizeOperation] using
      hnormalizedSelectionSet.fieldsCanMerge⟩

end GroundTypeNormalization

end NormalForm

end GraphQL
