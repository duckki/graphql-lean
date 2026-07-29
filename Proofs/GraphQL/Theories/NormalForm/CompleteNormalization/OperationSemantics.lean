import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.RootFilterSemantics
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.SelectionSetSemantics

/-! Operation-level semantic preservation for complete normalization. -/

namespace GraphQL

namespace NormalForm

namespace CompleteNormalization

theorem completeNormalizationSelectionSetSemanticsPreserved
    (schema : Schema) (operation : Operation)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hvalid : Validation.operationDefinitionValid schema operation)
    {ObjectRef : Type} (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues) (depth : Nat)
    (source : Execution.ResolverValue ObjectRef)
    (hcomplete : operationBoolVarsComplete operation variableValues)
    (hroot : Execution.rootSourceAppliesBool schema operation source = true)
    : Execution.executeSelectionSet schema resolvers variableValues depth
        operation.rootType source operation.selectionSet
      = Execution.executeSelectionSet schema resolvers variableValues depth
          operation.rootType source
          (completeNormalizeOperation schema operation).selectionSet := by
  rcases
    operationBoolVarsComplete_caseForVariableValues variableValues operation
      hcomplete with
    ⟨runtimeCase, hruntimeCase, hagrees⟩
  have hrootObject : schema.objectType operation.rootType := by
    have hrootEq := Validation.operationDefinitionValid_rootType_eq hvalid
    rw [hrootEq]
    exact hschema.2.1
  have hobject :
      objectTypeNameBool schema operation.rootType = true :=
    GroundTypeNormalization.objectTypeNameBool_eq_true_of_objectType schema
      hrootObject
  have hsource :
      ∃ runtimeType ref,
        source = Execution.ResolverValue.object runtimeType ref
          ∧ schema.typeIncludesObjectBool operation.rootType runtimeType =
            true :=
    GroundTypeNormalization.rootSourceAppliesBool_true_object schema
      operation source hroot
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
  have hfilteredFree :
      selectionSetDirectiveFree
        (filterSelectionSetBoolCase runtimeCase operation.selectionSet) :=
    filterSelectionSetBoolCase_directiveFree schema runtimeCase
      operation.selectionSet
  have hfilteredReady :
      selectionSetSemanticsReady schema operation.rootType
        (filterSelectionSetBoolCase runtimeCase operation.selectionSet) :=
    selectionSetSemanticsReady_filterSelectionSetBoolCase schema runtimeCase
      operation.rootType operation.selectionSet hready
  have hfilteredMerge :
      FieldMerge.fieldsInSetCanMerge schema operation.rootType
        (filterSelectionSetBoolCase runtimeCase operation.selectionSet) :=
    fieldsInSetCanMerge_filterSelectionSetBoolCase_forSemantics schema
      runtimeCase hmerge
  have hrootSelect :
      Execution.executeSelectionSet schema resolvers variableValues depth
          operation.rootType source
          (completeNormalizeOperation schema operation).selectionSet
        =
      Execution.executeSelectionSet schema resolvers variableValues depth
          operation.rootType source
          (normalizeSelectionSet schema operation.rootType
            (filterSelectionSetBoolCase runtimeCase
              operation.selectionSet)) := by
    simpa [completeNormalizeOperation] using
      executeSelectionSet_completeNormalizeRootSelectionSet_runtime
        schema resolvers variableValues operation depth operation.rootType
        source runtimeCase operation.selectionSet hruntimeCase hagrees
  have hground :
      Execution.executeSelectionSet schema resolvers variableValues depth
          operation.rootType source
          (normalizeSelectionSet schema operation.rootType
            (filterSelectionSetBoolCase runtimeCase operation.selectionSet))
        =
      Execution.executeSelectionSet schema resolvers variableValues depth
          operation.rootType source
          (filterSelectionSetBoolCase runtimeCase operation.selectionSet) :=
    GroundTypeNormalization.normalizeSelectionSet_executeSelectionSet
      schema resolvers variableValues hschema depth operation.rootType source
      (filterSelectionSetBoolCase runtimeCase operation.selectionSet)
      hobject hsource hfilteredFree hfilteredReady hfilteredMerge
  have hfilter :
      Execution.executeSelectionSet schema resolvers variableValues depth
          operation.rootType source
          (filterSelectionSetBoolCase runtimeCase operation.selectionSet)
        =
      Execution.executeSelectionSet schema resolvers variableValues depth
          operation.rootType source operation.selectionSet :=
    executeSelectionSet_filterSelectionSetBoolCase schema resolvers
      variableValues operation runtimeCase hagrees depth operation.rootType
      source operation.selectionSet
      (by
        intro varName hmem
        exact hmem)
  exact (hrootSelect.trans (hground.trans hfilter)).symm

theorem completeNormalizationEffectiveSemanticsPreserved
    (schema : Schema) (operation : Operation)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hvalid : Validation.operationDefinitionValid schema operation)
    {ObjectRef : Type} (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues) (depth : Nat)
    (source : Execution.ResolverValue ObjectRef)
    (hcomplete
      : operationBoolVarsComplete operation
          (Execution.coerceVariableValues operation variableValues))
    : Execution.executeQueryWithFuel schema resolvers variableValues operation
        depth source
      = Execution.executeQueryWithFuel schema resolvers variableValues
          (completeNormalizeOperation schema operation) depth source := by
  exact completeNormalizationEffectiveSemanticsPreserved_of_selectionSet
    schema operation
    (completeNormalizationSelectionSetSemanticsPreserved schema operation)
    hschema hvalid resolvers variableValues depth source hcomplete

theorem completeNormalizationSemanticsPreserved (schema : Schema) (operation : Operation)
    : NormalForm.completeNormalizationSemanticsPreserved schema operation := by
  apply completeNormalizationSemanticsPreserved_of_selectionSet schema operation
  exact completeNormalizationSelectionSetSemanticsPreserved schema operation

end CompleteNormalization

end NormalForm

end GraphQL
