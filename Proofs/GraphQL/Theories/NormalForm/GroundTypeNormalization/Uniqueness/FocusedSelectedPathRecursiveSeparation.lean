import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.FocusedSelectedPathCompositeSeparation

/-!
Recursive observable-path and same-field selected-path separation.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

theorem selectedPathTaggedSelectionSetsResponseDiffWitness_of_objectOutput_sameField_childWitness_valid_normal_alignedSpine
    (schema : Schema)
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine leftChildSpine rightChildSpine
      : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftProbeField rightProbeField parentType : Name)
    (targetLeftArguments targetRightArguments : List Argument)
    (leftRuntime rightRuntime : Name) {left right : List Selection}
    {responseName fieldName : Name} {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions parentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> objectTypeNameBool schema parentType = true
      -> selectionSetDeepProbeFuel schema parentType left ≤ fuel
      -> selectionSetDeepProbeFuel schema parentType right ≤ fuel
      -> SelectedFieldSpineRuntimeValid schema
          fieldDefinition.outputType.namedType
          fieldDefinition.outputType.namedType leftChildSpine
      -> SelectedFieldSpineRuntimeValid schema
          fieldDefinition.outputType.namedType
          fieldDefinition.outputType.namedType rightChildSpine
      -> PathLocalSupportValidNormal schema parentType leftCurrentSelectionSet
      -> PathLocalSupportValidNormal schema parentType rightCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext left leftCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext right rightCurrentSelectionSet
      -> Selection.field responseName fieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName fieldName rightArguments rightDirectives
            rightChildSelectionSet
          ∈ right
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> objectTypeNameBool schema fieldDefinition.outputType.namedType = true
      -> SelectedPathTaggedSelectionSetsResponseDiffWitness schema
          rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
          leftInitialSpine rightInitialSpine variableValues
          (fuel - leafProbeFuel fieldDefinition.outputType)
          fieldDefinition.outputType.namedType
          fieldDefinition.outputType.namedType targetParent leftProbeField
          rightProbeField targetLeftArguments targetRightArguments leftRuntime
          rightRuntime
          (fieldPairPathLocalNextSelectionSet schema parentType
            fieldDefinition.outputType.namedType fieldName leftArguments
            leftCurrentSelectionSet)
          (fieldPairPathLocalNextSelectionSet schema parentType
            fieldDefinition.outputType.namedType fieldName rightArguments
            rightCurrentSelectionSet)
          leftChildSpine rightChildSpine leftChildSelectionSet
          rightChildSelectionSet
      -> SelectedPathTaggedSelectionSetsResponseDiffWitness schema
          rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
          leftInitialSpine rightInitialSpine variableValues (fuel + 1)
          parentType parentType targetParent leftProbeField rightProbeField
          targetLeftArguments targetRightArguments leftRuntime rightRuntime
          leftCurrentSelectionSet rightCurrentSelectionSet
          ({
              responseName := responseName,
              fieldName := fieldName,
              arguments := leftArguments,
              childRuntime := some fieldDefinition.outputType.namedType
            }
            :: leftChildSpine)
          ({
              responseName := responseName,
              fieldName := fieldName,
              arguments := rightArguments,
              childRuntime := some fieldDefinition.outputType.namedType
            }
            :: rightChildSpine)
          left right := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hobject hleftFuel hrightFuel hleftChildSpineValid
    hrightChildSpineValid hleftSupport hrightSupport hleftContext
    hrightContext hleftMem hrightMem hlookup hobjectOutput hchildWitness
  let leftSpine : List NormalSelectionSetObservableFieldStep :=
    { responseName := responseName, fieldName := fieldName,
      arguments := leftArguments,
      childRuntime := some fieldDefinition.outputType.namedType } ::
      leftChildSpine
  let rightSpine : List NormalSelectionSetObservableFieldStep :=
    { responseName := responseName, fieldName := fieldName,
      arguments := rightArguments,
      childRuntime := some fieldDefinition.outputType.namedType } ::
      rightChildSpine
  have hcomposite :
      (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool
        schema = true :=
    typeRef_named_isCompositeBool_true_of_objectTypeNameBool hobjectOutput
  have hleftSpineValid :
      SelectedFieldSpineRuntimeValid schema parentType parentType
        leftSpine :=
    SelectedFieldSpineRuntimeValid.objectChild hobject hlookup
      hcomposite hleftChildSpineValid
  have hrightSpineValid :
      SelectedFieldSpineRuntimeValid schema parentType parentType
        rightSpine :=
    SelectedFieldSpineRuntimeValid.objectChild hobject hlookup
      hcomposite hrightChildSpineValid
  have hleftTail :
      selectedObservableFieldSpineTailForRuntime
          fieldDefinition.outputType.namedType fieldName leftArguments
          leftSpine =
        leftChildSpine := by
    dsimp [leftSpine]
    exact
      selectedObservableFieldSpineTailForRuntime_cons_self
        { responseName := responseName, fieldName := fieldName,
          arguments := leftArguments,
          childRuntime := some fieldDefinition.outputType.namedType }
        leftChildSpine rfl
  have hrightTail :
      selectedObservableFieldSpineTailForRuntime
          fieldDefinition.outputType.namedType fieldName rightArguments
          rightSpine =
        rightChildSpine := by
    dsimp [rightSpine]
    exact
      selectedObservableFieldSpineTailForRuntime_cons_self
        { responseName := responseName, fieldName := fieldName,
          arguments := rightArguments,
          childRuntime := some fieldDefinition.outputType.namedType }
        rightChildSpine rfl
  have hchildWitnessTail :
      SelectedPathTaggedSelectionSetsResponseDiffWitness schema
        rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
        leftInitialSpine rightInitialSpine variableValues
        (fuel - leafProbeFuel fieldDefinition.outputType)
        fieldDefinition.outputType.namedType
        fieldDefinition.outputType.namedType targetParent leftProbeField
        rightProbeField targetLeftArguments targetRightArguments leftRuntime
        rightRuntime
        (fieldPairPathLocalNextSelectionSet schema parentType
          fieldDefinition.outputType.namedType fieldName leftArguments
          leftCurrentSelectionSet)
        (fieldPairPathLocalNextSelectionSet schema parentType
          fieldDefinition.outputType.namedType fieldName rightArguments
          rightCurrentSelectionSet)
        (selectedObservableFieldSpineTailForRuntime
          fieldDefinition.outputType.namedType fieldName leftArguments
          leftSpine)
        (selectedObservableFieldSpineTailForRuntime
          fieldDefinition.outputType.namedType fieldName rightArguments
          rightSpine)
        leftChildSelectionSet rightChildSelectionSet := by
    simpa [hleftTail, hrightTail] using
      hchildWitness
  simpa [leftSpine, rightSpine] using
    selectedPathTaggedSelectionSetsResponseDiffWitness_of_objectOutput_sameField_childWitness_valid_normal_runtimeSpine
      (schema := schema)
      (leftVariableDefinitions := leftVariableDefinitions)
      (rightVariableDefinitions := rightVariableDefinitions)
      rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet leftInitialSpine
      rightInitialSpine leftSpine rightSpine variableValues fuel
      targetParent leftProbeField rightProbeField parentType
      targetLeftArguments targetRightArguments leftRuntime rightRuntime
      hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
      hrightNormal hobject hleftFuel hrightFuel hleftSpineValid
      hrightSpineValid hleftSupport hrightSupport hleftContext
      hrightContext hleftMem hrightMem hlookup hobjectOutput
      hchildWitnessTail

theorem responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_left_observable_leaf_right_normal_object_outputs_of_valid_normal_runtimeSpine
    (schema : Schema)
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine leftSpine rightSpine
      : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftProbeField rightProbeField
      leftParentType rightParentType leftSourceRuntimeType
      rightSourceRuntimeType
      : Name)
    (targetLeftArguments targetRightArguments : List Argument)
    (leftRuntime rightRuntime : Name) {left right : List Selection} {responseName : Name}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions leftParentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions
          rightParentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema leftParentType left
      -> selectionSetNormal schema rightParentType right
      -> objectTypeNameBool schema leftParentType = true
      -> objectTypeNameBool schema rightParentType = true
      -> selectionSetDeepProbeFuel schema leftParentType left ≤ fuel
      -> selectionSetDeepProbeFuel schema rightParentType right ≤ fuel
      -> SelectedFieldSpineRuntimeValid schema leftParentType
          leftSourceRuntimeType leftSpine
      -> SelectedFieldSpineRuntimeValid schema rightParentType
          rightSourceRuntimeType rightSpine
      -> PathLocalSupportValidNormal schema leftSourceRuntimeType leftCurrentSelectionSet
      -> PathLocalSupportValidNormal schema rightSourceRuntimeType
          rightCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext left leftCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext right rightCurrentSelectionSet
      -> NormalSelectionSetObservableResponsePath schema leftParentType left
          [responseName]
      -> (∀ {rightFieldName : Name} {rightArguments : List Argument}
              {rightDirectives : List DirectiveApplication}
              {rightChildSelectionSet : List Selection}
              {rightFieldDefinition : FieldDefinition},
            Selection.field responseName rightFieldName rightArguments
                rightDirectives rightChildSelectionSet
              ∈ right
            -> schema.lookupField rightParentType rightFieldName
                = some rightFieldDefinition
            -> (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool
                  schema
                = true
            -> objectTypeNameBool schema rightFieldDefinition.outputType.namedType = true)
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSelectedPathProbeResolvers schema
                  leftInitialSelectionSet rightInitialSelectionSet
                  leftInitialSpine rightInitialSpine targetParent leftProbeField
                  rightProbeField targetLeftArguments targetRightArguments
                  leftRuntime rightRuntime)
                targetParent leftProbeField rightProbeField targetLeftArguments
                targetRightArguments)
              variableValues (fuel + 1) leftParentType
              (projectionTargetResolverValue
                (.object leftSourceRuntimeType
                  (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
                    leftCurrentSelectionSet leftSpine)))
              left).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSelectedPathProbeResolvers schema
                  leftInitialSelectionSet rightInitialSelectionSet
                  leftInitialSpine rightInitialSpine targetParent leftProbeField
                  rightProbeField targetLeftArguments targetRightArguments
                  leftRuntime rightRuntime)
                targetParent leftProbeField rightProbeField targetLeftArguments
                targetRightArguments)
              variableValues (fuel + 1) rightParentType
              (projectionTargetResolverValue
                (.object rightSourceRuntimeType
                  (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                    rightCurrentSelectionSet rightSpine)))
              right).data := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hleftObject hrightObject hleftFuel hrightFuel
    hleftSpineValid hrightSpineValid hleftSupport hrightSupport
    hleftContext hrightContext hleftObservable hrightCompositeObject
  by_cases hrightResponseName :
      responseName ∈ right.filterMap Selection.responseName?
  · rcases
        selectionSetNormal_field_mem_of_object_responseName_mem
          hrightNormal hrightObject hrightResponseName with
      ⟨rightFieldName, rightArguments, rightDirectives,
        rightChildSelectionSet, hrightMem⟩
    rcases selectionSetValid_field_lookup_of_mem hrightValid hrightMem with
      ⟨rightFieldDefinition, hrightLookup, _hrightArguments,
        _hrightFieldValid⟩
    by_cases hrightLeaf :
        (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool
          schema = false
    · exact
        responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_left_observable_leaf_right_leaf
          (schema := schema)
          (leftVariableDefinitions := leftVariableDefinitions)
          (rightVariableDefinitions := rightVariableDefinitions)
          rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet leftCurrentSelectionSet
          rightCurrentSelectionSet leftInitialSpine rightInitialSpine
          leftSpine rightSpine variableValues fuel targetParent
          leftProbeField rightProbeField leftParentType rightParentType
          leftSourceRuntimeType rightSourceRuntimeType
          targetLeftArguments targetRightArguments leftRuntime
          rightRuntime hschema hleftValid hrightValid hleftFree
          hrightFree hleftNormal hrightNormal hleftObject hrightObject
          hleftFuel hrightFuel hleftSpineValid hrightSpineValid
          hleftSupport hrightSupport hleftContext hrightContext
          hleftObservable hrightMem hrightLookup hrightLeaf
    · have hrightComposite :
          (TypeRef.named
              rightFieldDefinition.outputType.namedType).isCompositeBool
            schema = true := by
        cases h :
            (TypeRef.named
                rightFieldDefinition.outputType.namedType).isCompositeBool
              schema <;>
          simp [h] at hrightLeaf ⊢
      have hrightObjectOutput :
          objectTypeNameBool schema
              rightFieldDefinition.outputType.namedType = true :=
        hrightCompositeObject hrightMem hrightLookup hrightComposite
      rcases
          field_leaf_of_object_normalSelectionSetObservableResponsePath_single
            hleftObject hleftObservable with
        ⟨leftFieldName, leftArguments, leftDirectives,
          leftChildSelectionSet, leftFieldDefinition, hleftMem,
          hleftLookup, hleftLeaf⟩
      exact
        responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_left_leaf_right_objectOutput_field_pair_of_valid_normal_runtimeSpine
          (schema := schema)
          (leftVariableDefinitions := leftVariableDefinitions)
          (rightVariableDefinitions := rightVariableDefinitions)
          rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet leftCurrentSelectionSet
          rightCurrentSelectionSet leftInitialSpine rightInitialSpine
          leftSpine rightSpine variableValues fuel targetParent
          leftProbeField rightProbeField leftParentType rightParentType
          leftSourceRuntimeType rightSourceRuntimeType
          targetLeftArguments targetRightArguments leftRuntime
          rightRuntime hschema hleftValid hrightValid hleftFree
          hrightFree hleftNormal hrightNormal hleftObject hrightObject
          hleftFuel hrightFuel hleftSpineValid hrightSpineValid
          hleftSupport hrightSupport hleftContext hrightContext
          hleftMem hrightMem hleftLookup hrightLookup hleftLeaf
          hrightObjectOutput
  · exact
      responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_left_observable_responseName_absent
        (schema := schema)
        (leftVariableDefinitions := leftVariableDefinitions)
        (rightVariableDefinitions := rightVariableDefinitions)
        rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
        leftCurrentSelectionSet rightCurrentSelectionSet
        leftInitialSpine rightInitialSpine leftSpine rightSpine
        variableValues fuel targetParent leftProbeField rightProbeField
        leftParentType rightParentType leftSourceRuntimeType
        rightSourceRuntimeType targetLeftArguments targetRightArguments
        leftRuntime rightRuntime hschema hleftValid hrightValid hleftFree
        hrightFree hleftNormal hrightNormal hleftObject hrightObject
        hleftFuel hrightFuel hleftSpineValid hrightSpineValid
        hleftSupport hrightSupport hleftContext hrightContext
        (by simpa using hleftObservable) hrightResponseName

theorem responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_left_observable_leaf_right_normal_of_valid_normal_runtimeSpine
    (schema : Schema)
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine leftSpine rightSpine
      : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftProbeField rightProbeField
      leftParentType rightParentType leftSourceRuntimeType
      rightSourceRuntimeType
      : Name)
    (targetLeftArguments targetRightArguments : List Argument)
    (leftRuntime rightRuntime : Name) {left right : List Selection} {responseName : Name}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions leftParentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions
          rightParentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema leftParentType left
      -> selectionSetNormal schema rightParentType right
      -> objectTypeNameBool schema leftParentType = true
      -> objectTypeNameBool schema rightParentType = true
      -> selectionSetDeepProbeFuel schema leftParentType left ≤ fuel
      -> selectionSetDeepProbeFuel schema rightParentType right ≤ fuel
      -> SelectedFieldSpineRuntimeValid schema leftParentType
          leftSourceRuntimeType leftSpine
      -> SelectedFieldSpineRuntimeValid schema rightParentType
          rightSourceRuntimeType rightSpine
      -> PathLocalSupportValidNormal schema leftSourceRuntimeType leftCurrentSelectionSet
      -> PathLocalSupportValidNormal schema rightSourceRuntimeType
          rightCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext left leftCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext right rightCurrentSelectionSet
      -> NormalSelectionSetObservableResponsePath schema leftParentType left
          [responseName]
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSelectedPathProbeResolvers schema
                  leftInitialSelectionSet rightInitialSelectionSet
                  leftInitialSpine rightInitialSpine targetParent leftProbeField
                  rightProbeField targetLeftArguments targetRightArguments
                  leftRuntime rightRuntime)
                targetParent leftProbeField rightProbeField targetLeftArguments
                targetRightArguments)
              variableValues (fuel + 1) leftParentType
              (projectionTargetResolverValue
                (.object leftSourceRuntimeType
                  (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
                    leftCurrentSelectionSet leftSpine)))
              left).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSelectedPathProbeResolvers schema
                  leftInitialSelectionSet rightInitialSelectionSet
                  leftInitialSpine rightInitialSpine targetParent leftProbeField
                  rightProbeField targetLeftArguments targetRightArguments
                  leftRuntime rightRuntime)
                targetParent leftProbeField rightProbeField targetLeftArguments
                targetRightArguments)
              variableValues (fuel + 1) rightParentType
              (projectionTargetResolverValue
                (.object rightSourceRuntimeType
                  (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                    rightCurrentSelectionSet rightSpine)))
              right).data := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hleftObject hrightObject hleftFuel hrightFuel
    hleftSpineValid hrightSpineValid hleftSupport hrightSupport
    hleftContext hrightContext hleftObservable
  by_cases hrightResponseName :
      responseName ∈ right.filterMap Selection.responseName?
  · rcases
        selectionSetNormal_field_mem_of_object_responseName_mem
          hrightNormal hrightObject hrightResponseName with
      ⟨rightFieldName, rightArguments, rightDirectives,
        rightChildSelectionSet, hrightMem⟩
    rcases selectionSetValid_field_lookup_of_mem hrightValid hrightMem with
      ⟨rightFieldDefinition, hrightLookup, _hrightArguments,
        _hrightFieldValid⟩
    by_cases hrightLeaf :
        (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool
          schema = false
    · exact
        responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_left_observable_leaf_right_leaf
          (schema := schema)
          (leftVariableDefinitions := leftVariableDefinitions)
          (rightVariableDefinitions := rightVariableDefinitions)
          rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet leftCurrentSelectionSet
          rightCurrentSelectionSet leftInitialSpine rightInitialSpine
          leftSpine rightSpine variableValues fuel targetParent
          leftProbeField rightProbeField leftParentType rightParentType
          leftSourceRuntimeType rightSourceRuntimeType
          targetLeftArguments targetRightArguments leftRuntime
          rightRuntime hschema hleftValid hrightValid hleftFree
          hrightFree hleftNormal hrightNormal hleftObject hrightObject
          hleftFuel hrightFuel hleftSpineValid hrightSpineValid
          hleftSupport hrightSupport hleftContext hrightContext
          hleftObservable hrightMem hrightLookup hrightLeaf
    · have hrightComposite :
          (TypeRef.named
              rightFieldDefinition.outputType.namedType).isCompositeBool
            schema = true := by
        cases h :
            (TypeRef.named
                rightFieldDefinition.outputType.namedType).isCompositeBool
              schema <;>
          simp [h] at hrightLeaf ⊢
      rcases
          field_leaf_of_object_normalSelectionSetObservableResponsePath_single
            hleftObject hleftObservable with
        ⟨leftFieldName, leftArguments, leftDirectives,
          leftChildSelectionSet, leftFieldDefinition, hleftMem,
          hleftLookup, hleftLeaf⟩
      exact
        responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_left_leaf_right_composite_field_pair_of_valid_normal_runtimeSpine
          (schema := schema)
          (leftVariableDefinitions := leftVariableDefinitions)
          (rightVariableDefinitions := rightVariableDefinitions)
          rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet leftCurrentSelectionSet
          rightCurrentSelectionSet leftInitialSpine rightInitialSpine
          leftSpine rightSpine variableValues fuel targetParent
          leftProbeField rightProbeField leftParentType rightParentType
          leftSourceRuntimeType rightSourceRuntimeType
          targetLeftArguments targetRightArguments leftRuntime
          rightRuntime hschema hleftValid hrightValid hleftFree
          hrightFree hleftNormal hrightNormal hleftObject hrightObject
          hleftFuel hrightFuel hleftSpineValid hrightSpineValid
          hleftSupport hrightSupport hleftContext hrightContext
          hleftMem hrightMem hleftLookup hrightLookup hleftLeaf
          hrightComposite
  · exact
      responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_left_observable_responseName_absent
        (schema := schema)
        (leftVariableDefinitions := leftVariableDefinitions)
        (rightVariableDefinitions := rightVariableDefinitions)
        rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
        leftCurrentSelectionSet rightCurrentSelectionSet
        leftInitialSpine rightInitialSpine leftSpine rightSpine
        variableValues fuel targetParent leftProbeField rightProbeField
        leftParentType rightParentType leftSourceRuntimeType
        rightSourceRuntimeType targetLeftArguments targetRightArguments
        leftRuntime rightRuntime hschema hleftValid hrightValid hleftFree
        hrightFree hleftNormal hrightNormal hleftObject hrightObject
        hleftFuel hrightFuel hleftSpineValid hrightSpineValid
        hleftSupport hrightSupport hleftContext hrightContext
        (by simpa using hleftObservable) hrightResponseName

theorem responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_left_observable_leaf_right_normal_of_valid_normal_runtimeSpine_fuels
    (schema : Schema)
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine leftSpine rightSpine
      : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (leftFuel rightFuel : Nat)
    (targetParent leftProbeField
      rightProbeField leftParentType rightParentType leftSourceRuntimeType
      rightSourceRuntimeType
      : Name)
    (targetLeftArguments targetRightArguments : List Argument)
    (leftRuntime rightRuntime : Name) {left right : List Selection} {responseName : Name}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions leftParentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions
          rightParentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema leftParentType left
      -> selectionSetNormal schema rightParentType right
      -> objectTypeNameBool schema leftParentType = true
      -> objectTypeNameBool schema rightParentType = true
      -> selectionSetDeepProbeFuel schema leftParentType left ≤ leftFuel
      -> selectionSetDeepProbeFuel schema rightParentType right ≤ rightFuel
      -> SelectedFieldSpineRuntimeValid schema leftParentType
          leftSourceRuntimeType leftSpine
      -> SelectedFieldSpineRuntimeValid schema rightParentType
          rightSourceRuntimeType rightSpine
      -> PathLocalSupportValidNormal schema leftSourceRuntimeType leftCurrentSelectionSet
      -> PathLocalSupportValidNormal schema rightSourceRuntimeType
          rightCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext left leftCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext right rightCurrentSelectionSet
      -> NormalSelectionSetObservableResponsePath schema leftParentType left
          [responseName]
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSelectedPathProbeResolvers schema
                  leftInitialSelectionSet rightInitialSelectionSet
                  leftInitialSpine rightInitialSpine targetParent leftProbeField
                  rightProbeField targetLeftArguments targetRightArguments
                  leftRuntime rightRuntime)
                targetParent leftProbeField rightProbeField targetLeftArguments
                targetRightArguments)
              variableValues (leftFuel + 1) leftParentType
              (projectionTargetResolverValue
                (.object leftSourceRuntimeType
                  (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
                    leftCurrentSelectionSet leftSpine)))
              left).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSelectedPathProbeResolvers schema
                  leftInitialSelectionSet rightInitialSelectionSet
                  leftInitialSpine rightInitialSpine targetParent leftProbeField
                  rightProbeField targetLeftArguments targetRightArguments
                  leftRuntime rightRuntime)
                targetParent leftProbeField rightProbeField targetLeftArguments
                targetRightArguments)
              variableValues (rightFuel + 1) rightParentType
              (projectionTargetResolverValue
                (.object rightSourceRuntimeType
                  (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                    rightCurrentSelectionSet rightSpine)))
              right).data := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hleftObject hrightObject hleftFuel hrightFuel
    hleftSpineValid hrightSpineValid hleftSupport hrightSupport
    hleftContext hrightContext hleftObservable
  by_cases hrightResponseName :
      responseName ∈ right.filterMap Selection.responseName?
  · rcases
        selectionSetNormal_field_mem_of_object_responseName_mem
          hrightNormal hrightObject hrightResponseName with
      ⟨rightFieldName, rightArguments, rightDirectives,
        rightChildSelectionSet, hrightMem⟩
    rcases selectionSetValid_field_lookup_of_mem hrightValid hrightMem with
      ⟨rightFieldDefinition, hrightLookup, _hrightArguments,
        _hrightFieldValid⟩
    by_cases hrightLeaf :
        (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool
          schema = false
    · exact
        responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_left_observable_leaf_right_leaf_fuels
          (schema := schema)
          (leftVariableDefinitions := leftVariableDefinitions)
          (rightVariableDefinitions := rightVariableDefinitions)
          rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet leftCurrentSelectionSet
          rightCurrentSelectionSet leftInitialSpine rightInitialSpine
          leftSpine rightSpine variableValues leftFuel rightFuel
          targetParent leftProbeField rightProbeField leftParentType
          rightParentType leftSourceRuntimeType rightSourceRuntimeType
          targetLeftArguments targetRightArguments leftRuntime
          rightRuntime hschema hleftValid hrightValid hleftFree
          hrightFree hleftNormal hrightNormal hleftObject hrightObject
          hleftFuel hrightFuel hleftSpineValid hrightSpineValid
          hleftSupport hrightSupport hleftContext hrightContext
          hleftObservable hrightMem hrightLookup hrightLeaf
    · have hrightComposite :
          (TypeRef.named
              rightFieldDefinition.outputType.namedType).isCompositeBool
            schema = true := by
        cases h :
            (TypeRef.named
                rightFieldDefinition.outputType.namedType).isCompositeBool
              schema <;>
          simp [h] at hrightLeaf ⊢
      rcases
          field_leaf_of_object_normalSelectionSetObservableResponsePath_single
            hleftObject hleftObservable with
        ⟨leftFieldName, leftArguments, leftDirectives,
          leftChildSelectionSet, leftFieldDefinition, hleftMem,
          hleftLookup, hleftLeaf⟩
      exact
        responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_left_leaf_right_composite_field_pair_of_valid_normal_runtimeSpine_fuels
          (schema := schema)
          (leftVariableDefinitions := leftVariableDefinitions)
          (rightVariableDefinitions := rightVariableDefinitions)
          rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet leftCurrentSelectionSet
          rightCurrentSelectionSet leftInitialSpine rightInitialSpine
          leftSpine rightSpine variableValues leftFuel rightFuel
          targetParent leftProbeField rightProbeField leftParentType
          rightParentType leftSourceRuntimeType rightSourceRuntimeType
          targetLeftArguments targetRightArguments leftRuntime
          rightRuntime hschema hleftValid hrightValid hleftFree
          hrightFree hleftNormal hrightNormal hleftObject hrightObject
          hleftFuel hrightFuel hleftSpineValid hrightSpineValid
          hleftSupport hrightSupport hleftContext hrightContext
          hleftMem hrightMem hleftLookup hrightLookup hleftLeaf
          hrightComposite
  · exact
      responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_left_observable_responseName_absent_fuels
        (schema := schema)
        (leftVariableDefinitions := leftVariableDefinitions)
        (rightVariableDefinitions := rightVariableDefinitions)
        rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
        leftCurrentSelectionSet rightCurrentSelectionSet
        leftInitialSpine rightInitialSpine leftSpine rightSpine
        variableValues leftFuel rightFuel targetParent leftProbeField
        rightProbeField leftParentType rightParentType leftSourceRuntimeType
        rightSourceRuntimeType targetLeftArguments targetRightArguments
        leftRuntime rightRuntime hschema hleftValid hrightValid hleftFree
        hrightFree hleftNormal hrightNormal hleftObject hrightObject
        hleftFuel hrightFuel hleftSpineValid hrightSpineValid
        hleftSupport hrightSupport hleftContext hrightContext
        (by simpa using hleftObservable) hrightResponseName

theorem responseData_not_semanticEquivalent_existsSpine_of_fieldPairOrDeepSuccess_selectedPathProbe_left_observable_leaf_right_normal_valid_normal_fuels
    (schema : Schema)
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (leftFuel rightFuel : Nat)
    (targetParent leftProbeField rightProbeField leftParentType rightParentType : Name)
    (targetLeftArguments targetRightArguments : List Argument)
    (leftRuntime rightRuntime : Name) {left right : List Selection} {responseName : Name}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions leftParentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions
          rightParentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema leftParentType left
      -> selectionSetNormal schema rightParentType right
      -> objectTypeNameBool schema leftParentType = true
      -> objectTypeNameBool schema rightParentType = true
      -> selectionSetDeepProbeFuel schema leftParentType left ≤ leftFuel
      -> selectionSetDeepProbeFuel schema rightParentType right ≤ rightFuel
      -> PathLocalSupportValidNormal schema leftParentType leftCurrentSelectionSet
      -> PathLocalSupportValidNormal schema rightParentType rightCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext left leftCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext right rightCurrentSelectionSet
      -> NormalSelectionSetObservableResponsePath schema leftParentType left
          [responseName]
      -> right ≠ []
      -> ∃ leftSpine rightSpine,
          SelectedFieldSpineRuntimeValid schema leftParentType leftParentType leftSpine
          ∧ SelectedFieldSpineRuntimeValid schema rightParentType
              rightParentType rightSpine
          ∧ ¬ Execution.ResponseValue.semanticEquivalent
                (Execution.executeSelectionSetAsResponse schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairSelectedPathProbeResolvers schema
                      leftInitialSelectionSet rightInitialSelectionSet
                      leftInitialSpine rightInitialSpine targetParent
                      leftProbeField rightProbeField targetLeftArguments
                      targetRightArguments leftRuntime rightRuntime)
                    targetParent leftProbeField rightProbeField
                    targetLeftArguments targetRightArguments)
                  variableValues (leftFuel + 1) leftParentType
                  (projectionTargetResolverValue
                    (.object leftParentType
                      (FieldPairSelectedPathProbeRef.target
                        FieldPairProbeTag.left leftCurrentSelectionSet
                        leftSpine)))
                  left).data
                (Execution.executeSelectionSetAsResponse schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairSelectedPathProbeResolvers schema
                      leftInitialSelectionSet rightInitialSelectionSet
                      leftInitialSpine rightInitialSpine targetParent
                      leftProbeField rightProbeField targetLeftArguments
                      targetRightArguments leftRuntime rightRuntime)
                    targetParent leftProbeField rightProbeField
                    targetLeftArguments targetRightArguments)
                  variableValues (rightFuel + 1) rightParentType
                  (projectionTargetResolverValue
                    (.object rightParentType
                      (FieldPairSelectedPathProbeRef.target
                        FieldPairProbeTag.right rightCurrentSelectionSet
                        rightSpine)))
                  right).data := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hleftObject hrightObject hleftFuel hrightFuel
    hleftSupport hrightSupport hleftContext hrightContext hleftObservable
    hrightNonempty
  rcases
      field_leaf_of_object_normalSelectionSetObservableResponsePath_single
        hleftObject hleftObservable with
    ⟨leftFieldName, leftArguments, _leftDirectives,
      _leftChildSelectionSet, leftFieldDefinition, _hleftMem,
      hleftLookup, hleftLeaf⟩
  let leftSpine : List NormalSelectionSetObservableFieldStep :=
    [{ responseName := responseName, fieldName := leftFieldName,
       arguments := leftArguments, childRuntime := none }]
  have hleftSpineValid :
      SelectedFieldSpineRuntimeValid schema leftParentType leftParentType
        leftSpine :=
    SelectedFieldSpineRuntimeValid.objectLeaf hleftObject hleftLookup
      hleftLeaf
  rcases
      selectedFieldSpineRuntimeValid_exists_of_valid_normal_object_nonempty
        hrightValid hrightNormal hrightObject hrightNonempty with
    ⟨rightSpine, hrightSpineValid, _hrightObservableSpine⟩
  refine ⟨leftSpine, rightSpine, hleftSpineValid, hrightSpineValid, ?_⟩
  exact
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_left_observable_leaf_right_normal_of_valid_normal_runtimeSpine_fuels
      (schema := schema)
      (leftVariableDefinitions := leftVariableDefinitions)
      (rightVariableDefinitions := rightVariableDefinitions)
      rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet leftInitialSpine
      rightInitialSpine leftSpine rightSpine variableValues leftFuel
      rightFuel targetParent leftProbeField rightProbeField leftParentType
      rightParentType leftParentType rightParentType targetLeftArguments
      targetRightArguments leftRuntime rightRuntime hschema hleftValid
      hrightValid hleftFree hrightFree hleftNormal hrightNormal
      hleftObject hrightObject hleftFuel hrightFuel hleftSpineValid
      hrightSpineValid hleftSupport hrightSupport hleftContext
      hrightContext hleftObservable

theorem responseData_not_semanticEquivalent_existsSpine_of_fieldPairOrDeepSuccess_selectedPathProbe_left_observable_right_responseName_absent_valid_normal_fuels
    (schema : Schema)
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (leftFuel rightFuel : Nat)
    (targetParent leftProbeField rightProbeField leftParentType rightParentType : Name)
    (targetLeftArguments targetRightArguments : List Argument)
    (leftRuntime rightRuntime : Name) {left right : List Selection} {responseName : Name}
    {pathTail : List Name}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions leftParentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions
          rightParentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema leftParentType left
      -> selectionSetNormal schema rightParentType right
      -> objectTypeNameBool schema leftParentType = true
      -> objectTypeNameBool schema rightParentType = true
      -> selectionSetDeepProbeFuel schema leftParentType left ≤ leftFuel
      -> selectionSetDeepProbeFuel schema rightParentType right ≤ rightFuel
      -> PathLocalSupportValidNormal schema leftParentType leftCurrentSelectionSet
      -> PathLocalSupportValidNormal schema rightParentType rightCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext left leftCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext right rightCurrentSelectionSet
      -> NormalSelectionSetObservableResponsePath schema leftParentType left
          (responseName :: pathTail)
      -> responseName ∉ right.filterMap Selection.responseName?
      -> right ≠ []
      -> ∃ leftSpine rightSpine,
          SelectedFieldSpineRuntimeValid schema leftParentType leftParentType leftSpine
          ∧ SelectedFieldSpineRuntimeValid schema rightParentType
              rightParentType rightSpine
          ∧ ¬ Execution.ResponseValue.semanticEquivalent
                (Execution.executeSelectionSetAsResponse schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairSelectedPathProbeResolvers schema
                      leftInitialSelectionSet rightInitialSelectionSet
                      leftInitialSpine rightInitialSpine targetParent
                      leftProbeField rightProbeField targetLeftArguments
                      targetRightArguments leftRuntime rightRuntime)
                    targetParent leftProbeField rightProbeField
                    targetLeftArguments targetRightArguments)
                  variableValues (leftFuel + 1) leftParentType
                  (projectionTargetResolverValue
                    (.object leftParentType
                      (FieldPairSelectedPathProbeRef.target
                        FieldPairProbeTag.left leftCurrentSelectionSet
                        leftSpine)))
                  left).data
                (Execution.executeSelectionSetAsResponse schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairSelectedPathProbeResolvers schema
                      leftInitialSelectionSet rightInitialSelectionSet
                      leftInitialSpine rightInitialSpine targetParent
                      leftProbeField rightProbeField targetLeftArguments
                      targetRightArguments leftRuntime rightRuntime)
                    targetParent leftProbeField rightProbeField
                    targetLeftArguments targetRightArguments)
                  variableValues (rightFuel + 1) rightParentType
                  (projectionTargetResolverValue
                    (.object rightParentType
                      (FieldPairSelectedPathProbeRef.target
                        FieldPairProbeTag.right rightCurrentSelectionSet
                        rightSpine)))
                  right).data := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hleftObject hrightObject hleftFuel hrightFuel
    hleftSupport hrightSupport hleftContext hrightContext hleftObservable
    hrightNoResponseName hrightNonempty
  rcases
      selectedFieldSpineRuntimeValid_exists_of_observableResponsePath_valid_normal
        hleftObservable hleftValid hleftNormal with
    ⟨leftRuntimeType, leftSpine, hleftInclude, hleftSpineValid,
      _hleftObservableSpine⟩
  have hleftRuntimeEq : leftRuntimeType = leftParentType :=
    typeIncludesObjectBool_eq_of_objectTypeNameBool_true schema
      hleftObject hleftInclude
  subst leftRuntimeType
  rcases
      selectedFieldSpineRuntimeValid_exists_of_valid_normal_object_nonempty
        hrightValid hrightNormal hrightObject hrightNonempty with
    ⟨rightSpine, hrightSpineValid, _hrightObservableSpine⟩
  refine ⟨leftSpine, rightSpine, hleftSpineValid, hrightSpineValid, ?_⟩
  exact
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_left_observable_responseName_absent_fuels
      (schema := schema)
      (leftVariableDefinitions := leftVariableDefinitions)
      (rightVariableDefinitions := rightVariableDefinitions)
      rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet leftInitialSpine
      rightInitialSpine leftSpine rightSpine variableValues leftFuel
      rightFuel targetParent leftProbeField rightProbeField leftParentType
      rightParentType leftParentType rightParentType targetLeftArguments
      targetRightArguments leftRuntime rightRuntime hschema hleftValid
      hrightValid hleftFree hrightFree hleftNormal hrightNormal
      hleftObject hrightObject hleftFuel hrightFuel hleftSpineValid
      hrightSpineValid hleftSupport hrightSupport hleftContext
      hrightContext (by simpa using hleftObservable) hrightNoResponseName

theorem responseData_not_semanticEquivalent_existsSpine_of_fieldPairOrDeepSuccess_selectedPathProbe_left_observable_composite_right_leaf_valid_normal_fuels
    (schema : Schema)
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (leftFuel rightFuel : Nat)
    (targetParent leftProbeField rightProbeField leftParentType rightParentType : Name)
    (targetLeftArguments targetRightArguments : List Argument)
    (leftRuntime rightRuntime : Name) {left right : List Selection}
    {responseName leftFieldName rightFieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {leftFieldDefinition rightFieldDefinition : FieldDefinition} {pathTail : List Name}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions leftParentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions
          rightParentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema leftParentType left
      -> selectionSetNormal schema rightParentType right
      -> objectTypeNameBool schema leftParentType = true
      -> objectTypeNameBool schema rightParentType = true
      -> selectionSetDeepProbeFuel schema leftParentType left ≤ leftFuel
      -> selectionSetDeepProbeFuel schema rightParentType right ≤ rightFuel
      -> PathLocalSupportValidNormal schema leftParentType leftCurrentSelectionSet
      -> PathLocalSupportValidNormal schema rightParentType rightCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext left leftCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext right rightCurrentSelectionSet
      -> NormalSelectionSetObservableResponsePath schema leftParentType left
          (responseName :: pathTail)
      -> Selection.field responseName leftFieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName rightFieldName rightArguments
            rightDirectives rightChildSelectionSet
          ∈ right
      -> schema.lookupField leftParentType leftFieldName = some leftFieldDefinition
      -> schema.lookupField rightParentType rightFieldName = some rightFieldDefinition
      -> (TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> ∃ leftSpine rightSpine,
          SelectedFieldSpineRuntimeValid schema leftParentType leftParentType leftSpine
          ∧ SelectedFieldSpineRuntimeValid schema rightParentType
              rightParentType rightSpine
          ∧ ¬ Execution.ResponseValue.semanticEquivalent
                (Execution.executeSelectionSetAsResponse schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairSelectedPathProbeResolvers schema
                      leftInitialSelectionSet rightInitialSelectionSet
                      leftInitialSpine rightInitialSpine targetParent
                      leftProbeField rightProbeField targetLeftArguments
                      targetRightArguments leftRuntime rightRuntime)
                    targetParent leftProbeField rightProbeField
                    targetLeftArguments targetRightArguments)
                  variableValues (leftFuel + 1) leftParentType
                  (projectionTargetResolverValue
                    (.object leftParentType
                      (FieldPairSelectedPathProbeRef.target
                        FieldPairProbeTag.left leftCurrentSelectionSet
                        leftSpine)))
                  left).data
                (Execution.executeSelectionSetAsResponse schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairSelectedPathProbeResolvers schema
                      leftInitialSelectionSet rightInitialSelectionSet
                      leftInitialSpine rightInitialSpine targetParent
                      leftProbeField rightProbeField targetLeftArguments
                      targetRightArguments leftRuntime rightRuntime)
                    targetParent leftProbeField rightProbeField
                    targetLeftArguments targetRightArguments)
                  variableValues (rightFuel + 1) rightParentType
                  (projectionTargetResolverValue
                    (.object rightParentType
                      (FieldPairSelectedPathProbeRef.target
                        FieldPairProbeTag.right rightCurrentSelectionSet
                        rightSpine)))
                  right).data := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hleftObject hrightObject hleftFuel hrightFuel
    hleftSupport hrightSupport hleftContext hrightContext hleftObservable
    hleftMem hrightMem hleftLookup hrightLookup hleftComposite hrightLeaf
  rcases
      selectedFieldSpineRuntimeValid_exists_of_observableResponsePath_valid_normal
        hleftObservable hleftValid hleftNormal with
    ⟨leftRuntimeType, leftSpine, hleftInclude, hleftSpineValid,
      _hleftObservableSpine⟩
  have hleftRuntimeEq : leftRuntimeType = leftParentType :=
    typeIncludesObjectBool_eq_of_objectTypeNameBool_true schema
      hleftObject hleftInclude
  subst leftRuntimeType
  let rightSpine : List NormalSelectionSetObservableFieldStep :=
    [{ responseName := responseName, fieldName := rightFieldName,
       arguments := rightArguments, childRuntime := none }]
  have hrightSpineValid :
      SelectedFieldSpineRuntimeValid schema rightParentType rightParentType
        rightSpine :=
    SelectedFieldSpineRuntimeValid.objectLeaf hrightObject hrightLookup
      hrightLeaf
  refine ⟨leftSpine, rightSpine, hleftSpineValid, hrightSpineValid, ?_⟩
  exact
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_left_composite_right_leaf_field_pair_of_valid_normal_runtimeSpine_fuels
      (schema := schema)
      (leftVariableDefinitions := leftVariableDefinitions)
      (rightVariableDefinitions := rightVariableDefinitions)
      rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet leftInitialSpine
      rightInitialSpine leftSpine rightSpine variableValues leftFuel
      rightFuel targetParent leftProbeField rightProbeField leftParentType
      rightParentType leftParentType rightParentType targetLeftArguments
      targetRightArguments leftRuntime rightRuntime hschema hleftValid
      hrightValid hleftFree hrightFree hleftNormal hrightNormal
      hleftObject hrightObject hleftFuel hrightFuel hleftSpineValid
      hrightSpineValid hleftSupport hrightSupport hleftContext
      hrightContext hleftMem hrightMem hleftLookup hrightLookup
      hleftComposite hrightLeaf

theorem selectedPathTaggedSelectionSetsResponseDiffWitness_of_left_observable_leaf_right_normal_object_outputs_valid_normal_runtimeSpine
    (schema : Schema)
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine leftSpine rightSpine
      : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftProbeField rightProbeField parentType : Name)
    (targetLeftArguments targetRightArguments : List Argument)
    (leftRuntime rightRuntime : Name) {left right : List Selection} {responseName : Name}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions parentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> objectTypeNameBool schema parentType = true
      -> selectionSetDeepProbeFuel schema parentType left ≤ fuel
      -> selectionSetDeepProbeFuel schema parentType right ≤ fuel
      -> SelectedFieldSpineRuntimeValid schema parentType parentType leftSpine
      -> SelectedFieldSpineRuntimeValid schema parentType parentType rightSpine
      -> PathLocalSupportValidNormal schema parentType leftCurrentSelectionSet
      -> PathLocalSupportValidNormal schema parentType rightCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext left leftCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext right rightCurrentSelectionSet
      -> NormalSelectionSetObservableResponsePath schema parentType left [responseName]
      -> (∀ {rightFieldName : Name} {rightArguments : List Argument}
              {rightDirectives : List DirectiveApplication}
              {rightChildSelectionSet : List Selection}
              {rightFieldDefinition : FieldDefinition},
            Selection.field responseName rightFieldName rightArguments
                rightDirectives rightChildSelectionSet
              ∈ right
            -> schema.lookupField parentType rightFieldName = some rightFieldDefinition
            -> (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool
                  schema
                = true
            -> objectTypeNameBool schema rightFieldDefinition.outputType.namedType = true)
      -> SelectedPathTaggedSelectionSetsResponseDiffWitness schema
          rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
          leftInitialSpine rightInitialSpine variableValues (fuel + 1)
          parentType parentType targetParent leftProbeField rightProbeField
          targetLeftArguments targetRightArguments leftRuntime rightRuntime
          leftCurrentSelectionSet rightCurrentSelectionSet leftSpine rightSpine
          left right := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hobject hleftFuel hrightFuel hleftSpineValid
    hrightSpineValid hleftSupport hrightSupport hleftContext
    hrightContext hleftObservable hrightCompositeObject
  rcases
      executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_of_valid_normal_runtimeSpine_support_context_fuel_ge_size
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftInitialSpine rightInitialSpine
        variableValues hschema (SelectionSet.size left + 1) parentType
        leftVariableDefinitions left fuel parentType targetParent
        leftProbeField rightProbeField targetLeftArguments
        targetRightArguments leftRuntime rightRuntime FieldPairProbeTag.left
        leftCurrentSelectionSet leftSpine (by omega) hleftFuel
        hleftValid hleftFree hleftNormal hleftSpineValid hleftSupport
        (fun _hobject => hleftContext)
        (fun hnonObject => by
          rw [hobject] at hnonObject
          simp at hnonObject) with
    ⟨leftFields, leftErrors, hleftResponse⟩
  rcases
      executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_of_valid_normal_runtimeSpine_support_context_fuel_ge_size
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftInitialSpine rightInitialSpine
        variableValues hschema (SelectionSet.size right + 1) parentType
        rightVariableDefinitions right fuel parentType targetParent
        leftProbeField rightProbeField targetLeftArguments
        targetRightArguments leftRuntime rightRuntime FieldPairProbeTag.right
        rightCurrentSelectionSet rightSpine (by omega) hrightFuel
        hrightValid hrightFree hrightNormal hrightSpineValid hrightSupport
        (fun _hobject => hrightContext)
        (fun hnonObject => by
          rw [hobject] at hnonObject
          simp at hnonObject) with
    ⟨rightFields, rightErrors, hrightResponse⟩
  have hdataNot :
      ¬ Execution.ResponseValue.semanticEquivalent
        (Execution.executeSelectionSetAsResponse schema
          (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
            (fieldPairSelectedPathProbeResolvers schema
              leftInitialSelectionSet rightInitialSelectionSet
              leftInitialSpine rightInitialSpine targetParent leftProbeField
              rightProbeField targetLeftArguments targetRightArguments
              leftRuntime rightRuntime)
            targetParent leftProbeField rightProbeField targetLeftArguments
            targetRightArguments)
          variableValues (fuel + 1) parentType
          (projectionTargetResolverValue
            (.object parentType
              (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
                leftCurrentSelectionSet leftSpine)))
          left).data
        (Execution.executeSelectionSetAsResponse schema
          (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
            (fieldPairSelectedPathProbeResolvers schema
              leftInitialSelectionSet rightInitialSelectionSet
              leftInitialSpine rightInitialSpine targetParent leftProbeField
              rightProbeField targetLeftArguments targetRightArguments
              leftRuntime rightRuntime)
            targetParent leftProbeField rightProbeField targetLeftArguments
            targetRightArguments)
          variableValues (fuel + 1) parentType
          (projectionTargetResolverValue
            (.object parentType
              (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                rightCurrentSelectionSet rightSpine)))
          right).data :=
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_left_observable_leaf_right_normal_object_outputs_of_valid_normal_runtimeSpine
      (schema := schema)
      (leftVariableDefinitions := leftVariableDefinitions)
      (rightVariableDefinitions := rightVariableDefinitions)
      rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet leftInitialSpine
      rightInitialSpine leftSpine rightSpine variableValues fuel
      targetParent leftProbeField rightProbeField parentType parentType
      parentType parentType targetLeftArguments targetRightArguments
      leftRuntime rightRuntime hschema hleftValid hrightValid hleftFree
      hrightFree hleftNormal hrightNormal hobject hobject hleftFuel
      hrightFuel hleftSpineValid hrightSpineValid hleftSupport
      hrightSupport hleftContext hrightContext hleftObservable
      hrightCompositeObject
  refine
    ⟨typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject,
      leftFields, leftErrors, rightFields, rightErrors, hleftResponse,
      hrightResponse, ?_⟩
  intro hobjects
  exact hdataNot (by simpa [hleftResponse, hrightResponse] using hobjects)

theorem selectedPathTaggedSelectionSetsResponseDiffWitness_of_left_observable_leaf_right_normal_valid_normal_runtimeSpine
    (schema : Schema)
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine leftSpine rightSpine
      : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftProbeField rightProbeField parentType : Name)
    (targetLeftArguments targetRightArguments : List Argument)
    (leftRuntime rightRuntime : Name) {left right : List Selection} {responseName : Name}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions parentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> objectTypeNameBool schema parentType = true
      -> selectionSetDeepProbeFuel schema parentType left ≤ fuel
      -> selectionSetDeepProbeFuel schema parentType right ≤ fuel
      -> SelectedFieldSpineRuntimeValid schema parentType parentType leftSpine
      -> SelectedFieldSpineRuntimeValid schema parentType parentType rightSpine
      -> PathLocalSupportValidNormal schema parentType leftCurrentSelectionSet
      -> PathLocalSupportValidNormal schema parentType rightCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext left leftCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext right rightCurrentSelectionSet
      -> NormalSelectionSetObservableResponsePath schema parentType left [responseName]
      -> SelectedPathTaggedSelectionSetsResponseDiffWitness schema
          rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
          leftInitialSpine rightInitialSpine variableValues (fuel + 1)
          parentType parentType targetParent leftProbeField rightProbeField
          targetLeftArguments targetRightArguments leftRuntime rightRuntime
          leftCurrentSelectionSet rightCurrentSelectionSet leftSpine rightSpine
          left right := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hobject hleftFuel hrightFuel hleftSpineValid
    hrightSpineValid hleftSupport hrightSupport hleftContext
    hrightContext hleftObservable
  rcases
      executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_of_valid_normal_runtimeSpine_support_context_fuel_ge_size
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftInitialSpine rightInitialSpine
        variableValues hschema (SelectionSet.size left + 1) parentType
        leftVariableDefinitions left fuel parentType targetParent
        leftProbeField rightProbeField targetLeftArguments
        targetRightArguments leftRuntime rightRuntime FieldPairProbeTag.left
        leftCurrentSelectionSet leftSpine (by omega) hleftFuel
        hleftValid hleftFree hleftNormal hleftSpineValid hleftSupport
        (fun _hobject => hleftContext)
        (fun hnonObject => by
          rw [hobject] at hnonObject
          simp at hnonObject) with
    ⟨leftFields, leftErrors, hleftResponse⟩
  rcases
      executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_of_valid_normal_runtimeSpine_support_context_fuel_ge_size
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftInitialSpine rightInitialSpine
        variableValues hschema (SelectionSet.size right + 1) parentType
        rightVariableDefinitions right fuel parentType targetParent
        leftProbeField rightProbeField targetLeftArguments
        targetRightArguments leftRuntime rightRuntime FieldPairProbeTag.right
        rightCurrentSelectionSet rightSpine (by omega) hrightFuel
        hrightValid hrightFree hrightNormal hrightSpineValid hrightSupport
        (fun _hobject => hrightContext)
        (fun hnonObject => by
          rw [hobject] at hnonObject
          simp at hnonObject) with
    ⟨rightFields, rightErrors, hrightResponse⟩
  have hdataNot :
      ¬ Execution.ResponseValue.semanticEquivalent
        (Execution.executeSelectionSetAsResponse schema
          (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
            (fieldPairSelectedPathProbeResolvers schema
              leftInitialSelectionSet rightInitialSelectionSet
              leftInitialSpine rightInitialSpine targetParent leftProbeField
              rightProbeField targetLeftArguments targetRightArguments
              leftRuntime rightRuntime)
            targetParent leftProbeField rightProbeField targetLeftArguments
            targetRightArguments)
          variableValues (fuel + 1) parentType
          (projectionTargetResolverValue
            (.object parentType
              (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
                leftCurrentSelectionSet leftSpine)))
          left).data
        (Execution.executeSelectionSetAsResponse schema
          (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
            (fieldPairSelectedPathProbeResolvers schema
              leftInitialSelectionSet rightInitialSelectionSet
              leftInitialSpine rightInitialSpine targetParent leftProbeField
              rightProbeField targetLeftArguments targetRightArguments
              leftRuntime rightRuntime)
            targetParent leftProbeField rightProbeField targetLeftArguments
            targetRightArguments)
          variableValues (fuel + 1) parentType
          (projectionTargetResolverValue
            (.object parentType
              (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                rightCurrentSelectionSet rightSpine)))
          right).data :=
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_left_observable_leaf_right_normal_of_valid_normal_runtimeSpine
      (schema := schema)
      (leftVariableDefinitions := leftVariableDefinitions)
      (rightVariableDefinitions := rightVariableDefinitions)
      rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet leftInitialSpine
      rightInitialSpine leftSpine rightSpine variableValues fuel
      targetParent leftProbeField rightProbeField parentType parentType
      parentType parentType targetLeftArguments targetRightArguments
      leftRuntime rightRuntime hschema hleftValid hrightValid hleftFree
      hrightFree hleftNormal hrightNormal hobject hobject hleftFuel
      hrightFuel hleftSpineValid hrightSpineValid hleftSupport
      hrightSupport hleftContext hrightContext hleftObservable
  refine
    ⟨typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject,
      leftFields, leftErrors, rightFields, rightErrors, hleftResponse,
      hrightResponse, ?_⟩
  intro hobjects
  exact hdataNot (by simpa [hleftResponse, hrightResponse] using hobjects)

theorem selectedPathTaggedSelectionSetsResponseDiffWitness_of_left_objectOutput_leaf_right_objectOutputPath_valid_normal_runtimeSpineExists
    (schema : Schema)
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftProbeField rightProbeField parentType : Name)
    (targetLeftArguments targetRightArguments : List Argument)
    (leftRuntime rightRuntime : Name) {left right : List Selection} {responseName : Name}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions parentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> objectTypeNameBool schema parentType = true
      -> selectionSetDeepProbeFuel schema parentType left ≤ fuel
      -> selectionSetDeepProbeFuel schema parentType right ≤ fuel
      -> PathLocalSupportValidNormal schema parentType leftCurrentSelectionSet
      -> PathLocalSupportValidNormal schema parentType rightCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext left leftCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext right rightCurrentSelectionSet
      -> NormalSelectionSetObjectOutputObservableResponsePath schema parentType
          left [responseName]
      -> NormalSelectionSetObjectOutputObservableResponsePath schema parentType
          right [responseName]
      -> ∃ leftSpine rightSpine,
          SelectedFieldSpineRuntimeValid schema parentType parentType leftSpine
          ∧ SelectedFieldSpineRuntimeValid schema parentType parentType rightSpine
          ∧ SelectedPathTaggedSelectionSetsResponseDiffWitness schema
              rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
              leftInitialSpine rightInitialSpine variableValues (fuel + 1)
              parentType parentType targetParent leftProbeField rightProbeField
              targetLeftArguments targetRightArguments leftRuntime rightRuntime
              leftCurrentSelectionSet rightCurrentSelectionSet leftSpine
              rightSpine left right := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hobject hleftFuel hrightFuel hleftSupport
    hrightSupport hleftContext hrightContext hleftPath hrightPath
  rcases
      selectedFieldSpineRuntimeValid_exists_of_objectOutputObservableResponsePath_valid_normal
        hleftPath hleftValid hleftNormal with
    ⟨leftSpine, hleftSpineValid, _hleftObservableSpine⟩
  rcases
      selectedFieldSpineRuntimeValid_exists_of_objectOutputObservableResponsePath_valid_normal
        hrightPath hrightValid hrightNormal with
    ⟨rightSpine, hrightSpineValid, _hrightObservableSpine⟩
  refine ⟨leftSpine, rightSpine, hleftSpineValid, hrightSpineValid, ?_⟩
  exact
    selectedPathTaggedSelectionSetsResponseDiffWitness_of_left_observable_leaf_right_normal_valid_normal_runtimeSpine
      (schema := schema)
      (leftVariableDefinitions := leftVariableDefinitions)
      (rightVariableDefinitions := rightVariableDefinitions)
      rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet leftInitialSpine
      rightInitialSpine leftSpine rightSpine variableValues fuel
      targetParent leftProbeField rightProbeField parentType
      targetLeftArguments targetRightArguments leftRuntime rightRuntime
      hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
      hrightNormal hobject hleftFuel hrightFuel hleftSpineValid
      hrightSpineValid hleftSupport hrightSupport hleftContext
      hrightContext hleftPath.to_observable

theorem selectedPathTaggedSelectionSetsResponseDiffWitness_of_objectOutput_sameField_childWitnessExists_valid_normal
    (schema : Schema)
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftProbeField rightProbeField parentType : Name)
    (targetLeftArguments targetRightArguments : List Argument)
    (leftRuntime rightRuntime : Name) {left right : List Selection}
    {responseName fieldName : Name} {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions parentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> objectTypeNameBool schema parentType = true
      -> selectionSetDeepProbeFuel schema parentType left ≤ fuel
      -> selectionSetDeepProbeFuel schema parentType right ≤ fuel
      -> PathLocalSupportValidNormal schema parentType leftCurrentSelectionSet
      -> PathLocalSupportValidNormal schema parentType rightCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext left leftCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext right rightCurrentSelectionSet
      -> Selection.field responseName fieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName fieldName rightArguments rightDirectives
            rightChildSelectionSet
          ∈ right
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> objectTypeNameBool schema fieldDefinition.outputType.namedType = true
      -> (∃ leftChildSpine rightChildSpine,
            SelectedFieldSpineRuntimeValid schema
              fieldDefinition.outputType.namedType
              fieldDefinition.outputType.namedType leftChildSpine
            ∧ SelectedFieldSpineRuntimeValid schema
                fieldDefinition.outputType.namedType
                fieldDefinition.outputType.namedType rightChildSpine
            ∧ SelectedPathTaggedSelectionSetsResponseDiffWitness schema
                rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
                leftInitialSpine rightInitialSpine variableValues
                (fuel - leafProbeFuel fieldDefinition.outputType)
                fieldDefinition.outputType.namedType
                fieldDefinition.outputType.namedType targetParent leftProbeField
                rightProbeField targetLeftArguments targetRightArguments
                leftRuntime rightRuntime
                (fieldPairPathLocalNextSelectionSet schema parentType
                  fieldDefinition.outputType.namedType fieldName leftArguments
                  leftCurrentSelectionSet)
                (fieldPairPathLocalNextSelectionSet schema parentType
                  fieldDefinition.outputType.namedType fieldName rightArguments
                  rightCurrentSelectionSet)
                leftChildSpine rightChildSpine leftChildSelectionSet
                rightChildSelectionSet)
      -> ∃ leftSpine rightSpine,
          SelectedFieldSpineRuntimeValid schema parentType parentType leftSpine
          ∧ SelectedFieldSpineRuntimeValid schema parentType parentType rightSpine
          ∧ SelectedPathTaggedSelectionSetsResponseDiffWitness schema
              rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
              leftInitialSpine rightInitialSpine variableValues (fuel + 1)
              parentType parentType targetParent leftProbeField rightProbeField
              targetLeftArguments targetRightArguments leftRuntime rightRuntime
              leftCurrentSelectionSet rightCurrentSelectionSet leftSpine
              rightSpine left right := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hobject hleftFuel hrightFuel hleftSupport
    hrightSupport hleftContext hrightContext hleftMem hrightMem hlookup
    hobjectOutput hchildExists
  rcases hchildExists with
    ⟨leftChildSpine, rightChildSpine, hleftChildSpineValid,
      hrightChildSpineValid, hchildWitness⟩
  let leftSpine : List NormalSelectionSetObservableFieldStep :=
    { responseName := responseName, fieldName := fieldName,
      arguments := leftArguments,
      childRuntime := some fieldDefinition.outputType.namedType } ::
      leftChildSpine
  let rightSpine : List NormalSelectionSetObservableFieldStep :=
    { responseName := responseName, fieldName := fieldName,
      arguments := rightArguments,
      childRuntime := some fieldDefinition.outputType.namedType } ::
      rightChildSpine
  have hcomposite :
      (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool
        schema = true :=
    typeRef_named_isCompositeBool_true_of_objectTypeNameBool hobjectOutput
  have hleftSpineValid :
      SelectedFieldSpineRuntimeValid schema parentType parentType
        leftSpine :=
    SelectedFieldSpineRuntimeValid.objectChild hobject hlookup
      hcomposite hleftChildSpineValid
  have hrightSpineValid :
      SelectedFieldSpineRuntimeValid schema parentType parentType
        rightSpine :=
    SelectedFieldSpineRuntimeValid.objectChild hobject hlookup
      hcomposite hrightChildSpineValid
  refine ⟨leftSpine, rightSpine, hleftSpineValid, hrightSpineValid, ?_⟩
  simpa [leftSpine, rightSpine] using
    selectedPathTaggedSelectionSetsResponseDiffWitness_of_objectOutput_sameField_childWitness_valid_normal_alignedSpine
      (schema := schema)
      (leftVariableDefinitions := leftVariableDefinitions)
      (rightVariableDefinitions := rightVariableDefinitions)
      rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet leftInitialSpine
      rightInitialSpine leftChildSpine rightChildSpine variableValues
      fuel targetParent leftProbeField rightProbeField parentType
      targetLeftArguments targetRightArguments leftRuntime rightRuntime
      hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
      hrightNormal hobject hleftFuel hrightFuel hleftChildSpineValid
      hrightChildSpineValid hleftSupport hrightSupport hleftContext
      hrightContext hleftMem hrightMem hlookup hobjectOutput
      hchildWitness

theorem selectedPathTaggedSelectionSetsResponseDiffWitness_of_objectOutput_sameField_childLeafPath_valid_normal
    (schema : Schema)
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftProbeField rightProbeField parentType : Name)
    (targetLeftArguments targetRightArguments : List Argument)
    (leftRuntime rightRuntime : Name) {left right : List Selection}
    {responseName fieldName childResponseName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions parentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> objectTypeNameBool schema parentType = true
      -> selectionSetDeepProbeFuel schema parentType left ≤ fuel
      -> selectionSetDeepProbeFuel schema parentType right ≤ fuel
      -> PathLocalSupportValidNormal schema parentType leftCurrentSelectionSet
      -> PathLocalSupportValidNormal schema parentType rightCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext left leftCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext right rightCurrentSelectionSet
      -> Selection.field responseName fieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName fieldName rightArguments rightDirectives
            rightChildSelectionSet
          ∈ right
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> objectTypeNameBool schema fieldDefinition.outputType.namedType = true
      -> NormalSelectionSetObjectOutputObservableResponsePath schema
          fieldDefinition.outputType.namedType leftChildSelectionSet
          [childResponseName]
      -> NormalSelectionSetObjectOutputObservableResponsePath schema
          fieldDefinition.outputType.namedType rightChildSelectionSet
          [childResponseName]
      -> ∃ leftSpine rightSpine,
          SelectedFieldSpineRuntimeValid schema parentType parentType leftSpine
          ∧ SelectedFieldSpineRuntimeValid schema parentType parentType rightSpine
          ∧ SelectedPathTaggedSelectionSetsResponseDiffWitness schema
              rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
              leftInitialSpine rightInitialSpine variableValues (fuel + 1)
              parentType parentType targetParent leftProbeField rightProbeField
              targetLeftArguments targetRightArguments leftRuntime rightRuntime
              leftCurrentSelectionSet rightCurrentSelectionSet leftSpine
              rightSpine left right := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hobject hleftFuel hrightFuel hleftSupport
    hrightSupport hleftContext hrightContext hleftMem hrightMem hlookup
    hobjectOutput hleftChildPath hrightChildPath
  let childFuel := fuel - leafProbeFuel fieldDefinition.outputType - 1
  have hleftChildValid :
      Validation.selectionSetValid schema leftVariableDefinitions
        fieldDefinition.outputType.namedType leftChildSelectionSet :=
    selectionSetValid_object_field_child_of_mem_lookup hleftValid hleftMem
      hlookup hobjectOutput
  have hrightChildValid :
      Validation.selectionSetValid schema rightVariableDefinitions
        fieldDefinition.outputType.namedType rightChildSelectionSet :=
    selectionSetValid_object_field_child_of_mem_lookup hrightValid hrightMem
      hlookup hobjectOutput
  have hleftChildFree : selectionSetDirectiveFree leftChildSelectionSet :=
    selectionSetDirectiveFree_field_child_of_mem hleftFree hleftMem
  have hrightChildFree : selectionSetDirectiveFree rightChildSelectionSet :=
    selectionSetDirectiveFree_field_child_of_mem hrightFree hrightMem
  have hleftChildNormal :
      selectionSetNormal schema fieldDefinition.outputType.namedType
        leftChildSelectionSet :=
    selectionSetNormal_field_child_of_mem_lookup hleftNormal hleftMem
      hlookup
  have hrightChildNormal :
      selectionSetNormal schema fieldDefinition.outputType.namedType
        rightChildSelectionSet :=
    selectionSetNormal_field_child_of_mem_lookup hrightNormal hrightMem
      hlookup
  have hleftChildSupport :
      PathLocalSupportValidNormal schema
        fieldDefinition.outputType.namedType
        (fieldPairPathLocalNextSelectionSet schema parentType
          fieldDefinition.outputType.namedType fieldName leftArguments
          leftCurrentSelectionSet) :=
    hleftSupport.fieldPairPathLocalNextSelectionSet_of_object_output hobject
      hobjectOutput hlookup rfl
  have hrightChildSupport :
      PathLocalSupportValidNormal schema
        fieldDefinition.outputType.namedType
        (fieldPairPathLocalNextSelectionSet schema parentType
          fieldDefinition.outputType.namedType fieldName rightArguments
          rightCurrentSelectionSet) :=
    hrightSupport.fieldPairPathLocalNextSelectionSet_of_object_output hobject
      hobjectOutput hlookup rfl
  have hleftAllFields : selectionsAllFields leftChildSelectionSet :=
    selectionSetNormal_allFields_of_object hleftChildNormal hobjectOutput
  have hrightAllFields : selectionsAllFields rightChildSelectionSet :=
    selectionSetNormal_allFields_of_object hrightChildNormal hobjectOutput
  have hleftPruned :
      runtimePrunedSelectionSet schema
          fieldDefinition.outputType.namedType leftChildSelectionSet =
        leftChildSelectionSet :=
    runtimePrunedSelectionSet_eq_self_of_allFields schema
      fieldDefinition.outputType.namedType hleftAllFields
  have hrightPruned :
      runtimePrunedSelectionSet schema
          fieldDefinition.outputType.namedType rightChildSelectionSet =
        rightChildSelectionSet :=
    runtimePrunedSelectionSet_eq_self_of_allFields schema
      fieldDefinition.outputType.namedType hrightAllFields
  have hleftChildContext :
      PathLocalSelectionSetCurrentContext leftChildSelectionSet
        (fieldPairPathLocalNextSelectionSet schema parentType
          fieldDefinition.outputType.namedType fieldName leftArguments
          leftCurrentSelectionSet) :=
    PathLocalSelectionSetCurrentContext.fieldPairPathLocalNextSelectionSet_field_child
      (schema := schema) (currentRuntimeType := parentType)
      (childRuntimeType := fieldDefinition.outputType.namedType)
      (targetField := fieldName) (responseName := responseName)
      (targetArguments := leftArguments) (arguments := leftArguments)
      (directives := leftDirectives) (selectionSet := left)
      (childSelectionSet := leftChildSelectionSet)
      (currentSelectionSet := leftCurrentSelectionSet) hleftContext
      hleftMem (argumentsEquivalent_refl_forSyntaxDiff leftArguments)
      hleftPruned
  have hrightChildContext :
      PathLocalSelectionSetCurrentContext rightChildSelectionSet
        (fieldPairPathLocalNextSelectionSet schema parentType
          fieldDefinition.outputType.namedType fieldName rightArguments
          rightCurrentSelectionSet) :=
    PathLocalSelectionSetCurrentContext.fieldPairPathLocalNextSelectionSet_field_child
      (schema := schema) (currentRuntimeType := parentType)
      (childRuntimeType := fieldDefinition.outputType.namedType)
      (targetField := fieldName) (responseName := responseName)
      (targetArguments := rightArguments) (arguments := rightArguments)
      (directives := rightDirectives) (selectionSet := right)
      (childSelectionSet := rightChildSelectionSet)
      (currentSelectionSet := rightCurrentSelectionSet) hrightContext
      hrightMem (argumentsEquivalent_refl_forSyntaxDiff rightArguments)
      hrightPruned
  have hleftChildFuel :
      selectionSetDeepProbeFuel schema
          fieldDefinition.outputType.namedType leftChildSelectionSet ≤
        childFuel := by
    have hlocal :=
      selectionSetDeepProbeFuel_field_mem schema parentType left
        responseName fieldName leftArguments leftDirectives
        leftChildSelectionSet fieldDefinition hleftMem hlookup
    dsimp [childFuel]
    omega
  have hrightChildFuel :
      selectionSetDeepProbeFuel schema
          fieldDefinition.outputType.namedType rightChildSelectionSet ≤
        childFuel := by
    have hlocal :=
      selectionSetDeepProbeFuel_field_mem schema parentType right
        responseName fieldName rightArguments rightDirectives
        rightChildSelectionSet fieldDefinition hrightMem hlookup
    dsimp [childFuel]
    omega
  have hchildFuelEq :
      childFuel + 1 = fuel - leafProbeFuel fieldDefinition.outputType := by
    have hlocal :=
      selectionSetDeepProbeFuel_field_mem schema parentType left
        responseName fieldName leftArguments leftDirectives
        leftChildSelectionSet fieldDefinition hleftMem hlookup
    dsimp [childFuel]
    omega
  have hchildExistsRaw :=
    selectedPathTaggedSelectionSetsResponseDiffWitness_of_left_objectOutput_leaf_right_objectOutputPath_valid_normal_runtimeSpineExists
      (schema := schema)
      (leftVariableDefinitions := leftVariableDefinitions)
      (rightVariableDefinitions := rightVariableDefinitions)
      rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      (fieldPairPathLocalNextSelectionSet schema parentType
        fieldDefinition.outputType.namedType fieldName leftArguments
        leftCurrentSelectionSet)
      (fieldPairPathLocalNextSelectionSet schema parentType
        fieldDefinition.outputType.namedType fieldName rightArguments
        rightCurrentSelectionSet)
      leftInitialSpine rightInitialSpine variableValues childFuel
      targetParent leftProbeField rightProbeField
      fieldDefinition.outputType.namedType targetLeftArguments
      targetRightArguments leftRuntime rightRuntime hschema hleftChildValid
      hrightChildValid hleftChildFree hrightChildFree hleftChildNormal
      hrightChildNormal hobjectOutput hleftChildFuel hrightChildFuel
      hleftChildSupport hrightChildSupport hleftChildContext
      hrightChildContext hleftChildPath hrightChildPath
  have hchildExists :
      ∃ leftChildSpine rightChildSpine,
        SelectedFieldSpineRuntimeValid schema
          fieldDefinition.outputType.namedType
          fieldDefinition.outputType.namedType leftChildSpine
          ∧ SelectedFieldSpineRuntimeValid schema
            fieldDefinition.outputType.namedType
            fieldDefinition.outputType.namedType rightChildSpine
          ∧ SelectedPathTaggedSelectionSetsResponseDiffWitness schema
            rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
            leftInitialSpine rightInitialSpine variableValues
            (fuel - leafProbeFuel fieldDefinition.outputType)
            fieldDefinition.outputType.namedType
            fieldDefinition.outputType.namedType targetParent leftProbeField
            rightProbeField targetLeftArguments targetRightArguments
            leftRuntime rightRuntime
            (fieldPairPathLocalNextSelectionSet schema parentType
              fieldDefinition.outputType.namedType fieldName leftArguments
              leftCurrentSelectionSet)
            (fieldPairPathLocalNextSelectionSet schema parentType
              fieldDefinition.outputType.namedType fieldName rightArguments
              rightCurrentSelectionSet)
            leftChildSpine rightChildSpine leftChildSelectionSet
            rightChildSelectionSet := by
    simpa [hchildFuelEq] using hchildExistsRaw
  exact
    selectedPathTaggedSelectionSetsResponseDiffWitness_of_objectOutput_sameField_childWitnessExists_valid_normal
      (schema := schema)
      (leftVariableDefinitions := leftVariableDefinitions)
      (rightVariableDefinitions := rightVariableDefinitions)
      rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet leftInitialSpine
      rightInitialSpine variableValues fuel targetParent leftProbeField
      rightProbeField parentType targetLeftArguments targetRightArguments
      leftRuntime rightRuntime hschema hleftValid hrightValid hleftFree
      hrightFree hleftNormal hrightNormal hobject hleftFuel hrightFuel
      hleftSupport hrightSupport hleftContext hrightContext hleftMem
      hrightMem hlookup hobjectOutput hchildExists

theorem selectedPathTaggedSelectionSetsResponseDiffWitness_of_objectOutput_sameField_left_observable_responseName_absent_valid_normal
    (schema : Schema)
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftProbeField rightProbeField parentType : Name)
    (targetLeftArguments targetRightArguments : List Argument)
    (leftRuntime rightRuntime : Name) {left right : List Selection}
    {responseName fieldName childResponseName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {fieldDefinition : FieldDefinition} {childPathTail : List Name}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions parentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> objectTypeNameBool schema parentType = true
      -> selectionSetDeepProbeFuel schema parentType left ≤ fuel
      -> selectionSetDeepProbeFuel schema parentType right ≤ fuel
      -> PathLocalSupportValidNormal schema parentType leftCurrentSelectionSet
      -> PathLocalSupportValidNormal schema parentType rightCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext left leftCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext right rightCurrentSelectionSet
      -> Selection.field responseName fieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName fieldName rightArguments rightDirectives
            rightChildSelectionSet
          ∈ right
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> objectTypeNameBool schema fieldDefinition.outputType.namedType = true
      -> NormalSelectionSetObservableResponsePath schema
          fieldDefinition.outputType.namedType leftChildSelectionSet
          (childResponseName :: childPathTail)
      -> childResponseName ∉ rightChildSelectionSet.filterMap Selection.responseName?
      -> ∃ leftSpine rightSpine,
          SelectedFieldSpineRuntimeValid schema parentType parentType leftSpine
          ∧ SelectedFieldSpineRuntimeValid schema parentType parentType rightSpine
          ∧ SelectedPathTaggedSelectionSetsResponseDiffWitness schema
              rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
              leftInitialSpine rightInitialSpine variableValues (fuel + 1)
              parentType parentType targetParent leftProbeField rightProbeField
              targetLeftArguments targetRightArguments leftRuntime rightRuntime
              leftCurrentSelectionSet rightCurrentSelectionSet leftSpine
              rightSpine left right := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hobject hleftFuel hrightFuel hleftSupport
    hrightSupport hleftContext hrightContext hleftMem hrightMem hlookup
    hobjectOutput hleftObservable hrightNoResponseName
  let childFuel := fuel - leafProbeFuel fieldDefinition.outputType - 1
  have hleftChildValid :
      Validation.selectionSetValid schema leftVariableDefinitions
        fieldDefinition.outputType.namedType leftChildSelectionSet :=
    selectionSetValid_object_field_child_of_mem_lookup hleftValid hleftMem
      hlookup hobjectOutput
  have hrightChildValid :
      Validation.selectionSetValid schema rightVariableDefinitions
        fieldDefinition.outputType.namedType rightChildSelectionSet :=
    selectionSetValid_object_field_child_of_mem_lookup hrightValid hrightMem
      hlookup hobjectOutput
  have hleftChildFree : selectionSetDirectiveFree leftChildSelectionSet :=
    selectionSetDirectiveFree_field_child_of_mem hleftFree hleftMem
  have hrightChildFree : selectionSetDirectiveFree rightChildSelectionSet :=
    selectionSetDirectiveFree_field_child_of_mem hrightFree hrightMem
  have hleftChildNormal :
      selectionSetNormal schema fieldDefinition.outputType.namedType
        leftChildSelectionSet :=
    selectionSetNormal_field_child_of_mem_lookup hleftNormal hleftMem
      hlookup
  have hrightChildNormal :
      selectionSetNormal schema fieldDefinition.outputType.namedType
        rightChildSelectionSet :=
    selectionSetNormal_field_child_of_mem_lookup hrightNormal hrightMem
      hlookup
  have hleftChildSupport :
      PathLocalSupportValidNormal schema
        fieldDefinition.outputType.namedType
        (fieldPairPathLocalNextSelectionSet schema parentType
          fieldDefinition.outputType.namedType fieldName leftArguments
          leftCurrentSelectionSet) :=
    hleftSupport.fieldPairPathLocalNextSelectionSet_of_object_output hobject
      hobjectOutput hlookup rfl
  have hrightChildSupport :
      PathLocalSupportValidNormal schema
        fieldDefinition.outputType.namedType
        (fieldPairPathLocalNextSelectionSet schema parentType
          fieldDefinition.outputType.namedType fieldName rightArguments
          rightCurrentSelectionSet) :=
    hrightSupport.fieldPairPathLocalNextSelectionSet_of_object_output hobject
      hobjectOutput hlookup rfl
  have hleftAllFields : selectionsAllFields leftChildSelectionSet :=
    selectionSetNormal_allFields_of_object hleftChildNormal hobjectOutput
  have hrightAllFields : selectionsAllFields rightChildSelectionSet :=
    selectionSetNormal_allFields_of_object hrightChildNormal hobjectOutput
  have hleftPruned :
      runtimePrunedSelectionSet schema
          fieldDefinition.outputType.namedType leftChildSelectionSet =
        leftChildSelectionSet :=
    runtimePrunedSelectionSet_eq_self_of_allFields schema
      fieldDefinition.outputType.namedType hleftAllFields
  have hrightPruned :
      runtimePrunedSelectionSet schema
          fieldDefinition.outputType.namedType rightChildSelectionSet =
        rightChildSelectionSet :=
    runtimePrunedSelectionSet_eq_self_of_allFields schema
      fieldDefinition.outputType.namedType hrightAllFields
  have hleftChildContext :
      PathLocalSelectionSetCurrentContext leftChildSelectionSet
        (fieldPairPathLocalNextSelectionSet schema parentType
          fieldDefinition.outputType.namedType fieldName leftArguments
          leftCurrentSelectionSet) :=
    PathLocalSelectionSetCurrentContext.fieldPairPathLocalNextSelectionSet_field_child
      (schema := schema) (currentRuntimeType := parentType)
      (childRuntimeType := fieldDefinition.outputType.namedType)
      (targetField := fieldName) (responseName := responseName)
      (targetArguments := leftArguments) (arguments := leftArguments)
      (directives := leftDirectives) (selectionSet := left)
      (childSelectionSet := leftChildSelectionSet)
      (currentSelectionSet := leftCurrentSelectionSet) hleftContext
      hleftMem (argumentsEquivalent_refl_forSyntaxDiff leftArguments)
      hleftPruned
  have hrightChildContext :
      PathLocalSelectionSetCurrentContext rightChildSelectionSet
        (fieldPairPathLocalNextSelectionSet schema parentType
          fieldDefinition.outputType.namedType fieldName rightArguments
          rightCurrentSelectionSet) :=
    PathLocalSelectionSetCurrentContext.fieldPairPathLocalNextSelectionSet_field_child
      (schema := schema) (currentRuntimeType := parentType)
      (childRuntimeType := fieldDefinition.outputType.namedType)
      (targetField := fieldName) (responseName := responseName)
      (targetArguments := rightArguments) (arguments := rightArguments)
      (directives := rightDirectives) (selectionSet := right)
      (childSelectionSet := rightChildSelectionSet)
      (currentSelectionSet := rightCurrentSelectionSet) hrightContext
      hrightMem (argumentsEquivalent_refl_forSyntaxDiff rightArguments)
      hrightPruned
  have hleftChildFuel :
      selectionSetDeepProbeFuel schema
          fieldDefinition.outputType.namedType leftChildSelectionSet ≤
        childFuel := by
    have hlocal :=
      selectionSetDeepProbeFuel_field_mem schema parentType left
        responseName fieldName leftArguments leftDirectives
        leftChildSelectionSet fieldDefinition hleftMem hlookup
    dsimp [childFuel]
    omega
  have hrightChildFuel :
      selectionSetDeepProbeFuel schema
          fieldDefinition.outputType.namedType rightChildSelectionSet ≤
        childFuel := by
    have hlocal :=
      selectionSetDeepProbeFuel_field_mem schema parentType right
        responseName fieldName rightArguments rightDirectives
        rightChildSelectionSet fieldDefinition hrightMem hlookup
    dsimp [childFuel]
    omega
  have hchildFuelEq :
      childFuel + 1 = fuel - leafProbeFuel fieldDefinition.outputType := by
    have hlocal :=
      selectionSetDeepProbeFuel_field_mem schema parentType left
        responseName fieldName leftArguments leftDirectives
        leftChildSelectionSet fieldDefinition hleftMem hlookup
    dsimp [childFuel]
    omega
  rcases
      pathLocalSelectionSetObservableFieldSpineAtSelectedRuntime_of_observableResponsePath_valid_normal
        hleftObservable hleftChildValid hleftChildNormal with
    ⟨childRuntime, childSpine, hinclude, hobservableSpine⟩
  have hchildRuntimeEq :
      childRuntime = fieldDefinition.outputType.namedType :=
    typeIncludesObjectBool_eq_of_objectTypeNameBool_true schema
      hobjectOutput hinclude
  subst childRuntime
  have hchildSpineValid :
      SelectedFieldSpineRuntimeValid schema
        fieldDefinition.outputType.namedType
        fieldDefinition.outputType.namedType childSpine :=
    selectedFieldSpineRuntimeValid_of_observableFieldSpineAtSelectedRuntime
      (hobservableSpine
        (fieldPairPathLocalNextSelectionSet schema parentType
          fieldDefinition.outputType.namedType fieldName leftArguments
          leftCurrentSelectionSet))
  have hchildExistsRaw :
      SelectedPathTaggedSelectionSetsResponseDiffWitness schema
        rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
        leftInitialSpine rightInitialSpine variableValues (childFuel + 1)
        fieldDefinition.outputType.namedType
        fieldDefinition.outputType.namedType targetParent leftProbeField
        rightProbeField targetLeftArguments targetRightArguments
        leftRuntime rightRuntime
        (fieldPairPathLocalNextSelectionSet schema parentType
          fieldDefinition.outputType.namedType fieldName leftArguments
          leftCurrentSelectionSet)
        (fieldPairPathLocalNextSelectionSet schema parentType
          fieldDefinition.outputType.namedType fieldName rightArguments
          rightCurrentSelectionSet)
        childSpine childSpine leftChildSelectionSet
        rightChildSelectionSet :=
    selectedPathTaggedSelectionSetsResponseDiffWitness_of_left_observable_responseName_absent_valid_normal_runtimeSpine
      (schema := schema)
      (leftVariableDefinitions := leftVariableDefinitions)
      (rightVariableDefinitions := rightVariableDefinitions)
      rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      (fieldPairPathLocalNextSelectionSet schema parentType
        fieldDefinition.outputType.namedType fieldName leftArguments
        leftCurrentSelectionSet)
      (fieldPairPathLocalNextSelectionSet schema parentType
        fieldDefinition.outputType.namedType fieldName rightArguments
        rightCurrentSelectionSet)
      leftInitialSpine rightInitialSpine childSpine childSpine
      variableValues childFuel targetParent leftProbeField rightProbeField
      fieldDefinition.outputType.namedType targetLeftArguments
      targetRightArguments leftRuntime rightRuntime hschema hleftChildValid
      hrightChildValid hleftChildFree hrightChildFree hleftChildNormal
      hrightChildNormal hobjectOutput hleftChildFuel hrightChildFuel
      hchildSpineValid hchildSpineValid hleftChildSupport
      hrightChildSupport hleftChildContext hrightChildContext
      hleftObservable hrightNoResponseName
  have hchildExists :
      ∃ leftChildSpine rightChildSpine,
        SelectedFieldSpineRuntimeValid schema
          fieldDefinition.outputType.namedType
          fieldDefinition.outputType.namedType leftChildSpine
          ∧ SelectedFieldSpineRuntimeValid schema
            fieldDefinition.outputType.namedType
            fieldDefinition.outputType.namedType rightChildSpine
          ∧ SelectedPathTaggedSelectionSetsResponseDiffWitness schema
            rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
            leftInitialSpine rightInitialSpine variableValues
            (fuel - leafProbeFuel fieldDefinition.outputType)
            fieldDefinition.outputType.namedType
            fieldDefinition.outputType.namedType targetParent leftProbeField
            rightProbeField targetLeftArguments targetRightArguments
            leftRuntime rightRuntime
            (fieldPairPathLocalNextSelectionSet schema parentType
              fieldDefinition.outputType.namedType fieldName leftArguments
              leftCurrentSelectionSet)
            (fieldPairPathLocalNextSelectionSet schema parentType
              fieldDefinition.outputType.namedType fieldName rightArguments
              rightCurrentSelectionSet)
            leftChildSpine rightChildSpine leftChildSelectionSet
            rightChildSelectionSet := by
    exact
      ⟨childSpine, childSpine, hchildSpineValid, hchildSpineValid,
        by simpa [hchildFuelEq] using hchildExistsRaw⟩
  exact
    selectedPathTaggedSelectionSetsResponseDiffWitness_of_objectOutput_sameField_childWitnessExists_valid_normal
      (schema := schema)
      (leftVariableDefinitions := leftVariableDefinitions)
      (rightVariableDefinitions := rightVariableDefinitions)
      rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet leftInitialSpine
      rightInitialSpine variableValues fuel targetParent leftProbeField
      rightProbeField parentType targetLeftArguments targetRightArguments
      leftRuntime rightRuntime hschema hleftValid hrightValid hleftFree
      hrightFree hleftNormal hrightNormal hobject hleftFuel hrightFuel
      hleftSupport hrightSupport hleftContext hrightContext hleftMem
      hrightMem hlookup hobjectOutput hchildExists

theorem selectedPathTaggedSelectionSetsResponseDiffWitnessRoot_of_objectOutput_sameField_left_observable_responseName_absent_valid_normal
    (schema : Schema)
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftProbeField rightProbeField parentType : Name)
    (targetLeftArguments targetRightArguments : List Argument)
    (leftRuntime rightRuntime : Name) {left right : List Selection}
    {responseName fieldName childResponseName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {fieldDefinition : FieldDefinition} {childPathTail : List Name}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions parentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> objectTypeNameBool schema parentType = true
      -> selectionSetDeepProbeFuel schema parentType left ≤ fuel
      -> selectionSetDeepProbeFuel schema parentType right ≤ fuel
      -> PathLocalSupportValidNormal schema parentType leftCurrentSelectionSet
      -> PathLocalSupportValidNormal schema parentType rightCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext left leftCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext right rightCurrentSelectionSet
      -> Selection.field responseName fieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName fieldName rightArguments rightDirectives
            rightChildSelectionSet
          ∈ right
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> objectTypeNameBool schema fieldDefinition.outputType.namedType = true
      -> NormalSelectionSetObservableResponsePath schema
          fieldDefinition.outputType.namedType leftChildSelectionSet
          (childResponseName :: childPathTail)
      -> childResponseName ∉ rightChildSelectionSet.filterMap Selection.responseName?
      -> ∃ leftSpine rightSpine,
          SelectedFieldSpineRuntimeValid schema parentType parentType leftSpine
          ∧ SelectedFieldSpineRuntimeValid schema parentType parentType rightSpine
          ∧ SelectedPathTaggedSelectionSetsResponseDiffWitness schema
              rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
              leftSpine rightSpine variableValues (fuel + 1)
              parentType parentType targetParent leftProbeField rightProbeField
              targetLeftArguments targetRightArguments leftRuntime rightRuntime
              leftCurrentSelectionSet rightCurrentSelectionSet leftSpine
              rightSpine left right := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hobject hleftFuel hrightFuel hleftSupport
    hrightSupport hleftContext hrightContext hleftMem hrightMem hlookup
    hobjectOutput hleftObservable hrightNoResponseName
  let childFuel := fuel - leafProbeFuel fieldDefinition.outputType - 1
  have hleftChildValid :
      Validation.selectionSetValid schema leftVariableDefinitions
        fieldDefinition.outputType.namedType leftChildSelectionSet :=
    selectionSetValid_object_field_child_of_mem_lookup hleftValid hleftMem
      hlookup hobjectOutput
  have hrightChildValid :
      Validation.selectionSetValid schema rightVariableDefinitions
        fieldDefinition.outputType.namedType rightChildSelectionSet :=
    selectionSetValid_object_field_child_of_mem_lookup hrightValid hrightMem
      hlookup hobjectOutput
  have hleftChildFree : selectionSetDirectiveFree leftChildSelectionSet :=
    selectionSetDirectiveFree_field_child_of_mem hleftFree hleftMem
  have hrightChildFree : selectionSetDirectiveFree rightChildSelectionSet :=
    selectionSetDirectiveFree_field_child_of_mem hrightFree hrightMem
  have hleftChildNormal :
      selectionSetNormal schema fieldDefinition.outputType.namedType
        leftChildSelectionSet :=
    selectionSetNormal_field_child_of_mem_lookup hleftNormal hleftMem
      hlookup
  have hrightChildNormal :
      selectionSetNormal schema fieldDefinition.outputType.namedType
        rightChildSelectionSet :=
    selectionSetNormal_field_child_of_mem_lookup hrightNormal hrightMem
      hlookup
  have hleftChildSupport :
      PathLocalSupportValidNormal schema
        fieldDefinition.outputType.namedType
        (fieldPairPathLocalNextSelectionSet schema parentType
          fieldDefinition.outputType.namedType fieldName leftArguments
          leftCurrentSelectionSet) :=
    hleftSupport.fieldPairPathLocalNextSelectionSet_of_object_output hobject
      hobjectOutput hlookup rfl
  have hrightChildSupport :
      PathLocalSupportValidNormal schema
        fieldDefinition.outputType.namedType
        (fieldPairPathLocalNextSelectionSet schema parentType
          fieldDefinition.outputType.namedType fieldName rightArguments
          rightCurrentSelectionSet) :=
    hrightSupport.fieldPairPathLocalNextSelectionSet_of_object_output hobject
      hobjectOutput hlookup rfl
  have hleftAllFields : selectionsAllFields leftChildSelectionSet :=
    selectionSetNormal_allFields_of_object hleftChildNormal hobjectOutput
  have hrightAllFields : selectionsAllFields rightChildSelectionSet :=
    selectionSetNormal_allFields_of_object hrightChildNormal hobjectOutput
  have hleftPruned :
      runtimePrunedSelectionSet schema
          fieldDefinition.outputType.namedType leftChildSelectionSet =
        leftChildSelectionSet :=
    runtimePrunedSelectionSet_eq_self_of_allFields schema
      fieldDefinition.outputType.namedType hleftAllFields
  have hrightPruned :
      runtimePrunedSelectionSet schema
          fieldDefinition.outputType.namedType rightChildSelectionSet =
        rightChildSelectionSet :=
    runtimePrunedSelectionSet_eq_self_of_allFields schema
      fieldDefinition.outputType.namedType hrightAllFields
  have hleftChildContext :
      PathLocalSelectionSetCurrentContext leftChildSelectionSet
        (fieldPairPathLocalNextSelectionSet schema parentType
          fieldDefinition.outputType.namedType fieldName leftArguments
          leftCurrentSelectionSet) :=
    PathLocalSelectionSetCurrentContext.fieldPairPathLocalNextSelectionSet_field_child
      (schema := schema) (currentRuntimeType := parentType)
      (childRuntimeType := fieldDefinition.outputType.namedType)
      (targetField := fieldName) (responseName := responseName)
      (targetArguments := leftArguments) (arguments := leftArguments)
      (directives := leftDirectives) (selectionSet := left)
      (childSelectionSet := leftChildSelectionSet)
      (currentSelectionSet := leftCurrentSelectionSet) hleftContext
      hleftMem (argumentsEquivalent_refl_forSyntaxDiff leftArguments)
      hleftPruned
  have hrightChildContext :
      PathLocalSelectionSetCurrentContext rightChildSelectionSet
        (fieldPairPathLocalNextSelectionSet schema parentType
          fieldDefinition.outputType.namedType fieldName rightArguments
          rightCurrentSelectionSet) :=
    PathLocalSelectionSetCurrentContext.fieldPairPathLocalNextSelectionSet_field_child
      (schema := schema) (currentRuntimeType := parentType)
      (childRuntimeType := fieldDefinition.outputType.namedType)
      (targetField := fieldName) (responseName := responseName)
      (targetArguments := rightArguments) (arguments := rightArguments)
      (directives := rightDirectives) (selectionSet := right)
      (childSelectionSet := rightChildSelectionSet)
      (currentSelectionSet := rightCurrentSelectionSet) hrightContext
      hrightMem (argumentsEquivalent_refl_forSyntaxDiff rightArguments)
      hrightPruned
  have hleftChildFuel :
      selectionSetDeepProbeFuel schema
          fieldDefinition.outputType.namedType leftChildSelectionSet ≤
        childFuel := by
    have hlocal :=
      selectionSetDeepProbeFuel_field_mem schema parentType left
        responseName fieldName leftArguments leftDirectives
        leftChildSelectionSet fieldDefinition hleftMem hlookup
    dsimp [childFuel]
    omega
  have hrightChildFuel :
      selectionSetDeepProbeFuel schema
          fieldDefinition.outputType.namedType rightChildSelectionSet ≤
        childFuel := by
    have hlocal :=
      selectionSetDeepProbeFuel_field_mem schema parentType right
        responseName fieldName rightArguments rightDirectives
        rightChildSelectionSet fieldDefinition hrightMem hlookup
    dsimp [childFuel]
    omega
  have hchildFuelEq :
      childFuel + 1 = fuel - leafProbeFuel fieldDefinition.outputType := by
    have hlocal :=
      selectionSetDeepProbeFuel_field_mem schema parentType left
        responseName fieldName leftArguments leftDirectives
        leftChildSelectionSet fieldDefinition hleftMem hlookup
    dsimp [childFuel]
    omega
  rcases
      pathLocalSelectionSetObservableFieldSpineAtSelectedRuntime_of_observableResponsePath_valid_normal
        hleftObservable hleftChildValid hleftChildNormal with
    ⟨childRuntime, childSpine, hinclude, hobservableSpine⟩
  have hchildRuntimeEq :
      childRuntime = fieldDefinition.outputType.namedType :=
    typeIncludesObjectBool_eq_of_objectTypeNameBool_true schema
      hobjectOutput hinclude
  subst childRuntime
  let leftSpine : List NormalSelectionSetObservableFieldStep :=
    { responseName := responseName, fieldName := fieldName,
      arguments := leftArguments,
      childRuntime := some fieldDefinition.outputType.namedType } ::
      childSpine
  let rightSpine : List NormalSelectionSetObservableFieldStep :=
    { responseName := responseName, fieldName := fieldName,
      arguments := rightArguments,
      childRuntime := some fieldDefinition.outputType.namedType } ::
      childSpine
  have hchildSpineValid :
      SelectedFieldSpineRuntimeValid schema
        fieldDefinition.outputType.namedType
        fieldDefinition.outputType.namedType childSpine :=
    selectedFieldSpineRuntimeValid_of_observableFieldSpineAtSelectedRuntime
      (hobservableSpine
        (fieldPairPathLocalNextSelectionSet schema parentType
          fieldDefinition.outputType.namedType fieldName leftArguments
          leftCurrentSelectionSet))
  have hcomposite :
      (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool
        schema = true :=
    typeRef_named_isCompositeBool_true_of_objectTypeNameBool hobjectOutput
  have hleftSpineValid :
      SelectedFieldSpineRuntimeValid schema parentType parentType
        leftSpine :=
    SelectedFieldSpineRuntimeValid.objectChild hobject hlookup
      hcomposite hchildSpineValid
  have hrightSpineValid :
      SelectedFieldSpineRuntimeValid schema parentType parentType
        rightSpine :=
    SelectedFieldSpineRuntimeValid.objectChild hobject hlookup
      hcomposite hchildSpineValid
  have hchildWitnessRaw :
      SelectedPathTaggedSelectionSetsResponseDiffWitness schema
        rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
        leftSpine rightSpine variableValues (childFuel + 1)
        fieldDefinition.outputType.namedType
        fieldDefinition.outputType.namedType targetParent leftProbeField
        rightProbeField targetLeftArguments targetRightArguments
        leftRuntime rightRuntime
        (fieldPairPathLocalNextSelectionSet schema parentType
          fieldDefinition.outputType.namedType fieldName leftArguments
          leftCurrentSelectionSet)
        (fieldPairPathLocalNextSelectionSet schema parentType
          fieldDefinition.outputType.namedType fieldName rightArguments
          rightCurrentSelectionSet)
        childSpine childSpine leftChildSelectionSet
        rightChildSelectionSet :=
    selectedPathTaggedSelectionSetsResponseDiffWitness_of_left_observable_responseName_absent_valid_normal_runtimeSpine
      (schema := schema)
      (leftVariableDefinitions := leftVariableDefinitions)
      (rightVariableDefinitions := rightVariableDefinitions)
      rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      (fieldPairPathLocalNextSelectionSet schema parentType
        fieldDefinition.outputType.namedType fieldName leftArguments
        leftCurrentSelectionSet)
      (fieldPairPathLocalNextSelectionSet schema parentType
        fieldDefinition.outputType.namedType fieldName rightArguments
        rightCurrentSelectionSet)
      leftSpine rightSpine childSpine childSpine variableValues
      childFuel targetParent leftProbeField rightProbeField
      fieldDefinition.outputType.namedType targetLeftArguments
      targetRightArguments leftRuntime rightRuntime hschema hleftChildValid
      hrightChildValid hleftChildFree hrightChildFree hleftChildNormal
      hrightChildNormal hobjectOutput hleftChildFuel hrightChildFuel
      hchildSpineValid hchildSpineValid hleftChildSupport
      hrightChildSupport hleftChildContext hrightChildContext
      hleftObservable hrightNoResponseName
  have hchildWitness :
      SelectedPathTaggedSelectionSetsResponseDiffWitness schema
        rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
        leftSpine rightSpine variableValues
        (fuel - leafProbeFuel fieldDefinition.outputType)
        fieldDefinition.outputType.namedType
        fieldDefinition.outputType.namedType targetParent leftProbeField
        rightProbeField targetLeftArguments targetRightArguments
        leftRuntime rightRuntime
        (fieldPairPathLocalNextSelectionSet schema parentType
          fieldDefinition.outputType.namedType fieldName leftArguments
          leftCurrentSelectionSet)
        (fieldPairPathLocalNextSelectionSet schema parentType
          fieldDefinition.outputType.namedType fieldName rightArguments
          rightCurrentSelectionSet)
        childSpine childSpine leftChildSelectionSet
        rightChildSelectionSet := by
    simpa [hchildFuelEq] using hchildWitnessRaw
  have hwitness :
      SelectedPathTaggedSelectionSetsResponseDiffWitness schema
        rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
        leftSpine rightSpine variableValues (fuel + 1)
        parentType parentType targetParent leftProbeField rightProbeField
        targetLeftArguments targetRightArguments leftRuntime rightRuntime
        leftCurrentSelectionSet rightCurrentSelectionSet leftSpine
        rightSpine left right := by
    simpa [leftSpine, rightSpine] using
      selectedPathTaggedSelectionSetsResponseDiffWitness_of_objectOutput_sameField_childWitness_valid_normal_alignedSpine
        (schema := schema)
        (leftVariableDefinitions := leftVariableDefinitions)
        (rightVariableDefinitions := rightVariableDefinitions)
        rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
        leftCurrentSelectionSet rightCurrentSelectionSet leftSpine
        rightSpine childSpine childSpine variableValues fuel
        targetParent leftProbeField rightProbeField parentType
        targetLeftArguments targetRightArguments leftRuntime rightRuntime
        hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
        hrightNormal hobject hleftFuel hrightFuel hchildSpineValid
        hchildSpineValid hleftSupport hrightSupport hleftContext
        hrightContext hleftMem hrightMem hlookup hobjectOutput
        hchildWitness
  exact ⟨leftSpine, rightSpine, hleftSpineValid, hrightSpineValid,
    hwitness⟩

theorem selectedPathTaggedSelectionSetsResponseDiffWitness_of_objectOutputSameFieldResponsePath_valid_normal
    (schema : Schema)
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftProbeField rightProbeField parentType : Name)
    (targetLeftArguments targetRightArguments : List Argument)
    (leftRuntime rightRuntime : Name) {left right : List Selection}
    {responsePath : List Name}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions parentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> objectTypeNameBool schema parentType = true
      -> selectionSetDeepProbeFuel schema parentType left ≤ fuel
      -> selectionSetDeepProbeFuel schema parentType right ≤ fuel
      -> PathLocalSupportValidNormal schema parentType leftCurrentSelectionSet
      -> PathLocalSupportValidNormal schema parentType rightCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext left leftCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext right rightCurrentSelectionSet
      -> NormalSelectionSetObjectOutputSameFieldResponsePath schema parentType
          left right responsePath
      -> ∃ leftSpine rightSpine,
          SelectedFieldSpineRuntimeValid schema parentType parentType leftSpine
          ∧ SelectedFieldSpineRuntimeValid schema parentType parentType rightSpine
          ∧ SelectedPathTaggedSelectionSetsResponseDiffWitness schema
              rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
              leftInitialSpine rightInitialSpine variableValues (fuel + 1)
              parentType parentType targetParent leftProbeField rightProbeField
              targetLeftArguments targetRightArguments leftRuntime rightRuntime
              leftCurrentSelectionSet rightCurrentSelectionSet leftSpine
              rightSpine left right := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hobject hleftFuel hrightFuel hleftSupport
    hrightSupport hleftContext hrightContext hpath
  induction hpath generalizing leftVariableDefinitions
      rightVariableDefinitions leftCurrentSelectionSet rightCurrentSelectionSet
      fuel with
  | leaf hobjectPath hleftMem hrightMem hlookup hleaf =>
      rename_i pathParentType responseName fieldName leftArguments
        rightArguments leftDirectives rightDirectives leftChildSelectionSet
        rightChildSelectionSet pathLeft pathRight fieldDefinition
      have hleftPath :
          NormalSelectionSetObjectOutputObservableResponsePath schema
            pathParentType pathLeft [responseName] :=
        NormalSelectionSetObjectOutputObservableResponsePath.objectLeaf
          hobjectPath hleftMem hlookup hleaf
      have hrightPath :
          NormalSelectionSetObjectOutputObservableResponsePath schema
            pathParentType pathRight [responseName] :=
        NormalSelectionSetObjectOutputObservableResponsePath.objectLeaf
          hobjectPath hrightMem hlookup hleaf
      exact
        selectedPathTaggedSelectionSetsResponseDiffWitness_of_left_objectOutput_leaf_right_objectOutputPath_valid_normal_runtimeSpineExists
          (schema := schema)
          (leftVariableDefinitions := leftVariableDefinitions)
          (rightVariableDefinitions := rightVariableDefinitions)
          rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
          leftCurrentSelectionSet rightCurrentSelectionSet leftInitialSpine
          rightInitialSpine variableValues fuel targetParent leftProbeField
          rightProbeField pathParentType targetLeftArguments
          targetRightArguments leftRuntime rightRuntime hschema hleftValid
          hrightValid hleftFree hrightFree hleftNormal hrightNormal
          hobject hleftFuel hrightFuel hleftSupport hrightSupport
          hleftContext hrightContext hleftPath hrightPath
  | child hobjectPath hleftMem hrightMem hlookup hcomposite
      hobjectOutput hchildPath ih =>
      rename_i pathParentType responseName fieldName leftArguments
        rightArguments leftDirectives rightDirectives leftChildSelectionSet
        rightChildSelectionSet pathLeft pathRight fieldDefinition childPath
      let childFuel := fuel - leafProbeFuel fieldDefinition.outputType - 1
      have hleftChildValid :
          Validation.selectionSetValid schema leftVariableDefinitions
            fieldDefinition.outputType.namedType leftChildSelectionSet :=
        selectionSetValid_object_field_child_of_mem_lookup hleftValid
          hleftMem hlookup hobjectOutput
      have hrightChildValid :
          Validation.selectionSetValid schema rightVariableDefinitions
            fieldDefinition.outputType.namedType rightChildSelectionSet :=
        selectionSetValid_object_field_child_of_mem_lookup hrightValid
          hrightMem hlookup hobjectOutput
      have hleftChildFree :
          selectionSetDirectiveFree leftChildSelectionSet :=
        selectionSetDirectiveFree_field_child_of_mem hleftFree hleftMem
      have hrightChildFree :
          selectionSetDirectiveFree rightChildSelectionSet :=
        selectionSetDirectiveFree_field_child_of_mem hrightFree hrightMem
      have hleftChildNormal :
          selectionSetNormal schema fieldDefinition.outputType.namedType
            leftChildSelectionSet :=
        selectionSetNormal_field_child_of_mem_lookup hleftNormal
          hleftMem hlookup
      have hrightChildNormal :
          selectionSetNormal schema fieldDefinition.outputType.namedType
            rightChildSelectionSet :=
        selectionSetNormal_field_child_of_mem_lookup hrightNormal
          hrightMem hlookup
      have hleftChildSupport :
          PathLocalSupportValidNormal schema
            fieldDefinition.outputType.namedType
            (fieldPairPathLocalNextSelectionSet schema pathParentType
              fieldDefinition.outputType.namedType fieldName leftArguments
              leftCurrentSelectionSet) :=
        hleftSupport.fieldPairPathLocalNextSelectionSet_of_object_output
          hobject hobjectOutput hlookup rfl
      have hrightChildSupport :
          PathLocalSupportValidNormal schema
            fieldDefinition.outputType.namedType
            (fieldPairPathLocalNextSelectionSet schema pathParentType
              fieldDefinition.outputType.namedType fieldName rightArguments
              rightCurrentSelectionSet) :=
        hrightSupport.fieldPairPathLocalNextSelectionSet_of_object_output
          hobject hobjectOutput hlookup rfl
      have hleftAllFields : selectionsAllFields leftChildSelectionSet :=
        selectionSetNormal_allFields_of_object hleftChildNormal
          hobjectOutput
      have hrightAllFields : selectionsAllFields rightChildSelectionSet :=
        selectionSetNormal_allFields_of_object hrightChildNormal
          hobjectOutput
      have hleftPruned :
          runtimePrunedSelectionSet schema
              fieldDefinition.outputType.namedType leftChildSelectionSet =
            leftChildSelectionSet :=
        runtimePrunedSelectionSet_eq_self_of_allFields schema
          fieldDefinition.outputType.namedType hleftAllFields
      have hrightPruned :
          runtimePrunedSelectionSet schema
              fieldDefinition.outputType.namedType rightChildSelectionSet =
            rightChildSelectionSet :=
        runtimePrunedSelectionSet_eq_self_of_allFields schema
          fieldDefinition.outputType.namedType hrightAllFields
      have hleftChildContext :
          PathLocalSelectionSetCurrentContext leftChildSelectionSet
            (fieldPairPathLocalNextSelectionSet schema pathParentType
              fieldDefinition.outputType.namedType fieldName leftArguments
              leftCurrentSelectionSet) :=
        PathLocalSelectionSetCurrentContext.fieldPairPathLocalNextSelectionSet_field_child
          (schema := schema) (currentRuntimeType := pathParentType)
          (childRuntimeType := fieldDefinition.outputType.namedType)
          (targetField := fieldName) (responseName := responseName)
          (targetArguments := leftArguments) (arguments := leftArguments)
          (directives := leftDirectives) (selectionSet := pathLeft)
          (childSelectionSet := leftChildSelectionSet)
          (currentSelectionSet := leftCurrentSelectionSet) hleftContext
          hleftMem (argumentsEquivalent_refl_forSyntaxDiff leftArguments)
          hleftPruned
      have hrightChildContext :
          PathLocalSelectionSetCurrentContext rightChildSelectionSet
            (fieldPairPathLocalNextSelectionSet schema pathParentType
              fieldDefinition.outputType.namedType fieldName rightArguments
              rightCurrentSelectionSet) :=
        PathLocalSelectionSetCurrentContext.fieldPairPathLocalNextSelectionSet_field_child
          (schema := schema) (currentRuntimeType := pathParentType)
          (childRuntimeType := fieldDefinition.outputType.namedType)
          (targetField := fieldName) (responseName := responseName)
          (targetArguments := rightArguments) (arguments := rightArguments)
          (directives := rightDirectives) (selectionSet := pathRight)
          (childSelectionSet := rightChildSelectionSet)
          (currentSelectionSet := rightCurrentSelectionSet) hrightContext
          hrightMem (argumentsEquivalent_refl_forSyntaxDiff rightArguments)
          hrightPruned
      have hleftChildFuel :
          selectionSetDeepProbeFuel schema
              fieldDefinition.outputType.namedType leftChildSelectionSet ≤
            childFuel := by
        have hlocal :=
          selectionSetDeepProbeFuel_field_mem schema pathParentType pathLeft
            responseName fieldName leftArguments leftDirectives
            leftChildSelectionSet fieldDefinition hleftMem hlookup
        dsimp [childFuel]
        omega
      have hrightChildFuel :
          selectionSetDeepProbeFuel schema
              fieldDefinition.outputType.namedType rightChildSelectionSet ≤
            childFuel := by
        have hlocal :=
          selectionSetDeepProbeFuel_field_mem schema pathParentType pathRight
            responseName fieldName rightArguments rightDirectives
            rightChildSelectionSet fieldDefinition hrightMem hlookup
        dsimp [childFuel]
        omega
      have hchildFuelEq :
          childFuel + 1 = fuel - leafProbeFuel fieldDefinition.outputType := by
        have hlocal :=
          selectionSetDeepProbeFuel_field_mem schema pathParentType pathLeft
            responseName fieldName leftArguments leftDirectives
            leftChildSelectionSet fieldDefinition hleftMem hlookup
        dsimp [childFuel]
        omega
      have hchildExistsRaw :=
        ih
          (leftVariableDefinitions := leftVariableDefinitions)
          (rightVariableDefinitions := rightVariableDefinitions)
          (leftCurrentSelectionSet :=
            fieldPairPathLocalNextSelectionSet schema pathParentType
              fieldDefinition.outputType.namedType fieldName leftArguments
              leftCurrentSelectionSet)
          (rightCurrentSelectionSet :=
            fieldPairPathLocalNextSelectionSet schema pathParentType
              fieldDefinition.outputType.namedType fieldName rightArguments
              rightCurrentSelectionSet)
          (fuel := childFuel)
          hleftChildValid hrightChildValid hleftChildFree hrightChildFree
          hleftChildNormal hrightChildNormal hobjectOutput
          hleftChildFuel hrightChildFuel hleftChildSupport
          hrightChildSupport hleftChildContext hrightChildContext
      have hchildExists :
          ∃ leftChildSpine rightChildSpine,
            SelectedFieldSpineRuntimeValid schema
              fieldDefinition.outputType.namedType
              fieldDefinition.outputType.namedType leftChildSpine
              ∧ SelectedFieldSpineRuntimeValid schema
                fieldDefinition.outputType.namedType
                fieldDefinition.outputType.namedType rightChildSpine
              ∧ SelectedPathTaggedSelectionSetsResponseDiffWitness schema
                rootSelectionSet leftInitialSelectionSet
                rightInitialSelectionSet leftInitialSpine rightInitialSpine
                variableValues
                (fuel - leafProbeFuel fieldDefinition.outputType)
                fieldDefinition.outputType.namedType
                fieldDefinition.outputType.namedType targetParent
                leftProbeField rightProbeField targetLeftArguments
                targetRightArguments leftRuntime rightRuntime
                (fieldPairPathLocalNextSelectionSet schema pathParentType
                  fieldDefinition.outputType.namedType fieldName
                  leftArguments leftCurrentSelectionSet)
                (fieldPairPathLocalNextSelectionSet schema pathParentType
                  fieldDefinition.outputType.namedType fieldName
                  rightArguments rightCurrentSelectionSet)
                leftChildSpine rightChildSpine leftChildSelectionSet
                rightChildSelectionSet := by
        simpa [hchildFuelEq] using hchildExistsRaw
      exact
        selectedPathTaggedSelectionSetsResponseDiffWitness_of_objectOutput_sameField_childWitnessExists_valid_normal
          (schema := schema)
          (leftVariableDefinitions := leftVariableDefinitions)
          (rightVariableDefinitions := rightVariableDefinitions)
          rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
          leftCurrentSelectionSet rightCurrentSelectionSet leftInitialSpine
          rightInitialSpine variableValues fuel targetParent leftProbeField
          rightProbeField pathParentType targetLeftArguments
          targetRightArguments leftRuntime rightRuntime hschema hleftValid
          hrightValid hleftFree hrightFree hleftNormal hrightNormal
          hobject hleftFuel hrightFuel hleftSupport hrightSupport
          hleftContext hrightContext hleftMem hrightMem hlookup
          hobjectOutput hchildExists

theorem responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_left_normal_object_outputs_right_observable_leaf_of_valid_normal_runtimeSpine
    (schema : Schema)
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine leftSpine rightSpine
      : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftProbeField rightProbeField
      leftParentType rightParentType leftSourceRuntimeType
      rightSourceRuntimeType
      : Name)
    (targetLeftArguments targetRightArguments : List Argument)
    (leftRuntime rightRuntime : Name) {left right : List Selection} {responseName : Name}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions leftParentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions
          rightParentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema leftParentType left
      -> selectionSetNormal schema rightParentType right
      -> objectTypeNameBool schema leftParentType = true
      -> objectTypeNameBool schema rightParentType = true
      -> selectionSetDeepProbeFuel schema leftParentType left ≤ fuel
      -> selectionSetDeepProbeFuel schema rightParentType right ≤ fuel
      -> SelectedFieldSpineRuntimeValid schema leftParentType
          leftSourceRuntimeType leftSpine
      -> SelectedFieldSpineRuntimeValid schema rightParentType
          rightSourceRuntimeType rightSpine
      -> PathLocalSupportValidNormal schema leftSourceRuntimeType leftCurrentSelectionSet
      -> PathLocalSupportValidNormal schema rightSourceRuntimeType
          rightCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext left leftCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext right rightCurrentSelectionSet
      -> NormalSelectionSetObservableResponsePath schema rightParentType right
          [responseName]
      -> (∀ {leftFieldName : Name} {leftArguments : List Argument}
              {leftDirectives : List DirectiveApplication}
              {leftChildSelectionSet : List Selection}
              {leftFieldDefinition : FieldDefinition},
            Selection.field responseName leftFieldName leftArguments
                leftDirectives leftChildSelectionSet
              ∈ left
            -> schema.lookupField leftParentType leftFieldName = some leftFieldDefinition
            -> (TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool
                  schema
                = true
            -> objectTypeNameBool schema leftFieldDefinition.outputType.namedType = true)
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSelectedPathProbeResolvers schema
                  leftInitialSelectionSet rightInitialSelectionSet
                  leftInitialSpine rightInitialSpine targetParent leftProbeField
                  rightProbeField targetLeftArguments targetRightArguments
                  leftRuntime rightRuntime)
                targetParent leftProbeField rightProbeField targetLeftArguments
                targetRightArguments)
              variableValues (fuel + 1) leftParentType
              (projectionTargetResolverValue
                (.object leftSourceRuntimeType
                  (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
                    leftCurrentSelectionSet leftSpine)))
              left).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSelectedPathProbeResolvers schema
                  leftInitialSelectionSet rightInitialSelectionSet
                  leftInitialSpine rightInitialSpine targetParent leftProbeField
                  rightProbeField targetLeftArguments targetRightArguments
                  leftRuntime rightRuntime)
                targetParent leftProbeField rightProbeField targetLeftArguments
                targetRightArguments)
              variableValues (fuel + 1) rightParentType
              (projectionTargetResolverValue
                (.object rightSourceRuntimeType
                  (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                    rightCurrentSelectionSet rightSpine)))
              right).data := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hleftObject hrightObject hleftFuel hrightFuel
    hleftSpineValid hrightSpineValid hleftSupport hrightSupport
    hleftContext hrightContext hrightObservable hleftCompositeObject
  by_cases hleftResponseName :
      responseName ∈ left.filterMap Selection.responseName?
  · rcases
        selectionSetNormal_field_mem_of_object_responseName_mem
          hleftNormal hleftObject hleftResponseName with
      ⟨leftFieldName, leftArguments, leftDirectives,
        leftChildSelectionSet, hleftMem⟩
    rcases selectionSetValid_field_lookup_of_mem hleftValid hleftMem with
      ⟨leftFieldDefinition, hleftLookup, _hleftArguments,
        _hleftFieldValid⟩
    by_cases hleftLeaf :
        (TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool
          schema = false
    · exact
        responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_left_leaf_right_observable_leaf
          (schema := schema)
          (leftVariableDefinitions := leftVariableDefinitions)
          (rightVariableDefinitions := rightVariableDefinitions)
          rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet leftCurrentSelectionSet
          rightCurrentSelectionSet leftInitialSpine rightInitialSpine
          leftSpine rightSpine variableValues fuel targetParent
          leftProbeField rightProbeField leftParentType rightParentType
          leftSourceRuntimeType rightSourceRuntimeType
          targetLeftArguments targetRightArguments leftRuntime
          rightRuntime hschema hleftValid hrightValid hleftFree
          hrightFree hleftNormal hrightNormal hleftObject hrightObject
          hleftFuel hrightFuel hleftSpineValid hrightSpineValid
          hleftSupport hrightSupport hleftContext hrightContext
          hleftMem hleftLookup hleftLeaf hrightObservable
    · have hleftComposite :
          (TypeRef.named
              leftFieldDefinition.outputType.namedType).isCompositeBool
            schema = true := by
        cases h :
            (TypeRef.named
                leftFieldDefinition.outputType.namedType).isCompositeBool
              schema <;>
          simp [h] at hleftLeaf ⊢
      have hleftObjectOutput :
          objectTypeNameBool schema
              leftFieldDefinition.outputType.namedType = true :=
        hleftCompositeObject hleftMem hleftLookup hleftComposite
      rcases
          field_leaf_of_object_normalSelectionSetObservableResponsePath_single
            hrightObject hrightObservable with
        ⟨rightFieldName, rightArguments, rightDirectives,
          rightChildSelectionSet, rightFieldDefinition, hrightMem,
          hrightLookup, hrightLeaf⟩
      exact
        responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_left_objectOutput_right_leaf_field_pair_of_valid_normal_runtimeSpine
          (schema := schema)
          (leftVariableDefinitions := leftVariableDefinitions)
          (rightVariableDefinitions := rightVariableDefinitions)
          rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet leftCurrentSelectionSet
          rightCurrentSelectionSet leftInitialSpine rightInitialSpine
          leftSpine rightSpine variableValues fuel targetParent
          leftProbeField rightProbeField leftParentType rightParentType
          leftSourceRuntimeType rightSourceRuntimeType
          targetLeftArguments targetRightArguments leftRuntime
          rightRuntime hschema hleftValid hrightValid hleftFree
          hrightFree hleftNormal hrightNormal hleftObject hrightObject
          hleftFuel hrightFuel hleftSpineValid hrightSpineValid
          hleftSupport hrightSupport hleftContext hrightContext
          hleftMem hrightMem hleftLookup hrightLookup hleftObjectOutput
          hrightLeaf
  · exact
      responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_right_observable_responseName_absent
        (schema := schema)
        (leftVariableDefinitions := leftVariableDefinitions)
        (rightVariableDefinitions := rightVariableDefinitions)
        rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
        leftCurrentSelectionSet rightCurrentSelectionSet
        leftInitialSpine rightInitialSpine leftSpine rightSpine
        variableValues fuel targetParent leftProbeField rightProbeField
        leftParentType rightParentType leftSourceRuntimeType
        rightSourceRuntimeType targetLeftArguments targetRightArguments
        leftRuntime rightRuntime hschema hleftValid hrightValid hleftFree
        hrightFree hleftNormal hrightNormal hleftObject hrightObject
        hleftFuel hrightFuel hleftSpineValid hrightSpineValid
        hleftSupport hrightSupport hleftContext hrightContext
        (by simpa using hrightObservable) hleftResponseName

theorem responseData_not_semanticEquivalent_existsSpine_of_fieldPairOrDeepSuccess_selectedPathProbe_left_normal_right_observable_leaf_valid_normal_fuels
    (schema : Schema)
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (leftFuel rightFuel : Nat)
    (targetParent leftProbeField rightProbeField leftParentType rightParentType : Name)
    (targetLeftArguments targetRightArguments : List Argument)
    (leftRuntime rightRuntime : Name) {left right : List Selection} {responseName : Name}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions leftParentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions
          rightParentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema leftParentType left
      -> selectionSetNormal schema rightParentType right
      -> objectTypeNameBool schema leftParentType = true
      -> objectTypeNameBool schema rightParentType = true
      -> selectionSetDeepProbeFuel schema leftParentType left ≤ leftFuel
      -> selectionSetDeepProbeFuel schema rightParentType right ≤ rightFuel
      -> PathLocalSupportValidNormal schema leftParentType leftCurrentSelectionSet
      -> PathLocalSupportValidNormal schema rightParentType rightCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext left leftCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext right rightCurrentSelectionSet
      -> NormalSelectionSetObservableResponsePath schema rightParentType right
          [responseName]
      -> left ≠ []
      -> ∃ leftSpine rightSpine,
          SelectedFieldSpineRuntimeValid schema leftParentType leftParentType leftSpine
          ∧ SelectedFieldSpineRuntimeValid schema rightParentType
              rightParentType rightSpine
          ∧ ¬ Execution.ResponseValue.semanticEquivalent
                (Execution.executeSelectionSetAsResponse schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairSelectedPathProbeResolvers schema
                      leftInitialSelectionSet rightInitialSelectionSet
                      leftInitialSpine rightInitialSpine targetParent
                      leftProbeField rightProbeField targetLeftArguments
                      targetRightArguments leftRuntime rightRuntime)
                    targetParent leftProbeField rightProbeField
                    targetLeftArguments targetRightArguments)
                  variableValues (leftFuel + 1) leftParentType
                  (projectionTargetResolverValue
                    (.object leftParentType
                      (FieldPairSelectedPathProbeRef.target
                        FieldPairProbeTag.left leftCurrentSelectionSet
                        leftSpine)))
                  left).data
                (Execution.executeSelectionSetAsResponse schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairSelectedPathProbeResolvers schema
                      leftInitialSelectionSet rightInitialSelectionSet
                      leftInitialSpine rightInitialSpine targetParent
                      leftProbeField rightProbeField targetLeftArguments
                      targetRightArguments leftRuntime rightRuntime)
                    targetParent leftProbeField rightProbeField
                    targetLeftArguments targetRightArguments)
                  variableValues (rightFuel + 1) rightParentType
                  (projectionTargetResolverValue
                    (.object rightParentType
                      (FieldPairSelectedPathProbeRef.target
                        FieldPairProbeTag.right rightCurrentSelectionSet
                        rightSpine)))
                  right).data := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hleftObject hrightObject hleftFuel hrightFuel
    hleftSupport hrightSupport hleftContext hrightContext hrightObservable
    hleftNonempty
  rcases
      selectedFieldSpineRuntimeValid_exists_of_valid_normal_object_nonempty
        hleftValid hleftNormal hleftObject hleftNonempty with
    ⟨leftSpine, hleftSpineValid, _hleftObservableSpine⟩
  rcases
      field_leaf_of_object_normalSelectionSetObservableResponsePath_single
        hrightObject hrightObservable with
    ⟨rightFieldName, rightArguments, _rightDirectives,
      _rightChildSelectionSet, rightFieldDefinition, _hrightMem,
      hrightLookup, hrightLeaf⟩
  let rightSpine : List NormalSelectionSetObservableFieldStep :=
    [{ responseName := responseName, fieldName := rightFieldName,
       arguments := rightArguments, childRuntime := none }]
  have hrightSpineValid :
      SelectedFieldSpineRuntimeValid schema rightParentType rightParentType
        rightSpine :=
    SelectedFieldSpineRuntimeValid.objectLeaf hrightObject hrightLookup
      hrightLeaf
  refine ⟨leftSpine, rightSpine, hleftSpineValid, hrightSpineValid, ?_⟩
  by_cases hleftResponseName :
      responseName ∈ left.filterMap Selection.responseName?
  · rcases
        selectionSetNormal_field_mem_of_object_responseName_mem
          hleftNormal hleftObject hleftResponseName with
      ⟨leftFieldName, leftArguments, leftDirectives,
        leftChildSelectionSet, hleftMem⟩
    rcases selectionSetValid_field_lookup_of_mem hleftValid hleftMem with
      ⟨leftFieldDefinition, hleftLookup, _hleftArguments,
        _hleftFieldValid⟩
    by_cases hleftLeaf :
        (TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool
          schema = false
    · exact
        responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_left_leaf_right_observable_leaf_fuels
          (schema := schema)
          (leftVariableDefinitions := leftVariableDefinitions)
          (rightVariableDefinitions := rightVariableDefinitions)
          rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet leftCurrentSelectionSet
          rightCurrentSelectionSet leftInitialSpine rightInitialSpine
          leftSpine rightSpine variableValues leftFuel rightFuel
          targetParent leftProbeField rightProbeField leftParentType
          rightParentType leftParentType rightParentType
          targetLeftArguments targetRightArguments leftRuntime
          rightRuntime hschema hleftValid hrightValid hleftFree
          hrightFree hleftNormal hrightNormal hleftObject hrightObject
          hleftFuel hrightFuel hleftSpineValid hrightSpineValid
          hleftSupport hrightSupport hleftContext hrightContext
          hleftMem hleftLookup hleftLeaf hrightObservable
    · have hleftComposite :
          (TypeRef.named
              leftFieldDefinition.outputType.namedType).isCompositeBool
            schema = true := by
        cases h :
            (TypeRef.named
                leftFieldDefinition.outputType.namedType).isCompositeBool
              schema <;>
          simp [h] at hleftLeaf ⊢
      exact
        responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_left_composite_right_leaf_field_pair_of_valid_normal_runtimeSpine_fuels
          (schema := schema)
          (leftVariableDefinitions := leftVariableDefinitions)
          (rightVariableDefinitions := rightVariableDefinitions)
          rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet leftCurrentSelectionSet
          rightCurrentSelectionSet leftInitialSpine rightInitialSpine
          leftSpine rightSpine variableValues leftFuel rightFuel
          targetParent leftProbeField rightProbeField leftParentType
          rightParentType leftParentType rightParentType
          targetLeftArguments targetRightArguments leftRuntime
          rightRuntime hschema hleftValid hrightValid hleftFree
          hrightFree hleftNormal hrightNormal hleftObject hrightObject
          hleftFuel hrightFuel hleftSpineValid hrightSpineValid
          hleftSupport hrightSupport hleftContext hrightContext
          hleftMem _hrightMem hleftLookup hrightLookup hleftComposite
          hrightLeaf
  · exact
      responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_right_observable_responseName_absent_fuels
        (schema := schema)
        (leftVariableDefinitions := leftVariableDefinitions)
        (rightVariableDefinitions := rightVariableDefinitions)
        rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
        leftCurrentSelectionSet rightCurrentSelectionSet leftInitialSpine
        rightInitialSpine leftSpine rightSpine variableValues leftFuel
        rightFuel targetParent leftProbeField rightProbeField leftParentType
        rightParentType leftParentType rightParentType targetLeftArguments
        targetRightArguments leftRuntime rightRuntime hschema hleftValid
        hrightValid hleftFree hrightFree hleftNormal hrightNormal
        hleftObject hrightObject hleftFuel hrightFuel hleftSpineValid
        hrightSpineValid hleftSupport hrightSupport hleftContext
        hrightContext (by simpa using hrightObservable) hleftResponseName

theorem responseData_not_semanticEquivalent_existsSpine_of_fieldPairOrDeepSuccess_selectedPathProbe_left_responseName_absent_right_observable_valid_normal_fuels
    (schema : Schema)
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (leftFuel rightFuel : Nat)
    (targetParent leftProbeField rightProbeField leftParentType rightParentType : Name)
    (targetLeftArguments targetRightArguments : List Argument)
    (leftRuntime rightRuntime : Name) {left right : List Selection} {responseName : Name}
    {pathTail : List Name}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions leftParentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions
          rightParentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema leftParentType left
      -> selectionSetNormal schema rightParentType right
      -> objectTypeNameBool schema leftParentType = true
      -> objectTypeNameBool schema rightParentType = true
      -> selectionSetDeepProbeFuel schema leftParentType left ≤ leftFuel
      -> selectionSetDeepProbeFuel schema rightParentType right ≤ rightFuel
      -> PathLocalSupportValidNormal schema leftParentType leftCurrentSelectionSet
      -> PathLocalSupportValidNormal schema rightParentType rightCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext left leftCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext right rightCurrentSelectionSet
      -> NormalSelectionSetObservableResponsePath schema rightParentType right
          (responseName :: pathTail)
      -> responseName ∉ left.filterMap Selection.responseName?
      -> left ≠ []
      -> ∃ leftSpine rightSpine,
          SelectedFieldSpineRuntimeValid schema leftParentType leftParentType leftSpine
          ∧ SelectedFieldSpineRuntimeValid schema rightParentType
              rightParentType rightSpine
          ∧ ¬ Execution.ResponseValue.semanticEquivalent
                (Execution.executeSelectionSetAsResponse schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairSelectedPathProbeResolvers schema
                      leftInitialSelectionSet rightInitialSelectionSet
                      leftInitialSpine rightInitialSpine targetParent
                      leftProbeField rightProbeField targetLeftArguments
                      targetRightArguments leftRuntime rightRuntime)
                    targetParent leftProbeField rightProbeField
                    targetLeftArguments targetRightArguments)
                  variableValues (leftFuel + 1) leftParentType
                  (projectionTargetResolverValue
                    (.object leftParentType
                      (FieldPairSelectedPathProbeRef.target
                        FieldPairProbeTag.left leftCurrentSelectionSet
                        leftSpine)))
                  left).data
                (Execution.executeSelectionSetAsResponse schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairSelectedPathProbeResolvers schema
                      leftInitialSelectionSet rightInitialSelectionSet
                      leftInitialSpine rightInitialSpine targetParent
                      leftProbeField rightProbeField targetLeftArguments
                      targetRightArguments leftRuntime rightRuntime)
                    targetParent leftProbeField rightProbeField
                    targetLeftArguments targetRightArguments)
                  variableValues (rightFuel + 1) rightParentType
                  (projectionTargetResolverValue
                    (.object rightParentType
                      (FieldPairSelectedPathProbeRef.target
                        FieldPairProbeTag.right rightCurrentSelectionSet
                        rightSpine)))
                  right).data := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hleftObject hrightObject hleftFuel hrightFuel
    hleftSupport hrightSupport hleftContext hrightContext hrightObservable
    hleftNoResponseName hleftNonempty
  rcases
      selectedFieldSpineRuntimeValid_exists_of_valid_normal_object_nonempty
        hleftValid hleftNormal hleftObject hleftNonempty with
    ⟨leftSpine, hleftSpineValid, _hleftObservableSpine⟩
  rcases
      selectedFieldSpineRuntimeValid_exists_of_observableResponsePath_valid_normal
        hrightObservable hrightValid hrightNormal with
    ⟨rightRuntimeType, rightSpine, hrightInclude, hrightSpineValid,
      _hrightObservableSpine⟩
  have hrightRuntimeEq : rightRuntimeType = rightParentType :=
    typeIncludesObjectBool_eq_of_objectTypeNameBool_true schema
      hrightObject hrightInclude
  subst rightRuntimeType
  refine ⟨leftSpine, rightSpine, hleftSpineValid, hrightSpineValid, ?_⟩
  exact
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_right_observable_responseName_absent_fuels
      (schema := schema)
      (leftVariableDefinitions := leftVariableDefinitions)
      (rightVariableDefinitions := rightVariableDefinitions)
      rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet leftInitialSpine
      rightInitialSpine leftSpine rightSpine variableValues leftFuel
      rightFuel targetParent leftProbeField rightProbeField leftParentType
      rightParentType leftParentType rightParentType targetLeftArguments
      targetRightArguments leftRuntime rightRuntime hschema hleftValid
      hrightValid hleftFree hrightFree hleftNormal hrightNormal
      hleftObject hrightObject hleftFuel hrightFuel hleftSpineValid
      hrightSpineValid hleftSupport hrightSupport hleftContext
      hrightContext (by simpa using hrightObservable) hleftNoResponseName

theorem responseData_not_semanticEquivalent_existsSpine_of_fieldPairOrDeepSuccess_selectedPathProbe_left_leaf_right_observable_composite_valid_normal_fuels
    (schema : Schema)
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (leftFuel rightFuel : Nat)
    (targetParent leftProbeField rightProbeField leftParentType rightParentType : Name)
    (targetLeftArguments targetRightArguments : List Argument)
    (leftRuntime rightRuntime : Name) {left right : List Selection}
    {responseName leftFieldName rightFieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {leftFieldDefinition rightFieldDefinition : FieldDefinition} {pathTail : List Name}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions leftParentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions
          rightParentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema leftParentType left
      -> selectionSetNormal schema rightParentType right
      -> objectTypeNameBool schema leftParentType = true
      -> objectTypeNameBool schema rightParentType = true
      -> selectionSetDeepProbeFuel schema leftParentType left ≤ leftFuel
      -> selectionSetDeepProbeFuel schema rightParentType right ≤ rightFuel
      -> PathLocalSupportValidNormal schema leftParentType leftCurrentSelectionSet
      -> PathLocalSupportValidNormal schema rightParentType rightCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext left leftCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext right rightCurrentSelectionSet
      -> NormalSelectionSetObservableResponsePath schema rightParentType right
          (responseName :: pathTail)
      -> Selection.field responseName leftFieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName rightFieldName rightArguments
            rightDirectives rightChildSelectionSet
          ∈ right
      -> schema.lookupField leftParentType leftFieldName = some leftFieldDefinition
      -> schema.lookupField rightParentType rightFieldName = some rightFieldDefinition
      -> (TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> ∃ leftSpine rightSpine,
          SelectedFieldSpineRuntimeValid schema leftParentType leftParentType leftSpine
          ∧ SelectedFieldSpineRuntimeValid schema rightParentType
              rightParentType rightSpine
          ∧ ¬ Execution.ResponseValue.semanticEquivalent
                (Execution.executeSelectionSetAsResponse schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairSelectedPathProbeResolvers schema
                      leftInitialSelectionSet rightInitialSelectionSet
                      leftInitialSpine rightInitialSpine targetParent
                      leftProbeField rightProbeField targetLeftArguments
                      targetRightArguments leftRuntime rightRuntime)
                    targetParent leftProbeField rightProbeField
                    targetLeftArguments targetRightArguments)
                  variableValues (leftFuel + 1) leftParentType
                  (projectionTargetResolverValue
                    (.object leftParentType
                      (FieldPairSelectedPathProbeRef.target
                        FieldPairProbeTag.left leftCurrentSelectionSet
                        leftSpine)))
                  left).data
                (Execution.executeSelectionSetAsResponse schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairSelectedPathProbeResolvers schema
                      leftInitialSelectionSet rightInitialSelectionSet
                      leftInitialSpine rightInitialSpine targetParent
                      leftProbeField rightProbeField targetLeftArguments
                      targetRightArguments leftRuntime rightRuntime)
                    targetParent leftProbeField rightProbeField
                    targetLeftArguments targetRightArguments)
                  variableValues (rightFuel + 1) rightParentType
                  (projectionTargetResolverValue
                    (.object rightParentType
                      (FieldPairSelectedPathProbeRef.target
                        FieldPairProbeTag.right rightCurrentSelectionSet
                        rightSpine)))
                  right).data := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hleftObject hrightObject hleftFuel hrightFuel
    hleftSupport hrightSupport hleftContext hrightContext hrightObservable
    hleftMem hrightMem hleftLookup hrightLookup hleftLeaf hrightComposite
  let leftSpine : List NormalSelectionSetObservableFieldStep :=
    [{ responseName := responseName, fieldName := leftFieldName,
       arguments := leftArguments, childRuntime := none }]
  have hleftSpineValid :
      SelectedFieldSpineRuntimeValid schema leftParentType leftParentType
        leftSpine :=
    SelectedFieldSpineRuntimeValid.objectLeaf hleftObject hleftLookup
      hleftLeaf
  rcases
      selectedFieldSpineRuntimeValid_exists_of_observableResponsePath_valid_normal
        hrightObservable hrightValid hrightNormal with
    ⟨rightRuntimeType, rightSpine, hrightInclude, hrightSpineValid,
      _hrightObservableSpine⟩
  have hrightRuntimeEq : rightRuntimeType = rightParentType :=
    typeIncludesObjectBool_eq_of_objectTypeNameBool_true schema
      hrightObject hrightInclude
  subst rightRuntimeType
  refine ⟨leftSpine, rightSpine, hleftSpineValid, hrightSpineValid, ?_⟩
  exact
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_left_leaf_right_composite_field_pair_of_valid_normal_runtimeSpine_fuels
      (schema := schema)
      (leftVariableDefinitions := leftVariableDefinitions)
      (rightVariableDefinitions := rightVariableDefinitions)
      rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet leftInitialSpine
      rightInitialSpine leftSpine rightSpine variableValues leftFuel
      rightFuel targetParent leftProbeField rightProbeField leftParentType
      rightParentType leftParentType rightParentType targetLeftArguments
      targetRightArguments leftRuntime rightRuntime hschema hleftValid
      hrightValid hleftFree hrightFree hleftNormal hrightNormal
      hleftObject hrightObject hleftFuel hrightFuel hleftSpineValid
      hrightSpineValid hleftSupport hrightSupport hleftContext
      hrightContext hleftMem hrightMem hleftLookup hrightLookup hleftLeaf
      hrightComposite

theorem selectedPathTaggedSelectionSetsResponseDiffWitness_of_left_normal_object_outputs_right_observable_leaf_valid_normal_runtimeSpine
    (schema : Schema)
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine leftSpine rightSpine
      : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftProbeField rightProbeField parentType : Name)
    (targetLeftArguments targetRightArguments : List Argument)
    (leftRuntime rightRuntime : Name) {left right : List Selection} {responseName : Name}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions parentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> objectTypeNameBool schema parentType = true
      -> selectionSetDeepProbeFuel schema parentType left ≤ fuel
      -> selectionSetDeepProbeFuel schema parentType right ≤ fuel
      -> SelectedFieldSpineRuntimeValid schema parentType parentType leftSpine
      -> SelectedFieldSpineRuntimeValid schema parentType parentType rightSpine
      -> PathLocalSupportValidNormal schema parentType leftCurrentSelectionSet
      -> PathLocalSupportValidNormal schema parentType rightCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext left leftCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext right rightCurrentSelectionSet
      -> NormalSelectionSetObservableResponsePath schema parentType right [responseName]
      -> (∀ {leftFieldName : Name} {leftArguments : List Argument}
              {leftDirectives : List DirectiveApplication}
              {leftChildSelectionSet : List Selection}
              {leftFieldDefinition : FieldDefinition},
            Selection.field responseName leftFieldName leftArguments
                leftDirectives leftChildSelectionSet
              ∈ left
            -> schema.lookupField parentType leftFieldName = some leftFieldDefinition
            -> (TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool
                  schema
                = true
            -> objectTypeNameBool schema leftFieldDefinition.outputType.namedType = true)
      -> SelectedPathTaggedSelectionSetsResponseDiffWitness schema
          rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
          leftInitialSpine rightInitialSpine variableValues (fuel + 1)
          parentType parentType targetParent leftProbeField rightProbeField
          targetLeftArguments targetRightArguments leftRuntime rightRuntime
          leftCurrentSelectionSet rightCurrentSelectionSet leftSpine rightSpine
          left right := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hobject hleftFuel hrightFuel hleftSpineValid
    hrightSpineValid hleftSupport hrightSupport hleftContext
    hrightContext hrightObservable hleftCompositeObject
  rcases
      executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_of_valid_normal_runtimeSpine_support_context_fuel_ge_size
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftInitialSpine rightInitialSpine
        variableValues hschema (SelectionSet.size left + 1) parentType
        leftVariableDefinitions left fuel parentType targetParent
        leftProbeField rightProbeField targetLeftArguments
        targetRightArguments leftRuntime rightRuntime FieldPairProbeTag.left
        leftCurrentSelectionSet leftSpine (by omega) hleftFuel
        hleftValid hleftFree hleftNormal hleftSpineValid hleftSupport
        (fun _hobject => hleftContext)
        (fun hnonObject => by
          rw [hobject] at hnonObject
          simp at hnonObject) with
    ⟨leftFields, leftErrors, hleftResponse⟩
  rcases
      executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_of_valid_normal_runtimeSpine_support_context_fuel_ge_size
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftInitialSpine rightInitialSpine
        variableValues hschema (SelectionSet.size right + 1) parentType
        rightVariableDefinitions right fuel parentType targetParent
        leftProbeField rightProbeField targetLeftArguments
        targetRightArguments leftRuntime rightRuntime FieldPairProbeTag.right
        rightCurrentSelectionSet rightSpine (by omega) hrightFuel
        hrightValid hrightFree hrightNormal hrightSpineValid hrightSupport
        (fun _hobject => hrightContext)
        (fun hnonObject => by
          rw [hobject] at hnonObject
          simp at hnonObject) with
    ⟨rightFields, rightErrors, hrightResponse⟩
  have hdataNot :
      ¬ Execution.ResponseValue.semanticEquivalent
        (Execution.executeSelectionSetAsResponse schema
          (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
            (fieldPairSelectedPathProbeResolvers schema
              leftInitialSelectionSet rightInitialSelectionSet
              leftInitialSpine rightInitialSpine targetParent leftProbeField
              rightProbeField targetLeftArguments targetRightArguments
              leftRuntime rightRuntime)
            targetParent leftProbeField rightProbeField targetLeftArguments
            targetRightArguments)
          variableValues (fuel + 1) parentType
          (projectionTargetResolverValue
            (.object parentType
              (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
                leftCurrentSelectionSet leftSpine)))
          left).data
        (Execution.executeSelectionSetAsResponse schema
          (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
            (fieldPairSelectedPathProbeResolvers schema
              leftInitialSelectionSet rightInitialSelectionSet
              leftInitialSpine rightInitialSpine targetParent leftProbeField
              rightProbeField targetLeftArguments targetRightArguments
              leftRuntime rightRuntime)
            targetParent leftProbeField rightProbeField targetLeftArguments
            targetRightArguments)
          variableValues (fuel + 1) parentType
          (projectionTargetResolverValue
            (.object parentType
              (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                rightCurrentSelectionSet rightSpine)))
          right).data :=
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_left_normal_object_outputs_right_observable_leaf_of_valid_normal_runtimeSpine
      (schema := schema)
      (leftVariableDefinitions := leftVariableDefinitions)
      (rightVariableDefinitions := rightVariableDefinitions)
      rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet leftInitialSpine
      rightInitialSpine leftSpine rightSpine variableValues fuel
      targetParent leftProbeField rightProbeField parentType parentType
      parentType parentType targetLeftArguments targetRightArguments
      leftRuntime rightRuntime hschema hleftValid hrightValid hleftFree
      hrightFree hleftNormal hrightNormal hobject hobject hleftFuel
      hrightFuel hleftSpineValid hrightSpineValid hleftSupport
      hrightSupport hleftContext hrightContext hrightObservable
      hleftCompositeObject
  refine
    ⟨typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject,
      leftFields, leftErrors, rightFields, rightErrors, hleftResponse,
      hrightResponse, ?_⟩
  intro hobjects
  exact hdataNot (by simpa [hleftResponse, hrightResponse] using hobjects)

theorem selectedPathTaggedSelectionSetsResponseDiffWitness_of_objectOutputSameFieldSpinePath_valid_normal
    (schema : Schema)
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftProbeField rightProbeField parentType : Name)
    (targetLeftArguments targetRightArguments : List Argument)
    (leftRuntime rightRuntime : Name) {left right : List Selection}
    {responsePath : List Name}
    {leftSpine rightSpine : List NormalSelectionSetObservableFieldStep}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions parentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> objectTypeNameBool schema parentType = true
      -> selectionSetDeepProbeFuel schema parentType left ≤ fuel
      -> selectionSetDeepProbeFuel schema parentType right ≤ fuel
      -> PathLocalSupportValidNormal schema parentType leftCurrentSelectionSet
      -> PathLocalSupportValidNormal schema parentType rightCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext left leftCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext right rightCurrentSelectionSet
      -> NormalSelectionSetObjectOutputSameFieldSpinePath schema parentType
          left right responsePath leftSpine rightSpine
      -> SelectedFieldSpineRuntimeValid schema parentType parentType leftSpine
          ∧ SelectedFieldSpineRuntimeValid schema parentType parentType rightSpine
          ∧ SelectedPathTaggedSelectionSetsResponseDiffWitness schema
              rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
              leftInitialSpine rightInitialSpine variableValues (fuel + 1)
              parentType parentType targetParent leftProbeField rightProbeField
              targetLeftArguments targetRightArguments leftRuntime rightRuntime
              leftCurrentSelectionSet rightCurrentSelectionSet leftSpine
              rightSpine left right := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hobject hleftFuel hrightFuel hleftSupport
    hrightSupport hleftContext hrightContext hpath
  induction hpath generalizing leftVariableDefinitions
      rightVariableDefinitions leftCurrentSelectionSet rightCurrentSelectionSet
      leftInitialSpine rightInitialSpine fuel with
  | leaf hobjectPath hleftMem hrightMem hlookup hleaf =>
      rename_i pathParentType responseName fieldName leftArguments
        rightArguments leftDirectives rightDirectives leftChildSelectionSet
        rightChildSelectionSet pathLeft pathRight fieldDefinition
      have hleftSpineValid :
          SelectedFieldSpineRuntimeValid schema pathParentType pathParentType
            [{ responseName := responseName, fieldName := fieldName,
               arguments := leftArguments, childRuntime := none }] :=
        SelectedFieldSpineRuntimeValid.objectLeaf hobjectPath hlookup
          hleaf
      have hrightSpineValid :
          SelectedFieldSpineRuntimeValid schema pathParentType pathParentType
            [{ responseName := responseName, fieldName := fieldName,
               arguments := rightArguments, childRuntime := none }] :=
        SelectedFieldSpineRuntimeValid.objectLeaf hobjectPath hlookup
          hleaf
      have hleftPath :
          NormalSelectionSetObservableResponsePath schema pathParentType
            pathLeft [responseName] :=
        (NormalSelectionSetObjectOutputObservableResponsePath.objectLeaf
          hobjectPath hleftMem hlookup hleaf).to_observable
      have hwitness :
          SelectedPathTaggedSelectionSetsResponseDiffWitness schema
            rootSelectionSet leftInitialSelectionSet
            rightInitialSelectionSet leftInitialSpine rightInitialSpine
            variableValues (fuel + 1) pathParentType pathParentType
            targetParent leftProbeField rightProbeField targetLeftArguments
            targetRightArguments leftRuntime rightRuntime
            leftCurrentSelectionSet rightCurrentSelectionSet
            [{ responseName := responseName, fieldName := fieldName,
               arguments := leftArguments, childRuntime := none }]
            [{ responseName := responseName, fieldName := fieldName,
               arguments := rightArguments, childRuntime := none }]
            pathLeft pathRight :=
        selectedPathTaggedSelectionSetsResponseDiffWitness_of_left_observable_leaf_right_normal_valid_normal_runtimeSpine
          (schema := schema)
          (leftVariableDefinitions := leftVariableDefinitions)
          (rightVariableDefinitions := rightVariableDefinitions)
          rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
          leftCurrentSelectionSet rightCurrentSelectionSet
          leftInitialSpine rightInitialSpine
          [{ responseName := responseName, fieldName := fieldName,
             arguments := leftArguments, childRuntime := none }]
          [{ responseName := responseName, fieldName := fieldName,
             arguments := rightArguments, childRuntime := none }]
          variableValues fuel targetParent leftProbeField rightProbeField
          pathParentType targetLeftArguments targetRightArguments
          leftRuntime rightRuntime hschema hleftValid hrightValid
          hleftFree hrightFree hleftNormal hrightNormal hobjectPath
          hleftFuel hrightFuel hleftSpineValid hrightSpineValid
          hleftSupport hrightSupport hleftContext hrightContext hleftPath
      exact ⟨hleftSpineValid, hrightSpineValid, hwitness⟩
  | child hobjectPath hleftMem hrightMem hlookup hcomposite
      hobjectOutput _hchildPath ih =>
      rename_i pathParentType responseName fieldName leftArguments
        rightArguments leftDirectives rightDirectives leftChildSelectionSet
        rightChildSelectionSet pathLeft pathRight fieldDefinition childPath
        leftChildSpine rightChildSpine
      let childFuel := fuel - leafProbeFuel fieldDefinition.outputType - 1
      have hleftChildValid :
          Validation.selectionSetValid schema leftVariableDefinitions
            fieldDefinition.outputType.namedType leftChildSelectionSet :=
        selectionSetValid_object_field_child_of_mem_lookup hleftValid
          hleftMem hlookup hobjectOutput
      have hrightChildValid :
          Validation.selectionSetValid schema rightVariableDefinitions
            fieldDefinition.outputType.namedType rightChildSelectionSet :=
        selectionSetValid_object_field_child_of_mem_lookup hrightValid
          hrightMem hlookup hobjectOutput
      have hleftChildFree :
          selectionSetDirectiveFree leftChildSelectionSet :=
        selectionSetDirectiveFree_field_child_of_mem hleftFree hleftMem
      have hrightChildFree :
          selectionSetDirectiveFree rightChildSelectionSet :=
        selectionSetDirectiveFree_field_child_of_mem hrightFree hrightMem
      have hleftChildNormal :
          selectionSetNormal schema fieldDefinition.outputType.namedType
            leftChildSelectionSet :=
        selectionSetNormal_field_child_of_mem_lookup hleftNormal
          hleftMem hlookup
      have hrightChildNormal :
          selectionSetNormal schema fieldDefinition.outputType.namedType
            rightChildSelectionSet :=
        selectionSetNormal_field_child_of_mem_lookup hrightNormal
          hrightMem hlookup
      have hleftChildSupport :
          PathLocalSupportValidNormal schema
            fieldDefinition.outputType.namedType
            (fieldPairPathLocalNextSelectionSet schema pathParentType
              fieldDefinition.outputType.namedType fieldName leftArguments
              leftCurrentSelectionSet) :=
        hleftSupport.fieldPairPathLocalNextSelectionSet_of_object_output
          hobjectPath hobjectOutput hlookup rfl
      have hrightChildSupport :
          PathLocalSupportValidNormal schema
            fieldDefinition.outputType.namedType
            (fieldPairPathLocalNextSelectionSet schema pathParentType
              fieldDefinition.outputType.namedType fieldName rightArguments
              rightCurrentSelectionSet) :=
        hrightSupport.fieldPairPathLocalNextSelectionSet_of_object_output
          hobjectPath hobjectOutput hlookup rfl
      have hleftAllFields : selectionsAllFields leftChildSelectionSet :=
        selectionSetNormal_allFields_of_object hleftChildNormal
          hobjectOutput
      have hrightAllFields : selectionsAllFields rightChildSelectionSet :=
        selectionSetNormal_allFields_of_object hrightChildNormal
          hobjectOutput
      have hleftPruned :
          runtimePrunedSelectionSet schema
              fieldDefinition.outputType.namedType leftChildSelectionSet =
            leftChildSelectionSet :=
        runtimePrunedSelectionSet_eq_self_of_allFields schema
          fieldDefinition.outputType.namedType hleftAllFields
      have hrightPruned :
          runtimePrunedSelectionSet schema
              fieldDefinition.outputType.namedType rightChildSelectionSet =
            rightChildSelectionSet :=
        runtimePrunedSelectionSet_eq_self_of_allFields schema
          fieldDefinition.outputType.namedType hrightAllFields
      have hleftChildContext :
          PathLocalSelectionSetCurrentContext leftChildSelectionSet
            (fieldPairPathLocalNextSelectionSet schema pathParentType
              fieldDefinition.outputType.namedType fieldName leftArguments
              leftCurrentSelectionSet) :=
        PathLocalSelectionSetCurrentContext.fieldPairPathLocalNextSelectionSet_field_child
          (schema := schema) (currentRuntimeType := pathParentType)
          (childRuntimeType := fieldDefinition.outputType.namedType)
          (targetField := fieldName) (responseName := responseName)
          (targetArguments := leftArguments) (arguments := leftArguments)
          (directives := leftDirectives) (selectionSet := pathLeft)
          (childSelectionSet := leftChildSelectionSet)
          (currentSelectionSet := leftCurrentSelectionSet) hleftContext
          hleftMem (argumentsEquivalent_refl_forSyntaxDiff leftArguments)
          hleftPruned
      have hrightChildContext :
          PathLocalSelectionSetCurrentContext rightChildSelectionSet
            (fieldPairPathLocalNextSelectionSet schema pathParentType
              fieldDefinition.outputType.namedType fieldName rightArguments
              rightCurrentSelectionSet) :=
        PathLocalSelectionSetCurrentContext.fieldPairPathLocalNextSelectionSet_field_child
          (schema := schema) (currentRuntimeType := pathParentType)
          (childRuntimeType := fieldDefinition.outputType.namedType)
          (targetField := fieldName) (responseName := responseName)
          (targetArguments := rightArguments) (arguments := rightArguments)
          (directives := rightDirectives) (selectionSet := pathRight)
          (childSelectionSet := rightChildSelectionSet)
          (currentSelectionSet := rightCurrentSelectionSet) hrightContext
          hrightMem (argumentsEquivalent_refl_forSyntaxDiff rightArguments)
          hrightPruned
      have hleftChildFuel :
          selectionSetDeepProbeFuel schema
              fieldDefinition.outputType.namedType leftChildSelectionSet ≤
            childFuel := by
        have hlocal :=
          selectionSetDeepProbeFuel_field_mem schema pathParentType pathLeft
            responseName fieldName leftArguments leftDirectives
            leftChildSelectionSet fieldDefinition hleftMem hlookup
        dsimp [childFuel]
        omega
      have hrightChildFuel :
          selectionSetDeepProbeFuel schema
              fieldDefinition.outputType.namedType rightChildSelectionSet ≤
            childFuel := by
        have hlocal :=
          selectionSetDeepProbeFuel_field_mem schema pathParentType pathRight
            responseName fieldName rightArguments rightDirectives
            rightChildSelectionSet fieldDefinition hrightMem hlookup
        dsimp [childFuel]
        omega
      have hchildFuelEq :
          childFuel + 1 = fuel - leafProbeFuel fieldDefinition.outputType := by
        have hlocal :=
          selectionSetDeepProbeFuel_field_mem schema pathParentType pathLeft
            responseName fieldName leftArguments leftDirectives
            leftChildSelectionSet fieldDefinition hleftMem hlookup
        dsimp [childFuel]
        omega
      rcases
          ih
            (leftVariableDefinitions := leftVariableDefinitions)
            (rightVariableDefinitions := rightVariableDefinitions)
            (leftCurrentSelectionSet :=
              fieldPairPathLocalNextSelectionSet schema pathParentType
                fieldDefinition.outputType.namedType fieldName
                leftArguments leftCurrentSelectionSet)
            (rightCurrentSelectionSet :=
              fieldPairPathLocalNextSelectionSet schema pathParentType
                fieldDefinition.outputType.namedType fieldName
                rightArguments rightCurrentSelectionSet)
            (leftInitialSpine := leftInitialSpine)
            (rightInitialSpine := rightInitialSpine)
            (fuel := childFuel)
            hleftChildValid hrightChildValid hleftChildFree
            hrightChildFree hleftChildNormal hrightChildNormal
            hobjectOutput hleftChildFuel hrightChildFuel
            hleftChildSupport hrightChildSupport hleftChildContext
            hrightChildContext with
        ⟨hleftChildSpineValid, hrightChildSpineValid,
          hchildWitnessRaw⟩
      have hchildWitness :
          SelectedPathTaggedSelectionSetsResponseDiffWitness schema
            rootSelectionSet leftInitialSelectionSet
            rightInitialSelectionSet leftInitialSpine rightInitialSpine
            variableValues
            (fuel - leafProbeFuel fieldDefinition.outputType)
            fieldDefinition.outputType.namedType
            fieldDefinition.outputType.namedType targetParent
            leftProbeField rightProbeField targetLeftArguments
            targetRightArguments leftRuntime rightRuntime
            (fieldPairPathLocalNextSelectionSet schema pathParentType
              fieldDefinition.outputType.namedType fieldName leftArguments
              leftCurrentSelectionSet)
            (fieldPairPathLocalNextSelectionSet schema pathParentType
              fieldDefinition.outputType.namedType fieldName rightArguments
              rightCurrentSelectionSet)
            leftChildSpine rightChildSpine leftChildSelectionSet
            rightChildSelectionSet := by
        simpa [hchildFuelEq] using hchildWitnessRaw
      have hleftSpineValid :
          SelectedFieldSpineRuntimeValid schema pathParentType pathParentType
            ({ responseName := responseName, fieldName := fieldName,
               arguments := leftArguments,
               childRuntime := some fieldDefinition.outputType.namedType } ::
              leftChildSpine) :=
        SelectedFieldSpineRuntimeValid.objectChild hobjectPath hlookup
          hcomposite hleftChildSpineValid
      have hrightSpineValid :
          SelectedFieldSpineRuntimeValid schema pathParentType pathParentType
            ({ responseName := responseName, fieldName := fieldName,
               arguments := rightArguments,
               childRuntime := some fieldDefinition.outputType.namedType } ::
              rightChildSpine) :=
        SelectedFieldSpineRuntimeValid.objectChild hobjectPath hlookup
          hcomposite hrightChildSpineValid
      have hwitness :
          SelectedPathTaggedSelectionSetsResponseDiffWitness schema
            rootSelectionSet leftInitialSelectionSet
            rightInitialSelectionSet leftInitialSpine rightInitialSpine
            variableValues (fuel + 1) pathParentType pathParentType
            targetParent leftProbeField rightProbeField targetLeftArguments
            targetRightArguments leftRuntime rightRuntime
            leftCurrentSelectionSet rightCurrentSelectionSet
            ({ responseName := responseName, fieldName := fieldName,
               arguments := leftArguments,
               childRuntime := some fieldDefinition.outputType.namedType } ::
              leftChildSpine)
            ({ responseName := responseName, fieldName := fieldName,
               arguments := rightArguments,
               childRuntime := some fieldDefinition.outputType.namedType } ::
              rightChildSpine)
            pathLeft pathRight :=
        selectedPathTaggedSelectionSetsResponseDiffWitness_of_objectOutput_sameField_childWitness_valid_normal_alignedSpine
          (schema := schema)
          (leftVariableDefinitions := leftVariableDefinitions)
          (rightVariableDefinitions := rightVariableDefinitions)
          rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
          leftCurrentSelectionSet rightCurrentSelectionSet
          leftInitialSpine rightInitialSpine leftChildSpine
          rightChildSpine variableValues fuel targetParent leftProbeField
          rightProbeField pathParentType targetLeftArguments
          targetRightArguments leftRuntime rightRuntime hschema hleftValid
          hrightValid hleftFree hrightFree hleftNormal hrightNormal
          hobjectPath hleftFuel hrightFuel hleftChildSpineValid
          hrightChildSpineValid hleftSupport hrightSupport hleftContext
          hrightContext hleftMem hrightMem hlookup hobjectOutput
          hchildWitness
      exact ⟨hleftSpineValid, hrightSpineValid, hwitness⟩

theorem selectedPathTaggedSelectionSetsResponseDiffWitnessRoot_of_objectOutputSameFieldResponsePath_valid_normal
    (schema : Schema)
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftProbeField rightProbeField parentType : Name)
    (targetLeftArguments targetRightArguments : List Argument)
    (leftRuntime rightRuntime : Name) {left right : List Selection}
    {responsePath : List Name}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions parentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> objectTypeNameBool schema parentType = true
      -> selectionSetDeepProbeFuel schema parentType left ≤ fuel
      -> selectionSetDeepProbeFuel schema parentType right ≤ fuel
      -> PathLocalSupportValidNormal schema parentType leftCurrentSelectionSet
      -> PathLocalSupportValidNormal schema parentType rightCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext left leftCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext right rightCurrentSelectionSet
      -> NormalSelectionSetObjectOutputSameFieldResponsePath schema parentType
          left right responsePath
      -> ∃ leftSpine rightSpine,
          SelectedFieldSpineRuntimeValid schema parentType parentType leftSpine
          ∧ SelectedFieldSpineRuntimeValid schema parentType parentType rightSpine
          ∧ SelectedPathTaggedSelectionSetsResponseDiffWitness schema
              rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
              leftSpine rightSpine variableValues (fuel + 1)
              parentType parentType targetParent leftProbeField rightProbeField
              targetLeftArguments targetRightArguments leftRuntime rightRuntime
              leftCurrentSelectionSet rightCurrentSelectionSet leftSpine
              rightSpine left right := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hobject hleftFuel hrightFuel hleftSupport
    hrightSupport hleftContext hrightContext hpath
  rcases
      normalSelectionSetObjectOutputSameFieldSpinePath_exists_of_responsePath
        hpath with
    ⟨leftSpine, rightSpine, hspinePath⟩
  rcases
      selectedPathTaggedSelectionSetsResponseDiffWitness_of_objectOutputSameFieldSpinePath_valid_normal
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftCurrentSelectionSet
        rightCurrentSelectionSet leftSpine rightSpine variableValues fuel
        targetParent leftProbeField rightProbeField parentType
        targetLeftArguments targetRightArguments leftRuntime rightRuntime
        hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
        hrightNormal hobject hleftFuel hrightFuel hleftSupport
        hrightSupport hleftContext hrightContext hspinePath with
    ⟨hleftSpineValid, hrightSpineValid, hwitness⟩
  exact ⟨leftSpine, rightSpine, hleftSpineValid, hrightSpineValid,
    hwitness⟩

theorem selectedPathTaggedSelectionSetsResponseDiffWitnessRoot_of_left_objectOutputObservablePath_right_responseName_absent_valid_normal
    (schema : Schema)
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftProbeField rightProbeField parentType : Name)
    (targetLeftArguments targetRightArguments : List Argument)
    (leftRuntime rightRuntime : Name) {left right : List Selection} {responseName : Name}
    {pathTail : List Name}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions parentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> objectTypeNameBool schema parentType = true
      -> selectionSetDeepProbeFuel schema parentType left ≤ fuel
      -> selectionSetDeepProbeFuel schema parentType right ≤ fuel
      -> PathLocalSupportValidNormal schema parentType leftCurrentSelectionSet
      -> PathLocalSupportValidNormal schema parentType rightCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext left leftCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext right rightCurrentSelectionSet
      -> NormalSelectionSetObjectOutputObservableResponsePath schema parentType
          left (responseName :: pathTail)
      -> responseName ∉ right.filterMap Selection.responseName?
      -> ∃ leftSpine rightSpine,
          SelectedFieldSpineRuntimeValid schema parentType parentType leftSpine
          ∧ SelectedFieldSpineRuntimeValid schema parentType parentType rightSpine
          ∧ SelectedPathTaggedSelectionSetsResponseDiffWitness schema
              rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
              leftInitialSpine rightInitialSpine variableValues (fuel + 1)
              parentType parentType targetParent leftProbeField rightProbeField
              targetLeftArguments targetRightArguments leftRuntime rightRuntime
              leftCurrentSelectionSet rightCurrentSelectionSet leftSpine
              rightSpine left right := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hobject hleftFuel hrightFuel hleftSupport hrightSupport
    hleftContext hrightContext hleftPath hrightNoResponseName
  rcases
      selectedFieldSpineRuntimeValid_exists_of_objectOutputObservableResponsePath_valid_normal
        hleftPath hleftValid hleftNormal with
    ⟨fieldSpine, hspineValid, _hobservableSpine⟩
  refine ⟨fieldSpine, fieldSpine, hspineValid, hspineValid, ?_⟩
  exact
    selectedPathTaggedSelectionSetsResponseDiffWitness_of_left_observable_responseName_absent_valid_normal_runtimeSpine
      (schema := schema)
      (leftVariableDefinitions := leftVariableDefinitions)
      (rightVariableDefinitions := rightVariableDefinitions)
      rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet leftInitialSpine
      rightInitialSpine fieldSpine fieldSpine variableValues fuel
      targetParent leftProbeField rightProbeField parentType
      targetLeftArguments targetRightArguments leftRuntime rightRuntime
      hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
      hrightNormal hobject hleftFuel hrightFuel hspineValid hspineValid
      hleftSupport hrightSupport hleftContext hrightContext
      hleftPath.to_observable hrightNoResponseName

end GroundTypeNormalization

end NormalForm

end GraphQL
