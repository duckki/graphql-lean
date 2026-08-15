import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.FocusedSelectedPathObjectPaths

/-!
Leaf field-head and leaf/composite boundary separation.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_leaf_field_pair_of_valid_normal_runtimeSpine
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
    (targetLeftArguments targetRightArguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime : Name) {left right : List Selection}
    {responseName leftFieldName rightFieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {leftFieldDefinition rightFieldDefinition : FieldDefinition}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions leftParentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions
          rightParentType right
      -> selectionSetArgumentsCoercible schema variableValues leftParentType left
      -> selectionSetArgumentsCoercible schema variableValues rightParentType right
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
      -> Selection.field responseName leftFieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName rightFieldName rightArguments rightDirectives
            rightChildSelectionSet
          ∈ right
      -> schema.lookupField leftParentType leftFieldName = some leftFieldDefinition
      -> schema.lookupField rightParentType rightFieldName = some rightFieldDefinition
      -> (TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool schema
          = false
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
  intro hschema hleftValid hrightValid hleftCoercion hrightCoercion
    hleftFree hrightFree hleftNormal
    hrightNormal hleftObject hrightObject hleftFuel hrightFuel
    hleftSpineValid hrightSpineValid hleftSupport hrightSupport
    hleftContext hrightContext hleftMem hrightMem hleftLookup
    hrightLookup hleftLeaf hrightLeaf
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet
      (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
        rightInitialSelectionSet leftInitialSpine rightInitialSpine
        targetParent leftProbeField rightProbeField targetLeftArguments
        targetRightArguments leftRuntime rightRuntime)
      targetParent leftProbeField rightProbeField targetLeftArguments
      targetRightArguments
  let leftSource :=
    projectionTargetResolverValue
      (.object leftSourceRuntimeType
        (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
          leftCurrentSelectionSet leftSpine))
  let rightSource :=
    projectionTargetResolverValue
      (.object rightSourceRuntimeType
        (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
          rightCurrentSelectionSet rightSpine))
  have hleftFieldOk :
      ∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
            childSelectionSet ∈ left ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema resolvers variableValues
              (fuel + 1) leftSource responseName
              [{
                parentType := leftParentType
                responseName := responseName
                fieldName := fieldName
                arguments := arguments
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(responseName, responseValue)], fieldErrors) := by
    simpa [resolvers, leftSource] using
      selectionSetFieldsExecuteOk_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_of_valid_normal_runtimeSpine
        (schema := schema)
        (variableDefinitions := leftVariableDefinitions)
        (rootSelectionSet := rootSelectionSet)
        (leftInitialSelectionSet := leftInitialSelectionSet)
        (rightInitialSelectionSet := rightInitialSelectionSet)
        (currentSelectionSet := leftCurrentSelectionSet)
        (leftInitialSpine := leftInitialSpine)
        (rightInitialSpine := rightInitialSpine)
        (spine := leftSpine)
        (variableValues := variableValues) (fuel := fuel)
        (targetParent := targetParent) (leftField := leftProbeField)
        (rightField := rightProbeField) (parentType := leftParentType)
        (sourceRuntimeType := leftSourceRuntimeType)
        (leftArguments := targetLeftArguments)
        (rightArguments := targetRightArguments)
        (leftRuntime := leftRuntime) (rightRuntime := rightRuntime)
        (tag := FieldPairProbeTag.left) (selectionSet := left)
        hschema hleftValid hleftCoercion hleftFree hleftNormal hleftObject hleftFuel
        hleftSpineValid hleftSupport hleftContext
  have hrightFieldOk :
      ∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
            childSelectionSet ∈ right ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema resolvers variableValues
              (fuel + 1) rightSource responseName
              [{
                parentType := rightParentType
                responseName := responseName
                fieldName := fieldName
                arguments := arguments
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(responseName, responseValue)], fieldErrors) := by
    simpa [resolvers, rightSource] using
      selectionSetFieldsExecuteOk_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_of_valid_normal_runtimeSpine
        (schema := schema)
        (variableDefinitions := rightVariableDefinitions)
        (rootSelectionSet := rootSelectionSet)
        (leftInitialSelectionSet := leftInitialSelectionSet)
        (rightInitialSelectionSet := rightInitialSelectionSet)
        (currentSelectionSet := rightCurrentSelectionSet)
        (leftInitialSpine := leftInitialSpine)
        (rightInitialSpine := rightInitialSpine)
        (spine := rightSpine)
        (variableValues := variableValues) (fuel := fuel)
        (targetParent := targetParent) (leftField := leftProbeField)
        (rightField := rightProbeField) (parentType := rightParentType)
        (sourceRuntimeType := rightSourceRuntimeType)
        (leftArguments := targetLeftArguments)
        (rightArguments := targetRightArguments)
        (leftRuntime := leftRuntime) (rightRuntime := rightRuntime)
        (tag := FieldPairProbeTag.right) (selectionSet := right)
        hschema hrightValid hrightCoercion hrightFree hrightNormal hrightObject
        hrightFuel hrightSpineValid hrightSupport hrightContext
  have hleftTarget :
      Execution.executeField schema resolvers variableValues (fuel + 1)
        leftSource responseName
        [{
          parentType := leftParentType
          responseName := responseName
          fieldName := leftFieldName
          arguments := leftArguments
          selectionSet := leftChildSelectionSet
        }]
      =
      .ok ([(responseName,
        leafProbeResponseValue leftFieldDefinition.outputType
          FieldPairProbeTag.left.scalar)], 0) := by
    dsimp [resolvers, leftSource]
    exact
      executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_leaf
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftCurrentSelectionSet leftInitialSpine
        rightInitialSpine leftSpine variableValues fuel targetParent
        leftProbeField rightProbeField leftParentType leftFieldName
        leftSourceRuntimeType responseName targetLeftArguments
        targetRightArguments leftArguments leftRuntime rightRuntime
        FieldPairProbeTag.left leftChildSelectionSet leftFieldDefinition
        hleftLookup
        ((selectionSetArgumentCoercionSucceeds_of_argumentsCoercible
            hleftCoercion hleftFree)
          responseName leftFieldName leftArguments leftDirectives
          leftChildSelectionSet hleftMem leftFieldDefinition hleftLookup)
        (by
          have hlocal :=
            leafProbeFuel_le_selectionSetDeepProbeFuel_of_field_mem schema
              leftParentType (selectionSet := left)
              (responseName := responseName) (fieldName := leftFieldName)
              (arguments := leftArguments) (directives := leftDirectives)
              (childSelectionSet := leftChildSelectionSet)
              (fieldDefinition := leftFieldDefinition) hleftMem
              hleftLookup
          omega)
        hleftLeaf
  have hrightTarget :
      Execution.executeField schema resolvers variableValues (fuel + 1)
        rightSource responseName
        [{
          parentType := rightParentType
          responseName := responseName
          fieldName := rightFieldName
          arguments := rightArguments
          selectionSet := rightChildSelectionSet
        }]
      =
      .ok ([(responseName,
        leafProbeResponseValue rightFieldDefinition.outputType
          FieldPairProbeTag.right.scalar)], 0) := by
    dsimp [resolvers, rightSource]
    exact
      executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_leaf
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet rightCurrentSelectionSet leftInitialSpine
        rightInitialSpine rightSpine variableValues fuel targetParent
        leftProbeField rightProbeField rightParentType rightFieldName
        rightSourceRuntimeType responseName targetLeftArguments
        targetRightArguments rightArguments leftRuntime rightRuntime
        FieldPairProbeTag.right rightChildSelectionSet rightFieldDefinition
        hrightLookup
        ((selectionSetArgumentCoercionSucceeds_of_argumentsCoercible
            hrightCoercion hrightFree)
          responseName rightFieldName rightArguments rightDirectives
          rightChildSelectionSet hrightMem rightFieldDefinition hrightLookup)
        (by
          have hlocal :=
            leafProbeFuel_le_selectionSetDeepProbeFuel_of_field_mem schema
              rightParentType (selectionSet := right)
              (responseName := responseName) (fieldName := rightFieldName)
              (arguments := rightArguments) (directives := rightDirectives)
              (childSelectionSet := rightChildSelectionSet)
              (fieldDefinition := rightFieldDefinition) hrightMem
              hrightLookup
          omega)
        hrightLeaf
  simpa [resolvers, leftSource, rightSource] using
    SemanticSeparation.responseData_not_semanticEquivalent_of_field_value_diff_of_field_ok_pair
      (schema := schema) (leftParentType := leftParentType)
      (rightParentType := rightParentType) (left := left) (right := right)
      (responseName := responseName) (leftFieldName := leftFieldName)
      (rightFieldName := rightFieldName)
      (leftArguments := leftArguments)
      (rightArguments := rightArguments)
      (leftDirectives := leftDirectives)
      (rightDirectives := rightDirectives)
      (leftChildSelectionSet := leftChildSelectionSet)
      (rightChildSelectionSet := rightChildSelectionSet)
      resolvers resolvers variableValues (fuel + 1) leftSource
      rightSource hleftObject hrightObject hleftNormal hrightNormal
      hleftFree hrightFree hleftMem hrightMem hleftTarget hrightTarget
      (leafProbeResponseValue_not_semanticEquivalent_of_ne_any
        leftFieldDefinition.outputType rightFieldDefinition.outputType
        (by simp [FieldPairProbeTag.scalar]))
      hleftFieldOk hrightFieldOk

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_leaf_field_pair_of_valid_normal_runtimeSpine_fuels
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
    (targetLeftArguments targetRightArguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime : Name) {left right : List Selection}
    {responseName leftFieldName rightFieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {leftFieldDefinition rightFieldDefinition : FieldDefinition}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions leftParentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions
          rightParentType right
      -> selectionSetArgumentsCoercible schema variableValues leftParentType left
      -> selectionSetArgumentsCoercible schema variableValues rightParentType right
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
      -> Selection.field responseName leftFieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName rightFieldName rightArguments rightDirectives
            rightChildSelectionSet
          ∈ right
      -> schema.lookupField leftParentType leftFieldName = some leftFieldDefinition
      -> schema.lookupField rightParentType rightFieldName = some rightFieldDefinition
      -> (TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool schema
          = false
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
  intro hschema hleftValid hrightValid hleftCoercion hrightCoercion
    hleftFree hrightFree hleftNormal
    hrightNormal hleftObject hrightObject hleftFuel hrightFuel
    hleftSpineValid hrightSpineValid hleftSupport hrightSupport
    hleftContext hrightContext hleftMem hrightMem hleftLookup
    hrightLookup hleftLeaf hrightLeaf
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet
      (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
        rightInitialSelectionSet leftInitialSpine rightInitialSpine
        targetParent leftProbeField rightProbeField targetLeftArguments
        targetRightArguments leftRuntime rightRuntime)
      targetParent leftProbeField rightProbeField targetLeftArguments
      targetRightArguments
  let leftSource :=
    projectionTargetResolverValue
      (.object leftSourceRuntimeType
        (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
          leftCurrentSelectionSet leftSpine))
  let rightSource :=
    projectionTargetResolverValue
      (.object rightSourceRuntimeType
        (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
          rightCurrentSelectionSet rightSpine))
  have hleftFieldOk :
      ∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
            childSelectionSet ∈ left ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema resolvers variableValues
              (leftFuel + 1) leftSource responseName
              [{
                parentType := leftParentType
                responseName := responseName
                fieldName := fieldName
                arguments := arguments
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(responseName, responseValue)], fieldErrors) := by
    simpa [resolvers, leftSource] using
      selectionSetFieldsExecuteOk_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_of_valid_normal_runtimeSpine
        (schema := schema)
        (variableDefinitions := leftVariableDefinitions)
        (rootSelectionSet := rootSelectionSet)
        (leftInitialSelectionSet := leftInitialSelectionSet)
        (rightInitialSelectionSet := rightInitialSelectionSet)
        (currentSelectionSet := leftCurrentSelectionSet)
        (leftInitialSpine := leftInitialSpine)
        (rightInitialSpine := rightInitialSpine)
        (spine := leftSpine)
        (variableValues := variableValues) (fuel := leftFuel)
        (targetParent := targetParent) (leftField := leftProbeField)
        (rightField := rightProbeField) (parentType := leftParentType)
        (sourceRuntimeType := leftSourceRuntimeType)
        (leftArguments := targetLeftArguments)
        (rightArguments := targetRightArguments)
        (leftRuntime := leftRuntime) (rightRuntime := rightRuntime)
        (tag := FieldPairProbeTag.left) (selectionSet := left)
        hschema hleftValid hleftCoercion hleftFree hleftNormal hleftObject hleftFuel
        hleftSpineValid hleftSupport hleftContext
  have hrightFieldOk :
      ∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
            childSelectionSet ∈ right ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema resolvers variableValues
              (rightFuel + 1) rightSource responseName
              [{
                parentType := rightParentType
                responseName := responseName
                fieldName := fieldName
                arguments := arguments
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(responseName, responseValue)], fieldErrors) := by
    simpa [resolvers, rightSource] using
      selectionSetFieldsExecuteOk_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_of_valid_normal_runtimeSpine
        (schema := schema)
        (variableDefinitions := rightVariableDefinitions)
        (rootSelectionSet := rootSelectionSet)
        (leftInitialSelectionSet := leftInitialSelectionSet)
        (rightInitialSelectionSet := rightInitialSelectionSet)
        (currentSelectionSet := rightCurrentSelectionSet)
        (leftInitialSpine := leftInitialSpine)
        (rightInitialSpine := rightInitialSpine)
        (spine := rightSpine)
        (variableValues := variableValues) (fuel := rightFuel)
        (targetParent := targetParent) (leftField := leftProbeField)
        (rightField := rightProbeField) (parentType := rightParentType)
        (sourceRuntimeType := rightSourceRuntimeType)
        (leftArguments := targetLeftArguments)
        (rightArguments := targetRightArguments)
        (leftRuntime := leftRuntime) (rightRuntime := rightRuntime)
        (tag := FieldPairProbeTag.right) (selectionSet := right)
        hschema hrightValid hrightCoercion hrightFree hrightNormal hrightObject
        hrightFuel hrightSpineValid hrightSupport hrightContext
  have hleftTarget :
      Execution.executeField schema resolvers variableValues (leftFuel + 1)
        leftSource responseName
        [{
          parentType := leftParentType
          responseName := responseName
          fieldName := leftFieldName
          arguments := leftArguments
          selectionSet := leftChildSelectionSet
        }]
      =
      .ok ([(responseName,
        leafProbeResponseValue leftFieldDefinition.outputType
          FieldPairProbeTag.left.scalar)], 0) := by
    dsimp [resolvers, leftSource]
    exact
      executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_leaf
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftCurrentSelectionSet leftInitialSpine
        rightInitialSpine leftSpine variableValues leftFuel targetParent
        leftProbeField rightProbeField leftParentType leftFieldName
        leftSourceRuntimeType responseName targetLeftArguments
        targetRightArguments leftArguments leftRuntime rightRuntime
        FieldPairProbeTag.left leftChildSelectionSet leftFieldDefinition
        hleftLookup
        ((selectionSetArgumentCoercionSucceeds_of_argumentsCoercible
            hleftCoercion hleftFree)
          responseName leftFieldName leftArguments leftDirectives
          leftChildSelectionSet hleftMem leftFieldDefinition hleftLookup)
        (by
          have hlocal :=
            leafProbeFuel_le_selectionSetDeepProbeFuel_of_field_mem schema
              leftParentType (selectionSet := left)
              (responseName := responseName) (fieldName := leftFieldName)
              (arguments := leftArguments) (directives := leftDirectives)
              (childSelectionSet := leftChildSelectionSet)
              (fieldDefinition := leftFieldDefinition) hleftMem
              hleftLookup
          omega)
        hleftLeaf
  have hrightTarget :
      Execution.executeField schema resolvers variableValues (rightFuel + 1)
        rightSource responseName
        [{
          parentType := rightParentType
          responseName := responseName
          fieldName := rightFieldName
          arguments := rightArguments
          selectionSet := rightChildSelectionSet
        }]
      =
      .ok ([(responseName,
        leafProbeResponseValue rightFieldDefinition.outputType
          FieldPairProbeTag.right.scalar)], 0) := by
    dsimp [resolvers, rightSource]
    exact
      executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_leaf
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet rightCurrentSelectionSet leftInitialSpine
        rightInitialSpine rightSpine variableValues rightFuel targetParent
        leftProbeField rightProbeField rightParentType rightFieldName
        rightSourceRuntimeType responseName targetLeftArguments
        targetRightArguments rightArguments leftRuntime rightRuntime
        FieldPairProbeTag.right rightChildSelectionSet rightFieldDefinition
        hrightLookup
        ((selectionSetArgumentCoercionSucceeds_of_argumentsCoercible
            hrightCoercion hrightFree)
          responseName rightFieldName rightArguments rightDirectives
          rightChildSelectionSet hrightMem rightFieldDefinition hrightLookup)
        (by
          have hlocal :=
            leafProbeFuel_le_selectionSetDeepProbeFuel_of_field_mem schema
              rightParentType (selectionSet := right)
              (responseName := responseName) (fieldName := rightFieldName)
              (arguments := rightArguments) (directives := rightDirectives)
              (childSelectionSet := rightChildSelectionSet)
              (fieldDefinition := rightFieldDefinition) hrightMem
              hrightLookup
          omega)
        hrightLeaf
  simpa [resolvers, leftSource, rightSource] using
    SemanticSeparation.responseData_not_semanticEquivalent_of_field_value_diff_of_field_ok_pair_fuels
      (schema := schema) (leftParentType := leftParentType)
      (rightParentType := rightParentType) (left := left) (right := right)
      (responseName := responseName) (leftFieldName := leftFieldName)
      (rightFieldName := rightFieldName)
      (leftArguments := leftArguments)
      (rightArguments := rightArguments)
      (leftDirectives := leftDirectives)
      (rightDirectives := rightDirectives)
      (leftChildSelectionSet := leftChildSelectionSet)
      (rightChildSelectionSet := rightChildSelectionSet)
      resolvers resolvers variableValues (leftFuel + 1)
      (rightFuel + 1) leftSource rightSource hleftObject hrightObject
      hleftNormal hrightNormal hleftFree hrightFree hleftMem hrightMem
      hleftTarget hrightTarget
      (leafProbeResponseValue_not_semanticEquivalent_of_ne_any
        leftFieldDefinition.outputType rightFieldDefinition.outputType
        (by simp [FieldPairProbeTag.scalar]))
      hleftFieldOk hrightFieldOk

theorem
    selectedPathTaggedSelectionSetsResponseDiffWitness_of_leaf_field_pair_valid_normal_runtimeSpine
    (schema : Schema)
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine leftSpine rightSpine
      : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftProbeField rightProbeField parentType : Name)
    (targetLeftArguments targetRightArguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime : Name) {left right : List Selection}
    {responseName leftFieldName rightFieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {leftFieldDefinition rightFieldDefinition : FieldDefinition}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions parentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
      -> selectionSetArgumentsCoercible schema variableValues parentType left
      -> selectionSetArgumentsCoercible schema variableValues parentType right
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
      -> Selection.field responseName leftFieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName rightFieldName rightArguments
            rightDirectives rightChildSelectionSet
          ∈ right
      -> schema.lookupField parentType leftFieldName = some leftFieldDefinition
      -> schema.lookupField parentType rightFieldName = some rightFieldDefinition
      -> (TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> SelectedPathTaggedSelectionSetsResponseDiffWitness schema
          rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
          leftInitialSpine rightInitialSpine variableValues (fuel + 1)
          parentType parentType targetParent leftProbeField rightProbeField
          targetLeftArguments targetRightArguments leftRuntime rightRuntime
          leftCurrentSelectionSet rightCurrentSelectionSet leftSpine rightSpine
          left right := by
  intro hschema hleftValid hrightValid hleftCoercion hrightCoercion
    hleftFree hrightFree hleftNormal
    hrightNormal hobject hleftFuel hrightFuel hleftSpineValid
    hrightSpineValid hleftSupport hrightSupport hleftContext
    hrightContext hleftMem hrightMem hleftLookup hrightLookup hleftLeaf
    hrightLeaf
  rcases
      executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_of_valid_normal_runtimeSpine_support_context_fuel_ge_size
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftInitialSpine rightInitialSpine
        variableValues hschema (SelectionSet.size left + 1) parentType
        leftVariableDefinitions left fuel parentType targetParent
        leftProbeField rightProbeField targetLeftArguments
        targetRightArguments leftRuntime rightRuntime FieldPairProbeTag.left
        leftCurrentSelectionSet leftSpine (by omega) hleftFuel
        hleftValid
        (selectionSetArgumentsCoercibleInPossibleTypes_of_object
          hobject hleftCoercion)
        hleftFree hleftNormal hleftSpineValid hleftSupport
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
        hrightValid
        (selectionSetArgumentsCoercibleInPossibleTypes_of_object
          hobject hrightCoercion)
        hrightFree hrightNormal hrightSpineValid hrightSupport
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
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_leaf_field_pair_of_valid_normal_runtimeSpine
      (schema := schema)
      (leftVariableDefinitions := leftVariableDefinitions)
      (rightVariableDefinitions := rightVariableDefinitions)
      rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet leftInitialSpine
      rightInitialSpine leftSpine rightSpine variableValues fuel
      targetParent leftProbeField rightProbeField parentType parentType
      parentType parentType targetLeftArguments targetRightArguments
      leftRuntime rightRuntime hschema hleftValid hrightValid
      hleftCoercion hrightCoercion hleftFree
      hrightFree hleftNormal hrightNormal hobject hobject hleftFuel
      hrightFuel hleftSpineValid hrightSpineValid hleftSupport
      hrightSupport hleftContext hrightContext hleftMem hrightMem
      hleftLookup hrightLookup hleftLeaf hrightLeaf
  refine ⟨
    typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject,
    leftFields,
    leftErrors,
    rightFields,
    rightErrors,
    hleftResponse,
    hrightResponse,
    ?_
  ⟩
  intro hobjects
  exact hdataNot (by simpa [hleftResponse, hrightResponse] using hobjects)

theorem
    selectedPathTaggedSelectionSetsResponseDiffWitness_of_object_fieldName_diff_leaf_valid_normal_self
    (schema : Schema)
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftProbeField rightProbeField parentType : Name)
    (targetLeftArguments targetRightArguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime : Name) {left right : List Selection}
    {responseName leftFieldName rightFieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {leftFieldDefinition rightFieldDefinition : FieldDefinition}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions parentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
      -> selectionSetArgumentsCoercible schema variableValues parentType left
      -> selectionSetArgumentsCoercible schema variableValues parentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> objectTypeNameBool schema parentType = true
      -> selectionSetDeepProbeFuel schema parentType left ≤ fuel
      -> selectionSetDeepProbeFuel schema parentType right ≤ fuel
      -> Selection.field responseName leftFieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName rightFieldName rightArguments
            rightDirectives rightChildSelectionSet
          ∈ right
      -> schema.lookupField parentType leftFieldName = some leftFieldDefinition
      -> schema.lookupField parentType rightFieldName = some rightFieldDefinition
      -> (TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> leftFieldName ≠ rightFieldName
      -> ∃ leftSpine rightSpine,
          SelectedPathTaggedSelectionSetsResponseDiffWitness schema
            rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
            leftInitialSpine rightInitialSpine variableValues (fuel + 1)
            parentType parentType targetParent leftProbeField rightProbeField
            targetLeftArguments targetRightArguments leftRuntime rightRuntime
            left right leftSpine rightSpine left right := by
  intro hschema hleftValid hrightValid hleftCoercion hrightCoercion
    hleftFree hrightFree hleftNormal
    hrightNormal hobject hleftFuel hrightFuel hleftMem hrightMem
    hleftLookup hrightLookup hleftLeaf hrightLeaf _hfieldDiff
  rcases
      normalSelectionSetObservableResponsePath_of_valid_normal_object_field_mem
        hleftValid hleftNormal hobject hleftMem hleftLookup with
    ⟨pathTail, hleftObservablePath⟩
  rcases
      pathLocalSelectionSetObservableFieldSpineAtSelectedRuntime_of_observableResponsePath_valid_normal
        hleftObservablePath hleftValid hleftNormal with
    ⟨runtimeType, spine, hinclude, hobservableSpine⟩
  have hruntimeEq : runtimeType = parentType :=
    typeIncludesObjectBool_eq_of_objectTypeNameBool_true schema hobject
      hinclude
  subst runtimeType
  have hspineValid :
      SelectedFieldSpineRuntimeValid schema parentType parentType spine :=
    selectedFieldSpineRuntimeValid_of_observableFieldSpineAtSelectedRuntime
      (hobservableSpine left)
  refine ⟨spine, spine, ?_⟩
  exact
    selectedPathTaggedSelectionSetsResponseDiffWitness_of_leaf_field_pair_valid_normal_runtimeSpine
      (schema := schema)
      (leftVariableDefinitions := leftVariableDefinitions)
      (rightVariableDefinitions := rightVariableDefinitions)
      rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      left right leftInitialSpine rightInitialSpine spine spine
      variableValues fuel targetParent leftProbeField rightProbeField
      parentType targetLeftArguments targetRightArguments leftRuntime
      rightRuntime hschema hleftValid hrightValid hleftCoercion hrightCoercion
      hleftFree hrightFree
      hleftNormal hrightNormal hobject hleftFuel hrightFuel hspineValid
      hspineValid
      (PathLocalSupportValidNormal.of_valid_normal_self hleftValid
        hleftFree hleftNormal)
      (PathLocalSupportValidNormal.of_valid_normal_self hrightValid
        hrightFree hrightNormal)
      PathLocalSelectionSetCurrentContext.self
      PathLocalSelectionSetCurrentContext.self hleftMem hrightMem
      hleftLookup hrightLookup hleftLeaf hrightLeaf

theorem
    selectedPathTaggedSelectionSetsResponseDiffWitness_of_object_arguments_diff_leaf_valid_normal_self
    (schema : Schema)
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftProbeField rightProbeField parentType : Name)
    (targetLeftArguments targetRightArguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime : Name) {left right : List Selection}
    {responseName fieldName : Name} {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions parentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
      -> selectionSetArgumentsCoercible schema variableValues parentType left
      -> selectionSetArgumentsCoercible schema variableValues parentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> objectTypeNameBool schema parentType = true
      -> selectionSetDeepProbeFuel schema parentType left ≤ fuel
      -> selectionSetDeepProbeFuel schema parentType right ≤ fuel
      -> Selection.field responseName fieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName fieldName rightArguments rightDirectives
            rightChildSelectionSet
          ∈ right
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> ¬ Argument.argumentsEquivalent leftArguments rightArguments
      -> ∃ leftSpine rightSpine,
          SelectedPathTaggedSelectionSetsResponseDiffWitness schema
            rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
            leftInitialSpine rightInitialSpine variableValues (fuel + 1)
            parentType parentType targetParent leftProbeField rightProbeField
            targetLeftArguments targetRightArguments leftRuntime rightRuntime
            left right leftSpine rightSpine left right := by
  intro hschema hleftValid hrightValid hleftCoercion hrightCoercion
    hleftFree hrightFree hleftNormal
    hrightNormal hobject hleftFuel hrightFuel hleftMem hrightMem
    hlookup hleaf _hargumentsDiff
  rcases
      normalSelectionSetObservableResponsePath_of_valid_normal_object_field_mem
        hleftValid hleftNormal hobject hleftMem hlookup with
    ⟨pathTail, hleftObservablePath⟩
  rcases
      pathLocalSelectionSetObservableFieldSpineAtSelectedRuntime_of_observableResponsePath_valid_normal
        hleftObservablePath hleftValid hleftNormal with
    ⟨runtimeType, spine, hinclude, hobservableSpine⟩
  have hruntimeEq : runtimeType = parentType :=
    typeIncludesObjectBool_eq_of_objectTypeNameBool_true schema hobject
      hinclude
  subst runtimeType
  have hspineValid :
      SelectedFieldSpineRuntimeValid schema parentType parentType spine :=
    selectedFieldSpineRuntimeValid_of_observableFieldSpineAtSelectedRuntime
      (hobservableSpine left)
  refine ⟨spine, spine, ?_⟩
  exact
    selectedPathTaggedSelectionSetsResponseDiffWitness_of_leaf_field_pair_valid_normal_runtimeSpine
      (schema := schema)
      (leftVariableDefinitions := leftVariableDefinitions)
      (rightVariableDefinitions := rightVariableDefinitions)
      rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      left right leftInitialSpine rightInitialSpine spine spine
      variableValues fuel targetParent leftProbeField rightProbeField
      parentType targetLeftArguments targetRightArguments leftRuntime
      rightRuntime hschema hleftValid hrightValid hleftCoercion hrightCoercion
      hleftFree hrightFree
      hleftNormal hrightNormal hobject hleftFuel hrightFuel hspineValid
      hspineValid
      (PathLocalSupportValidNormal.of_valid_normal_self hleftValid
        hleftFree hleftNormal)
      (PathLocalSupportValidNormal.of_valid_normal_self hrightValid
        hrightFree hrightNormal)
      PathLocalSelectionSetCurrentContext.self
      PathLocalSelectionSetCurrentContext.self hleftMem hrightMem
      hlookup hlookup hleaf hleaf

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_left_observable_leaf_right_leaf
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
    (targetLeftArguments targetRightArguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime : Name) {left right : List Selection}
    {responseName rightFieldName : Name} {rightArguments : List Argument}
    {rightDirectives : List DirectiveApplication}
    {rightChildSelectionSet : List Selection} {rightFieldDefinition : FieldDefinition}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions leftParentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions
          rightParentType right
      -> selectionSetArgumentsCoercible schema variableValues leftParentType left
      -> selectionSetArgumentsCoercible schema variableValues rightParentType right
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
      -> Selection.field responseName rightFieldName rightArguments
            rightDirectives rightChildSelectionSet
          ∈ right
      -> schema.lookupField rightParentType rightFieldName = some rightFieldDefinition
      -> (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool schema
          = false
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
  intro hschema hleftValid hrightValid hleftCoercion hrightCoercion
    hleftFree hrightFree hleftNormal
    hrightNormal hleftObject hrightObject hleftFuel hrightFuel
    hleftSpineValid hrightSpineValid hleftSupport hrightSupport
    hleftContext hrightContext hleftObservable hrightMem hrightLookup
    hrightLeaf
  rcases
      field_leaf_of_object_normalSelectionSetObservableResponsePath_single
        hleftObject hleftObservable with
    ⟨leftFieldName, leftArguments, leftDirectives, leftChildSelectionSet,
      leftFieldDefinition, hleftMem, hleftLookup, hleftLeaf⟩
  exact
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_leaf_field_pair_of_valid_normal_runtimeSpine
      (schema := schema)
      (leftVariableDefinitions := leftVariableDefinitions)
      (rightVariableDefinitions := rightVariableDefinitions)
      rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet leftInitialSpine
      rightInitialSpine leftSpine rightSpine variableValues fuel
      targetParent leftProbeField rightProbeField leftParentType
      rightParentType leftSourceRuntimeType rightSourceRuntimeType
      targetLeftArguments targetRightArguments leftRuntime rightRuntime
      hschema hleftValid hrightValid hleftCoercion hrightCoercion
      hleftFree hrightFree hleftNormal
      hrightNormal hleftObject hrightObject hleftFuel hrightFuel
      hleftSpineValid hrightSpineValid hleftSupport hrightSupport
      hleftContext hrightContext hleftMem hrightMem hleftLookup
      hrightLookup hleftLeaf hrightLeaf

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_left_observable_leaf_right_leaf_fuels
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
    (targetLeftArguments targetRightArguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime : Name) {left right : List Selection}
    {responseName rightFieldName : Name} {rightArguments : List Argument}
    {rightDirectives : List DirectiveApplication}
    {rightChildSelectionSet : List Selection} {rightFieldDefinition : FieldDefinition}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions leftParentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions
          rightParentType right
      -> selectionSetArgumentsCoercible schema variableValues leftParentType left
      -> selectionSetArgumentsCoercible schema variableValues rightParentType right
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
      -> Selection.field responseName rightFieldName rightArguments
            rightDirectives rightChildSelectionSet
          ∈ right
      -> schema.lookupField rightParentType rightFieldName = some rightFieldDefinition
      -> (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool schema
          = false
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
  intro hschema hleftValid hrightValid hleftCoercion hrightCoercion
    hleftFree hrightFree hleftNormal
    hrightNormal hleftObject hrightObject hleftFuel hrightFuel
    hleftSpineValid hrightSpineValid hleftSupport hrightSupport
    hleftContext hrightContext hleftObservable hrightMem hrightLookup
    hrightLeaf
  rcases
      field_leaf_of_object_normalSelectionSetObservableResponsePath_single
        hleftObject hleftObservable with
    ⟨leftFieldName, leftArguments, leftDirectives, leftChildSelectionSet,
      leftFieldDefinition, hleftMem, hleftLookup, hleftLeaf⟩
  exact
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_leaf_field_pair_of_valid_normal_runtimeSpine_fuels
      (schema := schema)
      (leftVariableDefinitions := leftVariableDefinitions)
      (rightVariableDefinitions := rightVariableDefinitions)
      rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet leftInitialSpine
      rightInitialSpine leftSpine rightSpine variableValues leftFuel
      rightFuel targetParent leftProbeField rightProbeField leftParentType
      rightParentType leftSourceRuntimeType rightSourceRuntimeType
      targetLeftArguments targetRightArguments leftRuntime rightRuntime
      hschema hleftValid hrightValid hleftCoercion hrightCoercion
      hleftFree hrightFree hleftNormal
      hrightNormal hleftObject hrightObject hleftFuel hrightFuel
      hleftSpineValid hrightSpineValid hleftSupport hrightSupport
      hleftContext hrightContext hleftMem hrightMem hleftLookup
      hrightLookup hleftLeaf hrightLeaf

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_left_leaf_right_observable_leaf
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
    (targetLeftArguments targetRightArguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime : Name) {left right : List Selection}
    {responseName leftFieldName : Name} {leftArguments : List Argument}
    {leftDirectives : List DirectiveApplication} {leftChildSelectionSet : List Selection}
    {leftFieldDefinition : FieldDefinition}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions leftParentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions
          rightParentType right
      -> selectionSetArgumentsCoercible schema variableValues leftParentType left
      -> selectionSetArgumentsCoercible schema variableValues rightParentType right
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
      -> Selection.field responseName leftFieldName leftArguments
            leftDirectives leftChildSelectionSet
          ∈ left
      -> schema.lookupField leftParentType leftFieldName = some leftFieldDefinition
      -> (TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> NormalSelectionSetObservableResponsePath schema rightParentType right
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
  intro hschema hleftValid hrightValid hleftCoercion hrightCoercion
    hleftFree hrightFree hleftNormal
    hrightNormal hleftObject hrightObject hleftFuel hrightFuel
    hleftSpineValid hrightSpineValid hleftSupport hrightSupport
    hleftContext hrightContext hleftMem hleftLookup hleftLeaf
    hrightObservable
  rcases
      field_leaf_of_object_normalSelectionSetObservableResponsePath_single
        hrightObject hrightObservable with
    ⟨rightFieldName, rightArguments, rightDirectives,
      rightChildSelectionSet, rightFieldDefinition, hrightMem,
      hrightLookup, hrightLeaf⟩
  exact
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_leaf_field_pair_of_valid_normal_runtimeSpine
      (schema := schema)
      (leftVariableDefinitions := leftVariableDefinitions)
      (rightVariableDefinitions := rightVariableDefinitions)
      rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet leftInitialSpine
      rightInitialSpine leftSpine rightSpine variableValues fuel
      targetParent leftProbeField rightProbeField leftParentType
      rightParentType leftSourceRuntimeType rightSourceRuntimeType
      targetLeftArguments targetRightArguments leftRuntime rightRuntime
      hschema hleftValid hrightValid hleftCoercion hrightCoercion
      hleftFree hrightFree hleftNormal
      hrightNormal hleftObject hrightObject hleftFuel hrightFuel
      hleftSpineValid hrightSpineValid hleftSupport hrightSupport
      hleftContext hrightContext hleftMem hrightMem hleftLookup
      hrightLookup hleftLeaf hrightLeaf

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_left_leaf_right_observable_leaf_fuels
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
    (targetLeftArguments targetRightArguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime : Name) {left right : List Selection}
    {responseName leftFieldName : Name} {leftArguments : List Argument}
    {leftDirectives : List DirectiveApplication} {leftChildSelectionSet : List Selection}
    {leftFieldDefinition : FieldDefinition}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions leftParentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions
          rightParentType right
      -> selectionSetArgumentsCoercible schema variableValues leftParentType left
      -> selectionSetArgumentsCoercible schema variableValues rightParentType right
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
      -> Selection.field responseName leftFieldName leftArguments
            leftDirectives leftChildSelectionSet
          ∈ left
      -> schema.lookupField leftParentType leftFieldName = some leftFieldDefinition
      -> (TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> NormalSelectionSetObservableResponsePath schema rightParentType right
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
  intro hschema hleftValid hrightValid hleftCoercion hrightCoercion
    hleftFree hrightFree hleftNormal
    hrightNormal hleftObject hrightObject hleftFuel hrightFuel
    hleftSpineValid hrightSpineValid hleftSupport hrightSupport
    hleftContext hrightContext hleftMem hleftLookup hleftLeaf
    hrightObservable
  rcases
      field_leaf_of_object_normalSelectionSetObservableResponsePath_single
        hrightObject hrightObservable with
    ⟨rightFieldName, rightArguments, rightDirectives,
      rightChildSelectionSet, rightFieldDefinition, hrightMem,
      hrightLookup, hrightLeaf⟩
  exact
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_leaf_field_pair_of_valid_normal_runtimeSpine_fuels
      (schema := schema)
      (leftVariableDefinitions := leftVariableDefinitions)
      (rightVariableDefinitions := rightVariableDefinitions)
      rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet leftInitialSpine
      rightInitialSpine leftSpine rightSpine variableValues leftFuel
      rightFuel targetParent leftProbeField rightProbeField leftParentType
      rightParentType leftSourceRuntimeType rightSourceRuntimeType
      targetLeftArguments targetRightArguments leftRuntime rightRuntime
      hschema hleftValid hrightValid hleftCoercion hrightCoercion
      hleftFree hrightFree hleftNormal
      hrightNormal hleftObject hrightObject hleftFuel hrightFuel
      hleftSpineValid hrightSpineValid hleftSupport hrightSupport
      hleftContext hrightContext hleftMem hrightMem hleftLookup
      hrightLookup hleftLeaf hrightLeaf

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_left_objectOutput_right_leaf_field_pair_of_field_ok
    (schema : Schema)
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
    (targetLeftArguments targetRightArguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime : Name) {left right : List Selection}
    {responseName leftFieldName rightFieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {leftFieldDefinition rightFieldDefinition : FieldDefinition}
    {leftChildFields : List (Name × Execution.ResponseValue)} {leftChildErrors : Nat}
    : selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema leftParentType left
      -> selectionSetNormal schema rightParentType right
      -> objectTypeNameBool schema leftParentType = true
      -> objectTypeNameBool schema rightParentType = true
      -> Selection.field responseName leftFieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName rightFieldName rightArguments
            rightDirectives rightChildSelectionSet
          ∈ right
      -> schema.lookupField leftParentType leftFieldName = some leftFieldDefinition
      -> schema.lookupField rightParentType rightFieldName = some rightFieldDefinition
      -> (Execution.coerceArgumentValues schema variableValues
            leftFieldDefinition.arguments leftArguments).isSuccess
          = true
      -> (Execution.coerceArgumentValues schema variableValues
            rightFieldDefinition.arguments rightArguments).isSuccess
          = true
      -> objectTypeNameBool schema leftFieldDefinition.outputType.namedType = true
      -> (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> leafProbeFuel leftFieldDefinition.outputType ≤ fuel
      -> leafProbeFuel rightFieldDefinition.outputType ≤ fuel
      -> Execution.executeSelectionSetAsResponse schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet leftInitialSpine rightInitialSpine
                targetParent leftProbeField rightProbeField targetLeftArguments
                targetRightArguments leftRuntime rightRuntime)
              targetParent leftProbeField rightProbeField targetLeftArguments
              targetRightArguments)
            variableValues
            (fuel - leafProbeFuel leftFieldDefinition.outputType)
            leftFieldDefinition.outputType.namedType
            (projectionTargetResolverValue
              (.object leftFieldDefinition.outputType.namedType
                (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
                  (fieldPairPathLocalNextSelectionSet schema leftParentType
                    leftFieldDefinition.outputType.namedType leftFieldName
                    leftArguments leftCurrentSelectionSet)
                  (selectedObservableFieldSpineTailForRuntime
                    leftFieldDefinition.outputType.namedType leftFieldName
                    leftArguments leftSpine))))
            leftChildSelectionSet
          = ({
                data := Execution.ResponseValue.object leftChildFields,
                errors := leftChildErrors
              }
              : Execution.Response)
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ left
            -> ∃ responseValue fieldErrors,
                Execution.executeField schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairSelectedPathProbeResolvers schema
                      leftInitialSelectionSet rightInitialSelectionSet
                      leftInitialSpine rightInitialSpine targetParent
                      leftProbeField rightProbeField targetLeftArguments
                      targetRightArguments leftRuntime rightRuntime)
                    targetParent leftProbeField rightProbeField targetLeftArguments
                    targetRightArguments)
                  variableValues (fuel + 1)
                  (projectionTargetResolverValue
                    (.object leftSourceRuntimeType
                      (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
                        leftCurrentSelectionSet leftSpine)))
                  responseName
                  [{
                    parentType := leftParentType
                    responseName := responseName
                    fieldName := fieldName
                    arguments := arguments
                    selectionSet := childSelectionSet
                  }]
                = .ok ([(responseName, responseValue)], fieldErrors))
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ right
            -> ∃ responseValue fieldErrors,
                Execution.executeField schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairSelectedPathProbeResolvers schema
                      leftInitialSelectionSet rightInitialSelectionSet
                      leftInitialSpine rightInitialSpine targetParent
                      leftProbeField rightProbeField targetLeftArguments
                      targetRightArguments leftRuntime rightRuntime)
                    targetParent leftProbeField rightProbeField targetLeftArguments
                    targetRightArguments)
                  variableValues (fuel + 1)
                  (projectionTargetResolverValue
                    (.object rightSourceRuntimeType
                      (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                        rightCurrentSelectionSet rightSpine)))
                  responseName
                  [{
                    parentType := rightParentType
                    responseName := responseName
                    fieldName := fieldName
                    arguments := arguments
                    selectionSet := childSelectionSet
                  }]
                = .ok ([(responseName, responseValue)], fieldErrors))
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
  intro hleftFree hrightFree hleftNormal hrightNormal hleftObject
    hrightObject hleftMem hrightMem hleftLookup hrightLookup hleftCoercion
    hrightCoercion
    hleftObjectOutput hrightLeaf hleftFuel hrightFuel hleftChildResponse
    hleftFieldOk hrightFieldOk
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet
      (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
        rightInitialSelectionSet leftInitialSpine rightInitialSpine
        targetParent leftProbeField rightProbeField targetLeftArguments
        targetRightArguments leftRuntime rightRuntime)
      targetParent leftProbeField rightProbeField targetLeftArguments
      targetRightArguments
  let leftSource :=
    projectionTargetResolverValue
      (.object leftSourceRuntimeType
        (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
          leftCurrentSelectionSet leftSpine))
  let rightSource :=
    projectionTargetResolverValue
      (.object rightSourceRuntimeType
        (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
          rightCurrentSelectionSet rightSpine))
  rcases
      wrapTypeRefSelectionSetResult_ok_nonNull_of_object_response
        leftFieldDefinition.outputType leftChildFields leftChildErrors with
    ⟨leftResponseValue, leftFieldErrors, hleftWrapped,
      _hleftNonNull⟩
  have hleftTarget :
      Execution.executeField schema resolvers variableValues (fuel + 1)
        leftSource responseName
        [{
          parentType := leftParentType
          responseName := responseName
          fieldName := leftFieldName
          arguments := leftArguments
          selectionSet := leftChildSelectionSet
        }]
      =
      .ok ([(responseName, leftResponseValue)], leftFieldErrors) := by
    dsimp [resolvers, leftSource]
    rw [
      executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_objectOutput_response_of_fuel_ge
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftCurrentSelectionSet leftInitialSpine
        rightInitialSpine leftSpine variableValues fuel targetParent
        leftProbeField rightProbeField leftParentType leftFieldName
        leftSourceRuntimeType responseName targetLeftArguments
        targetRightArguments leftArguments leftRuntime rightRuntime
        FieldPairProbeTag.left leftChildSelectionSet leftFieldDefinition
        hleftLookup hleftCoercion hleftObjectOutput hleftFuel]
    rw [hleftChildResponse]
    simp [Execution.singleFieldResult, hleftWrapped]
  have hrightTarget :
      Execution.executeField schema resolvers variableValues (fuel + 1)
        rightSource responseName
        [{
          parentType := rightParentType
          responseName := responseName
          fieldName := rightFieldName
          arguments := rightArguments
          selectionSet := rightChildSelectionSet
        }]
      =
      .ok ([(responseName,
        leafProbeResponseValue rightFieldDefinition.outputType
          FieldPairProbeTag.right.scalar)], 0) := by
    dsimp [resolvers, rightSource]
    exact
      executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_leaf
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet rightCurrentSelectionSet leftInitialSpine
        rightInitialSpine rightSpine variableValues fuel targetParent
        leftProbeField rightProbeField rightParentType rightFieldName
        rightSourceRuntimeType responseName targetLeftArguments
        targetRightArguments rightArguments leftRuntime rightRuntime
        FieldPairProbeTag.right rightChildSelectionSet rightFieldDefinition
        hrightLookup hrightCoercion hrightFuel hrightLeaf
  have hleftComposite :
      (TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool
        schema = true :=
    typeRef_named_isCompositeBool_true_of_objectTypeNameBool
      hleftObjectOutput
  have hleafObjectNot :
      ¬ Execution.ResponseValue.semanticEquivalent
        (leafProbeResponseValue rightFieldDefinition.outputType
          FieldPairProbeTag.right.scalar)
        leftResponseValue :=
    leafProbeResponseValue_not_semanticEquivalent_wrapped_object_of_composite
      schema rightFieldDefinition.outputType leftFieldDefinition.outputType
      FieldPairProbeTag.right.scalar leftResponseValue leftFieldErrors
      leftChildFields leftChildErrors hrightLeaf hleftComposite hleftWrapped
  have hvalueNot :
      ¬ Execution.ResponseValue.semanticEquivalent leftResponseValue
        (leafProbeResponseValue rightFieldDefinition.outputType
          FieldPairProbeTag.right.scalar) := by
    intro hsemantic
    exact hleafObjectNot hsemantic.symm
  simpa [resolvers, leftSource, rightSource] using
    SemanticSeparation.responseData_not_semanticEquivalent_of_field_value_diff_of_field_ok_pair
      (schema := schema) (leftParentType := leftParentType)
      (rightParentType := rightParentType) (left := left) (right := right)
      (responseName := responseName) (leftFieldName := leftFieldName)
      (rightFieldName := rightFieldName)
      (leftArguments := leftArguments)
      (rightArguments := rightArguments)
      (leftDirectives := leftDirectives)
      (rightDirectives := rightDirectives)
      (leftChildSelectionSet := leftChildSelectionSet)
      (rightChildSelectionSet := rightChildSelectionSet)
      resolvers resolvers variableValues (fuel + 1) leftSource
      rightSource hleftObject hrightObject hleftNormal hrightNormal
      hleftFree hrightFree hleftMem hrightMem hleftTarget hrightTarget
      hvalueNot hleftFieldOk hrightFieldOk

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_left_objectOutput_right_leaf_field_pair_of_field_ok_fuels
    (schema : Schema)
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
    (targetLeftArguments targetRightArguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime : Name) {left right : List Selection}
    {responseName leftFieldName rightFieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {leftFieldDefinition rightFieldDefinition : FieldDefinition}
    {leftChildFields : List (Name × Execution.ResponseValue)} {leftChildErrors : Nat}
    : selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema leftParentType left
      -> selectionSetNormal schema rightParentType right
      -> objectTypeNameBool schema leftParentType = true
      -> objectTypeNameBool schema rightParentType = true
      -> Selection.field responseName leftFieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName rightFieldName rightArguments
            rightDirectives rightChildSelectionSet
          ∈ right
      -> schema.lookupField leftParentType leftFieldName = some leftFieldDefinition
      -> schema.lookupField rightParentType rightFieldName = some rightFieldDefinition
      -> (Execution.coerceArgumentValues schema variableValues
            leftFieldDefinition.arguments leftArguments).isSuccess
          = true
      -> (Execution.coerceArgumentValues schema variableValues
            rightFieldDefinition.arguments rightArguments).isSuccess
          = true
      -> objectTypeNameBool schema leftFieldDefinition.outputType.namedType = true
      -> (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> leafProbeFuel leftFieldDefinition.outputType ≤ leftFuel
      -> leafProbeFuel rightFieldDefinition.outputType ≤ rightFuel
      -> Execution.executeSelectionSetAsResponse schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet leftInitialSpine rightInitialSpine
                targetParent leftProbeField rightProbeField targetLeftArguments
                targetRightArguments leftRuntime rightRuntime)
              targetParent leftProbeField rightProbeField targetLeftArguments
              targetRightArguments)
            variableValues
            (leftFuel - leafProbeFuel leftFieldDefinition.outputType)
            leftFieldDefinition.outputType.namedType
            (projectionTargetResolverValue
              (.object leftFieldDefinition.outputType.namedType
                (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
                  (fieldPairPathLocalNextSelectionSet schema leftParentType
                    leftFieldDefinition.outputType.namedType leftFieldName
                    leftArguments leftCurrentSelectionSet)
                  (selectedObservableFieldSpineTailForRuntime
                    leftFieldDefinition.outputType.namedType leftFieldName
                    leftArguments leftSpine))))
            leftChildSelectionSet
          = ({
                data := Execution.ResponseValue.object leftChildFields,
                errors := leftChildErrors
              }
              : Execution.Response)
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ left
            -> ∃ responseValue fieldErrors,
                Execution.executeField schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairSelectedPathProbeResolvers schema
                      leftInitialSelectionSet rightInitialSelectionSet
                      leftInitialSpine rightInitialSpine targetParent
                      leftProbeField rightProbeField targetLeftArguments
                      targetRightArguments leftRuntime rightRuntime)
                    targetParent leftProbeField rightProbeField targetLeftArguments
                    targetRightArguments)
                  variableValues (leftFuel + 1)
                  (projectionTargetResolverValue
                    (.object leftSourceRuntimeType
                      (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
                        leftCurrentSelectionSet leftSpine)))
                  responseName
                  [{
                    parentType := leftParentType
                    responseName := responseName
                    fieldName := fieldName
                    arguments := arguments
                    selectionSet := childSelectionSet
                  }]
                = .ok ([(responseName, responseValue)], fieldErrors))
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ right
            -> ∃ responseValue fieldErrors,
                Execution.executeField schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairSelectedPathProbeResolvers schema
                      leftInitialSelectionSet rightInitialSelectionSet
                      leftInitialSpine rightInitialSpine targetParent
                      leftProbeField rightProbeField targetLeftArguments
                      targetRightArguments leftRuntime rightRuntime)
                    targetParent leftProbeField rightProbeField targetLeftArguments
                    targetRightArguments)
                  variableValues (rightFuel + 1)
                  (projectionTargetResolverValue
                    (.object rightSourceRuntimeType
                      (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                        rightCurrentSelectionSet rightSpine)))
                  responseName
                  [{
                    parentType := rightParentType
                    responseName := responseName
                    fieldName := fieldName
                    arguments := arguments
                    selectionSet := childSelectionSet
                  }]
                = .ok ([(responseName, responseValue)], fieldErrors))
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
  intro hleftFree hrightFree hleftNormal hrightNormal hleftObject
    hrightObject hleftMem hrightMem hleftLookup hrightLookup hleftCoercion
    hrightCoercion
    hleftObjectOutput hrightLeaf hleftFuel hrightFuel hleftChildResponse
    hleftFieldOk hrightFieldOk
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet
      (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
        rightInitialSelectionSet leftInitialSpine rightInitialSpine
        targetParent leftProbeField rightProbeField targetLeftArguments
        targetRightArguments leftRuntime rightRuntime)
      targetParent leftProbeField rightProbeField targetLeftArguments
      targetRightArguments
  let leftSource :=
    projectionTargetResolverValue
      (.object leftSourceRuntimeType
        (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
          leftCurrentSelectionSet leftSpine))
  let rightSource :=
    projectionTargetResolverValue
      (.object rightSourceRuntimeType
        (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
          rightCurrentSelectionSet rightSpine))
  rcases
      wrapTypeRefSelectionSetResult_ok_nonNull_of_object_response
        leftFieldDefinition.outputType leftChildFields leftChildErrors with
    ⟨leftResponseValue, leftFieldErrors, hleftWrapped,
      _hleftNonNull⟩
  have hleftTarget :
      Execution.executeField schema resolvers variableValues (leftFuel + 1)
        leftSource responseName
        [{
          parentType := leftParentType
          responseName := responseName
          fieldName := leftFieldName
          arguments := leftArguments
          selectionSet := leftChildSelectionSet
        }]
      =
      .ok ([(responseName, leftResponseValue)], leftFieldErrors) := by
    dsimp [resolvers, leftSource]
    rw [
      executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_objectOutput_response_of_fuel_ge
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftCurrentSelectionSet leftInitialSpine
        rightInitialSpine leftSpine variableValues leftFuel targetParent
        leftProbeField rightProbeField leftParentType leftFieldName
        leftSourceRuntimeType responseName targetLeftArguments
        targetRightArguments leftArguments leftRuntime rightRuntime
        FieldPairProbeTag.left leftChildSelectionSet leftFieldDefinition
        hleftLookup hleftCoercion hleftObjectOutput hleftFuel]
    rw [hleftChildResponse]
    simp [Execution.singleFieldResult, hleftWrapped]
  have hrightTarget :
      Execution.executeField schema resolvers variableValues (rightFuel + 1)
        rightSource responseName
        [{
          parentType := rightParentType
          responseName := responseName
          fieldName := rightFieldName
          arguments := rightArguments
          selectionSet := rightChildSelectionSet
        }]
      =
      .ok ([(responseName,
        leafProbeResponseValue rightFieldDefinition.outputType
          FieldPairProbeTag.right.scalar)], 0) := by
    dsimp [resolvers, rightSource]
    exact
      executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_leaf
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet rightCurrentSelectionSet leftInitialSpine
        rightInitialSpine rightSpine variableValues rightFuel targetParent
        leftProbeField rightProbeField rightParentType rightFieldName
        rightSourceRuntimeType responseName targetLeftArguments
        targetRightArguments rightArguments leftRuntime rightRuntime
        FieldPairProbeTag.right rightChildSelectionSet rightFieldDefinition
        hrightLookup hrightCoercion hrightFuel hrightLeaf
  have hleftComposite :
      (TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool
        schema = true :=
    typeRef_named_isCompositeBool_true_of_objectTypeNameBool
      hleftObjectOutput
  have hleafObjectNot :
      ¬ Execution.ResponseValue.semanticEquivalent
        (leafProbeResponseValue rightFieldDefinition.outputType
          FieldPairProbeTag.right.scalar)
        leftResponseValue :=
    leafProbeResponseValue_not_semanticEquivalent_wrapped_object_of_composite
      schema rightFieldDefinition.outputType leftFieldDefinition.outputType
      FieldPairProbeTag.right.scalar leftResponseValue leftFieldErrors
      leftChildFields leftChildErrors hrightLeaf hleftComposite hleftWrapped
  have hvalueNot :
      ¬ Execution.ResponseValue.semanticEquivalent leftResponseValue
        (leafProbeResponseValue rightFieldDefinition.outputType
          FieldPairProbeTag.right.scalar) := by
    intro hsemantic
    exact hleafObjectNot hsemantic.symm
  simpa [resolvers, leftSource, rightSource] using
    SemanticSeparation.responseData_not_semanticEquivalent_of_field_value_diff_of_field_ok_pair_fuels
      (schema := schema) (leftParentType := leftParentType)
      (rightParentType := rightParentType) (left := left) (right := right)
      (responseName := responseName) (leftFieldName := leftFieldName)
      (rightFieldName := rightFieldName)
      (leftArguments := leftArguments)
      (rightArguments := rightArguments)
      (leftDirectives := leftDirectives)
      (rightDirectives := rightDirectives)
      (leftChildSelectionSet := leftChildSelectionSet)
      (rightChildSelectionSet := rightChildSelectionSet)
      resolvers resolvers variableValues (leftFuel + 1)
      (rightFuel + 1) leftSource rightSource hleftObject hrightObject
      hleftNormal hrightNormal hleftFree hrightFree hleftMem hrightMem
      hleftTarget hrightTarget hvalueNot hleftFieldOk hrightFieldOk

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_left_objectOutput_right_leaf_field_pair_of_valid_normal_runtimeSpine
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
    (targetLeftArguments targetRightArguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime : Name) {left right : List Selection}
    {responseName leftFieldName rightFieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {leftFieldDefinition rightFieldDefinition : FieldDefinition}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions leftParentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions
          rightParentType right
      -> selectionSetArgumentsCoercible schema variableValues leftParentType left
      -> selectionSetArgumentsCoercible schema variableValues rightParentType right
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
      -> Selection.field responseName leftFieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName rightFieldName rightArguments
            rightDirectives rightChildSelectionSet
          ∈ right
      -> schema.lookupField leftParentType leftFieldName = some leftFieldDefinition
      -> schema.lookupField rightParentType rightFieldName = some rightFieldDefinition
      -> objectTypeNameBool schema leftFieldDefinition.outputType.namedType = true
      -> (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool schema
          = false
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
  intro hschema hleftValid hrightValid hleftCoercion hrightCoercion
    hleftFree hrightFree hleftNormal
    hrightNormal hleftObject hrightObject hleftFuel hrightFuel
    hleftSpineValid hrightSpineValid hleftSupport hrightSupport
    hleftContext hrightContext hleftMem hrightMem hleftLookup
    hrightLookup hleftObjectOutput hrightLeaf
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet
      (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
        rightInitialSelectionSet leftInitialSpine rightInitialSpine
        targetParent leftProbeField rightProbeField targetLeftArguments
        targetRightArguments leftRuntime rightRuntime)
      targetParent leftProbeField rightProbeField targetLeftArguments
      targetRightArguments
  let leftSource :=
    projectionTargetResolverValue
      (.object leftSourceRuntimeType
        (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
          leftCurrentSelectionSet leftSpine))
  let rightSource :=
    projectionTargetResolverValue
      (.object rightSourceRuntimeType
        (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
          rightCurrentSelectionSet rightSpine))
  have hleftReady :
      SelectedPathSelectionSetFieldChildrenReady schema rootSelectionSet
        leftInitialSelectionSet rightInitialSelectionSet
        leftCurrentSelectionSet leftInitialSpine rightInitialSpine
        leftSpine variableValues fuel targetParent leftProbeField
        rightProbeField leftParentType targetLeftArguments
        targetRightArguments leftRuntime rightRuntime FieldPairProbeTag.left
        left :=
    selectedPathSelectionSetFieldChildrenReady_of_valid_normal_runtimeSpine_support_context_fuel_ge
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet leftInitialSpine rightInitialSpine
      variableValues hschema leftParentType leftVariableDefinitions left
      fuel leftSourceRuntimeType targetParent leftProbeField
      rightProbeField targetLeftArguments targetRightArguments
      leftRuntime rightRuntime FieldPairProbeTag.left leftCurrentSelectionSet
      leftSpine hleftFuel hleftValid hleftCoercion hleftFree hleftNormal hleftObject
      hleftSpineValid hleftSupport hleftContext
  have hleftFieldOk :
      ∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
            childSelectionSet ∈ left ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema resolvers variableValues
              (fuel + 1) leftSource responseName
              [{
                parentType := leftParentType
                responseName := responseName
                fieldName := fieldName
                arguments := arguments
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(responseName, responseValue)], fieldErrors) := by
    simpa [resolvers, leftSource] using
      executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_field_ok_of_selectedPathFieldChildrenReady
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftCurrentSelectionSet leftInitialSpine
        rightInitialSpine leftSpine variableValues fuel targetParent
        leftProbeField rightProbeField leftParentType
        leftSourceRuntimeType targetLeftArguments targetRightArguments
        leftRuntime rightRuntime FieldPairProbeTag.left left hleftReady
  have hrightFieldOk :
      ∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
            childSelectionSet ∈ right ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema resolvers variableValues
              (fuel + 1) rightSource responseName
              [{
                parentType := rightParentType
                responseName := responseName
                fieldName := fieldName
                arguments := arguments
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(responseName, responseValue)], fieldErrors) := by
    simpa [resolvers, rightSource] using
      selectionSetFieldsExecuteOk_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_of_valid_normal_runtimeSpine
        (schema := schema)
        (variableDefinitions := rightVariableDefinitions)
        (rootSelectionSet := rootSelectionSet)
        (leftInitialSelectionSet := leftInitialSelectionSet)
        (rightInitialSelectionSet := rightInitialSelectionSet)
        (currentSelectionSet := rightCurrentSelectionSet)
        (leftInitialSpine := leftInitialSpine)
        (rightInitialSpine := rightInitialSpine)
        (spine := rightSpine)
        (variableValues := variableValues) (fuel := fuel)
        (targetParent := targetParent) (leftField := leftProbeField)
        (rightField := rightProbeField) (parentType := rightParentType)
        (sourceRuntimeType := rightSourceRuntimeType)
        (leftArguments := targetLeftArguments)
        (rightArguments := targetRightArguments)
        (leftRuntime := leftRuntime) (rightRuntime := rightRuntime)
        (tag := FieldPairProbeTag.right) (selectionSet := right)
        hschema hrightValid hrightCoercion hrightFree hrightNormal hrightObject
        hrightFuel hrightSpineValid hrightSupport hrightContext
  rcases
      objectOutputChildResponse_of_selectedPathFieldChildrenReady
        (schema := schema)
        (rootSelectionSet := rootSelectionSet)
        (leftInitialSelectionSet := leftInitialSelectionSet)
        (rightInitialSelectionSet := rightInitialSelectionSet)
        (currentSelectionSet := leftCurrentSelectionSet)
        (selectionSet := left)
        (leftInitialSpine := leftInitialSpine)
        (rightInitialSpine := rightInitialSpine)
        (spine := leftSpine)
        (variableValues := variableValues) (fuel := fuel)
        (targetParent := targetParent) (leftField := leftProbeField)
        (rightField := rightProbeField) (parentType := leftParentType)
        (targetLeftArguments := targetLeftArguments)
        (targetRightArguments := targetRightArguments)
        (leftRuntime := leftRuntime) (rightRuntime := rightRuntime)
        (tag := FieldPairProbeTag.left)
        (responseName := responseName) (fieldName := leftFieldName)
        (arguments := leftArguments) (directives := leftDirectives)
        (childSelectionSet := leftChildSelectionSet)
        (fieldDefinition := leftFieldDefinition)
        hleftReady hleftMem hleftLookup hleftObjectOutput with
    ⟨leftChildFields, leftChildErrors, hleftChildResponse⟩
  have hleftLeafFuel :
      leafProbeFuel leftFieldDefinition.outputType ≤ fuel := by
    have hlocal :=
      leafProbeFuel_le_selectionSetDeepProbeFuel_of_field_mem schema
        leftParentType (selectionSet := left)
        (responseName := responseName) (fieldName := leftFieldName)
        (arguments := leftArguments) (directives := leftDirectives)
        (childSelectionSet := leftChildSelectionSet)
        (fieldDefinition := leftFieldDefinition) hleftMem hleftLookup
    omega
  have hrightLeafFuel :
      leafProbeFuel rightFieldDefinition.outputType ≤ fuel := by
    have hlocal :=
      leafProbeFuel_le_selectionSetDeepProbeFuel_of_field_mem schema
        rightParentType (selectionSet := right)
        (responseName := responseName) (fieldName := rightFieldName)
        (arguments := rightArguments) (directives := rightDirectives)
        (childSelectionSet := rightChildSelectionSet)
        (fieldDefinition := rightFieldDefinition) hrightMem hrightLookup
    omega
  simpa [resolvers, leftSource, rightSource] using
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_left_objectOutput_right_leaf_field_pair_of_field_ok
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet leftCurrentSelectionSet
      rightCurrentSelectionSet leftInitialSpine rightInitialSpine
      leftSpine rightSpine variableValues fuel targetParent
      leftProbeField rightProbeField leftParentType rightParentType
      leftSourceRuntimeType rightSourceRuntimeType targetLeftArguments
      targetRightArguments leftRuntime rightRuntime hleftFree hrightFree
      hleftNormal hrightNormal hleftObject hrightObject hleftMem
      hrightMem hleftLookup hrightLookup
      ((selectionSetArgumentCoercionSucceeds_of_argumentsCoercible
          hleftCoercion hleftFree)
        responseName leftFieldName leftArguments leftDirectives
        leftChildSelectionSet hleftMem leftFieldDefinition hleftLookup)
      ((selectionSetArgumentCoercionSucceeds_of_argumentsCoercible
          hrightCoercion hrightFree)
        responseName rightFieldName rightArguments rightDirectives
        rightChildSelectionSet hrightMem rightFieldDefinition hrightLookup)
      hleftObjectOutput hrightLeaf
      hleftLeafFuel hrightLeafFuel hleftChildResponse hleftFieldOk
      hrightFieldOk

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_left_objectOutput_right_leaf_field_pair_of_valid_normal_runtimeSpine_fuels
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
    (targetLeftArguments targetRightArguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime : Name) {left right : List Selection}
    {responseName leftFieldName rightFieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {leftFieldDefinition rightFieldDefinition : FieldDefinition}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions leftParentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions
          rightParentType right
      -> selectionSetArgumentsCoercible schema variableValues leftParentType left
      -> selectionSetArgumentsCoercible schema variableValues rightParentType right
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
      -> Selection.field responseName leftFieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName rightFieldName rightArguments
            rightDirectives rightChildSelectionSet
          ∈ right
      -> schema.lookupField leftParentType leftFieldName = some leftFieldDefinition
      -> schema.lookupField rightParentType rightFieldName = some rightFieldDefinition
      -> objectTypeNameBool schema leftFieldDefinition.outputType.namedType = true
      -> (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool schema
          = false
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
  intro hschema hleftValid hrightValid hleftCoercion hrightCoercion
    hleftFree hrightFree hleftNormal
    hrightNormal hleftObject hrightObject hleftFuel hrightFuel
    hleftSpineValid hrightSpineValid hleftSupport hrightSupport
    hleftContext hrightContext hleftMem hrightMem hleftLookup
    hrightLookup hleftObjectOutput hrightLeaf
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet
      (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
        rightInitialSelectionSet leftInitialSpine rightInitialSpine
        targetParent leftProbeField rightProbeField targetLeftArguments
        targetRightArguments leftRuntime rightRuntime)
      targetParent leftProbeField rightProbeField targetLeftArguments
      targetRightArguments
  let leftSource :=
    projectionTargetResolverValue
      (.object leftSourceRuntimeType
        (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
          leftCurrentSelectionSet leftSpine))
  let rightSource :=
    projectionTargetResolverValue
      (.object rightSourceRuntimeType
        (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
          rightCurrentSelectionSet rightSpine))
  have hleftReady :
      SelectedPathSelectionSetFieldChildrenReady schema rootSelectionSet
        leftInitialSelectionSet rightInitialSelectionSet
        leftCurrentSelectionSet leftInitialSpine rightInitialSpine
        leftSpine variableValues leftFuel targetParent leftProbeField
        rightProbeField leftParentType targetLeftArguments
        targetRightArguments leftRuntime rightRuntime FieldPairProbeTag.left
        left :=
    selectedPathSelectionSetFieldChildrenReady_of_valid_normal_runtimeSpine_support_context_fuel_ge
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet leftInitialSpine rightInitialSpine
      variableValues hschema leftParentType leftVariableDefinitions left
      leftFuel leftSourceRuntimeType targetParent leftProbeField
      rightProbeField targetLeftArguments targetRightArguments
      leftRuntime rightRuntime FieldPairProbeTag.left leftCurrentSelectionSet
      leftSpine hleftFuel hleftValid hleftCoercion hleftFree hleftNormal hleftObject
      hleftSpineValid hleftSupport hleftContext
  have hleftFieldOk :
      ∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
            childSelectionSet ∈ left ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema resolvers variableValues
              (leftFuel + 1) leftSource responseName
              [{
                parentType := leftParentType
                responseName := responseName
                fieldName := fieldName
                arguments := arguments
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(responseName, responseValue)], fieldErrors) := by
    simpa [resolvers, leftSource] using
      executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_field_ok_of_selectedPathFieldChildrenReady
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftCurrentSelectionSet leftInitialSpine
        rightInitialSpine leftSpine variableValues leftFuel targetParent
        leftProbeField rightProbeField leftParentType
        leftSourceRuntimeType targetLeftArguments targetRightArguments
        leftRuntime rightRuntime FieldPairProbeTag.left left hleftReady
  have hrightFieldOk :
      ∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
            childSelectionSet ∈ right ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema resolvers variableValues
              (rightFuel + 1) rightSource responseName
              [{
                parentType := rightParentType
                responseName := responseName
                fieldName := fieldName
                arguments := arguments
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(responseName, responseValue)], fieldErrors) := by
    simpa [resolvers, rightSource] using
      selectionSetFieldsExecuteOk_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_of_valid_normal_runtimeSpine
        (schema := schema)
        (variableDefinitions := rightVariableDefinitions)
        (rootSelectionSet := rootSelectionSet)
        (leftInitialSelectionSet := leftInitialSelectionSet)
        (rightInitialSelectionSet := rightInitialSelectionSet)
        (currentSelectionSet := rightCurrentSelectionSet)
        (leftInitialSpine := leftInitialSpine)
        (rightInitialSpine := rightInitialSpine)
        (spine := rightSpine)
        (variableValues := variableValues) (fuel := rightFuel)
        (targetParent := targetParent) (leftField := leftProbeField)
        (rightField := rightProbeField) (parentType := rightParentType)
        (sourceRuntimeType := rightSourceRuntimeType)
        (leftArguments := targetLeftArguments)
        (rightArguments := targetRightArguments)
        (leftRuntime := leftRuntime) (rightRuntime := rightRuntime)
        (tag := FieldPairProbeTag.right) (selectionSet := right)
        hschema hrightValid hrightCoercion hrightFree hrightNormal hrightObject
        hrightFuel hrightSpineValid hrightSupport hrightContext
  rcases
      objectOutputChildResponse_of_selectedPathFieldChildrenReady
        (schema := schema)
        (rootSelectionSet := rootSelectionSet)
        (leftInitialSelectionSet := leftInitialSelectionSet)
        (rightInitialSelectionSet := rightInitialSelectionSet)
        (currentSelectionSet := leftCurrentSelectionSet)
        (selectionSet := left)
        (leftInitialSpine := leftInitialSpine)
        (rightInitialSpine := rightInitialSpine)
        (spine := leftSpine)
        (variableValues := variableValues) (fuel := leftFuel)
        (targetParent := targetParent) (leftField := leftProbeField)
        (rightField := rightProbeField) (parentType := leftParentType)
        (targetLeftArguments := targetLeftArguments)
        (targetRightArguments := targetRightArguments)
        (leftRuntime := leftRuntime) (rightRuntime := rightRuntime)
        (tag := FieldPairProbeTag.left)
        (responseName := responseName) (fieldName := leftFieldName)
        (arguments := leftArguments) (directives := leftDirectives)
        (childSelectionSet := leftChildSelectionSet)
        (fieldDefinition := leftFieldDefinition)
        hleftReady hleftMem hleftLookup hleftObjectOutput with
    ⟨leftChildFields, leftChildErrors, hleftChildResponse⟩
  have hleftLeafFuel :
      leafProbeFuel leftFieldDefinition.outputType ≤ leftFuel := by
    have hlocal :=
      leafProbeFuel_le_selectionSetDeepProbeFuel_of_field_mem schema
        leftParentType (selectionSet := left)
        (responseName := responseName) (fieldName := leftFieldName)
        (arguments := leftArguments) (directives := leftDirectives)
        (childSelectionSet := leftChildSelectionSet)
        (fieldDefinition := leftFieldDefinition) hleftMem hleftLookup
    omega
  have hrightLeafFuel :
      leafProbeFuel rightFieldDefinition.outputType ≤ rightFuel := by
    have hlocal :=
      leafProbeFuel_le_selectionSetDeepProbeFuel_of_field_mem schema
        rightParentType (selectionSet := right)
        (responseName := responseName) (fieldName := rightFieldName)
        (arguments := rightArguments) (directives := rightDirectives)
        (childSelectionSet := rightChildSelectionSet)
        (fieldDefinition := rightFieldDefinition) hrightMem hrightLookup
    omega
  simpa [resolvers, leftSource, rightSource] using
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_left_objectOutput_right_leaf_field_pair_of_field_ok_fuels
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet leftCurrentSelectionSet
      rightCurrentSelectionSet leftInitialSpine rightInitialSpine
      leftSpine rightSpine variableValues leftFuel rightFuel
      targetParent leftProbeField rightProbeField leftParentType
      rightParentType leftSourceRuntimeType rightSourceRuntimeType
      targetLeftArguments targetRightArguments leftRuntime rightRuntime
      hleftFree hrightFree hleftNormal hrightNormal hleftObject
      hrightObject hleftMem hrightMem hleftLookup hrightLookup
      ((selectionSetArgumentCoercionSucceeds_of_argumentsCoercible
          hleftCoercion hleftFree)
        responseName leftFieldName leftArguments leftDirectives
        leftChildSelectionSet hleftMem leftFieldDefinition hleftLookup)
      ((selectionSetArgumentCoercionSucceeds_of_argumentsCoercible
          hrightCoercion hrightFree)
        responseName rightFieldName rightArguments rightDirectives
        rightChildSelectionSet hrightMem rightFieldDefinition hrightLookup)
      hleftObjectOutput hrightLeaf hleftLeafFuel hrightLeafFuel
      hleftChildResponse hleftFieldOk hrightFieldOk

theorem
    selectedPathTaggedSelectionSetsResponseDiffWitness_of_left_objectOutput_right_leaf_field_pair_valid_normal_runtimeSpine
    (schema : Schema)
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine leftSpine rightSpine
      : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftProbeField rightProbeField parentType : Name)
    (targetLeftArguments targetRightArguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime : Name) {left right : List Selection}
    {responseName leftFieldName rightFieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {leftFieldDefinition rightFieldDefinition : FieldDefinition}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions parentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
      -> selectionSetArgumentsCoercible schema variableValues parentType left
      -> selectionSetArgumentsCoercible schema variableValues parentType right
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
      -> Selection.field responseName leftFieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName rightFieldName rightArguments
            rightDirectives rightChildSelectionSet
          ∈ right
      -> schema.lookupField parentType leftFieldName = some leftFieldDefinition
      -> schema.lookupField parentType rightFieldName = some rightFieldDefinition
      -> objectTypeNameBool schema leftFieldDefinition.outputType.namedType = true
      -> (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> SelectedPathTaggedSelectionSetsResponseDiffWitness schema
          rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
          leftInitialSpine rightInitialSpine variableValues (fuel + 1)
          parentType parentType targetParent leftProbeField rightProbeField
          targetLeftArguments targetRightArguments leftRuntime rightRuntime
          leftCurrentSelectionSet rightCurrentSelectionSet leftSpine rightSpine
          left right := by
  intro hschema hleftValid hrightValid hleftCoercion hrightCoercion
    hleftFree hrightFree hleftNormal
    hrightNormal hobject hleftFuel hrightFuel hleftSpineValid
    hrightSpineValid hleftSupport hrightSupport hleftContext
    hrightContext hleftMem hrightMem hleftLookup hrightLookup
    hleftObjectOutput hrightLeaf
  rcases
      executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_of_valid_normal_runtimeSpine_support_context_fuel_ge_size
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftInitialSpine rightInitialSpine
        variableValues hschema (SelectionSet.size left + 1) parentType
        leftVariableDefinitions left fuel parentType targetParent
        leftProbeField rightProbeField targetLeftArguments
        targetRightArguments leftRuntime rightRuntime FieldPairProbeTag.left
        leftCurrentSelectionSet leftSpine (by omega) hleftFuel
        hleftValid
        (selectionSetArgumentsCoercibleInPossibleTypes_of_object
          hobject hleftCoercion)
        hleftFree hleftNormal hleftSpineValid hleftSupport
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
        hrightValid
        (selectionSetArgumentsCoercibleInPossibleTypes_of_object
          hobject hrightCoercion)
        hrightFree hrightNormal hrightSpineValid
        hrightSupport
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
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_left_objectOutput_right_leaf_field_pair_of_valid_normal_runtimeSpine
      (schema := schema)
      (leftVariableDefinitions := leftVariableDefinitions)
      (rightVariableDefinitions := rightVariableDefinitions)
      rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet leftInitialSpine
      rightInitialSpine leftSpine rightSpine variableValues fuel
      targetParent leftProbeField rightProbeField parentType parentType
      parentType parentType targetLeftArguments targetRightArguments
      leftRuntime rightRuntime hschema hleftValid hrightValid
      hleftCoercion hrightCoercion hleftFree
      hrightFree hleftNormal hrightNormal hobject hobject hleftFuel
      hrightFuel hleftSpineValid hrightSpineValid hleftSupport
      hrightSupport hleftContext hrightContext hleftMem hrightMem
      hleftLookup hrightLookup hleftObjectOutput hrightLeaf
  refine ⟨
    typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject,
    leftFields,
    leftErrors,
    rightFields,
    rightErrors,
    hleftResponse,
    hrightResponse,
    ?_
  ⟩
  intro hobjects
  exact hdataNot (by simpa [hleftResponse, hrightResponse] using hobjects)

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_left_composite_right_leaf_field_pair_of_selectedPathFieldChildrenReady
    (schema : Schema)
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
    (targetLeftArguments targetRightArguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime : Name) {left right : List Selection}
    {responseName leftFieldName rightFieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {leftFieldDefinition rightFieldDefinition : FieldDefinition}
    : selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema leftParentType left
      -> selectionSetNormal schema rightParentType right
      -> objectTypeNameBool schema leftParentType = true
      -> objectTypeNameBool schema rightParentType = true
      -> Selection.field responseName leftFieldName leftArguments
            leftDirectives leftChildSelectionSet
          ∈ left
      -> Selection.field responseName rightFieldName rightArguments
            rightDirectives rightChildSelectionSet
          ∈ right
      -> schema.lookupField leftParentType leftFieldName = some leftFieldDefinition
      -> schema.lookupField rightParentType rightFieldName = some rightFieldDefinition
      -> leafProbeFuel rightFieldDefinition.outputType ≤ fuel
      -> (TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> SelectedPathSelectionSetFieldChildrenReady schema rootSelectionSet
          leftInitialSelectionSet rightInitialSelectionSet leftCurrentSelectionSet
          leftInitialSpine rightInitialSpine leftSpine variableValues fuel
          targetParent leftProbeField rightProbeField leftParentType
          targetLeftArguments targetRightArguments leftRuntime rightRuntime
          FieldPairProbeTag.left left
      -> SelectedPathSelectionSetFieldChildrenReady schema rootSelectionSet
          leftInitialSelectionSet rightInitialSelectionSet rightCurrentSelectionSet
          leftInitialSpine rightInitialSpine rightSpine variableValues fuel
          targetParent leftProbeField rightProbeField rightParentType
          targetLeftArguments targetRightArguments leftRuntime rightRuntime
          FieldPairProbeTag.right right
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
  intro hleftFree hrightFree hleftNormal hrightNormal hleftObject
    hrightObject hleftMem hrightMem hleftLookup hrightLookup hrightFuel
    hleftComposite hrightLeaf hleftReady hrightReady
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet
      (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
        rightInitialSelectionSet leftInitialSpine rightInitialSpine
        targetParent leftProbeField rightProbeField targetLeftArguments
        targetRightArguments leftRuntime rightRuntime)
      targetParent leftProbeField rightProbeField targetLeftArguments
      targetRightArguments
  let leftSource :=
    projectionTargetResolverValue
      (.object leftSourceRuntimeType
        (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
          leftCurrentSelectionSet leftSpine))
  let rightSource :=
    projectionTargetResolverValue
      (.object rightSourceRuntimeType
        (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
          rightCurrentSelectionSet rightSpine))
  have hleftFieldOk :
      ∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
            childSelectionSet ∈ left ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema resolvers variableValues
              (fuel + 1) leftSource responseName
              [{
                parentType := leftParentType
                responseName := responseName
                fieldName := fieldName
                arguments := arguments
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(responseName, responseValue)], fieldErrors) := by
    dsimp [resolvers, leftSource]
    exact
      executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_field_ok_of_selectedPathFieldChildrenReady
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftCurrentSelectionSet leftInitialSpine
        rightInitialSpine leftSpine variableValues fuel targetParent
        leftProbeField rightProbeField leftParentType
        leftSourceRuntimeType targetLeftArguments targetRightArguments
        leftRuntime rightRuntime FieldPairProbeTag.left left hleftReady
  have hrightFieldOk :
      ∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
            childSelectionSet ∈ right ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema resolvers variableValues
              (fuel + 1) rightSource responseName
              [{
                parentType := rightParentType
                responseName := responseName
                fieldName := fieldName
                arguments := arguments
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(responseName, responseValue)], fieldErrors) := by
    dsimp [resolvers, rightSource]
    exact
      executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_field_ok_of_selectedPathFieldChildrenReady
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet rightCurrentSelectionSet leftInitialSpine
        rightInitialSpine rightSpine variableValues fuel targetParent
        leftProbeField rightProbeField rightParentType
        rightSourceRuntimeType targetLeftArguments targetRightArguments
        leftRuntime rightRuntime FieldPairProbeTag.right right hrightReady
  rcases
      hrightReady responseName rightFieldName rightArguments rightDirectives
        rightChildSelectionSet hrightMem with
    ⟨rightFieldDefinition', hrightLookup', hrightCoercion, _hrightFuel,
      _hrightCase⟩
  have hrightDefinitionEq :
      rightFieldDefinition' = rightFieldDefinition := by
    rw [hrightLookup] at hrightLookup'
    exact Option.some.inj hrightLookup'.symm
  subst rightFieldDefinition'
  have hrightTarget :
      Execution.executeField schema resolvers variableValues (fuel + 1)
        rightSource responseName
        [{
          parentType := rightParentType
          responseName := responseName
          fieldName := rightFieldName
          arguments := rightArguments
          selectionSet := rightChildSelectionSet
        }]
      =
      .ok ([(responseName,
        leafProbeResponseValue rightFieldDefinition.outputType
          FieldPairProbeTag.right.scalar)], 0) := by
    dsimp [resolvers, rightSource]
    exact
      executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_leaf
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet rightCurrentSelectionSet leftInitialSpine
        rightInitialSpine rightSpine variableValues fuel targetParent
        leftProbeField rightProbeField rightParentType rightFieldName
        rightSourceRuntimeType responseName targetLeftArguments
        targetRightArguments rightArguments leftRuntime rightRuntime
        FieldPairProbeTag.right rightChildSelectionSet rightFieldDefinition
        hrightLookup hrightCoercion hrightFuel hrightLeaf
  rcases
      hleftReady responseName leftFieldName leftArguments leftDirectives
        leftChildSelectionSet hleftMem with
    ⟨leftFieldDefinition', hleftLookup', hleftCoercion, hleftFuel, hleftCase⟩
  have hleftDefinitionEq :
      leftFieldDefinition' = leftFieldDefinition := by
    rw [hleftLookup] at hleftLookup'
    exact Option.some.inj hleftLookup'.symm
  subst leftFieldDefinition'
  rcases hleftCase with hleftLeaf | hleftCase
  · rw [hleftComposite] at hleftLeaf
    simp at hleftLeaf
  rcases hleftCase with hselectedChild | hleftCase
  · rcases hselectedChild with
      ⟨leftChildRuntime, leftTail, leftChildFields, leftChildErrors,
        hleftSelected, hleftRuntimeCase, hleftInclude,
        hleftChildResponse⟩
    rcases
        wrapTypeRefSelectionSetResult_ok_nonNull_of_object_response
          leftFieldDefinition.outputType leftChildFields leftChildErrors with
      ⟨leftResponseValue, leftFieldErrors, hleftWrapped,
        _hleftNonNull⟩
    have hleftTarget :
        Execution.executeField schema resolvers variableValues (fuel + 1)
          leftSource responseName
          [{
            parentType := leftParentType
            responseName := responseName
            fieldName := leftFieldName
            arguments := leftArguments
            selectionSet := leftChildSelectionSet
          }]
        =
        .ok ([(responseName, leftResponseValue)], leftFieldErrors) := by
      dsimp [resolvers, leftSource]
      rw [
        executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_objectProbe_response_of_fuel_ge
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet leftCurrentSelectionSet
          leftInitialSpine rightInitialSpine leftSpine leftTail
          variableValues fuel targetParent leftProbeField rightProbeField
          leftParentType leftFieldName leftSourceRuntimeType responseName
          targetLeftArguments targetRightArguments leftArguments
          leftRuntime rightRuntime FieldPairProbeTag.left
          leftChildSelectionSet leftFieldDefinition leftChildRuntime
          hleftLookup hleftCoercion hleftSelected hleftRuntimeCase hleftInclude
          hleftFuel]
      rw [hleftChildResponse]
      simp [Execution.singleFieldResult, hleftWrapped]
    have hleafObjectNot :
        ¬ Execution.ResponseValue.semanticEquivalent
          (leafProbeResponseValue rightFieldDefinition.outputType
            FieldPairProbeTag.right.scalar)
          leftResponseValue :=
      leafProbeResponseValue_not_semanticEquivalent_wrapped_object_of_composite
        schema rightFieldDefinition.outputType leftFieldDefinition.outputType
        FieldPairProbeTag.right.scalar leftResponseValue leftFieldErrors
        leftChildFields leftChildErrors hrightLeaf hleftComposite
        hleftWrapped
    have hvalueNot :
        ¬ Execution.ResponseValue.semanticEquivalent leftResponseValue
          (leafProbeResponseValue rightFieldDefinition.outputType
            FieldPairProbeTag.right.scalar) := by
      intro hsemantic
      exact hleafObjectNot hsemantic.symm
    exact
      SemanticSeparation.responseData_not_semanticEquivalent_of_field_value_diff_of_field_ok_pair
        resolvers resolvers variableValues (fuel + 1) leftSource rightSource
        hleftObject hrightObject hleftNormal hrightNormal hleftFree
        hrightFree hleftMem hrightMem hleftTarget hrightTarget hvalueNot
        hleftFieldOk hrightFieldOk
  rcases hleftCase with hobjectOutput | habstractFallback
  · rcases hobjectOutput with
      ⟨leftChildFields, leftChildErrors, hleftObjectOutput,
        hleftChildResponse⟩
    rcases
        wrapTypeRefSelectionSetResult_ok_nonNull_of_object_response
          leftFieldDefinition.outputType leftChildFields leftChildErrors with
      ⟨leftResponseValue, leftFieldErrors, hleftWrapped,
        _hleftNonNull⟩
    have hleftTarget :
        Execution.executeField schema resolvers variableValues (fuel + 1)
          leftSource responseName
          [{
            parentType := leftParentType
            responseName := responseName
            fieldName := leftFieldName
            arguments := leftArguments
            selectionSet := leftChildSelectionSet
          }]
        =
        .ok ([(responseName, leftResponseValue)], leftFieldErrors) := by
      dsimp [resolvers, leftSource]
      rw [
        executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_objectOutput_response_of_fuel_ge
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet leftCurrentSelectionSet leftInitialSpine
          rightInitialSpine leftSpine variableValues fuel targetParent
          leftProbeField rightProbeField leftParentType leftFieldName
          leftSourceRuntimeType responseName targetLeftArguments
          targetRightArguments leftArguments leftRuntime rightRuntime
          FieldPairProbeTag.left leftChildSelectionSet leftFieldDefinition
          hleftLookup hleftCoercion hleftObjectOutput hleftFuel]
      rw [hleftChildResponse]
      simp [Execution.singleFieldResult, hleftWrapped]
    have hleafObjectNot :
        ¬ Execution.ResponseValue.semanticEquivalent
          (leafProbeResponseValue rightFieldDefinition.outputType
            FieldPairProbeTag.right.scalar)
          leftResponseValue :=
      leafProbeResponseValue_not_semanticEquivalent_wrapped_object_of_composite
        schema rightFieldDefinition.outputType leftFieldDefinition.outputType
        FieldPairProbeTag.right.scalar leftResponseValue leftFieldErrors
        leftChildFields leftChildErrors hrightLeaf hleftComposite
        hleftWrapped
    have hvalueNot :
        ¬ Execution.ResponseValue.semanticEquivalent leftResponseValue
          (leafProbeResponseValue rightFieldDefinition.outputType
            FieldPairProbeTag.right.scalar) := by
      intro hsemantic
      exact hleafObjectNot hsemantic.symm
    exact
      SemanticSeparation.responseData_not_semanticEquivalent_of_field_value_diff_of_field_ok_pair
        resolvers resolvers variableValues (fuel + 1) leftSource rightSource
        hleftObject hrightObject hleftNormal hrightNormal hleftFree
        hrightFree hleftMem hrightMem hleftTarget hrightTarget hvalueNot
        hleftFieldOk hrightFieldOk
  · rcases habstractFallback with
      ⟨leftChildRuntime, leftChildFields, leftChildErrors,
        hleftCompositeFallback, hleftNonObject, hleftSelectedNone,
        hleftRuntime, hleftInclude, hleftChildResponse⟩
    rcases
        wrapTypeRefSelectionSetResult_ok_nonNull_of_object_response
          leftFieldDefinition.outputType leftChildFields leftChildErrors with
      ⟨leftResponseValue, leftFieldErrors, hleftWrapped,
        _hleftNonNull⟩
    have hleftTarget :
        Execution.executeField schema resolvers variableValues (fuel + 1)
          leftSource responseName
          [{
            parentType := leftParentType
            responseName := responseName
            fieldName := leftFieldName
            arguments := leftArguments
            selectionSet := leftChildSelectionSet
          }]
        =
        .ok ([(responseName, leftResponseValue)], leftFieldErrors) := by
      dsimp [resolvers, leftSource]
      rw [
        executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_abstractFallback_response_of_fuel_ge
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet leftCurrentSelectionSet leftInitialSpine
          rightInitialSpine leftSpine variableValues fuel targetParent
          leftProbeField rightProbeField leftParentType leftFieldName
          leftSourceRuntimeType responseName targetLeftArguments
          targetRightArguments leftArguments leftRuntime rightRuntime
          FieldPairProbeTag.left leftChildSelectionSet leftFieldDefinition
          leftChildRuntime hleftLookup hleftCoercion hleftCompositeFallback
          hleftNonObject hleftSelectedNone hleftRuntime hleftInclude
          hleftFuel]
      rw [hleftChildResponse]
      simp [Execution.singleFieldResult, hleftWrapped]
    have hleafObjectNot :
        ¬ Execution.ResponseValue.semanticEquivalent
          (leafProbeResponseValue rightFieldDefinition.outputType
            FieldPairProbeTag.right.scalar)
          leftResponseValue :=
      leafProbeResponseValue_not_semanticEquivalent_wrapped_object_of_composite
        schema rightFieldDefinition.outputType leftFieldDefinition.outputType
        FieldPairProbeTag.right.scalar leftResponseValue leftFieldErrors
        leftChildFields leftChildErrors hrightLeaf hleftComposite
        hleftWrapped
    have hvalueNot :
        ¬ Execution.ResponseValue.semanticEquivalent leftResponseValue
          (leafProbeResponseValue rightFieldDefinition.outputType
            FieldPairProbeTag.right.scalar) := by
      intro hsemantic
      exact hleafObjectNot hsemantic.symm
    exact
      SemanticSeparation.responseData_not_semanticEquivalent_of_field_value_diff_of_field_ok_pair
        resolvers resolvers variableValues (fuel + 1) leftSource rightSource
        hleftObject hrightObject hleftNormal hrightNormal hleftFree
        hrightFree hleftMem hrightMem hleftTarget hrightTarget hvalueNot
        hleftFieldOk hrightFieldOk

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_left_composite_right_leaf_field_pair_of_selectedPathFieldChildrenReady_fuels
    (schema : Schema)
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
    (targetLeftArguments targetRightArguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime : Name) {left right : List Selection}
    {responseName leftFieldName rightFieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {leftFieldDefinition rightFieldDefinition : FieldDefinition}
    : selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema leftParentType left
      -> selectionSetNormal schema rightParentType right
      -> objectTypeNameBool schema leftParentType = true
      -> objectTypeNameBool schema rightParentType = true
      -> Selection.field responseName leftFieldName leftArguments
            leftDirectives leftChildSelectionSet
          ∈ left
      -> Selection.field responseName rightFieldName rightArguments
            rightDirectives rightChildSelectionSet
          ∈ right
      -> schema.lookupField leftParentType leftFieldName = some leftFieldDefinition
      -> schema.lookupField rightParentType rightFieldName = some rightFieldDefinition
      -> leafProbeFuel rightFieldDefinition.outputType ≤ rightFuel
      -> (TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> SelectedPathSelectionSetFieldChildrenReady schema rootSelectionSet
          leftInitialSelectionSet rightInitialSelectionSet leftCurrentSelectionSet
          leftInitialSpine rightInitialSpine leftSpine variableValues leftFuel
          targetParent leftProbeField rightProbeField leftParentType
          targetLeftArguments targetRightArguments leftRuntime rightRuntime
          FieldPairProbeTag.left left
      -> SelectedPathSelectionSetFieldChildrenReady schema rootSelectionSet
          leftInitialSelectionSet rightInitialSelectionSet rightCurrentSelectionSet
          leftInitialSpine rightInitialSpine rightSpine variableValues rightFuel
          targetParent leftProbeField rightProbeField rightParentType
          targetLeftArguments targetRightArguments leftRuntime rightRuntime
          FieldPairProbeTag.right right
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
  intro hleftFree hrightFree hleftNormal hrightNormal hleftObject
    hrightObject hleftMem hrightMem hleftLookup hrightLookup hrightFuel
    hleftComposite hrightLeaf hleftReady hrightReady
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet
      (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
        rightInitialSelectionSet leftInitialSpine rightInitialSpine
        targetParent leftProbeField rightProbeField targetLeftArguments
        targetRightArguments leftRuntime rightRuntime)
      targetParent leftProbeField rightProbeField targetLeftArguments
      targetRightArguments
  let leftSource :=
    projectionTargetResolverValue
      (.object leftSourceRuntimeType
        (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
          leftCurrentSelectionSet leftSpine))
  let rightSource :=
    projectionTargetResolverValue
      (.object rightSourceRuntimeType
        (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
          rightCurrentSelectionSet rightSpine))
  have hleftFieldOk :
      ∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
            childSelectionSet ∈ left ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema resolvers variableValues
              (leftFuel + 1) leftSource responseName
              [{
                parentType := leftParentType
                responseName := responseName
                fieldName := fieldName
                arguments := arguments
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(responseName, responseValue)], fieldErrors) := by
    dsimp [resolvers, leftSource]
    exact
      executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_field_ok_of_selectedPathFieldChildrenReady
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftCurrentSelectionSet leftInitialSpine
        rightInitialSpine leftSpine variableValues leftFuel targetParent
        leftProbeField rightProbeField leftParentType
        leftSourceRuntimeType targetLeftArguments targetRightArguments
        leftRuntime rightRuntime FieldPairProbeTag.left left hleftReady
  have hrightFieldOk :
      ∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
            childSelectionSet ∈ right ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema resolvers variableValues
              (rightFuel + 1) rightSource responseName
              [{
                parentType := rightParentType
                responseName := responseName
                fieldName := fieldName
                arguments := arguments
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(responseName, responseValue)], fieldErrors) := by
    dsimp [resolvers, rightSource]
    exact
      executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_field_ok_of_selectedPathFieldChildrenReady
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet rightCurrentSelectionSet leftInitialSpine
        rightInitialSpine rightSpine variableValues rightFuel targetParent
        leftProbeField rightProbeField rightParentType
        rightSourceRuntimeType targetLeftArguments targetRightArguments
        leftRuntime rightRuntime FieldPairProbeTag.right right hrightReady
  rcases
      hrightReady responseName rightFieldName rightArguments rightDirectives
        rightChildSelectionSet hrightMem with
    ⟨rightFieldDefinition', hrightLookup', hrightCoercion, _hrightFuel,
      _hrightCase⟩
  have hrightDefinitionEq :
      rightFieldDefinition' = rightFieldDefinition := by
    rw [hrightLookup] at hrightLookup'
    exact Option.some.inj hrightLookup'.symm
  subst rightFieldDefinition'
  have hrightTarget :
      Execution.executeField schema resolvers variableValues
        (rightFuel + 1) rightSource responseName
        [{
          parentType := rightParentType
          responseName := responseName
          fieldName := rightFieldName
          arguments := rightArguments
          selectionSet := rightChildSelectionSet
        }]
      =
      .ok ([(responseName,
        leafProbeResponseValue rightFieldDefinition.outputType
          FieldPairProbeTag.right.scalar)], 0) := by
    dsimp [resolvers, rightSource]
    exact
      executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_leaf
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet rightCurrentSelectionSet leftInitialSpine
        rightInitialSpine rightSpine variableValues rightFuel targetParent
        leftProbeField rightProbeField rightParentType rightFieldName
        rightSourceRuntimeType responseName targetLeftArguments
        targetRightArguments rightArguments leftRuntime rightRuntime
        FieldPairProbeTag.right rightChildSelectionSet rightFieldDefinition
        hrightLookup hrightCoercion hrightFuel hrightLeaf
  rcases
      hleftReady responseName leftFieldName leftArguments leftDirectives
        leftChildSelectionSet hleftMem with
    ⟨leftFieldDefinition', hleftLookup', hleftCoercion, hleftFuel, hleftCase⟩
  have hleftDefinitionEq :
      leftFieldDefinition' = leftFieldDefinition := by
    rw [hleftLookup] at hleftLookup'
    exact Option.some.inj hleftLookup'.symm
  subst leftFieldDefinition'
  rcases hleftCase with hleftLeaf | hleftCase
  · rw [hleftComposite] at hleftLeaf
    simp at hleftLeaf
  rcases hleftCase with hselectedChild | hleftCase
  · rcases hselectedChild with
      ⟨leftChildRuntime, leftTail, leftChildFields, leftChildErrors,
        hleftSelected, hleftRuntimeCase, hleftInclude,
        hleftChildResponse⟩
    rcases
        wrapTypeRefSelectionSetResult_ok_nonNull_of_object_response
          leftFieldDefinition.outputType leftChildFields leftChildErrors with
      ⟨leftResponseValue, leftFieldErrors, hleftWrapped,
        _hleftNonNull⟩
    have hleftTarget :
        Execution.executeField schema resolvers variableValues
          (leftFuel + 1) leftSource responseName
          [{
            parentType := leftParentType
            responseName := responseName
            fieldName := leftFieldName
            arguments := leftArguments
            selectionSet := leftChildSelectionSet
          }]
        =
        .ok ([(responseName, leftResponseValue)], leftFieldErrors) := by
      dsimp [resolvers, leftSource]
      rw [
        executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_objectProbe_response_of_fuel_ge
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet leftCurrentSelectionSet
          leftInitialSpine rightInitialSpine leftSpine leftTail
          variableValues leftFuel targetParent leftProbeField
          rightProbeField leftParentType leftFieldName
          leftSourceRuntimeType responseName targetLeftArguments
          targetRightArguments leftArguments leftRuntime rightRuntime
          FieldPairProbeTag.left leftChildSelectionSet leftFieldDefinition
          leftChildRuntime hleftLookup hleftCoercion hleftSelected
          hleftRuntimeCase hleftInclude hleftFuel]
      rw [hleftChildResponse]
      simp [Execution.singleFieldResult, hleftWrapped]
    have hleafObjectNot :
        ¬ Execution.ResponseValue.semanticEquivalent
          (leafProbeResponseValue rightFieldDefinition.outputType
            FieldPairProbeTag.right.scalar)
          leftResponseValue :=
      leafProbeResponseValue_not_semanticEquivalent_wrapped_object_of_composite
        schema rightFieldDefinition.outputType leftFieldDefinition.outputType
        FieldPairProbeTag.right.scalar leftResponseValue leftFieldErrors
        leftChildFields leftChildErrors hrightLeaf hleftComposite
        hleftWrapped
    have hvalueNot :
        ¬ Execution.ResponseValue.semanticEquivalent leftResponseValue
          (leafProbeResponseValue rightFieldDefinition.outputType
            FieldPairProbeTag.right.scalar) := by
      intro hsemantic
      exact hleafObjectNot hsemantic.symm
    exact
      SemanticSeparation.responseData_not_semanticEquivalent_of_field_value_diff_of_field_ok_pair_fuels
        resolvers resolvers variableValues (leftFuel + 1)
        (rightFuel + 1) leftSource rightSource hleftObject hrightObject
        hleftNormal hrightNormal hleftFree hrightFree hleftMem
        hrightMem hleftTarget hrightTarget hvalueNot hleftFieldOk
        hrightFieldOk
  rcases hleftCase with hobjectOutput | habstractFallback
  · rcases hobjectOutput with
      ⟨leftChildFields, leftChildErrors, hleftObjectOutput,
        hleftChildResponse⟩
    rcases
        wrapTypeRefSelectionSetResult_ok_nonNull_of_object_response
          leftFieldDefinition.outputType leftChildFields leftChildErrors with
      ⟨leftResponseValue, leftFieldErrors, hleftWrapped,
        _hleftNonNull⟩
    have hleftTarget :
        Execution.executeField schema resolvers variableValues
          (leftFuel + 1) leftSource responseName
          [{
            parentType := leftParentType
            responseName := responseName
            fieldName := leftFieldName
            arguments := leftArguments
            selectionSet := leftChildSelectionSet
          }]
        =
        .ok ([(responseName, leftResponseValue)], leftFieldErrors) := by
      dsimp [resolvers, leftSource]
      rw [
        executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_objectOutput_response_of_fuel_ge
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet leftCurrentSelectionSet leftInitialSpine
          rightInitialSpine leftSpine variableValues leftFuel targetParent
          leftProbeField rightProbeField leftParentType leftFieldName
          leftSourceRuntimeType responseName targetLeftArguments
          targetRightArguments leftArguments leftRuntime rightRuntime
          FieldPairProbeTag.left leftChildSelectionSet
          leftFieldDefinition hleftLookup hleftCoercion hleftObjectOutput hleftFuel]
      rw [hleftChildResponse]
      simp [Execution.singleFieldResult, hleftWrapped]
    have hleafObjectNot :
        ¬ Execution.ResponseValue.semanticEquivalent
          (leafProbeResponseValue rightFieldDefinition.outputType
            FieldPairProbeTag.right.scalar)
          leftResponseValue :=
      leafProbeResponseValue_not_semanticEquivalent_wrapped_object_of_composite
        schema rightFieldDefinition.outputType leftFieldDefinition.outputType
        FieldPairProbeTag.right.scalar leftResponseValue leftFieldErrors
        leftChildFields leftChildErrors hrightLeaf hleftComposite
        hleftWrapped
    have hvalueNot :
        ¬ Execution.ResponseValue.semanticEquivalent leftResponseValue
          (leafProbeResponseValue rightFieldDefinition.outputType
            FieldPairProbeTag.right.scalar) := by
      intro hsemantic
      exact hleafObjectNot hsemantic.symm
    exact
      SemanticSeparation.responseData_not_semanticEquivalent_of_field_value_diff_of_field_ok_pair_fuels
        resolvers resolvers variableValues (leftFuel + 1)
        (rightFuel + 1) leftSource rightSource hleftObject hrightObject
        hleftNormal hrightNormal hleftFree hrightFree hleftMem
        hrightMem hleftTarget hrightTarget hvalueNot hleftFieldOk
        hrightFieldOk
  · rcases habstractFallback with
      ⟨leftChildRuntime, leftChildFields, leftChildErrors,
        hleftCompositeFallback, hleftNonObject, hleftSelectedNone,
        hleftRuntime, hleftInclude, hleftChildResponse⟩
    rcases
        wrapTypeRefSelectionSetResult_ok_nonNull_of_object_response
          leftFieldDefinition.outputType leftChildFields leftChildErrors with
      ⟨leftResponseValue, leftFieldErrors, hleftWrapped,
        _hleftNonNull⟩
    have hleftTarget :
        Execution.executeField schema resolvers variableValues
          (leftFuel + 1) leftSource responseName
          [{
            parentType := leftParentType
            responseName := responseName
            fieldName := leftFieldName
            arguments := leftArguments
            selectionSet := leftChildSelectionSet
          }]
        =
        .ok ([(responseName, leftResponseValue)], leftFieldErrors) := by
      dsimp [resolvers, leftSource]
      rw [
        executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_abstractFallback_response_of_fuel_ge
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet leftCurrentSelectionSet leftInitialSpine
          rightInitialSpine leftSpine variableValues leftFuel targetParent
          leftProbeField rightProbeField leftParentType leftFieldName
          leftSourceRuntimeType responseName targetLeftArguments
          targetRightArguments leftArguments leftRuntime rightRuntime
          FieldPairProbeTag.left leftChildSelectionSet
          leftFieldDefinition leftChildRuntime hleftLookup
          hleftCoercion hleftCompositeFallback hleftNonObject hleftSelectedNone
          hleftRuntime hleftInclude hleftFuel]
      rw [hleftChildResponse]
      simp [Execution.singleFieldResult, hleftWrapped]
    have hleafObjectNot :
        ¬ Execution.ResponseValue.semanticEquivalent
          (leafProbeResponseValue rightFieldDefinition.outputType
            FieldPairProbeTag.right.scalar)
          leftResponseValue :=
      leafProbeResponseValue_not_semanticEquivalent_wrapped_object_of_composite
        schema rightFieldDefinition.outputType leftFieldDefinition.outputType
        FieldPairProbeTag.right.scalar leftResponseValue leftFieldErrors
        leftChildFields leftChildErrors hrightLeaf hleftComposite
        hleftWrapped
    have hvalueNot :
        ¬ Execution.ResponseValue.semanticEquivalent leftResponseValue
          (leafProbeResponseValue rightFieldDefinition.outputType
            FieldPairProbeTag.right.scalar) := by
      intro hsemantic
      exact hleafObjectNot hsemantic.symm
    exact
      SemanticSeparation.responseData_not_semanticEquivalent_of_field_value_diff_of_field_ok_pair_fuels
        resolvers resolvers variableValues (leftFuel + 1)
        (rightFuel + 1) leftSource rightSource hleftObject hrightObject
        hleftNormal hrightNormal hleftFree hrightFree hleftMem
        hrightMem hleftTarget hrightTarget hvalueNot hleftFieldOk
        hrightFieldOk

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_left_composite_right_leaf_field_pair_of_valid_normal_runtimeSpine
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
    (targetLeftArguments targetRightArguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime : Name) {left right : List Selection}
    {responseName leftFieldName rightFieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {leftFieldDefinition rightFieldDefinition : FieldDefinition}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions leftParentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions
          rightParentType right
      -> selectionSetArgumentsCoercible schema variableValues leftParentType left
      -> selectionSetArgumentsCoercible schema variableValues rightParentType right
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
  intro hschema hleftValid hrightValid hleftCoercion hrightCoercion
    hleftFree hrightFree hleftNormal
    hrightNormal hleftObject hrightObject hleftFuel hrightFuel
    hleftSpineValid hrightSpineValid hleftSupport hrightSupport
    hleftContext hrightContext hleftMem hrightMem hleftLookup
    hrightLookup hleftComposite hrightLeaf
  have hleftReady :
      SelectedPathSelectionSetFieldChildrenReady schema rootSelectionSet
        leftInitialSelectionSet rightInitialSelectionSet
        leftCurrentSelectionSet leftInitialSpine rightInitialSpine
        leftSpine variableValues fuel targetParent leftProbeField
        rightProbeField leftParentType targetLeftArguments
        targetRightArguments leftRuntime rightRuntime FieldPairProbeTag.left
        left :=
    selectedPathSelectionSetFieldChildrenReady_of_valid_normal_runtimeSpine_support_context_fuel_ge
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet leftInitialSpine rightInitialSpine
      variableValues hschema leftParentType leftVariableDefinitions left
      fuel leftSourceRuntimeType targetParent leftProbeField
      rightProbeField targetLeftArguments targetRightArguments
      leftRuntime rightRuntime FieldPairProbeTag.left leftCurrentSelectionSet
      leftSpine hleftFuel hleftValid hleftCoercion hleftFree hleftNormal hleftObject
      hleftSpineValid hleftSupport hleftContext
  have hrightReady :
      SelectedPathSelectionSetFieldChildrenReady schema rootSelectionSet
        leftInitialSelectionSet rightInitialSelectionSet
        rightCurrentSelectionSet leftInitialSpine rightInitialSpine
        rightSpine variableValues fuel targetParent leftProbeField
        rightProbeField rightParentType targetLeftArguments
        targetRightArguments leftRuntime rightRuntime FieldPairProbeTag.right
        right :=
    selectedPathSelectionSetFieldChildrenReady_of_valid_normal_runtimeSpine_support_context_fuel_ge
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet leftInitialSpine rightInitialSpine
      variableValues hschema rightParentType rightVariableDefinitions right
      fuel rightSourceRuntimeType targetParent leftProbeField
      rightProbeField targetLeftArguments targetRightArguments
      leftRuntime rightRuntime FieldPairProbeTag.right rightCurrentSelectionSet
      rightSpine hrightFuel hrightValid hrightCoercion hrightFree hrightNormal
      hrightObject hrightSpineValid hrightSupport hrightContext
  have hrightLeafFuel :
      leafProbeFuel rightFieldDefinition.outputType ≤ fuel := by
    have hlocal :=
      leafProbeFuel_le_selectionSetDeepProbeFuel_of_field_mem schema
        rightParentType (selectionSet := right)
        (responseName := responseName) (fieldName := rightFieldName)
        (arguments := rightArguments) (directives := rightDirectives)
        (childSelectionSet := rightChildSelectionSet)
        (fieldDefinition := rightFieldDefinition) hrightMem
        hrightLookup
    omega
  exact
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_left_composite_right_leaf_field_pair_of_selectedPathFieldChildrenReady
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet leftCurrentSelectionSet
      rightCurrentSelectionSet leftInitialSpine rightInitialSpine
      leftSpine rightSpine variableValues fuel targetParent
      leftProbeField rightProbeField leftParentType rightParentType
      leftSourceRuntimeType rightSourceRuntimeType targetLeftArguments
      targetRightArguments leftRuntime rightRuntime hleftFree hrightFree
      hleftNormal hrightNormal hleftObject hrightObject hleftMem
      hrightMem hleftLookup hrightLookup hrightLeafFuel hleftComposite
      hrightLeaf hleftReady hrightReady

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_left_composite_right_leaf_field_pair_of_valid_normal_runtimeSpine_fuels
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
    (targetLeftArguments targetRightArguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime : Name) {left right : List Selection}
    {responseName leftFieldName rightFieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {leftFieldDefinition rightFieldDefinition : FieldDefinition}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions leftParentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions
          rightParentType right
      -> selectionSetArgumentsCoercible schema variableValues leftParentType left
      -> selectionSetArgumentsCoercible schema variableValues rightParentType right
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
  intro hschema hleftValid hrightValid hleftCoercion hrightCoercion
    hleftFree hrightFree hleftNormal
    hrightNormal hleftObject hrightObject hleftFuel hrightFuel
    hleftSpineValid hrightSpineValid hleftSupport hrightSupport
    hleftContext hrightContext hleftMem hrightMem hleftLookup
    hrightLookup hleftComposite hrightLeaf
  have hleftReady :
      SelectedPathSelectionSetFieldChildrenReady schema rootSelectionSet
        leftInitialSelectionSet rightInitialSelectionSet
        leftCurrentSelectionSet leftInitialSpine rightInitialSpine
        leftSpine variableValues leftFuel targetParent leftProbeField
        rightProbeField leftParentType targetLeftArguments
        targetRightArguments leftRuntime rightRuntime FieldPairProbeTag.left
        left :=
    selectedPathSelectionSetFieldChildrenReady_of_valid_normal_runtimeSpine_support_context_fuel_ge
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet leftInitialSpine rightInitialSpine
      variableValues hschema leftParentType leftVariableDefinitions left
      leftFuel leftSourceRuntimeType targetParent leftProbeField
      rightProbeField targetLeftArguments targetRightArguments
      leftRuntime rightRuntime FieldPairProbeTag.left leftCurrentSelectionSet
      leftSpine hleftFuel hleftValid hleftCoercion hleftFree hleftNormal hleftObject
      hleftSpineValid hleftSupport hleftContext
  have hrightReady :
      SelectedPathSelectionSetFieldChildrenReady schema rootSelectionSet
        leftInitialSelectionSet rightInitialSelectionSet
        rightCurrentSelectionSet leftInitialSpine rightInitialSpine
        rightSpine variableValues rightFuel targetParent leftProbeField
        rightProbeField rightParentType targetLeftArguments
        targetRightArguments leftRuntime rightRuntime FieldPairProbeTag.right
        right :=
    selectedPathSelectionSetFieldChildrenReady_of_valid_normal_runtimeSpine_support_context_fuel_ge
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet leftInitialSpine rightInitialSpine
      variableValues hschema rightParentType rightVariableDefinitions right
      rightFuel rightSourceRuntimeType targetParent leftProbeField
      rightProbeField targetLeftArguments targetRightArguments
      leftRuntime rightRuntime FieldPairProbeTag.right rightCurrentSelectionSet
      rightSpine hrightFuel hrightValid hrightCoercion hrightFree hrightNormal
      hrightObject hrightSpineValid hrightSupport hrightContext
  have hrightLeafFuel :
      leafProbeFuel rightFieldDefinition.outputType ≤ rightFuel := by
    have hlocal :=
      leafProbeFuel_le_selectionSetDeepProbeFuel_of_field_mem schema
        rightParentType (selectionSet := right)
        (responseName := responseName) (fieldName := rightFieldName)
        (arguments := rightArguments) (directives := rightDirectives)
        (childSelectionSet := rightChildSelectionSet)
        (fieldDefinition := rightFieldDefinition) hrightMem
        hrightLookup
    omega
  exact
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_left_composite_right_leaf_field_pair_of_selectedPathFieldChildrenReady_fuels
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet leftCurrentSelectionSet
      rightCurrentSelectionSet leftInitialSpine rightInitialSpine
      leftSpine rightSpine variableValues leftFuel rightFuel targetParent
      leftProbeField rightProbeField leftParentType rightParentType
      leftSourceRuntimeType rightSourceRuntimeType targetLeftArguments
      targetRightArguments leftRuntime rightRuntime hleftFree hrightFree
      hleftNormal hrightNormal hleftObject hrightObject hleftMem
      hrightMem hleftLookup hrightLookup hrightLeafFuel hleftComposite
      hrightLeaf hleftReady hrightReady

theorem
    selectedPathTaggedSelectionSetsResponseDiffWitness_of_left_composite_right_leaf_field_pair_valid_normal_runtimeSpine
    (schema : Schema)
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine leftSpine rightSpine
      : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftProbeField rightProbeField parentType : Name)
    (targetLeftArguments targetRightArguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime : Name) {left right : List Selection}
    {responseName leftFieldName rightFieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {leftFieldDefinition rightFieldDefinition : FieldDefinition}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions parentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
      -> selectionSetArgumentsCoercible schema variableValues parentType left
      -> selectionSetArgumentsCoercible schema variableValues parentType right
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
      -> Selection.field responseName leftFieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName rightFieldName rightArguments
            rightDirectives rightChildSelectionSet
          ∈ right
      -> schema.lookupField parentType leftFieldName = some leftFieldDefinition
      -> schema.lookupField parentType rightFieldName = some rightFieldDefinition
      -> (TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> SelectedPathTaggedSelectionSetsResponseDiffWitness schema
          rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
          leftInitialSpine rightInitialSpine variableValues (fuel + 1)
          parentType parentType targetParent leftProbeField rightProbeField
          targetLeftArguments targetRightArguments leftRuntime rightRuntime
          leftCurrentSelectionSet rightCurrentSelectionSet leftSpine rightSpine
          left right := by
  intro hschema hleftValid hrightValid hleftCoercion hrightCoercion
    hleftFree hrightFree hleftNormal
    hrightNormal hobject hleftFuel hrightFuel hleftSpineValid
    hrightSpineValid hleftSupport hrightSupport hleftContext
    hrightContext hleftMem hrightMem hleftLookup hrightLookup
    hleftComposite hrightLeaf
  rcases
      executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_of_valid_normal_runtimeSpine_support_context_fuel_ge_size
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftInitialSpine rightInitialSpine
        variableValues hschema (SelectionSet.size left + 1) parentType
        leftVariableDefinitions left fuel parentType targetParent
        leftProbeField rightProbeField targetLeftArguments
        targetRightArguments leftRuntime rightRuntime FieldPairProbeTag.left
        leftCurrentSelectionSet leftSpine (by omega) hleftFuel
        hleftValid
        (selectionSetArgumentsCoercibleInPossibleTypes_of_object
          hobject hleftCoercion)
        hleftFree hleftNormal hleftSpineValid hleftSupport
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
        hrightValid
        (selectionSetArgumentsCoercibleInPossibleTypes_of_object
          hobject hrightCoercion)
        hrightFree hrightNormal hrightSpineValid
        hrightSupport
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
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_left_composite_right_leaf_field_pair_of_valid_normal_runtimeSpine
      (schema := schema)
      (leftVariableDefinitions := leftVariableDefinitions)
      (rightVariableDefinitions := rightVariableDefinitions)
      rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet leftInitialSpine
      rightInitialSpine leftSpine rightSpine variableValues fuel
      targetParent leftProbeField rightProbeField parentType parentType
      parentType parentType targetLeftArguments targetRightArguments
      leftRuntime rightRuntime hschema hleftValid hrightValid hleftCoercion
      hrightCoercion hleftFree hrightFree hleftNormal hrightNormal hobject hobject hleftFuel
      hrightFuel hleftSpineValid hrightSpineValid hleftSupport
      hrightSupport hleftContext hrightContext hleftMem hrightMem
      hleftLookup hrightLookup hleftComposite hrightLeaf
  refine ⟨
    typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject,
    leftFields,
    leftErrors,
    rightFields,
    rightErrors,
    hleftResponse,
    hrightResponse,
    ?_
  ⟩
  intro hobjects
  exact hdataNot (by simpa [hleftResponse, hrightResponse] using hobjects)

end GroundTypeNormalization

end NormalForm

end GraphQL
