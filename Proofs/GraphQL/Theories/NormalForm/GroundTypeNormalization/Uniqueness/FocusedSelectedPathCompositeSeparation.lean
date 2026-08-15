import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.FocusedSelectedPathLeafSeparation

/-!
Composite-child lifting and object-output witness construction.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_left_leaf_right_composite_field_pair_of_selectedPathFieldChildrenReady
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
    (targetLeftArguments targetRightArguments : List Argument)
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
      -> leafProbeFuel leftFieldDefinition.outputType ≤ fuel
      -> (TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool schema
          = true
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
    hrightObject hleftMem hrightMem hleftLookup hrightLookup hleftFuel
    hleftLeaf hrightComposite hleftReady hrightReady
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
        hleftLookup hleftFuel hleftLeaf
  rcases
      hrightReady responseName rightFieldName rightArguments rightDirectives
        rightChildSelectionSet hrightMem with
    ⟨rightFieldDefinition', hrightLookup', hrightFuel, hrightCase⟩
  have hrightDefinitionEq :
      rightFieldDefinition' = rightFieldDefinition := by
    rw [hrightLookup] at hrightLookup'
    exact Option.some.inj hrightLookup'.symm
  subst rightFieldDefinition'
  rcases hrightCase with hrightLeaf | hrightCase
  · rw [hrightComposite] at hrightLeaf
    simp at hrightLeaf
  rcases hrightCase with hselectedChild | hrightCase
  · rcases hselectedChild with
      ⟨rightChildRuntime, rightTail, rightChildFields, rightChildErrors,
        hrightSelected, hrightRuntimeCase, hrightInclude,
        hrightChildResponse⟩
    rcases
        wrapTypeRefSelectionSetResult_ok_nonNull_of_object_response
          rightFieldDefinition.outputType rightChildFields
          rightChildErrors with
      ⟨rightResponseValue, rightFieldErrors, hrightWrapped,
        _hrightNonNull⟩
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
        .ok ([(responseName, rightResponseValue)], rightFieldErrors) := by
      dsimp [resolvers, rightSource]
      rw [
        executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_objectProbe_response_of_fuel_ge
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet rightCurrentSelectionSet
          leftInitialSpine rightInitialSpine rightSpine rightTail
          variableValues fuel targetParent leftProbeField rightProbeField
          rightParentType rightFieldName rightSourceRuntimeType responseName
          targetLeftArguments targetRightArguments rightArguments
          leftRuntime rightRuntime FieldPairProbeTag.right
          rightChildSelectionSet rightFieldDefinition rightChildRuntime
          hrightLookup hrightSelected hrightRuntimeCase hrightInclude
          hrightFuel]
      rw [hrightChildResponse]
      simp [Execution.singleFieldResult, hrightWrapped]
    have hvalueNot :
        ¬ Execution.ResponseValue.semanticEquivalent
          (leafProbeResponseValue leftFieldDefinition.outputType
            FieldPairProbeTag.left.scalar)
          rightResponseValue :=
      leafProbeResponseValue_not_semanticEquivalent_wrapped_object_of_composite
        schema leftFieldDefinition.outputType rightFieldDefinition.outputType
        FieldPairProbeTag.left.scalar rightResponseValue rightFieldErrors
        rightChildFields rightChildErrors hleftLeaf hrightComposite
        hrightWrapped
    exact
      SemanticSeparation.responseData_not_semanticEquivalent_of_field_value_diff_of_field_ok_pair
        resolvers resolvers variableValues (fuel + 1) leftSource rightSource
        hleftObject hrightObject hleftNormal hrightNormal hleftFree
        hrightFree hleftMem hrightMem hleftTarget hrightTarget hvalueNot
        hleftFieldOk hrightFieldOk
  rcases hrightCase with hobjectOutput | habstractFallback
  · rcases hobjectOutput with
      ⟨rightChildFields, rightChildErrors, hrightObjectOutput,
        hrightChildResponse⟩
    rcases
        wrapTypeRefSelectionSetResult_ok_nonNull_of_object_response
          rightFieldDefinition.outputType rightChildFields
          rightChildErrors with
      ⟨rightResponseValue, rightFieldErrors, hrightWrapped,
        _hrightNonNull⟩
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
        .ok ([(responseName, rightResponseValue)], rightFieldErrors) := by
      dsimp [resolvers, rightSource]
      rw [
        executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_objectOutput_response_of_fuel_ge
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet rightCurrentSelectionSet leftInitialSpine
          rightInitialSpine rightSpine variableValues fuel targetParent
          leftProbeField rightProbeField rightParentType rightFieldName
          rightSourceRuntimeType responseName targetLeftArguments
          targetRightArguments rightArguments leftRuntime rightRuntime
          FieldPairProbeTag.right rightChildSelectionSet
          rightFieldDefinition hrightLookup hrightObjectOutput hrightFuel]
      rw [hrightChildResponse]
      simp [Execution.singleFieldResult, hrightWrapped]
    have hvalueNot :
        ¬ Execution.ResponseValue.semanticEquivalent
          (leafProbeResponseValue leftFieldDefinition.outputType
            FieldPairProbeTag.left.scalar)
          rightResponseValue :=
      leafProbeResponseValue_not_semanticEquivalent_wrapped_object_of_composite
        schema leftFieldDefinition.outputType rightFieldDefinition.outputType
        FieldPairProbeTag.left.scalar rightResponseValue rightFieldErrors
        rightChildFields rightChildErrors hleftLeaf hrightComposite
        hrightWrapped
    exact
      SemanticSeparation.responseData_not_semanticEquivalent_of_field_value_diff_of_field_ok_pair
        resolvers resolvers variableValues (fuel + 1) leftSource rightSource
        hleftObject hrightObject hleftNormal hrightNormal hleftFree
        hrightFree hleftMem hrightMem hleftTarget hrightTarget hvalueNot
        hleftFieldOk hrightFieldOk
  · rcases habstractFallback with
      ⟨rightChildRuntime, rightChildFields, rightChildErrors,
        hrightCompositeFallback, hrightNonObject, hrightSelectedNone,
        hrightRuntime, hrightInclude, hrightChildResponse⟩
    rcases
        wrapTypeRefSelectionSetResult_ok_nonNull_of_object_response
          rightFieldDefinition.outputType rightChildFields
          rightChildErrors with
      ⟨rightResponseValue, rightFieldErrors, hrightWrapped,
        _hrightNonNull⟩
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
        .ok ([(responseName, rightResponseValue)], rightFieldErrors) := by
      dsimp [resolvers, rightSource]
      rw [
        executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_abstractFallback_response_of_fuel_ge
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet rightCurrentSelectionSet leftInitialSpine
          rightInitialSpine rightSpine variableValues fuel targetParent
          leftProbeField rightProbeField rightParentType rightFieldName
          rightSourceRuntimeType responseName targetLeftArguments
          targetRightArguments rightArguments leftRuntime rightRuntime
          FieldPairProbeTag.right rightChildSelectionSet
          rightFieldDefinition rightChildRuntime hrightLookup
          hrightCompositeFallback hrightNonObject hrightSelectedNone
          hrightRuntime hrightInclude hrightFuel]
      rw [hrightChildResponse]
      simp [Execution.singleFieldResult, hrightWrapped]
    have hvalueNot :
        ¬ Execution.ResponseValue.semanticEquivalent
          (leafProbeResponseValue leftFieldDefinition.outputType
            FieldPairProbeTag.left.scalar)
          rightResponseValue :=
      leafProbeResponseValue_not_semanticEquivalent_wrapped_object_of_composite
        schema leftFieldDefinition.outputType rightFieldDefinition.outputType
        FieldPairProbeTag.left.scalar rightResponseValue rightFieldErrors
        rightChildFields rightChildErrors hleftLeaf hrightComposite
        hrightWrapped
    exact
      SemanticSeparation.responseData_not_semanticEquivalent_of_field_value_diff_of_field_ok_pair
        resolvers resolvers variableValues (fuel + 1) leftSource rightSource
        hleftObject hrightObject hleftNormal hrightNormal hleftFree
        hrightFree hleftMem hrightMem hleftTarget hrightTarget hvalueNot
        hleftFieldOk hrightFieldOk

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_left_leaf_right_composite_field_pair_of_selectedPathFieldChildrenReady_fuels
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
    (targetLeftArguments targetRightArguments : List Argument)
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
      -> leafProbeFuel leftFieldDefinition.outputType ≤ leftFuel
      -> (TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool schema
          = true
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
    hrightObject hleftMem hrightMem hleftLookup hrightLookup hleftFuel
    hleftLeaf hrightComposite hleftReady hrightReady
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
        hleftLookup hleftFuel hleftLeaf
  rcases
      hrightReady responseName rightFieldName rightArguments rightDirectives
        rightChildSelectionSet hrightMem with
    ⟨rightFieldDefinition', hrightLookup', hrightFuel, hrightCase⟩
  have hrightDefinitionEq :
      rightFieldDefinition' = rightFieldDefinition := by
    rw [hrightLookup] at hrightLookup'
    exact Option.some.inj hrightLookup'.symm
  subst rightFieldDefinition'
  rcases hrightCase with hrightLeaf | hrightCase
  · rw [hrightComposite] at hrightLeaf
    simp at hrightLeaf
  rcases hrightCase with hselectedChild | hrightCase
  · rcases hselectedChild with
      ⟨rightChildRuntime, rightTail, rightChildFields, rightChildErrors,
        hrightSelected, hrightRuntimeCase, hrightInclude,
        hrightChildResponse⟩
    rcases
        wrapTypeRefSelectionSetResult_ok_nonNull_of_object_response
          rightFieldDefinition.outputType rightChildFields
          rightChildErrors with
      ⟨rightResponseValue, rightFieldErrors, hrightWrapped,
        _hrightNonNull⟩
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
        .ok ([(responseName, rightResponseValue)], rightFieldErrors) := by
      dsimp [resolvers, rightSource]
      rw [
        executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_objectProbe_response_of_fuel_ge
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet rightCurrentSelectionSet
          leftInitialSpine rightInitialSpine rightSpine rightTail
          variableValues rightFuel targetParent leftProbeField
          rightProbeField rightParentType rightFieldName
          rightSourceRuntimeType responseName targetLeftArguments
          targetRightArguments rightArguments leftRuntime rightRuntime
          FieldPairProbeTag.right rightChildSelectionSet
          rightFieldDefinition rightChildRuntime hrightLookup
          hrightSelected hrightRuntimeCase hrightInclude hrightFuel]
      rw [hrightChildResponse]
      simp [Execution.singleFieldResult, hrightWrapped]
    have hvalueNot :
        ¬ Execution.ResponseValue.semanticEquivalent
          (leafProbeResponseValue leftFieldDefinition.outputType
            FieldPairProbeTag.left.scalar)
          rightResponseValue :=
      leafProbeResponseValue_not_semanticEquivalent_wrapped_object_of_composite
        schema leftFieldDefinition.outputType rightFieldDefinition.outputType
        FieldPairProbeTag.left.scalar rightResponseValue rightFieldErrors
        rightChildFields rightChildErrors hleftLeaf hrightComposite
        hrightWrapped
    exact
      SemanticSeparation.responseData_not_semanticEquivalent_of_field_value_diff_of_field_ok_pair_fuels
        resolvers resolvers variableValues (leftFuel + 1)
        (rightFuel + 1) leftSource rightSource hleftObject hrightObject
        hleftNormal hrightNormal hleftFree hrightFree hleftMem
        hrightMem hleftTarget hrightTarget hvalueNot hleftFieldOk
        hrightFieldOk
  rcases hrightCase with hobjectOutput | habstractFallback
  · rcases hobjectOutput with
      ⟨rightChildFields, rightChildErrors, hrightObjectOutput,
        hrightChildResponse⟩
    rcases
        wrapTypeRefSelectionSetResult_ok_nonNull_of_object_response
          rightFieldDefinition.outputType rightChildFields
          rightChildErrors with
      ⟨rightResponseValue, rightFieldErrors, hrightWrapped,
        _hrightNonNull⟩
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
        .ok ([(responseName, rightResponseValue)], rightFieldErrors) := by
      dsimp [resolvers, rightSource]
      rw [
        executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_objectOutput_response_of_fuel_ge
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet rightCurrentSelectionSet leftInitialSpine
          rightInitialSpine rightSpine variableValues rightFuel targetParent
          leftProbeField rightProbeField rightParentType rightFieldName
          rightSourceRuntimeType responseName targetLeftArguments
          targetRightArguments rightArguments leftRuntime rightRuntime
          FieldPairProbeTag.right rightChildSelectionSet
          rightFieldDefinition hrightLookup hrightObjectOutput hrightFuel]
      rw [hrightChildResponse]
      simp [Execution.singleFieldResult, hrightWrapped]
    have hvalueNot :
        ¬ Execution.ResponseValue.semanticEquivalent
          (leafProbeResponseValue leftFieldDefinition.outputType
            FieldPairProbeTag.left.scalar)
          rightResponseValue :=
      leafProbeResponseValue_not_semanticEquivalent_wrapped_object_of_composite
        schema leftFieldDefinition.outputType rightFieldDefinition.outputType
        FieldPairProbeTag.left.scalar rightResponseValue rightFieldErrors
        rightChildFields rightChildErrors hleftLeaf hrightComposite
        hrightWrapped
    exact
      SemanticSeparation.responseData_not_semanticEquivalent_of_field_value_diff_of_field_ok_pair_fuels
        resolvers resolvers variableValues (leftFuel + 1)
        (rightFuel + 1) leftSource rightSource hleftObject hrightObject
        hleftNormal hrightNormal hleftFree hrightFree hleftMem
        hrightMem hleftTarget hrightTarget hvalueNot hleftFieldOk
        hrightFieldOk
  · rcases habstractFallback with
      ⟨rightChildRuntime, rightChildFields, rightChildErrors,
        hrightCompositeFallback, hrightNonObject, hrightSelectedNone,
        hrightRuntime, hrightInclude, hrightChildResponse⟩
    rcases
        wrapTypeRefSelectionSetResult_ok_nonNull_of_object_response
          rightFieldDefinition.outputType rightChildFields
          rightChildErrors with
      ⟨rightResponseValue, rightFieldErrors, hrightWrapped,
        _hrightNonNull⟩
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
        .ok ([(responseName, rightResponseValue)], rightFieldErrors) := by
      dsimp [resolvers, rightSource]
      rw [
        executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_abstractFallback_response_of_fuel_ge
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet rightCurrentSelectionSet leftInitialSpine
          rightInitialSpine rightSpine variableValues rightFuel targetParent
          leftProbeField rightProbeField rightParentType rightFieldName
          rightSourceRuntimeType responseName targetLeftArguments
          targetRightArguments rightArguments leftRuntime rightRuntime
          FieldPairProbeTag.right rightChildSelectionSet
          rightFieldDefinition rightChildRuntime hrightLookup
          hrightCompositeFallback hrightNonObject hrightSelectedNone
          hrightRuntime hrightInclude hrightFuel]
      rw [hrightChildResponse]
      simp [Execution.singleFieldResult, hrightWrapped]
    have hvalueNot :
        ¬ Execution.ResponseValue.semanticEquivalent
          (leafProbeResponseValue leftFieldDefinition.outputType
            FieldPairProbeTag.left.scalar)
          rightResponseValue :=
      leafProbeResponseValue_not_semanticEquivalent_wrapped_object_of_composite
        schema leftFieldDefinition.outputType rightFieldDefinition.outputType
        FieldPairProbeTag.left.scalar rightResponseValue rightFieldErrors
        rightChildFields rightChildErrors hleftLeaf hrightComposite
        hrightWrapped
    exact
      SemanticSeparation.responseData_not_semanticEquivalent_of_field_value_diff_of_field_ok_pair_fuels
        resolvers resolvers variableValues (leftFuel + 1)
        (rightFuel + 1) leftSource rightSource hleftObject hrightObject
        hleftNormal hrightNormal hleftFree hrightFree hleftMem
        hrightMem hleftTarget hrightTarget hvalueNot hleftFieldOk
        hrightFieldOk

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_left_leaf_right_composite_field_pair_of_valid_normal_runtimeSpine
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
          = false
      -> (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool schema
          = true
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
    hleftContext hrightContext hleftMem hrightMem hleftLookup
    hrightLookup hleftLeaf hrightComposite
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
      leftSpine hleftFuel hleftValid hleftFree hleftNormal hleftObject
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
      rightSpine hrightFuel hrightValid hrightFree hrightNormal
      hrightObject hrightSpineValid hrightSupport hrightContext
  have hleftLeafFuel :
      leafProbeFuel leftFieldDefinition.outputType ≤ fuel := by
    have hlocal :=
      leafProbeFuel_le_selectionSetDeepProbeFuel_of_field_mem schema
        leftParentType (selectionSet := left)
        (responseName := responseName) (fieldName := leftFieldName)
        (arguments := leftArguments) (directives := leftDirectives)
        (childSelectionSet := leftChildSelectionSet)
        (fieldDefinition := leftFieldDefinition) hleftMem
        hleftLookup
    omega
  exact
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_left_leaf_right_composite_field_pair_of_selectedPathFieldChildrenReady
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet leftCurrentSelectionSet
      rightCurrentSelectionSet leftInitialSpine rightInitialSpine
      leftSpine rightSpine variableValues fuel targetParent
      leftProbeField rightProbeField leftParentType rightParentType
      leftSourceRuntimeType rightSourceRuntimeType targetLeftArguments
      targetRightArguments leftRuntime rightRuntime hleftFree hrightFree
      hleftNormal hrightNormal hleftObject hrightObject hleftMem
      hrightMem hleftLookup hrightLookup hleftLeafFuel hleftLeaf
      hrightComposite hleftReady hrightReady

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_left_leaf_right_composite_field_pair_of_valid_normal_runtimeSpine_fuels
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
          = false
      -> (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool schema
          = true
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
    hleftContext hrightContext hleftMem hrightMem hleftLookup
    hrightLookup hleftLeaf hrightComposite
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
      leftSpine hleftFuel hleftValid hleftFree hleftNormal hleftObject
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
      rightSpine hrightFuel hrightValid hrightFree hrightNormal
      hrightObject hrightSpineValid hrightSupport hrightContext
  have hleftLeafFuel :
      leafProbeFuel leftFieldDefinition.outputType ≤ leftFuel := by
    have hlocal :=
      leafProbeFuel_le_selectionSetDeepProbeFuel_of_field_mem schema
        leftParentType (selectionSet := left)
        (responseName := responseName) (fieldName := leftFieldName)
        (arguments := leftArguments) (directives := leftDirectives)
        (childSelectionSet := leftChildSelectionSet)
        (fieldDefinition := leftFieldDefinition) hleftMem
        hleftLookup
    omega
  exact
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_left_leaf_right_composite_field_pair_of_selectedPathFieldChildrenReady_fuels
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet leftCurrentSelectionSet
      rightCurrentSelectionSet leftInitialSpine rightInitialSpine
      leftSpine rightSpine variableValues leftFuel rightFuel targetParent
      leftProbeField rightProbeField leftParentType rightParentType
      leftSourceRuntimeType rightSourceRuntimeType targetLeftArguments
      targetRightArguments leftRuntime rightRuntime hleftFree hrightFree
      hleftNormal hrightNormal hleftObject hrightObject hleftMem
      hrightMem hleftLookup hrightLookup hleftLeafFuel hleftLeaf
      hrightComposite hleftReady hrightReady

theorem
    selectedPathTaggedSelectionSetsResponseDiffWitness_of_left_leaf_right_composite_field_pair_valid_normal_runtimeSpine
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
    (leftRuntime rightRuntime : Name) {left right : List Selection}
    {responseName leftFieldName rightFieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {leftFieldDefinition rightFieldDefinition : FieldDefinition}
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
          = true
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
    hrightContext hleftMem hrightMem hleftLookup hrightLookup
    hleftLeaf hrightComposite
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
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_left_leaf_right_composite_field_pair_of_valid_normal_runtimeSpine
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
      hrightSupport hleftContext hrightContext hleftMem hrightMem
      hleftLookup hrightLookup hleftLeaf hrightComposite
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
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_left_leaf_right_objectOutput_field_pair_of_field_ok
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
    (targetLeftArguments targetRightArguments : List Argument)
    (leftRuntime rightRuntime : Name) {left right : List Selection}
    {responseName leftFieldName rightFieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {leftFieldDefinition rightFieldDefinition : FieldDefinition}
    {rightChildFields : List (Name × Execution.ResponseValue)} {rightChildErrors : Nat}
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
      -> (TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> objectTypeNameBool schema rightFieldDefinition.outputType.namedType = true
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
            (fuel - leafProbeFuel rightFieldDefinition.outputType)
            rightFieldDefinition.outputType.namedType
            (projectionTargetResolverValue
              (.object rightFieldDefinition.outputType.namedType
                (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                  (fieldPairPathLocalNextSelectionSet schema rightParentType
                    rightFieldDefinition.outputType.namedType rightFieldName
                    rightArguments rightCurrentSelectionSet)
                  (selectedObservableFieldSpineTailForRuntime
                    rightFieldDefinition.outputType.namedType rightFieldName
                    rightArguments rightSpine))))
            rightChildSelectionSet
          = ({
                data := Execution.ResponseValue.object rightChildFields,
                errors := rightChildErrors
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
    hrightObject hleftMem hrightMem hleftLookup hrightLookup hleftLeaf
    hrightObjectOutput hleftFuel hrightFuel hrightChildResponse
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
        rightFieldDefinition.outputType rightChildFields rightChildErrors with
    ⟨rightResponseValue, rightFieldErrors, hrightWrapped,
      _hrightNonNull⟩
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
        hleftLookup hleftFuel hleftLeaf
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
      .ok ([(responseName, rightResponseValue)], rightFieldErrors) := by
    dsimp [resolvers, rightSource]
    rw [
      executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_objectOutput_response_of_fuel_ge
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet rightCurrentSelectionSet leftInitialSpine
        rightInitialSpine rightSpine variableValues fuel targetParent
        leftProbeField rightProbeField rightParentType rightFieldName
        rightSourceRuntimeType responseName targetLeftArguments
        targetRightArguments rightArguments leftRuntime rightRuntime
        FieldPairProbeTag.right rightChildSelectionSet rightFieldDefinition
        hrightLookup hrightObjectOutput hrightFuel]
    rw [hrightChildResponse]
    simp [Execution.singleFieldResult, hrightWrapped]
  have hrightComposite :
      (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool
        schema = true :=
    typeRef_named_isCompositeBool_true_of_objectTypeNameBool
      hrightObjectOutput
  have hvalueNot :
      ¬ Execution.ResponseValue.semanticEquivalent
        (leafProbeResponseValue leftFieldDefinition.outputType
          FieldPairProbeTag.left.scalar)
        rightResponseValue :=
    leafProbeResponseValue_not_semanticEquivalent_wrapped_object_of_composite
      schema leftFieldDefinition.outputType rightFieldDefinition.outputType
      FieldPairProbeTag.left.scalar rightResponseValue rightFieldErrors
      rightChildFields rightChildErrors hleftLeaf hrightComposite
      hrightWrapped
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
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_left_leaf_right_objectOutput_field_pair_of_valid_normal_runtimeSpine
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
          = false
      -> objectTypeNameBool schema rightFieldDefinition.outputType.namedType = true
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
    hleftContext hrightContext hleftMem hrightMem hleftLookup
    hrightLookup hleftLeaf hrightObjectOutput
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
      leftRuntime rightRuntime FieldPairProbeTag.right
      rightCurrentSelectionSet rightSpine hrightFuel hrightValid
      hrightFree hrightNormal hrightObject hrightSpineValid
      hrightSupport hrightContext
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
        hschema hleftValid hleftFree hleftNormal hleftObject hleftFuel
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
      executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_field_ok_of_selectedPathFieldChildrenReady
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet rightCurrentSelectionSet leftInitialSpine
        rightInitialSpine rightSpine variableValues fuel targetParent
        leftProbeField rightProbeField rightParentType
        rightSourceRuntimeType targetLeftArguments targetRightArguments
        leftRuntime rightRuntime FieldPairProbeTag.right right hrightReady
  rcases
      objectOutputChildResponse_of_selectedPathFieldChildrenReady
        (schema := schema)
        (rootSelectionSet := rootSelectionSet)
        (leftInitialSelectionSet := leftInitialSelectionSet)
        (rightInitialSelectionSet := rightInitialSelectionSet)
        (currentSelectionSet := rightCurrentSelectionSet)
        (selectionSet := right)
        (leftInitialSpine := leftInitialSpine)
        (rightInitialSpine := rightInitialSpine)
        (spine := rightSpine)
        (variableValues := variableValues) (fuel := fuel)
        (targetParent := targetParent) (leftField := leftProbeField)
        (rightField := rightProbeField) (parentType := rightParentType)
        (targetLeftArguments := targetLeftArguments)
        (targetRightArguments := targetRightArguments)
        (leftRuntime := leftRuntime) (rightRuntime := rightRuntime)
        (tag := FieldPairProbeTag.right)
        (responseName := responseName) (fieldName := rightFieldName)
        (arguments := rightArguments) (directives := rightDirectives)
        (childSelectionSet := rightChildSelectionSet)
        (fieldDefinition := rightFieldDefinition)
        hrightReady hrightMem hrightLookup hrightObjectOutput with
    ⟨rightChildFields, rightChildErrors, hrightChildResponse⟩
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
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_left_leaf_right_objectOutput_field_pair_of_field_ok
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet leftCurrentSelectionSet
      rightCurrentSelectionSet leftInitialSpine rightInitialSpine
      leftSpine rightSpine variableValues fuel targetParent
      leftProbeField rightProbeField leftParentType rightParentType
      leftSourceRuntimeType rightSourceRuntimeType targetLeftArguments
      targetRightArguments leftRuntime rightRuntime hleftFree hrightFree
      hleftNormal hrightNormal hleftObject hrightObject hleftMem
      hrightMem hleftLookup hrightLookup hleftLeaf hrightObjectOutput
      hleftLeafFuel hrightLeafFuel hrightChildResponse hleftFieldOk
      hrightFieldOk

theorem
    selectedPathTaggedSelectionSetsResponseDiffWitness_of_left_leaf_right_objectOutput_field_pair_valid_normal_runtimeSpine
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
    (leftRuntime rightRuntime : Name) {left right : List Selection}
    {responseName leftFieldName rightFieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {leftFieldDefinition rightFieldDefinition : FieldDefinition}
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
      -> objectTypeNameBool schema rightFieldDefinition.outputType.namedType = true
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
    hrightContext hleftMem hrightMem hleftLookup hrightLookup hleftLeaf
    hrightObjectOutput
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
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_left_leaf_right_objectOutput_field_pair_of_valid_normal_runtimeSpine
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
      hrightSupport hleftContext hrightContext hleftMem hrightMem
      hleftLookup hrightLookup hleftLeaf hrightObjectOutput
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
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_objectOutput_field_pair_of_field_ok
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
    (targetLeftArguments targetRightArguments : List Argument)
    (leftRuntime rightRuntime : Name) {left right : List Selection}
    {responseName leftFieldName rightFieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {leftFieldDefinition rightFieldDefinition : FieldDefinition}
    {leftChildFields rightChildFields : List (Name × Execution.ResponseValue)}
    {leftChildErrors rightChildErrors : Nat}
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
      -> objectTypeNameBool schema leftFieldDefinition.outputType.namedType = true
      -> objectTypeNameBool schema rightFieldDefinition.outputType.namedType = true
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
      -> Execution.executeSelectionSetAsResponse schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet leftInitialSpine rightInitialSpine
                targetParent leftProbeField rightProbeField targetLeftArguments
                targetRightArguments leftRuntime rightRuntime)
              targetParent leftProbeField rightProbeField targetLeftArguments
              targetRightArguments)
            variableValues
            (fuel - leafProbeFuel rightFieldDefinition.outputType)
            rightFieldDefinition.outputType.namedType
            (projectionTargetResolverValue
              (.object rightFieldDefinition.outputType.namedType
                (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                  (fieldPairPathLocalNextSelectionSet schema rightParentType
                    rightFieldDefinition.outputType.namedType rightFieldName
                    rightArguments rightCurrentSelectionSet)
                  (selectedObservableFieldSpineTailForRuntime
                    rightFieldDefinition.outputType.namedType rightFieldName
                    rightArguments rightSpine))))
            rightChildSelectionSet
          = ({
                data := Execution.ResponseValue.object rightChildFields,
                errors := rightChildErrors
              }
              : Execution.Response)
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.ResponseValue.object leftChildFields)
            (Execution.ResponseValue.object rightChildFields)
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
    hrightObject hleftMem hrightMem hleftLookup hrightLookup
    hleftObjectOutput hrightObjectOutput hleftFuel hrightFuel
    hleftChildResponse hrightChildResponse hchildNot hleftFieldOk
    hrightFieldOk
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
  rcases
      wrapTypeRefSelectionSetResult_ok_nonNull_of_object_response
        rightFieldDefinition.outputType rightChildFields rightChildErrors with
    ⟨rightResponseValue, rightFieldErrors, hrightWrapped,
      _hrightNonNull⟩
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
        hleftLookup hleftObjectOutput hleftFuel]
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
      .ok ([(responseName, rightResponseValue)], rightFieldErrors) := by
    dsimp [resolvers, rightSource]
    rw [
      executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_objectOutput_response_of_fuel_ge
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet rightCurrentSelectionSet leftInitialSpine
        rightInitialSpine rightSpine variableValues fuel targetParent
        leftProbeField rightProbeField rightParentType rightFieldName
        rightSourceRuntimeType responseName targetLeftArguments
        targetRightArguments rightArguments leftRuntime rightRuntime
        FieldPairProbeTag.right rightChildSelectionSet rightFieldDefinition
        hrightLookup hrightObjectOutput hrightFuel]
    rw [hrightChildResponse]
    simp [Execution.singleFieldResult, hrightWrapped]
  have hvalueNot :
      ¬ Execution.ResponseValue.semanticEquivalent leftResponseValue
        rightResponseValue :=
    wrapped_object_values_not_semanticEquivalent_of_child
      leftFieldDefinition.outputType rightFieldDefinition.outputType
      hleftWrapped hrightWrapped hchildNot
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
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_objectOutput_field_pair_of_field_ok_fuels
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
    (targetLeftArguments targetRightArguments : List Argument)
    (leftRuntime rightRuntime : Name) {left right : List Selection}
    {responseName leftFieldName rightFieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {leftFieldDefinition rightFieldDefinition : FieldDefinition}
    {leftChildFields rightChildFields : List (Name × Execution.ResponseValue)}
    {leftChildErrors rightChildErrors : Nat}
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
      -> objectTypeNameBool schema leftFieldDefinition.outputType.namedType = true
      -> objectTypeNameBool schema rightFieldDefinition.outputType.namedType = true
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
      -> Execution.executeSelectionSetAsResponse schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet leftInitialSpine rightInitialSpine
                targetParent leftProbeField rightProbeField targetLeftArguments
                targetRightArguments leftRuntime rightRuntime)
              targetParent leftProbeField rightProbeField targetLeftArguments
              targetRightArguments)
            variableValues
            (rightFuel - leafProbeFuel rightFieldDefinition.outputType)
            rightFieldDefinition.outputType.namedType
            (projectionTargetResolverValue
              (.object rightFieldDefinition.outputType.namedType
                (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                  (fieldPairPathLocalNextSelectionSet schema rightParentType
                    rightFieldDefinition.outputType.namedType rightFieldName
                    rightArguments rightCurrentSelectionSet)
                  (selectedObservableFieldSpineTailForRuntime
                    rightFieldDefinition.outputType.namedType rightFieldName
                    rightArguments rightSpine))))
            rightChildSelectionSet
          = ({
                data := Execution.ResponseValue.object rightChildFields,
                errors := rightChildErrors
              }
              : Execution.Response)
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.ResponseValue.object leftChildFields)
            (Execution.ResponseValue.object rightChildFields)
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
    hrightObject hleftMem hrightMem hleftLookup hrightLookup
    hleftObjectOutput hrightObjectOutput hleftLeafFuel hrightLeafFuel
    hleftChildResponse hrightChildResponse hchildNot hleftFieldOk
    hrightFieldOk
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
  rcases
      wrapTypeRefSelectionSetResult_ok_nonNull_of_object_response
        rightFieldDefinition.outputType rightChildFields rightChildErrors with
    ⟨rightResponseValue, rightFieldErrors, hrightWrapped,
      _hrightNonNull⟩
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
        hleftLookup hleftObjectOutput hleftLeafFuel]
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
      .ok ([(responseName, rightResponseValue)], rightFieldErrors) := by
    dsimp [resolvers, rightSource]
    rw [
      executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_objectOutput_response_of_fuel_ge
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet rightCurrentSelectionSet leftInitialSpine
        rightInitialSpine rightSpine variableValues rightFuel targetParent
        leftProbeField rightProbeField rightParentType rightFieldName
        rightSourceRuntimeType responseName targetLeftArguments
        targetRightArguments rightArguments leftRuntime rightRuntime
        FieldPairProbeTag.right rightChildSelectionSet rightFieldDefinition
        hrightLookup hrightObjectOutput hrightLeafFuel]
    rw [hrightChildResponse]
    simp [Execution.singleFieldResult, hrightWrapped]
  have hvalueNot :
      ¬ Execution.ResponseValue.semanticEquivalent leftResponseValue
        rightResponseValue :=
    wrapped_object_values_not_semanticEquivalent_of_child
      leftFieldDefinition.outputType rightFieldDefinition.outputType
      hleftWrapped hrightWrapped hchildNot
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
      resolvers resolvers variableValues (leftFuel + 1) (rightFuel + 1)
      leftSource rightSource hleftObject hrightObject hleftNormal
      hrightNormal hleftFree hrightFree hleftMem hrightMem hleftTarget
      hrightTarget hvalueNot hleftFieldOk hrightFieldOk

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_child_field_pair_of_field_ok_fuels
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
    (targetLeftArguments targetRightArguments : List Argument)
    (leftRuntime rightRuntime : Name) {left right : List Selection}
    {responseName leftFieldName rightFieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {leftFieldDefinition rightFieldDefinition : FieldDefinition}
    {leftChildRuntime rightChildRuntime : Name}
    {leftChildSpine rightChildSpine : List NormalSelectionSetObservableFieldStep}
    {leftChildFields rightChildFields : List (Name × Execution.ResponseValue)}
    {leftChildErrors rightChildErrors : Nat}
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
      -> SelectedPathCompositeFieldChildSource schema leftParentType
          leftFieldName leftArguments leftCurrentSelectionSet leftSpine
          leftFieldDefinition leftChildRuntime leftChildSpine
      -> SelectedPathCompositeFieldChildSource schema rightParentType
          rightFieldName rightArguments rightCurrentSelectionSet rightSpine
          rightFieldDefinition rightChildRuntime rightChildSpine
      -> schema.typeIncludesObjectBool leftFieldDefinition.outputType.namedType
            leftChildRuntime
          = true
      -> schema.typeIncludesObjectBool rightFieldDefinition.outputType.namedType
            rightChildRuntime
          = true
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
            leftChildRuntime
            (projectionTargetResolverValue
              (.object leftChildRuntime
                (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
                  (fieldPairPathLocalNextSelectionSet schema leftParentType
                    leftChildRuntime leftFieldName leftArguments
                    leftCurrentSelectionSet)
                  leftChildSpine)))
            leftChildSelectionSet
          = ({
                data := Execution.ResponseValue.object leftChildFields,
                errors := leftChildErrors
              }
              : Execution.Response)
      -> Execution.executeSelectionSetAsResponse schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet leftInitialSpine rightInitialSpine
                targetParent leftProbeField rightProbeField targetLeftArguments
                targetRightArguments leftRuntime rightRuntime)
              targetParent leftProbeField rightProbeField targetLeftArguments
              targetRightArguments)
            variableValues
            (rightFuel - leafProbeFuel rightFieldDefinition.outputType)
            rightChildRuntime
            (projectionTargetResolverValue
              (.object rightChildRuntime
                (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                  (fieldPairPathLocalNextSelectionSet schema rightParentType
                    rightChildRuntime rightFieldName rightArguments
                    rightCurrentSelectionSet)
                  rightChildSpine)))
            rightChildSelectionSet
          = ({
                data := Execution.ResponseValue.object rightChildFields,
                errors := rightChildErrors
              }
              : Execution.Response)
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.ResponseValue.object leftChildFields)
            (Execution.ResponseValue.object rightChildFields)
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
    hrightObject hleftMem hrightMem hleftLookup hrightLookup
    hleftChildSource hrightChildSource hleftInclude hrightInclude
    hleftLeafFuel hrightLeafFuel hleftChildResponse hrightChildResponse
    hchildNot hleftFieldOk hrightFieldOk
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
  rcases
      wrapTypeRefSelectionSetResult_ok_nonNull_of_object_response
        rightFieldDefinition.outputType rightChildFields rightChildErrors with
    ⟨rightResponseValue, rightFieldErrors, hrightWrapped,
      _hrightNonNull⟩
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
    rcases hleftChildSource with hselected | hcase
    · rcases hselected with ⟨hselected, hruntimeCase⟩
      rw [
        executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_objectProbe_response_of_fuel_ge
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet leftCurrentSelectionSet
          leftInitialSpine rightInitialSpine leftSpine leftChildSpine
          variableValues leftFuel targetParent leftProbeField
          rightProbeField leftParentType leftFieldName
          leftSourceRuntimeType responseName targetLeftArguments
          targetRightArguments leftArguments leftRuntime rightRuntime
          FieldPairProbeTag.left leftChildSelectionSet
          leftFieldDefinition leftChildRuntime hleftLookup hselected
          hruntimeCase hleftInclude hleftLeafFuel]
      rw [hleftChildResponse]
      simp [Execution.singleFieldResult, hleftWrapped]
    rcases hcase with hobjectCase | habstractCase
    · rcases hobjectCase with
        ⟨hobjectOutput, hruntimeEq, hspineEq⟩
      subst leftChildRuntime
      subst leftChildSpine
      rw [
        executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_objectOutput_response_of_fuel_ge
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet leftCurrentSelectionSet
          leftInitialSpine rightInitialSpine leftSpine variableValues
          leftFuel targetParent leftProbeField rightProbeField
          leftParentType leftFieldName leftSourceRuntimeType responseName
          targetLeftArguments targetRightArguments leftArguments
          leftRuntime rightRuntime FieldPairProbeTag.left
          leftChildSelectionSet leftFieldDefinition hleftLookup
          hobjectOutput hleftLeafFuel]
      rw [hleftChildResponse]
      simp [Execution.singleFieldResult, hleftWrapped]
    · rcases habstractCase with
        ⟨hcomposite, hnonObject, hselectedNone, hruntime, hspineEq⟩
      subst leftChildSpine
      rw [
        executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_abstractFallback_response_of_fuel_ge
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet leftCurrentSelectionSet
          leftInitialSpine rightInitialSpine leftSpine variableValues
          leftFuel targetParent leftProbeField rightProbeField
          leftParentType leftFieldName leftSourceRuntimeType responseName
          targetLeftArguments targetRightArguments leftArguments
          leftRuntime rightRuntime FieldPairProbeTag.left
          leftChildSelectionSet leftFieldDefinition leftChildRuntime
          hleftLookup hcomposite hnonObject hselectedNone hruntime
          hleftInclude hleftLeafFuel]
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
      .ok ([(responseName, rightResponseValue)], rightFieldErrors) := by
    dsimp [resolvers, rightSource]
    rcases hrightChildSource with hselected | hcase
    · rcases hselected with ⟨hselected, hruntimeCase⟩
      rw [
        executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_objectProbe_response_of_fuel_ge
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet rightCurrentSelectionSet
          leftInitialSpine rightInitialSpine rightSpine rightChildSpine
          variableValues rightFuel targetParent leftProbeField
          rightProbeField rightParentType rightFieldName
          rightSourceRuntimeType responseName targetLeftArguments
          targetRightArguments rightArguments leftRuntime rightRuntime
          FieldPairProbeTag.right rightChildSelectionSet
          rightFieldDefinition rightChildRuntime hrightLookup hselected
          hruntimeCase hrightInclude hrightLeafFuel]
      rw [hrightChildResponse]
      simp [Execution.singleFieldResult, hrightWrapped]
    rcases hcase with hobjectCase | habstractCase
    · rcases hobjectCase with
        ⟨hobjectOutput, hruntimeEq, hspineEq⟩
      subst rightChildRuntime
      subst rightChildSpine
      rw [
        executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_objectOutput_response_of_fuel_ge
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet rightCurrentSelectionSet
          leftInitialSpine rightInitialSpine rightSpine variableValues
          rightFuel targetParent leftProbeField rightProbeField
          rightParentType rightFieldName rightSourceRuntimeType
          responseName targetLeftArguments targetRightArguments
          rightArguments leftRuntime rightRuntime FieldPairProbeTag.right
          rightChildSelectionSet rightFieldDefinition hrightLookup
          hobjectOutput hrightLeafFuel]
      rw [hrightChildResponse]
      simp [Execution.singleFieldResult, hrightWrapped]
    · rcases habstractCase with
        ⟨hcomposite, hnonObject, hselectedNone, hruntime, hspineEq⟩
      subst rightChildSpine
      rw [
        executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_abstractFallback_response_of_fuel_ge
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet rightCurrentSelectionSet
          leftInitialSpine rightInitialSpine rightSpine variableValues
          rightFuel targetParent leftProbeField rightProbeField
          rightParentType rightFieldName rightSourceRuntimeType
          responseName targetLeftArguments targetRightArguments
          rightArguments leftRuntime rightRuntime FieldPairProbeTag.right
          rightChildSelectionSet rightFieldDefinition rightChildRuntime
          hrightLookup hcomposite hnonObject hselectedNone hruntime
          hrightInclude hrightLeafFuel]
      rw [hrightChildResponse]
      simp [Execution.singleFieldResult, hrightWrapped]
  have hvalueNot :
      ¬ Execution.ResponseValue.semanticEquivalent leftResponseValue
        rightResponseValue :=
    wrapped_object_values_not_semanticEquivalent_of_child
      leftFieldDefinition.outputType rightFieldDefinition.outputType
      hleftWrapped hrightWrapped hchildNot
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
      resolvers resolvers variableValues (leftFuel + 1) (rightFuel + 1)
      leftSource rightSource hleftObject hrightObject hleftNormal
      hrightNormal hleftFree hrightFree hleftMem hrightMem hleftTarget
      hrightTarget hvalueNot hleftFieldOk hrightFieldOk

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_child_field_pair_of_field_children_fuels
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
    (targetLeftArguments targetRightArguments : List Argument)
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
          = true
      -> (∀ leftChildRuntime leftChildSpine rightChildRuntime rightChildSpine,
            SelectedPathCompositeFieldChildSource schema leftParentType
              leftFieldName leftArguments leftCurrentSelectionSet leftSpine
              leftFieldDefinition leftChildRuntime leftChildSpine
            -> SelectedPathCompositeFieldChildSource schema rightParentType
                rightFieldName rightArguments rightCurrentSelectionSet rightSpine
                rightFieldDefinition rightChildRuntime rightChildSpine
            -> schema.typeIncludesObjectBool
                  leftFieldDefinition.outputType.namedType leftChildRuntime
                = true
            -> schema.typeIncludesObjectBool
                  rightFieldDefinition.outputType.namedType rightChildRuntime
                = true
            -> ¬ Execution.ResponseValue.semanticEquivalent
                  (Execution.executeSelectionSetAsResponse schema
                    (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                      (fieldPairSelectedPathProbeResolvers schema
                        leftInitialSelectionSet rightInitialSelectionSet
                        leftInitialSpine rightInitialSpine targetParent
                        leftProbeField rightProbeField targetLeftArguments
                        targetRightArguments leftRuntime rightRuntime)
                      targetParent leftProbeField rightProbeField
                      targetLeftArguments targetRightArguments)
                    variableValues
                    (leftFuel - leafProbeFuel leftFieldDefinition.outputType)
                    leftChildRuntime
                    (projectionTargetResolverValue
                      (.object leftChildRuntime
                        (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
                          (fieldPairPathLocalNextSelectionSet schema leftParentType
                            leftChildRuntime leftFieldName leftArguments
                            leftCurrentSelectionSet)
                          leftChildSpine)))
                    leftChildSelectionSet).data
                  (Execution.executeSelectionSetAsResponse schema
                    (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                      (fieldPairSelectedPathProbeResolvers schema
                        leftInitialSelectionSet rightInitialSelectionSet
                        leftInitialSpine rightInitialSpine targetParent
                        leftProbeField rightProbeField targetLeftArguments
                        targetRightArguments leftRuntime rightRuntime)
                      targetParent leftProbeField rightProbeField
                      targetLeftArguments targetRightArguments)
                    variableValues
                    (rightFuel - leafProbeFuel rightFieldDefinition.outputType)
                    rightChildRuntime
                    (projectionTargetResolverValue
                      (.object rightChildRuntime
                        (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                          (fieldPairPathLocalNextSelectionSet schema rightParentType
                            rightChildRuntime rightFieldName rightArguments
                            rightCurrentSelectionSet)
                          rightChildSpine)))
                    rightChildSelectionSet).data)
      -> SelectedPathSelectionSetFieldChildrenReady schema rootSelectionSet
          leftInitialSelectionSet rightInitialSelectionSet
          leftCurrentSelectionSet leftInitialSpine rightInitialSpine leftSpine
          variableValues leftFuel targetParent leftProbeField rightProbeField
          leftParentType targetLeftArguments targetRightArguments leftRuntime
          rightRuntime FieldPairProbeTag.left left
      -> SelectedPathSelectionSetFieldChildrenReady schema rootSelectionSet
          leftInitialSelectionSet rightInitialSelectionSet
          rightCurrentSelectionSet leftInitialSpine rightInitialSpine rightSpine
          variableValues rightFuel targetParent leftProbeField rightProbeField
          rightParentType targetLeftArguments targetRightArguments leftRuntime
          rightRuntime FieldPairProbeTag.right right
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
    hrightObject hleftMem hrightMem hleftLookup hrightLookup
    hleftComposite hrightComposite hchildDataNot hleftChildren
    hrightChildren
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
      executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_field_ok_of_selectedPathFieldChildrenReady
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftCurrentSelectionSet leftInitialSpine
        rightInitialSpine leftSpine variableValues leftFuel targetParent
        leftProbeField rightProbeField leftParentType
        leftSourceRuntimeType targetLeftArguments targetRightArguments
        leftRuntime rightRuntime FieldPairProbeTag.left left hleftChildren
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
      executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_field_ok_of_selectedPathFieldChildrenReady
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet rightCurrentSelectionSet leftInitialSpine
        rightInitialSpine rightSpine variableValues rightFuel
        targetParent leftProbeField rightProbeField rightParentType
        rightSourceRuntimeType targetLeftArguments targetRightArguments
        leftRuntime rightRuntime FieldPairProbeTag.right right
        hrightChildren
  rcases
      compositeChildResponse_of_selectedPathFieldChildrenReady
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
        hleftChildren hleftMem hleftLookup hleftComposite with
    ⟨leftChildRuntime, leftChildSpine, leftChildFields,
      leftChildErrors, hleftChildSource, hleftInclude, hleftLeafFuel,
      hleftChildResponse⟩
  rcases
      compositeChildResponse_of_selectedPathFieldChildrenReady
        (schema := schema)
        (rootSelectionSet := rootSelectionSet)
        (leftInitialSelectionSet := leftInitialSelectionSet)
        (rightInitialSelectionSet := rightInitialSelectionSet)
        (currentSelectionSet := rightCurrentSelectionSet)
        (selectionSet := right)
        (leftInitialSpine := leftInitialSpine)
        (rightInitialSpine := rightInitialSpine)
        (spine := rightSpine)
        (variableValues := variableValues) (fuel := rightFuel)
        (targetParent := targetParent) (leftField := leftProbeField)
        (rightField := rightProbeField) (parentType := rightParentType)
        (targetLeftArguments := targetLeftArguments)
        (targetRightArguments := targetRightArguments)
        (leftRuntime := leftRuntime) (rightRuntime := rightRuntime)
        (tag := FieldPairProbeTag.right)
        (responseName := responseName) (fieldName := rightFieldName)
        (arguments := rightArguments) (directives := rightDirectives)
        (childSelectionSet := rightChildSelectionSet)
        (fieldDefinition := rightFieldDefinition)
        hrightChildren hrightMem hrightLookup hrightComposite with
    ⟨rightChildRuntime, rightChildSpine, rightChildFields,
      rightChildErrors, hrightChildSource, hrightInclude,
      hrightLeafFuel, hrightChildResponse⟩
  have hchildNot :
      ¬ Execution.ResponseValue.semanticEquivalent
        (Execution.ResponseValue.object leftChildFields)
        (Execution.ResponseValue.object rightChildFields) := by
    intro hsemantic
    exact (hchildDataNot leftChildRuntime leftChildSpine
            rightChildRuntime rightChildSpine hleftChildSource
            hrightChildSource hleftInclude hrightInclude)
            (by simpa [hleftChildResponse, hrightChildResponse] using
              hsemantic)
  simpa [resolvers, leftSource, rightSource] using
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_child_field_pair_of_field_ok_fuels
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet leftCurrentSelectionSet
      rightCurrentSelectionSet leftInitialSpine rightInitialSpine
      leftSpine rightSpine variableValues leftFuel rightFuel
      targetParent leftProbeField rightProbeField leftParentType
      rightParentType leftSourceRuntimeType rightSourceRuntimeType
      targetLeftArguments targetRightArguments leftRuntime rightRuntime
      hleftFree hrightFree hleftNormal hrightNormal hleftObject
      hrightObject hleftMem hrightMem hleftLookup hrightLookup
      hleftChildSource hrightChildSource hleftInclude hrightInclude
      hleftLeafFuel hrightLeafFuel hleftChildResponse
      hrightChildResponse hchildNot hleftFieldOk hrightFieldOk

theorem
    selectedPathTaggedSelectionSetsResponseDiffWitness_of_composite_sameField_childWitness_valid_normal_runtimeSpine
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
    (leftRuntime rightRuntime : Name) {left right : List Selection}
    {responseName fieldName : Name} {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {fieldDefinition : FieldDefinition} {childRuntime : Name}
    {leftChildSpine rightChildSpine : List NormalSelectionSetObservableFieldStep}
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
      -> Selection.field responseName fieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName fieldName rightArguments rightDirectives
            rightChildSelectionSet
          ∈ right
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> SelectedPathCompositeFieldChildSource schema parentType fieldName
          leftArguments leftCurrentSelectionSet leftSpine fieldDefinition
          childRuntime leftChildSpine
      -> SelectedPathCompositeFieldChildSource schema parentType fieldName
          rightArguments rightCurrentSelectionSet rightSpine fieldDefinition
          childRuntime rightChildSpine
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType childRuntime
          = true
      -> SelectedPathTaggedSelectionSetsResponseDiffWitness schema
          rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
          leftInitialSpine rightInitialSpine variableValues
          (fuel - leafProbeFuel fieldDefinition.outputType)
          fieldDefinition.outputType.namedType childRuntime targetParent
          leftProbeField rightProbeField targetLeftArguments
          targetRightArguments leftRuntime rightRuntime
          (fieldPairPathLocalNextSelectionSet schema parentType childRuntime
            fieldName leftArguments leftCurrentSelectionSet)
          (fieldPairPathLocalNextSelectionSet schema parentType childRuntime
            fieldName rightArguments rightCurrentSelectionSet)
          leftChildSpine rightChildSpine leftChildSelectionSet
          rightChildSelectionSet
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
    hrightContext hleftMem hrightMem hlookup hcomposite hleftChildSource
    hrightChildSource hinclude hchildWitness
  rcases hchildWitness with
    ⟨_hchildInclude, leftChildFields, leftChildErrors,
      rightChildFields, rightChildErrors, hleftChildResponse,
      hrightChildResponse, hchildNot⟩
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
  have hleftReady :
      SelectedPathSelectionSetFieldChildrenReady schema rootSelectionSet
        leftInitialSelectionSet rightInitialSelectionSet
        leftCurrentSelectionSet leftInitialSpine rightInitialSpine
        leftSpine variableValues fuel targetParent leftProbeField
        rightProbeField parentType targetLeftArguments
        targetRightArguments leftRuntime rightRuntime FieldPairProbeTag.left
        left :=
    selectedPathSelectionSetFieldChildrenReady_of_valid_normal_runtimeSpine_support_context_fuel_ge
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet leftInitialSpine rightInitialSpine
      variableValues hschema parentType leftVariableDefinitions left fuel
      parentType targetParent leftProbeField rightProbeField
      targetLeftArguments targetRightArguments leftRuntime rightRuntime
      FieldPairProbeTag.left leftCurrentSelectionSet leftSpine
      hleftFuel hleftValid hleftFree hleftNormal hobject
      hleftSpineValid hleftSupport hleftContext
  have hrightReady :
      SelectedPathSelectionSetFieldChildrenReady schema rootSelectionSet
        leftInitialSelectionSet rightInitialSelectionSet
        rightCurrentSelectionSet leftInitialSpine rightInitialSpine
        rightSpine variableValues fuel targetParent leftProbeField
        rightProbeField parentType targetLeftArguments
        targetRightArguments leftRuntime rightRuntime FieldPairProbeTag.right
        right :=
    selectedPathSelectionSetFieldChildrenReady_of_valid_normal_runtimeSpine_support_context_fuel_ge
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet leftInitialSpine rightInitialSpine
      variableValues hschema parentType rightVariableDefinitions right fuel
      parentType targetParent leftProbeField rightProbeField
      targetLeftArguments targetRightArguments leftRuntime rightRuntime
      FieldPairProbeTag.right rightCurrentSelectionSet rightSpine
      hrightFuel hrightValid hrightFree hrightNormal hobject
      hrightSpineValid hrightSupport hrightContext
  have hleftFieldOk :
      ∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
            childSelectionSet ∈ left ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSelectedPathProbeResolvers schema
                  leftInitialSelectionSet rightInitialSelectionSet
                  leftInitialSpine rightInitialSpine targetParent
                  leftProbeField rightProbeField targetLeftArguments
                  targetRightArguments leftRuntime rightRuntime)
                targetParent leftProbeField rightProbeField
                targetLeftArguments targetRightArguments)
              variableValues (fuel + 1)
              (projectionTargetResolverValue
                (.object parentType
                  (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
                    leftCurrentSelectionSet leftSpine)))
              responseName
              [{
                parentType := parentType
                responseName := responseName
                fieldName := fieldName
                arguments := arguments
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(responseName, responseValue)], fieldErrors) := by
    exact
      executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_field_ok_of_selectedPathFieldChildrenReady
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftCurrentSelectionSet leftInitialSpine
        rightInitialSpine leftSpine variableValues fuel targetParent
        leftProbeField rightProbeField parentType parentType
        targetLeftArguments targetRightArguments leftRuntime rightRuntime
        FieldPairProbeTag.left left hleftReady
  have hrightFieldOk :
      ∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
            childSelectionSet ∈ right ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSelectedPathProbeResolvers schema
                  leftInitialSelectionSet rightInitialSelectionSet
                  leftInitialSpine rightInitialSpine targetParent
                  leftProbeField rightProbeField targetLeftArguments
                  targetRightArguments leftRuntime rightRuntime)
                targetParent leftProbeField rightProbeField
                targetLeftArguments targetRightArguments)
              variableValues (fuel + 1)
              (projectionTargetResolverValue
                (.object parentType
                  (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                    rightCurrentSelectionSet rightSpine)))
              responseName
              [{
                parentType := parentType
                responseName := responseName
                fieldName := fieldName
                arguments := arguments
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(responseName, responseValue)], fieldErrors) := by
    exact
      executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_field_ok_of_selectedPathFieldChildrenReady
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet rightCurrentSelectionSet leftInitialSpine
        rightInitialSpine rightSpine variableValues fuel targetParent
        leftProbeField rightProbeField parentType parentType
        targetLeftArguments targetRightArguments leftRuntime rightRuntime
        FieldPairProbeTag.right right hrightReady
  have hleafFuel :
      leafProbeFuel fieldDefinition.outputType ≤ fuel := by
    have hlocal :=
      leafProbeFuel_le_selectionSetDeepProbeFuel_of_field_mem schema
        parentType (selectionSet := left)
        (responseName := responseName) (fieldName := fieldName)
        (arguments := leftArguments) (directives := leftDirectives)
        (childSelectionSet := leftChildSelectionSet)
        (fieldDefinition := fieldDefinition) hleftMem hlookup
    omega
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
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_child_field_pair_of_field_ok_fuels
      schema rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet leftInitialSpine
      rightInitialSpine leftSpine rightSpine variableValues fuel fuel
      targetParent leftProbeField rightProbeField parentType parentType
      parentType parentType targetLeftArguments targetRightArguments
      leftRuntime rightRuntime hleftFree hrightFree hleftNormal
      hrightNormal hobject hobject hleftMem hrightMem hlookup hlookup
      hleftChildSource hrightChildSource hinclude hinclude hleafFuel
      hleafFuel hleftChildResponse hrightChildResponse hchildNot
      hleftFieldOk hrightFieldOk
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
    selectedPathTaggedSelectionSetsResponseDiffWitness_of_composite_sameField_rightPrunedChildWitness_valid_normal_runtimeSpine
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
    (leftRuntime rightRuntime : Name) {left right : List Selection}
    {responseName fieldName : Name} {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {fieldDefinition : FieldDefinition} {childRuntime : Name}
    {leftChildSpine rightChildSpine : List NormalSelectionSetObservableFieldStep}
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
      -> Selection.field responseName fieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName fieldName rightArguments rightDirectives
            rightChildSelectionSet
          ∈ right
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> SelectedPathCompositeFieldChildSource schema parentType fieldName
          leftArguments leftCurrentSelectionSet leftSpine fieldDefinition
          childRuntime leftChildSpine
      -> SelectedPathCompositeFieldChildSource schema parentType fieldName
          rightArguments rightCurrentSelectionSet rightSpine fieldDefinition
          childRuntime rightChildSpine
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType childRuntime
          = true
      -> SelectedPathTaggedSelectionSetsRightPrunedResponseDiffWitness schema
          rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
          leftInitialSpine rightInitialSpine variableValues
          (fuel - leafProbeFuel fieldDefinition.outputType)
          fieldDefinition.outputType.namedType childRuntime targetParent
          leftProbeField rightProbeField targetLeftArguments
          targetRightArguments leftRuntime rightRuntime
          (fieldPairPathLocalNextSelectionSet schema parentType childRuntime
            fieldName leftArguments leftCurrentSelectionSet)
          (fieldPairPathLocalNextSelectionSet schema parentType childRuntime
            fieldName rightArguments rightCurrentSelectionSet)
          leftChildSpine rightChildSpine leftChildSelectionSet
          rightChildSelectionSet
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
    hrightContext hleftMem hrightMem hlookup hcomposite hleftChildSource
    hrightChildSource hinclude hchildWitness
  exact
    selectedPathTaggedSelectionSetsResponseDiffWitness_of_composite_sameField_childWitness_valid_normal_runtimeSpine
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
      hrightContext hleftMem hrightMem hlookup hcomposite
      hleftChildSource hrightChildSource hinclude
      (selectedPathTaggedSelectionSetsResponseDiffWitness_of_rightPruned
        hchildWitness)

theorem
    selectedPathTaggedSelectionSetsResponseDiffWitness_of_composite_sameField_leftPrunedChildWitness_valid_normal_runtimeSpine
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
    (leftRuntime rightRuntime : Name) {left right : List Selection}
    {responseName fieldName : Name} {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {fieldDefinition : FieldDefinition} {childRuntime : Name}
    {leftChildSpine rightChildSpine : List NormalSelectionSetObservableFieldStep}
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
      -> Selection.field responseName fieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName fieldName rightArguments rightDirectives
            rightChildSelectionSet
          ∈ right
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> SelectedPathCompositeFieldChildSource schema parentType fieldName
          leftArguments leftCurrentSelectionSet leftSpine fieldDefinition
          childRuntime leftChildSpine
      -> SelectedPathCompositeFieldChildSource schema parentType fieldName
          rightArguments rightCurrentSelectionSet rightSpine fieldDefinition
          childRuntime rightChildSpine
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType childRuntime
          = true
      -> SelectedPathTaggedSelectionSetsLeftPrunedResponseDiffWitness schema
          rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
          leftInitialSpine rightInitialSpine variableValues
          (fuel - leafProbeFuel fieldDefinition.outputType)
          fieldDefinition.outputType.namedType childRuntime targetParent
          leftProbeField rightProbeField targetLeftArguments
          targetRightArguments leftRuntime rightRuntime
          (fieldPairPathLocalNextSelectionSet schema parentType childRuntime
            fieldName leftArguments leftCurrentSelectionSet)
          (fieldPairPathLocalNextSelectionSet schema parentType childRuntime
            fieldName rightArguments rightCurrentSelectionSet)
          leftChildSpine rightChildSpine leftChildSelectionSet
          rightChildSelectionSet
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
    hrightContext hleftMem hrightMem hlookup hcomposite hleftChildSource
    hrightChildSource hinclude hchildWitness
  exact
    selectedPathTaggedSelectionSetsResponseDiffWitness_of_composite_sameField_childWitness_valid_normal_runtimeSpine
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
      hrightContext hleftMem hrightMem hlookup hcomposite
      hleftChildSource hrightChildSource hinclude
      (selectedPathTaggedSelectionSetsResponseDiffWitness_of_leftPruned
        hchildWitness)

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_objectOutput_field_pair_of_valid_normal_runtimeSpine
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
      -> objectTypeNameBool schema rightFieldDefinition.outputType.namedType = true
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
              leftChildSelectionSet).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSelectedPathProbeResolvers schema
                  leftInitialSelectionSet rightInitialSelectionSet
                  leftInitialSpine rightInitialSpine targetParent leftProbeField
                  rightProbeField targetLeftArguments targetRightArguments
                  leftRuntime rightRuntime)
                targetParent leftProbeField rightProbeField targetLeftArguments
                targetRightArguments)
              variableValues
              (fuel - leafProbeFuel rightFieldDefinition.outputType)
              rightFieldDefinition.outputType.namedType
              (projectionTargetResolverValue
                (.object rightFieldDefinition.outputType.namedType
                  (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                    (fieldPairPathLocalNextSelectionSet schema rightParentType
                      rightFieldDefinition.outputType.namedType rightFieldName
                      rightArguments rightCurrentSelectionSet)
                    (selectedObservableFieldSpineTailForRuntime
                      rightFieldDefinition.outputType.namedType rightFieldName
                      rightArguments rightSpine))))
              rightChildSelectionSet).data
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
    hleftContext hrightContext hleftMem hrightMem hleftLookup
    hrightLookup hleftObjectOutput hrightObjectOutput hchildDataNot
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
      leftSpine hleftFuel hleftValid hleftFree hleftNormal hleftObject
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
      leftRuntime rightRuntime FieldPairProbeTag.right
      rightCurrentSelectionSet rightSpine hrightFuel hrightValid
      hrightFree hrightNormal hrightObject hrightSpineValid
      hrightSupport hrightContext
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
      executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_field_ok_of_selectedPathFieldChildrenReady
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet rightCurrentSelectionSet leftInitialSpine
        rightInitialSpine rightSpine variableValues fuel targetParent
        leftProbeField rightProbeField rightParentType
        rightSourceRuntimeType targetLeftArguments targetRightArguments
        leftRuntime rightRuntime FieldPairProbeTag.right right hrightReady
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
  rcases
      objectOutputChildResponse_of_selectedPathFieldChildrenReady
        (schema := schema)
        (rootSelectionSet := rootSelectionSet)
        (leftInitialSelectionSet := leftInitialSelectionSet)
        (rightInitialSelectionSet := rightInitialSelectionSet)
        (currentSelectionSet := rightCurrentSelectionSet)
        (selectionSet := right)
        (leftInitialSpine := leftInitialSpine)
        (rightInitialSpine := rightInitialSpine)
        (spine := rightSpine)
        (variableValues := variableValues) (fuel := fuel)
        (targetParent := targetParent) (leftField := leftProbeField)
        (rightField := rightProbeField) (parentType := rightParentType)
        (targetLeftArguments := targetLeftArguments)
        (targetRightArguments := targetRightArguments)
        (leftRuntime := leftRuntime) (rightRuntime := rightRuntime)
        (tag := FieldPairProbeTag.right)
        (responseName := responseName) (fieldName := rightFieldName)
        (arguments := rightArguments) (directives := rightDirectives)
        (childSelectionSet := rightChildSelectionSet)
        (fieldDefinition := rightFieldDefinition)
        hrightReady hrightMem hrightLookup hrightObjectOutput with
    ⟨rightChildFields, rightChildErrors, hrightChildResponse⟩
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
  have hchildNot :
      ¬ Execution.ResponseValue.semanticEquivalent
        (Execution.ResponseValue.object leftChildFields)
        (Execution.ResponseValue.object rightChildFields) := by
    intro hsemantic
    exact hchildDataNot
      (by simpa [hleftChildResponse, hrightChildResponse] using
        hsemantic)
  simpa [resolvers, leftSource, rightSource] using
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_objectOutput_field_pair_of_field_ok
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet leftCurrentSelectionSet
      rightCurrentSelectionSet leftInitialSpine rightInitialSpine
      leftSpine rightSpine variableValues fuel targetParent
      leftProbeField rightProbeField leftParentType rightParentType
      leftSourceRuntimeType rightSourceRuntimeType targetLeftArguments
      targetRightArguments leftRuntime rightRuntime hleftFree hrightFree
      hleftNormal hrightNormal hleftObject hrightObject hleftMem
      hrightMem hleftLookup hrightLookup hleftObjectOutput
      hrightObjectOutput hleftLeafFuel hrightLeafFuel hleftChildResponse
      hrightChildResponse hchildNot hleftFieldOk hrightFieldOk

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_objectOutput_field_pair_of_valid_normal_runtimeSpine_fuels
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
      -> objectTypeNameBool schema rightFieldDefinition.outputType.namedType = true
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
              leftChildSelectionSet).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSelectedPathProbeResolvers schema
                  leftInitialSelectionSet rightInitialSelectionSet
                  leftInitialSpine rightInitialSpine targetParent leftProbeField
                  rightProbeField targetLeftArguments targetRightArguments
                  leftRuntime rightRuntime)
                targetParent leftProbeField rightProbeField targetLeftArguments
                targetRightArguments)
              variableValues
              (rightFuel - leafProbeFuel rightFieldDefinition.outputType)
              rightFieldDefinition.outputType.namedType
              (projectionTargetResolverValue
                (.object rightFieldDefinition.outputType.namedType
                  (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                    (fieldPairPathLocalNextSelectionSet schema rightParentType
                      rightFieldDefinition.outputType.namedType rightFieldName
                      rightArguments rightCurrentSelectionSet)
                    (selectedObservableFieldSpineTailForRuntime
                      rightFieldDefinition.outputType.namedType rightFieldName
                      rightArguments rightSpine))))
              rightChildSelectionSet).data
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
    hleftContext hrightContext hleftMem hrightMem hleftLookup
    hrightLookup hleftObjectOutput hrightObjectOutput hchildDataNot
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
      leftSpine hleftFuel hleftValid hleftFree hleftNormal hleftObject
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
      leftRuntime rightRuntime FieldPairProbeTag.right
      rightCurrentSelectionSet rightSpine hrightFuel hrightValid
      hrightFree hrightNormal hrightObject hrightSpineValid
      hrightSupport hrightContext
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
      executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_field_ok_of_selectedPathFieldChildrenReady
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet rightCurrentSelectionSet leftInitialSpine
        rightInitialSpine rightSpine variableValues rightFuel targetParent
        leftProbeField rightProbeField rightParentType
        rightSourceRuntimeType targetLeftArguments targetRightArguments
        leftRuntime rightRuntime FieldPairProbeTag.right right hrightReady
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
  rcases
      objectOutputChildResponse_of_selectedPathFieldChildrenReady
        (schema := schema)
        (rootSelectionSet := rootSelectionSet)
        (leftInitialSelectionSet := leftInitialSelectionSet)
        (rightInitialSelectionSet := rightInitialSelectionSet)
        (currentSelectionSet := rightCurrentSelectionSet)
        (selectionSet := right)
        (leftInitialSpine := leftInitialSpine)
        (rightInitialSpine := rightInitialSpine)
        (spine := rightSpine)
        (variableValues := variableValues) (fuel := rightFuel)
        (targetParent := targetParent) (leftField := leftProbeField)
        (rightField := rightProbeField) (parentType := rightParentType)
        (targetLeftArguments := targetLeftArguments)
        (targetRightArguments := targetRightArguments)
        (leftRuntime := leftRuntime) (rightRuntime := rightRuntime)
        (tag := FieldPairProbeTag.right)
        (responseName := responseName) (fieldName := rightFieldName)
        (arguments := rightArguments) (directives := rightDirectives)
        (childSelectionSet := rightChildSelectionSet)
        (fieldDefinition := rightFieldDefinition)
        hrightReady hrightMem hrightLookup hrightObjectOutput with
    ⟨rightChildFields, rightChildErrors, hrightChildResponse⟩
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
  have hchildNot :
      ¬ Execution.ResponseValue.semanticEquivalent
        (Execution.ResponseValue.object leftChildFields)
        (Execution.ResponseValue.object rightChildFields) := by
    intro hsemantic
    exact hchildDataNot
      (by simpa [hleftChildResponse, hrightChildResponse] using
        hsemantic)
  simpa [resolvers, leftSource, rightSource] using
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_objectOutput_field_pair_of_field_ok_fuels
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet leftCurrentSelectionSet
      rightCurrentSelectionSet leftInitialSpine rightInitialSpine
      leftSpine rightSpine variableValues leftFuel rightFuel targetParent
      leftProbeField rightProbeField leftParentType rightParentType
      leftSourceRuntimeType rightSourceRuntimeType targetLeftArguments
      targetRightArguments leftRuntime rightRuntime hleftFree hrightFree
      hleftNormal hrightNormal hleftObject hrightObject hleftMem
      hrightMem hleftLookup hrightLookup hleftObjectOutput
      hrightObjectOutput hleftLeafFuel hrightLeafFuel hleftChildResponse
      hrightChildResponse hchildNot hleftFieldOk hrightFieldOk

theorem
    selectedPathTaggedSelectionSetsResponseDiffWitness_of_objectOutput_field_pair_childDataDiff_valid_normal_runtimeSpine
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
    (leftRuntime rightRuntime : Name) {left right : List Selection}
    {responseName leftFieldName rightFieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {leftFieldDefinition rightFieldDefinition : FieldDefinition}
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
      -> Selection.field responseName leftFieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName rightFieldName rightArguments
            rightDirectives rightChildSelectionSet
          ∈ right
      -> schema.lookupField parentType leftFieldName = some leftFieldDefinition
      -> schema.lookupField parentType rightFieldName = some rightFieldDefinition
      -> objectTypeNameBool schema leftFieldDefinition.outputType.namedType = true
      -> objectTypeNameBool schema rightFieldDefinition.outputType.namedType = true
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
              variableValues
              (fuel - leafProbeFuel leftFieldDefinition.outputType)
              leftFieldDefinition.outputType.namedType
              (projectionTargetResolverValue
                (.object leftFieldDefinition.outputType.namedType
                  (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
                    (fieldPairPathLocalNextSelectionSet schema parentType
                      leftFieldDefinition.outputType.namedType leftFieldName
                      leftArguments leftCurrentSelectionSet)
                    (selectedObservableFieldSpineTailForRuntime
                      leftFieldDefinition.outputType.namedType leftFieldName
                      leftArguments leftSpine))))
              leftChildSelectionSet).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSelectedPathProbeResolvers schema
                  leftInitialSelectionSet rightInitialSelectionSet
                  leftInitialSpine rightInitialSpine targetParent leftProbeField
                  rightProbeField targetLeftArguments targetRightArguments
                  leftRuntime rightRuntime)
                targetParent leftProbeField rightProbeField targetLeftArguments
                targetRightArguments)
              variableValues
              (fuel - leafProbeFuel rightFieldDefinition.outputType)
              rightFieldDefinition.outputType.namedType
              (projectionTargetResolverValue
                (.object rightFieldDefinition.outputType.namedType
                  (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                    (fieldPairPathLocalNextSelectionSet schema parentType
                      rightFieldDefinition.outputType.namedType rightFieldName
                      rightArguments rightCurrentSelectionSet)
                    (selectedObservableFieldSpineTailForRuntime
                      rightFieldDefinition.outputType.namedType rightFieldName
                      rightArguments rightSpine))))
              rightChildSelectionSet).data
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
    hrightContext hleftMem hrightMem hleftLookup hrightLookup
    hleftObjectOutput hrightObjectOutput hchildDataNot
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
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_objectOutput_field_pair_of_valid_normal_runtimeSpine
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
      hrightSupport hleftContext hrightContext hleftMem hrightMem
      hleftLookup hrightLookup hleftObjectOutput hrightObjectOutput
      hchildDataNot
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
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_objectOutput_sameField_of_selectedPathTaggedSelectionSetsResponseDiffWitness
    (schema : Schema)
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine leftSpine rightSpine
      : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftProbeField rightProbeField
      parentType leftSourceRuntimeType rightSourceRuntimeType
      : Name)
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
      -> SelectedFieldSpineRuntimeValid schema parentType leftSourceRuntimeType leftSpine
      -> SelectedFieldSpineRuntimeValid schema parentType
          rightSourceRuntimeType rightSpine
      -> PathLocalSupportValidNormal schema leftSourceRuntimeType leftCurrentSelectionSet
      -> PathLocalSupportValidNormal schema rightSourceRuntimeType
          rightCurrentSelectionSet
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
          (selectedObservableFieldSpineTailForRuntime
            fieldDefinition.outputType.namedType fieldName leftArguments
            leftSpine)
          (selectedObservableFieldSpineTailForRuntime
            fieldDefinition.outputType.namedType fieldName rightArguments
            rightSpine)
          leftChildSelectionSet rightChildSelectionSet
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
              variableValues (fuel + 1) parentType
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
              variableValues (fuel + 1) parentType
              (projectionTargetResolverValue
                (.object rightSourceRuntimeType
                  (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                    rightCurrentSelectionSet rightSpine)))
              right).data := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hobject hleftFuel hrightFuel hleftSpineValid
    hrightSpineValid hleftSupport hrightSupport hleftContext
    hrightContext hleftMem hrightMem hlookup hobjectOutput hchildWitness
  have hchildNot :
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
          variableValues
          (fuel - leafProbeFuel fieldDefinition.outputType)
          fieldDefinition.outputType.namedType
          (projectionTargetResolverValue
            (.object fieldDefinition.outputType.namedType
              (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
                (fieldPairPathLocalNextSelectionSet schema parentType
                  fieldDefinition.outputType.namedType fieldName
                  leftArguments leftCurrentSelectionSet)
                (selectedObservableFieldSpineTailForRuntime
                  fieldDefinition.outputType.namedType fieldName
                  leftArguments leftSpine))))
          leftChildSelectionSet).data
        (Execution.executeSelectionSetAsResponse schema
          (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
            (fieldPairSelectedPathProbeResolvers schema
              leftInitialSelectionSet rightInitialSelectionSet
              leftInitialSpine rightInitialSpine targetParent leftProbeField
              rightProbeField targetLeftArguments targetRightArguments
              leftRuntime rightRuntime)
            targetParent leftProbeField rightProbeField targetLeftArguments
            targetRightArguments)
          variableValues
          (fuel - leafProbeFuel fieldDefinition.outputType)
          fieldDefinition.outputType.namedType
          (projectionTargetResolverValue
            (.object fieldDefinition.outputType.namedType
              (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                (fieldPairPathLocalNextSelectionSet schema parentType
                  fieldDefinition.outputType.namedType fieldName
                  rightArguments rightCurrentSelectionSet)
                (selectedObservableFieldSpineTailForRuntime
                  fieldDefinition.outputType.namedType fieldName
                  rightArguments rightSpine))))
          rightChildSelectionSet).data :=
    responseData_not_semanticEquivalent_of_selectedPathTaggedSelectionSetsResponseDiffWitness
      hchildWitness
  exact
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_objectOutput_field_pair_of_valid_normal_runtimeSpine
      (schema := schema)
      (leftVariableDefinitions := leftVariableDefinitions)
      (rightVariableDefinitions := rightVariableDefinitions)
      rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet leftInitialSpine
      rightInitialSpine leftSpine rightSpine variableValues fuel
      targetParent leftProbeField rightProbeField parentType parentType
      leftSourceRuntimeType rightSourceRuntimeType targetLeftArguments
      targetRightArguments leftRuntime rightRuntime hschema hleftValid
      hrightValid hleftFree hrightFree hleftNormal hrightNormal hobject
      hobject hleftFuel hrightFuel hleftSpineValid hrightSpineValid
      hleftSupport hrightSupport hleftContext hrightContext hleftMem
      hrightMem hlookup hlookup hobjectOutput hobjectOutput hchildNot

theorem
    selectedPathTaggedSelectionSetsResponseDiffWitness_of_objectOutput_sameField_childWitness_valid_normal_runtimeSpine
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
      -> SelectedFieldSpineRuntimeValid schema parentType parentType leftSpine
      -> SelectedFieldSpineRuntimeValid schema parentType parentType rightSpine
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
          (selectedObservableFieldSpineTailForRuntime
            fieldDefinition.outputType.namedType fieldName leftArguments
            leftSpine)
          (selectedObservableFieldSpineTailForRuntime
            fieldDefinition.outputType.namedType fieldName rightArguments
            rightSpine)
          leftChildSelectionSet rightChildSelectionSet
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
    hrightContext hleftMem hrightMem hlookup hobjectOutput hchildWitness
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
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_objectOutput_sameField_of_selectedPathTaggedSelectionSetsResponseDiffWitness
      (schema := schema)
      (leftVariableDefinitions := leftVariableDefinitions)
      (rightVariableDefinitions := rightVariableDefinitions)
      rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet leftInitialSpine
      rightInitialSpine leftSpine rightSpine variableValues fuel
      targetParent leftProbeField rightProbeField parentType parentType
      parentType targetLeftArguments targetRightArguments leftRuntime
      rightRuntime hschema hleftValid hrightValid hleftFree hrightFree
      hleftNormal hrightNormal hobject hleftFuel hrightFuel
      hleftSpineValid hrightSpineValid hleftSupport hrightSupport
      hleftContext hrightContext hleftMem hrightMem hlookup
      hobjectOutput hchildWitness
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
    selectedPathTaggedSelectionSetsResponseDiffWitness_of_objectOutput_sameField_rightPrunedChildWitness_valid_normal_runtimeSpine
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
      -> SelectedFieldSpineRuntimeValid schema parentType parentType leftSpine
      -> SelectedFieldSpineRuntimeValid schema parentType parentType rightSpine
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
      -> SelectedPathTaggedSelectionSetsRightPrunedResponseDiffWitness schema
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
          leftChildSelectionSet rightChildSelectionSet
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
    hrightContext hleftMem hrightMem hlookup hobjectOutput
    hchildWitness
  exact
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
      (selectedPathTaggedSelectionSetsResponseDiffWitness_of_rightPruned
        hchildWitness)

theorem
    selectedPathTaggedSelectionSetsResponseDiffWitness_of_objectOutput_sameField_leftPrunedChildWitness_valid_normal_runtimeSpine
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
      -> SelectedFieldSpineRuntimeValid schema parentType parentType leftSpine
      -> SelectedFieldSpineRuntimeValid schema parentType parentType rightSpine
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
      -> SelectedPathTaggedSelectionSetsLeftPrunedResponseDiffWitness schema
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
          leftChildSelectionSet rightChildSelectionSet
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
    hrightContext hleftMem hrightMem hlookup hobjectOutput
    hchildWitness
  exact
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
      (selectedPathTaggedSelectionSetsResponseDiffWitness_of_leftPruned
        hchildWitness)

end GroundTypeNormalization

end NormalForm

end GraphQL
