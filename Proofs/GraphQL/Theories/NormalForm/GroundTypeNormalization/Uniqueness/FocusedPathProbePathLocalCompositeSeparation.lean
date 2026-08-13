import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.FocusedPathProbePathLocalLeafSeparation

/-!
Composite-child and abstract-body separation through path-local focused probes.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_child_field_of_field_ok
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet currentSelectionSet
      : List Selection)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField parentType sourceRuntimeType : Name)
    (leftArguments rightArguments : List Argument) (leftRuntime rightRuntime : Name)
    {selectionSet : List Selection} {responseName fieldName : Name}
    {arguments : List Argument} {directives : List DirectiveApplication}
    {childSelectionSet : List Selection} {fieldDefinition : FieldDefinition}
    {runtimeType : Name}
    {leftChildFields rightChildFields : List (Name × Execution.ResponseValue)}
    {leftChildErrors rightChildErrors : Nat}
    : selectionSetDirectiveFree selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> objectTypeNameBool schema parentType = true
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> ((objectTypeNameBool schema fieldDefinition.outputType.namedType = true
            ∧ runtimeType = fieldDefinition.outputType.namedType)
          ∨ ((TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
                = true
              ∧ objectTypeNameBool schema fieldDefinition.outputType.namedType = false
              ∧ abstractRuntimeForFieldHeadDeep? schema parentType fieldName
                  arguments parentType currentSelectionSet
                = some runtimeType))
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType runtimeType
          = true
      -> leafProbeFuel fieldDefinition.outputType ≤ fuel
      -> Execution.executeSelectionSetAsResponse schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet targetParent leftField rightField
                leftArguments rightArguments leftRuntime rightRuntime)
              targetParent leftField rightField leftArguments rightArguments)
            variableValues
            (fuel - leafProbeFuel fieldDefinition.outputType)
            runtimeType
            (projectionTargetResolverValue
              (.object runtimeType
                (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                  (fieldPairPathLocalNextSelectionSet schema parentType
                    runtimeType fieldName arguments currentSelectionSet))))
            childSelectionSet
          = ({
                data := Execution.ResponseValue.object leftChildFields,
                errors := leftChildErrors
              }
              : Execution.Response)
      -> Execution.executeSelectionSetAsResponse schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet targetParent leftField rightField
                leftArguments rightArguments leftRuntime rightRuntime)
              targetParent leftField rightField leftArguments rightArguments)
            variableValues
            (fuel - leafProbeFuel fieldDefinition.outputType)
            runtimeType
            (projectionTargetResolverValue
              (.object runtimeType
                (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                  (fieldPairPathLocalNextSelectionSet schema parentType
                    runtimeType fieldName arguments currentSelectionSet))))
            childSelectionSet
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
              ∈ selectionSet
            -> ∃ responseValue fieldErrors,
                Execution.executeField schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                      rightInitialSelectionSet targetParent leftField rightField
                      leftArguments rightArguments leftRuntime rightRuntime)
                    targetParent leftField rightField leftArguments rightArguments)
                  variableValues (fuel + 1)
                  (projectionTargetResolverValue
                    (.object sourceRuntimeType
                      (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                        currentSelectionSet)))
                  responseName
                  [{
                    parentType := parentType
                    responseName := responseName
                    fieldName := fieldName
                    arguments := arguments
                    selectionSet := childSelectionSet
                  }]
                = .ok ([(responseName, responseValue)], fieldErrors))
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ selectionSet
            -> ∃ responseValue fieldErrors,
                Execution.executeField schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                      rightInitialSelectionSet targetParent leftField rightField
                      leftArguments rightArguments leftRuntime rightRuntime)
                    targetParent leftField rightField leftArguments rightArguments)
                  variableValues (fuel + 1)
                  (projectionTargetResolverValue
                    (.object sourceRuntimeType
                      (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                        currentSelectionSet)))
                  responseName
                  [{
                    parentType := parentType
                    responseName := responseName
                    fieldName := fieldName
                    arguments := arguments
                    selectionSet := childSelectionSet
                  }]
                = .ok ([(responseName, responseValue)], fieldErrors))
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet targetParent leftField rightField
                  leftArguments rightArguments leftRuntime rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) parentType
              (projectionTargetResolverValue
                (.object sourceRuntimeType
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                    currentSelectionSet)))
              selectionSet).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet targetParent leftField rightField
                  leftArguments rightArguments leftRuntime rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) parentType
              (projectionTargetResolverValue
                (.object sourceRuntimeType
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                    currentSelectionSet)))
              selectionSet).data := by
  intro hfree hnormal hobject hmem hlookup hruntime hinclude hfuel
    hleftChildResponse hrightChildResponse hchildNot hleftFieldOk
    hrightFieldOk
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet
      (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
        rightInitialSelectionSet targetParent leftField rightField
        leftArguments rightArguments leftRuntime rightRuntime)
      targetParent leftField rightField leftArguments rightArguments
  let leftSource :=
    projectionTargetResolverValue
      (.object sourceRuntimeType
        (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
          currentSelectionSet))
  let rightSource :=
    projectionTargetResolverValue
      (.object sourceRuntimeType
        (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
          currentSelectionSet))
  let leftChildResponse : Execution.Response :=
    { data := Execution.ResponseValue.object leftChildFields,
      errors := leftChildErrors }
  let rightChildResponse : Execution.Response :=
    { data := Execution.ResponseValue.object rightChildFields,
      errors := rightChildErrors }
  rcases
      wrapTypeRefSelectionSetResult_ok_nonNull_of_object_response
        fieldDefinition.outputType leftChildFields leftChildErrors with
    ⟨leftValue, leftFieldErrors, hleftWrapped, _hleftNonNull⟩
  rcases
      wrapTypeRefSelectionSetResult_ok_nonNull_of_object_response
        fieldDefinition.outputType rightChildFields rightChildErrors with
    ⟨rightValue, rightFieldErrors, hrightWrapped, _hrightNonNull⟩
  have hleftTarget :
      Execution.executeField schema resolvers variableValues (fuel + 1)
        leftSource responseName
        [{
          parentType := parentType
          responseName := responseName
          fieldName := fieldName
          arguments := arguments
          selectionSet := childSelectionSet
        }]
      =
      .ok ([(responseName, leftValue)], leftFieldErrors) := by
    dsimp [resolvers, leftSource]
    rw [
      executeField_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_objectProbe_response_of_fuel_ge
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet currentSelectionSet variableValues fuel
        targetParent leftField rightField parentType fieldName
        sourceRuntimeType responseName leftArguments rightArguments
        arguments leftRuntime rightRuntime FieldPairProbeTag.left
        childSelectionSet fieldDefinition runtimeType hlookup hruntime
        hinclude hfuel]
    rw [hleftChildResponse]
    simp [Execution.singleFieldResult, hleftWrapped]
  have hrightTarget :
      Execution.executeField schema resolvers variableValues (fuel + 1)
        rightSource responseName
        [{
          parentType := parentType
          responseName := responseName
          fieldName := fieldName
          arguments := arguments
          selectionSet := childSelectionSet
        }]
      =
      .ok ([(responseName, rightValue)], rightFieldErrors) := by
    dsimp [resolvers, rightSource]
    rw [
      executeField_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_objectProbe_response_of_fuel_ge
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet currentSelectionSet variableValues fuel
        targetParent leftField rightField parentType fieldName
        sourceRuntimeType responseName leftArguments rightArguments
        arguments leftRuntime rightRuntime FieldPairProbeTag.right
        childSelectionSet fieldDefinition runtimeType hlookup hruntime
        hinclude hfuel]
    rw [hrightChildResponse]
    simp [Execution.singleFieldResult, hrightWrapped]
  have hvalueNot :
      ¬ Execution.ResponseValue.semanticEquivalent leftValue rightValue := by
    intro hvalue
    apply
      not_wrapTypeRefSelectionSetResponse_data_semanticEquivalent_of_child
        responseName fieldDefinition.outputType
        (left := leftChildResponse) (right := rightChildResponse)
    · simpa [leftChildResponse, rightChildResponse] using hchildNot
    · have hsingle :
          Execution.ResponseValue.semanticEquivalent
            (Execution.ResponseValue.object [(responseName, leftValue)])
            (Execution.ResponseValue.object [(responseName, rightValue)]) :=
        responseValue_semanticEquivalent_singleton_object_field_of_canonical_eq
          (by
            simpa [Execution.ResponseValue.semanticEquivalent] using hvalue)
      simpa [wrapTypeRefSelectionSetResponse, leftChildResponse,
        rightChildResponse, hleftWrapped, hrightWrapped,
        Execution.singleFieldResult, Execution.selectionSetResultToResponse]
        using hsingle
  exact
    SemanticSeparation.responseData_not_semanticEquivalent_of_field_value_diff_of_field_ok
      resolvers resolvers variableValues (fuel + 1) leftSource rightSource
      hobject hnormal hnormal hfree hfree hmem hmem hleftTarget
      hrightTarget hvalueNot hleftFieldOk hrightFieldOk

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_child_field_pair_of_field_ok
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
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
    {leftChildRuntime rightChildRuntime : Name}
    {leftChildFields rightChildFields : List (Name × Execution.ResponseValue)}
    {leftChildErrors rightChildErrors : Nat}
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
      -> ((objectTypeNameBool schema leftFieldDefinition.outputType.namedType = true
            ∧ leftChildRuntime = leftFieldDefinition.outputType.namedType)
          ∨ ((TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool
                  schema
                = true
              ∧ objectTypeNameBool schema leftFieldDefinition.outputType.namedType = false
              ∧ abstractRuntimeForFieldHeadDeep? schema leftParentType
                  leftFieldName leftArguments leftParentType
                  leftCurrentSelectionSet
                = some leftChildRuntime))
      -> ((objectTypeNameBool schema rightFieldDefinition.outputType.namedType = true
            ∧ rightChildRuntime = rightFieldDefinition.outputType.namedType)
          ∨ ((TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool
                  schema
                = true
              ∧ objectTypeNameBool schema rightFieldDefinition.outputType.namedType
                = false
              ∧ abstractRuntimeForFieldHeadDeep? schema rightParentType
                  rightFieldName rightArguments rightParentType
                  rightCurrentSelectionSet
                = some rightChildRuntime))
      -> schema.typeIncludesObjectBool leftFieldDefinition.outputType.namedType
            leftChildRuntime
          = true
      -> schema.typeIncludesObjectBool rightFieldDefinition.outputType.namedType
            rightChildRuntime
          = true
      -> leafProbeFuel leftFieldDefinition.outputType ≤ fuel
      -> leafProbeFuel rightFieldDefinition.outputType ≤ fuel
      -> Execution.executeSelectionSetAsResponse schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet targetParent leftProbeField
                rightProbeField targetLeftArguments targetRightArguments
                leftRuntime rightRuntime)
              targetParent leftProbeField rightProbeField targetLeftArguments
              targetRightArguments)
            variableValues
            (fuel - leafProbeFuel leftFieldDefinition.outputType)
            leftChildRuntime
            (projectionTargetResolverValue
              (.object leftChildRuntime
                (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                  (fieldPairPathLocalNextSelectionSet schema leftParentType
                    leftChildRuntime leftFieldName leftArguments
                    leftCurrentSelectionSet))))
            leftChildSelectionSet
          = ({
                data := Execution.ResponseValue.object leftChildFields,
                errors := leftChildErrors
              }
              : Execution.Response)
      -> Execution.executeSelectionSetAsResponse schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet targetParent leftProbeField
                rightProbeField targetLeftArguments targetRightArguments
                leftRuntime rightRuntime)
              targetParent leftProbeField rightProbeField targetLeftArguments
              targetRightArguments)
            variableValues
            (fuel - leafProbeFuel rightFieldDefinition.outputType)
            rightChildRuntime
            (projectionTargetResolverValue
              (.object rightChildRuntime
                (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                  (fieldPairPathLocalNextSelectionSet schema rightParentType
                    rightChildRuntime rightFieldName rightArguments
                    rightCurrentSelectionSet))))
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
                    (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                      rightInitialSelectionSet targetParent leftProbeField
                      rightProbeField targetLeftArguments targetRightArguments
                      leftRuntime rightRuntime)
                    targetParent leftProbeField rightProbeField
                    targetLeftArguments targetRightArguments)
                  variableValues (fuel + 1)
                  (projectionTargetResolverValue
                    (.object leftSourceRuntimeType
                      (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                        leftCurrentSelectionSet)))
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
                    (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                      rightInitialSelectionSet targetParent leftProbeField
                      rightProbeField targetLeftArguments targetRightArguments
                      leftRuntime rightRuntime)
                    targetParent leftProbeField rightProbeField
                    targetLeftArguments targetRightArguments)
                  variableValues (fuel + 1)
                  (projectionTargetResolverValue
                    (.object rightSourceRuntimeType
                      (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                        rightCurrentSelectionSet)))
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
                (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet targetParent leftProbeField
                  rightProbeField targetLeftArguments targetRightArguments
                  leftRuntime rightRuntime)
                targetParent leftProbeField rightProbeField targetLeftArguments
                targetRightArguments)
              variableValues (fuel + 1) leftParentType
              (projectionTargetResolverValue
                (.object leftSourceRuntimeType
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                    leftCurrentSelectionSet)))
              left).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet targetParent leftProbeField
                  rightProbeField targetLeftArguments targetRightArguments
                  leftRuntime rightRuntime)
                targetParent leftProbeField rightProbeField targetLeftArguments
                targetRightArguments)
              variableValues (fuel + 1) rightParentType
              (projectionTargetResolverValue
                (.object rightSourceRuntimeType
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                    rightCurrentSelectionSet)))
              right).data := by
  intro hleftFree hrightFree hleftNormal hrightNormal hleftObject
    hrightObject hleftMem hrightMem hleftLookup hrightLookup hleftRuntime
    hrightRuntime hleftInclude hrightInclude hleftFuel hrightFuel
    hleftChildResponse hrightChildResponse hchildNot hleftFieldOk
    hrightFieldOk
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet
      (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
        rightInitialSelectionSet targetParent leftProbeField rightProbeField
        targetLeftArguments targetRightArguments leftRuntime rightRuntime)
      targetParent leftProbeField rightProbeField targetLeftArguments
      targetRightArguments
  let leftSource :=
    projectionTargetResolverValue
      (.object leftSourceRuntimeType
        (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
          leftCurrentSelectionSet))
  let rightSource :=
    projectionTargetResolverValue
      (.object rightSourceRuntimeType
        (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
          rightCurrentSelectionSet))
  let leftChildResponse : Execution.Response :=
    { data := Execution.ResponseValue.object leftChildFields,
      errors := leftChildErrors }
  let rightChildResponse : Execution.Response :=
    { data := Execution.ResponseValue.object rightChildFields,
      errors := rightChildErrors }
  rcases
      wrapTypeRefSelectionSetResult_ok_nonNull_of_object_response
        leftFieldDefinition.outputType leftChildFields leftChildErrors with
    ⟨leftValue, leftFieldErrors, hleftWrapped, _hleftNonNull⟩
  rcases
      wrapTypeRefSelectionSetResult_ok_nonNull_of_object_response
        rightFieldDefinition.outputType rightChildFields
        rightChildErrors with
    ⟨rightValue, rightFieldErrors, hrightWrapped, _hrightNonNull⟩
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
      .ok ([(responseName, leftValue)], leftFieldErrors) := by
    dsimp [resolvers, leftSource]
    rw [
      executeField_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_objectProbe_response_of_fuel_ge
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftCurrentSelectionSet variableValues fuel
        targetParent leftProbeField rightProbeField leftParentType
        leftFieldName leftSourceRuntimeType responseName
        targetLeftArguments targetRightArguments leftArguments leftRuntime
        rightRuntime FieldPairProbeTag.left leftChildSelectionSet
        leftFieldDefinition leftChildRuntime hleftLookup hleftRuntime
        hleftInclude hleftFuel]
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
      .ok ([(responseName, rightValue)], rightFieldErrors) := by
    dsimp [resolvers, rightSource]
    rw [
      executeField_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_objectProbe_response_of_fuel_ge
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet rightCurrentSelectionSet variableValues fuel
        targetParent leftProbeField rightProbeField rightParentType
        rightFieldName rightSourceRuntimeType responseName
        targetLeftArguments targetRightArguments rightArguments leftRuntime
        rightRuntime FieldPairProbeTag.right rightChildSelectionSet
        rightFieldDefinition rightChildRuntime hrightLookup hrightRuntime
        hrightInclude hrightFuel]
    rw [hrightChildResponse]
    simp [Execution.singleFieldResult, hrightWrapped]
  have hvalueNot :
      ¬ Execution.ResponseValue.semanticEquivalent leftValue rightValue :=
    wrapped_object_values_not_semanticEquivalent_of_child
      leftFieldDefinition.outputType rightFieldDefinition.outputType
      hleftWrapped hrightWrapped hchildNot
  exact
    SemanticSeparation.responseData_not_semanticEquivalent_of_field_value_diff_of_field_ok_pair
      resolvers resolvers variableValues (fuel + 1) leftSource rightSource
      hleftObject hrightObject hleftNormal hrightNormal hleftFree
      hrightFree hleftMem hrightMem hleftTarget hrightTarget hvalueNot
      hleftFieldOk hrightFieldOk

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_child_field_pair_of_field_ok_fuels
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (variableValues : Execution.VariableValues) (leftFuel rightFuel : Nat)
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
    {leftChildRuntime rightChildRuntime : Name}
    {leftChildFields rightChildFields : List (Name × Execution.ResponseValue)}
    {leftChildErrors rightChildErrors : Nat}
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
      -> ((objectTypeNameBool schema leftFieldDefinition.outputType.namedType = true
            ∧ leftChildRuntime = leftFieldDefinition.outputType.namedType)
          ∨ ((TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool
                  schema
                = true
              ∧ objectTypeNameBool schema leftFieldDefinition.outputType.namedType = false
              ∧ abstractRuntimeForFieldHeadDeep? schema leftParentType
                  leftFieldName leftArguments leftParentType
                  leftCurrentSelectionSet
                = some leftChildRuntime))
      -> ((objectTypeNameBool schema rightFieldDefinition.outputType.namedType = true
            ∧ rightChildRuntime = rightFieldDefinition.outputType.namedType)
          ∨ ((TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool
                  schema
                = true
              ∧ objectTypeNameBool schema rightFieldDefinition.outputType.namedType
                = false
              ∧ abstractRuntimeForFieldHeadDeep? schema rightParentType
                  rightFieldName rightArguments rightParentType
                  rightCurrentSelectionSet
                = some rightChildRuntime))
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
              (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet targetParent leftProbeField
                rightProbeField targetLeftArguments targetRightArguments
                leftRuntime rightRuntime)
              targetParent leftProbeField rightProbeField targetLeftArguments
              targetRightArguments)
            variableValues
            (leftFuel - leafProbeFuel leftFieldDefinition.outputType)
            leftChildRuntime
            (projectionTargetResolverValue
              (.object leftChildRuntime
                (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                  (fieldPairPathLocalNextSelectionSet schema leftParentType
                    leftChildRuntime leftFieldName leftArguments
                    leftCurrentSelectionSet))))
            leftChildSelectionSet
          = ({
                data := Execution.ResponseValue.object leftChildFields,
                errors := leftChildErrors
              }
              : Execution.Response)
      -> Execution.executeSelectionSetAsResponse schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet targetParent leftProbeField
                rightProbeField targetLeftArguments targetRightArguments
                leftRuntime rightRuntime)
              targetParent leftProbeField rightProbeField targetLeftArguments
              targetRightArguments)
            variableValues
            (rightFuel - leafProbeFuel rightFieldDefinition.outputType)
            rightChildRuntime
            (projectionTargetResolverValue
              (.object rightChildRuntime
                (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                  (fieldPairPathLocalNextSelectionSet schema rightParentType
                    rightChildRuntime rightFieldName rightArguments
                    rightCurrentSelectionSet))))
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
                    (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                      rightInitialSelectionSet targetParent leftProbeField
                      rightProbeField targetLeftArguments targetRightArguments
                      leftRuntime rightRuntime)
                    targetParent leftProbeField rightProbeField
                    targetLeftArguments targetRightArguments)
                  variableValues (leftFuel + 1)
                  (projectionTargetResolverValue
                    (.object leftSourceRuntimeType
                      (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                        leftCurrentSelectionSet)))
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
                    (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                      rightInitialSelectionSet targetParent leftProbeField
                      rightProbeField targetLeftArguments targetRightArguments
                      leftRuntime rightRuntime)
                    targetParent leftProbeField rightProbeField
                    targetLeftArguments targetRightArguments)
                  variableValues (rightFuel + 1)
                  (projectionTargetResolverValue
                    (.object rightSourceRuntimeType
                      (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                        rightCurrentSelectionSet)))
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
                (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet targetParent leftProbeField
                  rightProbeField targetLeftArguments targetRightArguments
                  leftRuntime rightRuntime)
                targetParent leftProbeField rightProbeField targetLeftArguments
                targetRightArguments)
              variableValues (leftFuel + 1) leftParentType
              (projectionTargetResolverValue
                (.object leftSourceRuntimeType
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                    leftCurrentSelectionSet)))
              left).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet targetParent leftProbeField
                  rightProbeField targetLeftArguments targetRightArguments
                  leftRuntime rightRuntime)
                targetParent leftProbeField rightProbeField targetLeftArguments
                targetRightArguments)
              variableValues (rightFuel + 1) rightParentType
              (projectionTargetResolverValue
                (.object rightSourceRuntimeType
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                    rightCurrentSelectionSet)))
              right).data := by
  intro hleftFree hrightFree hleftNormal hrightNormal hleftObject
    hrightObject hleftMem hrightMem hleftLookup hrightLookup hleftRuntime
    hrightRuntime hleftInclude hrightInclude hleftFuel hrightFuel
    hleftChildResponse hrightChildResponse hchildNot hleftFieldOk
    hrightFieldOk
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet
      (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
        rightInitialSelectionSet targetParent leftProbeField rightProbeField
        targetLeftArguments targetRightArguments leftRuntime rightRuntime)
      targetParent leftProbeField rightProbeField targetLeftArguments
      targetRightArguments
  let leftSource :=
    projectionTargetResolverValue
      (.object leftSourceRuntimeType
        (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
          leftCurrentSelectionSet))
  let rightSource :=
    projectionTargetResolverValue
      (.object rightSourceRuntimeType
        (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
          rightCurrentSelectionSet))
  let leftChildResponse : Execution.Response :=
    { data := Execution.ResponseValue.object leftChildFields,
      errors := leftChildErrors }
  let rightChildResponse : Execution.Response :=
    { data := Execution.ResponseValue.object rightChildFields,
      errors := rightChildErrors }
  rcases
      wrapTypeRefSelectionSetResult_ok_nonNull_of_object_response
        leftFieldDefinition.outputType leftChildFields leftChildErrors with
    ⟨leftValue, leftFieldErrors, hleftWrapped, _hleftNonNull⟩
  rcases
      wrapTypeRefSelectionSetResult_ok_nonNull_of_object_response
        rightFieldDefinition.outputType rightChildFields
        rightChildErrors with
    ⟨rightValue, rightFieldErrors, hrightWrapped, _hrightNonNull⟩
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
      .ok ([(responseName, leftValue)], leftFieldErrors) := by
    dsimp [resolvers, leftSource]
    rw [
      executeField_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_objectProbe_response_of_fuel_ge
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftCurrentSelectionSet variableValues
        leftFuel targetParent leftProbeField rightProbeField
        leftParentType leftFieldName leftSourceRuntimeType responseName
        targetLeftArguments targetRightArguments leftArguments
        leftRuntime rightRuntime FieldPairProbeTag.left
        leftChildSelectionSet leftFieldDefinition leftChildRuntime
        hleftLookup hleftRuntime hleftInclude hleftFuel]
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
      .ok ([(responseName, rightValue)], rightFieldErrors) := by
    dsimp [resolvers, rightSource]
    rw [
      executeField_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_objectProbe_response_of_fuel_ge
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet rightCurrentSelectionSet variableValues
        rightFuel targetParent leftProbeField rightProbeField
        rightParentType rightFieldName rightSourceRuntimeType responseName
        targetLeftArguments targetRightArguments rightArguments
        leftRuntime rightRuntime FieldPairProbeTag.right
        rightChildSelectionSet rightFieldDefinition rightChildRuntime
        hrightLookup hrightRuntime hrightInclude hrightFuel]
    rw [hrightChildResponse]
    simp [Execution.singleFieldResult, hrightWrapped]
  have hvalueNot :
      ¬ Execution.ResponseValue.semanticEquivalent leftValue rightValue :=
    wrapped_object_values_not_semanticEquivalent_of_child
      leftFieldDefinition.outputType rightFieldDefinition.outputType
      hleftWrapped hrightWrapped hchildNot
  exact
    SemanticSeparation.responseData_not_semanticEquivalent_of_field_value_diff_of_field_ok_pair_fuels
      resolvers resolvers variableValues (leftFuel + 1) (rightFuel + 1)
      leftSource rightSource hleftObject hrightObject hleftNormal
      hrightNormal hleftFree hrightFree hleftMem hrightMem hleftTarget
      hrightTarget hvalueNot hleftFieldOk hrightFieldOk

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_child_field_pair_of_field_children
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
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
    {leftChildRuntime rightChildRuntime : Name}
    {leftChildFields rightChildFields : List (Name × Execution.ResponseValue)}
    {leftChildErrors rightChildErrors : Nat}
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
      -> ((objectTypeNameBool schema leftFieldDefinition.outputType.namedType = true
            ∧ leftChildRuntime = leftFieldDefinition.outputType.namedType)
          ∨ ((TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool
                  schema
                = true
              ∧ objectTypeNameBool schema leftFieldDefinition.outputType.namedType = false
              ∧ abstractRuntimeForFieldHeadDeep? schema leftParentType
                  leftFieldName leftArguments leftParentType
                  leftCurrentSelectionSet
                = some leftChildRuntime))
      -> ((objectTypeNameBool schema rightFieldDefinition.outputType.namedType = true
            ∧ rightChildRuntime = rightFieldDefinition.outputType.namedType)
          ∨ ((TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool
                  schema
                = true
              ∧ objectTypeNameBool schema rightFieldDefinition.outputType.namedType
                = false
              ∧ abstractRuntimeForFieldHeadDeep? schema rightParentType
                  rightFieldName rightArguments rightParentType
                  rightCurrentSelectionSet
                = some rightChildRuntime))
      -> schema.typeIncludesObjectBool leftFieldDefinition.outputType.namedType
            leftChildRuntime
          = true
      -> schema.typeIncludesObjectBool rightFieldDefinition.outputType.namedType
            rightChildRuntime
          = true
      -> leafProbeFuel leftFieldDefinition.outputType ≤ fuel
      -> leafProbeFuel rightFieldDefinition.outputType ≤ fuel
      -> Execution.executeSelectionSetAsResponse schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet targetParent leftProbeField
                rightProbeField targetLeftArguments targetRightArguments
                leftRuntime rightRuntime)
              targetParent leftProbeField rightProbeField targetLeftArguments
              targetRightArguments)
            variableValues
            (fuel - leafProbeFuel leftFieldDefinition.outputType)
            leftChildRuntime
            (projectionTargetResolverValue
              (.object leftChildRuntime
                (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                  (fieldPairPathLocalNextSelectionSet schema leftParentType
                    leftChildRuntime leftFieldName leftArguments
                    leftCurrentSelectionSet))))
            leftChildSelectionSet
          = ({
                data := Execution.ResponseValue.object leftChildFields,
                errors := leftChildErrors
              }
              : Execution.Response)
      -> Execution.executeSelectionSetAsResponse schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet targetParent leftProbeField
                rightProbeField targetLeftArguments targetRightArguments
                leftRuntime rightRuntime)
              targetParent leftProbeField rightProbeField targetLeftArguments
              targetRightArguments)
            variableValues
            (fuel - leafProbeFuel rightFieldDefinition.outputType)
            rightChildRuntime
            (projectionTargetResolverValue
              (.object rightChildRuntime
                (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                  (fieldPairPathLocalNextSelectionSet schema rightParentType
                    rightChildRuntime rightFieldName rightArguments
                    rightCurrentSelectionSet))))
            rightChildSelectionSet
          = ({
                data := Execution.ResponseValue.object rightChildFields,
                errors := rightChildErrors
              }
              : Execution.Response)
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.ResponseValue.object leftChildFields)
            (Execution.ResponseValue.object rightChildFields)
      -> PathLocalSelectionSetFieldChildrenReady schema rootSelectionSet
          leftInitialSelectionSet rightInitialSelectionSet variableValues fuel
          targetParent leftProbeField rightProbeField leftParentType
          targetLeftArguments targetRightArguments leftRuntime rightRuntime
          FieldPairProbeTag.left leftCurrentSelectionSet left
      -> PathLocalSelectionSetFieldChildrenReady schema rootSelectionSet
          leftInitialSelectionSet rightInitialSelectionSet variableValues fuel
          targetParent leftProbeField rightProbeField rightParentType
          targetLeftArguments targetRightArguments leftRuntime rightRuntime
          FieldPairProbeTag.right rightCurrentSelectionSet right
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet targetParent leftProbeField
                  rightProbeField targetLeftArguments targetRightArguments
                  leftRuntime rightRuntime)
                targetParent leftProbeField rightProbeField targetLeftArguments
                targetRightArguments)
              variableValues (fuel + 1) leftParentType
              (projectionTargetResolverValue
                (.object leftSourceRuntimeType
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                    leftCurrentSelectionSet)))
              left).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet targetParent leftProbeField
                  rightProbeField targetLeftArguments targetRightArguments
                  leftRuntime rightRuntime)
                targetParent leftProbeField rightProbeField targetLeftArguments
                targetRightArguments)
              variableValues (fuel + 1) rightParentType
              (projectionTargetResolverValue
                (.object rightSourceRuntimeType
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                    rightCurrentSelectionSet)))
              right).data := by
  intro hleftFree hrightFree hleftNormal hrightNormal hleftObject
    hrightObject hleftMem hrightMem hleftLookup hrightLookup hleftRuntime
    hrightRuntime hleftInclude hrightInclude hleftFuel hrightFuel
    hleftChildResponse hrightChildResponse hchildNot hleftChildren
    hrightChildren
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet
      (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
        rightInitialSelectionSet targetParent leftProbeField rightProbeField
        targetLeftArguments targetRightArguments leftRuntime rightRuntime)
      targetParent leftProbeField rightProbeField targetLeftArguments
      targetRightArguments
  let leftSource :=
    projectionTargetResolverValue
      (.object leftSourceRuntimeType
        (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
          leftCurrentSelectionSet))
  let rightSource :=
    projectionTargetResolverValue
      (.object rightSourceRuntimeType
        (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
          rightCurrentSelectionSet))
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
      executeField_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_field_ok_of_field_children
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftCurrentSelectionSet variableValues fuel
        targetParent leftProbeField rightProbeField leftParentType
        leftSourceRuntimeType targetLeftArguments targetRightArguments
        leftRuntime rightRuntime FieldPairProbeTag.left left hleftChildren
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
      executeField_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_field_ok_of_field_children
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet rightCurrentSelectionSet variableValues fuel
        targetParent leftProbeField rightProbeField rightParentType
        rightSourceRuntimeType targetLeftArguments targetRightArguments
        leftRuntime rightRuntime FieldPairProbeTag.right right
        hrightChildren
  exact
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_child_field_pair_of_field_ok
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet leftCurrentSelectionSet
      rightCurrentSelectionSet variableValues fuel targetParent
      leftProbeField rightProbeField leftParentType rightParentType
      leftSourceRuntimeType rightSourceRuntimeType targetLeftArguments
      targetRightArguments leftRuntime rightRuntime hleftFree hrightFree
      hleftNormal hrightNormal hleftObject hrightObject hleftMem hrightMem
      hleftLookup hrightLookup hleftRuntime hrightRuntime hleftInclude
      hrightInclude hleftFuel hrightFuel hleftChildResponse
      hrightChildResponse hchildNot hleftFieldOk hrightFieldOk

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_child_field_pair_of_field_children_fuels
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (variableValues : Execution.VariableValues) (leftFuel rightFuel : Nat)
    (targetParent leftProbeField
      rightProbeField leftParentType rightParentType
      leftSourceRuntimeType rightSourceRuntimeType
      : Name)
    (targetLeftArguments targetRightArguments : List Argument)
    (leftRuntime rightRuntime : Name) {left right : List Selection}
    {responseName leftFieldName rightFieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {leftFieldDefinition rightFieldDefinition : FieldDefinition}
    {leftChildRuntime rightChildRuntime : Name}
    {leftChildFields rightChildFields : List (Name × Execution.ResponseValue)}
    {leftChildErrors rightChildErrors : Nat}
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
      -> ((objectTypeNameBool schema leftFieldDefinition.outputType.namedType = true
            ∧ leftChildRuntime = leftFieldDefinition.outputType.namedType)
          ∨ ((TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool
                  schema
                = true
              ∧ objectTypeNameBool schema leftFieldDefinition.outputType.namedType = false
              ∧ abstractRuntimeForFieldHeadDeep? schema leftParentType
                  leftFieldName leftArguments leftParentType
                  leftCurrentSelectionSet
                = some leftChildRuntime))
      -> ((objectTypeNameBool schema rightFieldDefinition.outputType.namedType = true
            ∧ rightChildRuntime = rightFieldDefinition.outputType.namedType)
          ∨ ((TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool
                  schema
                = true
              ∧ objectTypeNameBool schema rightFieldDefinition.outputType.namedType
                = false
              ∧ abstractRuntimeForFieldHeadDeep? schema rightParentType
                  rightFieldName rightArguments rightParentType
                  rightCurrentSelectionSet
                = some rightChildRuntime))
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
              (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet targetParent leftProbeField
                rightProbeField targetLeftArguments targetRightArguments
                leftRuntime rightRuntime)
              targetParent leftProbeField rightProbeField targetLeftArguments
              targetRightArguments)
            variableValues
            (leftFuel - leafProbeFuel leftFieldDefinition.outputType)
            leftChildRuntime
            (projectionTargetResolverValue
              (.object leftChildRuntime
                (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                  (fieldPairPathLocalNextSelectionSet schema leftParentType
                    leftChildRuntime leftFieldName leftArguments
                    leftCurrentSelectionSet))))
            leftChildSelectionSet
          = ({
                data := Execution.ResponseValue.object leftChildFields,
                errors := leftChildErrors
              }
              : Execution.Response)
      -> Execution.executeSelectionSetAsResponse schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet targetParent leftProbeField
                rightProbeField targetLeftArguments targetRightArguments
                leftRuntime rightRuntime)
              targetParent leftProbeField rightProbeField targetLeftArguments
              targetRightArguments)
            variableValues
            (rightFuel - leafProbeFuel rightFieldDefinition.outputType)
            rightChildRuntime
            (projectionTargetResolverValue
              (.object rightChildRuntime
                (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                  (fieldPairPathLocalNextSelectionSet schema rightParentType
                    rightChildRuntime rightFieldName rightArguments
                    rightCurrentSelectionSet))))
            rightChildSelectionSet
          = ({
                data := Execution.ResponseValue.object rightChildFields,
                errors := rightChildErrors
              }
              : Execution.Response)
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.ResponseValue.object leftChildFields)
            (Execution.ResponseValue.object rightChildFields)
      -> PathLocalSelectionSetFieldChildrenReady schema rootSelectionSet
          leftInitialSelectionSet rightInitialSelectionSet variableValues
          leftFuel targetParent leftProbeField rightProbeField leftParentType
          targetLeftArguments targetRightArguments leftRuntime rightRuntime
          FieldPairProbeTag.left leftCurrentSelectionSet left
      -> PathLocalSelectionSetFieldChildrenReady schema rootSelectionSet
          leftInitialSelectionSet rightInitialSelectionSet variableValues
          rightFuel targetParent leftProbeField rightProbeField rightParentType
          targetLeftArguments targetRightArguments leftRuntime rightRuntime
          FieldPairProbeTag.right rightCurrentSelectionSet right
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet targetParent leftProbeField
                  rightProbeField targetLeftArguments targetRightArguments
                  leftRuntime rightRuntime)
                targetParent leftProbeField rightProbeField targetLeftArguments
                targetRightArguments)
              variableValues (leftFuel + 1) leftParentType
              (projectionTargetResolverValue
                (.object leftSourceRuntimeType
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                    leftCurrentSelectionSet)))
              left).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet targetParent leftProbeField
                  rightProbeField targetLeftArguments targetRightArguments
                  leftRuntime rightRuntime)
                targetParent leftProbeField rightProbeField targetLeftArguments
                targetRightArguments)
              variableValues (rightFuel + 1) rightParentType
              (projectionTargetResolverValue
                (.object rightSourceRuntimeType
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                    rightCurrentSelectionSet)))
              right).data := by
  intro hleftFree hrightFree hleftNormal hrightNormal hleftObject
    hrightObject hleftMem hrightMem hleftLookup hrightLookup hleftRuntime
    hrightRuntime hleftInclude hrightInclude hleftFuel hrightFuel
    hleftChildResponse hrightChildResponse hchildNot hleftChildren
    hrightChildren
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet
      (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
        rightInitialSelectionSet targetParent leftProbeField rightProbeField
        targetLeftArguments targetRightArguments leftRuntime rightRuntime)
      targetParent leftProbeField rightProbeField targetLeftArguments
      targetRightArguments
  let leftSource :=
    projectionTargetResolverValue
      (.object leftSourceRuntimeType
        (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
          leftCurrentSelectionSet))
  let rightSource :=
    projectionTargetResolverValue
      (.object rightSourceRuntimeType
        (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
          rightCurrentSelectionSet))
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
      executeField_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_field_ok_of_field_children
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftCurrentSelectionSet variableValues
        leftFuel targetParent leftProbeField rightProbeField
        leftParentType leftSourceRuntimeType targetLeftArguments
        targetRightArguments leftRuntime rightRuntime FieldPairProbeTag.left
        left hleftChildren
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
      executeField_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_field_ok_of_field_children
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet rightCurrentSelectionSet variableValues
        rightFuel targetParent leftProbeField rightProbeField
        rightParentType rightSourceRuntimeType targetLeftArguments
        targetRightArguments leftRuntime rightRuntime FieldPairProbeTag.right
        right hrightChildren
  exact
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_child_field_pair_of_field_ok_fuels
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet leftCurrentSelectionSet
      rightCurrentSelectionSet variableValues leftFuel rightFuel
      targetParent leftProbeField rightProbeField leftParentType
      rightParentType leftSourceRuntimeType rightSourceRuntimeType
      targetLeftArguments targetRightArguments leftRuntime rightRuntime
      hleftFree hrightFree hleftNormal hrightNormal hleftObject
      hrightObject hleftMem hrightMem hleftLookup hrightLookup
      hleftRuntime hrightRuntime hleftInclude hrightInclude hleftFuel
      hrightFuel hleftChildResponse hrightChildResponse hchildNot
      hleftFieldOk hrightFieldOk

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_child_field_pair_of_valid_normal_support_context_fuel_ge
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftProbeField rightProbeField leftParentType rightParentType : Name)
    (targetLeftArguments targetRightArguments : List Argument)
    (leftRuntime rightRuntime : Name) {left right : List Selection}
    {responseName leftFieldName rightFieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {leftFieldDefinition rightFieldDefinition : FieldDefinition}
    {leftChildRuntime rightChildRuntime : Name}
    {leftChildFields rightChildFields : List (Name × Execution.ResponseValue)}
    {leftChildErrors rightChildErrors : Nat}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
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
      -> PathLocalSupportValidNormal schema leftParentType leftCurrentSelectionSet
      -> PathLocalSupportValidNormal schema rightParentType rightCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext left leftCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext right rightCurrentSelectionSet
      -> Selection.field responseName leftFieldName leftArguments
            leftDirectives leftChildSelectionSet
          ∈ left
      -> Selection.field responseName rightFieldName rightArguments
            rightDirectives rightChildSelectionSet
          ∈ right
      -> schema.lookupField leftParentType leftFieldName = some leftFieldDefinition
      -> schema.lookupField rightParentType rightFieldName = some rightFieldDefinition
      -> ((objectTypeNameBool schema leftFieldDefinition.outputType.namedType = true
            ∧ leftChildRuntime = leftFieldDefinition.outputType.namedType)
          ∨ ((TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool
                  schema
                = true
              ∧ objectTypeNameBool schema leftFieldDefinition.outputType.namedType = false
              ∧ abstractRuntimeForFieldHeadDeep? schema leftParentType
                  leftFieldName leftArguments leftParentType
                  leftCurrentSelectionSet
                = some leftChildRuntime))
      -> ((objectTypeNameBool schema rightFieldDefinition.outputType.namedType = true
            ∧ rightChildRuntime = rightFieldDefinition.outputType.namedType)
          ∨ ((TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool
                  schema
                = true
              ∧ objectTypeNameBool schema rightFieldDefinition.outputType.namedType
                = false
              ∧ abstractRuntimeForFieldHeadDeep? schema rightParentType
                  rightFieldName rightArguments rightParentType
                  rightCurrentSelectionSet
                = some rightChildRuntime))
      -> schema.typeIncludesObjectBool leftFieldDefinition.outputType.namedType
            leftChildRuntime
          = true
      -> schema.typeIncludesObjectBool rightFieldDefinition.outputType.namedType
            rightChildRuntime
          = true
      -> Execution.executeSelectionSetAsResponse schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet targetParent leftProbeField
                rightProbeField targetLeftArguments targetRightArguments
                leftRuntime rightRuntime)
              targetParent leftProbeField rightProbeField targetLeftArguments
              targetRightArguments)
            variableValues
            (fuel - leafProbeFuel leftFieldDefinition.outputType)
            leftChildRuntime
            (projectionTargetResolverValue
              (.object leftChildRuntime
                (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                  (fieldPairPathLocalNextSelectionSet schema leftParentType
                    leftChildRuntime leftFieldName leftArguments
                    leftCurrentSelectionSet))))
            leftChildSelectionSet
          = ({
                data := Execution.ResponseValue.object leftChildFields,
                errors := leftChildErrors
              }
              : Execution.Response)
      -> Execution.executeSelectionSetAsResponse schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet targetParent leftProbeField
                rightProbeField targetLeftArguments targetRightArguments
                leftRuntime rightRuntime)
              targetParent leftProbeField rightProbeField targetLeftArguments
              targetRightArguments)
            variableValues
            (fuel - leafProbeFuel rightFieldDefinition.outputType)
            rightChildRuntime
            (projectionTargetResolverValue
              (.object rightChildRuntime
                (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                  (fieldPairPathLocalNextSelectionSet schema rightParentType
                    rightChildRuntime rightFieldName rightArguments
                    rightCurrentSelectionSet))))
            rightChildSelectionSet
          = ({
                data := Execution.ResponseValue.object rightChildFields,
                errors := rightChildErrors
              }
              : Execution.Response)
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.ResponseValue.object leftChildFields)
            (Execution.ResponseValue.object rightChildFields)
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet targetParent leftProbeField
                  rightProbeField targetLeftArguments targetRightArguments
                  leftRuntime rightRuntime)
                targetParent leftProbeField rightProbeField targetLeftArguments
                targetRightArguments)
              variableValues (fuel + 1) leftParentType
              (projectionTargetResolverValue
                (.object leftParentType
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                    leftCurrentSelectionSet)))
              left).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet targetParent leftProbeField
                  rightProbeField targetLeftArguments targetRightArguments
                  leftRuntime rightRuntime)
                targetParent leftProbeField rightProbeField targetLeftArguments
                targetRightArguments)
              variableValues (fuel + 1) rightParentType
              (projectionTargetResolverValue
                (.object rightParentType
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                    rightCurrentSelectionSet)))
              right).data := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hleftObject hrightObject hleftFuel hrightFuel hleftSupport
    hrightSupport hleftContext hrightContext hleftMem hrightMem hleftLookup
    hrightLookup hleftRuntime hrightRuntime hleftInclude hrightInclude
    hleftChildResponse hrightChildResponse hchildNot
  have hleftChildren :
      PathLocalSelectionSetFieldChildrenReady schema rootSelectionSet
        leftInitialSelectionSet rightInitialSelectionSet variableValues fuel
        targetParent leftProbeField rightProbeField leftParentType
        targetLeftArguments targetRightArguments leftRuntime rightRuntime
        FieldPairProbeTag.left leftCurrentSelectionSet left :=
    pathLocalSelectionSetFieldChildrenReady_of_valid_normal_support_context_fuel_ge_size
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet variableValues hschema
      (SelectionSet.size left + 1) leftParentType leftVariableDefinitions
      left fuel targetParent leftProbeField rightProbeField
      targetLeftArguments targetRightArguments leftRuntime rightRuntime
      FieldPairProbeTag.left leftCurrentSelectionSet (by omega) hleftFuel
      hleftValid hleftFree hleftNormal hleftObject hleftSupport
      hleftContext
  have hrightChildren :
      PathLocalSelectionSetFieldChildrenReady schema rootSelectionSet
        leftInitialSelectionSet rightInitialSelectionSet variableValues fuel
        targetParent leftProbeField rightProbeField rightParentType
        targetLeftArguments targetRightArguments leftRuntime rightRuntime
        FieldPairProbeTag.right rightCurrentSelectionSet right :=
    pathLocalSelectionSetFieldChildrenReady_of_valid_normal_support_context_fuel_ge_size
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet variableValues hschema
      (SelectionSet.size right + 1) rightParentType
      rightVariableDefinitions right fuel targetParent leftProbeField
      rightProbeField targetLeftArguments targetRightArguments leftRuntime
      rightRuntime FieldPairProbeTag.right rightCurrentSelectionSet
      (by omega) hrightFuel hrightValid hrightFree hrightNormal
      hrightObject hrightSupport hrightContext
  exact
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_child_field_pair_of_field_children
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet leftCurrentSelectionSet
      rightCurrentSelectionSet variableValues fuel targetParent
      leftProbeField rightProbeField leftParentType rightParentType
      leftParentType rightParentType targetLeftArguments
      targetRightArguments leftRuntime rightRuntime hleftFree hrightFree
      hleftNormal hrightNormal hleftObject hrightObject hleftMem hrightMem
      hleftLookup hrightLookup hleftRuntime hrightRuntime hleftInclude
      hrightInclude
      (by
        have hlocal :=
          leafProbeFuel_le_selectionSetDeepProbeFuel_of_field_mem schema
            leftParentType (selectionSet := left)
            (responseName := responseName) (fieldName := leftFieldName)
            (arguments := leftArguments) (directives := leftDirectives)
            (childSelectionSet := leftChildSelectionSet)
            (fieldDefinition := leftFieldDefinition) hleftMem hleftLookup
        omega)
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
      hleftChildResponse hrightChildResponse hchildNot hleftChildren
      hrightChildren

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_child_field_pair_of_valid_normal_support_context_fuel_ge_fuels
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (variableValues : Execution.VariableValues) (leftFuel rightFuel : Nat)
    (targetParent leftProbeField rightProbeField leftParentType rightParentType : Name)
    (targetLeftArguments targetRightArguments : List Argument)
    (leftRuntime rightRuntime : Name) {left right : List Selection}
    {responseName leftFieldName rightFieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {leftFieldDefinition rightFieldDefinition : FieldDefinition}
    {leftChildRuntime rightChildRuntime : Name}
    {leftChildFields rightChildFields : List (Name × Execution.ResponseValue)}
    {leftChildErrors rightChildErrors : Nat}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
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
      -> Selection.field responseName leftFieldName leftArguments
            leftDirectives leftChildSelectionSet
          ∈ left
      -> Selection.field responseName rightFieldName rightArguments
            rightDirectives rightChildSelectionSet
          ∈ right
      -> schema.lookupField leftParentType leftFieldName = some leftFieldDefinition
      -> schema.lookupField rightParentType rightFieldName = some rightFieldDefinition
      -> ((objectTypeNameBool schema leftFieldDefinition.outputType.namedType = true
            ∧ leftChildRuntime = leftFieldDefinition.outputType.namedType)
          ∨ ((TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool
                  schema
                = true
              ∧ objectTypeNameBool schema leftFieldDefinition.outputType.namedType = false
              ∧ abstractRuntimeForFieldHeadDeep? schema leftParentType
                  leftFieldName leftArguments leftParentType
                  leftCurrentSelectionSet
                = some leftChildRuntime))
      -> ((objectTypeNameBool schema rightFieldDefinition.outputType.namedType = true
            ∧ rightChildRuntime = rightFieldDefinition.outputType.namedType)
          ∨ ((TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool
                  schema
                = true
              ∧ objectTypeNameBool schema rightFieldDefinition.outputType.namedType
                = false
              ∧ abstractRuntimeForFieldHeadDeep? schema rightParentType
                  rightFieldName rightArguments rightParentType
                  rightCurrentSelectionSet
                = some rightChildRuntime))
      -> schema.typeIncludesObjectBool leftFieldDefinition.outputType.namedType
            leftChildRuntime
          = true
      -> schema.typeIncludesObjectBool rightFieldDefinition.outputType.namedType
            rightChildRuntime
          = true
      -> Execution.executeSelectionSetAsResponse schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet targetParent leftProbeField
                rightProbeField targetLeftArguments targetRightArguments
                leftRuntime rightRuntime)
              targetParent leftProbeField rightProbeField targetLeftArguments
              targetRightArguments)
            variableValues
            (leftFuel - leafProbeFuel leftFieldDefinition.outputType)
            leftChildRuntime
            (projectionTargetResolverValue
              (.object leftChildRuntime
                (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                  (fieldPairPathLocalNextSelectionSet schema leftParentType
                    leftChildRuntime leftFieldName leftArguments
                    leftCurrentSelectionSet))))
            leftChildSelectionSet
          = ({
                data := Execution.ResponseValue.object leftChildFields,
                errors := leftChildErrors
              }
              : Execution.Response)
      -> Execution.executeSelectionSetAsResponse schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet targetParent leftProbeField
                rightProbeField targetLeftArguments targetRightArguments
                leftRuntime rightRuntime)
              targetParent leftProbeField rightProbeField targetLeftArguments
              targetRightArguments)
            variableValues
            (rightFuel - leafProbeFuel rightFieldDefinition.outputType)
            rightChildRuntime
            (projectionTargetResolverValue
              (.object rightChildRuntime
                (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                  (fieldPairPathLocalNextSelectionSet schema rightParentType
                    rightChildRuntime rightFieldName rightArguments
                    rightCurrentSelectionSet))))
            rightChildSelectionSet
          = ({
                data := Execution.ResponseValue.object rightChildFields,
                errors := rightChildErrors
              }
              : Execution.Response)
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.ResponseValue.object leftChildFields)
            (Execution.ResponseValue.object rightChildFields)
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet targetParent leftProbeField
                  rightProbeField targetLeftArguments targetRightArguments
                  leftRuntime rightRuntime)
                targetParent leftProbeField rightProbeField targetLeftArguments
                targetRightArguments)
              variableValues (leftFuel + 1) leftParentType
              (projectionTargetResolverValue
                (.object leftParentType
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                    leftCurrentSelectionSet)))
              left).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet targetParent leftProbeField
                  rightProbeField targetLeftArguments targetRightArguments
                  leftRuntime rightRuntime)
                targetParent leftProbeField rightProbeField targetLeftArguments
                targetRightArguments)
              variableValues (rightFuel + 1) rightParentType
              (projectionTargetResolverValue
                (.object rightParentType
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                    rightCurrentSelectionSet)))
              right).data := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hleftObject hrightObject hleftFuel hrightFuel hleftSupport
    hrightSupport hleftContext hrightContext hleftMem hrightMem hleftLookup
    hrightLookup hleftRuntime hrightRuntime hleftInclude hrightInclude
    hleftChildResponse hrightChildResponse hchildNot
  have hleftChildren :
      PathLocalSelectionSetFieldChildrenReady schema rootSelectionSet
        leftInitialSelectionSet rightInitialSelectionSet variableValues
        leftFuel targetParent leftProbeField rightProbeField leftParentType
        targetLeftArguments targetRightArguments leftRuntime rightRuntime
        FieldPairProbeTag.left leftCurrentSelectionSet left :=
    pathLocalSelectionSetFieldChildrenReady_of_valid_normal_support_context_fuel_ge_size
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet variableValues hschema
      (SelectionSet.size left + 1) leftParentType leftVariableDefinitions
      left leftFuel targetParent leftProbeField rightProbeField
      targetLeftArguments targetRightArguments leftRuntime rightRuntime
      FieldPairProbeTag.left leftCurrentSelectionSet (by omega) hleftFuel
      hleftValid hleftFree hleftNormal hleftObject hleftSupport
      hleftContext
  have hrightChildren :
      PathLocalSelectionSetFieldChildrenReady schema rootSelectionSet
        leftInitialSelectionSet rightInitialSelectionSet variableValues
        rightFuel targetParent leftProbeField rightProbeField rightParentType
        targetLeftArguments targetRightArguments leftRuntime rightRuntime
        FieldPairProbeTag.right rightCurrentSelectionSet right :=
    pathLocalSelectionSetFieldChildrenReady_of_valid_normal_support_context_fuel_ge_size
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet variableValues hschema
      (SelectionSet.size right + 1) rightParentType
      rightVariableDefinitions right rightFuel targetParent leftProbeField
      rightProbeField targetLeftArguments targetRightArguments leftRuntime
      rightRuntime FieldPairProbeTag.right rightCurrentSelectionSet
      (by omega) hrightFuel hrightValid hrightFree hrightNormal
      hrightObject hrightSupport hrightContext
  exact
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_child_field_pair_of_field_children_fuels
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet leftCurrentSelectionSet
      rightCurrentSelectionSet variableValues leftFuel rightFuel
      targetParent leftProbeField rightProbeField leftParentType
      rightParentType leftParentType rightParentType targetLeftArguments
      targetRightArguments leftRuntime rightRuntime hleftFree hrightFree
      hleftNormal hrightNormal hleftObject hrightObject hleftMem hrightMem
      hleftLookup hrightLookup hleftRuntime hrightRuntime hleftInclude
      hrightInclude
      (by
        have hlocal :=
          leafProbeFuel_le_selectionSetDeepProbeFuel_of_field_mem schema
            leftParentType (selectionSet := left)
            (responseName := responseName) (fieldName := leftFieldName)
            (arguments := leftArguments) (directives := leftDirectives)
            (childSelectionSet := leftChildSelectionSet)
            (fieldDefinition := leftFieldDefinition) hleftMem hleftLookup
        omega)
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
      hleftChildResponse hrightChildResponse hchildNot hleftChildren
      hrightChildren

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_left_object_child_of_valid_normal_support_context_fuel_ge
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftProbeField rightProbeField leftParentType rightParentType : Name)
    (targetLeftArguments targetRightArguments : List Argument)
    (leftRuntime rightRuntime : Name) {left right : List Selection}
    {responseName leftFieldName : Name} {leftArguments : List Argument}
    {leftDirectives : List DirectiveApplication} {leftChildSelectionSet : List Selection}
    {leftFieldDefinition : FieldDefinition}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
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
      -> PathLocalSupportValidNormal schema leftParentType leftCurrentSelectionSet
      -> PathLocalSupportValidNormal schema rightParentType rightCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext left leftCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext right rightCurrentSelectionSet
      -> Selection.field responseName leftFieldName leftArguments
            leftDirectives leftChildSelectionSet
          ∈ left
      -> schema.lookupField leftParentType leftFieldName = some leftFieldDefinition
      -> (TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> (∀ {leftChildRuntime rightFieldName : Name}
            {rightArguments : List Argument}
            {rightDirectives : List DirectiveApplication}
            {rightChildSelectionSet : List Selection}
            {rightFieldDefinition : FieldDefinition}
            {rightChildRuntime : Name},
            ((objectTypeNameBool schema leftFieldDefinition.outputType.namedType = true
                ∧ leftChildRuntime = leftFieldDefinition.outputType.namedType)
              ∨ ((TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool
                      schema
                    = true
                  ∧ objectTypeNameBool schema leftFieldDefinition.outputType.namedType
                    = false
                  ∧ abstractRuntimeForFieldHeadDeep? schema leftParentType
                      leftFieldName leftArguments leftParentType
                      leftCurrentSelectionSet
                    = some leftChildRuntime))
            -> schema.typeIncludesObjectBool
                  leftFieldDefinition.outputType.namedType leftChildRuntime
                = true
            -> Selection.field responseName rightFieldName rightArguments
                  rightDirectives rightChildSelectionSet
                ∈ right
            -> schema.lookupField rightParentType rightFieldName
                = some rightFieldDefinition
            -> (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool
                  schema
                = true
            -> ((objectTypeNameBool schema rightFieldDefinition.outputType.namedType
                    = true
                  ∧ rightChildRuntime = rightFieldDefinition.outputType.namedType)
                ∨ ((TypeRef.named
                        rightFieldDefinition.outputType.namedType).isCompositeBool
                        schema
                      = true
                    ∧ objectTypeNameBool schema rightFieldDefinition.outputType.namedType
                      = false
                    ∧ abstractRuntimeForFieldHeadDeep? schema rightParentType
                        rightFieldName rightArguments rightParentType
                        rightCurrentSelectionSet
                      = some rightChildRuntime))
            -> schema.typeIncludesObjectBool
                  rightFieldDefinition.outputType.namedType rightChildRuntime
                = true
            -> ¬ Execution.ResponseValue.semanticEquivalent
                  (Execution.executeSelectionSetAsResponse schema
                    (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                      (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                        rightInitialSelectionSet targetParent leftProbeField
                        rightProbeField targetLeftArguments targetRightArguments
                        leftRuntime rightRuntime)
                      targetParent leftProbeField rightProbeField targetLeftArguments
                      targetRightArguments)
                    variableValues
                    (fuel - leafProbeFuel leftFieldDefinition.outputType)
                    leftChildRuntime
                    (projectionTargetResolverValue
                      (.object leftChildRuntime
                        (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                          (fieldPairPathLocalNextSelectionSet schema leftParentType
                            leftChildRuntime leftFieldName leftArguments
                            leftCurrentSelectionSet))))
                    leftChildSelectionSet).data
                  (Execution.executeSelectionSetAsResponse schema
                    (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                      (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                        rightInitialSelectionSet targetParent leftProbeField
                        rightProbeField targetLeftArguments targetRightArguments
                        leftRuntime rightRuntime)
                      targetParent leftProbeField rightProbeField targetLeftArguments
                      targetRightArguments)
                    variableValues
                    (fuel - leafProbeFuel rightFieldDefinition.outputType)
                    rightChildRuntime
                    (projectionTargetResolverValue
                      (.object rightChildRuntime
                        (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                          (fieldPairPathLocalNextSelectionSet schema rightParentType
                            rightChildRuntime rightFieldName rightArguments
                            rightCurrentSelectionSet))))
                    rightChildSelectionSet).data)
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet targetParent leftProbeField
                  rightProbeField targetLeftArguments targetRightArguments
                  leftRuntime rightRuntime)
                targetParent leftProbeField rightProbeField targetLeftArguments
                targetRightArguments)
              variableValues (fuel + 1) leftParentType
              (projectionTargetResolverValue
                (.object leftParentType
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                    leftCurrentSelectionSet)))
              left).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet targetParent leftProbeField
                  rightProbeField targetLeftArguments targetRightArguments
                  leftRuntime rightRuntime)
                targetParent leftProbeField rightProbeField targetLeftArguments
                targetRightArguments)
              variableValues (fuel + 1) rightParentType
              (projectionTargetResolverValue
                (.object rightParentType
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                    rightCurrentSelectionSet)))
              right).data := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hleftObject hrightObject hleftFuel hrightFuel hleftSupport
    hrightSupport hleftContext hrightContext hleftMem hleftLookup
    hleftComposite hchildDataNot
  rcases
      pathLocalCompositeFieldRuntime_of_valid_normal_support_context
        hleftValid hleftNormal hleftSupport hleftContext hleftMem
        hleftLookup hleftComposite with
    ⟨leftChildRuntime, hleftRuntime, hleftInclude⟩
  by_cases hrightResponseName :
      responseName ∈ right.filterMap Selection.responseName?
  · rcases
        selectionSetNormal_field_mem_of_responseName_mem hrightNormal
          hrightObject hrightResponseName with
      ⟨rightFieldName, rightArguments, rightDirectives,
        rightChildSelectionSet, hrightMem⟩
    rcases selectionSetValid_field_lookup_of_mem hrightValid hrightMem with
      ⟨rightFieldDefinition, hrightLookup, _hrightArguments,
        _hrightFieldValid⟩
    by_cases hrightLeaf :
        (TypeRef.named
            rightFieldDefinition.outputType.namedType).isCompositeBool
          schema = false
    · exact
        responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_left_composite_right_leaf_field_pair_of_valid_normal_support_context_fuel_ge
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet leftCurrentSelectionSet
          rightCurrentSelectionSet variableValues fuel targetParent
          leftProbeField rightProbeField leftParentType rightParentType
          targetLeftArguments targetRightArguments leftRuntime rightRuntime
          hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
          hrightNormal hleftObject hrightObject hleftFuel hrightFuel
          hleftSupport hrightSupport hleftContext hrightContext hleftMem
          hrightMem hleftLookup hrightLookup hleftComposite hrightLeaf
    · have hrightComposite :
          (TypeRef.named
              rightFieldDefinition.outputType.namedType).isCompositeBool
            schema = true := by
        cases h :
            (TypeRef.named
                rightFieldDefinition.outputType.namedType).isCompositeBool
              schema
        · exact False.elim (hrightLeaf h)
        · rfl
      rcases
          pathLocalCompositeFieldRuntime_of_valid_normal_support_context
            hrightValid hrightNormal hrightSupport hrightContext hrightMem
            hrightLookup hrightComposite with
        ⟨rightChildRuntime, hrightRuntime, hrightInclude⟩
      have hchildNotData :
          ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema
                  leftInitialSelectionSet rightInitialSelectionSet
                  targetParent leftProbeField rightProbeField
                  targetLeftArguments targetRightArguments leftRuntime
                  rightRuntime)
                targetParent leftProbeField rightProbeField
                targetLeftArguments targetRightArguments)
              variableValues
              (fuel - leafProbeFuel leftFieldDefinition.outputType)
              leftChildRuntime
              (projectionTargetResolverValue
                (.object leftChildRuntime
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                    (fieldPairPathLocalNextSelectionSet schema
                      leftParentType leftChildRuntime leftFieldName
                      leftArguments leftCurrentSelectionSet))))
              leftChildSelectionSet).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema
                  leftInitialSelectionSet rightInitialSelectionSet
                  targetParent leftProbeField rightProbeField
                  targetLeftArguments targetRightArguments leftRuntime
                  rightRuntime)
                targetParent leftProbeField rightProbeField
                targetLeftArguments targetRightArguments)
              variableValues
              (fuel - leafProbeFuel rightFieldDefinition.outputType)
              rightChildRuntime
              (projectionTargetResolverValue
                (.object rightChildRuntime
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                    (fieldPairPathLocalNextSelectionSet schema
                      rightParentType rightChildRuntime rightFieldName
                      rightArguments rightCurrentSelectionSet))))
              rightChildSelectionSet).data :=
        hchildDataNot hleftRuntime hleftInclude hrightMem hrightLookup
          hrightComposite hrightRuntime hrightInclude
      rcases
          executeSelectionSetAsResponse_fieldPairOrDeepSuccess_pathLocalProbe_target_child_of_valid_normal_context_fuel_ge
            (schema := schema) (rootSelectionSet := rootSelectionSet)
            (leftInitialSelectionSet := leftInitialSelectionSet)
            (rightInitialSelectionSet := rightInitialSelectionSet)
            (currentSelectionSet := leftCurrentSelectionSet)
            (variableValues := variableValues)
            (variableDefinitions := leftVariableDefinitions)
            (parentType := leftParentType)
            (runtimeType := leftChildRuntime)
            (targetParent := targetParent)
            (leftField := leftProbeField) (rightField := rightProbeField)
            (responseName := responseName) (fieldName := leftFieldName)
            (targetLeftArguments := targetLeftArguments)
            (targetRightArguments := targetRightArguments)
            (targetArguments := leftArguments)
            (arguments := leftArguments) (directives := leftDirectives)
            (leftRuntime := leftRuntime) (rightRuntime := rightRuntime)
            (selectionSet := left)
            (childSelectionSet := leftChildSelectionSet)
            (fieldDefinition := leftFieldDefinition) (fuel := fuel)
            (tag := FieldPairProbeTag.left)
            hschema hleftValid hleftFree hleftNormal hleftObject hleftFuel
            hleftSupport hleftContext hleftMem hleftLookup hleftComposite
            hleftInclude
            (argumentsEquivalent_refl_forSyntaxDiff leftArguments) with
        ⟨leftChildFields, leftChildErrors, hleftChildResponse⟩
      rcases
          executeSelectionSetAsResponse_fieldPairOrDeepSuccess_pathLocalProbe_target_child_of_valid_normal_context_fuel_ge
            (schema := schema) (rootSelectionSet := rootSelectionSet)
            (leftInitialSelectionSet := leftInitialSelectionSet)
            (rightInitialSelectionSet := rightInitialSelectionSet)
            (currentSelectionSet := rightCurrentSelectionSet)
            (variableValues := variableValues)
            (variableDefinitions := rightVariableDefinitions)
            (parentType := rightParentType)
            (runtimeType := rightChildRuntime)
            (targetParent := targetParent)
            (leftField := leftProbeField) (rightField := rightProbeField)
            (responseName := responseName) (fieldName := rightFieldName)
            (targetLeftArguments := targetLeftArguments)
            (targetRightArguments := targetRightArguments)
            (targetArguments := rightArguments)
            (arguments := rightArguments) (directives := rightDirectives)
            (leftRuntime := leftRuntime) (rightRuntime := rightRuntime)
            (selectionSet := right)
            (childSelectionSet := rightChildSelectionSet)
            (fieldDefinition := rightFieldDefinition) (fuel := fuel)
            (tag := FieldPairProbeTag.right)
            hschema hrightValid hrightFree hrightNormal hrightObject
            hrightFuel hrightSupport hrightContext hrightMem hrightLookup
            hrightComposite hrightInclude
            (argumentsEquivalent_refl_forSyntaxDiff rightArguments) with
        ⟨rightChildFields, rightChildErrors, hrightChildResponse⟩
      have hchildObjectNot :
          ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.ResponseValue.object leftChildFields)
            (Execution.ResponseValue.object rightChildFields) := by
        intro hchildSemantic
        exact hchildNotData
          (by
            simpa [hleftChildResponse, hrightChildResponse] using
              hchildSemantic)
      exact
        responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_child_field_pair_of_valid_normal_support_context_fuel_ge
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet leftCurrentSelectionSet
          rightCurrentSelectionSet variableValues fuel targetParent
          leftProbeField rightProbeField leftParentType rightParentType
          targetLeftArguments targetRightArguments leftRuntime rightRuntime
          hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
          hrightNormal hleftObject hrightObject hleftFuel hrightFuel
          hleftSupport hrightSupport hleftContext hrightContext hleftMem
          hrightMem hleftLookup hrightLookup hleftRuntime hrightRuntime
          hleftInclude hrightInclude hleftChildResponse hrightChildResponse
          hchildObjectNot
  · exact
      responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_left_responseName_diff_of_valid_normal_support_context_fuel_ge
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftCurrentSelectionSet
        rightCurrentSelectionSet variableValues fuel targetParent
        leftProbeField rightProbeField leftParentType rightParentType
        targetLeftArguments targetRightArguments leftRuntime rightRuntime
        hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
        hrightNormal hleftObject hrightObject hleftFuel hrightFuel
        hleftSupport hrightSupport hleftContext hrightContext hleftMem
        hrightResponseName

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_left_object_child_of_valid_normal_support_context_fuel_ge_fuels
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (variableValues : Execution.VariableValues) (leftFuel rightFuel : Nat)
    (targetParent leftProbeField rightProbeField leftParentType rightParentType : Name)
    (targetLeftArguments targetRightArguments : List Argument)
    (leftRuntime rightRuntime : Name) {left right : List Selection}
    {responseName leftFieldName : Name} {leftArguments : List Argument}
    {leftDirectives : List DirectiveApplication} {leftChildSelectionSet : List Selection}
    {leftFieldDefinition : FieldDefinition}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
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
      -> Selection.field responseName leftFieldName leftArguments
            leftDirectives leftChildSelectionSet
          ∈ left
      -> schema.lookupField leftParentType leftFieldName = some leftFieldDefinition
      -> (TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> (∀ {leftChildRuntime rightFieldName : Name}
            {rightArguments : List Argument}
            {rightDirectives : List DirectiveApplication}
            {rightChildSelectionSet : List Selection}
            {rightFieldDefinition : FieldDefinition}
            {rightChildRuntime : Name},
            ((objectTypeNameBool schema leftFieldDefinition.outputType.namedType = true
                ∧ leftChildRuntime = leftFieldDefinition.outputType.namedType)
              ∨ ((TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool
                      schema
                    = true
                  ∧ objectTypeNameBool schema leftFieldDefinition.outputType.namedType
                    = false
                  ∧ abstractRuntimeForFieldHeadDeep? schema leftParentType
                      leftFieldName leftArguments leftParentType
                      leftCurrentSelectionSet
                    = some leftChildRuntime))
            -> schema.typeIncludesObjectBool
                  leftFieldDefinition.outputType.namedType leftChildRuntime
                = true
            -> Selection.field responseName rightFieldName rightArguments
                  rightDirectives rightChildSelectionSet
                ∈ right
            -> schema.lookupField rightParentType rightFieldName
                = some rightFieldDefinition
            -> (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool
                  schema
                = true
            -> ((objectTypeNameBool schema rightFieldDefinition.outputType.namedType
                    = true
                  ∧ rightChildRuntime = rightFieldDefinition.outputType.namedType)
                ∨ ((TypeRef.named
                        rightFieldDefinition.outputType.namedType).isCompositeBool
                        schema
                      = true
                    ∧ objectTypeNameBool schema rightFieldDefinition.outputType.namedType
                      = false
                    ∧ abstractRuntimeForFieldHeadDeep? schema rightParentType
                        rightFieldName rightArguments rightParentType
                        rightCurrentSelectionSet
                      = some rightChildRuntime))
            -> schema.typeIncludesObjectBool
                  rightFieldDefinition.outputType.namedType rightChildRuntime
                = true
            -> ¬ Execution.ResponseValue.semanticEquivalent
                  (Execution.executeSelectionSetAsResponse schema
                    (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                      (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                        rightInitialSelectionSet targetParent leftProbeField
                        rightProbeField targetLeftArguments targetRightArguments
                        leftRuntime rightRuntime)
                      targetParent leftProbeField rightProbeField targetLeftArguments
                      targetRightArguments)
                    variableValues
                    (leftFuel - leafProbeFuel leftFieldDefinition.outputType)
                    leftChildRuntime
                    (projectionTargetResolverValue
                      (.object leftChildRuntime
                        (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                          (fieldPairPathLocalNextSelectionSet schema leftParentType
                            leftChildRuntime leftFieldName leftArguments
                            leftCurrentSelectionSet))))
                    leftChildSelectionSet).data
                  (Execution.executeSelectionSetAsResponse schema
                    (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                      (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                        rightInitialSelectionSet targetParent leftProbeField
                        rightProbeField targetLeftArguments targetRightArguments
                        leftRuntime rightRuntime)
                      targetParent leftProbeField rightProbeField targetLeftArguments
                      targetRightArguments)
                    variableValues
                    (rightFuel - leafProbeFuel rightFieldDefinition.outputType)
                    rightChildRuntime
                    (projectionTargetResolverValue
                      (.object rightChildRuntime
                        (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                          (fieldPairPathLocalNextSelectionSet schema rightParentType
                            rightChildRuntime rightFieldName rightArguments
                            rightCurrentSelectionSet))))
                    rightChildSelectionSet).data)
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet targetParent leftProbeField
                  rightProbeField targetLeftArguments targetRightArguments
                  leftRuntime rightRuntime)
                targetParent leftProbeField rightProbeField targetLeftArguments
                targetRightArguments)
              variableValues (leftFuel + 1) leftParentType
              (projectionTargetResolverValue
                (.object leftParentType
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                    leftCurrentSelectionSet)))
              left).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet targetParent leftProbeField
                  rightProbeField targetLeftArguments targetRightArguments
                  leftRuntime rightRuntime)
                targetParent leftProbeField rightProbeField targetLeftArguments
                targetRightArguments)
              variableValues (rightFuel + 1) rightParentType
              (projectionTargetResolverValue
                (.object rightParentType
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                    rightCurrentSelectionSet)))
              right).data := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hleftObject hrightObject hleftFuel hrightFuel hleftSupport
    hrightSupport hleftContext hrightContext hleftMem hleftLookup
    hleftComposite hchildDataNot
  rcases
      pathLocalCompositeFieldRuntime_of_valid_normal_support_context
        hleftValid hleftNormal hleftSupport hleftContext hleftMem
        hleftLookup hleftComposite with
    ⟨leftChildRuntime, hleftRuntime, hleftInclude⟩
  by_cases hrightResponseName :
      responseName ∈ right.filterMap Selection.responseName?
  · rcases
        selectionSetNormal_field_mem_of_responseName_mem hrightNormal
          hrightObject hrightResponseName with
      ⟨rightFieldName, rightArguments, rightDirectives,
        rightChildSelectionSet, hrightMem⟩
    rcases selectionSetValid_field_lookup_of_mem hrightValid hrightMem with
      ⟨rightFieldDefinition, hrightLookup, _hrightArguments,
        _hrightFieldValid⟩
    by_cases hrightLeaf :
        (TypeRef.named
            rightFieldDefinition.outputType.namedType).isCompositeBool
          schema = false
    · exact
        responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_left_composite_right_leaf_field_pair_of_valid_normal_support_context_fuel_ge_fuels
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet leftCurrentSelectionSet
          rightCurrentSelectionSet variableValues leftFuel rightFuel
          targetParent leftProbeField rightProbeField leftParentType
          rightParentType targetLeftArguments targetRightArguments
          leftRuntime rightRuntime hschema hleftValid hrightValid
          hleftFree hrightFree hleftNormal hrightNormal hleftObject
          hrightObject hleftFuel hrightFuel hleftSupport hrightSupport
          hleftContext hrightContext hleftMem hrightMem hleftLookup
          hrightLookup hleftComposite hrightLeaf
    · have hrightComposite :
          (TypeRef.named
              rightFieldDefinition.outputType.namedType).isCompositeBool
            schema = true := by
        cases h :
            (TypeRef.named
                rightFieldDefinition.outputType.namedType).isCompositeBool
              schema
        · exact False.elim (hrightLeaf h)
        · rfl
      rcases
          pathLocalCompositeFieldRuntime_of_valid_normal_support_context
            hrightValid hrightNormal hrightSupport hrightContext hrightMem
            hrightLookup hrightComposite with
        ⟨rightChildRuntime, hrightRuntime, hrightInclude⟩
      have hchildNotData :
          ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema
                  leftInitialSelectionSet rightInitialSelectionSet
                  targetParent leftProbeField rightProbeField
                  targetLeftArguments targetRightArguments leftRuntime
                  rightRuntime)
                targetParent leftProbeField rightProbeField
                targetLeftArguments targetRightArguments)
              variableValues
              (leftFuel - leafProbeFuel leftFieldDefinition.outputType)
              leftChildRuntime
              (projectionTargetResolverValue
                (.object leftChildRuntime
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                    (fieldPairPathLocalNextSelectionSet schema
                      leftParentType leftChildRuntime leftFieldName
                      leftArguments leftCurrentSelectionSet))))
              leftChildSelectionSet).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema
                  leftInitialSelectionSet rightInitialSelectionSet
                  targetParent leftProbeField rightProbeField
                  targetLeftArguments targetRightArguments leftRuntime
                  rightRuntime)
                targetParent leftProbeField rightProbeField
                targetLeftArguments targetRightArguments)
              variableValues
              (rightFuel - leafProbeFuel rightFieldDefinition.outputType)
              rightChildRuntime
              (projectionTargetResolverValue
                (.object rightChildRuntime
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                    (fieldPairPathLocalNextSelectionSet schema
                      rightParentType rightChildRuntime rightFieldName
                      rightArguments rightCurrentSelectionSet))))
              rightChildSelectionSet).data :=
        hchildDataNot hleftRuntime hleftInclude hrightMem hrightLookup
          hrightComposite hrightRuntime hrightInclude
      rcases
          executeSelectionSetAsResponse_fieldPairOrDeepSuccess_pathLocalProbe_target_child_of_valid_normal_context_fuel_ge
            (schema := schema) (rootSelectionSet := rootSelectionSet)
            (leftInitialSelectionSet := leftInitialSelectionSet)
            (rightInitialSelectionSet := rightInitialSelectionSet)
            (currentSelectionSet := leftCurrentSelectionSet)
            (variableValues := variableValues)
            (variableDefinitions := leftVariableDefinitions)
            (parentType := leftParentType)
            (runtimeType := leftChildRuntime)
            (targetParent := targetParent)
            (leftField := leftProbeField) (rightField := rightProbeField)
            (responseName := responseName) (fieldName := leftFieldName)
            (targetLeftArguments := targetLeftArguments)
            (targetRightArguments := targetRightArguments)
            (targetArguments := leftArguments)
            (arguments := leftArguments) (directives := leftDirectives)
            (leftRuntime := leftRuntime) (rightRuntime := rightRuntime)
            (selectionSet := left)
            (childSelectionSet := leftChildSelectionSet)
            (fieldDefinition := leftFieldDefinition) (fuel := leftFuel)
            (tag := FieldPairProbeTag.left)
            hschema hleftValid hleftFree hleftNormal hleftObject hleftFuel
            hleftSupport hleftContext hleftMem hleftLookup hleftComposite
            hleftInclude
            (argumentsEquivalent_refl_forSyntaxDiff leftArguments) with
        ⟨leftChildFields, leftChildErrors, hleftChildResponse⟩
      rcases
          executeSelectionSetAsResponse_fieldPairOrDeepSuccess_pathLocalProbe_target_child_of_valid_normal_context_fuel_ge
            (schema := schema) (rootSelectionSet := rootSelectionSet)
            (leftInitialSelectionSet := leftInitialSelectionSet)
            (rightInitialSelectionSet := rightInitialSelectionSet)
            (currentSelectionSet := rightCurrentSelectionSet)
            (variableValues := variableValues)
            (variableDefinitions := rightVariableDefinitions)
            (parentType := rightParentType)
            (runtimeType := rightChildRuntime)
            (targetParent := targetParent)
            (leftField := leftProbeField) (rightField := rightProbeField)
            (responseName := responseName) (fieldName := rightFieldName)
            (targetLeftArguments := targetLeftArguments)
            (targetRightArguments := targetRightArguments)
            (targetArguments := rightArguments)
            (arguments := rightArguments) (directives := rightDirectives)
            (leftRuntime := leftRuntime) (rightRuntime := rightRuntime)
            (selectionSet := right)
            (childSelectionSet := rightChildSelectionSet)
            (fieldDefinition := rightFieldDefinition) (fuel := rightFuel)
            (tag := FieldPairProbeTag.right)
            hschema hrightValid hrightFree hrightNormal hrightObject
            hrightFuel hrightSupport hrightContext hrightMem hrightLookup
            hrightComposite hrightInclude
            (argumentsEquivalent_refl_forSyntaxDiff rightArguments) with
        ⟨rightChildFields, rightChildErrors, hrightChildResponse⟩
      have hchildObjectNot :
          ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.ResponseValue.object leftChildFields)
            (Execution.ResponseValue.object rightChildFields) := by
        intro hchildSemantic
        exact hchildNotData
          (by
            simpa [hleftChildResponse, hrightChildResponse] using
              hchildSemantic)
      exact
        responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_child_field_pair_of_valid_normal_support_context_fuel_ge_fuels
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet leftCurrentSelectionSet
          rightCurrentSelectionSet variableValues leftFuel rightFuel
          targetParent leftProbeField rightProbeField leftParentType
          rightParentType targetLeftArguments targetRightArguments
          leftRuntime rightRuntime hschema hleftValid hrightValid
          hleftFree hrightFree hleftNormal hrightNormal hleftObject
          hrightObject hleftFuel hrightFuel hleftSupport hrightSupport
          hleftContext hrightContext hleftMem hrightMem hleftLookup
          hrightLookup hleftRuntime hrightRuntime hleftInclude
          hrightInclude hleftChildResponse hrightChildResponse
          hchildObjectNot
  · exact
      responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_left_responseName_diff_of_valid_normal_support_context_fuel_ge_fuels
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftCurrentSelectionSet
        rightCurrentSelectionSet variableValues leftFuel rightFuel
        targetParent leftProbeField rightProbeField leftParentType
        rightParentType targetLeftArguments targetRightArguments
        leftRuntime rightRuntime hschema hleftValid hrightValid hleftFree
        hrightFree hleftNormal hrightNormal hleftObject hrightObject
        hleftFuel hrightFuel hleftSupport hrightSupport hleftContext
        hrightContext hleftMem hrightResponseName

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_right_object_child_of_valid_normal_support_context_fuel_ge
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftProbeField rightProbeField leftParentType rightParentType : Name)
    (targetLeftArguments targetRightArguments : List Argument)
    (leftRuntime rightRuntime : Name) {left right : List Selection}
    {responseName rightFieldName : Name} {rightArguments : List Argument}
    {rightDirectives : List DirectiveApplication}
    {rightChildSelectionSet : List Selection} {rightFieldDefinition : FieldDefinition}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
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
      -> PathLocalSupportValidNormal schema leftParentType leftCurrentSelectionSet
      -> PathLocalSupportValidNormal schema rightParentType rightCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext left leftCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext right rightCurrentSelectionSet
      -> Selection.field responseName rightFieldName rightArguments
            rightDirectives rightChildSelectionSet
          ∈ right
      -> schema.lookupField rightParentType rightFieldName = some rightFieldDefinition
      -> (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> (∀ {leftFieldName : Name}
            {leftArguments : List Argument}
            {leftDirectives : List DirectiveApplication}
            {leftChildSelectionSet : List Selection}
            {leftFieldDefinition : FieldDefinition}
            {leftChildRuntime rightChildRuntime : Name},
            Selection.field responseName leftFieldName leftArguments
                leftDirectives leftChildSelectionSet
              ∈ left
            -> schema.lookupField leftParentType leftFieldName = some leftFieldDefinition
            -> (TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool
                  schema
                = true
            -> ((objectTypeNameBool schema leftFieldDefinition.outputType.namedType = true
                  ∧ leftChildRuntime = leftFieldDefinition.outputType.namedType)
                ∨ ((TypeRef.named
                        leftFieldDefinition.outputType.namedType).isCompositeBool
                        schema
                      = true
                    ∧ objectTypeNameBool schema leftFieldDefinition.outputType.namedType
                      = false
                    ∧ abstractRuntimeForFieldHeadDeep? schema leftParentType
                        leftFieldName leftArguments leftParentType
                        leftCurrentSelectionSet
                      = some leftChildRuntime))
            -> schema.typeIncludesObjectBool
                  leftFieldDefinition.outputType.namedType leftChildRuntime
                = true
            -> ((objectTypeNameBool schema rightFieldDefinition.outputType.namedType
                    = true
                  ∧ rightChildRuntime = rightFieldDefinition.outputType.namedType)
                ∨ ((TypeRef.named
                        rightFieldDefinition.outputType.namedType).isCompositeBool
                        schema
                      = true
                    ∧ objectTypeNameBool schema rightFieldDefinition.outputType.namedType
                      = false
                    ∧ abstractRuntimeForFieldHeadDeep? schema rightParentType
                        rightFieldName rightArguments rightParentType
                        rightCurrentSelectionSet
                      = some rightChildRuntime))
            -> schema.typeIncludesObjectBool
                  rightFieldDefinition.outputType.namedType rightChildRuntime
                = true
            -> ¬ Execution.ResponseValue.semanticEquivalent
                  (Execution.executeSelectionSetAsResponse schema
                    (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                      (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                        rightInitialSelectionSet targetParent leftProbeField
                        rightProbeField targetLeftArguments targetRightArguments
                        leftRuntime rightRuntime)
                      targetParent leftProbeField rightProbeField targetLeftArguments
                      targetRightArguments)
                    variableValues
                    (fuel - leafProbeFuel leftFieldDefinition.outputType)
                    leftChildRuntime
                    (projectionTargetResolverValue
                      (.object leftChildRuntime
                        (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                          (fieldPairPathLocalNextSelectionSet schema leftParentType
                            leftChildRuntime leftFieldName leftArguments
                            leftCurrentSelectionSet))))
                    leftChildSelectionSet).data
                  (Execution.executeSelectionSetAsResponse schema
                    (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                      (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                        rightInitialSelectionSet targetParent leftProbeField
                        rightProbeField targetLeftArguments targetRightArguments
                        leftRuntime rightRuntime)
                      targetParent leftProbeField rightProbeField targetLeftArguments
                      targetRightArguments)
                    variableValues
                    (fuel - leafProbeFuel rightFieldDefinition.outputType)
                    rightChildRuntime
                    (projectionTargetResolverValue
                      (.object rightChildRuntime
                        (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                          (fieldPairPathLocalNextSelectionSet schema rightParentType
                            rightChildRuntime rightFieldName rightArguments
                            rightCurrentSelectionSet))))
                    rightChildSelectionSet).data)
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet targetParent leftProbeField
                  rightProbeField targetLeftArguments targetRightArguments
                  leftRuntime rightRuntime)
                targetParent leftProbeField rightProbeField targetLeftArguments
                targetRightArguments)
              variableValues (fuel + 1) leftParentType
              (projectionTargetResolverValue
                (.object leftParentType
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                    leftCurrentSelectionSet)))
              left).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet targetParent leftProbeField
                  rightProbeField targetLeftArguments targetRightArguments
                  leftRuntime rightRuntime)
                targetParent leftProbeField rightProbeField targetLeftArguments
                targetRightArguments)
              variableValues (fuel + 1) rightParentType
              (projectionTargetResolverValue
                (.object rightParentType
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                    rightCurrentSelectionSet)))
              right).data := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hleftObject hrightObject hleftFuel hrightFuel hleftSupport
    hrightSupport hleftContext hrightContext hrightMem hrightLookup
    hrightComposite hchildDataNot
  rcases
      pathLocalCompositeFieldRuntime_of_valid_normal_support_context
        hrightValid hrightNormal hrightSupport hrightContext hrightMem
        hrightLookup hrightComposite with
    ⟨rightChildRuntime, hrightRuntime, hrightInclude⟩
  by_cases hleftResponseName :
      responseName ∈ left.filterMap Selection.responseName?
  · rcases
        selectionSetNormal_field_mem_of_responseName_mem hleftNormal
          hleftObject hleftResponseName with
      ⟨leftFieldName, leftArguments, leftDirectives,
        leftChildSelectionSet, hleftMem⟩
    rcases selectionSetValid_field_lookup_of_mem hleftValid hleftMem with
      ⟨leftFieldDefinition, hleftLookup, _hleftArguments,
        _hleftFieldValid⟩
    by_cases hleftLeaf :
        (TypeRef.named
            leftFieldDefinition.outputType.namedType).isCompositeBool
          schema = false
    · exact
        responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_left_leaf_right_composite_field_pair_of_valid_normal_support_context_fuel_ge
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet leftCurrentSelectionSet
          rightCurrentSelectionSet variableValues fuel targetParent
          leftProbeField rightProbeField leftParentType rightParentType
          targetLeftArguments targetRightArguments leftRuntime rightRuntime
          hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
          hrightNormal hleftObject hrightObject hleftFuel hrightFuel
          hleftSupport hrightSupport hleftContext hrightContext hleftMem
          hrightMem hleftLookup hrightLookup hleftLeaf hrightComposite
    · have hleftComposite :
          (TypeRef.named
              leftFieldDefinition.outputType.namedType).isCompositeBool
            schema = true := by
        cases h :
            (TypeRef.named
                leftFieldDefinition.outputType.namedType).isCompositeBool
              schema
        · exact False.elim (hleftLeaf h)
        · rfl
      rcases
          pathLocalCompositeFieldRuntime_of_valid_normal_support_context
            hleftValid hleftNormal hleftSupport hleftContext hleftMem
            hleftLookup hleftComposite with
        ⟨leftChildRuntime, hleftRuntime, hleftInclude⟩
      have hchildNotData :
          ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema
                  leftInitialSelectionSet rightInitialSelectionSet
                  targetParent leftProbeField rightProbeField
                  targetLeftArguments targetRightArguments leftRuntime
                  rightRuntime)
                targetParent leftProbeField rightProbeField
                targetLeftArguments targetRightArguments)
              variableValues
              (fuel - leafProbeFuel leftFieldDefinition.outputType)
              leftChildRuntime
              (projectionTargetResolverValue
                (.object leftChildRuntime
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                    (fieldPairPathLocalNextSelectionSet schema
                      leftParentType leftChildRuntime leftFieldName
                      leftArguments leftCurrentSelectionSet))))
              leftChildSelectionSet).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema
                  leftInitialSelectionSet rightInitialSelectionSet
                  targetParent leftProbeField rightProbeField
                  targetLeftArguments targetRightArguments leftRuntime
                  rightRuntime)
                targetParent leftProbeField rightProbeField
                targetLeftArguments targetRightArguments)
              variableValues
              (fuel - leafProbeFuel rightFieldDefinition.outputType)
              rightChildRuntime
              (projectionTargetResolverValue
                (.object rightChildRuntime
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                    (fieldPairPathLocalNextSelectionSet schema
                      rightParentType rightChildRuntime rightFieldName
                      rightArguments rightCurrentSelectionSet))))
              rightChildSelectionSet).data :=
        hchildDataNot hleftMem hleftLookup hleftComposite hleftRuntime
          hleftInclude hrightRuntime hrightInclude
      rcases
          executeSelectionSetAsResponse_fieldPairOrDeepSuccess_pathLocalProbe_target_child_of_valid_normal_context_fuel_ge
            (schema := schema) (rootSelectionSet := rootSelectionSet)
            (leftInitialSelectionSet := leftInitialSelectionSet)
            (rightInitialSelectionSet := rightInitialSelectionSet)
            (currentSelectionSet := leftCurrentSelectionSet)
            (variableValues := variableValues)
            (variableDefinitions := leftVariableDefinitions)
            (parentType := leftParentType)
            (runtimeType := leftChildRuntime)
            (targetParent := targetParent)
            (leftField := leftProbeField) (rightField := rightProbeField)
            (responseName := responseName) (fieldName := leftFieldName)
            (targetLeftArguments := targetLeftArguments)
            (targetRightArguments := targetRightArguments)
            (targetArguments := leftArguments)
            (arguments := leftArguments) (directives := leftDirectives)
            (leftRuntime := leftRuntime) (rightRuntime := rightRuntime)
            (selectionSet := left)
            (childSelectionSet := leftChildSelectionSet)
            (fieldDefinition := leftFieldDefinition) (fuel := fuel)
            (tag := FieldPairProbeTag.left)
            hschema hleftValid hleftFree hleftNormal hleftObject hleftFuel
            hleftSupport hleftContext hleftMem hleftLookup hleftComposite
            hleftInclude
            (argumentsEquivalent_refl_forSyntaxDiff leftArguments) with
        ⟨leftChildFields, leftChildErrors, hleftChildResponse⟩
      rcases
          executeSelectionSetAsResponse_fieldPairOrDeepSuccess_pathLocalProbe_target_child_of_valid_normal_context_fuel_ge
            (schema := schema) (rootSelectionSet := rootSelectionSet)
            (leftInitialSelectionSet := leftInitialSelectionSet)
            (rightInitialSelectionSet := rightInitialSelectionSet)
            (currentSelectionSet := rightCurrentSelectionSet)
            (variableValues := variableValues)
            (variableDefinitions := rightVariableDefinitions)
            (parentType := rightParentType)
            (runtimeType := rightChildRuntime)
            (targetParent := targetParent)
            (leftField := leftProbeField) (rightField := rightProbeField)
            (responseName := responseName) (fieldName := rightFieldName)
            (targetLeftArguments := targetLeftArguments)
            (targetRightArguments := targetRightArguments)
            (targetArguments := rightArguments)
            (arguments := rightArguments) (directives := rightDirectives)
            (leftRuntime := leftRuntime) (rightRuntime := rightRuntime)
            (selectionSet := right)
            (childSelectionSet := rightChildSelectionSet)
            (fieldDefinition := rightFieldDefinition) (fuel := fuel)
            (tag := FieldPairProbeTag.right)
            hschema hrightValid hrightFree hrightNormal hrightObject
            hrightFuel hrightSupport hrightContext hrightMem hrightLookup
            hrightComposite hrightInclude
            (argumentsEquivalent_refl_forSyntaxDiff rightArguments) with
        ⟨rightChildFields, rightChildErrors, hrightChildResponse⟩
      have hchildObjectNot :
          ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.ResponseValue.object leftChildFields)
            (Execution.ResponseValue.object rightChildFields) := by
        intro hchildSemantic
        exact hchildNotData
          (by
            simpa [hleftChildResponse, hrightChildResponse] using
              hchildSemantic)
      exact
        responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_child_field_pair_of_valid_normal_support_context_fuel_ge
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet leftCurrentSelectionSet
          rightCurrentSelectionSet variableValues fuel targetParent
          leftProbeField rightProbeField leftParentType rightParentType
          targetLeftArguments targetRightArguments leftRuntime rightRuntime
          hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
          hrightNormal hleftObject hrightObject hleftFuel hrightFuel
          hleftSupport hrightSupport hleftContext hrightContext hleftMem
          hrightMem hleftLookup hrightLookup hleftRuntime hrightRuntime
          hleftInclude hrightInclude hleftChildResponse hrightChildResponse
          hchildObjectNot
  · exact
      responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_right_responseName_diff_of_valid_normal_support_context_fuel_ge
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftCurrentSelectionSet
        rightCurrentSelectionSet variableValues fuel targetParent
        leftProbeField rightProbeField leftParentType rightParentType
        targetLeftArguments targetRightArguments leftRuntime rightRuntime
        hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
        hrightNormal hleftObject hrightObject hleftFuel hrightFuel
        hleftSupport hrightSupport hleftContext hrightContext hrightMem
        hleftResponseName

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_right_object_child_of_valid_normal_support_context_fuel_ge_fuels
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (variableValues : Execution.VariableValues) (leftFuel rightFuel : Nat)
    (targetParent leftProbeField rightProbeField leftParentType rightParentType : Name)
    (targetLeftArguments targetRightArguments : List Argument)
    (leftRuntime rightRuntime : Name) {left right : List Selection}
    {responseName rightFieldName : Name} {rightArguments : List Argument}
    {rightDirectives : List DirectiveApplication}
    {rightChildSelectionSet : List Selection} {rightFieldDefinition : FieldDefinition}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
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
      -> Selection.field responseName rightFieldName rightArguments
            rightDirectives rightChildSelectionSet
          ∈ right
      -> schema.lookupField rightParentType rightFieldName = some rightFieldDefinition
      -> (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> (∀ {leftFieldName : Name}
            {leftArguments : List Argument}
            {leftDirectives : List DirectiveApplication}
            {leftChildSelectionSet : List Selection}
            {leftFieldDefinition : FieldDefinition}
            {leftChildRuntime rightChildRuntime : Name},
            Selection.field responseName leftFieldName leftArguments
                leftDirectives leftChildSelectionSet
              ∈ left
            -> schema.lookupField leftParentType leftFieldName = some leftFieldDefinition
            -> (TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool
                  schema
                = true
            -> ((objectTypeNameBool schema leftFieldDefinition.outputType.namedType = true
                  ∧ leftChildRuntime = leftFieldDefinition.outputType.namedType)
                ∨ ((TypeRef.named
                        leftFieldDefinition.outputType.namedType).isCompositeBool
                        schema
                      = true
                    ∧ objectTypeNameBool schema leftFieldDefinition.outputType.namedType
                      = false
                    ∧ abstractRuntimeForFieldHeadDeep? schema leftParentType
                        leftFieldName leftArguments leftParentType
                        leftCurrentSelectionSet
                      = some leftChildRuntime))
            -> schema.typeIncludesObjectBool
                  leftFieldDefinition.outputType.namedType leftChildRuntime
                = true
            -> ((objectTypeNameBool schema rightFieldDefinition.outputType.namedType
                    = true
                  ∧ rightChildRuntime = rightFieldDefinition.outputType.namedType)
                ∨ ((TypeRef.named
                        rightFieldDefinition.outputType.namedType).isCompositeBool
                        schema
                      = true
                    ∧ objectTypeNameBool schema rightFieldDefinition.outputType.namedType
                      = false
                    ∧ abstractRuntimeForFieldHeadDeep? schema rightParentType
                        rightFieldName rightArguments rightParentType
                        rightCurrentSelectionSet
                      = some rightChildRuntime))
            -> schema.typeIncludesObjectBool
                  rightFieldDefinition.outputType.namedType rightChildRuntime
                = true
            -> ¬ Execution.ResponseValue.semanticEquivalent
                  (Execution.executeSelectionSetAsResponse schema
                    (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                      (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                        rightInitialSelectionSet targetParent leftProbeField
                        rightProbeField targetLeftArguments targetRightArguments
                        leftRuntime rightRuntime)
                      targetParent leftProbeField rightProbeField targetLeftArguments
                      targetRightArguments)
                    variableValues
                    (leftFuel - leafProbeFuel leftFieldDefinition.outputType)
                    leftChildRuntime
                    (projectionTargetResolverValue
                      (.object leftChildRuntime
                        (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                          (fieldPairPathLocalNextSelectionSet schema leftParentType
                            leftChildRuntime leftFieldName leftArguments
                            leftCurrentSelectionSet))))
                    leftChildSelectionSet).data
                  (Execution.executeSelectionSetAsResponse schema
                    (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                      (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                        rightInitialSelectionSet targetParent leftProbeField
                        rightProbeField targetLeftArguments targetRightArguments
                        leftRuntime rightRuntime)
                      targetParent leftProbeField rightProbeField targetLeftArguments
                      targetRightArguments)
                    variableValues
                    (rightFuel - leafProbeFuel rightFieldDefinition.outputType)
                    rightChildRuntime
                    (projectionTargetResolverValue
                      (.object rightChildRuntime
                        (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                          (fieldPairPathLocalNextSelectionSet schema rightParentType
                            rightChildRuntime rightFieldName rightArguments
                            rightCurrentSelectionSet))))
                    rightChildSelectionSet).data)
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet targetParent leftProbeField
                  rightProbeField targetLeftArguments targetRightArguments
                  leftRuntime rightRuntime)
                targetParent leftProbeField rightProbeField targetLeftArguments
                targetRightArguments)
              variableValues (leftFuel + 1) leftParentType
              (projectionTargetResolverValue
                (.object leftParentType
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                    leftCurrentSelectionSet)))
              left).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet targetParent leftProbeField
                  rightProbeField targetLeftArguments targetRightArguments
                  leftRuntime rightRuntime)
                targetParent leftProbeField rightProbeField targetLeftArguments
                targetRightArguments)
              variableValues (rightFuel + 1) rightParentType
              (projectionTargetResolverValue
                (.object rightParentType
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                    rightCurrentSelectionSet)))
              right).data := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hleftObject hrightObject hleftFuel hrightFuel hleftSupport
    hrightSupport hleftContext hrightContext hrightMem hrightLookup
    hrightComposite hchildDataNot
  rcases
      pathLocalCompositeFieldRuntime_of_valid_normal_support_context
        hrightValid hrightNormal hrightSupport hrightContext hrightMem
        hrightLookup hrightComposite with
    ⟨rightChildRuntime, hrightRuntime, hrightInclude⟩
  by_cases hleftResponseName :
      responseName ∈ left.filterMap Selection.responseName?
  · rcases
        selectionSetNormal_field_mem_of_responseName_mem hleftNormal
          hleftObject hleftResponseName with
      ⟨leftFieldName, leftArguments, leftDirectives,
        leftChildSelectionSet, hleftMem⟩
    rcases selectionSetValid_field_lookup_of_mem hleftValid hleftMem with
      ⟨leftFieldDefinition, hleftLookup, _hleftArguments,
        _hleftFieldValid⟩
    by_cases hleftLeaf :
        (TypeRef.named
            leftFieldDefinition.outputType.namedType).isCompositeBool
          schema = false
    · exact
        responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_left_leaf_right_composite_field_pair_of_valid_normal_support_context_fuel_ge_fuels
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet leftCurrentSelectionSet
          rightCurrentSelectionSet variableValues leftFuel rightFuel
          targetParent leftProbeField rightProbeField leftParentType
          rightParentType targetLeftArguments targetRightArguments
          leftRuntime rightRuntime hschema hleftValid hrightValid
          hleftFree hrightFree hleftNormal hrightNormal hleftObject
          hrightObject hleftFuel hrightFuel hleftSupport hrightSupport
          hleftContext hrightContext hleftMem hrightMem hleftLookup
          hrightLookup hleftLeaf hrightComposite
    · have hleftComposite :
          (TypeRef.named
              leftFieldDefinition.outputType.namedType).isCompositeBool
            schema = true := by
        cases h :
            (TypeRef.named
                leftFieldDefinition.outputType.namedType).isCompositeBool
              schema
        · exact False.elim (hleftLeaf h)
        · rfl
      rcases
          pathLocalCompositeFieldRuntime_of_valid_normal_support_context
            hleftValid hleftNormal hleftSupport hleftContext hleftMem
            hleftLookup hleftComposite with
        ⟨leftChildRuntime, hleftRuntime, hleftInclude⟩
      have hchildNotData :
          ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema
                  leftInitialSelectionSet rightInitialSelectionSet
                  targetParent leftProbeField rightProbeField
                  targetLeftArguments targetRightArguments leftRuntime
                  rightRuntime)
                targetParent leftProbeField rightProbeField
                targetLeftArguments targetRightArguments)
              variableValues
              (leftFuel - leafProbeFuel leftFieldDefinition.outputType)
              leftChildRuntime
              (projectionTargetResolverValue
                (.object leftChildRuntime
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                    (fieldPairPathLocalNextSelectionSet schema
                      leftParentType leftChildRuntime leftFieldName
                      leftArguments leftCurrentSelectionSet))))
              leftChildSelectionSet).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema
                  leftInitialSelectionSet rightInitialSelectionSet
                  targetParent leftProbeField rightProbeField
                  targetLeftArguments targetRightArguments leftRuntime
                  rightRuntime)
                targetParent leftProbeField rightProbeField
                targetLeftArguments targetRightArguments)
              variableValues
              (rightFuel - leafProbeFuel rightFieldDefinition.outputType)
              rightChildRuntime
              (projectionTargetResolverValue
                (.object rightChildRuntime
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                    (fieldPairPathLocalNextSelectionSet schema
                      rightParentType rightChildRuntime rightFieldName
                      rightArguments rightCurrentSelectionSet))))
              rightChildSelectionSet).data :=
        hchildDataNot hleftMem hleftLookup hleftComposite hleftRuntime
          hleftInclude hrightRuntime hrightInclude
      rcases
          executeSelectionSetAsResponse_fieldPairOrDeepSuccess_pathLocalProbe_target_child_of_valid_normal_context_fuel_ge
            (schema := schema) (rootSelectionSet := rootSelectionSet)
            (leftInitialSelectionSet := leftInitialSelectionSet)
            (rightInitialSelectionSet := rightInitialSelectionSet)
            (currentSelectionSet := leftCurrentSelectionSet)
            (variableValues := variableValues)
            (variableDefinitions := leftVariableDefinitions)
            (parentType := leftParentType)
            (runtimeType := leftChildRuntime)
            (targetParent := targetParent)
            (leftField := leftProbeField) (rightField := rightProbeField)
            (responseName := responseName) (fieldName := leftFieldName)
            (targetLeftArguments := targetLeftArguments)
            (targetRightArguments := targetRightArguments)
            (targetArguments := leftArguments)
            (arguments := leftArguments) (directives := leftDirectives)
            (leftRuntime := leftRuntime) (rightRuntime := rightRuntime)
            (selectionSet := left)
            (childSelectionSet := leftChildSelectionSet)
            (fieldDefinition := leftFieldDefinition) (fuel := leftFuel)
            (tag := FieldPairProbeTag.left)
            hschema hleftValid hleftFree hleftNormal hleftObject hleftFuel
            hleftSupport hleftContext hleftMem hleftLookup hleftComposite
            hleftInclude
            (argumentsEquivalent_refl_forSyntaxDiff leftArguments) with
        ⟨leftChildFields, leftChildErrors, hleftChildResponse⟩
      rcases
          executeSelectionSetAsResponse_fieldPairOrDeepSuccess_pathLocalProbe_target_child_of_valid_normal_context_fuel_ge
            (schema := schema) (rootSelectionSet := rootSelectionSet)
            (leftInitialSelectionSet := leftInitialSelectionSet)
            (rightInitialSelectionSet := rightInitialSelectionSet)
            (currentSelectionSet := rightCurrentSelectionSet)
            (variableValues := variableValues)
            (variableDefinitions := rightVariableDefinitions)
            (parentType := rightParentType)
            (runtimeType := rightChildRuntime)
            (targetParent := targetParent)
            (leftField := leftProbeField) (rightField := rightProbeField)
            (responseName := responseName) (fieldName := rightFieldName)
            (targetLeftArguments := targetLeftArguments)
            (targetRightArguments := targetRightArguments)
            (targetArguments := rightArguments)
            (arguments := rightArguments) (directives := rightDirectives)
            (leftRuntime := leftRuntime) (rightRuntime := rightRuntime)
            (selectionSet := right)
            (childSelectionSet := rightChildSelectionSet)
            (fieldDefinition := rightFieldDefinition) (fuel := rightFuel)
            (tag := FieldPairProbeTag.right)
            hschema hrightValid hrightFree hrightNormal hrightObject
            hrightFuel hrightSupport hrightContext hrightMem hrightLookup
            hrightComposite hrightInclude
            (argumentsEquivalent_refl_forSyntaxDiff rightArguments) with
        ⟨rightChildFields, rightChildErrors, hrightChildResponse⟩
      have hchildObjectNot :
          ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.ResponseValue.object leftChildFields)
            (Execution.ResponseValue.object rightChildFields) := by
        intro hchildSemantic
        exact hchildNotData
          (by
            simpa [hleftChildResponse, hrightChildResponse] using
              hchildSemantic)
      exact
        responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_child_field_pair_of_valid_normal_support_context_fuel_ge_fuels
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet leftCurrentSelectionSet
          rightCurrentSelectionSet variableValues leftFuel rightFuel
          targetParent leftProbeField rightProbeField leftParentType
          rightParentType targetLeftArguments targetRightArguments
          leftRuntime rightRuntime hschema hleftValid hrightValid
          hleftFree hrightFree hleftNormal hrightNormal hleftObject
          hrightObject hleftFuel hrightFuel hleftSupport hrightSupport
          hleftContext hrightContext hleftMem hrightMem hleftLookup
          hrightLookup hleftRuntime hrightRuntime hleftInclude
          hrightInclude hleftChildResponse hrightChildResponse
          hchildObjectNot
  · exact
      responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_right_responseName_diff_of_valid_normal_support_context_fuel_ge_fuels
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftCurrentSelectionSet
        rightCurrentSelectionSet variableValues leftFuel rightFuel
        targetParent leftProbeField rightProbeField leftParentType
        rightParentType targetLeftArguments targetRightArguments
        leftRuntime rightRuntime hschema hleftValid hrightValid hleftFree
        hrightFree hleftNormal hrightNormal hleftObject hrightObject
        hleftFuel hrightFuel hleftSupport hrightSupport hleftContext
        hrightContext hrightMem hleftResponseName

theorem
    responseData_not_semanticEquivalent_empty_object_of_valid_normal_object_nonempty_response
    {ObjectRef : Type} (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues) (fuel : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef) {selectionSet : List Selection}
    {fields : List (Name × Execution.ResponseValue)} {errors : Nat}
    : objectTypeNameBool schema parentType = true
      -> selectionSetDirectiveFree selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> selectionSet ≠ []
      -> Execution.executeSelectionSetAsResponse schema resolvers variableValues fuel
            parentType source selectionSet
          = ({ data := Execution.ResponseValue.object fields, errors := errors }
              : Execution.Response)
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema resolvers variableValues
              fuel parentType source selectionSet).data
            (Execution.ResponseValue.object []) := by
  intro hobject hfree hnormal hnonempty hresponse hsemantic
  rcases selectionSetNormal_field_mem_of_object_nonempty hnormal hobject
      hnonempty with
    ⟨responseName, fieldName, arguments, directives, childSelectionSet,
      hmem⟩
  have hresponseNameMem :
      responseName ∈ selectionSet.filterMap Selection.responseName? := by
    exact
      List.mem_filterMap.mpr
        ⟨Selection.field responseName fieldName arguments directives
          childSelectionSet, hmem, by simp [Selection.responseName?]⟩
  have hcollectKey :
      responseName ∈
        (Execution.collectFields schema variableValues parentType source
          selectionSet).map Prod.fst :=
    (ExecutionKeys.collectFields_normal_object_key_mem_iff schema
      variableValues parentType source responseName hobject hnormal
      hfree).mpr hresponseNameMem
  have hkeys :
      fields.map Prod.fst =
        (Execution.collectFields schema variableValues parentType source
          selectionSet).map Prod.fst :=
    ExecutionResponseKeys.executeSelectionSetAsResponse_object_keys_eq_collectFields
      schema resolvers variableValues fuel parentType source selectionSet
      hresponse
  have hfieldsKey : responseName ∈ fields.map Prod.fst := by
    rw [hkeys]
    exact hcollectKey
  cases fields with
  | nil =>
      simp at hfieldsKey
  | cons field fields =>
      exact
        SemanticSeparation.responseValue_object_cons_not_semanticEquivalent_empty_object
          (field := field) (fields := fields)
          (by simpa [hresponse] using hsemantic)

theorem
    responseData_empty_object_not_semanticEquivalent_of_valid_normal_object_nonempty_response
    {ObjectRef : Type} (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues) (fuel : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef) {selectionSet : List Selection}
    {fields : List (Name × Execution.ResponseValue)} {errors : Nat}
    : objectTypeNameBool schema parentType = true
      -> selectionSetDirectiveFree selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> selectionSet ≠ []
      -> Execution.executeSelectionSetAsResponse schema resolvers variableValues fuel
            parentType source selectionSet
          = ({ data := Execution.ResponseValue.object fields, errors := errors }
              : Execution.Response)
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.ResponseValue.object [])
            (Execution.executeSelectionSetAsResponse schema resolvers variableValues
              fuel parentType source selectionSet).data := by
  intro hobject hfree hnormal hnonempty hresponse hsemantic
  exact
    responseData_not_semanticEquivalent_empty_object_of_valid_normal_object_nonempty_response
      schema resolvers variableValues fuel parentType source hobject hfree
      hnormal hnonempty hresponse
      (by
        unfold Execution.ResponseValue.semanticEquivalent at hsemantic ⊢
        exact hsemantic.symm)

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_child_field_of_field_ok_of_sound
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet currentSelectionSet
      : List Selection)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField parentType sourceRuntimeType : Name)
    (leftArguments rightArguments : List Argument) (leftRuntime rightRuntime : Name)
    {selectionSet : List Selection} {responseName fieldName : Name}
    {arguments : List Argument} {directives : List DirectiveApplication}
    {childSelectionSet : List Selection} {fieldDefinition : FieldDefinition}
    {runtimeType : Name}
    {leftChildFields rightChildFields : List (Name × Execution.ResponseValue)}
    {leftChildErrors rightChildErrors : Nat}
    : selectionSetDirectiveFree selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> objectTypeNameBool schema parentType = true
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> ((objectTypeNameBool schema fieldDefinition.outputType.namedType = true
            ∧ runtimeType = fieldDefinition.outputType.namedType)
          ∨ ((TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
                = true
              ∧ objectTypeNameBool schema fieldDefinition.outputType.namedType = false
              ∧ abstractRuntimeForFieldHeadDeep? schema parentType fieldName
                  arguments parentType currentSelectionSet
                = some runtimeType))
      -> PathLocalCurrentRuntimeSound schema (parentType, currentSelectionSet)
      -> leafProbeFuel fieldDefinition.outputType ≤ fuel
      -> Execution.executeSelectionSetAsResponse schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet targetParent leftField rightField
                leftArguments rightArguments leftRuntime rightRuntime)
              targetParent leftField rightField leftArguments rightArguments)
            variableValues
            (fuel - leafProbeFuel fieldDefinition.outputType)
            runtimeType
            (projectionTargetResolverValue
              (.object runtimeType
                (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                  (fieldPairPathLocalNextSelectionSet schema parentType
                    runtimeType fieldName arguments currentSelectionSet))))
            childSelectionSet
          = ({
                data := Execution.ResponseValue.object leftChildFields,
                errors := leftChildErrors
              }
              : Execution.Response)
      -> Execution.executeSelectionSetAsResponse schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet targetParent leftField rightField
                leftArguments rightArguments leftRuntime rightRuntime)
              targetParent leftField rightField leftArguments rightArguments)
            variableValues
            (fuel - leafProbeFuel fieldDefinition.outputType)
            runtimeType
            (projectionTargetResolverValue
              (.object runtimeType
                (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                  (fieldPairPathLocalNextSelectionSet schema parentType
                    runtimeType fieldName arguments currentSelectionSet))))
            childSelectionSet
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
              ∈ selectionSet
            -> ∃ responseValue fieldErrors,
                Execution.executeField schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                      rightInitialSelectionSet targetParent leftField rightField
                      leftArguments rightArguments leftRuntime rightRuntime)
                    targetParent leftField rightField leftArguments rightArguments)
                  variableValues (fuel + 1)
                  (projectionTargetResolverValue
                    (.object sourceRuntimeType
                      (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                        currentSelectionSet)))
                  responseName
                  [{
                    parentType := parentType
                    responseName := responseName
                    fieldName := fieldName
                    arguments := arguments
                    selectionSet := childSelectionSet
                  }]
                = .ok ([(responseName, responseValue)], fieldErrors))
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ selectionSet
            -> ∃ responseValue fieldErrors,
                Execution.executeField schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                      rightInitialSelectionSet targetParent leftField rightField
                      leftArguments rightArguments leftRuntime rightRuntime)
                    targetParent leftField rightField leftArguments rightArguments)
                  variableValues (fuel + 1)
                  (projectionTargetResolverValue
                    (.object sourceRuntimeType
                      (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                        currentSelectionSet)))
                  responseName
                  [{
                    parentType := parentType
                    responseName := responseName
                    fieldName := fieldName
                    arguments := arguments
                    selectionSet := childSelectionSet
                  }]
                = .ok ([(responseName, responseValue)], fieldErrors))
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet targetParent leftField rightField
                  leftArguments rightArguments leftRuntime rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) parentType
              (projectionTargetResolverValue
                (.object sourceRuntimeType
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                    currentSelectionSet)))
              selectionSet).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet targetParent leftField rightField
                  leftArguments rightArguments leftRuntime rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) parentType
              (projectionTargetResolverValue
                (.object sourceRuntimeType
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                    currentSelectionSet)))
              selectionSet).data := by
  intro hfree hnormal hobject hmem hlookup hruntime hsound hfuel
    hleftChildResponse hrightChildResponse hchildNot hleftFieldOk
    hrightFieldOk
  have hinclude :
      schema.typeIncludesObjectBool fieldDefinition.outputType.namedType
        runtimeType = true := by
    rcases hruntime with hobjectRuntime | habstractRuntime
    · rcases hobjectRuntime with ⟨hobjectOutput, hruntimeEq⟩
      subst runtimeType
      exact
        typeIncludesObjectBool_self_of_objectTypeNameBool schema
          hobjectOutput
    · exact
        hsound parentType fieldName runtimeType arguments fieldDefinition
          hlookup habstractRuntime.1 habstractRuntime.2.1
          habstractRuntime.2.2
  exact
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_child_field_of_field_ok
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet currentSelectionSet variableValues fuel
      targetParent leftField rightField parentType sourceRuntimeType
      leftArguments rightArguments leftRuntime rightRuntime hfree hnormal
      hobject hmem hlookup hruntime hinclude hfuel hleftChildResponse
      hrightChildResponse hchildNot hleftFieldOk hrightFieldOk

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_tagged_abstract_inlineFragment_body
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet currentSelectionSet
      : List Selection)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField normalParentType runtimeType : Name)
    (leftArguments rightArguments : List Argument) (leftRuntime rightRuntime : Name)
    {pref suffix bodySelectionSet : List Selection}
    : objectTypeNameBool schema normalParentType = false
      -> objectTypeNameBool schema runtimeType = true
      -> selectionSetDirectiveFree
          (pref
            ++ Selection.inlineFragment (some runtimeType) [] bodySelectionSet :: suffix)
      -> selectionSetNormal schema normalParentType
          (pref
            ++ Selection.inlineFragment (some runtimeType) [] bodySelectionSet :: suffix)
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet targetParent leftField rightField
                  leftArguments rightArguments leftRuntime rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) runtimeType
              (projectionTargetResolverValue
                (.object runtimeType
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                    currentSelectionSet)))
              bodySelectionSet).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet targetParent leftField rightField
                  leftArguments rightArguments leftRuntime rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) runtimeType
              (projectionTargetResolverValue
                (.object runtimeType
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                    currentSelectionSet)))
              bodySelectionSet).data
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet targetParent leftField rightField
                  leftArguments rightArguments leftRuntime rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) runtimeType
              (projectionTargetResolverValue
                (.object runtimeType
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                    currentSelectionSet)))
              (pref
                ++ Selection.inlineFragment (some runtimeType) [] bodySelectionSet
                    :: suffix)).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet targetParent leftField rightField
                  leftArguments rightArguments leftRuntime rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) runtimeType
              (projectionTargetResolverValue
                (.object runtimeType
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                    currentSelectionSet)))
              (pref
                ++ Selection.inlineFragment (some runtimeType) [] bodySelectionSet
                    :: suffix)).data := by
  intro hnonObject hruntimeObject hfree hnormal hbodyNot hsemantic
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet
      (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
        rightInitialSelectionSet targetParent leftField rightField
        leftArguments rightArguments leftRuntime rightRuntime)
      targetParent leftField rightField leftArguments rightArguments
  let leftSource :=
    projectionTargetResolverValue
      (.object runtimeType
        (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
          currentSelectionSet))
  let rightSource :=
    projectionTargetResolverValue
      (.object runtimeType
        (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
          currentSelectionSet))
  have hleftMiddle :
      Execution.executeSelectionSet schema resolvers variableValues
        (fuel + 1) runtimeType leftSource
        (pref ++ Selection.inlineFragment (some runtimeType) []
          bodySelectionSet :: suffix)
      =
      Execution.executeSelectionSet schema resolvers variableValues
        (fuel + 1) runtimeType leftSource
        [Selection.inlineFragment (some runtimeType) []
          bodySelectionSet] := by
    dsimp [leftSource]
    simpa [projectionTargetResolverValue, projectionResolverValue] using
      executeSelectionSet_middle_inlineFragment_only_eq_singleton_at_runtime_parent
        schema resolvers variableValues (fuel + 1)
        (ProjectionResolverRef.target
          (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
            currentSelectionSet))
        hnonObject hruntimeObject hfree hnormal
  have hrightMiddle :
      Execution.executeSelectionSet schema resolvers variableValues
        (fuel + 1) runtimeType rightSource
        (pref ++ Selection.inlineFragment (some runtimeType) []
          bodySelectionSet :: suffix)
      =
      Execution.executeSelectionSet schema resolvers variableValues
        (fuel + 1) runtimeType rightSource
        [Selection.inlineFragment (some runtimeType) []
          bodySelectionSet] := by
    dsimp [rightSource]
    simpa [projectionTargetResolverValue, projectionResolverValue] using
      executeSelectionSet_middle_inlineFragment_only_eq_singleton_at_runtime_parent
        schema resolvers variableValues (fuel + 1)
        (ProjectionResolverRef.target
          (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
            currentSelectionSet))
        hnonObject hruntimeObject hfree hnormal
  have hleftApply :
      Execution.doesFragmentTypeApplyBool schema runtimeType leftSource
          runtimeType =
        true := by
    dsimp [leftSource]
    simpa [projectionTargetResolverValue, projectionResolverValue] using
      doesFragmentTypeApplyBool_object_self schema
        (ref :=
          ProjectionResolverRef.target
            (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
              currentSelectionSet))
        hruntimeObject
  have hrightApply :
      Execution.doesFragmentTypeApplyBool schema runtimeType rightSource
          runtimeType =
        true := by
    dsimp [rightSource]
    simpa [projectionTargetResolverValue, projectionResolverValue] using
      doesFragmentTypeApplyBool_object_self schema
        (ref :=
          ProjectionResolverRef.target
            (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
              currentSelectionSet))
        hruntimeObject
  have hleftFlatten :
      Execution.executeSelectionSet schema resolvers variableValues
        (fuel + 1) runtimeType leftSource
        [Selection.inlineFragment (some runtimeType) []
          bodySelectionSet]
      =
      Execution.executeSelectionSet schema resolvers variableValues
        (fuel + 1) runtimeType leftSource bodySelectionSet := by
    simpa using
      executeSelectionSet_inlineFragment_some_directiveFree_apply_flatten
        schema resolvers variableValues (fuel + 1) runtimeType runtimeType
        leftSource bodySelectionSet [] hleftApply
  have hrightFlatten :
      Execution.executeSelectionSet schema resolvers variableValues
        (fuel + 1) runtimeType rightSource
        [Selection.inlineFragment (some runtimeType) []
          bodySelectionSet]
      =
      Execution.executeSelectionSet schema resolvers variableValues
        (fuel + 1) runtimeType rightSource bodySelectionSet := by
    simpa using
      executeSelectionSet_inlineFragment_some_directiveFree_apply_flatten
        schema resolvers variableValues (fuel + 1) runtimeType runtimeType
        rightSource bodySelectionSet [] hrightApply
  apply hbodyNot
  simpa [Execution.executeSelectionSetAsResponse, resolvers, leftSource, rightSource,
    hleftMiddle, hrightMiddle, hleftFlatten, hrightFlatten] using hsemantic

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_abstract_inlineFragment_body_pair
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet currentSelectionSet
      : List Selection)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField normalParentType runtimeType : Name)
    (leftArguments rightArguments : List Argument) (leftRuntime rightRuntime : Name)
    {left right leftBodySelectionSet rightBodySelectionSet : List Selection}
    {leftDirectives rightDirectives : List DirectiveApplication}
    : objectTypeNameBool schema normalParentType = false
      -> objectTypeNameBool schema runtimeType = true
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema normalParentType left
      -> selectionSetNormal schema normalParentType right
      -> Selection.inlineFragment (some runtimeType) leftDirectives leftBodySelectionSet
          ∈ left
      -> Selection.inlineFragment (some runtimeType) rightDirectives rightBodySelectionSet
          ∈ right
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet targetParent leftField rightField
                  leftArguments rightArguments leftRuntime rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) runtimeType
              (projectionTargetResolverValue
                (.object runtimeType
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                    currentSelectionSet)))
              leftBodySelectionSet).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet targetParent leftField rightField
                  leftArguments rightArguments leftRuntime rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) runtimeType
              (projectionTargetResolverValue
                (.object runtimeType
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                    currentSelectionSet)))
              rightBodySelectionSet).data
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet targetParent leftField rightField
                  leftArguments rightArguments leftRuntime rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) runtimeType
              (projectionTargetResolverValue
                (.object runtimeType
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                    currentSelectionSet)))
              left).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet targetParent leftField rightField
                  leftArguments rightArguments leftRuntime rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) runtimeType
              (projectionTargetResolverValue
                (.object runtimeType
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                    currentSelectionSet)))
              right).data := by
  intro hnonObject hruntimeObject hleftFree hrightFree hleftNormal
    hrightNormal hleftMem hrightMem hbodyNot hsemantic
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet
      (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
        rightInitialSelectionSet targetParent leftField rightField
        leftArguments rightArguments leftRuntime rightRuntime)
      targetParent leftField rightField leftArguments rightArguments
  let leftSource :=
    projectionTargetResolverValue
      (.object runtimeType
        (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
          currentSelectionSet))
  let rightSource :=
    projectionTargetResolverValue
      (.object runtimeType
        (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
          currentSelectionSet))
  have hleftDirectives : leftDirectives = [] :=
    selectionSetDirectiveFree_inlineFragment_directives_nil_of_mem
      hleftFree hleftMem
  have hrightDirectives : rightDirectives = [] :=
    selectionSetDirectiveFree_inlineFragment_directives_nil_of_mem
      hrightFree hrightMem
  subst leftDirectives
  subst rightDirectives
  rcases List.mem_iff_append.mp hleftMem with
    ⟨leftPref, leftSuffix, hleftSelectionSet⟩
  rcases List.mem_iff_append.mp hrightMem with
    ⟨rightPref, rightSuffix, hrightSelectionSet⟩
  subst left
  subst right
  have hleftMiddle :
      Execution.executeSelectionSet schema resolvers variableValues
        (fuel + 1) runtimeType leftSource
        (leftPref ++ Selection.inlineFragment (some runtimeType) []
          leftBodySelectionSet :: leftSuffix)
      =
      Execution.executeSelectionSet schema resolvers variableValues
        (fuel + 1) runtimeType leftSource
        [Selection.inlineFragment (some runtimeType) []
          leftBodySelectionSet] := by
    dsimp [leftSource]
    simpa [projectionTargetResolverValue, projectionResolverValue] using
      executeSelectionSet_middle_inlineFragment_only_eq_singleton_at_runtime_parent
        schema resolvers variableValues (fuel + 1)
        (ProjectionResolverRef.target
          (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
            currentSelectionSet))
        hnonObject hruntimeObject hleftFree hleftNormal
  have hrightMiddle :
      Execution.executeSelectionSet schema resolvers variableValues
        (fuel + 1) runtimeType rightSource
        (rightPref ++ Selection.inlineFragment (some runtimeType) []
          rightBodySelectionSet :: rightSuffix)
      =
      Execution.executeSelectionSet schema resolvers variableValues
        (fuel + 1) runtimeType rightSource
        [Selection.inlineFragment (some runtimeType) []
          rightBodySelectionSet] := by
    dsimp [rightSource]
    simpa [projectionTargetResolverValue, projectionResolverValue] using
      executeSelectionSet_middle_inlineFragment_only_eq_singleton_at_runtime_parent
        schema resolvers variableValues (fuel + 1)
        (ProjectionResolverRef.target
          (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
            currentSelectionSet))
        hnonObject hruntimeObject hrightFree hrightNormal
  have hleftApply :
      Execution.doesFragmentTypeApplyBool schema runtimeType leftSource
          runtimeType =
        true := by
    dsimp [leftSource]
    simpa [projectionTargetResolverValue, projectionResolverValue] using
      doesFragmentTypeApplyBool_object_self schema
        (ref :=
          ProjectionResolverRef.target
            (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
              currentSelectionSet))
        hruntimeObject
  have hrightApply :
      Execution.doesFragmentTypeApplyBool schema runtimeType rightSource
          runtimeType =
        true := by
    dsimp [rightSource]
    simpa [projectionTargetResolverValue, projectionResolverValue] using
      doesFragmentTypeApplyBool_object_self schema
        (ref :=
          ProjectionResolverRef.target
            (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
              currentSelectionSet))
        hruntimeObject
  have hleftFlatten :
      Execution.executeSelectionSet schema resolvers variableValues
        (fuel + 1) runtimeType leftSource
        [Selection.inlineFragment (some runtimeType) []
          leftBodySelectionSet]
      =
      Execution.executeSelectionSet schema resolvers variableValues
        (fuel + 1) runtimeType leftSource leftBodySelectionSet := by
    simpa using
      executeSelectionSet_inlineFragment_some_directiveFree_apply_flatten
        schema resolvers variableValues (fuel + 1) runtimeType runtimeType
        leftSource leftBodySelectionSet [] hleftApply
  have hrightFlatten :
      Execution.executeSelectionSet schema resolvers variableValues
        (fuel + 1) runtimeType rightSource
        [Selection.inlineFragment (some runtimeType) []
          rightBodySelectionSet]
      =
      Execution.executeSelectionSet schema resolvers variableValues
        (fuel + 1) runtimeType rightSource rightBodySelectionSet := by
    simpa using
      executeSelectionSet_inlineFragment_some_directiveFree_apply_flatten
        schema resolvers variableValues (fuel + 1) runtimeType runtimeType
        rightSource rightBodySelectionSet [] hrightApply
  apply hbodyNot
  simpa [Execution.executeSelectionSetAsResponse, resolvers, leftSource, rightSource,
    hleftMiddle, hrightMiddle, hleftFlatten, hrightFlatten] using hsemantic

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_abstract_inlineFragment_body_pair_current_pair
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField normalParentType runtimeType : Name)
    (leftArguments rightArguments : List Argument) (leftRuntime rightRuntime : Name)
    {left right leftBodySelectionSet rightBodySelectionSet : List Selection}
    {leftDirectives rightDirectives : List DirectiveApplication}
    : objectTypeNameBool schema normalParentType = false
      -> objectTypeNameBool schema runtimeType = true
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema normalParentType left
      -> selectionSetNormal schema normalParentType right
      -> Selection.inlineFragment (some runtimeType) leftDirectives leftBodySelectionSet
          ∈ left
      -> Selection.inlineFragment (some runtimeType) rightDirectives rightBodySelectionSet
          ∈ right
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet targetParent leftField rightField
                  leftArguments rightArguments leftRuntime rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) runtimeType
              (projectionTargetResolverValue
                (.object runtimeType
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                    leftCurrentSelectionSet)))
              leftBodySelectionSet).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet targetParent leftField rightField
                  leftArguments rightArguments leftRuntime rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) runtimeType
              (projectionTargetResolverValue
                (.object runtimeType
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                    rightCurrentSelectionSet)))
              rightBodySelectionSet).data
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet targetParent leftField rightField
                  leftArguments rightArguments leftRuntime rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) runtimeType
              (projectionTargetResolverValue
                (.object runtimeType
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                    leftCurrentSelectionSet)))
              left).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet targetParent leftField rightField
                  leftArguments rightArguments leftRuntime rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) runtimeType
              (projectionTargetResolverValue
                (.object runtimeType
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                    rightCurrentSelectionSet)))
              right).data := by
  intro hnonObject hruntimeObject hleftFree hrightFree hleftNormal
    hrightNormal hleftMem hrightMem hbodyNot hsemantic
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet
      (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
        rightInitialSelectionSet targetParent leftField rightField
        leftArguments rightArguments leftRuntime rightRuntime)
      targetParent leftField rightField leftArguments rightArguments
  let leftSource :=
    projectionTargetResolverValue
      (.object runtimeType
        (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
          leftCurrentSelectionSet))
  let rightSource :=
    projectionTargetResolverValue
      (.object runtimeType
        (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
          rightCurrentSelectionSet))
  have hleftDirectives : leftDirectives = [] :=
    selectionSetDirectiveFree_inlineFragment_directives_nil_of_mem
      hleftFree hleftMem
  have hrightDirectives : rightDirectives = [] :=
    selectionSetDirectiveFree_inlineFragment_directives_nil_of_mem
      hrightFree hrightMem
  subst leftDirectives
  subst rightDirectives
  rcases List.mem_iff_append.mp hleftMem with
    ⟨leftPref, leftSuffix, hleftSelectionSet⟩
  rcases List.mem_iff_append.mp hrightMem with
    ⟨rightPref, rightSuffix, hrightSelectionSet⟩
  subst left
  subst right
  have hleftMiddle :
      Execution.executeSelectionSet schema resolvers variableValues
        (fuel + 1) runtimeType leftSource
        (leftPref ++ Selection.inlineFragment (some runtimeType) []
          leftBodySelectionSet :: leftSuffix)
      =
      Execution.executeSelectionSet schema resolvers variableValues
        (fuel + 1) runtimeType leftSource
        [Selection.inlineFragment (some runtimeType) []
          leftBodySelectionSet] := by
    dsimp [leftSource]
    simpa [projectionTargetResolverValue, projectionResolverValue] using
      executeSelectionSet_middle_inlineFragment_only_eq_singleton_at_runtime_parent
        schema resolvers variableValues (fuel + 1)
        (ProjectionResolverRef.target
          (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
            leftCurrentSelectionSet))
        hnonObject hruntimeObject hleftFree hleftNormal
  have hrightMiddle :
      Execution.executeSelectionSet schema resolvers variableValues
        (fuel + 1) runtimeType rightSource
        (rightPref ++ Selection.inlineFragment (some runtimeType) []
          rightBodySelectionSet :: rightSuffix)
      =
      Execution.executeSelectionSet schema resolvers variableValues
        (fuel + 1) runtimeType rightSource
        [Selection.inlineFragment (some runtimeType) []
          rightBodySelectionSet] := by
    dsimp [rightSource]
    simpa [projectionTargetResolverValue, projectionResolverValue] using
      executeSelectionSet_middle_inlineFragment_only_eq_singleton_at_runtime_parent
        schema resolvers variableValues (fuel + 1)
        (ProjectionResolverRef.target
          (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
            rightCurrentSelectionSet))
        hnonObject hruntimeObject hrightFree hrightNormal
  have hleftApply :
      Execution.doesFragmentTypeApplyBool schema runtimeType leftSource
          runtimeType =
        true := by
    dsimp [leftSource]
    simpa [projectionTargetResolverValue, projectionResolverValue] using
      doesFragmentTypeApplyBool_object_self schema
        (ref :=
          ProjectionResolverRef.target
            (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
              leftCurrentSelectionSet))
        hruntimeObject
  have hrightApply :
      Execution.doesFragmentTypeApplyBool schema runtimeType rightSource
          runtimeType =
        true := by
    dsimp [rightSource]
    simpa [projectionTargetResolverValue, projectionResolverValue] using
      doesFragmentTypeApplyBool_object_self schema
        (ref :=
          ProjectionResolverRef.target
            (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
              rightCurrentSelectionSet))
        hruntimeObject
  have hleftFlatten :
      Execution.executeSelectionSet schema resolvers variableValues
        (fuel + 1) runtimeType leftSource
        [Selection.inlineFragment (some runtimeType) []
          leftBodySelectionSet]
      =
      Execution.executeSelectionSet schema resolvers variableValues
        (fuel + 1) runtimeType leftSource leftBodySelectionSet := by
    simpa using
      executeSelectionSet_inlineFragment_some_directiveFree_apply_flatten
        schema resolvers variableValues (fuel + 1) runtimeType runtimeType
        leftSource leftBodySelectionSet [] hleftApply
  have hrightFlatten :
      Execution.executeSelectionSet schema resolvers variableValues
        (fuel + 1) runtimeType rightSource
        [Selection.inlineFragment (some runtimeType) []
          rightBodySelectionSet]
      =
      Execution.executeSelectionSet schema resolvers variableValues
        (fuel + 1) runtimeType rightSource rightBodySelectionSet := by
    simpa using
      executeSelectionSet_inlineFragment_some_directiveFree_apply_flatten
        schema resolvers variableValues (fuel + 1) runtimeType runtimeType
        rightSource rightBodySelectionSet [] hrightApply
  apply hbodyNot
  simpa [Execution.executeSelectionSetAsResponse, resolvers, leftSource, rightSource,
    hleftMiddle, hrightMiddle, hleftFlatten, hrightFlatten] using hsemantic

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_left_abstract_typeCondition_body
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet currentSelectionSet
      : List Selection)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField normalParentType runtimeType : Name)
    (leftArguments rightArguments : List Argument) (leftRuntime rightRuntime : Name)
    {left right leftBodySelectionSet : List Selection}
    {leftDirectives : List DirectiveApplication}
    : objectTypeNameBool schema normalParentType = false
      -> objectTypeNameBool schema runtimeType = true
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema normalParentType left
      -> selectionSetNormal schema normalParentType right
      -> Selection.inlineFragment (some runtimeType) leftDirectives leftBodySelectionSet
          ∈ left
      -> runtimeType ∉ right.filterMap inlineFragmentTypeCondition?
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet targetParent leftField rightField
                  leftArguments rightArguments leftRuntime rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) runtimeType
              (projectionTargetResolverValue
                (.object runtimeType
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                    currentSelectionSet)))
              leftBodySelectionSet).data
            (Execution.ResponseValue.object [])
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet targetParent leftField rightField
                  leftArguments rightArguments leftRuntime rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) runtimeType
              (projectionTargetResolverValue
                (.object runtimeType
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                    currentSelectionSet)))
              left).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet targetParent leftField rightField
                  leftArguments rightArguments leftRuntime rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) runtimeType
              (projectionTargetResolverValue
                (.object runtimeType
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                    currentSelectionSet)))
              right).data := by
  intro hnonObject hruntimeObject hleftFree hrightFree hleftNormal
    hrightNormal hleftMem hrightNoTypeCondition hbodyNot hsemantic
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet
      (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
        rightInitialSelectionSet targetParent leftField rightField
        leftArguments rightArguments leftRuntime rightRuntime)
      targetParent leftField rightField leftArguments rightArguments
  let leftSource :=
    projectionTargetResolverValue
      (.object runtimeType
        (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
          currentSelectionSet))
  let rightSource :=
    projectionTargetResolverValue
      (.object runtimeType
        (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
          currentSelectionSet))
  have hleftDirectives : leftDirectives = [] :=
    selectionSetDirectiveFree_inlineFragment_directives_nil_of_mem
      hleftFree hleftMem
  subst leftDirectives
  rcases List.mem_iff_append.mp hleftMem with
    ⟨leftPref, leftSuffix, hleftSelectionSet⟩
  subst left
  have hleftMiddle :
      Execution.executeSelectionSet schema resolvers variableValues
        (fuel + 1) runtimeType leftSource
        (leftPref ++ Selection.inlineFragment (some runtimeType) []
          leftBodySelectionSet :: leftSuffix)
      =
      Execution.executeSelectionSet schema resolvers variableValues
        (fuel + 1) runtimeType leftSource
        [Selection.inlineFragment (some runtimeType) []
          leftBodySelectionSet] := by
    dsimp [leftSource]
    simpa [projectionTargetResolverValue, projectionResolverValue] using
      executeSelectionSet_middle_inlineFragment_only_eq_singleton_at_runtime_parent
        schema resolvers variableValues (fuel + 1)
        (ProjectionResolverRef.target
          (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
            currentSelectionSet))
        hnonObject hruntimeObject hleftFree hleftNormal
  have hleftApply :
      Execution.doesFragmentTypeApplyBool schema runtimeType leftSource
          runtimeType =
        true := by
    dsimp [leftSource]
    simpa [projectionTargetResolverValue, projectionResolverValue] using
      doesFragmentTypeApplyBool_object_self schema
        (ref :=
          ProjectionResolverRef.target
            (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
              currentSelectionSet))
        hruntimeObject
  have hleftFlatten :
      Execution.executeSelectionSet schema resolvers variableValues
        (fuel + 1) runtimeType leftSource
        [Selection.inlineFragment (some runtimeType) []
          leftBodySelectionSet]
      =
      Execution.executeSelectionSet schema resolvers variableValues
        (fuel + 1) runtimeType leftSource leftBodySelectionSet := by
    simpa using
      executeSelectionSet_inlineFragment_some_directiveFree_apply_flatten
        schema resolvers variableValues (fuel + 1) runtimeType runtimeType
        leftSource leftBodySelectionSet [] hleftApply
  have hrightCollect :
      Execution.collectFields schema variableValues runtimeType rightSource
        right = [] := by
    dsimp [rightSource]
    simpa [projectionTargetResolverValue, projectionResolverValue] using
      collectFields_inlineFragments_without_typeCondition_eq_nil_at_runtime_parent
        (schema := schema) (variableValues := variableValues)
        (normalParentType := normalParentType)
        (executionParentType := runtimeType) (runtimeType := runtimeType)
        (ref :=
          ProjectionResolverRef.target
            (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
              currentSelectionSet))
        hnonObject hrightFree hrightNormal hrightNoTypeCondition
  have hrightResponse :
      Execution.executeSelectionSetAsResponse schema resolvers variableValues
          (fuel + 1) runtimeType rightSource right =
        ({ data := Execution.ResponseValue.object [], errors := 0 } :
          Execution.Response) := by
    simp [Execution.executeSelectionSetAsResponse, Execution.selectionSetResultToResponse,
      Execution.executeSelectionSet, Execution.executeRootSelectionSet,
      hrightCollect, Execution.executeCollectedFields]
  have hsemantic' := hsemantic
  rw [hrightResponse] at hsemantic'
  apply hbodyNot
  simpa [Execution.executeSelectionSetAsResponse, resolvers, leftSource, rightSource,
    hleftMiddle, hleftFlatten] using hsemantic'

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_right_abstract_typeCondition_body
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet currentSelectionSet
      : List Selection)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField normalParentType runtimeType : Name)
    (leftArguments rightArguments : List Argument) (leftRuntime rightRuntime : Name)
    {left right rightBodySelectionSet : List Selection}
    {rightDirectives : List DirectiveApplication}
    : objectTypeNameBool schema normalParentType = false
      -> objectTypeNameBool schema runtimeType = true
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema normalParentType left
      -> selectionSetNormal schema normalParentType right
      -> Selection.inlineFragment (some runtimeType) rightDirectives rightBodySelectionSet
          ∈ right
      -> runtimeType ∉ left.filterMap inlineFragmentTypeCondition?
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.ResponseValue.object [])
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet targetParent leftField rightField
                  leftArguments rightArguments leftRuntime rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) runtimeType
              (projectionTargetResolverValue
                (.object runtimeType
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                    currentSelectionSet)))
              rightBodySelectionSet).data
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet targetParent leftField rightField
                  leftArguments rightArguments leftRuntime rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) runtimeType
              (projectionTargetResolverValue
                (.object runtimeType
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                    currentSelectionSet)))
              left).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet targetParent leftField rightField
                  leftArguments rightArguments leftRuntime rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) runtimeType
              (projectionTargetResolverValue
                (.object runtimeType
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                    currentSelectionSet)))
              right).data := by
  intro hnonObject hruntimeObject hleftFree hrightFree hleftNormal
    hrightNormal hrightMem hleftNoTypeCondition hbodyNot hsemantic
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet
      (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
        rightInitialSelectionSet targetParent leftField rightField
        leftArguments rightArguments leftRuntime rightRuntime)
      targetParent leftField rightField leftArguments rightArguments
  let leftSource :=
    projectionTargetResolverValue
      (.object runtimeType
        (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
          currentSelectionSet))
  let rightSource :=
    projectionTargetResolverValue
      (.object runtimeType
        (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
          currentSelectionSet))
  have hrightDirectives : rightDirectives = [] :=
    selectionSetDirectiveFree_inlineFragment_directives_nil_of_mem
      hrightFree hrightMem
  subst rightDirectives
  rcases List.mem_iff_append.mp hrightMem with
    ⟨rightPref, rightSuffix, hrightSelectionSet⟩
  subst right
  have hrightMiddle :
      Execution.executeSelectionSet schema resolvers variableValues
        (fuel + 1) runtimeType rightSource
        (rightPref ++ Selection.inlineFragment (some runtimeType) []
          rightBodySelectionSet :: rightSuffix)
      =
      Execution.executeSelectionSet schema resolvers variableValues
        (fuel + 1) runtimeType rightSource
        [Selection.inlineFragment (some runtimeType) []
          rightBodySelectionSet] := by
    dsimp [rightSource]
    simpa [projectionTargetResolverValue, projectionResolverValue] using
      executeSelectionSet_middle_inlineFragment_only_eq_singleton_at_runtime_parent
        schema resolvers variableValues (fuel + 1)
        (ProjectionResolverRef.target
          (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
            currentSelectionSet))
        hnonObject hruntimeObject hrightFree hrightNormal
  have hrightApply :
      Execution.doesFragmentTypeApplyBool schema runtimeType rightSource
          runtimeType =
        true := by
    dsimp [rightSource]
    simpa [projectionTargetResolverValue, projectionResolverValue] using
      doesFragmentTypeApplyBool_object_self schema
        (ref :=
          ProjectionResolverRef.target
            (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
              currentSelectionSet))
        hruntimeObject
  have hrightFlatten :
      Execution.executeSelectionSet schema resolvers variableValues
        (fuel + 1) runtimeType rightSource
        [Selection.inlineFragment (some runtimeType) []
          rightBodySelectionSet]
      =
      Execution.executeSelectionSet schema resolvers variableValues
        (fuel + 1) runtimeType rightSource rightBodySelectionSet := by
    simpa using
      executeSelectionSet_inlineFragment_some_directiveFree_apply_flatten
        schema resolvers variableValues (fuel + 1) runtimeType runtimeType
        rightSource rightBodySelectionSet [] hrightApply
  have hleftCollect :
      Execution.collectFields schema variableValues runtimeType leftSource
        left = [] := by
    dsimp [leftSource]
    simpa [projectionTargetResolverValue, projectionResolverValue] using
      collectFields_inlineFragments_without_typeCondition_eq_nil_at_runtime_parent
        (schema := schema) (variableValues := variableValues)
        (normalParentType := normalParentType)
        (executionParentType := runtimeType) (runtimeType := runtimeType)
        (ref :=
          ProjectionResolverRef.target
            (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
              currentSelectionSet))
        hnonObject hleftFree hleftNormal hleftNoTypeCondition
  have hleftResponse :
      Execution.executeSelectionSetAsResponse schema resolvers variableValues
          (fuel + 1) runtimeType leftSource left =
        ({ data := Execution.ResponseValue.object [], errors := 0 } :
          Execution.Response) := by
    simp [Execution.executeSelectionSetAsResponse, Execution.selectionSetResultToResponse,
      Execution.executeSelectionSet, Execution.executeRootSelectionSet,
      hleftCollect, Execution.executeCollectedFields]
  have hsemantic' := hsemantic
  rw [hleftResponse] at hsemantic'
  apply hbodyNot
  simpa [Execution.executeSelectionSetAsResponse, resolvers, leftSource, rightSource,
    hrightMiddle, hrightFlatten] using hsemantic'

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_left_abstract_typeCondition_body_current_pair
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField normalParentType runtimeType : Name)
    (leftArguments rightArguments : List Argument) (leftRuntime rightRuntime : Name)
    {left right leftBodySelectionSet : List Selection}
    {leftDirectives : List DirectiveApplication}
    : objectTypeNameBool schema normalParentType = false
      -> objectTypeNameBool schema runtimeType = true
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema normalParentType left
      -> selectionSetNormal schema normalParentType right
      -> Selection.inlineFragment (some runtimeType) leftDirectives leftBodySelectionSet
          ∈ left
      -> runtimeType ∉ right.filterMap inlineFragmentTypeCondition?
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet targetParent leftField rightField
                  leftArguments rightArguments leftRuntime rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) runtimeType
              (projectionTargetResolverValue
                (.object runtimeType
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                    leftCurrentSelectionSet)))
              leftBodySelectionSet).data
            (Execution.ResponseValue.object [])
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet targetParent leftField rightField
                  leftArguments rightArguments leftRuntime rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) runtimeType
              (projectionTargetResolverValue
                (.object runtimeType
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                    leftCurrentSelectionSet)))
              left).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet targetParent leftField rightField
                  leftArguments rightArguments leftRuntime rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) runtimeType
              (projectionTargetResolverValue
                (.object runtimeType
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                    rightCurrentSelectionSet)))
              right).data := by
  intro hnonObject hruntimeObject hleftFree hrightFree hleftNormal
    hrightNormal hleftMem hrightNoTypeCondition hbodyNot hsemantic
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet
      (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
        rightInitialSelectionSet targetParent leftField rightField
        leftArguments rightArguments leftRuntime rightRuntime)
      targetParent leftField rightField leftArguments rightArguments
  let leftSource :=
    projectionTargetResolverValue
      (.object runtimeType
        (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
          leftCurrentSelectionSet))
  let rightSource :=
    projectionTargetResolverValue
      (.object runtimeType
        (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
          rightCurrentSelectionSet))
  have hleftDirectives : leftDirectives = [] :=
    selectionSetDirectiveFree_inlineFragment_directives_nil_of_mem
      hleftFree hleftMem
  subst leftDirectives
  rcases List.mem_iff_append.mp hleftMem with
    ⟨leftPref, leftSuffix, hleftSelectionSet⟩
  subst left
  have hleftMiddle :
      Execution.executeSelectionSet schema resolvers variableValues
        (fuel + 1) runtimeType leftSource
        (leftPref ++ Selection.inlineFragment (some runtimeType) []
          leftBodySelectionSet :: leftSuffix)
      =
      Execution.executeSelectionSet schema resolvers variableValues
        (fuel + 1) runtimeType leftSource
        [Selection.inlineFragment (some runtimeType) []
          leftBodySelectionSet] := by
    dsimp [leftSource]
    simpa [projectionTargetResolverValue, projectionResolverValue] using
      executeSelectionSet_middle_inlineFragment_only_eq_singleton_at_runtime_parent
        schema resolvers variableValues (fuel + 1)
        (ProjectionResolverRef.target
          (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
            leftCurrentSelectionSet))
        hnonObject hruntimeObject hleftFree hleftNormal
  have hleftApply :
      Execution.doesFragmentTypeApplyBool schema runtimeType leftSource
          runtimeType =
        true := by
    dsimp [leftSource]
    simpa [projectionTargetResolverValue, projectionResolverValue] using
      doesFragmentTypeApplyBool_object_self schema
        (ref :=
          ProjectionResolverRef.target
            (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
              leftCurrentSelectionSet))
        hruntimeObject
  have hleftFlatten :
      Execution.executeSelectionSet schema resolvers variableValues
        (fuel + 1) runtimeType leftSource
        [Selection.inlineFragment (some runtimeType) []
          leftBodySelectionSet]
      =
      Execution.executeSelectionSet schema resolvers variableValues
        (fuel + 1) runtimeType leftSource leftBodySelectionSet := by
    simpa using
      executeSelectionSet_inlineFragment_some_directiveFree_apply_flatten
        schema resolvers variableValues (fuel + 1) runtimeType runtimeType
        leftSource leftBodySelectionSet [] hleftApply
  have hrightCollect :
      Execution.collectFields schema variableValues runtimeType rightSource
        right = [] := by
    dsimp [rightSource]
    simpa [projectionTargetResolverValue, projectionResolverValue] using
      collectFields_inlineFragments_without_typeCondition_eq_nil_at_runtime_parent
        (schema := schema) (variableValues := variableValues)
        (normalParentType := normalParentType)
        (executionParentType := runtimeType) (runtimeType := runtimeType)
        (ref :=
          ProjectionResolverRef.target
            (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
              rightCurrentSelectionSet))
        hnonObject hrightFree hrightNormal hrightNoTypeCondition
  have hrightResponse :
      Execution.executeSelectionSetAsResponse schema resolvers variableValues
          (fuel + 1) runtimeType rightSource right =
        ({ data := Execution.ResponseValue.object [], errors := 0 } :
          Execution.Response) := by
    simp [Execution.executeSelectionSetAsResponse, Execution.selectionSetResultToResponse,
      Execution.executeSelectionSet, Execution.executeRootSelectionSet,
      hrightCollect, Execution.executeCollectedFields]
  have hsemantic' := hsemantic
  rw [hrightResponse] at hsemantic'
  apply hbodyNot
  simpa [Execution.executeSelectionSetAsResponse, resolvers, leftSource, rightSource,
    hleftMiddle, hleftFlatten] using hsemantic'

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_right_abstract_typeCondition_body_current_pair
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField normalParentType runtimeType : Name)
    (leftArguments rightArguments : List Argument) (leftRuntime rightRuntime : Name)
    {left right rightBodySelectionSet : List Selection}
    {rightDirectives : List DirectiveApplication}
    : objectTypeNameBool schema normalParentType = false
      -> objectTypeNameBool schema runtimeType = true
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema normalParentType left
      -> selectionSetNormal schema normalParentType right
      -> Selection.inlineFragment (some runtimeType) rightDirectives rightBodySelectionSet
          ∈ right
      -> runtimeType ∉ left.filterMap inlineFragmentTypeCondition?
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.ResponseValue.object [])
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet targetParent leftField rightField
                  leftArguments rightArguments leftRuntime rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) runtimeType
              (projectionTargetResolverValue
                (.object runtimeType
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                    rightCurrentSelectionSet)))
              rightBodySelectionSet).data
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet targetParent leftField rightField
                  leftArguments rightArguments leftRuntime rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) runtimeType
              (projectionTargetResolverValue
                (.object runtimeType
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                    leftCurrentSelectionSet)))
              left).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet targetParent leftField rightField
                  leftArguments rightArguments leftRuntime rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) runtimeType
              (projectionTargetResolverValue
                (.object runtimeType
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                    rightCurrentSelectionSet)))
              right).data := by
  intro hnonObject hruntimeObject hleftFree hrightFree hleftNormal
    hrightNormal hrightMem hleftNoTypeCondition hbodyNot hsemantic
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet
      (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
        rightInitialSelectionSet targetParent leftField rightField
        leftArguments rightArguments leftRuntime rightRuntime)
      targetParent leftField rightField leftArguments rightArguments
  let leftSource :=
    projectionTargetResolverValue
      (.object runtimeType
        (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
          leftCurrentSelectionSet))
  let rightSource :=
    projectionTargetResolverValue
      (.object runtimeType
        (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
          rightCurrentSelectionSet))
  have hrightDirectives : rightDirectives = [] :=
    selectionSetDirectiveFree_inlineFragment_directives_nil_of_mem
      hrightFree hrightMem
  subst rightDirectives
  rcases List.mem_iff_append.mp hrightMem with
    ⟨rightPref, rightSuffix, hrightSelectionSet⟩
  subst right
  have hrightMiddle :
      Execution.executeSelectionSet schema resolvers variableValues
        (fuel + 1) runtimeType rightSource
        (rightPref ++ Selection.inlineFragment (some runtimeType) []
          rightBodySelectionSet :: rightSuffix)
      =
      Execution.executeSelectionSet schema resolvers variableValues
        (fuel + 1) runtimeType rightSource
        [Selection.inlineFragment (some runtimeType) []
          rightBodySelectionSet] := by
    dsimp [rightSource]
    simpa [projectionTargetResolverValue, projectionResolverValue] using
      executeSelectionSet_middle_inlineFragment_only_eq_singleton_at_runtime_parent
        schema resolvers variableValues (fuel + 1)
        (ProjectionResolverRef.target
          (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
            rightCurrentSelectionSet))
        hnonObject hruntimeObject hrightFree hrightNormal
  have hrightApply :
      Execution.doesFragmentTypeApplyBool schema runtimeType rightSource
          runtimeType =
        true := by
    dsimp [rightSource]
    simpa [projectionTargetResolverValue, projectionResolverValue] using
      doesFragmentTypeApplyBool_object_self schema
        (ref :=
          ProjectionResolverRef.target
            (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
              rightCurrentSelectionSet))
        hruntimeObject
  have hrightFlatten :
      Execution.executeSelectionSet schema resolvers variableValues
        (fuel + 1) runtimeType rightSource
        [Selection.inlineFragment (some runtimeType) []
          rightBodySelectionSet]
      =
      Execution.executeSelectionSet schema resolvers variableValues
        (fuel + 1) runtimeType rightSource rightBodySelectionSet := by
    simpa using
      executeSelectionSet_inlineFragment_some_directiveFree_apply_flatten
        schema resolvers variableValues (fuel + 1) runtimeType runtimeType
        rightSource rightBodySelectionSet [] hrightApply
  have hleftCollect :
      Execution.collectFields schema variableValues runtimeType leftSource
        left = [] := by
    dsimp [leftSource]
    simpa [projectionTargetResolverValue, projectionResolverValue] using
      collectFields_inlineFragments_without_typeCondition_eq_nil_at_runtime_parent
        (schema := schema) (variableValues := variableValues)
        (normalParentType := normalParentType)
        (executionParentType := runtimeType) (runtimeType := runtimeType)
        (ref :=
          ProjectionResolverRef.target
            (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
              leftCurrentSelectionSet))
        hnonObject hleftFree hleftNormal hleftNoTypeCondition
  have hleftResponse :
      Execution.executeSelectionSetAsResponse schema resolvers variableValues
          (fuel + 1) runtimeType leftSource left =
        ({ data := Execution.ResponseValue.object [], errors := 0 } :
          Execution.Response) := by
    simp [Execution.executeSelectionSetAsResponse, Execution.selectionSetResultToResponse,
      Execution.executeSelectionSet, Execution.executeRootSelectionSet,
      hleftCollect, Execution.executeCollectedFields]
  have hsemantic' := hsemantic
  rw [hleftResponse] at hsemantic'
  apply hbodyNot
  simpa [Execution.executeSelectionSetAsResponse, resolvers, leftSource, rightSource,
    hrightMiddle, hrightFlatten] using hsemantic'

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_left_abstract_inlineFragment_of_valid_normal
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet currentSelectionSet
      : List Selection)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField normalParentType runtimeType : Name)
    (leftArguments rightArguments : List Argument) (leftRuntime rightRuntime : Name)
    {left right leftBodySelectionSet : List Selection}
    {leftDirectives : List DirectiveApplication}
    : objectTypeNameBool schema normalParentType = false
      -> objectTypeNameBool schema runtimeType = true
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema normalParentType left
      -> selectionSetNormal schema normalParentType right
      -> Selection.inlineFragment (some runtimeType) leftDirectives leftBodySelectionSet
          ∈ left
      -> (runtimeType ∉ right.filterMap inlineFragmentTypeCondition?
          -> ¬ Execution.ResponseValue.semanticEquivalent
                (Execution.executeSelectionSetAsResponse schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                      rightInitialSelectionSet targetParent leftField rightField
                      leftArguments rightArguments leftRuntime rightRuntime)
                    targetParent leftField rightField leftArguments rightArguments)
                  variableValues (fuel + 1) runtimeType
                  (projectionTargetResolverValue
                    (.object runtimeType
                      (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                        currentSelectionSet)))
                  leftBodySelectionSet).data
                (Execution.ResponseValue.object []))
      -> (∀ {rightDirectives rightBodySelectionSet},
            Selection.inlineFragment (some runtimeType) rightDirectives
                rightBodySelectionSet
              ∈ right
            -> ¬ Execution.ResponseValue.semanticEquivalent
                  (Execution.executeSelectionSetAsResponse schema
                    (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                      (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                        rightInitialSelectionSet targetParent leftField rightField
                        leftArguments rightArguments leftRuntime rightRuntime)
                      targetParent leftField rightField leftArguments rightArguments)
                    variableValues (fuel + 1) runtimeType
                    (projectionTargetResolverValue
                      (.object runtimeType
                        (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                          currentSelectionSet)))
                    leftBodySelectionSet).data
                  (Execution.executeSelectionSetAsResponse schema
                    (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                      (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                        rightInitialSelectionSet targetParent leftField rightField
                        leftArguments rightArguments leftRuntime rightRuntime)
                      targetParent leftField rightField leftArguments rightArguments)
                    variableValues (fuel + 1) runtimeType
                    (projectionTargetResolverValue
                      (.object runtimeType
                        (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                          currentSelectionSet)))
                    rightBodySelectionSet).data)
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet targetParent leftField rightField
                  leftArguments rightArguments leftRuntime rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) runtimeType
              (projectionTargetResolverValue
                (.object runtimeType
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                    currentSelectionSet)))
              left).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet targetParent leftField rightField
                  leftArguments rightArguments leftRuntime rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) runtimeType
              (projectionTargetResolverValue
                (.object runtimeType
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                    currentSelectionSet)))
              right).data := by
  intro hnonObject hruntimeObject hleftFree hrightFree hleftNormal
    hrightNormal hleftMem hmissing hmatching
  by_cases hrightTypeCondition :
      runtimeType ∈ right.filterMap inlineFragmentTypeCondition?
  · rcases
        selectionSetNormal_inlineFragment_mem_of_abstract_typeCondition_mem
          hrightNormal hnonObject hrightTypeCondition with
      ⟨rightDirectives, rightBodySelectionSet, hrightMem⟩
    exact
      responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_abstract_inlineFragment_body_pair
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet currentSelectionSet variableValues fuel
        targetParent leftField rightField normalParentType runtimeType
        leftArguments rightArguments leftRuntime rightRuntime hnonObject
        hruntimeObject hleftFree hrightFree hleftNormal hrightNormal
        hleftMem hrightMem (hmatching hrightMem)
  · exact
      responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_left_abstract_typeCondition_body
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet currentSelectionSet variableValues fuel
        targetParent leftField rightField normalParentType runtimeType
        leftArguments rightArguments leftRuntime rightRuntime hnonObject
        hruntimeObject hleftFree hrightFree hleftNormal hrightNormal
        hleftMem hrightTypeCondition (hmissing hrightTypeCondition)

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_right_abstract_inlineFragment_of_valid_normal
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet currentSelectionSet
      : List Selection)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField normalParentType runtimeType : Name)
    (leftArguments rightArguments : List Argument) (leftRuntime rightRuntime : Name)
    {left right rightBodySelectionSet : List Selection}
    {rightDirectives : List DirectiveApplication}
    : objectTypeNameBool schema normalParentType = false
      -> objectTypeNameBool schema runtimeType = true
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema normalParentType left
      -> selectionSetNormal schema normalParentType right
      -> Selection.inlineFragment (some runtimeType) rightDirectives rightBodySelectionSet
          ∈ right
      -> (runtimeType ∉ left.filterMap inlineFragmentTypeCondition?
          -> ¬ Execution.ResponseValue.semanticEquivalent
                (Execution.ResponseValue.object [])
                (Execution.executeSelectionSetAsResponse schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                      rightInitialSelectionSet targetParent leftField rightField
                      leftArguments rightArguments leftRuntime rightRuntime)
                    targetParent leftField rightField leftArguments rightArguments)
                  variableValues (fuel + 1) runtimeType
                  (projectionTargetResolverValue
                    (.object runtimeType
                      (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                        currentSelectionSet)))
                  rightBodySelectionSet).data)
      -> (∀ {leftDirectives leftBodySelectionSet},
            Selection.inlineFragment (some runtimeType) leftDirectives
                leftBodySelectionSet
              ∈ left
            -> ¬ Execution.ResponseValue.semanticEquivalent
                  (Execution.executeSelectionSetAsResponse schema
                    (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                      (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                        rightInitialSelectionSet targetParent leftField rightField
                        leftArguments rightArguments leftRuntime rightRuntime)
                      targetParent leftField rightField leftArguments rightArguments)
                    variableValues (fuel + 1) runtimeType
                    (projectionTargetResolverValue
                      (.object runtimeType
                        (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                          currentSelectionSet)))
                    leftBodySelectionSet).data
                  (Execution.executeSelectionSetAsResponse schema
                    (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                      (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                        rightInitialSelectionSet targetParent leftField rightField
                        leftArguments rightArguments leftRuntime rightRuntime)
                      targetParent leftField rightField leftArguments rightArguments)
                    variableValues (fuel + 1) runtimeType
                    (projectionTargetResolverValue
                      (.object runtimeType
                        (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                          currentSelectionSet)))
                    rightBodySelectionSet).data)
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet targetParent leftField rightField
                  leftArguments rightArguments leftRuntime rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) runtimeType
              (projectionTargetResolverValue
                (.object runtimeType
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                    currentSelectionSet)))
              left).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet targetParent leftField rightField
                  leftArguments rightArguments leftRuntime rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) runtimeType
              (projectionTargetResolverValue
                (.object runtimeType
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                    currentSelectionSet)))
              right).data := by
  intro hnonObject hruntimeObject hleftFree hrightFree hleftNormal
    hrightNormal hrightMem hmissing hmatching
  by_cases hleftTypeCondition :
      runtimeType ∈ left.filterMap inlineFragmentTypeCondition?
  · rcases
        selectionSetNormal_inlineFragment_mem_of_abstract_typeCondition_mem
          hleftNormal hnonObject hleftTypeCondition with
      ⟨leftDirectives, leftBodySelectionSet, hleftMem⟩
    exact
      responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_abstract_inlineFragment_body_pair
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet currentSelectionSet variableValues fuel
        targetParent leftField rightField normalParentType runtimeType
        leftArguments rightArguments leftRuntime rightRuntime hnonObject
        hruntimeObject hleftFree hrightFree hleftNormal hrightNormal
        hleftMem hrightMem (hmatching hleftMem)
  · exact
      responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_right_abstract_typeCondition_body
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet currentSelectionSet variableValues fuel
        targetParent leftField rightField normalParentType runtimeType
        leftArguments rightArguments leftRuntime rightRuntime hnonObject
        hruntimeObject hleftFree hrightFree hleftNormal hrightNormal
        hrightMem hleftTypeCondition (hmissing hleftTypeCondition)

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_left_abstract_inlineFragment_of_valid_normal_current_pair
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField normalParentType runtimeType : Name)
    (leftArguments rightArguments : List Argument) (leftRuntime rightRuntime : Name)
    {left right leftBodySelectionSet : List Selection}
    {leftDirectives : List DirectiveApplication}
    : objectTypeNameBool schema normalParentType = false
      -> objectTypeNameBool schema runtimeType = true
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema normalParentType left
      -> selectionSetNormal schema normalParentType right
      -> Selection.inlineFragment (some runtimeType) leftDirectives leftBodySelectionSet
          ∈ left
      -> (runtimeType ∉ right.filterMap inlineFragmentTypeCondition?
          -> ¬ Execution.ResponseValue.semanticEquivalent
                (Execution.executeSelectionSetAsResponse schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                      rightInitialSelectionSet targetParent leftField rightField
                      leftArguments rightArguments leftRuntime rightRuntime)
                    targetParent leftField rightField leftArguments rightArguments)
                  variableValues (fuel + 1) runtimeType
                  (projectionTargetResolverValue
                    (.object runtimeType
                      (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                        leftCurrentSelectionSet)))
                  leftBodySelectionSet).data
                (Execution.ResponseValue.object []))
      -> (∀ {rightDirectives rightBodySelectionSet},
            Selection.inlineFragment (some runtimeType) rightDirectives
                rightBodySelectionSet
              ∈ right
            -> ¬ Execution.ResponseValue.semanticEquivalent
                  (Execution.executeSelectionSetAsResponse schema
                    (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                      (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                        rightInitialSelectionSet targetParent leftField rightField
                        leftArguments rightArguments leftRuntime rightRuntime)
                      targetParent leftField rightField leftArguments rightArguments)
                    variableValues (fuel + 1) runtimeType
                    (projectionTargetResolverValue
                      (.object runtimeType
                        (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                          leftCurrentSelectionSet)))
                    leftBodySelectionSet).data
                  (Execution.executeSelectionSetAsResponse schema
                    (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                      (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                        rightInitialSelectionSet targetParent leftField rightField
                        leftArguments rightArguments leftRuntime rightRuntime)
                      targetParent leftField rightField leftArguments rightArguments)
                    variableValues (fuel + 1) runtimeType
                    (projectionTargetResolverValue
                      (.object runtimeType
                        (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                          rightCurrentSelectionSet)))
                    rightBodySelectionSet).data)
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet targetParent leftField rightField
                  leftArguments rightArguments leftRuntime rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) runtimeType
              (projectionTargetResolverValue
                (.object runtimeType
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                    leftCurrentSelectionSet)))
              left).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet targetParent leftField rightField
                  leftArguments rightArguments leftRuntime rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) runtimeType
              (projectionTargetResolverValue
                (.object runtimeType
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                    rightCurrentSelectionSet)))
              right).data := by
  intro hnonObject hruntimeObject hleftFree hrightFree hleftNormal
    hrightNormal hleftMem hmissing hmatching
  by_cases hrightTypeCondition :
      runtimeType ∈ right.filterMap inlineFragmentTypeCondition?
  · rcases
        selectionSetNormal_inlineFragment_mem_of_abstract_typeCondition_mem
          hrightNormal hnonObject hrightTypeCondition with
      ⟨rightDirectives, rightBodySelectionSet, hrightMem⟩
    exact
      responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_abstract_inlineFragment_body_pair_current_pair
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftCurrentSelectionSet
        rightCurrentSelectionSet variableValues fuel targetParent leftField
        rightField normalParentType runtimeType leftArguments rightArguments
        leftRuntime rightRuntime hnonObject hruntimeObject hleftFree
        hrightFree hleftNormal hrightNormal hleftMem hrightMem
        (hmatching hrightMem)
  · exact
      responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_left_abstract_typeCondition_body_current_pair
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftCurrentSelectionSet
        rightCurrentSelectionSet variableValues fuel targetParent leftField
        rightField normalParentType runtimeType leftArguments rightArguments
        leftRuntime rightRuntime hnonObject hruntimeObject hleftFree
        hrightFree hleftNormal hrightNormal hleftMem hrightTypeCondition
        (hmissing hrightTypeCondition)

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_right_abstract_inlineFragment_of_valid_normal_current_pair
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField normalParentType runtimeType : Name)
    (leftArguments rightArguments : List Argument) (leftRuntime rightRuntime : Name)
    {left right rightBodySelectionSet : List Selection}
    {rightDirectives : List DirectiveApplication}
    : objectTypeNameBool schema normalParentType = false
      -> objectTypeNameBool schema runtimeType = true
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema normalParentType left
      -> selectionSetNormal schema normalParentType right
      -> Selection.inlineFragment (some runtimeType) rightDirectives rightBodySelectionSet
          ∈ right
      -> (runtimeType ∉ left.filterMap inlineFragmentTypeCondition?
          -> ¬ Execution.ResponseValue.semanticEquivalent
                (Execution.ResponseValue.object [])
                (Execution.executeSelectionSetAsResponse schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                      rightInitialSelectionSet targetParent leftField rightField
                      leftArguments rightArguments leftRuntime rightRuntime)
                    targetParent leftField rightField leftArguments rightArguments)
                  variableValues (fuel + 1) runtimeType
                  (projectionTargetResolverValue
                    (.object runtimeType
                      (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                        rightCurrentSelectionSet)))
                  rightBodySelectionSet).data)
      -> (∀ {leftDirectives leftBodySelectionSet},
            Selection.inlineFragment (some runtimeType) leftDirectives
                leftBodySelectionSet
              ∈ left
            -> ¬ Execution.ResponseValue.semanticEquivalent
                  (Execution.executeSelectionSetAsResponse schema
                    (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                      (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                        rightInitialSelectionSet targetParent leftField rightField
                        leftArguments rightArguments leftRuntime rightRuntime)
                      targetParent leftField rightField leftArguments rightArguments)
                    variableValues (fuel + 1) runtimeType
                    (projectionTargetResolverValue
                      (.object runtimeType
                        (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                          leftCurrentSelectionSet)))
                    leftBodySelectionSet).data
                  (Execution.executeSelectionSetAsResponse schema
                    (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                      (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                        rightInitialSelectionSet targetParent leftField rightField
                        leftArguments rightArguments leftRuntime rightRuntime)
                      targetParent leftField rightField leftArguments rightArguments)
                    variableValues (fuel + 1) runtimeType
                    (projectionTargetResolverValue
                      (.object runtimeType
                        (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                          rightCurrentSelectionSet)))
                    rightBodySelectionSet).data)
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet targetParent leftField rightField
                  leftArguments rightArguments leftRuntime rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) runtimeType
              (projectionTargetResolverValue
                (.object runtimeType
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                    leftCurrentSelectionSet)))
              left).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet targetParent leftField rightField
                  leftArguments rightArguments leftRuntime rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) runtimeType
              (projectionTargetResolverValue
                (.object runtimeType
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                    rightCurrentSelectionSet)))
              right).data := by
  intro hnonObject hruntimeObject hleftFree hrightFree hleftNormal
    hrightNormal hrightMem hmissing hmatching
  by_cases hleftTypeCondition :
      runtimeType ∈ left.filterMap inlineFragmentTypeCondition?
  · rcases
        selectionSetNormal_inlineFragment_mem_of_abstract_typeCondition_mem
          hleftNormal hnonObject hleftTypeCondition with
      ⟨leftDirectives, leftBodySelectionSet, hleftMem⟩
    exact
      responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_abstract_inlineFragment_body_pair_current_pair
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftCurrentSelectionSet
        rightCurrentSelectionSet variableValues fuel targetParent leftField
        rightField normalParentType runtimeType leftArguments rightArguments
        leftRuntime rightRuntime hnonObject hruntimeObject hleftFree
        hrightFree hleftNormal hrightNormal hleftMem hrightMem
        (hmatching hleftMem)
  · exact
      responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_right_abstract_typeCondition_body_current_pair
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftCurrentSelectionSet
        rightCurrentSelectionSet variableValues fuel targetParent leftField
        rightField normalParentType runtimeType leftArguments rightArguments
        leftRuntime rightRuntime hnonObject hruntimeObject hleftFree
        hrightFree hleftNormal hrightNormal hrightMem hleftTypeCondition
        (hmissing hleftTypeCondition)

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_left_abstract_inlineFragment_of_valid_normal_support_context_fuel_ge
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField normalParentType runtimeType : Name)
    (leftArguments rightArguments : List Argument) (leftRuntime rightRuntime : Name)
    {left right leftBodySelectionSet : List Selection}
    {leftDirectives : List DirectiveApplication}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions normalParentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions
          normalParentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema normalParentType left
      -> selectionSetNormal schema normalParentType right
      -> objectTypeNameBool schema normalParentType = false
      -> objectTypeNameBool schema runtimeType = true
      -> schema.typeIncludesObjectBool normalParentType runtimeType = true
      -> selectionSetDeepProbeFuel schema normalParentType left ≤ fuel
      -> selectionSetDeepProbeFuel schema normalParentType right ≤ fuel
      -> PathLocalSupportValidNormal schema runtimeType leftCurrentSelectionSet
      -> PathLocalSupportValidNormal schema runtimeType rightCurrentSelectionSet
      -> (∀ {bodyDirectives bodySelectionSet},
            Selection.inlineFragment (some runtimeType) bodyDirectives bodySelectionSet
              ∈ left
            -> PathLocalSelectionSetCurrentContext bodySelectionSet
                leftCurrentSelectionSet)
      -> (∀ {bodyDirectives bodySelectionSet},
            Selection.inlineFragment (some runtimeType) bodyDirectives bodySelectionSet
              ∈ right
            -> PathLocalSelectionSetCurrentContext bodySelectionSet
                rightCurrentSelectionSet)
      -> Selection.inlineFragment (some runtimeType) leftDirectives leftBodySelectionSet
          ∈ left
      -> (∀ {rightDirectives rightBodySelectionSet},
            Selection.inlineFragment (some runtimeType) rightDirectives
                rightBodySelectionSet
              ∈ right
            -> ¬ Execution.ResponseValue.semanticEquivalent
                  (Execution.executeSelectionSetAsResponse schema
                    (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                      (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                        rightInitialSelectionSet targetParent leftField rightField
                        leftArguments rightArguments leftRuntime rightRuntime)
                      targetParent leftField rightField leftArguments
                      rightArguments)
                    variableValues (fuel + 1) runtimeType
                    (projectionTargetResolverValue
                      (.object runtimeType
                        (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                          leftCurrentSelectionSet)))
                    leftBodySelectionSet).data
                  (Execution.executeSelectionSetAsResponse schema
                    (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                      (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                        rightInitialSelectionSet targetParent leftField rightField
                        leftArguments rightArguments leftRuntime rightRuntime)
                      targetParent leftField rightField leftArguments
                      rightArguments)
                    variableValues (fuel + 1) runtimeType
                    (projectionTargetResolverValue
                      (.object runtimeType
                        (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                          rightCurrentSelectionSet)))
                    rightBodySelectionSet).data)
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet targetParent leftField rightField
                  leftArguments rightArguments leftRuntime rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) runtimeType
              (projectionTargetResolverValue
                (.object runtimeType
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                    leftCurrentSelectionSet)))
              left).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet targetParent leftField rightField
                  leftArguments rightArguments leftRuntime rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) runtimeType
              (projectionTargetResolverValue
                (.object runtimeType
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                    rightCurrentSelectionSet)))
              right).data := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hnonObject hruntimeObject _hinclude hleftFuel
    _hrightFuel hleftSupport _hrightSupport hleftContext _hrightContext
    hleftMem hmatching
  have hleftBodyValid :
      Validation.selectionSetValid schema leftVariableDefinitions runtimeType
        leftBodySelectionSet :=
    selectionSetValid_inlineFragment_some_child_of_mem hleftValid hleftMem
  have hleftBodyNonempty : leftBodySelectionSet ≠ [] :=
    selectionSetValid_inlineFragment_some_child_nonempty_of_mem hleftValid
      hleftMem
  have hleftBodyFree : selectionSetDirectiveFree leftBodySelectionSet :=
    selectionSetDirectiveFree_inlineFragment_child_of_mem hleftFree hleftMem
  rcases selectionSetNormal_inlineFragment_child_of_mem hleftNormal
      hleftMem with
    ⟨_htypeObject, hleftBodyNormal⟩
  have hleftBodyFuel :
      selectionSetDeepProbeFuel schema runtimeType leftBodySelectionSet ≤
        fuel := by
    have hlocal :=
      selectionSetDeepProbeFuel_inlineFragment_some_mem schema
        normalParentType left runtimeType leftDirectives leftBodySelectionSet
        hleftMem
    omega
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet
      (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
        rightInitialSelectionSet targetParent leftField rightField
        leftArguments rightArguments leftRuntime rightRuntime)
      targetParent leftField rightField leftArguments rightArguments
  let leftSource :=
    projectionTargetResolverValue
      (.object runtimeType
        (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
          leftCurrentSelectionSet))
  have hmissing :
      runtimeType ∉ right.filterMap inlineFragmentTypeCondition? ->
      ¬ Execution.ResponseValue.semanticEquivalent
        (Execution.executeSelectionSetAsResponse schema
          (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
            (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
              rightInitialSelectionSet targetParent leftField rightField
              leftArguments rightArguments leftRuntime rightRuntime)
            targetParent leftField rightField leftArguments rightArguments)
          variableValues (fuel + 1) runtimeType
          (projectionTargetResolverValue
            (.object runtimeType
              (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                leftCurrentSelectionSet)))
          leftBodySelectionSet).data
        (Execution.ResponseValue.object []) := by
    intro _hrightNoType
    have hbodyInclude :
        schema.typeIncludesObjectBool runtimeType runtimeType = true :=
      typeIncludesObjectBool_self_of_objectTypeNameBool schema
        hruntimeObject
    rcases
        executeSelectionSetAsResponse_fieldPairOrDeepSuccess_pathLocalProbe_tagged_of_valid_normal_support_context_fuel_ge_size
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet variableValues hschema
          (SelectionSet.size leftBodySelectionSet + 1) runtimeType
          leftVariableDefinitions leftBodySelectionSet fuel runtimeType
          targetParent leftField rightField leftArguments rightArguments
          leftRuntime rightRuntime FieldPairProbeTag.left
          leftCurrentSelectionSet (by omega) hleftBodyFuel
          hleftBodyValid hleftBodyFree hleftBodyNormal hbodyInclude
          hleftSupport (fun _hobject => hleftContext hleftMem)
          (fun hbodyNonObject => by
            rw [hruntimeObject] at hbodyNonObject
            simp at hbodyNonObject) with
      ⟨leftBodyFields, leftBodyErrors, hleftBodyResponse⟩
    have hnot :=
      responseData_not_semanticEquivalent_empty_object_of_valid_normal_object_nonempty_response
        schema resolvers variableValues (fuel + 1) runtimeType leftSource
        hruntimeObject hleftBodyFree hleftBodyNormal hleftBodyNonempty
        (fields := leftBodyFields) (errors := leftBodyErrors)
        (by simpa [resolvers, leftSource] using hleftBodyResponse)
    simpa [resolvers, leftSource] using hnot
  exact
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_left_abstract_inlineFragment_of_valid_normal_current_pair
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet leftCurrentSelectionSet
      rightCurrentSelectionSet variableValues fuel targetParent leftField
      rightField normalParentType runtimeType leftArguments rightArguments
      leftRuntime rightRuntime hnonObject hruntimeObject hleftFree
      hrightFree hleftNormal hrightNormal hleftMem hmissing hmatching

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_right_abstract_inlineFragment_of_valid_normal_support_context_fuel_ge
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField normalParentType runtimeType : Name)
    (leftArguments rightArguments : List Argument) (leftRuntime rightRuntime : Name)
    {left right rightBodySelectionSet : List Selection}
    {rightDirectives : List DirectiveApplication}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions normalParentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions
          normalParentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema normalParentType left
      -> selectionSetNormal schema normalParentType right
      -> objectTypeNameBool schema normalParentType = false
      -> objectTypeNameBool schema runtimeType = true
      -> schema.typeIncludesObjectBool normalParentType runtimeType = true
      -> selectionSetDeepProbeFuel schema normalParentType left ≤ fuel
      -> selectionSetDeepProbeFuel schema normalParentType right ≤ fuel
      -> PathLocalSupportValidNormal schema runtimeType leftCurrentSelectionSet
      -> PathLocalSupportValidNormal schema runtimeType rightCurrentSelectionSet
      -> (∀ {bodyDirectives bodySelectionSet},
            Selection.inlineFragment (some runtimeType) bodyDirectives bodySelectionSet
              ∈ left
            -> PathLocalSelectionSetCurrentContext bodySelectionSet
                leftCurrentSelectionSet)
      -> (∀ {bodyDirectives bodySelectionSet},
            Selection.inlineFragment (some runtimeType) bodyDirectives bodySelectionSet
              ∈ right
            -> PathLocalSelectionSetCurrentContext bodySelectionSet
                rightCurrentSelectionSet)
      -> Selection.inlineFragment (some runtimeType) rightDirectives rightBodySelectionSet
          ∈ right
      -> (∀ {leftDirectives leftBodySelectionSet},
            Selection.inlineFragment (some runtimeType) leftDirectives
                leftBodySelectionSet
              ∈ left
            -> ¬ Execution.ResponseValue.semanticEquivalent
                  (Execution.executeSelectionSetAsResponse schema
                    (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                      (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                        rightInitialSelectionSet targetParent leftField rightField
                        leftArguments rightArguments leftRuntime rightRuntime)
                      targetParent leftField rightField leftArguments
                      rightArguments)
                    variableValues (fuel + 1) runtimeType
                    (projectionTargetResolverValue
                      (.object runtimeType
                        (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                          leftCurrentSelectionSet)))
                    leftBodySelectionSet).data
                  (Execution.executeSelectionSetAsResponse schema
                    (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                      (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                        rightInitialSelectionSet targetParent leftField rightField
                        leftArguments rightArguments leftRuntime rightRuntime)
                      targetParent leftField rightField leftArguments
                      rightArguments)
                    variableValues (fuel + 1) runtimeType
                    (projectionTargetResolverValue
                      (.object runtimeType
                        (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                          rightCurrentSelectionSet)))
                    rightBodySelectionSet).data)
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet targetParent leftField rightField
                  leftArguments rightArguments leftRuntime rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) runtimeType
              (projectionTargetResolverValue
                (.object runtimeType
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                    leftCurrentSelectionSet)))
              left).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet targetParent leftField rightField
                  leftArguments rightArguments leftRuntime rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) runtimeType
              (projectionTargetResolverValue
                (.object runtimeType
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                    rightCurrentSelectionSet)))
              right).data := by
  intro hschema _hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hnonObject hruntimeObject _hinclude _hleftFuel
    hrightFuel _hleftSupport hrightSupport _hleftContext hrightContext
    hrightMem hmatching
  have hrightBodyValid :
      Validation.selectionSetValid schema rightVariableDefinitions runtimeType
        rightBodySelectionSet :=
    selectionSetValid_inlineFragment_some_child_of_mem hrightValid
      hrightMem
  have hrightBodyNonempty : rightBodySelectionSet ≠ [] :=
    selectionSetValid_inlineFragment_some_child_nonempty_of_mem hrightValid
      hrightMem
  have hrightBodyFree : selectionSetDirectiveFree rightBodySelectionSet :=
    selectionSetDirectiveFree_inlineFragment_child_of_mem hrightFree
      hrightMem
  rcases selectionSetNormal_inlineFragment_child_of_mem hrightNormal
      hrightMem with
    ⟨_htypeObject, hrightBodyNormal⟩
  have hrightBodyFuel :
      selectionSetDeepProbeFuel schema runtimeType rightBodySelectionSet ≤
        fuel := by
    have hlocal :=
      selectionSetDeepProbeFuel_inlineFragment_some_mem schema
        normalParentType right runtimeType rightDirectives
        rightBodySelectionSet hrightMem
    omega
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet
      (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
        rightInitialSelectionSet targetParent leftField rightField
        leftArguments rightArguments leftRuntime rightRuntime)
      targetParent leftField rightField leftArguments rightArguments
  let rightSource :=
    projectionTargetResolverValue
      (.object runtimeType
        (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
          rightCurrentSelectionSet))
  have hmissing :
      runtimeType ∉ left.filterMap inlineFragmentTypeCondition? ->
      ¬ Execution.ResponseValue.semanticEquivalent
        (Execution.ResponseValue.object [])
        (Execution.executeSelectionSetAsResponse schema
          (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
            (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
              rightInitialSelectionSet targetParent leftField rightField
              leftArguments rightArguments leftRuntime rightRuntime)
            targetParent leftField rightField leftArguments rightArguments)
          variableValues (fuel + 1) runtimeType
          (projectionTargetResolverValue
            (.object runtimeType
              (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                rightCurrentSelectionSet)))
          rightBodySelectionSet).data := by
    intro _hleftNoType
    have hbodyInclude :
        schema.typeIncludesObjectBool runtimeType runtimeType = true :=
      typeIncludesObjectBool_self_of_objectTypeNameBool schema
        hruntimeObject
    rcases
        executeSelectionSetAsResponse_fieldPairOrDeepSuccess_pathLocalProbe_tagged_of_valid_normal_support_context_fuel_ge_size
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet variableValues hschema
          (SelectionSet.size rightBodySelectionSet + 1) runtimeType
          rightVariableDefinitions rightBodySelectionSet fuel runtimeType
          targetParent leftField rightField leftArguments rightArguments
          leftRuntime rightRuntime FieldPairProbeTag.right
          rightCurrentSelectionSet (by omega) hrightBodyFuel
          hrightBodyValid hrightBodyFree hrightBodyNormal hbodyInclude
          hrightSupport (fun _hobject => hrightContext hrightMem)
          (fun hbodyNonObject => by
            rw [hruntimeObject] at hbodyNonObject
            simp at hbodyNonObject) with
      ⟨rightBodyFields, rightBodyErrors, hrightBodyResponse⟩
    have hnot :=
      responseData_empty_object_not_semanticEquivalent_of_valid_normal_object_nonempty_response
        schema resolvers variableValues (fuel + 1) runtimeType rightSource
        hruntimeObject hrightBodyFree hrightBodyNormal hrightBodyNonempty
        (fields := rightBodyFields) (errors := rightBodyErrors)
        (by simpa [resolvers, rightSource] using hrightBodyResponse)
    simpa [resolvers, rightSource] using hnot
  exact
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_right_abstract_inlineFragment_of_valid_normal_current_pair
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet leftCurrentSelectionSet
      rightCurrentSelectionSet variableValues fuel targetParent leftField
      rightField normalParentType runtimeType leftArguments rightArguments
      leftRuntime rightRuntime hnonObject hruntimeObject hleftFree
      hrightFree hleftNormal hrightNormal hrightMem hmissing hmatching

end GroundTypeNormalization

end NormalForm

end GraphQL
