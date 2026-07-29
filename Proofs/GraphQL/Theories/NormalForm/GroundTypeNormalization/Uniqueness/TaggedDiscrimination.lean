import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.SemanticSeparation
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.SingletonProjection
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.TaggedSuccess

/-!
Semantic discriminators for tagged uniqueness probes.

The tagged probe resolvers make left/right field-head choices visible in leaf
values.  These lemmas package the response-level consequences of that fact.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

theorem responseData_not_semanticEquivalent_of_tagged_object_leaf_field_of_field_children
    (schema : Schema) (rootSelectionSet : List Selection)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField parentType sourceRuntimeType : Name)
    (leftArguments rightArguments : List Argument) {selectionSet : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication} {childSelectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
    : selectionSetDirectiveFree selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> objectTypeNameBool schema parentType = true
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> leafProbeFuel fieldDefinition.outputType ≤ fuel
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ selectionSet
            -> ∃ fieldDefinition,
                schema.lookupField parentType fieldName = some fieldDefinition
                ∧ leafProbeFuel fieldDefinition.outputType ≤ fuel
                ∧ ((TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool
                        schema
                      = false
                    ∨ ∃ childRuntimeType responseFields childErrors,
                        (((objectTypeNameBool schema fieldDefinition.outputType.namedType
                                = true
                              ∧ childRuntimeType = fieldDefinition.outputType.namedType)
                            ∨ ((TypeRef.named
                                    fieldDefinition.outputType.namedType).isCompositeBool
                                    schema
                                  = true
                                ∧ objectTypeNameBool schema
                                    fieldDefinition.outputType.namedType
                                  = false
                                ∧ abstractRuntimeForFieldHeadDeep? schema parentType
                                    fieldName arguments parentType rootSelectionSet
                                  = some childRuntimeType))
                          ∧ schema.typeIncludesObjectBool
                              fieldDefinition.outputType.namedType childRuntimeType
                            = true
                          ∧ Execution.executeSelectionSetAsResponse schema
                              (fieldPairProbeResolvers schema rootSelectionSet
                                targetParent leftField rightField leftArguments
                                rightArguments)
                              variableValues
                              (fuel - leafProbeFuel fieldDefinition.outputType)
                              childRuntimeType
                              (.object childRuntimeType (some FieldPairProbeTag.left))
                              childSelectionSet
                            = ({
                                  data := Execution.ResponseValue.object responseFields,
                                  errors := childErrors
                                }
                                : Execution.Response))))
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ selectionSet
            -> ∃ fieldDefinition,
                schema.lookupField parentType fieldName = some fieldDefinition
                ∧ leafProbeFuel fieldDefinition.outputType ≤ fuel
                ∧ ((TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool
                        schema
                      = false
                    ∨ ∃ childRuntimeType responseFields childErrors,
                        (((objectTypeNameBool schema fieldDefinition.outputType.namedType
                                = true
                              ∧ childRuntimeType = fieldDefinition.outputType.namedType)
                            ∨ ((TypeRef.named
                                    fieldDefinition.outputType.namedType).isCompositeBool
                                    schema
                                  = true
                                ∧ objectTypeNameBool schema
                                    fieldDefinition.outputType.namedType
                                  = false
                                ∧ abstractRuntimeForFieldHeadDeep? schema parentType
                                    fieldName arguments parentType rootSelectionSet
                                  = some childRuntimeType))
                          ∧ schema.typeIncludesObjectBool
                              fieldDefinition.outputType.namedType childRuntimeType
                            = true
                          ∧ Execution.executeSelectionSetAsResponse schema
                              (fieldPairProbeResolvers schema rootSelectionSet
                                targetParent leftField rightField leftArguments
                                rightArguments)
                              variableValues
                              (fuel - leafProbeFuel fieldDefinition.outputType)
                              childRuntimeType
                              (.object childRuntimeType (some FieldPairProbeTag.right))
                              childSelectionSet
                            = ({
                                  data := Execution.ResponseValue.object responseFields,
                                  errors := childErrors
                                }
                                : Execution.Response))))
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairProbeResolvers schema rootSelectionSet targetParent
                leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) parentType
              (.object sourceRuntimeType (some FieldPairProbeTag.left))
              selectionSet).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairProbeResolvers schema rootSelectionSet targetParent
                leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) parentType
              (.object sourceRuntimeType (some FieldPairProbeTag.right))
              selectionSet).data := by
  intro hfree hnormal hobject hmem hlookup hfuel hleaf hleftChildren
    hrightChildren
  let resolvers :=
    fieldPairProbeResolvers schema rootSelectionSet targetParent leftField
      rightField leftArguments rightArguments
  have hleftFieldOk :
      ∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
            childSelectionSet ∈ selectionSet ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema resolvers variableValues (fuel + 1)
              (.object sourceRuntimeType (some FieldPairProbeTag.left))
              responseName
              [{
                parentType := parentType,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(responseName, responseValue)], fieldErrors) := by
    exact
      executeField_fieldPairProbe_tagged_object_field_ok_of_field_children
        schema rootSelectionSet variableValues fuel targetParent leftField
        rightField parentType sourceRuntimeType leftArguments rightArguments
        FieldPairProbeTag.left selectionSet hleftChildren
  have hrightFieldOk :
      ∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
            childSelectionSet ∈ selectionSet ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema resolvers variableValues (fuel + 1)
              (.object sourceRuntimeType (some FieldPairProbeTag.right))
              responseName
              [{
                parentType := parentType,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(responseName, responseValue)], fieldErrors) := by
    exact
      executeField_fieldPairProbe_tagged_object_field_ok_of_field_children
        schema rootSelectionSet variableValues fuel targetParent leftField
        rightField parentType sourceRuntimeType leftArguments rightArguments
        FieldPairProbeTag.right selectionSet hrightChildren
  have hleftTarget :
      Execution.executeField schema resolvers variableValues (fuel + 1)
        (.object sourceRuntimeType (some FieldPairProbeTag.left))
        responseName
        [{
          parentType := parentType,
          responseName := responseName,
          fieldName := fieldName,
          arguments := arguments,
          selectionSet := childSelectionSet
        }]
      =
      .ok ([(responseName,
        leafProbeResponseValue fieldDefinition.outputType
          FieldPairProbeTag.left.scalar)], 0) := by
    dsimp [resolvers]
    exact
      executeField_fieldPairProbe_tagged_object_leaf schema rootSelectionSet
        variableValues fuel targetParent leftField rightField parentType
        fieldName sourceRuntimeType responseName leftArguments rightArguments
        arguments FieldPairProbeTag.left childSelectionSet fieldDefinition
        hlookup hfuel hleaf
  have hrightTarget :
      Execution.executeField schema resolvers variableValues (fuel + 1)
        (.object sourceRuntimeType (some FieldPairProbeTag.right))
        responseName
        [{
          parentType := parentType,
          responseName := responseName,
          fieldName := fieldName,
          arguments := arguments,
          selectionSet := childSelectionSet
        }]
      =
      .ok ([(responseName,
        leafProbeResponseValue fieldDefinition.outputType
          FieldPairProbeTag.right.scalar)], 0) := by
    dsimp [resolvers]
    exact
      executeField_fieldPairProbe_tagged_object_leaf schema rootSelectionSet
        variableValues fuel targetParent leftField rightField parentType
        fieldName sourceRuntimeType responseName leftArguments rightArguments
        arguments FieldPairProbeTag.right childSelectionSet fieldDefinition
        hlookup hfuel hleaf
  exact
    SemanticSeparation.responseData_not_semanticEquivalent_of_field_value_diff_of_field_ok
      resolvers resolvers variableValues (fuel + 1)
      (.object sourceRuntimeType (some FieldPairProbeTag.left))
      (.object sourceRuntimeType (some FieldPairProbeTag.right))
      hobject hnormal hnormal hfree hfree hmem hmem hleftTarget
      hrightTarget
      (leafProbeResponseValue_not_semanticEquivalent_of_ne
        fieldDefinition.outputType (by simp [FieldPairProbeTag.scalar]))
      hleftFieldOk hrightFieldOk

theorem responseData_not_semanticEquivalent_of_tagged_object_child_field_of_field_ok
    (schema : Schema) (rootSelectionSet : List Selection)
    (variableValues : Execution.VariableValues)
    (fuel : Nat) (targetParent leftField rightField parentType sourceRuntimeType : Name)
    (leftArguments rightArguments : List Argument)
    {selectionSet : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet : List Selection}
    {fieldDefinition : FieldDefinition} {runtimeType : Name}
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
                  arguments parentType rootSelectionSet
                = some runtimeType))
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType runtimeType
          = true
      -> leafProbeFuel fieldDefinition.outputType ≤ fuel
      -> Execution.executeSelectionSetAsResponse schema
            (fieldPairProbeResolvers schema rootSelectionSet targetParent
              leftField rightField leftArguments rightArguments)
            variableValues
            (fuel - leafProbeFuel fieldDefinition.outputType)
            runtimeType (.object runtimeType (some FieldPairProbeTag.left))
            childSelectionSet
          = ({
                data := Execution.ResponseValue.object leftChildFields,
                errors := leftChildErrors
              }
              : Execution.Response)
      -> Execution.executeSelectionSetAsResponse schema
            (fieldPairProbeResolvers schema rootSelectionSet targetParent
              leftField rightField leftArguments rightArguments)
            variableValues
            (fuel - leafProbeFuel fieldDefinition.outputType)
            runtimeType (.object runtimeType (some FieldPairProbeTag.right))
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
                  (fieldPairProbeResolvers schema rootSelectionSet targetParent
                    leftField rightField leftArguments rightArguments)
                  variableValues (fuel + 1)
                  (.object sourceRuntimeType (some FieldPairProbeTag.left))
                  responseName
                  [{
                    parentType := parentType,
                    responseName := responseName,
                    fieldName := fieldName,
                    arguments := arguments,
                    selectionSet := childSelectionSet
                  }]
                = .ok ([(responseName, responseValue)], fieldErrors))
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ selectionSet
            -> ∃ responseValue fieldErrors,
                Execution.executeField schema
                  (fieldPairProbeResolvers schema rootSelectionSet targetParent
                    leftField rightField leftArguments rightArguments)
                  variableValues (fuel + 1)
                  (.object sourceRuntimeType (some FieldPairProbeTag.right))
                  responseName
                  [{
                    parentType := parentType,
                    responseName := responseName,
                    fieldName := fieldName,
                    arguments := arguments,
                    selectionSet := childSelectionSet
                  }]
                = .ok ([(responseName, responseValue)], fieldErrors))
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairProbeResolvers schema rootSelectionSet targetParent
                leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) parentType
              (.object sourceRuntimeType (some FieldPairProbeTag.left))
              selectionSet).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairProbeResolvers schema rootSelectionSet targetParent
                leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) parentType
              (.object sourceRuntimeType (some FieldPairProbeTag.right))
              selectionSet).data := by
  intro hfree hnormal hobject hmem hlookup hruntime hinclude hfuel
    hleftChildResponse hrightChildResponse hchildNot hleftFieldOk
    hrightFieldOk
  let resolvers :=
    fieldPairProbeResolvers schema rootSelectionSet targetParent leftField
      rightField leftArguments rightArguments
  let leftChildResponse : Execution.Response :=
    { data := Execution.ResponseValue.object leftChildFields, errors := leftChildErrors }
  let rightChildResponse : Execution.Response :=
    { data := Execution.ResponseValue.object rightChildFields, errors := rightChildErrors }
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
        (.object sourceRuntimeType (some FieldPairProbeTag.left))
        responseName
        [{
          parentType := parentType,
          responseName := responseName,
          fieldName := fieldName,
          arguments := arguments,
          selectionSet := childSelectionSet
        }]
      =
      .ok ([(responseName, leftValue)], leftFieldErrors) := by
    dsimp [resolvers]
    rw [
      executeField_fieldPairProbe_tagged_object_objectProbe_response_of_fuel_ge
        schema rootSelectionSet variableValues fuel targetParent leftField
        rightField parentType fieldName sourceRuntimeType responseName
        leftArguments rightArguments arguments FieldPairProbeTag.left
        childSelectionSet fieldDefinition runtimeType hlookup hruntime
        hinclude hfuel]
    rw [hleftChildResponse]
    simp [Execution.singleFieldResult, hleftWrapped]
  have hrightTarget :
      Execution.executeField schema resolvers variableValues (fuel + 1)
        (.object sourceRuntimeType (some FieldPairProbeTag.right))
        responseName
        [{
          parentType := parentType,
          responseName := responseName,
          fieldName := fieldName,
          arguments := arguments,
          selectionSet := childSelectionSet
        }]
      =
      .ok ([(responseName, rightValue)], rightFieldErrors) := by
    dsimp [resolvers]
    rw [
      executeField_fieldPairProbe_tagged_object_objectProbe_response_of_fuel_ge
        schema rootSelectionSet variableValues fuel targetParent leftField
        rightField parentType fieldName sourceRuntimeType responseName
        leftArguments rightArguments arguments FieldPairProbeTag.right
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
      resolvers resolvers variableValues (fuel + 1)
      (.object sourceRuntimeType (some FieldPairProbeTag.left))
      (.object sourceRuntimeType (some FieldPairProbeTag.right))
      hobject hnormal hnormal hfree hfree hmem hmem hleftTarget
      hrightTarget hvalueNot hleftFieldOk hrightFieldOk

theorem responseData_not_semanticEquivalent_of_tagged_object_child_field_pair_of_field_ok
    (schema : Schema) (rootSelectionSet : List Selection)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField parentType sourceRuntimeType : Name)
    (targetLeftArguments targetRightArguments : List Argument)
    {left right : List Selection} {responseName fieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {fieldDefinition : FieldDefinition} {runtimeType : Name}
    {leftChildFields rightChildFields : List (Name × Execution.ResponseValue)}
    {leftChildErrors rightChildErrors : Nat}
    : selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> objectTypeNameBool schema parentType = true
      -> Selection.field responseName fieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName fieldName rightArguments rightDirectives
            rightChildSelectionSet
          ∈ right
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> ((objectTypeNameBool schema fieldDefinition.outputType.namedType = true
            ∧ runtimeType = fieldDefinition.outputType.namedType)
          ∨ ((TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
                = true
              ∧ objectTypeNameBool schema fieldDefinition.outputType.namedType = false
              ∧ abstractRuntimeForFieldHeadDeep? schema parentType fieldName
                  leftArguments parentType rootSelectionSet
                = some runtimeType))
      -> ((objectTypeNameBool schema fieldDefinition.outputType.namedType = true
            ∧ runtimeType = fieldDefinition.outputType.namedType)
          ∨ ((TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
                = true
              ∧ objectTypeNameBool schema fieldDefinition.outputType.namedType = false
              ∧ abstractRuntimeForFieldHeadDeep? schema parentType fieldName
                  rightArguments parentType rootSelectionSet
                = some runtimeType))
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType runtimeType
          = true
      -> leafProbeFuel fieldDefinition.outputType ≤ fuel
      -> Execution.executeSelectionSetAsResponse schema
            (fieldPairProbeResolvers schema rootSelectionSet targetParent
              leftField rightField targetLeftArguments targetRightArguments)
            variableValues
            (fuel - leafProbeFuel fieldDefinition.outputType)
            runtimeType (.object runtimeType (some FieldPairProbeTag.left))
            leftChildSelectionSet
          = ({
                data := Execution.ResponseValue.object leftChildFields,
                errors := leftChildErrors
              }
              : Execution.Response)
      -> Execution.executeSelectionSetAsResponse schema
            (fieldPairProbeResolvers schema rootSelectionSet targetParent
              leftField rightField targetLeftArguments targetRightArguments)
            variableValues
            (fuel - leafProbeFuel fieldDefinition.outputType)
            runtimeType (.object runtimeType (some FieldPairProbeTag.right))
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
                  (fieldPairProbeResolvers schema rootSelectionSet targetParent
                    leftField rightField targetLeftArguments targetRightArguments)
                  variableValues (fuel + 1)
                  (.object sourceRuntimeType (some FieldPairProbeTag.left))
                  responseName
                  [{
                    parentType := parentType,
                    responseName := responseName,
                    fieldName := fieldName,
                    arguments := arguments,
                    selectionSet := childSelectionSet
                  }]
                = .ok ([(responseName, responseValue)], fieldErrors))
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ right
            -> ∃ responseValue fieldErrors,
                Execution.executeField schema
                  (fieldPairProbeResolvers schema rootSelectionSet targetParent
                    leftField rightField targetLeftArguments targetRightArguments)
                  variableValues (fuel + 1)
                  (.object sourceRuntimeType (some FieldPairProbeTag.right))
                  responseName
                  [{
                    parentType := parentType,
                    responseName := responseName,
                    fieldName := fieldName,
                    arguments := arguments,
                    selectionSet := childSelectionSet
                  }]
                = .ok ([(responseName, responseValue)], fieldErrors))
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairProbeResolvers schema rootSelectionSet targetParent
                leftField rightField targetLeftArguments targetRightArguments)
              variableValues (fuel + 1) parentType
              (.object sourceRuntimeType (some FieldPairProbeTag.left))
              left).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairProbeResolvers schema rootSelectionSet targetParent
                leftField rightField targetLeftArguments targetRightArguments)
              variableValues (fuel + 1) parentType
              (.object sourceRuntimeType (some FieldPairProbeTag.right))
              right).data := by
  intro hleftFree hrightFree hleftNormal hrightNormal hobject hleftMem
    hrightMem hlookup hleftRuntime hrightRuntime hinclude hfuel
    hleftChildResponse
    hrightChildResponse hchildNot hleftFieldOk hrightFieldOk
  let resolvers :=
    fieldPairProbeResolvers schema rootSelectionSet targetParent leftField
      rightField targetLeftArguments targetRightArguments
  let leftChildResponse : Execution.Response :=
    { data := Execution.ResponseValue.object leftChildFields, errors := leftChildErrors }
  let rightChildResponse : Execution.Response :=
    { data := Execution.ResponseValue.object rightChildFields, errors := rightChildErrors }
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
        (.object sourceRuntimeType (some FieldPairProbeTag.left))
        responseName
        [{
          parentType := parentType,
          responseName := responseName,
          fieldName := fieldName,
          arguments := leftArguments,
          selectionSet := leftChildSelectionSet
        }]
      =
      .ok ([(responseName, leftValue)], leftFieldErrors) := by
    dsimp [resolvers]
    rw [
      executeField_fieldPairProbe_tagged_object_objectProbe_response_of_fuel_ge
        schema rootSelectionSet variableValues fuel targetParent leftField
        rightField parentType fieldName sourceRuntimeType responseName
        targetLeftArguments targetRightArguments leftArguments
        FieldPairProbeTag.left leftChildSelectionSet fieldDefinition
        runtimeType hlookup hleftRuntime hinclude hfuel]
    rw [hleftChildResponse]
    simp [Execution.singleFieldResult, hleftWrapped]
  have hrightTarget :
      Execution.executeField schema resolvers variableValues (fuel + 1)
        (.object sourceRuntimeType (some FieldPairProbeTag.right))
        responseName
        [{
          parentType := parentType,
          responseName := responseName,
          fieldName := fieldName,
          arguments := rightArguments,
          selectionSet := rightChildSelectionSet
        }]
      =
      .ok ([(responseName, rightValue)], rightFieldErrors) := by
    dsimp [resolvers]
    rw [
      executeField_fieldPairProbe_tagged_object_objectProbe_response_of_fuel_ge
        schema rootSelectionSet variableValues fuel targetParent leftField
        rightField parentType fieldName sourceRuntimeType responseName
        targetLeftArguments targetRightArguments rightArguments
        FieldPairProbeTag.right rightChildSelectionSet fieldDefinition
        runtimeType hlookup hrightRuntime hinclude hfuel]
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
      resolvers resolvers variableValues (fuel + 1)
      (.object sourceRuntimeType (some FieldPairProbeTag.left))
      (.object sourceRuntimeType (some FieldPairProbeTag.right))
      hobject hleftNormal hrightNormal hleftFree hrightFree hleftMem
      hrightMem hleftTarget hrightTarget hvalueNot hleftFieldOk
      hrightFieldOk

theorem
    responseData_not_semanticEquivalent_of_tagged_object_child_field_pair_of_valid_normal_child_promoted_fuel_ge
    (schema : Schema) (rootSelectionSet : List Selection)
    (variableValues : Execution.VariableValues)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ∀ parentType leftVariableDefinitions rightVariableDefinitions
            (left right : List Selection) fuel sourceRuntimeType targetParent
            leftField rightField
            (targetLeftArguments targetRightArguments : List Argument)
            {responseName fieldName : Name}
            {leftArguments rightArguments : List Argument}
            {leftDirectives rightDirectives : List DirectiveApplication}
            {leftChildSelectionSet rightChildSelectionSet : List Selection}
            {fieldDefinition : FieldDefinition} {runtimeType : Name},
          Validation.selectionSetValid schema leftVariableDefinitions parentType left
          -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
          -> selectionSetDirectiveFree left
          -> selectionSetDirectiveFree right
          -> selectionSetNormal schema parentType left
          -> selectionSetNormal schema parentType right
          -> objectTypeNameBool schema parentType = true
          -> schema.typeIncludesObjectBool parentType sourceRuntimeType = true
          -> schema.isCompositeType fieldDefinition.outputType.namedType
          -> (∀ abstractTargetParent abstractTargetField targetRuntimeType
                  targetFieldDefinition,
                schema.lookupField abstractTargetParent abstractTargetField
                  = some targetFieldDefinition
                -> (TypeRef.named
                      targetFieldDefinition.outputType.namedType).isCompositeBool
                      schema
                    = true
                -> objectTypeNameBool schema targetFieldDefinition.outputType.namedType
                    = false
                -> abstractRuntimeForFieldDeep? schema abstractTargetParent
                      abstractTargetField parentType left
                    = some targetRuntimeType
                -> ∃ runtimeType,
                    abstractRuntimeForFieldDeep? schema abstractTargetParent
                        abstractTargetField abstractTargetParent rootSelectionSet
                      = some runtimeType
                    ∧ schema.typeIncludesObjectBool
                        targetFieldDefinition.outputType.namedType runtimeType
                      = true)
          -> (∀ abstractTargetParent abstractTargetField targetRuntimeType
                  targetFieldDefinition,
                schema.lookupField abstractTargetParent abstractTargetField
                  = some targetFieldDefinition
                -> (TypeRef.named
                      targetFieldDefinition.outputType.namedType).isCompositeBool
                      schema
                    = true
                -> objectTypeNameBool schema targetFieldDefinition.outputType.namedType
                    = false
                -> abstractRuntimeForFieldDeep? schema abstractTargetParent
                      abstractTargetField parentType right
                    = some targetRuntimeType
                -> ∃ runtimeType,
                    abstractRuntimeForFieldDeep? schema abstractTargetParent
                        abstractTargetField abstractTargetParent rootSelectionSet
                      = some runtimeType
                    ∧ schema.typeIncludesObjectBool
                        targetFieldDefinition.outputType.namedType runtimeType
                      = true)
          -> (∀ abstractTargetParent abstractTargetField targetRuntimeType
                  targetFieldDefinition,
                schema.lookupField abstractTargetParent abstractTargetField
                  = some targetFieldDefinition
                -> (TypeRef.named
                      targetFieldDefinition.outputType.namedType).isCompositeBool
                      schema
                    = true
                -> objectTypeNameBool schema targetFieldDefinition.outputType.namedType
                    = false
                -> abstractRuntimeForFieldDeep? schema abstractTargetParent
                      abstractTargetField fieldDefinition.outputType.namedType
                      leftChildSelectionSet
                    = some targetRuntimeType
                -> ∃ runtimeType,
                    abstractRuntimeForFieldDeep? schema abstractTargetParent
                        abstractTargetField abstractTargetParent rootSelectionSet
                      = some runtimeType
                    ∧ schema.typeIncludesObjectBool
                        targetFieldDefinition.outputType.namedType runtimeType
                      = true)
          -> (∀ abstractTargetParent abstractTargetField targetRuntimeType
                  targetFieldDefinition,
                schema.lookupField abstractTargetParent abstractTargetField
                  = some targetFieldDefinition
                -> (TypeRef.named
                      targetFieldDefinition.outputType.namedType).isCompositeBool
                      schema
                    = true
                -> objectTypeNameBool schema targetFieldDefinition.outputType.namedType
                    = false
                -> abstractRuntimeForFieldDeep? schema abstractTargetParent
                      abstractTargetField fieldDefinition.outputType.namedType
                      rightChildSelectionSet
                    = some targetRuntimeType
                -> ∃ runtimeType,
                    abstractRuntimeForFieldDeep? schema abstractTargetParent
                        abstractTargetField abstractTargetParent rootSelectionSet
                      = some runtimeType
                    ∧ schema.typeIncludesObjectBool
                        targetFieldDefinition.outputType.namedType runtimeType
                      = true)
          -> selectionSetDeepHeadPromotionAvailable schema rootSelectionSet
              parentType left
          -> selectionSetDeepHeadPromotionAvailable schema rootSelectionSet
              parentType right
          -> selectionSetDeepProbeFuel schema parentType left ≤ fuel
          -> selectionSetDeepProbeFuel schema parentType right ≤ fuel
          -> Selection.field responseName fieldName leftArguments leftDirectives
                leftChildSelectionSet
              ∈ left
          -> Selection.field responseName fieldName rightArguments rightDirectives
                rightChildSelectionSet
              ∈ right
          -> schema.lookupField parentType fieldName = some fieldDefinition
          -> ((objectTypeNameBool schema fieldDefinition.outputType.namedType = true
                ∧ runtimeType = fieldDefinition.outputType.namedType)
              ∨ ((TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool
                      schema
                    = true
                  ∧ objectTypeNameBool schema fieldDefinition.outputType.namedType = false
                  ∧ abstractRuntimeForFieldHeadDeep? schema parentType fieldName
                      leftArguments parentType rootSelectionSet
                    = some runtimeType))
          -> ((objectTypeNameBool schema fieldDefinition.outputType.namedType = true
                ∧ runtimeType = fieldDefinition.outputType.namedType)
              ∨ ((TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool
                      schema
                    = true
                  ∧ objectTypeNameBool schema fieldDefinition.outputType.namedType = false
                  ∧ abstractRuntimeForFieldHeadDeep? schema parentType fieldName
                      rightArguments parentType rootSelectionSet
                    = some runtimeType))
          -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType
                runtimeType
              = true
          -> ¬ Execution.ResponseValue.semanticEquivalent
                (Execution.executeSelectionSetAsResponse schema
                  (fieldPairProbeResolvers schema rootSelectionSet targetParent
                    leftField rightField targetLeftArguments targetRightArguments)
                  variableValues
                  (fuel - leafProbeFuel fieldDefinition.outputType)
                  runtimeType (.object runtimeType (some FieldPairProbeTag.left))
                  leftChildSelectionSet).data
                (Execution.executeSelectionSetAsResponse schema
                  (fieldPairProbeResolvers schema rootSelectionSet targetParent
                    leftField rightField targetLeftArguments targetRightArguments)
                  variableValues
                  (fuel - leafProbeFuel fieldDefinition.outputType)
                  runtimeType (.object runtimeType (some FieldPairProbeTag.right))
                  rightChildSelectionSet).data
          -> ¬ Execution.ResponseValue.semanticEquivalent
                (Execution.executeSelectionSetAsResponse schema
                  (fieldPairProbeResolvers schema rootSelectionSet targetParent
                    leftField rightField targetLeftArguments targetRightArguments)
                  variableValues (fuel + 1) parentType
                  (.object sourceRuntimeType (some FieldPairProbeTag.left))
                  left).data
                (Execution.executeSelectionSetAsResponse schema
                  (fieldPairProbeResolvers schema rootSelectionSet targetParent
                    leftField rightField targetLeftArguments targetRightArguments)
                  variableValues (fuel + 1) parentType
                  (.object sourceRuntimeType (some FieldPairProbeTag.right))
                  right).data := by
  intro hschema parentType leftVariableDefinitions rightVariableDefinitions
    left right fuel sourceRuntimeType targetParent leftField rightField
    targetLeftArguments targetRightArguments responseName fieldName
    leftArguments rightArguments leftDirectives rightDirectives
    leftChildSelectionSet rightChildSelectionSet fieldDefinition runtimeType
    hleftValid hrightValid hleftFree hrightFree hleftNormal hrightNormal
    hobject hinclude hcomposite hleftPromote hrightPromote
    hleftChildPromote hrightChildPromote hleftHeadPromote
    hrightHeadPromote hleftFuel hrightFuel hleftMem
    hrightMem hlookup hleftRuntime hrightRuntime hruntimeInclude hchildNot
  let resolvers :=
    fieldPairProbeResolvers schema rootSelectionSet targetParent leftField
      rightField targetLeftArguments targetRightArguments
  rcases selectionSetValid_field_lookup_of_mem hleftValid hleftMem with
    ⟨leftCandidateDefinition, hleftCandidateLookup, _hleftArgumentsValid,
      hleftFieldValid⟩
  have hleftDefinitionEq : leftCandidateDefinition = fieldDefinition := by
    rw [hlookup] at hleftCandidateLookup
    exact Option.some.inj hleftCandidateLookup.symm
  subst leftCandidateDefinition
  rcases selectionSetValid_field_lookup_of_mem hrightValid hrightMem with
    ⟨rightCandidateDefinition, hrightCandidateLookup, _hrightArgumentsValid,
      hrightFieldValid⟩
  have hrightDefinitionEq : rightCandidateDefinition = fieldDefinition := by
    rw [hlookup] at hrightCandidateLookup
    exact Option.some.inj hrightCandidateLookup.symm
  subst rightCandidateDefinition
  rcases fieldSelectionSetValid_child_of_composite hleftFieldValid
      hcomposite with
    ⟨_hleftChildNonempty, hleftChildValid⟩
  rcases fieldSelectionSetValid_child_of_composite hrightFieldValid
      hcomposite with
    ⟨_hrightChildNonempty, hrightChildValid⟩
  have hleftChildFree :
      selectionSetDirectiveFree leftChildSelectionSet :=
    selectionSetDirectiveFree_field_child_of_mem hleftFree hleftMem
  have hrightChildFree :
      selectionSetDirectiveFree rightChildSelectionSet :=
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
  have hleafFuel :
      leafProbeFuel fieldDefinition.outputType ≤ fuel := by
    have hlocal :
        leafProbeFuel fieldDefinition.outputType
          ≤ selectionSetDeepProbeFuel schema parentType left :=
      leafProbeFuel_le_selectionSetDeepProbeFuel_of_field_mem schema
        parentType hleftMem hlookup
    omega
  have hleftChildFuel :
      selectionSetDeepProbeFuel schema fieldDefinition.outputType.namedType
          leftChildSelectionSet
        ≤ fuel - leafProbeFuel fieldDefinition.outputType - 1 := by
    have hlocal :=
      selectionSetDeepProbeFuel_field_mem schema parentType left responseName
        fieldName leftArguments leftDirectives leftChildSelectionSet
        fieldDefinition hleftMem hlookup
    omega
  have hrightChildFuel :
      selectionSetDeepProbeFuel schema fieldDefinition.outputType.namedType
          rightChildSelectionSet
        ≤ fuel - leafProbeFuel fieldDefinition.outputType - 1 := by
    have hlocal :=
      selectionSetDeepProbeFuel_field_mem schema parentType right responseName
        fieldName rightArguments rightDirectives rightChildSelectionSet
        fieldDefinition hrightMem hlookup
    omega
  have hleftChildSize :
      SelectionSet.size leftChildSelectionSet <
        SelectionSet.size leftChildSelectionSet + 1 := by
    omega
  have hrightChildSize :
      SelectionSet.size rightChildSelectionSet <
        SelectionSet.size rightChildSelectionSet + 1 := by
    omega
  have hleftChildHeadPromote :
      selectionSetDeepHeadPromotionAvailable schema rootSelectionSet
        fieldDefinition.outputType.namedType leftChildSelectionSet := by
    intro abstractTargetParent abstractTargetField targetArguments
      targetRuntimeType targetFieldDefinition htargetLookup
      htargetComposite htargetNonObject hlocalRuntime
    rcases
        abstractRuntimeForFieldHeadDeep?_object_field_child_promote_some_of_valid_normal
          hleftValid hleftFree hleftNormal hleftMem hlookup
          hlocalRuntime with
      ⟨parentRuntimeType, hparentRuntime⟩
    exact
      hleftHeadPromote abstractTargetParent abstractTargetField
        targetArguments parentRuntimeType targetFieldDefinition
        htargetLookup htargetComposite htargetNonObject hparentRuntime
  have hrightChildHeadPromote :
      selectionSetDeepHeadPromotionAvailable schema rootSelectionSet
        fieldDefinition.outputType.namedType rightChildSelectionSet := by
    intro abstractTargetParent abstractTargetField targetArguments
      targetRuntimeType targetFieldDefinition htargetLookup
      htargetComposite htargetNonObject hlocalRuntime
    rcases
        abstractRuntimeForFieldHeadDeep?_object_field_child_promote_some_of_valid_normal
          hrightValid hrightFree hrightNormal hrightMem hlookup
          hlocalRuntime with
      ⟨parentRuntimeType, hparentRuntime⟩
    exact
      hrightHeadPromote abstractTargetParent abstractTargetField
        targetArguments parentRuntimeType targetFieldDefinition
        htargetLookup htargetComposite htargetNonObject hparentRuntime
  rcases
      executeSelectionSetAsResponse_fieldPairProbe_tagged_of_valid_normal_promoted_fuel_ge_size
        schema rootSelectionSet variableValues hschema
        (SelectionSet.size leftChildSelectionSet + 1)
        fieldDefinition.outputType.namedType leftVariableDefinitions
        leftChildSelectionSet
        (fuel - leafProbeFuel fieldDefinition.outputType - 1)
        runtimeType targetParent leftField rightField targetLeftArguments
        targetRightArguments FieldPairProbeTag.left hleftChildSize
        hleftChildFuel hleftChildValid hleftChildFree hleftChildNormal
        hruntimeInclude hleftChildPromote hleftChildHeadPromote with
    ⟨leftChildFields, leftChildErrors, hleftChildResponseRaw⟩
  rcases
      executeSelectionSetAsResponse_fieldPairProbe_tagged_of_valid_normal_promoted_fuel_ge_size
        schema rootSelectionSet variableValues hschema
        (SelectionSet.size rightChildSelectionSet + 1)
        fieldDefinition.outputType.namedType rightVariableDefinitions
        rightChildSelectionSet
        (fuel - leafProbeFuel fieldDefinition.outputType - 1)
        runtimeType targetParent leftField rightField targetLeftArguments
        targetRightArguments FieldPairProbeTag.right hrightChildSize
        hrightChildFuel hrightChildValid hrightChildFree hrightChildNormal
        hruntimeInclude hrightChildPromote hrightChildHeadPromote with
    ⟨rightChildFields, rightChildErrors, hrightChildResponseRaw⟩
  have hchildFuelEq :
      fuel - leafProbeFuel fieldDefinition.outputType - 1 + 1 =
        fuel - leafProbeFuel fieldDefinition.outputType := by
    have hleafFuelLt :
        leafProbeFuel fieldDefinition.outputType < fuel := by
      have hlocal :=
        selectionSetDeepProbeFuel_field_mem schema parentType left responseName
          fieldName leftArguments leftDirectives leftChildSelectionSet
          fieldDefinition hleftMem hlookup
      have hchildPos :=
        selectionSetDeepProbeFuel_pos schema
          fieldDefinition.outputType.namedType leftChildSelectionSet
      omega
    omega
  have hleftChildResponse :
      Execution.executeSelectionSetAsResponse schema resolvers variableValues
          (fuel - leafProbeFuel fieldDefinition.outputType)
          runtimeType (.object runtimeType (some FieldPairProbeTag.left))
          leftChildSelectionSet =
        ({ data := Execution.ResponseValue.object leftChildFields, errors := leftChildErrors } :
          Execution.Response) := by
    dsimp [resolvers]
    simpa [hchildFuelEq] using hleftChildResponseRaw
  have hrightChildResponse :
      Execution.executeSelectionSetAsResponse schema resolvers variableValues
          (fuel - leafProbeFuel fieldDefinition.outputType)
          runtimeType (.object runtimeType (some FieldPairProbeTag.right))
          rightChildSelectionSet =
        ({ data := Execution.ResponseValue.object rightChildFields, errors := rightChildErrors } :
          Execution.Response) := by
    dsimp [resolvers]
    simpa [hchildFuelEq] using hrightChildResponseRaw
  have hchildObjectsNot :
      ¬ Execution.ResponseValue.semanticEquivalent
        (Execution.ResponseValue.object leftChildFields)
        (Execution.ResponseValue.object rightChildFields) := by
    intro hobjects
    exact hchildNot (by
      have hleftChildResponse' := hleftChildResponse
      have hrightChildResponse' := hrightChildResponse
      dsimp [resolvers] at hleftChildResponse' hrightChildResponse'
      rw [hleftChildResponse', hrightChildResponse']
      exact hobjects)
  have hleftFieldOk :
      ∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
            childSelectionSet ∈ left ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema resolvers variableValues (fuel + 1)
              (.object sourceRuntimeType (some FieldPairProbeTag.left))
              responseName
              [{
                parentType := parentType,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(responseName, responseValue)], fieldErrors) := by
    dsimp [resolvers]
    exact
      executeField_fieldPairProbe_tagged_object_field_ok_of_valid_normal_promoted_fuel_ge
        schema rootSelectionSet variableValues hschema parentType
        leftVariableDefinitions left fuel sourceRuntimeType targetParent
        leftField rightField targetLeftArguments targetRightArguments
        FieldPairProbeTag.left hleftFuel hleftValid hleftFree hleftNormal
        hobject hinclude hleftPromote hleftHeadPromote
  have hrightFieldOk :
      ∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
            childSelectionSet ∈ right ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema resolvers variableValues (fuel + 1)
              (.object sourceRuntimeType (some FieldPairProbeTag.right))
              responseName
              [{
                parentType := parentType,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(responseName, responseValue)], fieldErrors) := by
    dsimp [resolvers]
    exact
      executeField_fieldPairProbe_tagged_object_field_ok_of_valid_normal_promoted_fuel_ge
        schema rootSelectionSet variableValues hschema parentType
        rightVariableDefinitions right fuel sourceRuntimeType targetParent
        leftField rightField targetLeftArguments targetRightArguments
        FieldPairProbeTag.right hrightFuel hrightValid hrightFree
        hrightNormal hobject hinclude hrightPromote hrightHeadPromote
  exact
    responseData_not_semanticEquivalent_of_tagged_object_child_field_pair_of_field_ok
      schema rootSelectionSet variableValues fuel targetParent leftField
      rightField parentType sourceRuntimeType targetLeftArguments
      targetRightArguments hleftFree hrightFree hleftNormal hrightNormal
      hobject hleftMem hrightMem hlookup hleftRuntime hrightRuntime
      hruntimeInclude
      hleafFuel hleftChildResponse hrightChildResponse hchildObjectsNot
      hleftFieldOk hrightFieldOk

theorem responseData_not_semanticEquivalent_of_tagged_abstract_inlineFragment_body
    (schema : Schema) (rootSelectionSet : List Selection)
    (variableValues : Execution.VariableValues)
    (fuel : Nat) (targetParent leftField rightField normalParentType runtimeType : Name)
    (leftArguments rightArguments : List Argument)
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
              (fieldPairProbeResolvers schema rootSelectionSet targetParent
                leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) runtimeType
              (.object runtimeType (some FieldPairProbeTag.left))
              bodySelectionSet).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairProbeResolvers schema rootSelectionSet targetParent
                leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) runtimeType
              (.object runtimeType (some FieldPairProbeTag.right))
              bodySelectionSet).data
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairProbeResolvers schema rootSelectionSet targetParent
                leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) runtimeType
              (.object runtimeType (some FieldPairProbeTag.left))
              (pref
                ++ Selection.inlineFragment (some runtimeType) [] bodySelectionSet
                    :: suffix)).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairProbeResolvers schema rootSelectionSet targetParent
                leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) runtimeType
              (.object runtimeType (some FieldPairProbeTag.right))
              (pref
                ++ Selection.inlineFragment (some runtimeType) [] bodySelectionSet
                    :: suffix)).data := by
  intro hnonObject hruntimeObject hfree hnormal hbodyNot hsemantic
  let resolvers :=
    fieldPairProbeResolvers schema rootSelectionSet targetParent leftField
      rightField leftArguments rightArguments
  have hleftMiddle :
      Execution.executeSelectionSet schema resolvers variableValues
        (fuel + 1) runtimeType
        (.object runtimeType (some FieldPairProbeTag.left))
        (pref ++ Selection.inlineFragment (some runtimeType) []
          bodySelectionSet :: suffix)
      =
      Execution.executeSelectionSet schema resolvers variableValues
        (fuel + 1) runtimeType
        (.object runtimeType (some FieldPairProbeTag.left))
        [Selection.inlineFragment (some runtimeType) []
          bodySelectionSet] :=
    executeSelectionSet_middle_inlineFragment_only_eq_singleton_at_runtime_parent
      schema resolvers variableValues (fuel + 1)
      (some FieldPairProbeTag.left) hnonObject hruntimeObject hfree hnormal
  have hrightMiddle :
      Execution.executeSelectionSet schema resolvers variableValues
        (fuel + 1) runtimeType
        (.object runtimeType (some FieldPairProbeTag.right))
        (pref ++ Selection.inlineFragment (some runtimeType) []
          bodySelectionSet :: suffix)
      =
      Execution.executeSelectionSet schema resolvers variableValues
        (fuel + 1) runtimeType
        (.object runtimeType (some FieldPairProbeTag.right))
        [Selection.inlineFragment (some runtimeType) []
          bodySelectionSet] :=
    executeSelectionSet_middle_inlineFragment_only_eq_singleton_at_runtime_parent
      schema resolvers variableValues (fuel + 1)
      (some FieldPairProbeTag.right) hnonObject hruntimeObject hfree hnormal
  have hleftApply :
      Execution.doesFragmentTypeApplyBool schema runtimeType
        (.object runtimeType (some FieldPairProbeTag.left)) runtimeType =
          true :=
    doesFragmentTypeApplyBool_object_self schema
      (ref := some FieldPairProbeTag.left) hruntimeObject
  have hrightApply :
      Execution.doesFragmentTypeApplyBool schema runtimeType
        (.object runtimeType (some FieldPairProbeTag.right)) runtimeType =
          true :=
    doesFragmentTypeApplyBool_object_self schema
      (ref := some FieldPairProbeTag.right) hruntimeObject
  have hleftFlatten :
      Execution.executeSelectionSet schema resolvers variableValues
        (fuel + 1) runtimeType
        (.object runtimeType (some FieldPairProbeTag.left))
        [Selection.inlineFragment (some runtimeType) []
          bodySelectionSet]
      =
      Execution.executeSelectionSet schema resolvers variableValues
        (fuel + 1) runtimeType
        (.object runtimeType (some FieldPairProbeTag.left))
        bodySelectionSet := by
    simpa using
      executeSelectionSet_inlineFragment_some_directiveFree_apply_flatten
        schema resolvers variableValues (fuel + 1) runtimeType runtimeType
        (.object runtimeType (some FieldPairProbeTag.left))
        bodySelectionSet [] hleftApply
  have hrightFlatten :
      Execution.executeSelectionSet schema resolvers variableValues
        (fuel + 1) runtimeType
        (.object runtimeType (some FieldPairProbeTag.right))
        [Selection.inlineFragment (some runtimeType) []
          bodySelectionSet]
      =
      Execution.executeSelectionSet schema resolvers variableValues
        (fuel + 1) runtimeType
        (.object runtimeType (some FieldPairProbeTag.right))
        bodySelectionSet := by
    simpa using
      executeSelectionSet_inlineFragment_some_directiveFree_apply_flatten
        schema resolvers variableValues (fuel + 1) runtimeType runtimeType
        (.object runtimeType (some FieldPairProbeTag.right))
        bodySelectionSet [] hrightApply
  apply hbodyNot
  simpa [Execution.executeSelectionSetAsResponse, resolvers, hleftMiddle, hrightMiddle,
    hleftFlatten, hrightFlatten] using hsemantic

theorem responseData_not_semanticEquivalent_of_tagged_abstract_inlineFragment_body_pair
    (schema : Schema) (rootSelectionSet : List Selection)
    (variableValues : Execution.VariableValues)
    (fuel : Nat) (targetParent leftField rightField normalParentType runtimeType : Name)
    (leftArguments rightArguments : List Argument)
    {leftPref rightPref leftSuffix rightSuffix leftBodySelectionSet rightBodySelectionSet
      : List Selection}
    : objectTypeNameBool schema normalParentType = false
      -> objectTypeNameBool schema runtimeType = true
      -> selectionSetDirectiveFree
          (leftPref
            ++ Selection.inlineFragment (some runtimeType) [] leftBodySelectionSet
                :: leftSuffix)
      -> selectionSetDirectiveFree
          (rightPref
            ++ Selection.inlineFragment (some runtimeType) [] rightBodySelectionSet
                :: rightSuffix)
      -> selectionSetNormal schema normalParentType
          (leftPref
            ++ Selection.inlineFragment (some runtimeType) [] leftBodySelectionSet
                :: leftSuffix)
      -> selectionSetNormal schema normalParentType
          (rightPref
            ++ Selection.inlineFragment (some runtimeType) [] rightBodySelectionSet
                :: rightSuffix)
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairProbeResolvers schema rootSelectionSet targetParent
                leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) runtimeType
              (.object runtimeType (some FieldPairProbeTag.left))
              leftBodySelectionSet).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairProbeResolvers schema rootSelectionSet targetParent
                leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) runtimeType
              (.object runtimeType (some FieldPairProbeTag.right))
              rightBodySelectionSet).data
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairProbeResolvers schema rootSelectionSet targetParent
                leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) runtimeType
              (.object runtimeType (some FieldPairProbeTag.left))
              (leftPref
                ++ Selection.inlineFragment (some runtimeType) [] leftBodySelectionSet
                    :: leftSuffix)).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairProbeResolvers schema rootSelectionSet targetParent
                leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) runtimeType
              (.object runtimeType (some FieldPairProbeTag.right))
              (rightPref
                ++ Selection.inlineFragment (some runtimeType) [] rightBodySelectionSet
                    :: rightSuffix)).data := by
  intro hnonObject hruntimeObject hleftFree hrightFree hleftNormal
    hrightNormal hbodyNot hsemantic
  let resolvers :=
    fieldPairProbeResolvers schema rootSelectionSet targetParent leftField
      rightField leftArguments rightArguments
  have hleftMiddle :
      Execution.executeSelectionSet schema resolvers variableValues
        (fuel + 1) runtimeType
        (.object runtimeType (some FieldPairProbeTag.left))
        (leftPref ++ Selection.inlineFragment (some runtimeType) []
          leftBodySelectionSet :: leftSuffix)
      =
      Execution.executeSelectionSet schema resolvers variableValues
        (fuel + 1) runtimeType
        (.object runtimeType (some FieldPairProbeTag.left))
        [Selection.inlineFragment (some runtimeType) []
          leftBodySelectionSet] :=
    executeSelectionSet_middle_inlineFragment_only_eq_singleton_at_runtime_parent
      schema resolvers variableValues (fuel + 1)
      (some FieldPairProbeTag.left) hnonObject hruntimeObject hleftFree
      hleftNormal
  have hrightMiddle :
      Execution.executeSelectionSet schema resolvers variableValues
        (fuel + 1) runtimeType
        (.object runtimeType (some FieldPairProbeTag.right))
        (rightPref ++ Selection.inlineFragment (some runtimeType) []
          rightBodySelectionSet :: rightSuffix)
      =
      Execution.executeSelectionSet schema resolvers variableValues
        (fuel + 1) runtimeType
        (.object runtimeType (some FieldPairProbeTag.right))
        [Selection.inlineFragment (some runtimeType) []
          rightBodySelectionSet] :=
    executeSelectionSet_middle_inlineFragment_only_eq_singleton_at_runtime_parent
      schema resolvers variableValues (fuel + 1)
      (some FieldPairProbeTag.right) hnonObject hruntimeObject hrightFree
      hrightNormal
  have hleftApply :
      Execution.doesFragmentTypeApplyBool schema runtimeType
        (.object runtimeType (some FieldPairProbeTag.left)) runtimeType =
          true :=
    doesFragmentTypeApplyBool_object_self schema
      (ref := some FieldPairProbeTag.left) hruntimeObject
  have hrightApply :
      Execution.doesFragmentTypeApplyBool schema runtimeType
        (.object runtimeType (some FieldPairProbeTag.right)) runtimeType =
          true :=
    doesFragmentTypeApplyBool_object_self schema
      (ref := some FieldPairProbeTag.right) hruntimeObject
  have hleftFlatten :
      Execution.executeSelectionSet schema resolvers variableValues
        (fuel + 1) runtimeType
        (.object runtimeType (some FieldPairProbeTag.left))
        [Selection.inlineFragment (some runtimeType) []
          leftBodySelectionSet]
      =
      Execution.executeSelectionSet schema resolvers variableValues
        (fuel + 1) runtimeType
        (.object runtimeType (some FieldPairProbeTag.left))
        leftBodySelectionSet := by
    simpa using
      executeSelectionSet_inlineFragment_some_directiveFree_apply_flatten
        schema resolvers variableValues (fuel + 1) runtimeType runtimeType
        (.object runtimeType (some FieldPairProbeTag.left))
        leftBodySelectionSet [] hleftApply
  have hrightFlatten :
      Execution.executeSelectionSet schema resolvers variableValues
        (fuel + 1) runtimeType
        (.object runtimeType (some FieldPairProbeTag.right))
        [Selection.inlineFragment (some runtimeType) []
          rightBodySelectionSet]
      =
      Execution.executeSelectionSet schema resolvers variableValues
        (fuel + 1) runtimeType
        (.object runtimeType (some FieldPairProbeTag.right))
        rightBodySelectionSet := by
    simpa using
      executeSelectionSet_inlineFragment_some_directiveFree_apply_flatten
        schema resolvers variableValues (fuel + 1) runtimeType runtimeType
        (.object runtimeType (some FieldPairProbeTag.right))
        rightBodySelectionSet [] hrightApply
  apply hbodyNot
  simpa [Execution.executeSelectionSetAsResponse, resolvers, hleftMiddle, hrightMiddle,
    hleftFlatten, hrightFlatten] using hsemantic

theorem
    responseData_not_semanticEquivalent_of_tagged_object_leaf_field_of_valid_normal_promoted_fuel_ge
    (schema : Schema) (rootSelectionSet : List Selection)
    (variableValues : Execution.VariableValues)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ∀ parentType variableDefinitions (selectionSet : List Selection)
            fuel sourceRuntimeType targetParent leftField rightField
            (leftArguments rightArguments : List Argument)
            {responseName fieldName : Name} {arguments : List Argument}
            {directives : List DirectiveApplication}
            {childSelectionSet : List Selection}
            {fieldDefinition : FieldDefinition},
          Validation.selectionSetValid schema variableDefinitions parentType selectionSet
          -> selectionSetDirectiveFree selectionSet
          -> selectionSetNormal schema parentType selectionSet
          -> objectTypeNameBool schema parentType = true
          -> schema.typeIncludesObjectBool parentType sourceRuntimeType = true
          -> (∀ abstractTargetParent abstractTargetField targetRuntimeType
                  targetFieldDefinition,
                schema.lookupField abstractTargetParent abstractTargetField
                  = some targetFieldDefinition
                -> (TypeRef.named
                      targetFieldDefinition.outputType.namedType).isCompositeBool
                      schema
                    = true
                -> objectTypeNameBool schema targetFieldDefinition.outputType.namedType
                    = false
                -> abstractRuntimeForFieldDeep? schema abstractTargetParent
                      abstractTargetField parentType selectionSet
                    = some targetRuntimeType
                -> ∃ runtimeType,
                    abstractRuntimeForFieldDeep? schema abstractTargetParent
                        abstractTargetField abstractTargetParent rootSelectionSet
                      = some runtimeType
                    ∧ schema.typeIncludesObjectBool
                        targetFieldDefinition.outputType.namedType runtimeType
                      = true)
          -> selectionSetDeepHeadPromotionAvailable schema rootSelectionSet
              parentType selectionSet
          -> selectionSetDeepProbeFuel schema parentType selectionSet ≤ fuel
          -> Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ selectionSet
          -> schema.lookupField parentType fieldName = some fieldDefinition
          -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
              = false
          -> ¬ Execution.ResponseValue.semanticEquivalent
                (Execution.executeSelectionSetAsResponse schema
                  (fieldPairProbeResolvers schema rootSelectionSet targetParent
                    leftField rightField leftArguments rightArguments)
                  variableValues
                  (fuel + 1)
                  parentType
                  (.object sourceRuntimeType (some FieldPairProbeTag.left))
                  selectionSet).data
                (Execution.executeSelectionSetAsResponse schema
                  (fieldPairProbeResolvers schema rootSelectionSet targetParent
                    leftField rightField leftArguments rightArguments)
                  variableValues
                  (fuel + 1)
                  parentType
                  (.object sourceRuntimeType (some FieldPairProbeTag.right))
                  selectionSet).data := by
  intro hschema parentType variableDefinitions selectionSet
    fuel sourceRuntimeType targetParent leftField rightField leftArguments
    rightArguments responseName fieldName arguments directives
    childSelectionSet fieldDefinition hvalid hfree hnormal hobject
    hinclude hpromote hheadPromote hfuel hmem hlookup hleaf
  let resolvers :=
    fieldPairProbeResolvers schema rootSelectionSet targetParent leftField
      rightField leftArguments rightArguments
  have hleafFuel : leafProbeFuel fieldDefinition.outputType ≤ fuel := by
    have hlocal :
        leafProbeFuel fieldDefinition.outputType
          ≤ selectionSetDeepProbeFuel schema parentType selectionSet :=
      leafProbeFuel_le_selectionSetDeepProbeFuel_of_field_mem schema
        parentType (selectionSet := selectionSet)
        (responseName := responseName) (fieldName := fieldName)
        (arguments := arguments) (directives := directives)
        (childSelectionSet := childSelectionSet)
        (fieldDefinition := fieldDefinition) hmem hlookup
    omega
  have hleftFieldOk :
      ∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
            childSelectionSet ∈ selectionSet ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema resolvers variableValues
              (fuel + 1)
              (.object sourceRuntimeType (some FieldPairProbeTag.left))
              responseName
              [{
                parentType := parentType,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(responseName, responseValue)], fieldErrors) := by
    dsimp [resolvers]
    exact
      executeField_fieldPairProbe_tagged_object_field_ok_of_valid_normal_promoted_fuel_ge
        schema rootSelectionSet variableValues hschema parentType
        variableDefinitions selectionSet fuel sourceRuntimeType targetParent
        leftField rightField leftArguments rightArguments FieldPairProbeTag.left
        hfuel hvalid hfree hnormal hobject hinclude hpromote
        hheadPromote
  have hrightFieldOk :
      ∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
            childSelectionSet ∈ selectionSet ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema resolvers variableValues
              (fuel + 1)
              (.object sourceRuntimeType (some FieldPairProbeTag.right))
              responseName
              [{
                parentType := parentType,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(responseName, responseValue)], fieldErrors) := by
    dsimp [resolvers]
    exact
      executeField_fieldPairProbe_tagged_object_field_ok_of_valid_normal_promoted_fuel_ge
        schema rootSelectionSet variableValues hschema parentType
        variableDefinitions selectionSet fuel sourceRuntimeType targetParent
        leftField rightField leftArguments rightArguments FieldPairProbeTag.right
        hfuel hvalid hfree hnormal hobject hinclude hpromote
        hheadPromote
  have hleftTarget :
      Execution.executeField schema resolvers variableValues (fuel + 1)
        (.object sourceRuntimeType (some FieldPairProbeTag.left))
        responseName
        [{
          parentType := parentType,
          responseName := responseName,
          fieldName := fieldName,
          arguments := arguments,
          selectionSet := childSelectionSet
        }]
      =
      .ok ([(responseName,
        leafProbeResponseValue fieldDefinition.outputType
          FieldPairProbeTag.left.scalar)], 0) := by
    dsimp [resolvers]
    exact
      executeField_fieldPairProbe_tagged_object_leaf schema rootSelectionSet
        variableValues fuel targetParent leftField rightField parentType
        fieldName sourceRuntimeType responseName leftArguments rightArguments
        arguments FieldPairProbeTag.left childSelectionSet fieldDefinition
        hlookup hleafFuel hleaf
  have hrightTarget :
      Execution.executeField schema resolvers variableValues (fuel + 1)
        (.object sourceRuntimeType (some FieldPairProbeTag.right))
        responseName
        [{
          parentType := parentType,
          responseName := responseName,
          fieldName := fieldName,
          arguments := arguments,
          selectionSet := childSelectionSet
        }]
      =
      .ok ([(responseName,
        leafProbeResponseValue fieldDefinition.outputType
          FieldPairProbeTag.right.scalar)], 0) := by
    dsimp [resolvers]
    exact
      executeField_fieldPairProbe_tagged_object_leaf schema rootSelectionSet
        variableValues fuel targetParent leftField rightField parentType
        fieldName sourceRuntimeType responseName leftArguments rightArguments
        arguments FieldPairProbeTag.right childSelectionSet fieldDefinition
        hlookup hleafFuel hleaf
  exact
    SemanticSeparation.responseData_not_semanticEquivalent_of_field_value_diff_of_field_ok
      resolvers resolvers variableValues (fuel + 1)
      (.object sourceRuntimeType (some FieldPairProbeTag.left))
      (.object sourceRuntimeType (some FieldPairProbeTag.right))
      hobject hnormal hnormal hfree hfree hmem hmem hleftTarget
      hrightTarget
      (leafProbeResponseValue_not_semanticEquivalent_of_ne
        fieldDefinition.outputType (by simp [FieldPairProbeTag.scalar]))
      hleftFieldOk hrightFieldOk

theorem
    responseData_not_semanticEquivalent_of_tagged_object_leaf_field_of_valid_normal_promoted_deepProbeFuel
    (schema : Schema) (rootSelectionSet : List Selection)
    (variableValues : Execution.VariableValues)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ∀ parentType variableDefinitions (selectionSet : List Selection)
            sourceRuntimeType targetParent leftField rightField
            (leftArguments rightArguments : List Argument)
            {responseName fieldName : Name} {arguments : List Argument}
            {directives : List DirectiveApplication}
            {childSelectionSet : List Selection}
            {fieldDefinition : FieldDefinition},
          Validation.selectionSetValid schema variableDefinitions parentType selectionSet
          -> selectionSetDirectiveFree selectionSet
          -> selectionSetNormal schema parentType selectionSet
          -> objectTypeNameBool schema parentType = true
          -> schema.typeIncludesObjectBool parentType sourceRuntimeType = true
          -> (∀ abstractTargetParent abstractTargetField targetRuntimeType
                  targetFieldDefinition,
                schema.lookupField abstractTargetParent abstractTargetField
                  = some targetFieldDefinition
                -> (TypeRef.named
                      targetFieldDefinition.outputType.namedType).isCompositeBool
                      schema
                    = true
                -> objectTypeNameBool schema targetFieldDefinition.outputType.namedType
                    = false
                -> abstractRuntimeForFieldDeep? schema abstractTargetParent
                      abstractTargetField parentType selectionSet
                    = some targetRuntimeType
                -> ∃ runtimeType,
                    abstractRuntimeForFieldDeep? schema abstractTargetParent
                        abstractTargetField abstractTargetParent rootSelectionSet
                      = some runtimeType
                    ∧ schema.typeIncludesObjectBool
                        targetFieldDefinition.outputType.namedType runtimeType
                      = true)
          -> selectionSetDeepHeadPromotionAvailable schema rootSelectionSet
              parentType selectionSet
          -> Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ selectionSet
          -> schema.lookupField parentType fieldName = some fieldDefinition
          -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
              = false
          -> ¬ Execution.ResponseValue.semanticEquivalent
                (Execution.executeSelectionSetAsResponse schema
                  (fieldPairProbeResolvers schema rootSelectionSet targetParent
                    leftField rightField leftArguments rightArguments)
                  variableValues
                  (selectionSetDeepProbeFuel schema parentType selectionSet + 1)
                  parentType
                  (.object sourceRuntimeType (some FieldPairProbeTag.left))
                  selectionSet).data
                (Execution.executeSelectionSetAsResponse schema
                  (fieldPairProbeResolvers schema rootSelectionSet targetParent
                    leftField rightField leftArguments rightArguments)
                  variableValues
                  (selectionSetDeepProbeFuel schema parentType selectionSet + 1)
                  parentType
                  (.object sourceRuntimeType (some FieldPairProbeTag.right))
                  selectionSet).data := by
  intro hschema parentType variableDefinitions selectionSet sourceRuntimeType
    targetParent leftField rightField leftArguments rightArguments
    responseName fieldName arguments directives childSelectionSet
    fieldDefinition hvalid hfree hnormal hobject hinclude hpromote
    hheadPromote hmem hlookup hleaf
  exact
    responseData_not_semanticEquivalent_of_tagged_object_leaf_field_of_valid_normal_promoted_fuel_ge
      schema rootSelectionSet variableValues hschema parentType
      variableDefinitions selectionSet
      (selectionSetDeepProbeFuel schema parentType selectionSet)
      sourceRuntimeType targetParent leftField rightField leftArguments
      rightArguments hvalid hfree hnormal hobject hinclude hpromote
      hheadPromote
      (by omega) hmem hlookup hleaf

theorem
    responseData_not_semanticEquivalent_of_tagged_object_left_responseName_diff_of_valid_normal_promoted_fuel_ge
    (schema : Schema) (rootSelectionSet : List Selection)
    (variableValues : Execution.VariableValues)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ∀ parentType leftVariableDefinitions rightVariableDefinitions
            (left right : List Selection) fuel sourceRuntimeType targetParent
            leftField rightField (leftArguments rightArguments : List Argument)
            {responseName fieldName : Name} {arguments : List Argument}
            {directives : List DirectiveApplication}
            {childSelectionSet : List Selection},
          Validation.selectionSetValid schema leftVariableDefinitions parentType left
          -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
          -> selectionSetDirectiveFree left
          -> selectionSetDirectiveFree right
          -> selectionSetNormal schema parentType left
          -> selectionSetNormal schema parentType right
          -> objectTypeNameBool schema parentType = true
          -> schema.typeIncludesObjectBool parentType sourceRuntimeType = true
          -> (∀ abstractTargetParent abstractTargetField targetRuntimeType
                  targetFieldDefinition,
                schema.lookupField abstractTargetParent abstractTargetField
                  = some targetFieldDefinition
                -> (TypeRef.named
                      targetFieldDefinition.outputType.namedType).isCompositeBool
                      schema
                    = true
                -> objectTypeNameBool schema targetFieldDefinition.outputType.namedType
                    = false
                -> abstractRuntimeForFieldDeep? schema abstractTargetParent
                      abstractTargetField parentType left
                    = some targetRuntimeType
                -> ∃ runtimeType,
                    abstractRuntimeForFieldDeep? schema abstractTargetParent
                        abstractTargetField abstractTargetParent rootSelectionSet
                      = some runtimeType
                    ∧ schema.typeIncludesObjectBool
                        targetFieldDefinition.outputType.namedType runtimeType
                      = true)
          -> selectionSetDeepHeadPromotionAvailable schema rootSelectionSet
              parentType left
          -> (∀ abstractTargetParent abstractTargetField targetRuntimeType
                  targetFieldDefinition,
                schema.lookupField abstractTargetParent abstractTargetField
                  = some targetFieldDefinition
                -> (TypeRef.named
                      targetFieldDefinition.outputType.namedType).isCompositeBool
                      schema
                    = true
                -> objectTypeNameBool schema targetFieldDefinition.outputType.namedType
                    = false
                -> abstractRuntimeForFieldDeep? schema abstractTargetParent
                      abstractTargetField parentType right
                    = some targetRuntimeType
                -> ∃ runtimeType,
                    abstractRuntimeForFieldDeep? schema abstractTargetParent
                        abstractTargetField abstractTargetParent rootSelectionSet
                      = some runtimeType
                    ∧ schema.typeIncludesObjectBool
                        targetFieldDefinition.outputType.namedType runtimeType
                      = true)
          -> selectionSetDeepHeadPromotionAvailable schema rootSelectionSet
              parentType right
          -> selectionSetDeepProbeFuel schema parentType left ≤ fuel
          -> selectionSetDeepProbeFuel schema parentType right ≤ fuel
          -> Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ left
          -> responseName ∉ right.filterMap Selection.responseName?
          -> ¬ Execution.ResponseValue.semanticEquivalent
                (Execution.executeSelectionSetAsResponse schema
                  (fieldPairProbeResolvers schema rootSelectionSet targetParent
                    leftField rightField leftArguments rightArguments)
                  variableValues
                  (fuel + 1)
                  parentType
                  (.object sourceRuntimeType (some FieldPairProbeTag.left))
                  left).data
                (Execution.executeSelectionSetAsResponse schema
                  (fieldPairProbeResolvers schema rootSelectionSet targetParent
                    leftField rightField leftArguments rightArguments)
                  variableValues
                  (fuel + 1)
                  parentType
                  (.object sourceRuntimeType (some FieldPairProbeTag.right))
                  right).data := by
  intro hschema parentType leftVariableDefinitions rightVariableDefinitions
    left right fuel sourceRuntimeType targetParent leftField rightField
    leftArguments rightArguments responseName fieldName arguments directives
    childSelectionSet hleftValid hrightValid hleftFree hrightFree
    hleftNormal hrightNormal hobject hinclude hleftPromote
    hleftHeadPromote hrightPromote hrightHeadPromote
    hleftFuel hrightFuel hleftMem hrightNoResponseName
  let resolvers :=
    fieldPairProbeResolvers schema rootSelectionSet targetParent leftField
      rightField leftArguments rightArguments
  have hleftFieldOk :
      ∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
            childSelectionSet ∈ left ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema resolvers variableValues
              (fuel + 1)
              (.object sourceRuntimeType (some FieldPairProbeTag.left))
              responseName
              [{
                parentType := parentType,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(responseName, responseValue)], fieldErrors) := by
    dsimp [resolvers]
    exact
      executeField_fieldPairProbe_tagged_object_field_ok_of_valid_normal_promoted_fuel_ge
        schema rootSelectionSet variableValues hschema parentType
        leftVariableDefinitions left fuel sourceRuntimeType targetParent
        leftField rightField leftArguments rightArguments FieldPairProbeTag.left
        hleftFuel hleftValid hleftFree hleftNormal hobject hinclude
        hleftPromote hleftHeadPromote
  have hrightFieldOk :
      ∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
            childSelectionSet ∈ right ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema resolvers variableValues
              (fuel + 1)
              (.object sourceRuntimeType (some FieldPairProbeTag.right))
              responseName
              [{
                parentType := parentType,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(responseName, responseValue)], fieldErrors) := by
    dsimp [resolvers]
    exact
      executeField_fieldPairProbe_tagged_object_field_ok_of_valid_normal_promoted_fuel_ge
        schema rootSelectionSet variableValues hschema parentType
        rightVariableDefinitions right fuel sourceRuntimeType targetParent
        leftField rightField leftArguments rightArguments
        FieldPairProbeTag.right hrightFuel hrightValid hrightFree
        hrightNormal hobject hinclude hrightPromote hrightHeadPromote
  exact
    SemanticSeparation.responseData_not_semanticEquivalent_of_left_responseName_diff_of_field_ok_sources
      resolvers resolvers variableValues (fuel + 1)
      (.object sourceRuntimeType (some FieldPairProbeTag.left))
      (.object sourceRuntimeType (some FieldPairProbeTag.right))
      hobject hleftNormal hrightNormal hleftFree hrightFree hleftMem
      hrightNoResponseName hleftFieldOk hrightFieldOk

theorem
    responseData_not_semanticEquivalent_of_tagged_object_right_responseName_diff_of_valid_normal_promoted_fuel_ge
    (schema : Schema) (rootSelectionSet : List Selection)
    (variableValues : Execution.VariableValues)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ∀ parentType leftVariableDefinitions rightVariableDefinitions
            (left right : List Selection) fuel sourceRuntimeType targetParent
            leftField rightField (leftArguments rightArguments : List Argument)
            {responseName fieldName : Name} {arguments : List Argument}
            {directives : List DirectiveApplication}
            {childSelectionSet : List Selection},
          Validation.selectionSetValid schema leftVariableDefinitions parentType left
          -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
          -> selectionSetDirectiveFree left
          -> selectionSetDirectiveFree right
          -> selectionSetNormal schema parentType left
          -> selectionSetNormal schema parentType right
          -> objectTypeNameBool schema parentType = true
          -> schema.typeIncludesObjectBool parentType sourceRuntimeType = true
          -> (∀ abstractTargetParent abstractTargetField targetRuntimeType
                  targetFieldDefinition,
                schema.lookupField abstractTargetParent abstractTargetField
                  = some targetFieldDefinition
                -> (TypeRef.named
                      targetFieldDefinition.outputType.namedType).isCompositeBool
                      schema
                    = true
                -> objectTypeNameBool schema targetFieldDefinition.outputType.namedType
                    = false
                -> abstractRuntimeForFieldDeep? schema abstractTargetParent
                      abstractTargetField parentType left
                    = some targetRuntimeType
                -> ∃ runtimeType,
                    abstractRuntimeForFieldDeep? schema abstractTargetParent
                        abstractTargetField abstractTargetParent rootSelectionSet
                      = some runtimeType
                    ∧ schema.typeIncludesObjectBool
                        targetFieldDefinition.outputType.namedType runtimeType
                      = true)
          -> selectionSetDeepHeadPromotionAvailable schema rootSelectionSet
              parentType left
          -> (∀ abstractTargetParent abstractTargetField targetRuntimeType
                  targetFieldDefinition,
                schema.lookupField abstractTargetParent abstractTargetField
                  = some targetFieldDefinition
                -> (TypeRef.named
                      targetFieldDefinition.outputType.namedType).isCompositeBool
                      schema
                    = true
                -> objectTypeNameBool schema targetFieldDefinition.outputType.namedType
                    = false
                -> abstractRuntimeForFieldDeep? schema abstractTargetParent
                      abstractTargetField parentType right
                    = some targetRuntimeType
                -> ∃ runtimeType,
                    abstractRuntimeForFieldDeep? schema abstractTargetParent
                        abstractTargetField abstractTargetParent rootSelectionSet
                      = some runtimeType
                    ∧ schema.typeIncludesObjectBool
                        targetFieldDefinition.outputType.namedType runtimeType
                      = true)
          -> selectionSetDeepHeadPromotionAvailable schema rootSelectionSet
              parentType right
          -> selectionSetDeepProbeFuel schema parentType left ≤ fuel
          -> selectionSetDeepProbeFuel schema parentType right ≤ fuel
          -> Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ right
          -> responseName ∉ left.filterMap Selection.responseName?
          -> ¬ Execution.ResponseValue.semanticEquivalent
                (Execution.executeSelectionSetAsResponse schema
                  (fieldPairProbeResolvers schema rootSelectionSet targetParent
                    leftField rightField leftArguments rightArguments)
                  variableValues
                  (fuel + 1)
                  parentType
                  (.object sourceRuntimeType (some FieldPairProbeTag.left))
                  left).data
                (Execution.executeSelectionSetAsResponse schema
                  (fieldPairProbeResolvers schema rootSelectionSet targetParent
                    leftField rightField leftArguments rightArguments)
                  variableValues
                  (fuel + 1)
                  parentType
                  (.object sourceRuntimeType (some FieldPairProbeTag.right))
                  right).data := by
  intro hschema parentType leftVariableDefinitions rightVariableDefinitions
    left right fuel sourceRuntimeType targetParent leftField rightField
    leftArguments rightArguments responseName fieldName arguments directives
    childSelectionSet hleftValid hrightValid hleftFree hrightFree
    hleftNormal hrightNormal hobject hinclude hleftPromote
    hleftHeadPromote hrightPromote hrightHeadPromote
    hleftFuel hrightFuel hrightMem hleftNoResponseName
  let resolvers :=
    fieldPairProbeResolvers schema rootSelectionSet targetParent leftField
      rightField leftArguments rightArguments
  have hleftFieldOk :
      ∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
            childSelectionSet ∈ left ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema resolvers variableValues
              (fuel + 1)
              (.object sourceRuntimeType (some FieldPairProbeTag.left))
              responseName
              [{
                parentType := parentType,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(responseName, responseValue)], fieldErrors) := by
    dsimp [resolvers]
    exact
      executeField_fieldPairProbe_tagged_object_field_ok_of_valid_normal_promoted_fuel_ge
        schema rootSelectionSet variableValues hschema parentType
        leftVariableDefinitions left fuel sourceRuntimeType targetParent
        leftField rightField leftArguments rightArguments FieldPairProbeTag.left
        hleftFuel hleftValid hleftFree hleftNormal hobject hinclude
        hleftPromote hleftHeadPromote
  have hrightFieldOk :
      ∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
            childSelectionSet ∈ right ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema resolvers variableValues
              (fuel + 1)
              (.object sourceRuntimeType (some FieldPairProbeTag.right))
              responseName
              [{
                parentType := parentType,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(responseName, responseValue)], fieldErrors) := by
    dsimp [resolvers]
    exact
      executeField_fieldPairProbe_tagged_object_field_ok_of_valid_normal_promoted_fuel_ge
        schema rootSelectionSet variableValues hschema parentType
        rightVariableDefinitions right fuel sourceRuntimeType targetParent
        leftField rightField leftArguments rightArguments
        FieldPairProbeTag.right hrightFuel hrightValid hrightFree
        hrightNormal hobject hinclude hrightPromote hrightHeadPromote
  exact
    SemanticSeparation.responseData_not_semanticEquivalent_of_right_responseName_diff_of_field_ok_sources
      resolvers resolvers variableValues (fuel + 1)
      (.object sourceRuntimeType (some FieldPairProbeTag.left))
      (.object sourceRuntimeType (some FieldPairProbeTag.right))
      hobject hleftNormal hrightNormal hleftFree hrightFree hrightMem
      hleftNoResponseName hleftFieldOk hrightFieldOk

theorem
    responseData_not_semanticEquivalent_of_tagged_object_left_responseName_diff_pair_of_valid_normal_promoted_fuel_ge
    (schema : Schema) (rootSelectionSet : List Selection)
    (variableValues : Execution.VariableValues)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ∀ leftParentType rightParentType leftVariableDefinitions
            rightVariableDefinitions (left right : List Selection) fuel
            leftSourceRuntimeType rightSourceRuntimeType targetParent leftField
            rightField (leftArguments rightArguments : List Argument)
            {responseName fieldName : Name} {arguments : List Argument}
            {directives : List DirectiveApplication}
            {childSelectionSet : List Selection},
          Validation.selectionSetValid schema leftVariableDefinitions leftParentType left
          -> Validation.selectionSetValid schema rightVariableDefinitions
              rightParentType right
          -> selectionSetDirectiveFree left
          -> selectionSetDirectiveFree right
          -> selectionSetNormal schema leftParentType left
          -> selectionSetNormal schema rightParentType right
          -> objectTypeNameBool schema leftParentType = true
          -> objectTypeNameBool schema rightParentType = true
          -> schema.typeIncludesObjectBool leftParentType leftSourceRuntimeType = true
          -> schema.typeIncludesObjectBool rightParentType rightSourceRuntimeType = true
          -> (∀ abstractTargetParent abstractTargetField targetRuntimeType
                  targetFieldDefinition,
                schema.lookupField abstractTargetParent abstractTargetField
                  = some targetFieldDefinition
                -> (TypeRef.named
                      targetFieldDefinition.outputType.namedType).isCompositeBool
                      schema
                    = true
                -> objectTypeNameBool schema targetFieldDefinition.outputType.namedType
                    = false
                -> abstractRuntimeForFieldDeep? schema abstractTargetParent
                      abstractTargetField leftParentType left
                    = some targetRuntimeType
                -> ∃ runtimeType,
                    abstractRuntimeForFieldDeep? schema abstractTargetParent
                        abstractTargetField abstractTargetParent rootSelectionSet
                      = some runtimeType
                    ∧ schema.typeIncludesObjectBool
                        targetFieldDefinition.outputType.namedType runtimeType
                      = true)
          -> selectionSetDeepHeadPromotionAvailable schema rootSelectionSet
              leftParentType left
          -> (∀ abstractTargetParent abstractTargetField targetRuntimeType
                  targetFieldDefinition,
                schema.lookupField abstractTargetParent abstractTargetField
                  = some targetFieldDefinition
                -> (TypeRef.named
                      targetFieldDefinition.outputType.namedType).isCompositeBool
                      schema
                    = true
                -> objectTypeNameBool schema targetFieldDefinition.outputType.namedType
                    = false
                -> abstractRuntimeForFieldDeep? schema abstractTargetParent
                      abstractTargetField rightParentType right
                    = some targetRuntimeType
                -> ∃ runtimeType,
                    abstractRuntimeForFieldDeep? schema abstractTargetParent
                        abstractTargetField abstractTargetParent rootSelectionSet
                      = some runtimeType
                    ∧ schema.typeIncludesObjectBool
                        targetFieldDefinition.outputType.namedType runtimeType
                      = true)
          -> selectionSetDeepHeadPromotionAvailable schema rootSelectionSet
              rightParentType right
          -> selectionSetDeepProbeFuel schema leftParentType left ≤ fuel
          -> selectionSetDeepProbeFuel schema rightParentType right ≤ fuel
          -> Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ left
          -> responseName ∉ right.filterMap Selection.responseName?
          -> ¬ Execution.ResponseValue.semanticEquivalent
                (Execution.executeSelectionSetAsResponse schema
                  (fieldPairProbeResolvers schema rootSelectionSet targetParent
                    leftField rightField leftArguments rightArguments)
                  variableValues (fuel + 1) leftParentType
                  (.object leftSourceRuntimeType (some FieldPairProbeTag.left))
                  left).data
                (Execution.executeSelectionSetAsResponse schema
                  (fieldPairProbeResolvers schema rootSelectionSet targetParent
                    leftField rightField leftArguments rightArguments)
                  variableValues (fuel + 1) rightParentType
                  (.object rightSourceRuntimeType (some FieldPairProbeTag.right))
                  right).data := by
  intro hschema leftParentType rightParentType leftVariableDefinitions
    rightVariableDefinitions left right fuel leftSourceRuntimeType
    rightSourceRuntimeType targetParent leftField rightField leftArguments
    rightArguments responseName fieldName arguments directives
    childSelectionSet hleftValid hrightValid hleftFree hrightFree
    hleftNormal hrightNormal hleftObject hrightObject hleftInclude
    hrightInclude hleftPromote hleftHeadPromote hrightPromote
    hrightHeadPromote hleftFuel hrightFuel hleftMem hrightNoResponseName
  let resolvers :=
    fieldPairProbeResolvers schema rootSelectionSet targetParent leftField
      rightField leftArguments rightArguments
  have hleftFieldOk :
      ∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
            childSelectionSet ∈ left ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema resolvers variableValues (fuel + 1)
              (.object leftSourceRuntimeType (some FieldPairProbeTag.left))
              responseName
              [{
                parentType := leftParentType,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(responseName, responseValue)], fieldErrors) := by
    dsimp [resolvers]
    exact
      executeField_fieldPairProbe_tagged_object_field_ok_of_valid_normal_promoted_fuel_ge
        schema rootSelectionSet variableValues hschema leftParentType
        leftVariableDefinitions left fuel leftSourceRuntimeType targetParent
        leftField rightField leftArguments rightArguments
        FieldPairProbeTag.left hleftFuel hleftValid hleftFree hleftNormal
        hleftObject hleftInclude hleftPromote hleftHeadPromote
  have hrightFieldOk :
      ∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
            childSelectionSet ∈ right ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema resolvers variableValues (fuel + 1)
              (.object rightSourceRuntimeType (some FieldPairProbeTag.right))
              responseName
              [{
                parentType := rightParentType,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(responseName, responseValue)], fieldErrors) := by
    dsimp [resolvers]
    exact
      executeField_fieldPairProbe_tagged_object_field_ok_of_valid_normal_promoted_fuel_ge
        schema rootSelectionSet variableValues hschema rightParentType
        rightVariableDefinitions right fuel rightSourceRuntimeType
        targetParent leftField rightField leftArguments rightArguments
        FieldPairProbeTag.right hrightFuel hrightValid hrightFree
        hrightNormal hrightObject hrightInclude hrightPromote
        hrightHeadPromote
  exact
    SemanticSeparation.responseData_not_semanticEquivalent_of_left_responseName_diff_of_field_ok_sources_pair
      resolvers resolvers variableValues (fuel + 1)
      (.object leftSourceRuntimeType (some FieldPairProbeTag.left))
      (.object rightSourceRuntimeType (some FieldPairProbeTag.right))
      hleftObject hrightObject hleftNormal hrightNormal hleftFree
      hrightFree hleftMem hrightNoResponseName hleftFieldOk hrightFieldOk

theorem
    responseData_not_semanticEquivalent_of_tagged_object_right_responseName_diff_pair_of_valid_normal_promoted_fuel_ge
    (schema : Schema) (rootSelectionSet : List Selection)
    (variableValues : Execution.VariableValues)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ∀ leftParentType rightParentType leftVariableDefinitions
            rightVariableDefinitions (left right : List Selection) fuel
            leftSourceRuntimeType rightSourceRuntimeType targetParent leftField
            rightField (leftArguments rightArguments : List Argument)
            {responseName fieldName : Name} {arguments : List Argument}
            {directives : List DirectiveApplication}
            {childSelectionSet : List Selection},
          Validation.selectionSetValid schema leftVariableDefinitions leftParentType left
          -> Validation.selectionSetValid schema rightVariableDefinitions
              rightParentType right
          -> selectionSetDirectiveFree left
          -> selectionSetDirectiveFree right
          -> selectionSetNormal schema leftParentType left
          -> selectionSetNormal schema rightParentType right
          -> objectTypeNameBool schema leftParentType = true
          -> objectTypeNameBool schema rightParentType = true
          -> schema.typeIncludesObjectBool leftParentType leftSourceRuntimeType = true
          -> schema.typeIncludesObjectBool rightParentType rightSourceRuntimeType = true
          -> (∀ abstractTargetParent abstractTargetField targetRuntimeType
                  targetFieldDefinition,
                schema.lookupField abstractTargetParent abstractTargetField
                  = some targetFieldDefinition
                -> (TypeRef.named
                      targetFieldDefinition.outputType.namedType).isCompositeBool
                      schema
                    = true
                -> objectTypeNameBool schema targetFieldDefinition.outputType.namedType
                    = false
                -> abstractRuntimeForFieldDeep? schema abstractTargetParent
                      abstractTargetField leftParentType left
                    = some targetRuntimeType
                -> ∃ runtimeType,
                    abstractRuntimeForFieldDeep? schema abstractTargetParent
                        abstractTargetField abstractTargetParent rootSelectionSet
                      = some runtimeType
                    ∧ schema.typeIncludesObjectBool
                        targetFieldDefinition.outputType.namedType runtimeType
                      = true)
          -> selectionSetDeepHeadPromotionAvailable schema rootSelectionSet
              leftParentType left
          -> (∀ abstractTargetParent abstractTargetField targetRuntimeType
                  targetFieldDefinition,
                schema.lookupField abstractTargetParent abstractTargetField
                  = some targetFieldDefinition
                -> (TypeRef.named
                      targetFieldDefinition.outputType.namedType).isCompositeBool
                      schema
                    = true
                -> objectTypeNameBool schema targetFieldDefinition.outputType.namedType
                    = false
                -> abstractRuntimeForFieldDeep? schema abstractTargetParent
                      abstractTargetField rightParentType right
                    = some targetRuntimeType
                -> ∃ runtimeType,
                    abstractRuntimeForFieldDeep? schema abstractTargetParent
                        abstractTargetField abstractTargetParent rootSelectionSet
                      = some runtimeType
                    ∧ schema.typeIncludesObjectBool
                        targetFieldDefinition.outputType.namedType runtimeType
                      = true)
          -> selectionSetDeepHeadPromotionAvailable schema rootSelectionSet
              rightParentType right
          -> selectionSetDeepProbeFuel schema leftParentType left ≤ fuel
          -> selectionSetDeepProbeFuel schema rightParentType right ≤ fuel
          -> Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ right
          -> responseName ∉ left.filterMap Selection.responseName?
          -> ¬ Execution.ResponseValue.semanticEquivalent
                (Execution.executeSelectionSetAsResponse schema
                  (fieldPairProbeResolvers schema rootSelectionSet targetParent
                    leftField rightField leftArguments rightArguments)
                  variableValues (fuel + 1) leftParentType
                  (.object leftSourceRuntimeType (some FieldPairProbeTag.left))
                  left).data
                (Execution.executeSelectionSetAsResponse schema
                  (fieldPairProbeResolvers schema rootSelectionSet targetParent
                    leftField rightField leftArguments rightArguments)
                  variableValues (fuel + 1) rightParentType
                  (.object rightSourceRuntimeType (some FieldPairProbeTag.right))
                  right).data := by
  intro hschema leftParentType rightParentType leftVariableDefinitions
    rightVariableDefinitions left right fuel leftSourceRuntimeType
    rightSourceRuntimeType targetParent leftField rightField leftArguments
    rightArguments responseName fieldName arguments directives
    childSelectionSet hleftValid hrightValid hleftFree hrightFree
    hleftNormal hrightNormal hleftObject hrightObject hleftInclude
    hrightInclude hleftPromote hleftHeadPromote hrightPromote
    hrightHeadPromote hleftFuel hrightFuel hrightMem hleftNoResponseName
  let resolvers :=
    fieldPairProbeResolvers schema rootSelectionSet targetParent leftField
      rightField leftArguments rightArguments
  have hleftFieldOk :
      ∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
            childSelectionSet ∈ left ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema resolvers variableValues (fuel + 1)
              (.object leftSourceRuntimeType (some FieldPairProbeTag.left))
              responseName
              [{
                parentType := leftParentType,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(responseName, responseValue)], fieldErrors) := by
    dsimp [resolvers]
    exact
      executeField_fieldPairProbe_tagged_object_field_ok_of_valid_normal_promoted_fuel_ge
        schema rootSelectionSet variableValues hschema leftParentType
        leftVariableDefinitions left fuel leftSourceRuntimeType targetParent
        leftField rightField leftArguments rightArguments
        FieldPairProbeTag.left hleftFuel hleftValid hleftFree hleftNormal
        hleftObject hleftInclude hleftPromote hleftHeadPromote
  have hrightFieldOk :
      ∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
            childSelectionSet ∈ right ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema resolvers variableValues (fuel + 1)
              (.object rightSourceRuntimeType (some FieldPairProbeTag.right))
              responseName
              [{
                parentType := rightParentType,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(responseName, responseValue)], fieldErrors) := by
    dsimp [resolvers]
    exact
      executeField_fieldPairProbe_tagged_object_field_ok_of_valid_normal_promoted_fuel_ge
        schema rootSelectionSet variableValues hschema rightParentType
        rightVariableDefinitions right fuel rightSourceRuntimeType
        targetParent leftField rightField leftArguments rightArguments
        FieldPairProbeTag.right hrightFuel hrightValid hrightFree
        hrightNormal hrightObject hrightInclude hrightPromote
        hrightHeadPromote
  exact
    SemanticSeparation.responseData_not_semanticEquivalent_of_right_responseName_diff_of_field_ok_sources_pair
      resolvers resolvers variableValues (fuel + 1)
      (.object leftSourceRuntimeType (some FieldPairProbeTag.left))
      (.object rightSourceRuntimeType (some FieldPairProbeTag.right))
      hleftObject hrightObject hleftNormal hrightNormal hleftFree
      hrightFree hrightMem hleftNoResponseName hleftFieldOk hrightFieldOk

theorem
    responseData_not_semanticEquivalent_of_tagged_object_left_responseName_diff_pair_of_valid_normal_promoted_fuel_ge_fuels
    (schema : Schema) (rootSelectionSet : List Selection)
    (variableValues : Execution.VariableValues)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ∀ leftParentType rightParentType leftVariableDefinitions
            rightVariableDefinitions (left right : List Selection)
            leftFuel rightFuel leftSourceRuntimeType rightSourceRuntimeType
            targetParent leftField rightField
            (leftArguments rightArguments : List Argument)
            {responseName fieldName : Name} {arguments : List Argument}
            {directives : List DirectiveApplication}
            {childSelectionSet : List Selection},
          Validation.selectionSetValid schema leftVariableDefinitions leftParentType left
          -> Validation.selectionSetValid schema rightVariableDefinitions
              rightParentType right
          -> selectionSetDirectiveFree left
          -> selectionSetDirectiveFree right
          -> selectionSetNormal schema leftParentType left
          -> selectionSetNormal schema rightParentType right
          -> objectTypeNameBool schema leftParentType = true
          -> objectTypeNameBool schema rightParentType = true
          -> schema.typeIncludesObjectBool leftParentType leftSourceRuntimeType = true
          -> schema.typeIncludesObjectBool rightParentType rightSourceRuntimeType = true
          -> (∀ abstractTargetParent abstractTargetField targetRuntimeType
                  targetFieldDefinition,
                schema.lookupField abstractTargetParent abstractTargetField
                  = some targetFieldDefinition
                -> (TypeRef.named
                      targetFieldDefinition.outputType.namedType).isCompositeBool
                      schema
                    = true
                -> objectTypeNameBool schema targetFieldDefinition.outputType.namedType
                    = false
                -> abstractRuntimeForFieldDeep? schema abstractTargetParent
                      abstractTargetField leftParentType left
                    = some targetRuntimeType
                -> ∃ runtimeType,
                    abstractRuntimeForFieldDeep? schema abstractTargetParent
                        abstractTargetField abstractTargetParent rootSelectionSet
                      = some runtimeType
                    ∧ schema.typeIncludesObjectBool
                        targetFieldDefinition.outputType.namedType runtimeType
                      = true)
          -> selectionSetDeepHeadPromotionAvailable schema rootSelectionSet
              leftParentType left
          -> (∀ abstractTargetParent abstractTargetField targetRuntimeType
                  targetFieldDefinition,
                schema.lookupField abstractTargetParent abstractTargetField
                  = some targetFieldDefinition
                -> (TypeRef.named
                      targetFieldDefinition.outputType.namedType).isCompositeBool
                      schema
                    = true
                -> objectTypeNameBool schema targetFieldDefinition.outputType.namedType
                    = false
                -> abstractRuntimeForFieldDeep? schema abstractTargetParent
                      abstractTargetField rightParentType right
                    = some targetRuntimeType
                -> ∃ runtimeType,
                    abstractRuntimeForFieldDeep? schema abstractTargetParent
                        abstractTargetField abstractTargetParent rootSelectionSet
                      = some runtimeType
                    ∧ schema.typeIncludesObjectBool
                        targetFieldDefinition.outputType.namedType runtimeType
                      = true)
          -> selectionSetDeepHeadPromotionAvailable schema rootSelectionSet
              rightParentType right
          -> selectionSetDeepProbeFuel schema leftParentType left ≤ leftFuel
          -> selectionSetDeepProbeFuel schema rightParentType right ≤ rightFuel
          -> Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ left
          -> responseName ∉ right.filterMap Selection.responseName?
          -> ¬ Execution.ResponseValue.semanticEquivalent
                (Execution.executeSelectionSetAsResponse schema
                  (fieldPairProbeResolvers schema rootSelectionSet targetParent
                    leftField rightField leftArguments rightArguments)
                  variableValues (leftFuel + 1) leftParentType
                  (.object leftSourceRuntimeType (some FieldPairProbeTag.left))
                  left).data
                (Execution.executeSelectionSetAsResponse schema
                  (fieldPairProbeResolvers schema rootSelectionSet targetParent
                    leftField rightField leftArguments rightArguments)
                  variableValues (rightFuel + 1) rightParentType
                  (.object rightSourceRuntimeType (some FieldPairProbeTag.right))
                  right).data := by
  intro hschema leftParentType rightParentType leftVariableDefinitions
    rightVariableDefinitions left right leftFuel rightFuel
    leftSourceRuntimeType rightSourceRuntimeType targetParent leftField
    rightField leftArguments rightArguments responseName fieldName arguments
    directives childSelectionSet hleftValid hrightValid hleftFree hrightFree
    hleftNormal hrightNormal hleftObject hrightObject hleftInclude
    hrightInclude hleftPromote hleftHeadPromote hrightPromote
    hrightHeadPromote hleftFuel hrightFuel hleftMem hrightNoResponseName
  let resolvers :=
    fieldPairProbeResolvers schema rootSelectionSet targetParent leftField
      rightField leftArguments rightArguments
  have hleftFieldOk :
      ∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
            childSelectionSet ∈ left ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema resolvers variableValues
              (leftFuel + 1)
              (.object leftSourceRuntimeType (some FieldPairProbeTag.left))
              responseName
              [{
                parentType := leftParentType,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(responseName, responseValue)], fieldErrors) := by
    dsimp [resolvers]
    exact
      executeField_fieldPairProbe_tagged_object_field_ok_of_valid_normal_promoted_fuel_ge
        schema rootSelectionSet variableValues hschema leftParentType
        leftVariableDefinitions left leftFuel leftSourceRuntimeType
        targetParent leftField rightField leftArguments rightArguments
        FieldPairProbeTag.left hleftFuel hleftValid hleftFree hleftNormal
        hleftObject hleftInclude hleftPromote hleftHeadPromote
  have hrightFieldOk :
      ∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
            childSelectionSet ∈ right ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema resolvers variableValues
              (rightFuel + 1)
              (.object rightSourceRuntimeType (some FieldPairProbeTag.right))
              responseName
              [{
                parentType := rightParentType,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(responseName, responseValue)], fieldErrors) := by
    dsimp [resolvers]
    exact
      executeField_fieldPairProbe_tagged_object_field_ok_of_valid_normal_promoted_fuel_ge
        schema rootSelectionSet variableValues hschema rightParentType
        rightVariableDefinitions right rightFuel rightSourceRuntimeType
        targetParent leftField rightField leftArguments rightArguments
        FieldPairProbeTag.right hrightFuel hrightValid hrightFree
        hrightNormal hrightObject hrightInclude hrightPromote
        hrightHeadPromote
  exact
    SemanticSeparation.responseData_not_semanticEquivalent_of_left_responseName_diff_of_field_ok_sources_pair_fuels
      resolvers resolvers variableValues (leftFuel + 1) (rightFuel + 1)
      (.object leftSourceRuntimeType (some FieldPairProbeTag.left))
      (.object rightSourceRuntimeType (some FieldPairProbeTag.right))
      hleftObject hrightObject hleftNormal hrightNormal hleftFree
      hrightFree hleftMem hrightNoResponseName hleftFieldOk hrightFieldOk

theorem
    responseData_not_semanticEquivalent_of_tagged_object_right_responseName_diff_pair_of_valid_normal_promoted_fuel_ge_fuels
    (schema : Schema) (rootSelectionSet : List Selection)
    (variableValues : Execution.VariableValues)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ∀ leftParentType rightParentType leftVariableDefinitions
            rightVariableDefinitions (left right : List Selection)
            leftFuel rightFuel leftSourceRuntimeType rightSourceRuntimeType
            targetParent leftField rightField
            (leftArguments rightArguments : List Argument)
            {responseName fieldName : Name} {arguments : List Argument}
            {directives : List DirectiveApplication}
            {childSelectionSet : List Selection},
          Validation.selectionSetValid schema leftVariableDefinitions leftParentType left
          -> Validation.selectionSetValid schema rightVariableDefinitions
              rightParentType right
          -> selectionSetDirectiveFree left
          -> selectionSetDirectiveFree right
          -> selectionSetNormal schema leftParentType left
          -> selectionSetNormal schema rightParentType right
          -> objectTypeNameBool schema leftParentType = true
          -> objectTypeNameBool schema rightParentType = true
          -> schema.typeIncludesObjectBool leftParentType leftSourceRuntimeType = true
          -> schema.typeIncludesObjectBool rightParentType rightSourceRuntimeType = true
          -> (∀ abstractTargetParent abstractTargetField targetRuntimeType
                  targetFieldDefinition,
                schema.lookupField abstractTargetParent abstractTargetField
                  = some targetFieldDefinition
                -> (TypeRef.named
                      targetFieldDefinition.outputType.namedType).isCompositeBool
                      schema
                    = true
                -> objectTypeNameBool schema targetFieldDefinition.outputType.namedType
                    = false
                -> abstractRuntimeForFieldDeep? schema abstractTargetParent
                      abstractTargetField leftParentType left
                    = some targetRuntimeType
                -> ∃ runtimeType,
                    abstractRuntimeForFieldDeep? schema abstractTargetParent
                        abstractTargetField abstractTargetParent rootSelectionSet
                      = some runtimeType
                    ∧ schema.typeIncludesObjectBool
                        targetFieldDefinition.outputType.namedType runtimeType
                      = true)
          -> selectionSetDeepHeadPromotionAvailable schema rootSelectionSet
              leftParentType left
          -> (∀ abstractTargetParent abstractTargetField targetRuntimeType
                  targetFieldDefinition,
                schema.lookupField abstractTargetParent abstractTargetField
                  = some targetFieldDefinition
                -> (TypeRef.named
                      targetFieldDefinition.outputType.namedType).isCompositeBool
                      schema
                    = true
                -> objectTypeNameBool schema targetFieldDefinition.outputType.namedType
                    = false
                -> abstractRuntimeForFieldDeep? schema abstractTargetParent
                      abstractTargetField rightParentType right
                    = some targetRuntimeType
                -> ∃ runtimeType,
                    abstractRuntimeForFieldDeep? schema abstractTargetParent
                        abstractTargetField abstractTargetParent rootSelectionSet
                      = some runtimeType
                    ∧ schema.typeIncludesObjectBool
                        targetFieldDefinition.outputType.namedType runtimeType
                      = true)
          -> selectionSetDeepHeadPromotionAvailable schema rootSelectionSet
              rightParentType right
          -> selectionSetDeepProbeFuel schema leftParentType left ≤ leftFuel
          -> selectionSetDeepProbeFuel schema rightParentType right ≤ rightFuel
          -> Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ right
          -> responseName ∉ left.filterMap Selection.responseName?
          -> ¬ Execution.ResponseValue.semanticEquivalent
                (Execution.executeSelectionSetAsResponse schema
                  (fieldPairProbeResolvers schema rootSelectionSet targetParent
                    leftField rightField leftArguments rightArguments)
                  variableValues (leftFuel + 1) leftParentType
                  (.object leftSourceRuntimeType (some FieldPairProbeTag.left))
                  left).data
                (Execution.executeSelectionSetAsResponse schema
                  (fieldPairProbeResolvers schema rootSelectionSet targetParent
                    leftField rightField leftArguments rightArguments)
                  variableValues (rightFuel + 1) rightParentType
                  (.object rightSourceRuntimeType (some FieldPairProbeTag.right))
                  right).data := by
  intro hschema leftParentType rightParentType leftVariableDefinitions
    rightVariableDefinitions left right leftFuel rightFuel
    leftSourceRuntimeType rightSourceRuntimeType targetParent leftField
    rightField leftArguments rightArguments responseName fieldName arguments
    directives childSelectionSet hleftValid hrightValid hleftFree hrightFree
    hleftNormal hrightNormal hleftObject hrightObject hleftInclude
    hrightInclude hleftPromote hleftHeadPromote hrightPromote
    hrightHeadPromote hleftFuel hrightFuel hrightMem hleftNoResponseName
  let resolvers :=
    fieldPairProbeResolvers schema rootSelectionSet targetParent leftField
      rightField leftArguments rightArguments
  have hleftFieldOk :
      ∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
            childSelectionSet ∈ left ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema resolvers variableValues
              (leftFuel + 1)
              (.object leftSourceRuntimeType (some FieldPairProbeTag.left))
              responseName
              [{
                parentType := leftParentType,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(responseName, responseValue)], fieldErrors) := by
    dsimp [resolvers]
    exact
      executeField_fieldPairProbe_tagged_object_field_ok_of_valid_normal_promoted_fuel_ge
        schema rootSelectionSet variableValues hschema leftParentType
        leftVariableDefinitions left leftFuel leftSourceRuntimeType
        targetParent leftField rightField leftArguments rightArguments
        FieldPairProbeTag.left hleftFuel hleftValid hleftFree hleftNormal
        hleftObject hleftInclude hleftPromote hleftHeadPromote
  have hrightFieldOk :
      ∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
            childSelectionSet ∈ right ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema resolvers variableValues
              (rightFuel + 1)
              (.object rightSourceRuntimeType (some FieldPairProbeTag.right))
              responseName
              [{
                parentType := rightParentType,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(responseName, responseValue)], fieldErrors) := by
    dsimp [resolvers]
    exact
      executeField_fieldPairProbe_tagged_object_field_ok_of_valid_normal_promoted_fuel_ge
        schema rootSelectionSet variableValues hschema rightParentType
        rightVariableDefinitions right rightFuel rightSourceRuntimeType
        targetParent leftField rightField leftArguments rightArguments
        FieldPairProbeTag.right hrightFuel hrightValid hrightFree
        hrightNormal hrightObject hrightInclude hrightPromote
        hrightHeadPromote
  exact
    SemanticSeparation.responseData_not_semanticEquivalent_of_right_responseName_diff_of_field_ok_sources_pair_fuels
      resolvers resolvers variableValues (leftFuel + 1) (rightFuel + 1)
      (.object leftSourceRuntimeType (some FieldPairProbeTag.left))
      (.object rightSourceRuntimeType (some FieldPairProbeTag.right))
      hleftObject hrightObject hleftNormal hrightNormal hleftFree
      hrightFree hrightMem hleftNoResponseName hleftFieldOk hrightFieldOk

theorem
    responseData_not_semanticEquivalent_of_tagged_object_left_responseName_diff_pair_of_valid_normal_promoted_fuel_ge_fuels_roots
    (schema : Schema) (leftRootSelectionSet rightRootSelectionSet : List Selection)
    (variableValues : Execution.VariableValues)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ∀ leftParentType rightParentType leftVariableDefinitions
            rightVariableDefinitions (left right : List Selection)
            leftFuel rightFuel leftSourceRuntimeType rightSourceRuntimeType
            targetParent leftField rightField
            (leftArguments rightArguments : List Argument)
            {responseName fieldName : Name} {arguments : List Argument}
            {directives : List DirectiveApplication}
            {childSelectionSet : List Selection},
          Validation.selectionSetValid schema leftVariableDefinitions leftParentType left
          -> Validation.selectionSetValid schema rightVariableDefinitions
              rightParentType right
          -> selectionSetDirectiveFree left
          -> selectionSetDirectiveFree right
          -> selectionSetNormal schema leftParentType left
          -> selectionSetNormal schema rightParentType right
          -> objectTypeNameBool schema leftParentType = true
          -> objectTypeNameBool schema rightParentType = true
          -> schema.typeIncludesObjectBool leftParentType leftSourceRuntimeType = true
          -> schema.typeIncludesObjectBool rightParentType rightSourceRuntimeType = true
          -> (∀ abstractTargetParent abstractTargetField targetRuntimeType
                  targetFieldDefinition,
                schema.lookupField abstractTargetParent abstractTargetField
                  = some targetFieldDefinition
                -> (TypeRef.named
                      targetFieldDefinition.outputType.namedType).isCompositeBool
                      schema
                    = true
                -> objectTypeNameBool schema targetFieldDefinition.outputType.namedType
                    = false
                -> abstractRuntimeForFieldDeep? schema abstractTargetParent
                      abstractTargetField leftParentType left
                    = some targetRuntimeType
                -> ∃ runtimeType,
                    abstractRuntimeForFieldDeep? schema abstractTargetParent
                        abstractTargetField abstractTargetParent
                        leftRootSelectionSet
                      = some runtimeType
                    ∧ schema.typeIncludesObjectBool
                        targetFieldDefinition.outputType.namedType runtimeType
                      = true)
          -> selectionSetDeepHeadPromotionAvailable schema leftRootSelectionSet
              leftParentType left
          -> (∀ abstractTargetParent abstractTargetField targetRuntimeType
                  targetFieldDefinition,
                schema.lookupField abstractTargetParent abstractTargetField
                  = some targetFieldDefinition
                -> (TypeRef.named
                      targetFieldDefinition.outputType.namedType).isCompositeBool
                      schema
                    = true
                -> objectTypeNameBool schema targetFieldDefinition.outputType.namedType
                    = false
                -> abstractRuntimeForFieldDeep? schema abstractTargetParent
                      abstractTargetField rightParentType right
                    = some targetRuntimeType
                -> ∃ runtimeType,
                    abstractRuntimeForFieldDeep? schema abstractTargetParent
                        abstractTargetField abstractTargetParent
                        rightRootSelectionSet
                      = some runtimeType
                    ∧ schema.typeIncludesObjectBool
                        targetFieldDefinition.outputType.namedType runtimeType
                      = true)
          -> selectionSetDeepHeadPromotionAvailable schema rightRootSelectionSet
              rightParentType right
          -> selectionSetDeepProbeFuel schema leftParentType left ≤ leftFuel
          -> selectionSetDeepProbeFuel schema rightParentType right ≤ rightFuel
          -> Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ left
          -> responseName ∉ right.filterMap Selection.responseName?
          -> ¬ Execution.ResponseValue.semanticEquivalent
                (Execution.executeSelectionSetAsResponse schema
                  (fieldPairProbeResolvers schema leftRootSelectionSet targetParent
                    leftField rightField leftArguments rightArguments)
                  variableValues (leftFuel + 1) leftParentType
                  (.object leftSourceRuntimeType (some FieldPairProbeTag.left))
                  left).data
                (Execution.executeSelectionSetAsResponse schema
                  (fieldPairProbeResolvers schema rightRootSelectionSet targetParent
                    leftField rightField leftArguments rightArguments)
                  variableValues (rightFuel + 1) rightParentType
                  (.object rightSourceRuntimeType (some FieldPairProbeTag.right))
                  right).data := by
  intro hschema leftParentType rightParentType leftVariableDefinitions
    rightVariableDefinitions left right leftFuel rightFuel
    leftSourceRuntimeType rightSourceRuntimeType targetParent leftField
    rightField leftArguments rightArguments responseName fieldName arguments
    directives childSelectionSet hleftValid hrightValid hleftFree hrightFree
    hleftNormal hrightNormal hleftObject hrightObject hleftInclude
    hrightInclude hleftPromote hleftHeadPromote hrightPromote
    hrightHeadPromote hleftFuel hrightFuel hleftMem hrightNoResponseName
  let leftResolvers :=
    fieldPairProbeResolvers schema leftRootSelectionSet targetParent leftField
      rightField leftArguments rightArguments
  let rightResolvers :=
    fieldPairProbeResolvers schema rightRootSelectionSet targetParent
      leftField rightField leftArguments rightArguments
  have hleftFieldOk :
      ∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
            childSelectionSet ∈ left ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema leftResolvers variableValues
              (leftFuel + 1)
              (.object leftSourceRuntimeType (some FieldPairProbeTag.left))
              responseName
              [{
                parentType := leftParentType,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(responseName, responseValue)], fieldErrors) := by
    dsimp [leftResolvers]
    exact
      executeField_fieldPairProbe_tagged_object_field_ok_of_valid_normal_promoted_fuel_ge
        schema leftRootSelectionSet variableValues hschema leftParentType
        leftVariableDefinitions left leftFuel leftSourceRuntimeType
        targetParent leftField rightField leftArguments rightArguments
        FieldPairProbeTag.left hleftFuel hleftValid hleftFree hleftNormal
        hleftObject hleftInclude hleftPromote hleftHeadPromote
  have hrightFieldOk :
      ∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
            childSelectionSet ∈ right ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema rightResolvers variableValues
              (rightFuel + 1)
              (.object rightSourceRuntimeType (some FieldPairProbeTag.right))
              responseName
              [{
                parentType := rightParentType,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(responseName, responseValue)], fieldErrors) := by
    dsimp [rightResolvers]
    exact
      executeField_fieldPairProbe_tagged_object_field_ok_of_valid_normal_promoted_fuel_ge
        schema rightRootSelectionSet variableValues hschema rightParentType
        rightVariableDefinitions right rightFuel rightSourceRuntimeType
        targetParent leftField rightField leftArguments rightArguments
        FieldPairProbeTag.right hrightFuel hrightValid hrightFree
        hrightNormal hrightObject hrightInclude hrightPromote
        hrightHeadPromote
  exact
    SemanticSeparation.responseData_not_semanticEquivalent_of_left_responseName_diff_of_field_ok_sources_pair_fuels
      leftResolvers rightResolvers variableValues (leftFuel + 1)
      (rightFuel + 1)
      (.object leftSourceRuntimeType (some FieldPairProbeTag.left))
      (.object rightSourceRuntimeType (some FieldPairProbeTag.right))
      hleftObject hrightObject hleftNormal hrightNormal hleftFree
      hrightFree hleftMem hrightNoResponseName hleftFieldOk hrightFieldOk

theorem
    responseData_not_semanticEquivalent_of_tagged_object_right_responseName_diff_pair_of_valid_normal_promoted_fuel_ge_fuels_roots
    (schema : Schema) (leftRootSelectionSet rightRootSelectionSet : List Selection)
    (variableValues : Execution.VariableValues)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ∀ leftParentType rightParentType leftVariableDefinitions
            rightVariableDefinitions (left right : List Selection)
            leftFuel rightFuel leftSourceRuntimeType rightSourceRuntimeType
            targetParent leftField rightField
            (leftArguments rightArguments : List Argument)
            {responseName fieldName : Name} {arguments : List Argument}
            {directives : List DirectiveApplication}
            {childSelectionSet : List Selection},
          Validation.selectionSetValid schema leftVariableDefinitions leftParentType left
          -> Validation.selectionSetValid schema rightVariableDefinitions
              rightParentType right
          -> selectionSetDirectiveFree left
          -> selectionSetDirectiveFree right
          -> selectionSetNormal schema leftParentType left
          -> selectionSetNormal schema rightParentType right
          -> objectTypeNameBool schema leftParentType = true
          -> objectTypeNameBool schema rightParentType = true
          -> schema.typeIncludesObjectBool leftParentType leftSourceRuntimeType = true
          -> schema.typeIncludesObjectBool rightParentType rightSourceRuntimeType = true
          -> (∀ abstractTargetParent abstractTargetField targetRuntimeType
                  targetFieldDefinition,
                schema.lookupField abstractTargetParent abstractTargetField
                  = some targetFieldDefinition
                -> (TypeRef.named
                      targetFieldDefinition.outputType.namedType).isCompositeBool
                      schema
                    = true
                -> objectTypeNameBool schema targetFieldDefinition.outputType.namedType
                    = false
                -> abstractRuntimeForFieldDeep? schema abstractTargetParent
                      abstractTargetField leftParentType left
                    = some targetRuntimeType
                -> ∃ runtimeType,
                    abstractRuntimeForFieldDeep? schema abstractTargetParent
                        abstractTargetField abstractTargetParent
                        leftRootSelectionSet
                      = some runtimeType
                    ∧ schema.typeIncludesObjectBool
                        targetFieldDefinition.outputType.namedType runtimeType
                      = true)
          -> selectionSetDeepHeadPromotionAvailable schema leftRootSelectionSet
              leftParentType left
          -> (∀ abstractTargetParent abstractTargetField targetRuntimeType
                  targetFieldDefinition,
                schema.lookupField abstractTargetParent abstractTargetField
                  = some targetFieldDefinition
                -> (TypeRef.named
                      targetFieldDefinition.outputType.namedType).isCompositeBool
                      schema
                    = true
                -> objectTypeNameBool schema targetFieldDefinition.outputType.namedType
                    = false
                -> abstractRuntimeForFieldDeep? schema abstractTargetParent
                      abstractTargetField rightParentType right
                    = some targetRuntimeType
                -> ∃ runtimeType,
                    abstractRuntimeForFieldDeep? schema abstractTargetParent
                        abstractTargetField abstractTargetParent
                        rightRootSelectionSet
                      = some runtimeType
                    ∧ schema.typeIncludesObjectBool
                        targetFieldDefinition.outputType.namedType runtimeType
                      = true)
          -> selectionSetDeepHeadPromotionAvailable schema rightRootSelectionSet
              rightParentType right
          -> selectionSetDeepProbeFuel schema leftParentType left ≤ leftFuel
          -> selectionSetDeepProbeFuel schema rightParentType right ≤ rightFuel
          -> Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ right
          -> responseName ∉ left.filterMap Selection.responseName?
          -> ¬ Execution.ResponseValue.semanticEquivalent
                (Execution.executeSelectionSetAsResponse schema
                  (fieldPairProbeResolvers schema leftRootSelectionSet targetParent
                    leftField rightField leftArguments rightArguments)
                  variableValues (leftFuel + 1) leftParentType
                  (.object leftSourceRuntimeType (some FieldPairProbeTag.left))
                  left).data
                (Execution.executeSelectionSetAsResponse schema
                  (fieldPairProbeResolvers schema rightRootSelectionSet targetParent
                    leftField rightField leftArguments rightArguments)
                  variableValues (rightFuel + 1) rightParentType
                  (.object rightSourceRuntimeType (some FieldPairProbeTag.right))
                  right).data := by
  intro hschema leftParentType rightParentType leftVariableDefinitions
    rightVariableDefinitions left right leftFuel rightFuel
    leftSourceRuntimeType rightSourceRuntimeType targetParent leftField
    rightField leftArguments rightArguments responseName fieldName arguments
    directives childSelectionSet hleftValid hrightValid hleftFree hrightFree
    hleftNormal hrightNormal hleftObject hrightObject hleftInclude
    hrightInclude hleftPromote hleftHeadPromote hrightPromote
    hrightHeadPromote hleftFuel hrightFuel hrightMem hleftNoResponseName
  let leftResolvers :=
    fieldPairProbeResolvers schema leftRootSelectionSet targetParent leftField
      rightField leftArguments rightArguments
  let rightResolvers :=
    fieldPairProbeResolvers schema rightRootSelectionSet targetParent
      leftField rightField leftArguments rightArguments
  have hleftFieldOk :
      ∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
            childSelectionSet ∈ left ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema leftResolvers variableValues
              (leftFuel + 1)
              (.object leftSourceRuntimeType (some FieldPairProbeTag.left))
              responseName
              [{
                parentType := leftParentType,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(responseName, responseValue)], fieldErrors) := by
    dsimp [leftResolvers]
    exact
      executeField_fieldPairProbe_tagged_object_field_ok_of_valid_normal_promoted_fuel_ge
        schema leftRootSelectionSet variableValues hschema leftParentType
        leftVariableDefinitions left leftFuel leftSourceRuntimeType
        targetParent leftField rightField leftArguments rightArguments
        FieldPairProbeTag.left hleftFuel hleftValid hleftFree hleftNormal
        hleftObject hleftInclude hleftPromote hleftHeadPromote
  have hrightFieldOk :
      ∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
            childSelectionSet ∈ right ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema rightResolvers variableValues
              (rightFuel + 1)
              (.object rightSourceRuntimeType (some FieldPairProbeTag.right))
              responseName
              [{
                parentType := rightParentType,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(responseName, responseValue)], fieldErrors) := by
    dsimp [rightResolvers]
    exact
      executeField_fieldPairProbe_tagged_object_field_ok_of_valid_normal_promoted_fuel_ge
        schema rightRootSelectionSet variableValues hschema rightParentType
        rightVariableDefinitions right rightFuel rightSourceRuntimeType
        targetParent leftField rightField leftArguments rightArguments
        FieldPairProbeTag.right hrightFuel hrightValid hrightFree
        hrightNormal hrightObject hrightInclude hrightPromote
        hrightHeadPromote
  exact
    SemanticSeparation.responseData_not_semanticEquivalent_of_right_responseName_diff_of_field_ok_sources_pair_fuels
      leftResolvers rightResolvers variableValues (leftFuel + 1)
      (rightFuel + 1)
      (.object leftSourceRuntimeType (some FieldPairProbeTag.left))
      (.object rightSourceRuntimeType (some FieldPairProbeTag.right))
      hleftObject hrightObject hleftNormal hrightNormal hleftFree
      hrightFree hrightMem hleftNoResponseName hleftFieldOk hrightFieldOk

theorem
    responseData_not_semanticEquivalent_of_tagged_object_leaf_field_pair_of_valid_normal_promoted_fuel_ge
    (schema : Schema) (rootSelectionSet : List Selection)
    (variableValues : Execution.VariableValues)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ∀ leftParentType rightParentType leftVariableDefinitions
            rightVariableDefinitions (left right : List Selection) fuel
            leftSourceRuntimeType rightSourceRuntimeType targetParent leftField
            rightField (targetLeftArguments targetRightArguments : List Argument)
            {responseName leftFieldName rightFieldName : Name}
            {leftArguments rightArguments : List Argument}
            {leftDirectives rightDirectives : List DirectiveApplication}
            {leftChildSelectionSet rightChildSelectionSet : List Selection}
            {leftFieldDefinition rightFieldDefinition : FieldDefinition},
          Validation.selectionSetValid schema leftVariableDefinitions leftParentType left
          -> Validation.selectionSetValid schema rightVariableDefinitions
              rightParentType right
          -> selectionSetDirectiveFree left
          -> selectionSetDirectiveFree right
          -> selectionSetNormal schema leftParentType left
          -> selectionSetNormal schema rightParentType right
          -> objectTypeNameBool schema leftParentType = true
          -> objectTypeNameBool schema rightParentType = true
          -> schema.typeIncludesObjectBool leftParentType leftSourceRuntimeType = true
          -> schema.typeIncludesObjectBool rightParentType rightSourceRuntimeType = true
          -> (∀ abstractTargetParent abstractTargetField targetRuntimeType
                  targetFieldDefinition,
                schema.lookupField abstractTargetParent abstractTargetField
                  = some targetFieldDefinition
                -> (TypeRef.named
                      targetFieldDefinition.outputType.namedType).isCompositeBool
                      schema
                    = true
                -> objectTypeNameBool schema targetFieldDefinition.outputType.namedType
                    = false
                -> abstractRuntimeForFieldDeep? schema abstractTargetParent
                      abstractTargetField leftParentType left
                    = some targetRuntimeType
                -> ∃ runtimeType,
                    abstractRuntimeForFieldDeep? schema abstractTargetParent
                        abstractTargetField abstractTargetParent rootSelectionSet
                      = some runtimeType
                    ∧ schema.typeIncludesObjectBool
                        targetFieldDefinition.outputType.namedType runtimeType
                      = true)
          -> selectionSetDeepHeadPromotionAvailable schema rootSelectionSet
              leftParentType left
          -> (∀ abstractTargetParent abstractTargetField targetRuntimeType
                  targetFieldDefinition,
                schema.lookupField abstractTargetParent abstractTargetField
                  = some targetFieldDefinition
                -> (TypeRef.named
                      targetFieldDefinition.outputType.namedType).isCompositeBool
                      schema
                    = true
                -> objectTypeNameBool schema targetFieldDefinition.outputType.namedType
                    = false
                -> abstractRuntimeForFieldDeep? schema abstractTargetParent
                      abstractTargetField rightParentType right
                    = some targetRuntimeType
                -> ∃ runtimeType,
                    abstractRuntimeForFieldDeep? schema abstractTargetParent
                        abstractTargetField abstractTargetParent rootSelectionSet
                      = some runtimeType
                    ∧ schema.typeIncludesObjectBool
                        targetFieldDefinition.outputType.namedType runtimeType
                      = true)
          -> selectionSetDeepHeadPromotionAvailable schema rootSelectionSet
              rightParentType right
          -> selectionSetDeepProbeFuel schema leftParentType left ≤ fuel
          -> selectionSetDeepProbeFuel schema rightParentType right ≤ fuel
          -> Selection.field responseName leftFieldName leftArguments leftDirectives
                leftChildSelectionSet
              ∈ left
          -> Selection.field responseName rightFieldName rightArguments
                rightDirectives rightChildSelectionSet
              ∈ right
          -> schema.lookupField leftParentType leftFieldName = some leftFieldDefinition
          -> schema.lookupField rightParentType rightFieldName = some rightFieldDefinition
          -> (TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool
                schema
              = false
          -> (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool
                schema
              = false
          -> ¬ Execution.ResponseValue.semanticEquivalent
                (Execution.executeSelectionSetAsResponse schema
                  (fieldPairProbeResolvers schema rootSelectionSet targetParent
                    leftField rightField targetLeftArguments targetRightArguments)
                  variableValues (fuel + 1) leftParentType
                  (.object leftSourceRuntimeType (some FieldPairProbeTag.left))
                  left).data
                (Execution.executeSelectionSetAsResponse schema
                  (fieldPairProbeResolvers schema rootSelectionSet targetParent
                    leftField rightField targetLeftArguments targetRightArguments)
                  variableValues (fuel + 1) rightParentType
                  (.object rightSourceRuntimeType (some FieldPairProbeTag.right))
                  right).data := by
  intro hschema leftParentType rightParentType leftVariableDefinitions
    rightVariableDefinitions left right fuel leftSourceRuntimeType
    rightSourceRuntimeType targetParent leftField rightField
    targetLeftArguments targetRightArguments responseName leftFieldName
    rightFieldName leftArguments rightArguments leftDirectives
    rightDirectives leftChildSelectionSet rightChildSelectionSet
    leftFieldDefinition rightFieldDefinition hleftValid hrightValid
    hleftFree hrightFree hleftNormal hrightNormal hleftObject hrightObject
    hleftInclude hrightInclude hleftPromote hleftHeadPromote hrightPromote
    hrightHeadPromote hleftFuel hrightFuel hleftMem hrightMem hleftLookup
    hrightLookup hleftLeaf hrightLeaf
  let resolvers :=
    fieldPairProbeResolvers schema rootSelectionSet targetParent leftField
      rightField targetLeftArguments targetRightArguments
  have hleftLeafFuel :
      leafProbeFuel leftFieldDefinition.outputType ≤ fuel := by
    have hlocal :
        leafProbeFuel leftFieldDefinition.outputType
          ≤ selectionSetDeepProbeFuel schema leftParentType left :=
      leafProbeFuel_le_selectionSetDeepProbeFuel_of_field_mem schema
        leftParentType hleftMem hleftLookup
    omega
  have hrightLeafFuel :
      leafProbeFuel rightFieldDefinition.outputType ≤ fuel := by
    have hlocal :
        leafProbeFuel rightFieldDefinition.outputType
          ≤ selectionSetDeepProbeFuel schema rightParentType right :=
      leafProbeFuel_le_selectionSetDeepProbeFuel_of_field_mem schema
        rightParentType hrightMem hrightLookup
    omega
  have hleftFieldOk :
      ∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
            childSelectionSet ∈ left ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema resolvers variableValues (fuel + 1)
              (.object leftSourceRuntimeType (some FieldPairProbeTag.left))
              responseName
              [{
                parentType := leftParentType,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(responseName, responseValue)], fieldErrors) := by
    dsimp [resolvers]
    exact
      executeField_fieldPairProbe_tagged_object_field_ok_of_valid_normal_promoted_fuel_ge
        schema rootSelectionSet variableValues hschema leftParentType
        leftVariableDefinitions left fuel leftSourceRuntimeType targetParent
        leftField rightField targetLeftArguments targetRightArguments
        FieldPairProbeTag.left hleftFuel hleftValid hleftFree hleftNormal
        hleftObject hleftInclude hleftPromote hleftHeadPromote
  have hrightFieldOk :
      ∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
            childSelectionSet ∈ right ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema resolvers variableValues (fuel + 1)
              (.object rightSourceRuntimeType (some FieldPairProbeTag.right))
              responseName
              [{
                parentType := rightParentType,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(responseName, responseValue)], fieldErrors) := by
    dsimp [resolvers]
    exact
      executeField_fieldPairProbe_tagged_object_field_ok_of_valid_normal_promoted_fuel_ge
        schema rootSelectionSet variableValues hschema rightParentType
        rightVariableDefinitions right fuel rightSourceRuntimeType
        targetParent leftField rightField targetLeftArguments
        targetRightArguments FieldPairProbeTag.right hrightFuel hrightValid
        hrightFree hrightNormal hrightObject hrightInclude hrightPromote
        hrightHeadPromote
  have hleftTarget :
      Execution.executeField schema resolvers variableValues (fuel + 1)
        (.object leftSourceRuntimeType (some FieldPairProbeTag.left))
        responseName
        [{
          parentType := leftParentType,
          responseName := responseName,
          fieldName := leftFieldName,
          arguments := leftArguments,
          selectionSet := leftChildSelectionSet
        }]
      =
      .ok ([(responseName,
        leafProbeResponseValue leftFieldDefinition.outputType
          FieldPairProbeTag.left.scalar)], 0) := by
    dsimp [resolvers]
    exact
      executeField_fieldPairProbe_tagged_object_leaf schema rootSelectionSet
        variableValues fuel targetParent leftField rightField leftParentType
        leftFieldName leftSourceRuntimeType responseName targetLeftArguments
        targetRightArguments leftArguments FieldPairProbeTag.left
        leftChildSelectionSet leftFieldDefinition hleftLookup hleftLeafFuel
        hleftLeaf
  have hrightTarget :
      Execution.executeField schema resolvers variableValues (fuel + 1)
        (.object rightSourceRuntimeType (some FieldPairProbeTag.right))
        responseName
        [{
          parentType := rightParentType,
          responseName := responseName,
          fieldName := rightFieldName,
          arguments := rightArguments,
          selectionSet := rightChildSelectionSet
        }]
      =
      .ok ([(responseName,
        leafProbeResponseValue rightFieldDefinition.outputType
          FieldPairProbeTag.right.scalar)], 0) := by
    dsimp [resolvers]
    exact
      executeField_fieldPairProbe_tagged_object_leaf schema rootSelectionSet
        variableValues fuel targetParent leftField rightField rightParentType
        rightFieldName rightSourceRuntimeType responseName targetLeftArguments
        targetRightArguments rightArguments FieldPairProbeTag.right
        rightChildSelectionSet rightFieldDefinition hrightLookup
        hrightLeafFuel hrightLeaf
  exact
    SemanticSeparation.responseData_not_semanticEquivalent_of_field_value_diff_of_field_ok_pair
      resolvers resolvers variableValues (fuel + 1)
      (.object leftSourceRuntimeType (some FieldPairProbeTag.left))
      (.object rightSourceRuntimeType (some FieldPairProbeTag.right))
      hleftObject hrightObject hleftNormal hrightNormal hleftFree
      hrightFree hleftMem hrightMem hleftTarget hrightTarget
      (leafProbeResponseValue_not_semanticEquivalent_of_ne_any
        leftFieldDefinition.outputType rightFieldDefinition.outputType
        (by simp [FieldPairProbeTag.scalar]))
      hleftFieldOk hrightFieldOk

theorem
    responseData_not_semanticEquivalent_of_tagged_object_leaf_field_pair_of_valid_normal_promoted_fuel_ge_fuels
    (schema : Schema) (rootSelectionSet : List Selection)
    (variableValues : Execution.VariableValues)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ∀ leftParentType rightParentType leftVariableDefinitions
            rightVariableDefinitions (left right : List Selection)
            leftFuel rightFuel leftSourceRuntimeType rightSourceRuntimeType
            targetParent leftField rightField
            (targetLeftArguments targetRightArguments : List Argument)
            {responseName leftFieldName rightFieldName : Name}
            {leftArguments rightArguments : List Argument}
            {leftDirectives rightDirectives : List DirectiveApplication}
            {leftChildSelectionSet rightChildSelectionSet : List Selection}
            {leftFieldDefinition rightFieldDefinition : FieldDefinition},
          Validation.selectionSetValid schema leftVariableDefinitions leftParentType left
          -> Validation.selectionSetValid schema rightVariableDefinitions
              rightParentType right
          -> selectionSetDirectiveFree left
          -> selectionSetDirectiveFree right
          -> selectionSetNormal schema leftParentType left
          -> selectionSetNormal schema rightParentType right
          -> objectTypeNameBool schema leftParentType = true
          -> objectTypeNameBool schema rightParentType = true
          -> schema.typeIncludesObjectBool leftParentType leftSourceRuntimeType = true
          -> schema.typeIncludesObjectBool rightParentType rightSourceRuntimeType = true
          -> (∀ abstractTargetParent abstractTargetField targetRuntimeType
                  targetFieldDefinition,
                schema.lookupField abstractTargetParent abstractTargetField
                  = some targetFieldDefinition
                -> (TypeRef.named
                      targetFieldDefinition.outputType.namedType).isCompositeBool
                      schema
                    = true
                -> objectTypeNameBool schema targetFieldDefinition.outputType.namedType
                    = false
                -> abstractRuntimeForFieldDeep? schema abstractTargetParent
                      abstractTargetField leftParentType left
                    = some targetRuntimeType
                -> ∃ runtimeType,
                    abstractRuntimeForFieldDeep? schema abstractTargetParent
                        abstractTargetField abstractTargetParent rootSelectionSet
                      = some runtimeType
                    ∧ schema.typeIncludesObjectBool
                        targetFieldDefinition.outputType.namedType runtimeType
                      = true)
          -> selectionSetDeepHeadPromotionAvailable schema rootSelectionSet
              leftParentType left
          -> (∀ abstractTargetParent abstractTargetField targetRuntimeType
                  targetFieldDefinition,
                schema.lookupField abstractTargetParent abstractTargetField
                  = some targetFieldDefinition
                -> (TypeRef.named
                      targetFieldDefinition.outputType.namedType).isCompositeBool
                      schema
                    = true
                -> objectTypeNameBool schema targetFieldDefinition.outputType.namedType
                    = false
                -> abstractRuntimeForFieldDeep? schema abstractTargetParent
                      abstractTargetField rightParentType right
                    = some targetRuntimeType
                -> ∃ runtimeType,
                    abstractRuntimeForFieldDeep? schema abstractTargetParent
                        abstractTargetField abstractTargetParent rootSelectionSet
                      = some runtimeType
                    ∧ schema.typeIncludesObjectBool
                        targetFieldDefinition.outputType.namedType runtimeType
                      = true)
          -> selectionSetDeepHeadPromotionAvailable schema rootSelectionSet
              rightParentType right
          -> selectionSetDeepProbeFuel schema leftParentType left ≤ leftFuel
          -> selectionSetDeepProbeFuel schema rightParentType right ≤ rightFuel
          -> Selection.field responseName leftFieldName leftArguments leftDirectives
                leftChildSelectionSet
              ∈ left
          -> Selection.field responseName rightFieldName rightArguments
                rightDirectives rightChildSelectionSet
              ∈ right
          -> schema.lookupField leftParentType leftFieldName = some leftFieldDefinition
          -> schema.lookupField rightParentType rightFieldName = some rightFieldDefinition
          -> (TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool
                schema
              = false
          -> (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool
                schema
              = false
          -> ¬ Execution.ResponseValue.semanticEquivalent
                (Execution.executeSelectionSetAsResponse schema
                  (fieldPairProbeResolvers schema rootSelectionSet targetParent
                    leftField rightField targetLeftArguments targetRightArguments)
                  variableValues (leftFuel + 1) leftParentType
                  (.object leftSourceRuntimeType (some FieldPairProbeTag.left))
                  left).data
                (Execution.executeSelectionSetAsResponse schema
                  (fieldPairProbeResolvers schema rootSelectionSet targetParent
                    leftField rightField targetLeftArguments targetRightArguments)
                  variableValues (rightFuel + 1) rightParentType
                  (.object rightSourceRuntimeType (some FieldPairProbeTag.right))
                  right).data := by
  intro hschema leftParentType rightParentType leftVariableDefinitions
    rightVariableDefinitions left right leftFuel rightFuel
    leftSourceRuntimeType rightSourceRuntimeType targetParent leftField
    rightField targetLeftArguments targetRightArguments responseName
    leftFieldName rightFieldName leftArguments rightArguments
    leftDirectives rightDirectives leftChildSelectionSet
    rightChildSelectionSet leftFieldDefinition rightFieldDefinition
    hleftValid hrightValid hleftFree hrightFree hleftNormal hrightNormal
    hleftObject hrightObject hleftInclude hrightInclude hleftPromote
    hleftHeadPromote hrightPromote hrightHeadPromote hleftFuel
    hrightFuel hleftMem hrightMem hleftLookup hrightLookup hleftLeaf
    hrightLeaf
  let resolvers :=
    fieldPairProbeResolvers schema rootSelectionSet targetParent leftField
      rightField targetLeftArguments targetRightArguments
  have hleftLeafFuel :
      leafProbeFuel leftFieldDefinition.outputType ≤ leftFuel := by
    have hlocal :
        leafProbeFuel leftFieldDefinition.outputType
          ≤ selectionSetDeepProbeFuel schema leftParentType left :=
      leafProbeFuel_le_selectionSetDeepProbeFuel_of_field_mem schema
        leftParentType hleftMem hleftLookup
    omega
  have hrightLeafFuel :
      leafProbeFuel rightFieldDefinition.outputType ≤ rightFuel := by
    have hlocal :
        leafProbeFuel rightFieldDefinition.outputType
          ≤ selectionSetDeepProbeFuel schema rightParentType right :=
      leafProbeFuel_le_selectionSetDeepProbeFuel_of_field_mem schema
        rightParentType hrightMem hrightLookup
    omega
  have hleftFieldOk :
      ∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
            childSelectionSet ∈ left ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema resolvers variableValues
              (leftFuel + 1)
              (.object leftSourceRuntimeType (some FieldPairProbeTag.left))
              responseName
              [{
                parentType := leftParentType,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(responseName, responseValue)], fieldErrors) := by
    dsimp [resolvers]
    exact
      executeField_fieldPairProbe_tagged_object_field_ok_of_valid_normal_promoted_fuel_ge
        schema rootSelectionSet variableValues hschema leftParentType
        leftVariableDefinitions left leftFuel leftSourceRuntimeType
        targetParent leftField rightField targetLeftArguments
        targetRightArguments FieldPairProbeTag.left hleftFuel hleftValid
        hleftFree hleftNormal hleftObject hleftInclude hleftPromote
        hleftHeadPromote
  have hrightFieldOk :
      ∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
            childSelectionSet ∈ right ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema resolvers variableValues
              (rightFuel + 1)
              (.object rightSourceRuntimeType (some FieldPairProbeTag.right))
              responseName
              [{
                parentType := rightParentType,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(responseName, responseValue)], fieldErrors) := by
    dsimp [resolvers]
    exact
      executeField_fieldPairProbe_tagged_object_field_ok_of_valid_normal_promoted_fuel_ge
        schema rootSelectionSet variableValues hschema rightParentType
        rightVariableDefinitions right rightFuel rightSourceRuntimeType
        targetParent leftField rightField targetLeftArguments
        targetRightArguments FieldPairProbeTag.right hrightFuel hrightValid
        hrightFree hrightNormal hrightObject hrightInclude hrightPromote
        hrightHeadPromote
  have hleftTarget :
      Execution.executeField schema resolvers variableValues
        (leftFuel + 1)
        (.object leftSourceRuntimeType (some FieldPairProbeTag.left))
        responseName
        [{
          parentType := leftParentType,
          responseName := responseName,
          fieldName := leftFieldName,
          arguments := leftArguments,
          selectionSet := leftChildSelectionSet
        }]
      =
      .ok ([(responseName,
        leafProbeResponseValue leftFieldDefinition.outputType
          FieldPairProbeTag.left.scalar)], 0) := by
    dsimp [resolvers]
    exact
      executeField_fieldPairProbe_tagged_object_leaf schema rootSelectionSet
        variableValues leftFuel targetParent leftField rightField
        leftParentType leftFieldName leftSourceRuntimeType responseName
        targetLeftArguments targetRightArguments leftArguments
        FieldPairProbeTag.left leftChildSelectionSet leftFieldDefinition
        hleftLookup hleftLeafFuel hleftLeaf
  have hrightTarget :
      Execution.executeField schema resolvers variableValues
        (rightFuel + 1)
        (.object rightSourceRuntimeType (some FieldPairProbeTag.right))
        responseName
        [{
          parentType := rightParentType,
          responseName := responseName,
          fieldName := rightFieldName,
          arguments := rightArguments,
          selectionSet := rightChildSelectionSet
        }]
      =
      .ok ([(responseName,
        leafProbeResponseValue rightFieldDefinition.outputType
          FieldPairProbeTag.right.scalar)], 0) := by
    dsimp [resolvers]
    exact
      executeField_fieldPairProbe_tagged_object_leaf schema rootSelectionSet
        variableValues rightFuel targetParent leftField rightField
        rightParentType rightFieldName rightSourceRuntimeType responseName
        targetLeftArguments targetRightArguments rightArguments
        FieldPairProbeTag.right rightChildSelectionSet rightFieldDefinition
        hrightLookup hrightLeafFuel hrightLeaf
  exact
    SemanticSeparation.responseData_not_semanticEquivalent_of_field_value_diff_of_field_ok_pair_fuels
      resolvers resolvers variableValues (leftFuel + 1) (rightFuel + 1)
      (.object leftSourceRuntimeType (some FieldPairProbeTag.left))
      (.object rightSourceRuntimeType (some FieldPairProbeTag.right))
      hleftObject hrightObject hleftNormal hrightNormal hleftFree
      hrightFree hleftMem hrightMem hleftTarget hrightTarget
      (leafProbeResponseValue_not_semanticEquivalent_of_ne_any
        leftFieldDefinition.outputType rightFieldDefinition.outputType
        (by simp [FieldPairProbeTag.scalar]))
      hleftFieldOk hrightFieldOk

theorem
    responseData_not_semanticEquivalent_of_tagged_object_leaf_field_pair_of_valid_normal_promoted_fuel_ge_fuels_roots
    (schema : Schema) (leftRootSelectionSet rightRootSelectionSet : List Selection)
    (variableValues : Execution.VariableValues)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ∀ leftParentType rightParentType leftVariableDefinitions
            rightVariableDefinitions (left right : List Selection)
            leftFuel rightFuel leftSourceRuntimeType rightSourceRuntimeType
            targetParent leftField rightField
            (targetLeftArguments targetRightArguments : List Argument)
            {responseName leftFieldName rightFieldName : Name}
            {leftArguments rightArguments : List Argument}
            {leftDirectives rightDirectives : List DirectiveApplication}
            {leftChildSelectionSet rightChildSelectionSet : List Selection}
            {leftFieldDefinition rightFieldDefinition : FieldDefinition},
          Validation.selectionSetValid schema leftVariableDefinitions leftParentType left
          -> Validation.selectionSetValid schema rightVariableDefinitions
              rightParentType right
          -> selectionSetDirectiveFree left
          -> selectionSetDirectiveFree right
          -> selectionSetNormal schema leftParentType left
          -> selectionSetNormal schema rightParentType right
          -> objectTypeNameBool schema leftParentType = true
          -> objectTypeNameBool schema rightParentType = true
          -> schema.typeIncludesObjectBool leftParentType leftSourceRuntimeType = true
          -> schema.typeIncludesObjectBool rightParentType rightSourceRuntimeType = true
          -> (∀ abstractTargetParent abstractTargetField targetRuntimeType
                  targetFieldDefinition,
                schema.lookupField abstractTargetParent abstractTargetField
                  = some targetFieldDefinition
                -> (TypeRef.named
                      targetFieldDefinition.outputType.namedType).isCompositeBool
                      schema
                    = true
                -> objectTypeNameBool schema targetFieldDefinition.outputType.namedType
                    = false
                -> abstractRuntimeForFieldDeep? schema abstractTargetParent
                      abstractTargetField leftParentType left
                    = some targetRuntimeType
                -> ∃ runtimeType,
                    abstractRuntimeForFieldDeep? schema abstractTargetParent
                        abstractTargetField abstractTargetParent leftRootSelectionSet
                      = some runtimeType
                    ∧ schema.typeIncludesObjectBool
                        targetFieldDefinition.outputType.namedType runtimeType
                      = true)
          -> selectionSetDeepHeadPromotionAvailable schema leftRootSelectionSet
              leftParentType left
          -> (∀ abstractTargetParent abstractTargetField targetRuntimeType
                  targetFieldDefinition,
                schema.lookupField abstractTargetParent abstractTargetField
                  = some targetFieldDefinition
                -> (TypeRef.named
                      targetFieldDefinition.outputType.namedType).isCompositeBool
                      schema
                    = true
                -> objectTypeNameBool schema targetFieldDefinition.outputType.namedType
                    = false
                -> abstractRuntimeForFieldDeep? schema abstractTargetParent
                      abstractTargetField rightParentType right
                    = some targetRuntimeType
                -> ∃ runtimeType,
                    abstractRuntimeForFieldDeep? schema abstractTargetParent
                        abstractTargetField abstractTargetParent rightRootSelectionSet
                      = some runtimeType
                    ∧ schema.typeIncludesObjectBool
                        targetFieldDefinition.outputType.namedType runtimeType
                      = true)
          -> selectionSetDeepHeadPromotionAvailable schema rightRootSelectionSet
              rightParentType right
          -> selectionSetDeepProbeFuel schema leftParentType left ≤ leftFuel
          -> selectionSetDeepProbeFuel schema rightParentType right ≤ rightFuel
          -> Selection.field responseName leftFieldName leftArguments leftDirectives
                leftChildSelectionSet
              ∈ left
          -> Selection.field responseName rightFieldName rightArguments
                rightDirectives rightChildSelectionSet
              ∈ right
          -> schema.lookupField leftParentType leftFieldName = some leftFieldDefinition
          -> schema.lookupField rightParentType rightFieldName = some rightFieldDefinition
          -> (TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool
                schema
              = false
          -> (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool
                schema
              = false
          -> ¬ Execution.ResponseValue.semanticEquivalent
                (Execution.executeSelectionSetAsResponse schema
                  (fieldPairProbeResolvers schema leftRootSelectionSet targetParent
                    leftField rightField targetLeftArguments targetRightArguments)
                  variableValues (leftFuel + 1) leftParentType
                  (.object leftSourceRuntimeType (some FieldPairProbeTag.left))
                  left).data
                (Execution.executeSelectionSetAsResponse schema
                  (fieldPairProbeResolvers schema rightRootSelectionSet targetParent
                    leftField rightField targetLeftArguments targetRightArguments)
                  variableValues (rightFuel + 1) rightParentType
                  (.object rightSourceRuntimeType (some FieldPairProbeTag.right))
                  right).data := by
  intro hschema leftParentType rightParentType leftVariableDefinitions
    rightVariableDefinitions left right leftFuel rightFuel
    leftSourceRuntimeType rightSourceRuntimeType targetParent leftField
    rightField targetLeftArguments targetRightArguments responseName
    leftFieldName rightFieldName leftArguments rightArguments
    leftDirectives rightDirectives leftChildSelectionSet
    rightChildSelectionSet leftFieldDefinition rightFieldDefinition
    hleftValid hrightValid hleftFree hrightFree hleftNormal hrightNormal
    hleftObject hrightObject hleftInclude hrightInclude hleftPromote
    hleftHeadPromote hrightPromote hrightHeadPromote hleftFuel
    hrightFuel hleftMem hrightMem hleftLookup hrightLookup hleftLeaf
    hrightLeaf
  let leftResolvers :=
    fieldPairProbeResolvers schema leftRootSelectionSet targetParent
      leftField rightField targetLeftArguments targetRightArguments
  let rightResolvers :=
    fieldPairProbeResolvers schema rightRootSelectionSet targetParent
      leftField rightField targetLeftArguments targetRightArguments
  have hleftLeafFuel :
      leafProbeFuel leftFieldDefinition.outputType ≤ leftFuel := by
    have hlocal :
        leafProbeFuel leftFieldDefinition.outputType
          ≤ selectionSetDeepProbeFuel schema leftParentType left :=
      leafProbeFuel_le_selectionSetDeepProbeFuel_of_field_mem schema
        leftParentType hleftMem hleftLookup
    omega
  have hrightLeafFuel :
      leafProbeFuel rightFieldDefinition.outputType ≤ rightFuel := by
    have hlocal :
        leafProbeFuel rightFieldDefinition.outputType
          ≤ selectionSetDeepProbeFuel schema rightParentType right :=
      leafProbeFuel_le_selectionSetDeepProbeFuel_of_field_mem schema
        rightParentType hrightMem hrightLookup
    omega
  have hleftFieldOk :
      ∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
            childSelectionSet ∈ left ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema leftResolvers variableValues
              (leftFuel + 1)
              (.object leftSourceRuntimeType (some FieldPairProbeTag.left))
              responseName
              [{
                parentType := leftParentType,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(responseName, responseValue)], fieldErrors) := by
    dsimp [leftResolvers]
    exact
      executeField_fieldPairProbe_tagged_object_field_ok_of_valid_normal_promoted_fuel_ge
        schema leftRootSelectionSet variableValues hschema leftParentType
        leftVariableDefinitions left leftFuel leftSourceRuntimeType
        targetParent leftField rightField targetLeftArguments
        targetRightArguments FieldPairProbeTag.left hleftFuel hleftValid
        hleftFree hleftNormal hleftObject hleftInclude hleftPromote
        hleftHeadPromote
  have hrightFieldOk :
      ∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
            childSelectionSet ∈ right ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema rightResolvers variableValues
              (rightFuel + 1)
              (.object rightSourceRuntimeType (some FieldPairProbeTag.right))
              responseName
              [{
                parentType := rightParentType,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(responseName, responseValue)], fieldErrors) := by
    dsimp [rightResolvers]
    exact
      executeField_fieldPairProbe_tagged_object_field_ok_of_valid_normal_promoted_fuel_ge
        schema rightRootSelectionSet variableValues hschema rightParentType
        rightVariableDefinitions right rightFuel rightSourceRuntimeType
        targetParent leftField rightField targetLeftArguments
        targetRightArguments FieldPairProbeTag.right hrightFuel hrightValid
        hrightFree hrightNormal hrightObject hrightInclude hrightPromote
        hrightHeadPromote
  have hleftTarget :
      Execution.executeField schema leftResolvers variableValues
        (leftFuel + 1)
        (.object leftSourceRuntimeType (some FieldPairProbeTag.left))
        responseName
        [{
          parentType := leftParentType,
          responseName := responseName,
          fieldName := leftFieldName,
          arguments := leftArguments,
          selectionSet := leftChildSelectionSet
        }]
      =
      .ok ([(responseName,
        leafProbeResponseValue leftFieldDefinition.outputType
          FieldPairProbeTag.left.scalar)], 0) := by
    dsimp [leftResolvers]
    exact
      executeField_fieldPairProbe_tagged_object_leaf schema
        leftRootSelectionSet variableValues leftFuel targetParent leftField
        rightField leftParentType leftFieldName leftSourceRuntimeType
        responseName targetLeftArguments targetRightArguments leftArguments
        FieldPairProbeTag.left leftChildSelectionSet leftFieldDefinition
        hleftLookup hleftLeafFuel hleftLeaf
  have hrightTarget :
      Execution.executeField schema rightResolvers variableValues
        (rightFuel + 1)
        (.object rightSourceRuntimeType (some FieldPairProbeTag.right))
        responseName
        [{
          parentType := rightParentType,
          responseName := responseName,
          fieldName := rightFieldName,
          arguments := rightArguments,
          selectionSet := rightChildSelectionSet
        }]
      =
      .ok ([(responseName,
        leafProbeResponseValue rightFieldDefinition.outputType
          FieldPairProbeTag.right.scalar)], 0) := by
    dsimp [rightResolvers]
    exact
      executeField_fieldPairProbe_tagged_object_leaf schema
        rightRootSelectionSet variableValues rightFuel targetParent leftField
        rightField rightParentType rightFieldName rightSourceRuntimeType
        responseName targetLeftArguments targetRightArguments rightArguments
        FieldPairProbeTag.right rightChildSelectionSet rightFieldDefinition
        hrightLookup hrightLeafFuel hrightLeaf
  exact
    SemanticSeparation.responseData_not_semanticEquivalent_of_field_value_diff_of_field_ok_pair_fuels
      leftResolvers rightResolvers variableValues (leftFuel + 1)
      (rightFuel + 1)
      (.object leftSourceRuntimeType (some FieldPairProbeTag.left))
      (.object rightSourceRuntimeType (some FieldPairProbeTag.right))
      hleftObject hrightObject hleftNormal hrightNormal hleftFree
      hrightFree hleftMem hrightMem hleftTarget hrightTarget
      (leafProbeResponseValue_not_semanticEquivalent_of_ne_any
        leftFieldDefinition.outputType rightFieldDefinition.outputType
        (by simp [FieldPairProbeTag.scalar]))
      hleftFieldOk hrightFieldOk

end GroundTypeNormalization

end NormalForm

end GraphQL
