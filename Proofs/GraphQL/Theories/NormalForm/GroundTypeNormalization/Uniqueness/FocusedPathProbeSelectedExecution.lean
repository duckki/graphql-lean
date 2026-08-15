import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.FocusedPathProbeSelectedRuntime

/-!
Selected-path response execution and semantic parent lifts for focused probes.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

theorem
    pathLocalSelectionSetObservableLeafAtRuntime_object_child_of_valid_normal_support_context
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {selectionSet currentSelectionSet childSelectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> objectTypeNameBool schema parentType = true
      -> PathLocalSupportValidNormal schema parentType currentSelectionSet
      -> PathLocalSelectionSetCurrentContext selectionSet currentSelectionSet
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> (∀ childRuntime,
            ((objectTypeNameBool schema fieldDefinition.outputType.namedType = true
                ∧ childRuntime = fieldDefinition.outputType.namedType)
              ∨ ((TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool
                      schema
                    = true
                  ∧ objectTypeNameBool schema fieldDefinition.outputType.namedType = false
                  ∧ abstractRuntimeForFieldHeadDeep? schema parentType fieldName
                      arguments parentType currentSelectionSet
                    = some childRuntime))
            -> PathLocalSelectionSetObservableLeafAtRuntime schema
                fieldDefinition.outputType.namedType childRuntime
                (fieldPairPathLocalNextSelectionSet schema parentType childRuntime
                  fieldName arguments currentSelectionSet)
                childSelectionSet)
      -> PathLocalSelectionSetObservableLeafAtRuntime schema parentType
          parentType currentSelectionSet selectionSet := by
  intro hschema hvalid hnormal hobject hsupport hcontext hmem hlookup
    hcomposite hchildObservable
  rcases
      pathLocalCompositeFieldChildReady_of_valid_normal_support_context
        hschema hvalid hnormal hobject hsupport hcontext hmem hlookup
        hcomposite with
    ⟨childRuntime, hruntime, _hinclude, _hchildSupport, _hobjectContext,
      _habstractContext⟩
  exact
    PathLocalSelectionSetObservableLeafAtRuntime.objectChild hobject hmem
      hlookup
      (by
        unfold Schema.isCompositeType
        unfold TypeRef.isCompositeBool TypeRef.namedType at hcomposite
        cases hlookupType : schema.lookupType
            fieldDefinition.outputType.namedType with
        | none =>
            simp [hlookupType] at hcomposite
        | some typeDefinition =>
            have htypeComposite :
                TypeDefinition.isCompositeType typeDefinition := by
              cases typeDefinition <;>
                simp [hlookupType, TypeDefinition.isCompositeType] at hcomposite ⊢
            exact ⟨typeDefinition, rfl, htypeComposite⟩)
      hruntime
      (hchildObservable childRuntime hruntime)

def PathLocalTaggedSelectionSetResponseDiffWitness
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (normalParentType runtimeType targetParent leftField rightField : Name)
    (leftArguments rightArguments : List Argument)
    (leftRuntime rightRuntime : Name)
    (currentSelectionSet selectionSet : List Selection)
    : Prop :=
  schema.typeIncludesObjectBool normalParentType runtimeType = true
  ∧ ∃ leftFields leftErrors rightFields rightErrors,
      Execution.executeSelectionSetAsResponse schema
          (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
            (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
              rightInitialSelectionSet targetParent leftField rightField
              leftArguments rightArguments leftRuntime rightRuntime)
            targetParent leftField rightField leftArguments rightArguments)
          variableValues fuel runtimeType
          (projectionTargetResolverValue
            (.object runtimeType
              (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                currentSelectionSet)))
          selectionSet
        = ({ data := Execution.ResponseValue.object leftFields, errors := leftErrors }
            : Execution.Response)
      ∧ Execution.executeSelectionSetAsResponse schema
          (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
            (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
              rightInitialSelectionSet targetParent leftField rightField
              leftArguments rightArguments leftRuntime rightRuntime)
            targetParent leftField rightField leftArguments rightArguments)
          variableValues fuel runtimeType
          (projectionTargetResolverValue
            (.object runtimeType
              (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                currentSelectionSet)))
          selectionSet
        = ({ data := Execution.ResponseValue.object rightFields, errors := rightErrors }
            : Execution.Response)
      ∧ ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.ResponseValue.object leftFields)
            (Execution.ResponseValue.object rightFields)

def SelectedPathTaggedSelectionSetResponseDiffWitness
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (normalParentType runtimeType targetParent leftField rightField : Name)
    (leftArguments rightArguments : List Argument)
    (leftRuntime rightRuntime : Name)
    (leftCurrentSelectionSet rightCurrentSelectionSet : List Selection)
    (leftSpine rightSpine : List NormalSelectionSetObservableFieldStep)
    (selectionSet : List Selection)
    : Prop :=
  schema.typeIncludesObjectBool normalParentType runtimeType = true
  ∧ ∃ leftFields leftErrors rightFields rightErrors,
      Execution.executeSelectionSetAsResponse schema
          (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
            (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
              rightInitialSelectionSet leftInitialSpine rightInitialSpine
              targetParent leftField rightField leftArguments rightArguments
              leftRuntime rightRuntime)
            targetParent leftField rightField leftArguments rightArguments)
          variableValues fuel runtimeType
          (projectionTargetResolverValue
            (.object runtimeType
              (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
                leftCurrentSelectionSet leftSpine)))
          selectionSet
        = ({ data := Execution.ResponseValue.object leftFields, errors := leftErrors }
            : Execution.Response)
      ∧ Execution.executeSelectionSetAsResponse schema
          (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
            (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
              rightInitialSelectionSet leftInitialSpine rightInitialSpine
              targetParent leftField rightField leftArguments rightArguments
              leftRuntime rightRuntime)
            targetParent leftField rightField leftArguments rightArguments)
          variableValues fuel runtimeType
          (projectionTargetResolverValue
            (.object runtimeType
              (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                rightCurrentSelectionSet rightSpine)))
          selectionSet
        = ({ data := Execution.ResponseValue.object rightFields, errors := rightErrors }
            : Execution.Response)
      ∧ ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.ResponseValue.object leftFields)
            (Execution.ResponseValue.object rightFields)

theorem
    responseData_not_semanticEquivalent_of_selectedPathTaggedSelectionSetResponseDiffWitness
    {schema : Schema}
    {rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection}
    {leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep}
    {variableValues : Execution.VariableValues} {fuel : Nat}
    {normalParentType runtimeType targetParent leftField rightField : Name}
    {leftArguments rightArguments : List Argument} {leftRuntime rightRuntime : Name}
    {leftCurrentSelectionSet rightCurrentSelectionSet : List Selection}
    {leftSpine rightSpine : List NormalSelectionSetObservableFieldStep}
    {selectionSet : List Selection}
    : SelectedPathTaggedSelectionSetResponseDiffWitness schema
        rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
        leftInitialSpine rightInitialSpine variableValues fuel
        normalParentType runtimeType targetParent leftField rightField
        leftArguments rightArguments leftRuntime rightRuntime
        leftCurrentSelectionSet rightCurrentSelectionSet leftSpine rightSpine
        selectionSet
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet leftInitialSpine rightInitialSpine
                  targetParent leftField rightField leftArguments rightArguments
                  leftRuntime rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues fuel runtimeType
              (projectionTargetResolverValue
                (.object runtimeType
                  (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
                    leftCurrentSelectionSet leftSpine)))
              selectionSet).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet leftInitialSpine rightInitialSpine
                  targetParent leftField rightField leftArguments rightArguments
                  leftRuntime rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues fuel runtimeType
              (projectionTargetResolverValue
                (.object runtimeType
                  (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                    rightCurrentSelectionSet rightSpine)))
              selectionSet).data := by
  intro hwitness hsemantic
  rcases hwitness with
    ⟨_hinclude, leftFields, leftErrors, rightFields, rightErrors,
      hleft, hright, hnot⟩
  exact hnot (by simpa [hleft, hright] using hsemantic)

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_leaf_field_of_field_ok
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine leftSpine rightSpine
      : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField parentType
      leftSourceRuntimeType rightSourceRuntimeType
      : Name)
    (leftArguments rightArguments : List Argument) (leftRuntime rightRuntime : Name)
    {selectionSet : List Selection} {responseName fieldName : Name}
    {arguments : List Argument} {directives : List DirectiveApplication}
    {childSelectionSet : List Selection} {fieldDefinition : FieldDefinition}
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
            -> ∃ responseValue fieldErrors,
                Execution.executeField schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairSelectedPathProbeResolvers schema
                      leftInitialSelectionSet rightInitialSelectionSet
                      leftInitialSpine rightInitialSpine targetParent leftField
                      rightField leftArguments rightArguments leftRuntime
                      rightRuntime)
                    targetParent leftField rightField leftArguments
                    rightArguments)
                  variableValues (fuel + 1)
                  (projectionTargetResolverValue
                    (.object leftSourceRuntimeType
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
                = .ok ([(responseName, responseValue)], fieldErrors))
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ selectionSet
            -> ∃ responseValue fieldErrors,
                Execution.executeField schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairSelectedPathProbeResolvers schema
                      leftInitialSelectionSet rightInitialSelectionSet
                      leftInitialSpine rightInitialSpine targetParent leftField
                      rightField leftArguments rightArguments leftRuntime
                      rightRuntime)
                    targetParent leftField rightField leftArguments
                    rightArguments)
                  variableValues (fuel + 1)
                  (projectionTargetResolverValue
                    (.object rightSourceRuntimeType
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
                = .ok ([(responseName, responseValue)], fieldErrors))
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet leftInitialSpine rightInitialSpine
                  targetParent leftField rightField leftArguments rightArguments
                  leftRuntime rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) parentType
              (projectionTargetResolverValue
                (.object leftSourceRuntimeType
                  (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
                    leftCurrentSelectionSet leftSpine)))
              selectionSet).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet leftInitialSpine rightInitialSpine
                  targetParent leftField rightField leftArguments rightArguments
                  leftRuntime rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) parentType
              (projectionTargetResolverValue
                (.object rightSourceRuntimeType
                  (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                    rightCurrentSelectionSet rightSpine)))
              selectionSet).data := by
  intro hfree hnormal hobject hmem hlookup hfuel hleaf hleftFieldOk
    hrightFieldOk
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet
      (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
        rightInitialSelectionSet leftInitialSpine rightInitialSpine
        targetParent leftField rightField leftArguments rightArguments
        leftRuntime rightRuntime)
      targetParent leftField rightField leftArguments rightArguments
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
      .ok ([(responseName,
        leafProbeResponseValue fieldDefinition.outputType
          FieldPairProbeTag.left.scalar)], 0) := by
    dsimp [resolvers, leftSource]
    exact
      executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_leaf
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftCurrentSelectionSet leftInitialSpine
        rightInitialSpine leftSpine variableValues fuel targetParent
        leftField rightField parentType fieldName leftSourceRuntimeType
        responseName leftArguments rightArguments arguments leftRuntime
        rightRuntime FieldPairProbeTag.left childSelectionSet
        fieldDefinition hlookup hfuel hleaf
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
      .ok ([(responseName,
        leafProbeResponseValue fieldDefinition.outputType
          FieldPairProbeTag.right.scalar)], 0) := by
    dsimp [resolvers, rightSource]
    exact
      executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_leaf
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet rightCurrentSelectionSet leftInitialSpine
        rightInitialSpine rightSpine variableValues fuel targetParent
        leftField rightField parentType fieldName rightSourceRuntimeType
        responseName leftArguments rightArguments arguments leftRuntime
        rightRuntime FieldPairProbeTag.right childSelectionSet
        fieldDefinition hlookup hfuel hleaf
  exact
    SemanticSeparation.responseData_not_semanticEquivalent_of_field_value_diff_of_field_ok
      resolvers resolvers variableValues (fuel + 1) leftSource rightSource
      hobject hnormal hnormal hfree hfree hmem hmem hleftTarget
      hrightTarget
      (leafProbeResponseValue_not_semanticEquivalent_of_ne
        fieldDefinition.outputType (by simp [FieldPairProbeTag.scalar]))
      hleftFieldOk hrightFieldOk

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_child_field_of_field_ok
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine leftSpine rightSpine leftTail rightTail
      : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField parentType
      leftSourceRuntimeType rightSourceRuntimeType
      : Name)
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
      -> selectedObservableFieldSpineNext? fieldName arguments leftSpine
          = some (some runtimeType, leftTail)
      -> selectedObservableFieldSpineNext? fieldName arguments rightSpine
          = some (some runtimeType, rightTail)
      -> ((objectTypeNameBool schema fieldDefinition.outputType.namedType = true
            ∧ runtimeType = fieldDefinition.outputType.namedType)
          ∨ ((TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
                = true
              ∧ objectTypeNameBool schema fieldDefinition.outputType.namedType = false))
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType runtimeType
          = true
      -> leafProbeFuel fieldDefinition.outputType ≤ fuel
      -> Execution.executeSelectionSetAsResponse schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet leftInitialSpine rightInitialSpine
                targetParent leftField rightField leftArguments rightArguments
                leftRuntime rightRuntime)
              targetParent leftField rightField leftArguments rightArguments)
            variableValues
            (fuel - leafProbeFuel fieldDefinition.outputType)
            runtimeType
            (projectionTargetResolverValue
              (.object runtimeType
                (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
                  (fieldPairPathLocalNextSelectionSet schema parentType
                    runtimeType fieldName arguments leftCurrentSelectionSet)
                  leftTail)))
            childSelectionSet
          = ({
                data := Execution.ResponseValue.object leftChildFields,
                errors := leftChildErrors
              }
              : Execution.Response)
      -> Execution.executeSelectionSetAsResponse schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet leftInitialSpine rightInitialSpine
                targetParent leftField rightField leftArguments rightArguments
                leftRuntime rightRuntime)
              targetParent leftField rightField leftArguments rightArguments)
            variableValues
            (fuel - leafProbeFuel fieldDefinition.outputType)
            runtimeType
            (projectionTargetResolverValue
              (.object runtimeType
                (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                  (fieldPairPathLocalNextSelectionSet schema parentType
                    runtimeType fieldName arguments rightCurrentSelectionSet)
                  rightTail)))
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
                    (fieldPairSelectedPathProbeResolvers schema
                      leftInitialSelectionSet rightInitialSelectionSet
                      leftInitialSpine rightInitialSpine targetParent leftField
                      rightField leftArguments rightArguments leftRuntime
                      rightRuntime)
                    targetParent leftField rightField leftArguments
                    rightArguments)
                  variableValues (fuel + 1)
                  (projectionTargetResolverValue
                    (.object leftSourceRuntimeType
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
                = .ok ([(responseName, responseValue)], fieldErrors))
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ selectionSet
            -> ∃ responseValue fieldErrors,
                Execution.executeField schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairSelectedPathProbeResolvers schema
                      leftInitialSelectionSet rightInitialSelectionSet
                      leftInitialSpine rightInitialSpine targetParent leftField
                      rightField leftArguments rightArguments leftRuntime
                      rightRuntime)
                    targetParent leftField rightField leftArguments
                    rightArguments)
                  variableValues (fuel + 1)
                  (projectionTargetResolverValue
                    (.object rightSourceRuntimeType
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
                = .ok ([(responseName, responseValue)], fieldErrors))
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet leftInitialSpine rightInitialSpine
                  targetParent leftField rightField leftArguments rightArguments
                  leftRuntime rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) parentType
              (projectionTargetResolverValue
                (.object leftSourceRuntimeType
                  (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
                    leftCurrentSelectionSet leftSpine)))
              selectionSet).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet leftInitialSpine rightInitialSpine
                  targetParent leftField rightField leftArguments rightArguments
                  leftRuntime rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) parentType
              (projectionTargetResolverValue
                (.object rightSourceRuntimeType
                  (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                    rightCurrentSelectionSet rightSpine)))
              selectionSet).data := by
  intro hfree hnormal hobject hmem hlookup hleftSelected hrightSelected
    hruntime hinclude hfuel hleftChildResponse hrightChildResponse hchildNot
    hleftFieldOk hrightFieldOk
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet
      (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
        rightInitialSelectionSet leftInitialSpine rightInitialSpine
        targetParent leftField rightField leftArguments rightArguments
        leftRuntime rightRuntime)
      targetParent leftField rightField leftArguments rightArguments
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
      executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_objectProbe_response_of_fuel_ge
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftCurrentSelectionSet
        leftInitialSpine rightInitialSpine leftSpine leftTail
        variableValues fuel targetParent leftField rightField parentType
        fieldName leftSourceRuntimeType responseName leftArguments
        rightArguments arguments leftRuntime rightRuntime
        FieldPairProbeTag.left childSelectionSet fieldDefinition runtimeType
        hlookup hleftSelected hruntime hinclude hfuel]
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
      executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_objectProbe_response_of_fuel_ge
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet rightCurrentSelectionSet
        leftInitialSpine rightInitialSpine rightSpine rightTail
        variableValues fuel targetParent leftField rightField parentType
        fieldName rightSourceRuntimeType responseName leftArguments
        rightArguments arguments leftRuntime rightRuntime
        FieldPairProbeTag.right childSelectionSet fieldDefinition runtimeType
        hlookup hrightSelected hruntime hinclude hfuel]
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
    not_selectionSetsDataEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_root_responseName_value_diff_of_object_responses
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (parentFuel : Nat)
    (parentType responseName leftField rightField : Name)
    (leftArguments rightArguments : List Argument) (leftRuntime rightRuntime : Name)
    {left right : List Selection}
    {leftFields rightFields : List (Name × Execution.ResponseValue)}
    {leftErrors rightErrors : Nat} {leftValue rightValue : Execution.ResponseValue}
    : objectTypeNameBool schema parentType = true
      -> Execution.executeSelectionSetAsResponse schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairSelectedPathProbeResolvers schema
                leftInitialSelectionSet rightInitialSelectionSet
                leftInitialSpine rightInitialSpine parentType leftField
                rightField leftArguments rightArguments leftRuntime
                rightRuntime)
              parentType leftField rightField leftArguments rightArguments)
            variableValues (parentFuel + 1) parentType
            (projectionRootResolverValue
              (.object parentType FieldPairSelectedPathProbeRef.root))
            left
          = ({ data := Execution.ResponseValue.object leftFields, errors := leftErrors }
              : Execution.Response)
      -> Execution.executeSelectionSetAsResponse schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairSelectedPathProbeResolvers schema
                leftInitialSelectionSet rightInitialSelectionSet
                leftInitialSpine rightInitialSpine parentType leftField
                rightField leftArguments rightArguments leftRuntime
                rightRuntime)
              parentType leftField rightField leftArguments rightArguments)
            variableValues (parentFuel + 1) parentType
            (projectionRootResolverValue
              (.object parentType FieldPairSelectedPathProbeRef.root))
            right
          = ({ data := Execution.ResponseValue.object rightFields, errors := rightErrors }
              : Execution.Response)
      -> (leftFields.map Prod.fst).Nodup
      -> (rightFields.map Prod.fst).Nodup
      -> (responseName, leftValue) ∈ leftFields
      -> (responseName, rightValue) ∈ rightFields
      -> ¬ Execution.ResponseValue.semanticEquivalent leftValue rightValue
      -> ¬ selectionSetsDataEquivalent schema parentType left right := by
  intro hobject hleftResponse hrightResponse hleftNodup hrightNodup
    hleftMem hrightMem hvalue
  have hsource :
      ∃ runtimeType ref,
        projectionRootResolverValue
            (.object parentType FieldPairSelectedPathProbeRef.root)
          =
          Execution.ResolverValue.object runtimeType ref
          ∧ schema.typeIncludesObjectBool parentType runtimeType = true := by
    refine ⟨
      parentType,
      ProjectionResolverRef.root FieldPairSelectedPathProbeRef.root,
      ?_,
      typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject
    ⟩
    simp [projectionRootResolverValue, projectionResolverValue]
  exact
    SemanticSeparation.not_selectionSetsDataEquivalent_of_response_field_value_mismatch
      (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
        (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
          rightInitialSelectionSet leftInitialSpine rightInitialSpine
          parentType leftField rightField leftArguments rightArguments
          leftRuntime rightRuntime)
        parentType leftField rightField leftArguments rightArguments)
      variableValues (parentFuel + 1)
      (projectionRootResolverValue
        (.object parentType FieldPairSelectedPathProbeRef.root))
      hsource hleftResponse hrightResponse hleftNodup hrightNodup
      hleftMem hrightMem hvalue

theorem
    not_selectionSetsDataEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_root_arguments_child_response_diff_of_field_ok
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (parentFuel : Nat)
    (parentType responseName fieldName : Name)
    (leftArguments rightArguments : List Argument) (leftRuntime rightRuntime : Name)
    {left right : List Selection}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
    {leftChildFields rightChildFields : List (Name × Execution.ResponseValue)}
    {leftChildErrors rightChildErrors : Nat}
    : objectTypeNameBool schema parentType = true
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> Selection.field responseName fieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName fieldName rightArguments rightDirectives
            rightChildSelectionSet
          ∈ right
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType leftRuntime
          = true
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType rightRuntime
          = true
      -> leafProbeFuel fieldDefinition.outputType ≤ parentFuel
      -> ¬ Argument.argumentsEquivalent leftArguments rightArguments
      -> Execution.executeSelectionSetAsResponse schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet leftInitialSpine rightInitialSpine
                parentType fieldName fieldName leftArguments rightArguments
                leftRuntime rightRuntime)
              parentType fieldName fieldName leftArguments rightArguments)
            variableValues
            (parentFuel - leafProbeFuel fieldDefinition.outputType)
            leftRuntime
            (projectionTargetResolverValue
              (.object leftRuntime
                (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
                  leftInitialSelectionSet leftInitialSpine)))
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
                parentType fieldName fieldName leftArguments rightArguments
                leftRuntime rightRuntime)
              parentType fieldName fieldName leftArguments rightArguments)
            variableValues
            (parentFuel - leafProbeFuel fieldDefinition.outputType)
            rightRuntime
            (projectionTargetResolverValue
              (.object rightRuntime
                (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                  rightInitialSelectionSet rightInitialSpine)))
            rightChildSelectionSet
          = ({
                data := Execution.ResponseValue.object rightChildFields,
                errors := rightChildErrors
              }
              : Execution.Response)
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.ResponseValue.object leftChildFields)
            (Execution.ResponseValue.object rightChildFields)
      -> (∀ responseName siblingFieldName arguments directives childSelectionSet,
            Selection.field responseName siblingFieldName arguments directives
                childSelectionSet
              ∈ left
            -> ∃ responseValue fieldErrors,
                Execution.executeField schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairSelectedPathProbeResolvers schema
                      leftInitialSelectionSet rightInitialSelectionSet
                      leftInitialSpine rightInitialSpine parentType fieldName
                      fieldName leftArguments rightArguments leftRuntime
                      rightRuntime)
                    parentType fieldName fieldName leftArguments rightArguments)
                  variableValues (parentFuel + 1)
                  (projectionRootResolverValue
                    (.object parentType FieldPairSelectedPathProbeRef.root))
                  responseName
                  [{
                    parentType := parentType
                    responseName := responseName
                    fieldName := siblingFieldName
                    arguments := arguments
                    selectionSet := childSelectionSet
                  }]
                = .ok ([(responseName, responseValue)], fieldErrors))
      -> (∀ responseName siblingFieldName arguments directives childSelectionSet,
            Selection.field responseName siblingFieldName arguments directives
                childSelectionSet
              ∈ right
            -> ∃ responseValue fieldErrors,
                Execution.executeField schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairSelectedPathProbeResolvers schema
                      leftInitialSelectionSet rightInitialSelectionSet
                      leftInitialSpine rightInitialSpine parentType fieldName
                      fieldName leftArguments rightArguments leftRuntime
                      rightRuntime)
                    parentType fieldName fieldName leftArguments rightArguments)
                  variableValues (parentFuel + 1)
                  (projectionRootResolverValue
                    (.object parentType FieldPairSelectedPathProbeRef.root))
                  responseName
                  [{
                    parentType := parentType
                    responseName := responseName
                    fieldName := siblingFieldName
                    arguments := arguments
                    selectionSet := childSelectionSet
                  }]
                = .ok ([(responseName, responseValue)], fieldErrors))
      -> ¬ selectionSetsDataEquivalent schema parentType left right := by
  intro hobject hleftNormal hrightNormal hleftFree hrightFree hleftMem
    hrightMem hlookup hleftInclude hrightInclude hfuel hargumentsDiff
    hleftChildResponse hrightChildResponse hchildNot hleftFieldOk
    hrightFieldOk
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet
      (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
        rightInitialSelectionSet leftInitialSpine rightInitialSpine
        parentType fieldName fieldName leftArguments rightArguments
        leftRuntime rightRuntime)
      parentType fieldName fieldName leftArguments rightArguments
  let source :=
    projectionRootResolverValue
      (.object parentType FieldPairSelectedPathProbeRef.root)
  rcases
      wrapTypeRefSelectionSetResult_ok_nonNull_of_object_response
        fieldDefinition.outputType leftChildFields leftChildErrors with
    ⟨leftValue, leftFieldErrors, hleftWrapped, _hleftNonNull⟩
  rcases
      wrapTypeRefSelectionSetResult_ok_nonNull_of_object_response
        fieldDefinition.outputType rightChildFields rightChildErrors with
    ⟨rightValue, rightFieldErrors, hrightWrapped, _hrightNonNull⟩
  have hleftTarget :
      Execution.executeField schema resolvers variableValues (parentFuel + 1)
        source responseName
        [{
          parentType := parentType
          responseName := responseName
          fieldName := fieldName
          arguments := leftArguments
          selectionSet := leftChildSelectionSet
        }]
      =
      .ok ([(responseName, leftValue)], leftFieldErrors) := by
    dsimp [resolvers, source]
    have hleftChildRaw :
        Execution.selectionSetResultToResponse
          (Execution.executeCollectedFields schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairSelectedPathProbeResolvers schema
                leftInitialSelectionSet rightInitialSelectionSet
                leftInitialSpine rightInitialSpine parentType fieldName
                fieldName leftArguments rightArguments leftRuntime
                rightRuntime)
              parentType fieldName fieldName leftArguments rightArguments)
            variableValues
            (parentFuel - leafProbeFuel fieldDefinition.outputType)
            (projectionTargetResolverValue
              (.object leftRuntime
                (FieldPairSelectedPathProbeRef.target
                  FieldPairProbeTag.left leftInitialSelectionSet
                  leftInitialSpine)))
            (Execution.collectFields schema variableValues leftRuntime
              (projectionTargetResolverValue
                (.object leftRuntime
                  (FieldPairSelectedPathProbeRef.target
                    FieldPairProbeTag.left leftInitialSelectionSet
                    leftInitialSpine)))
              leftChildSelectionSet))
        =
        ({ data := Execution.ResponseValue.object leftChildFields,
           errors := leftChildErrors } : Execution.Response) := by
      simpa [Execution.executeSelectionSetAsResponse, Execution.executeSelectionSet,
        Execution.executeRootSelectionSet] using hleftChildResponse
    have hfield :=
      executeField_fieldPairOrDeepSuccess_selectedPathProbe_left_root_response
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftInitialSpine rightInitialSpine
        variableValues
        (parentFuel - leafProbeFuel fieldDefinition.outputType)
        parentType fieldName fieldName responseName leftArguments
        rightArguments leftArguments leftRuntime rightRuntime
        leftChildSelectionSet fieldDefinition
        (argumentsEquivalent_refl_forSyntaxDiff leftArguments)
        hlookup hleftInclude
    have hfuelEq :
        parentFuel - leafProbeFuel fieldDefinition.outputType
            + leafProbeFuel fieldDefinition.outputType + 1
          =
        parentFuel + 1 := by
      omega
    simpa [hleftChildRaw, hleftWrapped, Execution.singleFieldResult,
      hfuelEq] using hfield
  have hrightTarget :
      Execution.executeField schema resolvers variableValues (parentFuel + 1)
        source responseName
        [{
          parentType := parentType
          responseName := responseName
          fieldName := fieldName
          arguments := rightArguments
          selectionSet := rightChildSelectionSet
        }]
      =
      .ok ([(responseName, rightValue)], rightFieldErrors) := by
    dsimp [resolvers, source]
    have hrightChildRaw :
        Execution.selectionSetResultToResponse
          (Execution.executeCollectedFields schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairSelectedPathProbeResolvers schema
                leftInitialSelectionSet rightInitialSelectionSet
                leftInitialSpine rightInitialSpine parentType fieldName
                fieldName leftArguments rightArguments leftRuntime
                rightRuntime)
              parentType fieldName fieldName leftArguments rightArguments)
            variableValues
            (parentFuel - leafProbeFuel fieldDefinition.outputType)
            (projectionTargetResolverValue
              (.object rightRuntime
                (FieldPairSelectedPathProbeRef.target
                  FieldPairProbeTag.right rightInitialSelectionSet
                  rightInitialSpine)))
            (Execution.collectFields schema variableValues rightRuntime
              (projectionTargetResolverValue
                (.object rightRuntime
                  (FieldPairSelectedPathProbeRef.target
                    FieldPairProbeTag.right rightInitialSelectionSet
                    rightInitialSpine)))
              rightChildSelectionSet))
        =
        ({ data := Execution.ResponseValue.object rightChildFields,
           errors := rightChildErrors } : Execution.Response) := by
      simpa [Execution.executeSelectionSetAsResponse, Execution.executeSelectionSet,
        Execution.executeRootSelectionSet] using hrightChildResponse
    have hnotLeft :
        ¬ fieldProbeTarget parentType fieldName leftArguments parentType
          fieldName rightArguments :=
      not_fieldProbeTarget_of_arguments_not_equivalent hargumentsDiff
        (argumentsEquivalent_refl_forSyntaxDiff rightArguments)
    have hfield :=
      executeField_fieldPairOrDeepSuccess_selectedPathProbe_right_root_response_of_not_left
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftInitialSpine rightInitialSpine
        variableValues
        (parentFuel - leafProbeFuel fieldDefinition.outputType)
        parentType fieldName fieldName responseName leftArguments
        rightArguments rightArguments leftRuntime rightRuntime
        rightChildSelectionSet fieldDefinition hnotLeft
        (argumentsEquivalent_refl_forSyntaxDiff rightArguments)
        hlookup hrightInclude
    have hfuelEq :
        parentFuel - leafProbeFuel fieldDefinition.outputType
            + leafProbeFuel fieldDefinition.outputType + 1
          =
        parentFuel + 1 := by
      omega
    simpa [hrightChildRaw, hrightWrapped, Execution.singleFieldResult,
      hfuelEq] using hfield
  have hvalueNot :
      ¬ Execution.ResponseValue.semanticEquivalent leftValue rightValue := by
    intro hvalue
    let leftChildResponse : Execution.Response :=
      { data := Execution.ResponseValue.object leftChildFields,
        errors := leftChildErrors }
    let rightChildResponse : Execution.Response :=
      { data := Execution.ResponseValue.object rightChildFields,
        errors := rightChildErrors }
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
  rcases
      ExecutionSuccess.executeSelectionSetAsResponse_object_field_mem_of_field_ok
        schema resolvers variableValues (parentFuel + 1) parentType
        source left responseName fieldName leftArguments leftDirectives
        leftChildSelectionSet leftValue leftFieldErrors hleftFree
        hleftNormal hobject hleftMem hleftTarget hleftFieldOk with
    ⟨leftFields, leftErrors, hleftResponse, hleftValueMem⟩
  rcases
      ExecutionSuccess.executeSelectionSetAsResponse_object_field_mem_of_field_ok
        schema resolvers variableValues (parentFuel + 1) parentType
        source right responseName fieldName rightArguments rightDirectives
        rightChildSelectionSet rightValue rightFieldErrors hrightFree
        hrightNormal hobject hrightMem hrightTarget hrightFieldOk with
    ⟨rightFields, rightErrors, hrightResponse, hrightValueMem⟩
  have hleftKeys :=
    ExecutionResponseKeys.executeSelectionSetAsResponse_object_keys_eq_collectFields
      schema resolvers variableValues (parentFuel + 1) parentType source
      left hleftResponse
  have hrightKeys :=
    ExecutionResponseKeys.executeSelectionSetAsResponse_object_keys_eq_collectFields
      schema resolvers variableValues (parentFuel + 1) parentType source
      right hrightResponse
  have hleftNodup : (leftFields.map Prod.fst).Nodup := by
    rw [hleftKeys]
    exact ExecutionKeys.collectFields_normal_object_keys_nodup schema
      variableValues parentType source left hleftFree hleftNormal hobject
  have hrightNodup : (rightFields.map Prod.fst).Nodup := by
    rw [hrightKeys]
    exact ExecutionKeys.collectFields_normal_object_keys_nodup schema
      variableValues parentType source right hrightFree hrightNormal hobject
  exact
    not_selectionSetsDataEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_root_responseName_value_diff_of_object_responses
      schema rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftInitialSpine rightInitialSpine variableValues parentFuel
      parentType responseName fieldName fieldName leftArguments
      rightArguments leftRuntime rightRuntime hobject
      (by simpa [resolvers, source] using hleftResponse)
      (by simpa [resolvers, source] using hrightResponse)
      hleftNodup hrightNodup hleftValueMem hrightValueMem hvalueNot

theorem
    not_selectionSetsDataEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_root_fieldName_child_response_diff_of_field_ok
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (parentFuel : Nat)
    (parentType responseName leftFieldName rightFieldName : Name)
    (leftArguments rightArguments : List Argument) (leftRuntime rightRuntime : Name)
    {left right : List Selection}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {leftFieldDefinition rightFieldDefinition : FieldDefinition}
    {leftChildFields rightChildFields : List (Name × Execution.ResponseValue)}
    {leftChildErrors rightChildErrors : Nat}
    : objectTypeNameBool schema parentType = true
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> Selection.field responseName leftFieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName rightFieldName rightArguments
            rightDirectives rightChildSelectionSet
          ∈ right
      -> schema.lookupField parentType leftFieldName = some leftFieldDefinition
      -> schema.lookupField parentType rightFieldName = some rightFieldDefinition
      -> schema.typeIncludesObjectBool leftFieldDefinition.outputType.namedType
            leftRuntime
          = true
      -> schema.typeIncludesObjectBool rightFieldDefinition.outputType.namedType
            rightRuntime
          = true
      -> leafProbeFuel leftFieldDefinition.outputType ≤ parentFuel
      -> leafProbeFuel rightFieldDefinition.outputType ≤ parentFuel
      -> leftFieldName ≠ rightFieldName
      -> Execution.executeSelectionSetAsResponse schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet leftInitialSpine rightInitialSpine
                parentType leftFieldName rightFieldName leftArguments
                rightArguments leftRuntime rightRuntime)
              parentType leftFieldName rightFieldName leftArguments
              rightArguments)
            variableValues
            (parentFuel - leafProbeFuel leftFieldDefinition.outputType)
            leftRuntime
            (projectionTargetResolverValue
              (.object leftRuntime
                (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
                  leftInitialSelectionSet leftInitialSpine)))
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
                parentType leftFieldName rightFieldName leftArguments
                rightArguments leftRuntime rightRuntime)
              parentType leftFieldName rightFieldName leftArguments
              rightArguments)
            variableValues
            (parentFuel - leafProbeFuel rightFieldDefinition.outputType)
            rightRuntime
            (projectionTargetResolverValue
              (.object rightRuntime
                (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                  rightInitialSelectionSet rightInitialSpine)))
            rightChildSelectionSet
          = ({
                data := Execution.ResponseValue.object rightChildFields,
                errors := rightChildErrors
              }
              : Execution.Response)
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.ResponseValue.object leftChildFields)
            (Execution.ResponseValue.object rightChildFields)
      -> (∀ responseName siblingFieldName arguments directives childSelectionSet,
            Selection.field responseName siblingFieldName arguments directives
                childSelectionSet
              ∈ left
            -> ∃ responseValue fieldErrors,
                Execution.executeField schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairSelectedPathProbeResolvers schema
                      leftInitialSelectionSet rightInitialSelectionSet
                      leftInitialSpine rightInitialSpine parentType leftFieldName
                      rightFieldName leftArguments rightArguments leftRuntime
                      rightRuntime)
                    parentType leftFieldName rightFieldName leftArguments
                    rightArguments)
                  variableValues (parentFuel + 1)
                  (projectionRootResolverValue
                    (.object parentType FieldPairSelectedPathProbeRef.root))
                  responseName
                  [{
                    parentType := parentType
                    responseName := responseName
                    fieldName := siblingFieldName
                    arguments := arguments
                    selectionSet := childSelectionSet
                  }]
                = .ok ([(responseName, responseValue)], fieldErrors))
      -> (∀ responseName siblingFieldName arguments directives childSelectionSet,
            Selection.field responseName siblingFieldName arguments directives
                childSelectionSet
              ∈ right
            -> ∃ responseValue fieldErrors,
                Execution.executeField schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairSelectedPathProbeResolvers schema
                      leftInitialSelectionSet rightInitialSelectionSet
                      leftInitialSpine rightInitialSpine parentType leftFieldName
                      rightFieldName leftArguments rightArguments leftRuntime
                      rightRuntime)
                    parentType leftFieldName rightFieldName leftArguments
                    rightArguments)
                  variableValues (parentFuel + 1)
                  (projectionRootResolverValue
                    (.object parentType FieldPairSelectedPathProbeRef.root))
                  responseName
                  [{
                    parentType := parentType
                    responseName := responseName
                    fieldName := siblingFieldName
                    arguments := arguments
                    selectionSet := childSelectionSet
                  }]
                = .ok ([(responseName, responseValue)], fieldErrors))
      -> ¬ selectionSetsDataEquivalent schema parentType left right := by
  intro hobject hleftNormal hrightNormal hleftFree hrightFree hleftMem
    hrightMem hleftLookup hrightLookup hleftInclude hrightInclude
    hleftFuel hrightFuel hfieldDiff hleftChildResponse
    hrightChildResponse hchildNot hleftFieldOk hrightFieldOk
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet
      (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
        rightInitialSelectionSet leftInitialSpine rightInitialSpine
        parentType leftFieldName rightFieldName leftArguments rightArguments
        leftRuntime rightRuntime)
      parentType leftFieldName rightFieldName leftArguments rightArguments
  let source :=
    projectionRootResolverValue
      (.object parentType FieldPairSelectedPathProbeRef.root)
  rcases
      wrapTypeRefSelectionSetResult_ok_nonNull_of_object_response
        leftFieldDefinition.outputType leftChildFields leftChildErrors with
    ⟨leftValue, leftFieldErrors, hleftWrapped, _hleftNonNull⟩
  rcases
      wrapTypeRefSelectionSetResult_ok_nonNull_of_object_response
        rightFieldDefinition.outputType rightChildFields rightChildErrors with
    ⟨rightValue, rightFieldErrors, hrightWrapped, _hrightNonNull⟩
  have hleftTarget :
      Execution.executeField schema resolvers variableValues
        (parentFuel + 1) source responseName
        [{
          parentType := parentType
          responseName := responseName
          fieldName := leftFieldName
          arguments := leftArguments
          selectionSet := leftChildSelectionSet
        }]
      =
      .ok ([(responseName, leftValue)], leftFieldErrors) := by
    dsimp [resolvers, source]
    have hleftChildRaw :
        Execution.selectionSetResultToResponse
          (Execution.executeCollectedFields schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairSelectedPathProbeResolvers schema
                leftInitialSelectionSet rightInitialSelectionSet
                leftInitialSpine rightInitialSpine parentType leftFieldName
                rightFieldName leftArguments rightArguments leftRuntime
                rightRuntime)
              parentType leftFieldName rightFieldName leftArguments
              rightArguments)
            variableValues
            (parentFuel - leafProbeFuel leftFieldDefinition.outputType)
            (projectionTargetResolverValue
              (.object leftRuntime
                (FieldPairSelectedPathProbeRef.target
                  FieldPairProbeTag.left leftInitialSelectionSet
                  leftInitialSpine)))
            (Execution.collectFields schema variableValues leftRuntime
              (projectionTargetResolverValue
                (.object leftRuntime
                  (FieldPairSelectedPathProbeRef.target
                    FieldPairProbeTag.left leftInitialSelectionSet
                    leftInitialSpine)))
              leftChildSelectionSet))
        =
        ({ data := Execution.ResponseValue.object leftChildFields,
           errors := leftChildErrors } : Execution.Response) := by
      simpa [Execution.executeSelectionSetAsResponse, Execution.executeSelectionSet,
        Execution.executeRootSelectionSet] using hleftChildResponse
    have hfield :=
      executeField_fieldPairOrDeepSuccess_selectedPathProbe_left_root_response
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftInitialSpine rightInitialSpine
        variableValues
        (parentFuel - leafProbeFuel leftFieldDefinition.outputType)
        parentType leftFieldName rightFieldName responseName leftArguments
        rightArguments leftArguments leftRuntime rightRuntime
        leftChildSelectionSet leftFieldDefinition
        (argumentsEquivalent_refl_forSyntaxDiff leftArguments)
        hleftLookup hleftInclude
    have hfuelEq :
        parentFuel - leafProbeFuel leftFieldDefinition.outputType
            + leafProbeFuel leftFieldDefinition.outputType + 1
          =
        parentFuel + 1 := by
      omega
    simpa [hleftChildRaw, hleftWrapped, Execution.singleFieldResult,
      hfuelEq] using hfield
  have hrightTarget :
      Execution.executeField schema resolvers variableValues
        (parentFuel + 1) source responseName
        [{
          parentType := parentType
          responseName := responseName
          fieldName := rightFieldName
          arguments := rightArguments
          selectionSet := rightChildSelectionSet
        }]
      =
      .ok ([(responseName, rightValue)], rightFieldErrors) := by
    dsimp [resolvers, source]
    have hrightChildRaw :
        Execution.selectionSetResultToResponse
          (Execution.executeCollectedFields schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairSelectedPathProbeResolvers schema
                leftInitialSelectionSet rightInitialSelectionSet
                leftInitialSpine rightInitialSpine parentType leftFieldName
                rightFieldName leftArguments rightArguments leftRuntime
                rightRuntime)
              parentType leftFieldName rightFieldName leftArguments
              rightArguments)
            variableValues
            (parentFuel - leafProbeFuel rightFieldDefinition.outputType)
            (projectionTargetResolverValue
              (.object rightRuntime
                (FieldPairSelectedPathProbeRef.target
                  FieldPairProbeTag.right rightInitialSelectionSet
                  rightInitialSpine)))
            (Execution.collectFields schema variableValues rightRuntime
              (projectionTargetResolverValue
                (.object rightRuntime
                  (FieldPairSelectedPathProbeRef.target
                    FieldPairProbeTag.right rightInitialSelectionSet
                    rightInitialSpine)))
              rightChildSelectionSet))
        =
        ({ data := Execution.ResponseValue.object rightChildFields,
           errors := rightChildErrors } : Execution.Response) := by
      simpa [Execution.executeSelectionSetAsResponse, Execution.executeSelectionSet,
        Execution.executeRootSelectionSet] using hrightChildResponse
    have hnotLeft :
        ¬ fieldProbeTarget parentType leftFieldName leftArguments parentType
          rightFieldName rightArguments :=
      not_fieldProbeTarget_of_fieldName_ne hfieldDiff
    have hfield :=
      executeField_fieldPairOrDeepSuccess_selectedPathProbe_right_root_response_of_not_left
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftInitialSpine rightInitialSpine
        variableValues
        (parentFuel - leafProbeFuel rightFieldDefinition.outputType)
        parentType leftFieldName rightFieldName responseName leftArguments
        rightArguments rightArguments leftRuntime rightRuntime
        rightChildSelectionSet rightFieldDefinition hnotLeft
        (argumentsEquivalent_refl_forSyntaxDiff rightArguments)
        hrightLookup hrightInclude
    have hfuelEq :
        parentFuel - leafProbeFuel rightFieldDefinition.outputType
            + leafProbeFuel rightFieldDefinition.outputType + 1
          =
        parentFuel + 1 := by
      omega
    simpa [hrightChildRaw, hrightWrapped, Execution.singleFieldResult,
      hfuelEq] using hfield
  have hvalueNot :
      ¬ Execution.ResponseValue.semanticEquivalent leftValue rightValue :=
    wrapped_object_values_not_semanticEquivalent_of_child
      leftFieldDefinition.outputType rightFieldDefinition.outputType
      hleftWrapped hrightWrapped hchildNot
  rcases
      ExecutionSuccess.executeSelectionSetAsResponse_object_field_mem_of_field_ok
        schema resolvers variableValues (parentFuel + 1) parentType
        source left responseName leftFieldName leftArguments
        leftDirectives leftChildSelectionSet leftValue leftFieldErrors
        hleftFree hleftNormal hobject hleftMem hleftTarget
        hleftFieldOk with
    ⟨leftFields, leftErrors, hleftResponse, hleftValueMem⟩
  rcases
      ExecutionSuccess.executeSelectionSetAsResponse_object_field_mem_of_field_ok
        schema resolvers variableValues (parentFuel + 1) parentType
        source right responseName rightFieldName rightArguments
        rightDirectives rightChildSelectionSet rightValue rightFieldErrors
        hrightFree hrightNormal hobject hrightMem hrightTarget
        hrightFieldOk with
    ⟨rightFields, rightErrors, hrightResponse, hrightValueMem⟩
  have hleftKeys :=
    ExecutionResponseKeys.executeSelectionSetAsResponse_object_keys_eq_collectFields
      schema resolvers variableValues (parentFuel + 1) parentType source
      left hleftResponse
  have hrightKeys :=
    ExecutionResponseKeys.executeSelectionSetAsResponse_object_keys_eq_collectFields
      schema resolvers variableValues (parentFuel + 1) parentType source
      right hrightResponse
  have hleftNodup : (leftFields.map Prod.fst).Nodup := by
    rw [hleftKeys]
    exact ExecutionKeys.collectFields_normal_object_keys_nodup schema
      variableValues parentType source left hleftFree hleftNormal hobject
  have hrightNodup : (rightFields.map Prod.fst).Nodup := by
    rw [hrightKeys]
    exact ExecutionKeys.collectFields_normal_object_keys_nodup schema
      variableValues parentType source right hrightFree hrightNormal hobject
  exact
    not_selectionSetsDataEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_root_responseName_value_diff_of_object_responses
      schema rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftInitialSpine rightInitialSpine variableValues parentFuel
      parentType responseName leftFieldName rightFieldName leftArguments
      rightArguments leftRuntime rightRuntime hobject
      (by simpa [resolvers, source] using hleftResponse)
      (by simpa [resolvers, source] using hrightResponse)
      hleftNodup hrightNodup hleftValueMem hrightValueMem hvalueNot

theorem
    not_selectionSetsDataEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_root_arguments_child_response_diff_of_field_cases
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (parentFuel : Nat)
    (parentType responseName fieldName : Name)
    (leftArguments rightArguments : List Argument) (leftRuntime rightRuntime : Name)
    {left right : List Selection}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
    {leftChildFields rightChildFields : List (Name × Execution.ResponseValue)}
    {leftChildErrors rightChildErrors : Nat}
    : objectTypeNameBool schema parentType = true
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> Selection.field responseName fieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName fieldName rightArguments rightDirectives
            rightChildSelectionSet
          ∈ right
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType leftRuntime
          = true
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType rightRuntime
          = true
      -> leafProbeFuel fieldDefinition.outputType ≤ parentFuel
      -> ¬ Argument.argumentsEquivalent leftArguments rightArguments
      -> Execution.executeSelectionSetAsResponse schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet leftInitialSpine rightInitialSpine
                parentType fieldName fieldName leftArguments rightArguments
                leftRuntime rightRuntime)
              parentType fieldName fieldName leftArguments rightArguments)
            variableValues
            (parentFuel - leafProbeFuel fieldDefinition.outputType)
            leftRuntime
            (projectionTargetResolverValue
              (.object leftRuntime
                (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
                  leftInitialSelectionSet leftInitialSpine)))
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
                parentType fieldName fieldName leftArguments rightArguments
                leftRuntime rightRuntime)
              parentType fieldName fieldName leftArguments rightArguments)
            variableValues
            (parentFuel - leafProbeFuel fieldDefinition.outputType)
            rightRuntime
            (projectionTargetResolverValue
              (.object rightRuntime
                (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                  rightInitialSelectionSet rightInitialSpine)))
            rightChildSelectionSet
          = ({
                data := Execution.ResponseValue.object rightChildFields,
                errors := rightChildErrors
              }
              : Execution.Response)
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.ResponseValue.object leftChildFields)
            (Execution.ResponseValue.object rightChildFields)
      -> (∀ responseName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ left
            -> Argument.argumentsEquivalent arguments leftArguments
            -> ∃ childFields childErrors,
                Execution.executeSelectionSetAsResponse schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairSelectedPathProbeResolvers schema
                      leftInitialSelectionSet rightInitialSelectionSet
                      leftInitialSpine rightInitialSpine parentType fieldName
                      fieldName leftArguments rightArguments leftRuntime
                      rightRuntime)
                    parentType fieldName fieldName leftArguments rightArguments)
                  variableValues
                  (parentFuel - leafProbeFuel fieldDefinition.outputType)
                  leftRuntime
                  (projectionTargetResolverValue
                    (.object leftRuntime
                      (FieldPairSelectedPathProbeRef.target
                        FieldPairProbeTag.left leftInitialSelectionSet
                        leftInitialSpine)))
                  childSelectionSet
                = ({
                      data := Execution.ResponseValue.object childFields,
                      errors := childErrors
                    }
                    : Execution.Response))
      -> (∀ responseName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ left
            -> Argument.argumentsEquivalent arguments rightArguments
            -> ∃ childFields childErrors,
                Execution.executeSelectionSetAsResponse schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairSelectedPathProbeResolvers schema
                      leftInitialSelectionSet rightInitialSelectionSet
                      leftInitialSpine rightInitialSpine parentType fieldName
                      fieldName leftArguments rightArguments leftRuntime
                      rightRuntime)
                    parentType fieldName fieldName leftArguments rightArguments)
                  variableValues
                  (parentFuel - leafProbeFuel fieldDefinition.outputType)
                  rightRuntime
                  (projectionTargetResolverValue
                    (.object rightRuntime
                      (FieldPairSelectedPathProbeRef.target
                        FieldPairProbeTag.right rightInitialSelectionSet
                        rightInitialSpine)))
                  childSelectionSet
                = ({
                      data := Execution.ResponseValue.object childFields,
                      errors := childErrors
                    }
                    : Execution.Response))
      -> (∀ responseName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ right
            -> Argument.argumentsEquivalent arguments leftArguments
            -> ∃ childFields childErrors,
                Execution.executeSelectionSetAsResponse schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairSelectedPathProbeResolvers schema
                      leftInitialSelectionSet rightInitialSelectionSet
                      leftInitialSpine rightInitialSpine parentType fieldName
                      fieldName leftArguments rightArguments leftRuntime
                      rightRuntime)
                    parentType fieldName fieldName leftArguments rightArguments)
                  variableValues
                  (parentFuel - leafProbeFuel fieldDefinition.outputType)
                  leftRuntime
                  (projectionTargetResolverValue
                    (.object leftRuntime
                      (FieldPairSelectedPathProbeRef.target
                        FieldPairProbeTag.left leftInitialSelectionSet
                        leftInitialSpine)))
                  childSelectionSet
                = ({
                      data := Execution.ResponseValue.object childFields,
                      errors := childErrors
                    }
                    : Execution.Response))
      -> (∀ responseName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ right
            -> Argument.argumentsEquivalent arguments rightArguments
            -> ∃ childFields childErrors,
                Execution.executeSelectionSetAsResponse schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairSelectedPathProbeResolvers schema
                      leftInitialSelectionSet rightInitialSelectionSet
                      leftInitialSpine rightInitialSpine parentType fieldName
                      fieldName leftArguments rightArguments leftRuntime
                      rightRuntime)
                    parentType fieldName fieldName leftArguments rightArguments)
                  variableValues
                  (parentFuel - leafProbeFuel fieldDefinition.outputType)
                  rightRuntime
                  (projectionTargetResolverValue
                    (.object rightRuntime
                      (FieldPairSelectedPathProbeRef.target
                        FieldPairProbeTag.right rightInitialSelectionSet
                        rightInitialSpine)))
                  childSelectionSet
                = ({
                      data := Execution.ResponseValue.object childFields,
                      errors := childErrors
                    }
                    : Execution.Response))
      -> (∀ responseName siblingFieldName arguments directives childSelectionSet,
            Selection.field responseName siblingFieldName arguments directives
                childSelectionSet
              ∈ left
            -> ∃ responseValue fieldErrors,
                Execution.executeField schema
                  (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet
                    (ProjectionResolverRef.filler
                      : ProjectionResolverRef FieldPairSelectedPathProbeRef))
                  variableValues (parentFuel + 1)
                  (projectionRootResolverValue
                    (.object parentType FieldPairSelectedPathProbeRef.root))
                  responseName
                  [{
                    parentType := parentType,
                    responseName := responseName,
                    fieldName := siblingFieldName,
                    arguments := arguments,
                    selectionSet := childSelectionSet
                  }]
                = .ok ([(responseName, responseValue)], fieldErrors))
      -> (∀ responseName siblingFieldName arguments directives childSelectionSet,
            Selection.field responseName siblingFieldName arguments directives
                childSelectionSet
              ∈ right
            -> ∃ responseValue fieldErrors,
                Execution.executeField schema
                  (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet
                    (ProjectionResolverRef.filler
                      : ProjectionResolverRef FieldPairSelectedPathProbeRef))
                  variableValues (parentFuel + 1)
                  (projectionRootResolverValue
                    (.object parentType FieldPairSelectedPathProbeRef.root))
                  responseName
                  [{
                    parentType := parentType,
                    responseName := responseName,
                    fieldName := siblingFieldName,
                    arguments := arguments,
                    selectionSet := childSelectionSet
                  }]
                = .ok ([(responseName, responseValue)], fieldErrors))
      -> ¬ selectionSetsDataEquivalent schema parentType left right := by
  intro hobject hleftNormal hrightNormal hleftFree hrightFree hleftMem
    hrightMem hlookup hleftInclude hrightInclude hfuel hargumentsDiff
    hleftChildResponse hrightChildResponse hchildNot hleftLeftTarget
    hleftRightTarget hrightLeftTarget hrightRightTarget hleftDeep
    hrightDeep
  have hleftOther :
      ∀ responseName siblingFieldName arguments directives childSelectionSet,
        Selection.field responseName siblingFieldName arguments directives
            childSelectionSet ∈ left ->
        ¬ fieldPairProjectionTarget parentType fieldName fieldName
            leftArguments rightArguments parentType siblingFieldName
            arguments ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSelectedPathProbeResolvers schema
                  leftInitialSelectionSet rightInitialSelectionSet
                  leftInitialSpine rightInitialSpine parentType fieldName
                  fieldName leftArguments rightArguments leftRuntime
                  rightRuntime)
                parentType fieldName fieldName leftArguments rightArguments)
              variableValues (parentFuel + 1)
              (projectionRootResolverValue
                (.object parentType FieldPairSelectedPathProbeRef.root))
              responseName
              [{
                parentType := parentType,
                responseName := responseName,
                fieldName := siblingFieldName,
                arguments := arguments,
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(responseName, responseValue)], fieldErrors) :=
    selectionSetOtherFieldsExecuteOk_fieldPairOrDeepSuccess_selectedPathProbe_of_deepSuccessWithRef_ok
      schema rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftInitialSpine rightInitialSpine variableValues (parentFuel + 1)
      parentType fieldName fieldName leftArguments rightArguments
      leftRuntime rightRuntime left hleftDeep
  have hrightOther :
      ∀ responseName siblingFieldName arguments directives childSelectionSet,
        Selection.field responseName siblingFieldName arguments directives
            childSelectionSet ∈ right ->
        ¬ fieldPairProjectionTarget parentType fieldName fieldName
            leftArguments rightArguments parentType siblingFieldName
            arguments ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSelectedPathProbeResolvers schema
                  leftInitialSelectionSet rightInitialSelectionSet
                  leftInitialSpine rightInitialSpine parentType fieldName
                  fieldName leftArguments rightArguments leftRuntime
                  rightRuntime)
                parentType fieldName fieldName leftArguments rightArguments)
              variableValues (parentFuel + 1)
              (projectionRootResolverValue
                (.object parentType FieldPairSelectedPathProbeRef.root))
              responseName
              [{
                parentType := parentType,
                responseName := responseName,
                fieldName := siblingFieldName,
                arguments := arguments,
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(responseName, responseValue)], fieldErrors) :=
    selectionSetOtherFieldsExecuteOk_fieldPairOrDeepSuccess_selectedPathProbe_of_deepSuccessWithRef_ok
      schema rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftInitialSpine rightInitialSpine variableValues (parentFuel + 1)
      parentType fieldName fieldName leftArguments rightArguments
      leftRuntime rightRuntime right hrightDeep
  have hleftFieldOk :
      ∀ responseName siblingFieldName arguments directives childSelectionSet,
        Selection.field responseName siblingFieldName arguments directives
            childSelectionSet ∈ left ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSelectedPathProbeResolvers schema
                  leftInitialSelectionSet rightInitialSelectionSet
                  leftInitialSpine rightInitialSpine parentType fieldName
                  fieldName leftArguments rightArguments leftRuntime
                  rightRuntime)
                parentType fieldName fieldName leftArguments rightArguments)
              variableValues (parentFuel + 1)
              (projectionRootResolverValue
                (.object parentType FieldPairSelectedPathProbeRef.root))
              responseName
              [{
                parentType := parentType,
                responseName := responseName,
                fieldName := siblingFieldName,
                arguments := arguments,
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(responseName, responseValue)], fieldErrors) :=
    selectionSetFieldsExecuteOk_fieldPairOrDeepSuccess_selectedPathProbe_of_field_cases
      schema rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftInitialSpine rightInitialSpine variableValues parentFuel
      parentType fieldName fieldName leftArguments rightArguments
      leftRuntime rightRuntime fieldDefinition fieldDefinition left hlookup
      hlookup hleftInclude hrightInclude hfuel hfuel hleftLeftTarget
      hleftRightTarget hleftOther
  have hrightFieldOk :
      ∀ responseName siblingFieldName arguments directives childSelectionSet,
        Selection.field responseName siblingFieldName arguments directives
            childSelectionSet ∈ right ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSelectedPathProbeResolvers schema
                  leftInitialSelectionSet rightInitialSelectionSet
                  leftInitialSpine rightInitialSpine parentType fieldName
                  fieldName leftArguments rightArguments leftRuntime
                  rightRuntime)
                parentType fieldName fieldName leftArguments rightArguments)
              variableValues (parentFuel + 1)
              (projectionRootResolverValue
                (.object parentType FieldPairSelectedPathProbeRef.root))
              responseName
              [{
                parentType := parentType,
                responseName := responseName,
                fieldName := siblingFieldName,
                arguments := arguments,
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(responseName, responseValue)], fieldErrors) :=
    selectionSetFieldsExecuteOk_fieldPairOrDeepSuccess_selectedPathProbe_of_field_cases
      schema rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftInitialSpine rightInitialSpine variableValues parentFuel
      parentType fieldName fieldName leftArguments rightArguments
      leftRuntime rightRuntime fieldDefinition fieldDefinition right hlookup
      hlookup hleftInclude hrightInclude hfuel hfuel hrightLeftTarget
      hrightRightTarget hrightOther
  exact
    not_selectionSetsDataEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_root_arguments_child_response_diff_of_field_ok
      schema rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftInitialSpine rightInitialSpine variableValues parentFuel
      parentType responseName fieldName leftArguments rightArguments
      leftRuntime rightRuntime hobject hleftNormal hrightNormal hleftFree
      hrightFree hleftMem hrightMem hlookup hleftInclude hrightInclude
      hfuel hargumentsDiff hleftChildResponse hrightChildResponse hchildNot
      hleftFieldOk hrightFieldOk

theorem
    not_selectionSetsDataEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_root_fieldName_child_response_diff_of_field_cases
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (parentFuel : Nat)
    (parentType responseName leftFieldName rightFieldName : Name)
    (leftArguments rightArguments : List Argument) (leftRuntime rightRuntime : Name)
    {left right : List Selection}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {leftFieldDefinition rightFieldDefinition : FieldDefinition}
    {leftChildFields rightChildFields : List (Name × Execution.ResponseValue)}
    {leftChildErrors rightChildErrors : Nat}
    : objectTypeNameBool schema parentType = true
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> Selection.field responseName leftFieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName rightFieldName rightArguments
            rightDirectives rightChildSelectionSet
          ∈ right
      -> schema.lookupField parentType leftFieldName = some leftFieldDefinition
      -> schema.lookupField parentType rightFieldName = some rightFieldDefinition
      -> schema.typeIncludesObjectBool leftFieldDefinition.outputType.namedType
            leftRuntime
          = true
      -> schema.typeIncludesObjectBool rightFieldDefinition.outputType.namedType
            rightRuntime
          = true
      -> leafProbeFuel leftFieldDefinition.outputType ≤ parentFuel
      -> leafProbeFuel rightFieldDefinition.outputType ≤ parentFuel
      -> leftFieldName ≠ rightFieldName
      -> Execution.executeSelectionSetAsResponse schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet leftInitialSpine rightInitialSpine
                parentType leftFieldName rightFieldName leftArguments
                rightArguments leftRuntime rightRuntime)
              parentType leftFieldName rightFieldName leftArguments
              rightArguments)
            variableValues
            (parentFuel - leafProbeFuel leftFieldDefinition.outputType)
            leftRuntime
            (projectionTargetResolverValue
              (.object leftRuntime
                (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
                  leftInitialSelectionSet leftInitialSpine)))
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
                parentType leftFieldName rightFieldName leftArguments
                rightArguments leftRuntime rightRuntime)
              parentType leftFieldName rightFieldName leftArguments
              rightArguments)
            variableValues
            (parentFuel - leafProbeFuel rightFieldDefinition.outputType)
            rightRuntime
            (projectionTargetResolverValue
              (.object rightRuntime
                (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                  rightInitialSelectionSet rightInitialSpine)))
            rightChildSelectionSet
          = ({
                data := Execution.ResponseValue.object rightChildFields,
                errors := rightChildErrors
              }
              : Execution.Response)
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.ResponseValue.object leftChildFields)
            (Execution.ResponseValue.object rightChildFields)
      -> (∀ responseName arguments directives childSelectionSet,
            Selection.field responseName leftFieldName arguments directives
                childSelectionSet
              ∈ left
            -> Argument.argumentsEquivalent arguments leftArguments
            -> ∃ childFields childErrors,
                Execution.executeSelectionSetAsResponse schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairSelectedPathProbeResolvers schema
                      leftInitialSelectionSet rightInitialSelectionSet
                      leftInitialSpine rightInitialSpine parentType
                      leftFieldName rightFieldName leftArguments rightArguments
                      leftRuntime rightRuntime)
                    parentType leftFieldName rightFieldName leftArguments
                    rightArguments)
                  variableValues
                  (parentFuel - leafProbeFuel leftFieldDefinition.outputType)
                  leftRuntime
                  (projectionTargetResolverValue
                    (.object leftRuntime
                      (FieldPairSelectedPathProbeRef.target
                        FieldPairProbeTag.left leftInitialSelectionSet
                        leftInitialSpine)))
                  childSelectionSet
                = ({
                      data := Execution.ResponseValue.object childFields,
                      errors := childErrors
                    }
                    : Execution.Response))
      -> (∀ responseName arguments directives childSelectionSet,
            Selection.field responseName rightFieldName arguments directives
                childSelectionSet
              ∈ left
            -> Argument.argumentsEquivalent arguments rightArguments
            -> ∃ childFields childErrors,
                Execution.executeSelectionSetAsResponse schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairSelectedPathProbeResolvers schema
                      leftInitialSelectionSet rightInitialSelectionSet
                      leftInitialSpine rightInitialSpine parentType
                      leftFieldName rightFieldName leftArguments rightArguments
                      leftRuntime rightRuntime)
                    parentType leftFieldName rightFieldName leftArguments
                    rightArguments)
                  variableValues
                  (parentFuel - leafProbeFuel rightFieldDefinition.outputType)
                  rightRuntime
                  (projectionTargetResolverValue
                    (.object rightRuntime
                      (FieldPairSelectedPathProbeRef.target
                        FieldPairProbeTag.right rightInitialSelectionSet
                        rightInitialSpine)))
                  childSelectionSet
                = ({
                      data := Execution.ResponseValue.object childFields,
                      errors := childErrors
                    }
                    : Execution.Response))
      -> (∀ responseName arguments directives childSelectionSet,
            Selection.field responseName leftFieldName arguments directives
                childSelectionSet
              ∈ right
            -> Argument.argumentsEquivalent arguments leftArguments
            -> ∃ childFields childErrors,
                Execution.executeSelectionSetAsResponse schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairSelectedPathProbeResolvers schema
                      leftInitialSelectionSet rightInitialSelectionSet
                      leftInitialSpine rightInitialSpine parentType
                      leftFieldName rightFieldName leftArguments rightArguments
                      leftRuntime rightRuntime)
                    parentType leftFieldName rightFieldName leftArguments
                    rightArguments)
                  variableValues
                  (parentFuel - leafProbeFuel leftFieldDefinition.outputType)
                  leftRuntime
                  (projectionTargetResolverValue
                    (.object leftRuntime
                      (FieldPairSelectedPathProbeRef.target
                        FieldPairProbeTag.left leftInitialSelectionSet
                        leftInitialSpine)))
                  childSelectionSet
                = ({
                      data := Execution.ResponseValue.object childFields,
                      errors := childErrors
                    }
                    : Execution.Response))
      -> (∀ responseName arguments directives childSelectionSet,
            Selection.field responseName rightFieldName arguments directives
                childSelectionSet
              ∈ right
            -> Argument.argumentsEquivalent arguments rightArguments
            -> ∃ childFields childErrors,
                Execution.executeSelectionSetAsResponse schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairSelectedPathProbeResolvers schema
                      leftInitialSelectionSet rightInitialSelectionSet
                      leftInitialSpine rightInitialSpine parentType
                      leftFieldName rightFieldName leftArguments rightArguments
                      leftRuntime rightRuntime)
                    parentType leftFieldName rightFieldName leftArguments
                    rightArguments)
                  variableValues
                  (parentFuel - leafProbeFuel rightFieldDefinition.outputType)
                  rightRuntime
                  (projectionTargetResolverValue
                    (.object rightRuntime
                      (FieldPairSelectedPathProbeRef.target
                        FieldPairProbeTag.right rightInitialSelectionSet
                        rightInitialSpine)))
                  childSelectionSet
                = ({
                      data := Execution.ResponseValue.object childFields,
                      errors := childErrors
                    }
                    : Execution.Response))
      -> (∀ responseName siblingFieldName arguments directives childSelectionSet,
            Selection.field responseName siblingFieldName arguments directives
                childSelectionSet
              ∈ left
            -> ∃ responseValue fieldErrors,
                Execution.executeField schema
                  (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet
                    (ProjectionResolverRef.filler
                      : ProjectionResolverRef FieldPairSelectedPathProbeRef))
                  variableValues (parentFuel + 1)
                  (projectionRootResolverValue
                    (.object parentType FieldPairSelectedPathProbeRef.root))
                  responseName
                  [{
                    parentType := parentType,
                    responseName := responseName,
                    fieldName := siblingFieldName,
                    arguments := arguments,
                    selectionSet := childSelectionSet
                  }]
                = .ok ([(responseName, responseValue)], fieldErrors))
      -> (∀ responseName siblingFieldName arguments directives childSelectionSet,
            Selection.field responseName siblingFieldName arguments directives
                childSelectionSet
              ∈ right
            -> ∃ responseValue fieldErrors,
                Execution.executeField schema
                  (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet
                    (ProjectionResolverRef.filler
                      : ProjectionResolverRef FieldPairSelectedPathProbeRef))
                  variableValues (parentFuel + 1)
                  (projectionRootResolverValue
                    (.object parentType FieldPairSelectedPathProbeRef.root))
                  responseName
                  [{
                    parentType := parentType,
                    responseName := responseName,
                    fieldName := siblingFieldName,
                    arguments := arguments,
                    selectionSet := childSelectionSet
                  }]
                = .ok ([(responseName, responseValue)], fieldErrors))
      -> ¬ selectionSetsDataEquivalent schema parentType left right := by
  intro hobject hleftNormal hrightNormal hleftFree hrightFree hleftMem
    hrightMem hleftLookup hrightLookup hleftInclude hrightInclude
    hleftFuel hrightFuel hfieldDiff hleftChildResponse
    hrightChildResponse hchildNot hleftLeftTarget hleftRightTarget
    hrightLeftTarget hrightRightTarget hleftDeep hrightDeep
  have hleftOther :
      ∀ responseName siblingFieldName arguments directives childSelectionSet,
        Selection.field responseName siblingFieldName arguments directives
            childSelectionSet ∈ left ->
        ¬ fieldPairProjectionTarget parentType leftFieldName rightFieldName
            leftArguments rightArguments parentType siblingFieldName
            arguments ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSelectedPathProbeResolvers schema
                  leftInitialSelectionSet rightInitialSelectionSet
                  leftInitialSpine rightInitialSpine parentType
                  leftFieldName rightFieldName leftArguments rightArguments
                  leftRuntime rightRuntime)
                parentType leftFieldName rightFieldName leftArguments
                rightArguments)
              variableValues (parentFuel + 1)
              (projectionRootResolverValue
                (.object parentType FieldPairSelectedPathProbeRef.root))
              responseName
              [{
                parentType := parentType,
                responseName := responseName,
                fieldName := siblingFieldName,
                arguments := arguments,
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(responseName, responseValue)], fieldErrors) :=
    selectionSetOtherFieldsExecuteOk_fieldPairOrDeepSuccess_selectedPathProbe_of_deepSuccessWithRef_ok
      schema rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftInitialSpine rightInitialSpine variableValues (parentFuel + 1)
      parentType leftFieldName rightFieldName leftArguments rightArguments
      leftRuntime rightRuntime left hleftDeep
  have hrightOther :
      ∀ responseName siblingFieldName arguments directives childSelectionSet,
        Selection.field responseName siblingFieldName arguments directives
            childSelectionSet ∈ right ->
        ¬ fieldPairProjectionTarget parentType leftFieldName rightFieldName
            leftArguments rightArguments parentType siblingFieldName
            arguments ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSelectedPathProbeResolvers schema
                  leftInitialSelectionSet rightInitialSelectionSet
                  leftInitialSpine rightInitialSpine parentType
                  leftFieldName rightFieldName leftArguments rightArguments
                  leftRuntime rightRuntime)
                parentType leftFieldName rightFieldName leftArguments
                rightArguments)
              variableValues (parentFuel + 1)
              (projectionRootResolverValue
                (.object parentType FieldPairSelectedPathProbeRef.root))
              responseName
              [{
                parentType := parentType,
                responseName := responseName,
                fieldName := siblingFieldName,
                arguments := arguments,
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(responseName, responseValue)], fieldErrors) :=
    selectionSetOtherFieldsExecuteOk_fieldPairOrDeepSuccess_selectedPathProbe_of_deepSuccessWithRef_ok
      schema rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftInitialSpine rightInitialSpine variableValues (parentFuel + 1)
      parentType leftFieldName rightFieldName leftArguments rightArguments
      leftRuntime rightRuntime right hrightDeep
  have hleftFieldOk :
      ∀ responseName siblingFieldName arguments directives childSelectionSet,
        Selection.field responseName siblingFieldName arguments directives
            childSelectionSet ∈ left ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSelectedPathProbeResolvers schema
                  leftInitialSelectionSet rightInitialSelectionSet
                  leftInitialSpine rightInitialSpine parentType
                  leftFieldName rightFieldName leftArguments rightArguments
                  leftRuntime rightRuntime)
                parentType leftFieldName rightFieldName leftArguments
                rightArguments)
              variableValues (parentFuel + 1)
              (projectionRootResolverValue
                (.object parentType FieldPairSelectedPathProbeRef.root))
              responseName
              [{
                parentType := parentType,
                responseName := responseName,
                fieldName := siblingFieldName,
                arguments := arguments,
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(responseName, responseValue)], fieldErrors) :=
    selectionSetFieldsExecuteOk_fieldPairOrDeepSuccess_selectedPathProbe_of_field_cases
      schema rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftInitialSpine rightInitialSpine variableValues parentFuel
      parentType leftFieldName rightFieldName leftArguments rightArguments
      leftRuntime rightRuntime leftFieldDefinition rightFieldDefinition left
      hleftLookup hrightLookup hleftInclude hrightInclude hleftFuel
      hrightFuel hleftLeftTarget hleftRightTarget hleftOther
  have hrightFieldOk :
      ∀ responseName siblingFieldName arguments directives childSelectionSet,
        Selection.field responseName siblingFieldName arguments directives
            childSelectionSet ∈ right ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSelectedPathProbeResolvers schema
                  leftInitialSelectionSet rightInitialSelectionSet
                  leftInitialSpine rightInitialSpine parentType
                  leftFieldName rightFieldName leftArguments rightArguments
                  leftRuntime rightRuntime)
                parentType leftFieldName rightFieldName leftArguments
                rightArguments)
              variableValues (parentFuel + 1)
              (projectionRootResolverValue
                (.object parentType FieldPairSelectedPathProbeRef.root))
              responseName
              [{
                parentType := parentType,
                responseName := responseName,
                fieldName := siblingFieldName,
                arguments := arguments,
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(responseName, responseValue)], fieldErrors) :=
    selectionSetFieldsExecuteOk_fieldPairOrDeepSuccess_selectedPathProbe_of_field_cases
      schema rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftInitialSpine rightInitialSpine variableValues parentFuel
      parentType leftFieldName rightFieldName leftArguments rightArguments
      leftRuntime rightRuntime leftFieldDefinition rightFieldDefinition right
      hleftLookup hrightLookup hleftInclude hrightInclude hleftFuel
      hrightFuel hrightLeftTarget hrightRightTarget hrightOther
  exact
    not_selectionSetsDataEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_root_fieldName_child_response_diff_of_field_ok
      schema rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftInitialSpine rightInitialSpine variableValues parentFuel
      parentType responseName leftFieldName rightFieldName leftArguments
      rightArguments leftRuntime rightRuntime hobject hleftNormal
      hrightNormal hleftFree hrightFree hleftMem hrightMem hleftLookup
      hrightLookup hleftInclude hrightInclude hleftFuel hrightFuel
      hfieldDiff hleftChildResponse hrightChildResponse hchildNot
      hleftFieldOk hrightFieldOk

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_tagged_abstract_inlineFragment_body
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine leftSpine rightSpine
      : List NormalSelectionSetObservableFieldStep)
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
                (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet leftInitialSpine rightInitialSpine
                  targetParent leftField rightField leftArguments rightArguments
                  leftRuntime rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) runtimeType
              (projectionTargetResolverValue
                (.object runtimeType
                  (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
                    leftCurrentSelectionSet leftSpine)))
              bodySelectionSet).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet leftInitialSpine rightInitialSpine
                  targetParent leftField rightField leftArguments rightArguments
                  leftRuntime rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) runtimeType
              (projectionTargetResolverValue
                (.object runtimeType
                  (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                    rightCurrentSelectionSet rightSpine)))
              bodySelectionSet).data
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet leftInitialSpine rightInitialSpine
                  targetParent leftField rightField leftArguments rightArguments
                  leftRuntime rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) runtimeType
              (projectionTargetResolverValue
                (.object runtimeType
                  (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
                    leftCurrentSelectionSet leftSpine)))
              (pref
                ++ Selection.inlineFragment (some runtimeType) [] bodySelectionSet
                    :: suffix)).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet leftInitialSpine rightInitialSpine
                  targetParent leftField rightField leftArguments rightArguments
                  leftRuntime rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) runtimeType
              (projectionTargetResolverValue
                (.object runtimeType
                  (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                    rightCurrentSelectionSet rightSpine)))
              (pref
                ++ Selection.inlineFragment (some runtimeType) [] bodySelectionSet
                    :: suffix)).data := by
  intro hnonObject hruntimeObject hfree hnormal hbodyNot hsemantic
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet
      (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
        rightInitialSelectionSet leftInitialSpine rightInitialSpine
        targetParent leftField rightField leftArguments rightArguments
        leftRuntime rightRuntime)
      targetParent leftField rightField leftArguments rightArguments
  let leftSource :=
    projectionTargetResolverValue
      (.object runtimeType
        (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
          leftCurrentSelectionSet leftSpine))
  let rightSource :=
    projectionTargetResolverValue
      (.object runtimeType
        (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
          rightCurrentSelectionSet rightSpine))
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
          (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
            leftCurrentSelectionSet leftSpine))
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
          (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
            rightCurrentSelectionSet rightSpine))
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
            (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
              leftCurrentSelectionSet leftSpine))
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
            (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
              rightCurrentSelectionSet rightSpine))
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
    executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_field_ok_of_field_children
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet currentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine spine
      : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField parentType sourceRuntimeType : Name)
    (leftArguments rightArguments : List Argument) (leftRuntime rightRuntime : Name)
    (tag : FieldPairProbeTag) (selectionSet : List Selection)
    : (∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
        -> ∃ fieldDefinition,
            schema.lookupField parentType fieldName = some fieldDefinition
            ∧ leafProbeFuel fieldDefinition.outputType ≤ fuel
            ∧ ((TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
                  = false
                ∨ ∃ childRuntimeType tail responseFields childErrors,
                    (selectedObservableFieldSpineNext? fieldName arguments spine
                        = some (some childRuntimeType, tail)
                      ∧ (((objectTypeNameBool schema fieldDefinition.outputType.namedType
                                = true
                              ∧ childRuntimeType = fieldDefinition.outputType.namedType)
                            ∨ ((TypeRef.named
                                    fieldDefinition.outputType.namedType).isCompositeBool
                                    schema
                                  = true
                                ∧ objectTypeNameBool schema
                                    fieldDefinition.outputType.namedType
                                  = false))
                          ∧ schema.typeIncludesObjectBool
                              fieldDefinition.outputType.namedType
                              childRuntimeType
                            = true
                          ∧ Execution.executeSelectionSetAsResponse schema
                              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                                (fieldPairSelectedPathProbeResolvers schema
                                  leftInitialSelectionSet rightInitialSelectionSet
                                  leftInitialSpine rightInitialSpine targetParent
                                  leftField rightField leftArguments rightArguments
                                  leftRuntime rightRuntime)
                                targetParent leftField rightField leftArguments
                                rightArguments)
                              variableValues
                              (fuel - leafProbeFuel fieldDefinition.outputType)
                              childRuntimeType
                              (projectionTargetResolverValue
                                (.object childRuntimeType
                                  (FieldPairSelectedPathProbeRef.target tag
                                    (fieldPairPathLocalNextSelectionSet schema
                                      parentType childRuntimeType fieldName
                                      arguments currentSelectionSet)
                                    tail)))
                              childSelectionSet
                            = ({
                                  data := Execution.ResponseValue.object responseFields,
                                  errors := childErrors
                                }
                                : Execution.Response)))))
      -> ∀ responseName fieldName arguments directives childSelectionSet,
          Selection.field responseName fieldName arguments directives childSelectionSet
            ∈ selectionSet
          -> ∃ responseValue fieldErrors,
              (Execution.executeField schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairSelectedPathProbeResolvers schema
                      leftInitialSelectionSet rightInitialSelectionSet
                      leftInitialSpine rightInitialSpine targetParent leftField
                      rightField leftArguments rightArguments leftRuntime
                      rightRuntime)
                    targetParent leftField rightField leftArguments
                    rightArguments)
                  variableValues (fuel + 1)
                  (projectionTargetResolverValue
                    (.object sourceRuntimeType
                      (FieldPairSelectedPathProbeRef.target tag
                        currentSelectionSet spine)))
                  responseName
                  [{
                    parentType := parentType
                    responseName := responseName
                    fieldName := fieldName
                    arguments := arguments
                    selectionSet := childSelectionSet
                  }]
                = .ok ([(responseName, responseValue)], fieldErrors)) := by
  intro hchildren responseName fieldName arguments directives
    childSelectionSet hmem
  rcases hchildren responseName fieldName arguments directives
      childSelectionSet hmem with
    ⟨fieldDefinition, hlookup, hfuel, hleafOrChild⟩
  rcases hleafOrChild with hleaf | hchild
  · refine ⟨leafProbeResponseValue fieldDefinition.outputType tag.scalar, 0, ?_⟩
    exact
      executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_leaf
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet currentSelectionSet leftInitialSpine
        rightInitialSpine spine variableValues fuel targetParent
        leftField rightField parentType fieldName sourceRuntimeType
        responseName leftArguments rightArguments arguments leftRuntime
        rightRuntime tag childSelectionSet fieldDefinition hlookup
        hfuel hleaf
  · rcases hchild with
      ⟨childRuntimeType, tail, responseFields, childErrors, hselected,
        hruntime, hinclude, hchildResponse⟩
    rcases
        executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_objectProbe_ok_of_child_response
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet currentSelectionSet leftInitialSpine
          rightInitialSpine spine tail variableValues fuel targetParent
          leftField rightField parentType fieldName sourceRuntimeType
          responseName leftArguments rightArguments arguments leftRuntime
          rightRuntime tag childSelectionSet fieldDefinition
          childRuntimeType responseFields childErrors hlookup hselected
          hruntime hinclude hfuel hchildResponse with
      ⟨responseValue, fieldErrors, hexecute, _hnonNull⟩
    exact ⟨responseValue, fieldErrors, hexecute⟩

def SelectedPathSelectionSetFieldChildrenReady
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet currentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine spine
      : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues)
    (fuel : Nat) (targetParent leftField rightField parentType : Name)
    (leftArguments rightArguments : List Argument)
    (leftRuntime rightRuntime : Name) (tag : FieldPairProbeTag)
    (selectionSet : List Selection)
    : Prop :=
  ∀ responseName fieldName arguments directives childSelectionSet,
    Selection.field responseName fieldName arguments directives childSelectionSet
      ∈ selectionSet
    -> ∃ fieldDefinition,
        schema.lookupField parentType fieldName = some fieldDefinition
        ∧ leafProbeFuel fieldDefinition.outputType ≤ fuel
        ∧ (((TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
              = false)
            ∨ (∃ childRuntimeType tail responseFields childErrors,
                selectedObservableFieldSpineNext? fieldName arguments spine
                  = some (some childRuntimeType, tail)
                ∧ (((objectTypeNameBool schema fieldDefinition.outputType.namedType = true
                        ∧ childRuntimeType = fieldDefinition.outputType.namedType)
                      ∨ ((TypeRef.named
                              fieldDefinition.outputType.namedType).isCompositeBool
                              schema
                            = true
                          ∧ objectTypeNameBool schema fieldDefinition.outputType.namedType
                            = false))
                    ∧ schema.typeIncludesObjectBool
                        fieldDefinition.outputType.namedType
                        childRuntimeType
                      = true
                    ∧ Execution.executeSelectionSetAsResponse schema
                        (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                          (fieldPairSelectedPathProbeResolvers schema
                            leftInitialSelectionSet rightInitialSelectionSet
                            leftInitialSpine rightInitialSpine targetParent
                            leftField rightField leftArguments rightArguments
                            leftRuntime rightRuntime)
                          targetParent leftField rightField leftArguments
                          rightArguments)
                        variableValues
                        (fuel - leafProbeFuel fieldDefinition.outputType)
                        childRuntimeType
                        (projectionTargetResolverValue
                          (.object childRuntimeType
                            (FieldPairSelectedPathProbeRef.target tag
                              (fieldPairPathLocalNextSelectionSet schema
                                parentType childRuntimeType fieldName
                                arguments currentSelectionSet)
                              tail)))
                        childSelectionSet
                      = ({
                            data := Execution.ResponseValue.object responseFields,
                            errors := childErrors
                          }
                          : Execution.Response)))
            ∨ (∃ responseFields childErrors,
                objectTypeNameBool schema fieldDefinition.outputType.namedType = true
                ∧ Execution.executeSelectionSetAsResponse schema
                    (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                      (fieldPairSelectedPathProbeResolvers schema
                        leftInitialSelectionSet rightInitialSelectionSet
                        leftInitialSpine rightInitialSpine targetParent
                        leftField rightField leftArguments rightArguments
                        leftRuntime rightRuntime)
                      targetParent leftField rightField leftArguments
                      rightArguments)
                    variableValues
                    (fuel - leafProbeFuel fieldDefinition.outputType)
                    fieldDefinition.outputType.namedType
                    (projectionTargetResolverValue
                      (.object fieldDefinition.outputType.namedType
                        (FieldPairSelectedPathProbeRef.target tag
                          (fieldPairPathLocalNextSelectionSet schema
                            parentType fieldDefinition.outputType.namedType
                            fieldName arguments currentSelectionSet)
                          (selectedObservableFieldSpineTailForRuntime
                            fieldDefinition.outputType.namedType fieldName
                            arguments spine))))
                    childSelectionSet
                  = ({
                        data := Execution.ResponseValue.object responseFields,
                        errors := childErrors
                      }
                      : Execution.Response))
            ∨ (∃ childRuntimeType responseFields childErrors,
                (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool
                    schema
                  = true
                ∧ objectTypeNameBool schema fieldDefinition.outputType.namedType = false
                ∧ selectedObservableFieldSpineNext? fieldName arguments spine = none
                ∧ abstractRuntimeForFieldHeadDeep? schema parentType
                    fieldName arguments parentType currentSelectionSet
                  = some childRuntimeType
                ∧ schema.typeIncludesObjectBool
                    fieldDefinition.outputType.namedType childRuntimeType
                  = true
                ∧ Execution.executeSelectionSetAsResponse schema
                    (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                      (fieldPairSelectedPathProbeResolvers schema
                        leftInitialSelectionSet rightInitialSelectionSet
                        leftInitialSpine rightInitialSpine targetParent
                        leftField rightField leftArguments rightArguments
                        leftRuntime rightRuntime)
                      targetParent leftField rightField leftArguments
                      rightArguments)
                    variableValues
                    (fuel - leafProbeFuel fieldDefinition.outputType)
                    childRuntimeType
                    (projectionTargetResolverValue
                      (.object childRuntimeType
                        (FieldPairSelectedPathProbeRef.target tag
                          (fieldPairPathLocalNextSelectionSet schema
                            parentType childRuntimeType fieldName arguments
                            currentSelectionSet)
                          [])))
                    childSelectionSet
                  = ({
                        data := Execution.ResponseValue.object responseFields,
                        errors := childErrors
                      }
                      : Execution.Response)))

theorem
    executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_field_ok_of_selectedPathFieldChildrenReady
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet currentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine spine
      : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField parentType sourceRuntimeType : Name)
    (leftArguments rightArguments : List Argument) (leftRuntime rightRuntime : Name)
    (tag : FieldPairProbeTag) (selectionSet : List Selection)
    : SelectedPathSelectionSetFieldChildrenReady schema rootSelectionSet
        leftInitialSelectionSet rightInitialSelectionSet currentSelectionSet
        leftInitialSpine rightInitialSpine spine variableValues fuel
        targetParent leftField rightField parentType leftArguments
        rightArguments leftRuntime rightRuntime tag selectionSet
      -> ∀ responseName fieldName arguments directives childSelectionSet,
          Selection.field responseName fieldName arguments directives childSelectionSet
            ∈ selectionSet
          -> ∃ responseValue fieldErrors,
              (Execution.executeField schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairSelectedPathProbeResolvers schema
                      leftInitialSelectionSet rightInitialSelectionSet
                      leftInitialSpine rightInitialSpine targetParent leftField
                      rightField leftArguments rightArguments leftRuntime
                      rightRuntime)
                    targetParent leftField rightField leftArguments
                    rightArguments)
                  variableValues (fuel + 1)
                  (projectionTargetResolverValue
                    (.object sourceRuntimeType
                      (FieldPairSelectedPathProbeRef.target tag
                        currentSelectionSet spine)))
                  responseName
                  [{
                    parentType := parentType
                    responseName := responseName
                    fieldName := fieldName
                    arguments := arguments
                    selectionSet := childSelectionSet
                  }]
                = .ok ([(responseName, responseValue)], fieldErrors)) := by
  intro hchildren responseName fieldName arguments directives
    childSelectionSet hmem
  rcases hchildren responseName fieldName arguments directives
      childSelectionSet hmem with
    ⟨fieldDefinition, hlookup, hfuel, hcase⟩
  rcases hcase with hleaf | hcase
  · refine ⟨leafProbeResponseValue fieldDefinition.outputType tag.scalar, 0, ?_⟩
    exact
      executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_leaf
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet currentSelectionSet leftInitialSpine
        rightInitialSpine spine variableValues fuel targetParent
        leftField rightField parentType fieldName sourceRuntimeType
        responseName leftArguments rightArguments arguments leftRuntime
        rightRuntime tag childSelectionSet fieldDefinition hlookup
        hfuel hleaf
  rcases hcase with hselectedChild | hcase
  · rcases hselectedChild with
      ⟨childRuntimeType, tail, responseFields, childErrors, hselected,
        hruntime, hinclude, hchildResponse⟩
    rcases
        executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_objectProbe_ok_of_child_response
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet currentSelectionSet leftInitialSpine
          rightInitialSpine spine tail variableValues fuel targetParent
          leftField rightField parentType fieldName sourceRuntimeType
          responseName leftArguments rightArguments arguments leftRuntime
          rightRuntime tag childSelectionSet fieldDefinition
          childRuntimeType responseFields childErrors hlookup hselected
          hruntime hinclude hfuel hchildResponse with
      ⟨responseValue, fieldErrors, hexecute, _hnonNull⟩
    exact ⟨responseValue, fieldErrors, hexecute⟩
  rcases hcase with hobjectOutput | habstractFallback
  · rcases hobjectOutput with
      ⟨responseFields, childErrors, hobject, hchildResponse⟩
    rcases
        executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_objectOutput_ok_of_child_response
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet currentSelectionSet leftInitialSpine
          rightInitialSpine spine variableValues fuel targetParent
          leftField rightField parentType fieldName sourceRuntimeType
          responseName leftArguments rightArguments arguments leftRuntime
          rightRuntime tag childSelectionSet fieldDefinition responseFields
          childErrors hlookup hobject hfuel hchildResponse with
      ⟨responseValue, fieldErrors, hexecute, _hnonNull⟩
    exact ⟨responseValue, fieldErrors, hexecute⟩
  · rcases habstractFallback with
      ⟨childRuntimeType, responseFields, childErrors, hcomposite,
        hnonObject, hselectedNone, hruntime, hinclude, hchildResponse⟩
    rcases
        executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_abstractFallback_ok_of_child_response
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet currentSelectionSet leftInitialSpine
          rightInitialSpine spine variableValues fuel targetParent
          leftField rightField parentType fieldName sourceRuntimeType
          responseName leftArguments rightArguments arguments leftRuntime
          rightRuntime tag childSelectionSet fieldDefinition
          childRuntimeType responseFields childErrors hlookup hcomposite
          hnonObject hselectedNone hruntime hinclude hfuel
          hchildResponse with
      ⟨responseValue, fieldErrors, hexecute, _hnonNull⟩
    exact ⟨responseValue, fieldErrors, hexecute⟩

theorem
    executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_of_field_children
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet currentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine spine
      : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField parentType sourceRuntimeType : Name)
    (leftArguments rightArguments : List Argument) (leftRuntime rightRuntime : Name)
    (tag : FieldPairProbeTag) (selectionSet : List Selection)
    : selectionSetDirectiveFree selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> objectTypeNameBool schema parentType = true
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ selectionSet
            -> ∃ fieldDefinition,
                schema.lookupField parentType fieldName = some fieldDefinition
                ∧ leafProbeFuel fieldDefinition.outputType ≤ fuel
                ∧ ((TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool
                        schema
                      = false
                    ∨ ∃ childRuntimeType tail responseFields childErrors,
                        (selectedObservableFieldSpineNext? fieldName arguments spine
                            = some (some childRuntimeType, tail)
                          ∧ (((objectTypeNameBool schema
                                      fieldDefinition.outputType.namedType
                                    = true
                                  ∧ childRuntimeType
                                    = fieldDefinition.outputType.namedType)
                                ∨ ((TypeRef.named
                                        fieldDefinition.outputType.namedType).isCompositeBool
                                        schema
                                      = true
                                    ∧ objectTypeNameBool schema
                                        fieldDefinition.outputType.namedType
                                      = false))
                              ∧ schema.typeIncludesObjectBool
                                  fieldDefinition.outputType.namedType
                                  childRuntimeType
                                = true
                              ∧ Execution.executeSelectionSetAsResponse schema
                                  (fieldPairOrDeepSuccessResolvers schema
                                    rootSelectionSet
                                    (fieldPairSelectedPathProbeResolvers schema
                                      leftInitialSelectionSet rightInitialSelectionSet
                                      leftInitialSpine rightInitialSpine targetParent
                                      leftField rightField leftArguments rightArguments
                                      leftRuntime rightRuntime)
                                    targetParent leftField rightField leftArguments
                                    rightArguments)
                                  variableValues
                                  (fuel - leafProbeFuel fieldDefinition.outputType)
                                  childRuntimeType
                                  (projectionTargetResolverValue
                                    (.object childRuntimeType
                                      (FieldPairSelectedPathProbeRef.target tag
                                        (fieldPairPathLocalNextSelectionSet schema
                                          parentType childRuntimeType fieldName
                                          arguments currentSelectionSet)
                                        tail)))
                                  childSelectionSet
                                = ({
                                      data :=
                                        Execution.ResponseValue.object responseFields,
                                      errors := childErrors
                                    }
                                    : Execution.Response)))))
      -> ∃ responseFields errors,
          (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSelectedPathProbeResolvers schema
                  leftInitialSelectionSet rightInitialSelectionSet
                  leftInitialSpine rightInitialSpine targetParent leftField
                  rightField leftArguments rightArguments leftRuntime
                  rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) parentType
              (projectionTargetResolverValue
                (.object sourceRuntimeType
                  (FieldPairSelectedPathProbeRef.target tag currentSelectionSet spine)))
              selectionSet
            = ({ data := Execution.ResponseValue.object responseFields, errors := errors }
                : Execution.Response)) := by
  intro hfree hnormal hobject hchildren
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet
      (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
        rightInitialSelectionSet leftInitialSpine rightInitialSpine
        targetParent leftField rightField leftArguments rightArguments
        leftRuntime rightRuntime)
      targetParent leftField rightField leftArguments rightArguments
  have hfieldOk :
      ∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
            childSelectionSet ∈ selectionSet ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema resolvers variableValues (fuel + 1)
              (projectionTargetResolverValue
                (.object sourceRuntimeType
                  (FieldPairSelectedPathProbeRef.target tag
                    currentSelectionSet spine)))
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
      executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_field_ok_of_field_children
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet currentSelectionSet leftInitialSpine
        rightInitialSpine spine variableValues fuel targetParent
        leftField rightField parentType sourceRuntimeType leftArguments
        rightArguments leftRuntime rightRuntime tag selectionSet hchildren
  simpa [resolvers] using
    ExecutionSuccess.executeSelectionSetAsResponse_object_of_field_ok schema
      resolvers variableValues (fuel + 1) parentType
      (projectionTargetResolverValue
        (.object sourceRuntimeType
          (FieldPairSelectedPathProbeRef.target tag currentSelectionSet
            spine)))
      selectionSet hfree hnormal hobject hfieldOk

theorem
    executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_of_selectedPathFieldChildrenReady
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet currentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine spine
      : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField parentType sourceRuntimeType : Name)
    (leftArguments rightArguments : List Argument) (leftRuntime rightRuntime : Name)
    (tag : FieldPairProbeTag) (selectionSet : List Selection)
    : selectionSetDirectiveFree selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> objectTypeNameBool schema parentType = true
      -> SelectedPathSelectionSetFieldChildrenReady schema rootSelectionSet
          leftInitialSelectionSet rightInitialSelectionSet currentSelectionSet
          leftInitialSpine rightInitialSpine spine variableValues fuel
          targetParent leftField rightField parentType leftArguments
          rightArguments leftRuntime rightRuntime tag selectionSet
      -> ∃ responseFields errors,
          (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSelectedPathProbeResolvers schema
                  leftInitialSelectionSet rightInitialSelectionSet
                  leftInitialSpine rightInitialSpine targetParent leftField
                  rightField leftArguments rightArguments leftRuntime
                  rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) parentType
              (projectionTargetResolverValue
                (.object sourceRuntimeType
                  (FieldPairSelectedPathProbeRef.target tag currentSelectionSet spine)))
              selectionSet
            = ({ data := Execution.ResponseValue.object responseFields, errors := errors }
                : Execution.Response)) := by
  intro hfree hnormal hobject hchildren
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet
      (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
        rightInitialSelectionSet leftInitialSpine rightInitialSpine
        targetParent leftField rightField leftArguments rightArguments
        leftRuntime rightRuntime)
      targetParent leftField rightField leftArguments rightArguments
  have hfieldOk :
      ∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
            childSelectionSet ∈ selectionSet ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema resolvers variableValues (fuel + 1)
              (projectionTargetResolverValue
                (.object sourceRuntimeType
                  (FieldPairSelectedPathProbeRef.target tag
                    currentSelectionSet spine)))
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
        rightInitialSelectionSet currentSelectionSet leftInitialSpine
        rightInitialSpine spine variableValues fuel targetParent
        leftField rightField parentType sourceRuntimeType leftArguments
        rightArguments leftRuntime rightRuntime tag selectionSet hchildren
  simpa [resolvers] using
    ExecutionSuccess.executeSelectionSetAsResponse_object_of_field_ok schema
      resolvers variableValues (fuel + 1) parentType
      (projectionTargetResolverValue
        (.object sourceRuntimeType
          (FieldPairSelectedPathProbeRef.target tag currentSelectionSet
            spine)))
      selectionSet hfree hnormal hobject hfieldOk

theorem
    executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_abstract_of_runtime_inlineFragment_body_response
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet currentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine spine
      : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField normalParentType runtimeType : Name)
    (leftArguments rightArguments : List Argument) (leftRuntime rightRuntime : Name)
    (tag : FieldPairProbeTag) {selectionSet : List Selection}
    : objectTypeNameBool schema normalParentType = false
      -> objectTypeNameBool schema runtimeType = true
      -> selectionSetDirectiveFree selectionSet
      -> selectionSetNormal schema normalParentType selectionSet
      -> (∀ bodySelectionSet,
            Selection.inlineFragment (some runtimeType) [] bodySelectionSet ∈ selectionSet
            -> ∃ responseFields errors,
                Execution.executeSelectionSetAsResponse schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairSelectedPathProbeResolvers schema
                      leftInitialSelectionSet rightInitialSelectionSet
                      leftInitialSpine rightInitialSpine targetParent leftField
                      rightField leftArguments rightArguments leftRuntime
                      rightRuntime)
                    targetParent leftField rightField leftArguments rightArguments)
                  variableValues (fuel + 1) runtimeType
                  (projectionTargetResolverValue
                    (.object runtimeType
                      (FieldPairSelectedPathProbeRef.target tag
                        currentSelectionSet spine)))
                  bodySelectionSet
                = ({
                      data := Execution.ResponseValue.object responseFields,
                      errors := errors
                    }
                    : Execution.Response))
      -> ∃ responseFields errors,
          Execution.executeSelectionSetAsResponse schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairSelectedPathProbeResolvers schema
                leftInitialSelectionSet rightInitialSelectionSet
                leftInitialSpine rightInitialSpine targetParent leftField
                rightField leftArguments rightArguments leftRuntime
                rightRuntime)
              targetParent leftField rightField leftArguments rightArguments)
            variableValues (fuel + 1) runtimeType
            (projectionTargetResolverValue
              (.object runtimeType
                (FieldPairSelectedPathProbeRef.target tag currentSelectionSet spine)))
            selectionSet
          = ({ data := Execution.ResponseValue.object responseFields, errors := errors }
              : Execution.Response) := by
  intro hnonObject hruntimeObject hfree hnormal hbodyResponse
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet
      (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
        rightInitialSelectionSet leftInitialSpine rightInitialSpine
        targetParent leftField rightField leftArguments rightArguments
        leftRuntime rightRuntime)
      targetParent leftField rightField leftArguments rightArguments
  let source :=
    projectionTargetResolverValue
      (.object runtimeType
        (FieldPairSelectedPathProbeRef.target tag currentSelectionSet
          spine))
  by_cases hruntimeMem :
      runtimeType ∈ selectionSet.filterMap inlineFragmentTypeCondition?
  · rcases List.mem_filterMap.mp hruntimeMem with
      ⟨selection, hselectionMem, hselectionRuntime⟩
    cases selection with
    | field responseName fieldName arguments directives childSelectionSet =>
        simp [inlineFragmentTypeCondition?] at hselectionRuntime
    | inlineFragment maybeTypeCondition directives bodySelectionSet =>
        cases maybeTypeCondition with
        | none =>
            simp [inlineFragmentTypeCondition?] at hselectionRuntime
        | some typeCondition =>
            simp [inlineFragmentTypeCondition?] at hselectionRuntime
            subst typeCondition
            have hdirectives : directives = [] :=
              selectionSetDirectiveFree_inlineFragment_directives_nil_of_mem
                hfree hselectionMem
            subst directives
            rcases List.mem_iff_append.mp hselectionMem with
              ⟨pref, suffix, hselectionSet⟩
            subst selectionSet
            have hinlineMem :
                Selection.inlineFragment (some runtimeType) []
                    bodySelectionSet ∈
                  pref ++ Selection.inlineFragment (some runtimeType) []
                    bodySelectionSet :: suffix := by
              exact List.mem_append_right _ (by simp)
            rcases hbodyResponse bodySelectionSet hinlineMem with
              ⟨bodyFields, bodyErrors, hbodyExec⟩
            have hmiddle :
                Execution.executeSelectionSet schema resolvers variableValues
                  (fuel + 1) runtimeType source
                  (pref ++ Selection.inlineFragment (some runtimeType) []
                    bodySelectionSet :: suffix)
                =
                Execution.executeSelectionSet schema resolvers variableValues
                  (fuel + 1) runtimeType source
                  [Selection.inlineFragment (some runtimeType) []
                    bodySelectionSet] :=
              by
                simpa [source, projectionTargetResolverValue,
                  projectionResolverValue] using
                  executeSelectionSet_middle_inlineFragment_only_eq_singleton_at_runtime_parent
                    schema resolvers variableValues (fuel + 1)
                    (ProjectionResolverRef.target
                      (FieldPairSelectedPathProbeRef.target tag
                        currentSelectionSet spine))
                    hnonObject hruntimeObject hfree hnormal
            have happly :
                Execution.doesFragmentTypeApplyBool schema runtimeType
                  source runtimeType = true := by
              dsimp [source]
              simpa [projectionTargetResolverValue, projectionResolverValue]
                using
                  (doesFragmentTypeApplyBool_object_self schema
                    (ref :=
                      ProjectionResolverRef.target
                        (FieldPairSelectedPathProbeRef.target tag
                          currentSelectionSet spine))
                    hruntimeObject)
            have hflatten :
                Execution.executeSelectionSet schema resolvers variableValues
                  (fuel + 1) runtimeType source
                  [Selection.inlineFragment (some runtimeType) []
                    bodySelectionSet]
                =
                Execution.executeSelectionSet schema resolvers variableValues
                  (fuel + 1) runtimeType source bodySelectionSet := by
              simpa using
                executeSelectionSet_inlineFragment_some_directiveFree_apply_flatten
                  schema resolvers variableValues (fuel + 1) runtimeType
                  runtimeType source bodySelectionSet [] happly
            refine ⟨bodyFields, bodyErrors, ?_⟩
            calc
              Execution.executeSelectionSetAsResponse schema resolvers variableValues
                    (fuel + 1) runtimeType source
                    (pref
                      ++ Selection.inlineFragment (some runtimeType) [] bodySelectionSet
                          :: suffix)
                  = Execution.executeSelectionSetAsResponse schema resolvers
                      variableValues (fuel + 1) runtimeType source
                      [Selection.inlineFragment (some runtimeType) []
                        bodySelectionSet] := by
                simp [Execution.executeSelectionSetAsResponse, hmiddle]
              _ = Execution.executeSelectionSetAsResponse schema resolvers variableValues
                    (fuel + 1) runtimeType source bodySelectionSet := by
                simp [Execution.executeSelectionSetAsResponse, hflatten]
              _ = ({
                      data := Execution.ResponseValue.object bodyFields,
                      errors := bodyErrors
                    }
                    : Execution.Response) := by
                simpa [resolvers, source] using hbodyExec
  · have hcollect :
        Execution.collectFields schema variableValues runtimeType source
          selectionSet = [] :=
      by
        simpa [source, projectionTargetResolverValue,
          projectionResolverValue] using
          collectFields_inlineFragments_without_typeCondition_eq_nil_at_runtime_parent
            schema variableValues (normalParentType := normalParentType)
            (executionParentType := runtimeType) (runtimeType := runtimeType)
            (ProjectionResolverRef.target
              (FieldPairSelectedPathProbeRef.target tag currentSelectionSet
                spine))
            hnonObject hfree hnormal hruntimeMem
    have hcollectObject :
        Execution.collectFields schema variableValues runtimeType
          (Execution.ResolverValue.object runtimeType
            (ProjectionResolverRef.target
              (FieldPairSelectedPathProbeRef.target tag currentSelectionSet
                spine)))
          selectionSet = [] := by
      simpa [source, projectionTargetResolverValue,
        projectionResolverValue] using hcollect
    refine ⟨[], 0, ?_⟩
    simp [projectionTargetResolverValue, projectionResolverValue,
      Execution.executeSelectionSetAsResponse, Execution.selectionSetResultToResponse,
      Execution.executeSelectionSet, Execution.executeRootSelectionSet,
      hcollectObject, Execution.executeCollectedFields]

theorem
    executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_nil_of_valid_normal_support_context_fuel_ge_size
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ∀ n normalParentType variableDefinitions (selectionSet : List Selection)
            fuel runtimeType targetParent leftField rightField
            (leftArguments rightArguments : List Argument)
            (leftRuntime rightRuntime : Name) (tag : FieldPairProbeTag)
            (currentSelectionSet : List Selection),
          SelectionSet.size selectionSet < n
          -> selectionSetDeepProbeFuel schema normalParentType selectionSet ≤ fuel
          -> Validation.selectionSetValid schema variableDefinitions normalParentType
              selectionSet
          -> selectionSetDirectiveFree selectionSet
          -> selectionSetNormal schema normalParentType selectionSet
          -> schema.typeIncludesObjectBool normalParentType runtimeType = true
          -> PathLocalSupportValidNormal schema runtimeType currentSelectionSet
          -> (objectTypeNameBool schema normalParentType = true
              -> PathLocalSelectionSetCurrentContext selectionSet currentSelectionSet)
          -> (objectTypeNameBool schema normalParentType = false
              -> ∀ {directives bodySelectionSet},
                  Selection.inlineFragment (some runtimeType) directives bodySelectionSet
                    ∈ selectionSet
                  -> PathLocalSelectionSetCurrentContext bodySelectionSet
                      currentSelectionSet)
          -> ∃ responseFields errors,
              Execution.executeSelectionSetAsResponse schema
                (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                  (fieldPairSelectedPathProbeResolvers schema
                    leftInitialSelectionSet rightInitialSelectionSet
                    leftInitialSpine rightInitialSpine targetParent leftField
                    rightField leftArguments rightArguments leftRuntime
                    rightRuntime)
                  targetParent leftField rightField leftArguments
                  rightArguments)
                variableValues (fuel + 1) runtimeType
                (projectionTargetResolverValue
                  (.object runtimeType
                    (FieldPairSelectedPathProbeRef.target tag currentSelectionSet [])))
                selectionSet
              = ({
                    data := Execution.ResponseValue.object responseFields,
                    errors := errors
                  }
                  : Execution.Response) := by
  intro hschema n
  induction n with
  | zero =>
      intro normalParentType variableDefinitions selectionSet fuel runtimeType
        targetParent leftField rightField leftArguments rightArguments
        leftRuntime rightRuntime tag currentSelectionSet hsize
        _hfuel _hvalid _hfree _hnormal _hinclude _hsupport
        _hobjectContext _habstractContext
      omega
  | succ n ih =>
      intro normalParentType variableDefinitions selectionSet fuel runtimeType
        targetParent leftField rightField leftArguments rightArguments
        leftRuntime rightRuntime tag currentSelectionSet hsize hfuel hvalid
        hfree hnormal hinclude hsupport hobjectContext habstractContext
      have hruntimeObject :
          objectTypeNameBool schema runtimeType = true :=
        objectTypeNameBool_of_typeIncludesObjectBool hschema hinclude
      by_cases hparentObject :
          objectTypeNameBool schema normalParentType = true
      · have hruntimeEq : runtimeType = normalParentType :=
          typeIncludesObjectBool_eq_of_objectTypeNameBool_true schema
            hparentObject hinclude
        subst runtimeType
        have hcontext :
            PathLocalSelectionSetCurrentContext selectionSet
              currentSelectionSet :=
          hobjectContext hparentObject
        refine
          executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_of_selectedPathFieldChildrenReady
            schema rootSelectionSet leftInitialSelectionSet
            rightInitialSelectionSet currentSelectionSet leftInitialSpine
            rightInitialSpine [] variableValues fuel targetParent
            leftField rightField normalParentType normalParentType
            leftArguments rightArguments leftRuntime rightRuntime tag
            selectionSet hfree hnormal hparentObject ?_
        intro responseName fieldName arguments directives childSelectionSet
          hmem
        rcases selectionSetValid_field_lookup_of_mem hvalid hmem with
          ⟨fieldDefinition, hlookup, _harguments, _hfieldSelectionValid⟩
        have hleafFuel :
            leafProbeFuel fieldDefinition.outputType ≤ fuel := by
          have hlocal :=
            leafProbeFuel_le_selectionSetDeepProbeFuel_of_field_mem schema
              normalParentType (selectionSet := selectionSet)
              (responseName := responseName) (fieldName := fieldName)
              (arguments := arguments) (directives := directives)
              (childSelectionSet := childSelectionSet)
              (fieldDefinition := fieldDefinition) hmem hlookup
          omega
        refine ⟨fieldDefinition, hlookup, hleafFuel, ?_⟩
        by_cases hreturnLeaf :
            (TypeRef.named
                fieldDefinition.outputType.namedType).isCompositeBool
              schema = false
        · exact Or.inl hreturnLeaf
        · have hreturnComposite :
              (TypeRef.named
                  fieldDefinition.outputType.namedType).isCompositeBool
                schema = true := by
            cases h :
                (TypeRef.named
                    fieldDefinition.outputType.namedType).isCompositeBool
                  schema <;>
              simp [h] at hreturnLeaf ⊢
          have hfieldDeepFuel :
              leafProbeFuel fieldDefinition.outputType
                + selectionSetDeepProbeFuel schema
                  fieldDefinition.outputType.namedType childSelectionSet
                + 1 ≤ fuel := by
            have hlocal :=
              selectionSetDeepProbeFuel_field_mem schema normalParentType
                selectionSet responseName fieldName arguments directives
                childSelectionSet fieldDefinition hmem hlookup
            omega
          let childFuel :=
            fuel - leafProbeFuel fieldDefinition.outputType - 1
          have hchildSize :
              SelectionSet.size childSelectionSet < n := by
            have hlt :=
              selectionSet_size_field_child_lt_of_mem
                (responseName := responseName) (fieldName := fieldName)
                (arguments := arguments) (directives := directives)
                (childSelectionSet := childSelectionSet)
                (selectionSet := selectionSet) hmem
            omega
          have hchildFuel :
              selectionSetDeepProbeFuel schema
                  fieldDefinition.outputType.namedType childSelectionSet
                ≤ childFuel := by
            dsimp [childFuel]
            omega
          have hchildFree :
              selectionSetDirectiveFree childSelectionSet :=
            selectionSetDirectiveFree_field_child_of_mem hfree hmem
          have hchildNormal :
              selectionSetNormal schema
                fieldDefinition.outputType.namedType childSelectionSet :=
            selectionSetNormal_field_child_of_mem_lookup hnormal hmem
              hlookup
          by_cases hreturnObject :
              objectTypeNameBool schema
                  fieldDefinition.outputType.namedType = true
          · have hchildValid :
                Validation.selectionSetValid schema variableDefinitions
                  fieldDefinition.outputType.namedType childSelectionSet :=
              selectionSetValid_object_field_child_of_mem_lookup hvalid hmem
                hlookup hreturnObject
            have hchildInclude :
                schema.typeIncludesObjectBool
                    fieldDefinition.outputType.namedType
                    fieldDefinition.outputType.namedType = true :=
              typeIncludesObjectBool_self_of_objectTypeNameBool schema
                hreturnObject
            have hallFields :
                selectionsAllFields childSelectionSet :=
              selectionSetNormal_allFields_of_object hchildNormal
                hreturnObject
            have hpruned :
                runtimePrunedSelectionSet schema
                    fieldDefinition.outputType.namedType childSelectionSet =
                  childSelectionSet :=
              runtimePrunedSelectionSet_eq_self_of_allFields schema
                fieldDefinition.outputType.namedType hallFields
            have hchildSupport :
                PathLocalSupportValidNormal schema
                  fieldDefinition.outputType.namedType
                  (fieldPairPathLocalNextSelectionSet schema
                    normalParentType fieldDefinition.outputType.namedType
                    fieldName arguments currentSelectionSet) :=
              hsupport.fieldPairPathLocalNextSelectionSet_of_object_output
                hparentObject hreturnObject hlookup rfl
            have hchildContext :
                PathLocalSelectionSetCurrentContext childSelectionSet
                  (fieldPairPathLocalNextSelectionSet schema
                    normalParentType fieldDefinition.outputType.namedType
                    fieldName arguments currentSelectionSet) :=
              PathLocalSelectionSetCurrentContext.fieldPairPathLocalNextSelectionSet_field_child
                (schema := schema) (currentRuntimeType := normalParentType)
                (childRuntimeType :=
                  fieldDefinition.outputType.namedType)
                (targetField := fieldName) (responseName := responseName)
                (targetArguments := arguments) (arguments := arguments)
                (directives := directives) (selectionSet := selectionSet)
                (childSelectionSet := childSelectionSet)
                (currentSelectionSet := currentSelectionSet)
                hcontext hmem
                (argumentsEquivalent_refl_forSyntaxDiff arguments) hpruned
            rcases
                ih fieldDefinition.outputType.namedType variableDefinitions
                  childSelectionSet childFuel
                  fieldDefinition.outputType.namedType targetParent
                  leftField rightField leftArguments rightArguments
                  leftRuntime rightRuntime tag
                  (fieldPairPathLocalNextSelectionSet schema
                    normalParentType fieldDefinition.outputType.namedType
                    fieldName arguments currentSelectionSet)
                  hchildSize hchildFuel hchildValid hchildFree
                  hchildNormal hchildInclude hchildSupport
                  (fun _hobject => hchildContext)
                  (fun hnonObject => by
                    rw [hreturnObject] at hnonObject
                    simp at hnonObject) with
              ⟨responseFields, errors, hchildResponse⟩
            have hchildFuelEq :
                childFuel + 1 =
                  fuel - leafProbeFuel fieldDefinition.outputType := by
              dsimp [childFuel]
              omega
            refine Or.inr (Or.inr (Or.inl ?_))
            refine ⟨responseFields, errors, hreturnObject, ?_⟩
            simpa [selectedObservableFieldSpineTailForRuntime,
              selectedObservableFieldSpineNext?, hchildFuelEq] using
              hchildResponse
          · have hreturnNonObject :
                objectTypeNameBool schema
                    fieldDefinition.outputType.namedType = false := by
              cases h :
                  objectTypeNameBool schema
                    fieldDefinition.outputType.namedType <;>
                simp [h] at hreturnObject ⊢
            have hsound :
                PathLocalCurrentRuntimeSound schema
                  (normalParentType, currentSelectionSet) :=
              hsupport.sound
            have hready :
                PathLocalSelectionSetHeadReady schema normalParentType
                  currentSelectionSet selectionSet :=
              PathLocalSelectionSetCurrentContext.headReady_of_valid_normal
                hsound hcontext hvalid hnormal
            rcases
                hready responseName fieldName arguments directives
                  childSelectionSet fieldDefinition hmem hlookup
                  hreturnComposite hreturnNonObject with
              ⟨childRuntimeType, hruntime, hchildInclude⟩
            have hchildObject :
                objectTypeNameBool schema childRuntimeType = true :=
              objectTypeNameBool_of_typeIncludesObjectBool hschema
                hchildInclude
            have hchildNonempty : childSelectionSet ≠ [] := by
              rcases
                  selectionSetValid_field_lookup_leaf_or_composite_child
                    hvalid hmem with
                ⟨candidateDefinition, hcandidateLookup, hkind⟩
              have hdefinitionEq :
                  candidateDefinition = fieldDefinition := by
                rw [hlookup] at hcandidateLookup
                exact (Option.some.inj hcandidateLookup).symm
              subst candidateDefinition
              rcases hkind with hleaf | hcomposite
              · have hleafComposite := hleaf.1
                rw [hreturnComposite] at hleafComposite
                simp at hleafComposite
              · exact hcomposite.2.1
            have hchildValid :
                Validation.selectionSetValid schema variableDefinitions
                  fieldDefinition.outputType.namedType childSelectionSet :=
              selectionSetValid_field_child_of_mem_lookup hvalid hmem
                hchildNonempty hlookup
            have hchildSupport :
                PathLocalSupportValidNormal schema childRuntimeType
                  (fieldPairPathLocalNextSelectionSet schema
                    normalParentType childRuntimeType fieldName arguments
                    currentSelectionSet) :=
              hsupport.fieldPairPathLocalNextSelectionSet_of_abstract_output
                hparentObject hchildObject hlookup hreturnComposite
                hchildInclude
            rcases
                ih fieldDefinition.outputType.namedType variableDefinitions
                  childSelectionSet childFuel childRuntimeType targetParent
                  leftField rightField leftArguments rightArguments
                  leftRuntime rightRuntime tag
                  (fieldPairPathLocalNextSelectionSet schema
                    normalParentType childRuntimeType fieldName arguments
                    currentSelectionSet)
                  hchildSize hchildFuel hchildValid hchildFree
                  hchildNormal hchildInclude hchildSupport
                  (fun hchildParentObject => by
                    rw [hreturnNonObject] at hchildParentObject
                    simp at hchildParentObject)
                  (by
                    intro _hchildParentNonObject
                    intro bodyDirectives bodySelectionSet hbodyMem
                    exact
                      PathLocalSelectionSetCurrentContext.fieldPairPathLocalNextSelectionSet_inlineFragment_body
                        (schema := schema)
                        (currentRuntimeType := normalParentType)
                        (childRuntimeType := childRuntimeType)
                        (childParentType :=
                          fieldDefinition.outputType.namedType)
                        (targetField := fieldName)
                        (responseName := responseName)
                        (targetArguments := arguments)
                        (arguments := arguments)
                        (directives := directives)
                        (bodyDirectives := bodyDirectives)
                        (selectionSet := selectionSet)
                        (childSelectionSet := childSelectionSet)
                        (bodySelectionSet := bodySelectionSet)
                        (currentSelectionSet := currentSelectionSet)
                        hcontext hmem hbodyMem
                        (argumentsEquivalent_refl_forSyntaxDiff arguments)
                        hchildNormal hchildObject) with
              ⟨responseFields, errors, hchildResponse⟩
            have hchildFuelEq :
                childFuel + 1 =
                  fuel - leafProbeFuel fieldDefinition.outputType := by
              dsimp [childFuel]
              omega
            refine Or.inr (Or.inr (Or.inr ?_))
            refine ⟨
              childRuntimeType,
              responseFields,
              errors,
              hreturnComposite,
              hreturnNonObject,
              ?_,
              hruntime,
              hchildInclude,
              ?_
            ⟩
            · simp [selectedObservableFieldSpineNext?]
            · simpa [hchildFuelEq] using hchildResponse
      · have hparentNonObject :
            objectTypeNameBool schema normalParentType = false := by
          cases h : objectTypeNameBool schema normalParentType <;>
            simp [h] at hparentObject ⊢
        refine
          executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_abstract_of_runtime_inlineFragment_body_response
            schema rootSelectionSet leftInitialSelectionSet
            rightInitialSelectionSet currentSelectionSet leftInitialSpine
            rightInitialSpine [] variableValues fuel targetParent
            leftField rightField normalParentType runtimeType
            leftArguments rightArguments leftRuntime rightRuntime tag
            hparentNonObject hruntimeObject hfree hnormal ?_
        intro bodySelectionSet hinlineMem
        have hbodyValid :
            Validation.selectionSetValid schema variableDefinitions
              runtimeType bodySelectionSet :=
          selectionSetValid_inlineFragment_some_child_of_mem hvalid
            hinlineMem
        have hbodyFree : selectionSetDirectiveFree bodySelectionSet :=
          selectionSetDirectiveFree_inlineFragment_child_of_mem hfree
            hinlineMem
        have hbodyNormal :
            selectionSetNormal schema runtimeType bodySelectionSet :=
          (selectionSetNormal_inlineFragment_child_of_mem hnormal
            hinlineMem).2
        have hbodySize :
            SelectionSet.size bodySelectionSet < n := by
          have hlt :=
            selectionSet_size_inlineFragment_child_lt_of_mem
              (typeCondition := some runtimeType)
              (directives := ([] : List DirectiveApplication))
              (childSelectionSet := bodySelectionSet)
              (selectionSet := selectionSet) hinlineMem
          omega
        have hbodyFuel :
            selectionSetDeepProbeFuel schema runtimeType bodySelectionSet
              ≤ fuel := by
          have hlocal :=
            selectionSetDeepProbeFuel_inlineFragment_some_mem schema
              normalParentType selectionSet runtimeType
              ([] : List DirectiveApplication) bodySelectionSet hinlineMem
          omega
        have hbodyInclude :
            schema.typeIncludesObjectBool runtimeType runtimeType = true :=
          typeIncludesObjectBool_self_of_objectTypeNameBool schema
            hruntimeObject
        have hbodyContext :
            PathLocalSelectionSetCurrentContext bodySelectionSet
              currentSelectionSet :=
          habstractContext hparentNonObject hinlineMem
        rcases
            ih runtimeType variableDefinitions bodySelectionSet fuel
              runtimeType targetParent leftField rightField leftArguments
              rightArguments leftRuntime rightRuntime tag
              currentSelectionSet hbodySize hbodyFuel hbodyValid hbodyFree
              hbodyNormal hbodyInclude hsupport
              (fun _hobject => hbodyContext)
              (fun hnonObject => by
                rw [hruntimeObject] at hnonObject
                simp at hnonObject) with
          ⟨bodyFields, bodyErrors, hbodyResponse⟩
        exact ⟨bodyFields, bodyErrors, hbodyResponse⟩

theorem
    executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_of_valid_normal_runtimeSpine_support_context_fuel_ge_size
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ∀ n normalParentType variableDefinitions (selectionSet : List Selection)
            fuel runtimeType targetParent leftField rightField
            (leftArguments rightArguments : List Argument)
            (leftRuntime rightRuntime : Name) (tag : FieldPairProbeTag)
            (currentSelectionSet : List Selection)
            (spine : List NormalSelectionSetObservableFieldStep),
          SelectionSet.size selectionSet < n
          -> selectionSetDeepProbeFuel schema normalParentType selectionSet ≤ fuel
          -> Validation.selectionSetValid schema variableDefinitions normalParentType
              selectionSet
          -> selectionSetDirectiveFree selectionSet
          -> selectionSetNormal schema normalParentType selectionSet
          -> SelectedFieldSpineRuntimeValid schema normalParentType runtimeType spine
          -> PathLocalSupportValidNormal schema runtimeType currentSelectionSet
          -> (objectTypeNameBool schema normalParentType = true
              -> PathLocalSelectionSetCurrentContext selectionSet currentSelectionSet)
          -> (objectTypeNameBool schema normalParentType = false
              -> ∀ {directives bodySelectionSet},
                  Selection.inlineFragment (some runtimeType) directives bodySelectionSet
                    ∈ selectionSet
                  -> PathLocalSelectionSetCurrentContext bodySelectionSet
                      currentSelectionSet)
          -> ∃ responseFields errors,
              Execution.executeSelectionSetAsResponse schema
                (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                  (fieldPairSelectedPathProbeResolvers schema
                    leftInitialSelectionSet rightInitialSelectionSet
                    leftInitialSpine rightInitialSpine targetParent leftField
                    rightField leftArguments rightArguments leftRuntime
                    rightRuntime)
                  targetParent leftField rightField leftArguments
                  rightArguments)
                variableValues (fuel + 1) runtimeType
                (projectionTargetResolverValue
                  (.object runtimeType
                    (FieldPairSelectedPathProbeRef.target tag currentSelectionSet spine)))
                selectionSet
              = ({
                    data := Execution.ResponseValue.object responseFields,
                    errors := errors
                  }
                  : Execution.Response) := by
  intro hschema n
  induction n with
  | zero =>
      intro normalParentType variableDefinitions selectionSet fuel runtimeType
        targetParent leftField rightField leftArguments rightArguments
        leftRuntime rightRuntime tag currentSelectionSet spine hsize
        _hfuel _hvalid _hfree _hnormal _hspineValid _hsupport
        _hobjectContext _habstractContext
      omega
  | succ n ih =>
      intro normalParentType variableDefinitions selectionSet fuel runtimeType
        targetParent leftField rightField leftArguments rightArguments
        leftRuntime rightRuntime tag currentSelectionSet spine hsize hfuel
        hvalid hfree hnormal hspineValid hsupport hobjectContext
        habstractContext
      have hinclude :
          schema.typeIncludesObjectBool normalParentType runtimeType = true :=
        selectedFieldSpineRuntimeValid_typeIncludes hspineValid
      have hruntimeObject :
          objectTypeNameBool schema runtimeType = true :=
        selectedFieldSpineRuntimeValid_runtime_object hspineValid
      by_cases hparentObject :
          objectTypeNameBool schema normalParentType = true
      · have hruntimeEq : runtimeType = normalParentType :=
          typeIncludesObjectBool_eq_of_objectTypeNameBool_true schema
            hparentObject hinclude
        subst runtimeType
        have hcontext :
            PathLocalSelectionSetCurrentContext selectionSet
              currentSelectionSet :=
          hobjectContext hparentObject
        refine
          executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_of_selectedPathFieldChildrenReady
            schema rootSelectionSet leftInitialSelectionSet
            rightInitialSelectionSet currentSelectionSet leftInitialSpine
            rightInitialSpine spine variableValues fuel targetParent
            leftField rightField normalParentType normalParentType
            leftArguments rightArguments leftRuntime rightRuntime tag
            selectionSet hfree hnormal hparentObject ?_
        intro responseName fieldName arguments directives childSelectionSet
          hmem
        rcases selectionSetValid_field_lookup_of_mem hvalid hmem with
          ⟨fieldDefinition, hlookup, _harguments, _hfieldSelectionValid⟩
        have hleafFuel :
            leafProbeFuel fieldDefinition.outputType ≤ fuel := by
          have hlocal :=
            leafProbeFuel_le_selectionSetDeepProbeFuel_of_field_mem schema
              normalParentType (selectionSet := selectionSet)
              (responseName := responseName) (fieldName := fieldName)
              (arguments := arguments) (directives := directives)
              (childSelectionSet := childSelectionSet)
              (fieldDefinition := fieldDefinition) hmem hlookup
          omega
        refine ⟨fieldDefinition, hlookup, hleafFuel, ?_⟩
        by_cases hreturnLeaf :
            (TypeRef.named
                fieldDefinition.outputType.namedType).isCompositeBool
              schema = false
        · exact Or.inl hreturnLeaf
        · have hreturnComposite :
              (TypeRef.named
                  fieldDefinition.outputType.namedType).isCompositeBool
                schema = true := by
            cases h :
                (TypeRef.named
                    fieldDefinition.outputType.namedType).isCompositeBool
                  schema <;>
              simp [h] at hreturnLeaf ⊢
          have hfieldDeepFuel :
              leafProbeFuel fieldDefinition.outputType
                + selectionSetDeepProbeFuel schema
                  fieldDefinition.outputType.namedType childSelectionSet
                + 1 ≤ fuel := by
            have hlocal :=
              selectionSetDeepProbeFuel_field_mem schema normalParentType
                selectionSet responseName fieldName arguments directives
                childSelectionSet fieldDefinition hmem hlookup
            omega
          let childFuel :=
            fuel - leafProbeFuel fieldDefinition.outputType - 1
          have hchildSize :
              SelectionSet.size childSelectionSet < n := by
            have hlt :=
              selectionSet_size_field_child_lt_of_mem
                (responseName := responseName) (fieldName := fieldName)
                (arguments := arguments) (directives := directives)
                (childSelectionSet := childSelectionSet)
                (selectionSet := selectionSet) hmem
            omega
          have hchildFuel :
              selectionSetDeepProbeFuel schema
                  fieldDefinition.outputType.namedType childSelectionSet
                ≤ childFuel := by
            dsimp [childFuel]
            omega
          have hchildFree :
              selectionSetDirectiveFree childSelectionSet :=
            selectionSetDirectiveFree_field_child_of_mem hfree hmem
          have hchildNormal :
              selectionSetNormal schema
                fieldDefinition.outputType.namedType childSelectionSet :=
            selectionSetNormal_field_child_of_mem_lookup hnormal hmem
              hlookup
          by_cases hreturnObject :
              objectTypeNameBool schema
                  fieldDefinition.outputType.namedType = true
          · have hchildValid :
                Validation.selectionSetValid schema variableDefinitions
                  fieldDefinition.outputType.namedType childSelectionSet :=
              selectionSetValid_object_field_child_of_mem_lookup hvalid hmem
                hlookup hreturnObject
            have hchildInclude :
                schema.typeIncludesObjectBool
                    fieldDefinition.outputType.namedType
                    fieldDefinition.outputType.namedType = true :=
              typeIncludesObjectBool_self_of_objectTypeNameBool schema
                hreturnObject
            have hallFields :
                selectionsAllFields childSelectionSet :=
              selectionSetNormal_allFields_of_object hchildNormal
                hreturnObject
            have hpruned :
                runtimePrunedSelectionSet schema
                    fieldDefinition.outputType.namedType childSelectionSet =
                  childSelectionSet :=
              runtimePrunedSelectionSet_eq_self_of_allFields schema
                fieldDefinition.outputType.namedType hallFields
            have hchildSupport :
                PathLocalSupportValidNormal schema
                  fieldDefinition.outputType.namedType
                  (fieldPairPathLocalNextSelectionSet schema
                    normalParentType fieldDefinition.outputType.namedType
                    fieldName arguments currentSelectionSet) :=
              hsupport.fieldPairPathLocalNextSelectionSet_of_object_output
                hparentObject hreturnObject hlookup rfl
            have hchildContext :
                PathLocalSelectionSetCurrentContext childSelectionSet
                  (fieldPairPathLocalNextSelectionSet schema
                    normalParentType fieldDefinition.outputType.namedType
                    fieldName arguments currentSelectionSet) :=
              PathLocalSelectionSetCurrentContext.fieldPairPathLocalNextSelectionSet_field_child
                (schema := schema) (currentRuntimeType := normalParentType)
                (childRuntimeType :=
                  fieldDefinition.outputType.namedType)
                (targetField := fieldName) (responseName := responseName)
                (targetArguments := arguments) (arguments := arguments)
                (directives := directives) (selectionSet := selectionSet)
                (childSelectionSet := childSelectionSet)
                (currentSelectionSet := currentSelectionSet)
                hcontext hmem
                (argumentsEquivalent_refl_forSyntaxDiff arguments) hpruned
            have htailCase :=
              selectedFieldSpineRuntimeValid_tailForRuntime_of_objectOutput
                (arguments := arguments) hspineValid hparentObject hlookup
                hreturnObject
            rcases htailCase with htailNil | htailValid
            · rcases
                executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_nil_of_valid_normal_support_context_fuel_ge_size
                  schema rootSelectionSet leftInitialSelectionSet
                  rightInitialSelectionSet leftInitialSpine
                  rightInitialSpine variableValues hschema
                  n fieldDefinition.outputType.namedType
                  variableDefinitions childSelectionSet childFuel
                  fieldDefinition.outputType.namedType targetParent
                  leftField rightField leftArguments rightArguments
                  leftRuntime rightRuntime tag
                  (fieldPairPathLocalNextSelectionSet schema
                    normalParentType fieldDefinition.outputType.namedType
                    fieldName arguments currentSelectionSet)
                  hchildSize hchildFuel hchildValid hchildFree
                  hchildNormal hchildInclude hchildSupport
                  (fun _hobject => hchildContext)
                  (fun hnonObject => by
                    rw [hreturnObject] at hnonObject
                    simp at hnonObject) with
                ⟨responseFields, errors, hchildResponse⟩
              have hchildFuelEq :
                  childFuel + 1 =
                    fuel - leafProbeFuel fieldDefinition.outputType := by
                dsimp [childFuel]
                omega
              refine Or.inr (Or.inr (Or.inl ?_))
              refine ⟨responseFields, errors, hreturnObject, ?_⟩
              simpa [htailNil, hchildFuelEq] using hchildResponse
            · rcases
                ih fieldDefinition.outputType.namedType
                  variableDefinitions childSelectionSet childFuel
                  fieldDefinition.outputType.namedType targetParent
                  leftField rightField leftArguments rightArguments
                  leftRuntime rightRuntime tag
                  (fieldPairPathLocalNextSelectionSet schema
                    normalParentType fieldDefinition.outputType.namedType
                    fieldName arguments currentSelectionSet)
                  (selectedObservableFieldSpineTailForRuntime
                    fieldDefinition.outputType.namedType fieldName
                    arguments spine)
                  hchildSize hchildFuel hchildValid hchildFree
                  hchildNormal htailValid hchildSupport
                  (fun _hobject => hchildContext)
                  (fun hnonObject => by
                    rw [hreturnObject] at hnonObject
                    simp at hnonObject) with
                ⟨responseFields, errors, hchildResponse⟩
              have hchildFuelEq :
                  childFuel + 1 =
                    fuel - leafProbeFuel fieldDefinition.outputType := by
                dsimp [childFuel]
                omega
              refine Or.inr (Or.inr (Or.inl ?_))
              refine ⟨responseFields, errors, hreturnObject, ?_⟩
              simpa [hchildFuelEq] using hchildResponse
          · have hreturnNonObject :
                objectTypeNameBool schema
                    fieldDefinition.outputType.namedType = false := by
              cases h :
                  objectTypeNameBool schema
                    fieldDefinition.outputType.namedType <;>
                simp [h] at hreturnObject ⊢
            have hchildNonempty : childSelectionSet ≠ [] := by
              rcases
                  selectionSetValid_field_lookup_leaf_or_composite_child
                    hvalid hmem with
                ⟨candidateDefinition, hcandidateLookup, hkind⟩
              have hdefinitionEq :
                  candidateDefinition = fieldDefinition := by
                rw [hlookup] at hcandidateLookup
                exact (Option.some.inj hcandidateLookup).symm
              subst candidateDefinition
              rcases hkind with hleaf | hcomposite
              · have hleafComposite := hleaf.1
                rw [hreturnComposite] at hleafComposite
                simp at hleafComposite
              · exact hcomposite.2.1
            have hchildValid :
                Validation.selectionSetValid schema variableDefinitions
                  fieldDefinition.outputType.namedType childSelectionSet :=
              selectionSetValid_field_child_of_mem_lookup hvalid hmem
                hchildNonempty hlookup
            cases hselected
                  : selectedObservableFieldSpineNext? fieldName arguments spine with
            | none =>
                have hsound :
                    PathLocalCurrentRuntimeSound schema
                      (normalParentType, currentSelectionSet) :=
                  hsupport.sound
                have hready :
                    PathLocalSelectionSetHeadReady schema normalParentType
                      currentSelectionSet selectionSet :=
                  PathLocalSelectionSetCurrentContext.headReady_of_valid_normal
                    hsound hcontext hvalid hnormal
                rcases
                    hready responseName fieldName arguments directives
                      childSelectionSet fieldDefinition hmem hlookup
                      hreturnComposite hreturnNonObject with
                  ⟨childRuntimeType, hruntime, hchildInclude⟩
                have hchildObject :
                    objectTypeNameBool schema childRuntimeType = true :=
                  objectTypeNameBool_of_typeIncludesObjectBool hschema
                    hchildInclude
                have hchildSupport :
                    PathLocalSupportValidNormal schema childRuntimeType
                      (fieldPairPathLocalNextSelectionSet schema
                        normalParentType childRuntimeType fieldName
                        arguments currentSelectionSet) :=
                  hsupport.fieldPairPathLocalNextSelectionSet_of_abstract_output
                    hparentObject hchildObject hlookup hreturnComposite
                    hchildInclude
                rcases
                    executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_nil_of_valid_normal_support_context_fuel_ge_size
                      schema rootSelectionSet leftInitialSelectionSet
                      rightInitialSelectionSet leftInitialSpine
                      rightInitialSpine variableValues hschema
                      n fieldDefinition.outputType.namedType
                      variableDefinitions childSelectionSet childFuel
                      childRuntimeType targetParent leftField rightField
                      leftArguments rightArguments leftRuntime rightRuntime
                      tag
                      (fieldPairPathLocalNextSelectionSet schema
                        normalParentType childRuntimeType fieldName
                        arguments currentSelectionSet)
                      hchildSize hchildFuel hchildValid hchildFree
                      hchildNormal hchildInclude hchildSupport
                      (fun hchildParentObject => by
                        rw [hreturnNonObject] at hchildParentObject
                        simp at hchildParentObject)
                      (by
                        intro _hchildParentNonObject
                        intro bodyDirectives bodySelectionSet hbodyMem
                        exact
                          PathLocalSelectionSetCurrentContext.fieldPairPathLocalNextSelectionSet_inlineFragment_body
                            (schema := schema)
                            (currentRuntimeType := normalParentType)
                            (childRuntimeType := childRuntimeType)
                            (childParentType :=
                              fieldDefinition.outputType.namedType)
                            (targetField := fieldName)
                            (responseName := responseName)
                            (targetArguments := arguments)
                            (arguments := arguments)
                            (directives := directives)
                            (bodyDirectives := bodyDirectives)
                            (selectionSet := selectionSet)
                            (childSelectionSet := childSelectionSet)
                            (bodySelectionSet := bodySelectionSet)
                            (currentSelectionSet := currentSelectionSet)
                            hcontext hmem hbodyMem
                            (argumentsEquivalent_refl_forSyntaxDiff
                              arguments)
                            hchildNormal hchildObject) with
                  ⟨responseFields, errors, hchildResponse⟩
                have hchildFuelEq :
                    childFuel + 1 =
                      fuel - leafProbeFuel fieldDefinition.outputType := by
                  dsimp [childFuel]
                  omega
                refine Or.inr (Or.inr (Or.inr ?_))
                refine ⟨
                  childRuntimeType,
                  responseFields,
                  errors,
                  hreturnComposite,
                  hreturnNonObject,
                  rfl,
                  hruntime,
                  hchildInclude,
                  ?_
                ⟩
                simpa [hchildFuelEq] using hchildResponse
            | some selected =>
                rcases selected with ⟨maybeRuntime, tail⟩
                cases maybeRuntime with
                | none =>
                    exact False.elim
                      (selectedFieldSpineRuntimeValid_no_leaf_selectedNext_of_composite
                        hspineValid hparentObject hlookup
                        hreturnComposite hselected)
                | some selectedRuntime =>
                    rcases
                        selectedFieldSpineRuntimeValid_child_of_selectedNext
                          hspineValid hparentObject hlookup hselected with
                      ⟨hruntimeCase, hchildInclude, htailValid⟩
                    have hchildObject :
                        objectTypeNameBool schema selectedRuntime = true :=
                      selectedFieldSpineRuntimeValid_runtime_object
                        htailValid
                    have hchildSupport :
                        PathLocalSupportValidNormal schema selectedRuntime
                          (fieldPairPathLocalNextSelectionSet schema
                            normalParentType selectedRuntime fieldName
                            arguments currentSelectionSet) :=
                      hsupport.fieldPairPathLocalNextSelectionSet_of_abstract_output
                        hparentObject hchildObject hlookup
                        hreturnComposite hchildInclude
                    rcases
                        ih fieldDefinition.outputType.namedType
                          variableDefinitions childSelectionSet childFuel
                          selectedRuntime targetParent leftField rightField
                          leftArguments rightArguments leftRuntime
                          rightRuntime tag
                          (fieldPairPathLocalNextSelectionSet schema
                            normalParentType selectedRuntime fieldName
                            arguments currentSelectionSet)
                          tail hchildSize hchildFuel hchildValid
                          hchildFree hchildNormal htailValid hchildSupport
                          (fun hchildParentObject => by
                            rw [hreturnNonObject] at hchildParentObject
                            simp at hchildParentObject)
                          (by
                            intro _hchildParentNonObject
                            intro bodyDirectives bodySelectionSet hbodyMem
                            exact
                              PathLocalSelectionSetCurrentContext.fieldPairPathLocalNextSelectionSet_inlineFragment_body
                                (schema := schema)
                                (currentRuntimeType := normalParentType)
                                (childRuntimeType := selectedRuntime)
                                (childParentType :=
                                  fieldDefinition.outputType.namedType)
                                (targetField := fieldName)
                                (responseName := responseName)
                                (targetArguments := arguments)
                                (arguments := arguments)
                                (directives := directives)
                                (bodyDirectives := bodyDirectives)
                                (selectionSet := selectionSet)
                                (childSelectionSet := childSelectionSet)
                                (bodySelectionSet := bodySelectionSet)
                                (currentSelectionSet := currentSelectionSet)
                                hcontext hmem hbodyMem
                                (argumentsEquivalent_refl_forSyntaxDiff
                                  arguments)
                                hchildNormal hchildObject) with
                      ⟨responseFields, errors, hchildResponse⟩
                    have hchildFuelEq :
                        childFuel + 1 =
                          fuel - leafProbeFuel fieldDefinition.outputType := by
                      dsimp [childFuel]
                      omega
                    refine Or.inr (Or.inl ?_)
                    refine ⟨
                      selectedRuntime,
                      tail,
                      responseFields,
                      errors,
                      rfl,
                      hruntimeCase,
                      hchildInclude,
                      ?_
                    ⟩
                    simpa [hchildFuelEq] using hchildResponse
      · have hparentNonObject :
            objectTypeNameBool schema normalParentType = false := by
          cases h : objectTypeNameBool schema normalParentType <;>
            simp [h] at hparentObject ⊢
        have hbodySpineValid :
            SelectedFieldSpineRuntimeValid schema runtimeType runtimeType
              spine := by
          cases hspineValid with
          | objectLeaf hobject _hlookup _hleaf =>
              rw [hparentNonObject] at hobject
              simp at hobject
          | objectChild hobject _hlookup _hcomposite _hchildValid =>
              rw [hparentNonObject] at hobject
              simp at hobject
          | abstractRuntime _hnonObject _hruntimeObject _hinclude
              hchildValid =>
              exact hchildValid
        refine
          executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_abstract_of_runtime_inlineFragment_body_response
            schema rootSelectionSet leftInitialSelectionSet
            rightInitialSelectionSet currentSelectionSet leftInitialSpine
            rightInitialSpine spine variableValues fuel targetParent
            leftField rightField normalParentType runtimeType
            leftArguments rightArguments leftRuntime rightRuntime tag
            hparentNonObject hruntimeObject hfree hnormal ?_
        intro bodySelectionSet hinlineMem
        have hbodyValid :
            Validation.selectionSetValid schema variableDefinitions
              runtimeType bodySelectionSet :=
          selectionSetValid_inlineFragment_some_child_of_mem hvalid
            hinlineMem
        have hbodyFree : selectionSetDirectiveFree bodySelectionSet :=
          selectionSetDirectiveFree_inlineFragment_child_of_mem hfree
            hinlineMem
        have hbodyNormal :
            selectionSetNormal schema runtimeType bodySelectionSet :=
          (selectionSetNormal_inlineFragment_child_of_mem hnormal
            hinlineMem).2
        have hbodySize :
            SelectionSet.size bodySelectionSet < n := by
          have hlt :=
            selectionSet_size_inlineFragment_child_lt_of_mem
              (typeCondition := some runtimeType)
              (directives := ([] : List DirectiveApplication))
              (childSelectionSet := bodySelectionSet)
              (selectionSet := selectionSet) hinlineMem
          omega
        have hbodyFuel :
            selectionSetDeepProbeFuel schema runtimeType bodySelectionSet
              ≤ fuel := by
          have hlocal :=
            selectionSetDeepProbeFuel_inlineFragment_some_mem schema
              normalParentType selectionSet runtimeType
              ([] : List DirectiveApplication) bodySelectionSet hinlineMem
          omega
        have hbodyContext :
            PathLocalSelectionSetCurrentContext bodySelectionSet
              currentSelectionSet :=
          habstractContext hparentNonObject hinlineMem
        rcases
            ih runtimeType variableDefinitions bodySelectionSet fuel
              runtimeType targetParent leftField rightField leftArguments
              rightArguments leftRuntime rightRuntime tag
              currentSelectionSet spine hbodySize hbodyFuel hbodyValid
              hbodyFree hbodyNormal hbodySpineValid hsupport
              (fun _hobject => hbodyContext)
              (fun hnonObject => by
                rw [hruntimeObject] at hnonObject
                simp at hnonObject) with
          ⟨bodyFields, bodyErrors, hbodyResponse⟩
        exact ⟨bodyFields, bodyErrors, hbodyResponse⟩

theorem
    executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_of_valid_normal_runtimeSpine_support_context_fuel_ge
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ∀ normalParentType variableDefinitions (selectionSet : List Selection)
            fuel runtimeType targetParent leftField rightField
            (leftArguments rightArguments : List Argument)
            (leftRuntime rightRuntime : Name) (tag : FieldPairProbeTag)
            (currentSelectionSet : List Selection)
            (spine : List NormalSelectionSetObservableFieldStep),
          selectionSetDeepProbeFuel schema normalParentType selectionSet ≤ fuel
          -> Validation.selectionSetValid schema variableDefinitions normalParentType
              selectionSet
          -> selectionSetDirectiveFree selectionSet
          -> selectionSetNormal schema normalParentType selectionSet
          -> SelectedFieldSpineRuntimeValid schema normalParentType runtimeType spine
          -> PathLocalSupportValidNormal schema runtimeType currentSelectionSet
          -> (objectTypeNameBool schema normalParentType = true
              -> PathLocalSelectionSetCurrentContext selectionSet currentSelectionSet)
          -> (objectTypeNameBool schema normalParentType = false
              -> ∀ {directives bodySelectionSet},
                  Selection.inlineFragment (some runtimeType) directives bodySelectionSet
                    ∈ selectionSet
                  -> PathLocalSelectionSetCurrentContext bodySelectionSet
                      currentSelectionSet)
          -> ∃ responseFields errors,
              Execution.executeSelectionSetAsResponse schema
                (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                  (fieldPairSelectedPathProbeResolvers schema
                    leftInitialSelectionSet rightInitialSelectionSet
                    leftInitialSpine rightInitialSpine targetParent leftField
                    rightField leftArguments rightArguments leftRuntime
                    rightRuntime)
                  targetParent leftField rightField leftArguments
                  rightArguments)
                variableValues (fuel + 1) runtimeType
                (projectionTargetResolverValue
                  (.object runtimeType
                    (FieldPairSelectedPathProbeRef.target tag currentSelectionSet spine)))
                selectionSet
              = ({
                    data := Execution.ResponseValue.object responseFields,
                    errors := errors
                  }
                  : Execution.Response) := by
  intro hschema normalParentType variableDefinitions selectionSet fuel
    runtimeType targetParent leftField rightField leftArguments
    rightArguments leftRuntime rightRuntime tag currentSelectionSet spine
    hfuel hvalid hfree hnormal hspineValid hsupport hobjectContext
    habstractContext
  exact
    executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_of_valid_normal_runtimeSpine_support_context_fuel_ge_size
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet leftInitialSpine rightInitialSpine
      variableValues hschema (SelectionSet.size selectionSet + 1)
      normalParentType variableDefinitions selectionSet fuel runtimeType
      targetParent leftField rightField leftArguments rightArguments
      leftRuntime rightRuntime tag currentSelectionSet spine (by omega)
      hfuel hvalid hfree hnormal hspineValid hsupport hobjectContext
      habstractContext

theorem
    executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_left_argument_target_child_of_valid_normal_field_mem
    (schema : Schema) (rootSelectionSet rightInitialSelectionSet : List Selection)
    (rightInitialSpine : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ∀ parentType variableDefinitions (selectionSet : List Selection)
            fuel responseName fieldName runtimeType
            (leftArguments rightArguments arguments : List Argument)
            (directives : List DirectiveApplication)
            (childSelectionSet : List Selection)
            (fieldDefinition : FieldDefinition)
            (spine : List NormalSelectionSetObservableFieldStep),
          Validation.selectionSetValid schema variableDefinitions parentType selectionSet
          -> selectionSetDirectiveFree selectionSet
          -> selectionSetNormal schema parentType selectionSet
          -> objectTypeNameBool schema parentType = true
          -> Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ selectionSet
          -> Argument.argumentsEquivalent arguments leftArguments
          -> schema.lookupField parentType fieldName = some fieldDefinition
          -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
              = true
          -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType
                runtimeType
              = true
          -> SelectedFieldSpineRuntimeValid schema
              fieldDefinition.outputType.namedType runtimeType spine
          -> selectionSetDeepProbeFuel schema
                fieldDefinition.outputType.namedType childSelectionSet
              ≤ fuel
          -> ∃ responseFields errors,
              Execution.executeSelectionSetAsResponse schema
                (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                  (fieldPairSelectedPathProbeResolvers schema
                    (fieldPairPathLocalNextSelectionSet schema parentType
                      runtimeType fieldName leftArguments selectionSet)
                    rightInitialSelectionSet spine rightInitialSpine parentType
                    fieldName fieldName leftArguments rightArguments
                    runtimeType runtimeType)
                  parentType fieldName fieldName leftArguments rightArguments)
                variableValues (fuel + 1) runtimeType
                (projectionTargetResolverValue
                  (.object runtimeType
                    (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
                      (fieldPairPathLocalNextSelectionSet schema parentType
                        runtimeType fieldName leftArguments selectionSet)
                      spine)))
                childSelectionSet
              = ({
                    data := Execution.ResponseValue.object responseFields,
                    errors := errors
                  }
                  : Execution.Response) := by
  intro hschema parentType variableDefinitions selectionSet fuel
    responseName fieldName runtimeType leftArguments rightArguments
    arguments directives childSelectionSet fieldDefinition spine hvalid
    hfree hnormal hobject hmem harguments hlookup hcomposite hinclude
    hspineValid hfuel
  rcases selectionSetValid_field_lookup_leaf_or_composite_child hvalid hmem with
    ⟨candidateDefinition, hcandidateLookup, hkind⟩
  have hdefinitionEq : candidateDefinition = fieldDefinition := by
    rw [hlookup] at hcandidateLookup
    exact (Option.some.inj hcandidateLookup).symm
  subst candidateDefinition
  rcases hkind with hleaf | hcompositeKind
  · have hleafComposite := hleaf.1
    rw [hcomposite] at hleafComposite
    simp at hleafComposite
  · have hchildValid :
        Validation.selectionSetValid schema variableDefinitions
          fieldDefinition.outputType.namedType childSelectionSet :=
      hcompositeKind.2.2
    have hchildFree : selectionSetDirectiveFree childSelectionSet :=
      selectionSetDirectiveFree_field_child_of_mem hfree hmem
    have hchildNormal :
        selectionSetNormal schema fieldDefinition.outputType.namedType
          childSelectionSet :=
      selectionSetNormal_field_child_of_mem_lookup hnormal hmem hlookup
    have hchildObject : objectTypeNameBool schema runtimeType = true :=
      objectTypeNameBool_of_typeIncludesObjectBool hschema hinclude
    have hparentSupport :
        PathLocalSupportValidNormal schema parentType selectionSet :=
      PathLocalSupportValidNormal.of_valid_normal_self hvalid hfree hnormal
    have hchildSupport :
        PathLocalSupportValidNormal schema runtimeType
          (fieldPairPathLocalNextSelectionSet schema parentType runtimeType
            fieldName leftArguments selectionSet) :=
      hparentSupport.fieldPairPathLocalNextSelectionSet_of_abstract_output
        hobject hchildObject hlookup hcomposite hinclude
    have hobjectContext :
        objectTypeNameBool schema fieldDefinition.outputType.namedType = true ->
          PathLocalSelectionSetCurrentContext childSelectionSet
            (fieldPairPathLocalNextSelectionSet schema parentType
              runtimeType fieldName leftArguments selectionSet) := by
      intro hreturnObject
      have hruntimeEq : runtimeType = fieldDefinition.outputType.namedType :=
        typeIncludesObjectBool_eq_of_objectTypeNameBool_true schema
          hreturnObject hinclude
      subst runtimeType
      have hallFields : selectionsAllFields childSelectionSet :=
        selectionSetNormal_allFields_of_object hchildNormal hreturnObject
      have hpruned :
          runtimePrunedSelectionSet schema
              fieldDefinition.outputType.namedType childSelectionSet =
            childSelectionSet :=
        runtimePrunedSelectionSet_eq_self_of_allFields schema
          fieldDefinition.outputType.namedType hallFields
      exact
        PathLocalSelectionSetCurrentContext.fieldPairPathLocalNextSelectionSet_field_child
          (schema := schema) (currentRuntimeType := parentType)
          (childRuntimeType := fieldDefinition.outputType.namedType)
          (targetField := fieldName) (responseName := responseName)
          (targetArguments := leftArguments) (arguments := arguments)
          (directives := directives) (selectionSet := selectionSet)
          (childSelectionSet := childSelectionSet)
          (currentSelectionSet := selectionSet)
          PathLocalSelectionSetCurrentContext.self hmem harguments hpruned
    have habstractContext :
        objectTypeNameBool schema fieldDefinition.outputType.namedType = false ->
          ∀ {bodyDirectives bodySelectionSet},
            Selection.inlineFragment (some runtimeType) bodyDirectives
              bodySelectionSet ∈ childSelectionSet ->
              PathLocalSelectionSetCurrentContext bodySelectionSet
                (fieldPairPathLocalNextSelectionSet schema parentType
                  runtimeType fieldName leftArguments selectionSet) := by
      intro _hreturnNonObject bodyDirectives bodySelectionSet hbodyMem
      exact
        PathLocalSelectionSetCurrentContext.fieldPairPathLocalNextSelectionSet_inlineFragment_body
          (schema := schema) (currentRuntimeType := parentType)
          (childRuntimeType := runtimeType)
          (childParentType := fieldDefinition.outputType.namedType)
          (targetField := fieldName) (responseName := responseName)
          (targetArguments := leftArguments) (arguments := arguments)
          (directives := directives) (bodyDirectives := bodyDirectives)
          (selectionSet := selectionSet) (childSelectionSet := childSelectionSet)
          (bodySelectionSet := bodySelectionSet)
          (currentSelectionSet := selectionSet)
          PathLocalSelectionSetCurrentContext.self hmem hbodyMem
          harguments hchildNormal hchildObject
    exact
      executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_of_valid_normal_runtimeSpine_support_context_fuel_ge
        schema rootSelectionSet
        (fieldPairPathLocalNextSelectionSet schema parentType runtimeType
          fieldName leftArguments selectionSet)
        rightInitialSelectionSet spine rightInitialSpine variableValues
        hschema fieldDefinition.outputType.namedType variableDefinitions
        childSelectionSet fuel runtimeType parentType fieldName fieldName
        leftArguments rightArguments runtimeType runtimeType
        FieldPairProbeTag.left
        (fieldPairPathLocalNextSelectionSet schema parentType runtimeType
          fieldName leftArguments selectionSet)
        spine hfuel hchildValid hchildFree hchildNormal hspineValid
        hchildSupport hobjectContext habstractContext

theorem
    executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_right_argument_target_child_of_valid_normal_field_mem
    (schema : Schema) (rootSelectionSet leftInitialSelectionSet : List Selection)
    (leftInitialSpine : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ∀ parentType variableDefinitions (selectionSet : List Selection)
            fuel responseName fieldName runtimeType
            (leftArguments rightArguments arguments : List Argument)
            (directives : List DirectiveApplication)
            (childSelectionSet : List Selection)
            (fieldDefinition : FieldDefinition)
            (spine : List NormalSelectionSetObservableFieldStep),
          Validation.selectionSetValid schema variableDefinitions parentType selectionSet
          -> selectionSetDirectiveFree selectionSet
          -> selectionSetNormal schema parentType selectionSet
          -> objectTypeNameBool schema parentType = true
          -> Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ selectionSet
          -> Argument.argumentsEquivalent arguments rightArguments
          -> schema.lookupField parentType fieldName = some fieldDefinition
          -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
              = true
          -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType
                runtimeType
              = true
          -> SelectedFieldSpineRuntimeValid schema
              fieldDefinition.outputType.namedType runtimeType spine
          -> selectionSetDeepProbeFuel schema
                fieldDefinition.outputType.namedType childSelectionSet
              ≤ fuel
          -> ∃ responseFields errors,
              Execution.executeSelectionSetAsResponse schema
                (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                  (fieldPairSelectedPathProbeResolvers schema
                    leftInitialSelectionSet
                    (fieldPairPathLocalNextSelectionSet schema parentType
                      runtimeType fieldName rightArguments selectionSet)
                    leftInitialSpine spine parentType fieldName fieldName
                    leftArguments rightArguments runtimeType runtimeType)
                  parentType fieldName fieldName leftArguments rightArguments)
                variableValues (fuel + 1) runtimeType
                (projectionTargetResolverValue
                  (.object runtimeType
                    (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                      (fieldPairPathLocalNextSelectionSet schema parentType
                        runtimeType fieldName rightArguments selectionSet)
                      spine)))
                childSelectionSet
              = ({
                    data := Execution.ResponseValue.object responseFields,
                    errors := errors
                  }
                  : Execution.Response) := by
  intro hschema parentType variableDefinitions selectionSet fuel
    responseName fieldName runtimeType leftArguments rightArguments
    arguments directives childSelectionSet fieldDefinition spine hvalid
    hfree hnormal hobject hmem harguments hlookup hcomposite hinclude
    hspineValid hfuel
  rcases selectionSetValid_field_lookup_leaf_or_composite_child hvalid hmem with
    ⟨candidateDefinition, hcandidateLookup, hkind⟩
  have hdefinitionEq : candidateDefinition = fieldDefinition := by
    rw [hlookup] at hcandidateLookup
    exact (Option.some.inj hcandidateLookup).symm
  subst candidateDefinition
  rcases hkind with hleaf | hcompositeKind
  · have hleafComposite := hleaf.1
    rw [hcomposite] at hleafComposite
    simp at hleafComposite
  · have hchildValid :
        Validation.selectionSetValid schema variableDefinitions
          fieldDefinition.outputType.namedType childSelectionSet :=
      hcompositeKind.2.2
    have hchildFree : selectionSetDirectiveFree childSelectionSet :=
      selectionSetDirectiveFree_field_child_of_mem hfree hmem
    have hchildNormal :
        selectionSetNormal schema fieldDefinition.outputType.namedType
          childSelectionSet :=
      selectionSetNormal_field_child_of_mem_lookup hnormal hmem hlookup
    have hchildObject : objectTypeNameBool schema runtimeType = true :=
      objectTypeNameBool_of_typeIncludesObjectBool hschema hinclude
    have hparentSupport :
        PathLocalSupportValidNormal schema parentType selectionSet :=
      PathLocalSupportValidNormal.of_valid_normal_self hvalid hfree hnormal
    have hchildSupport :
        PathLocalSupportValidNormal schema runtimeType
          (fieldPairPathLocalNextSelectionSet schema parentType runtimeType
            fieldName rightArguments selectionSet) :=
      hparentSupport.fieldPairPathLocalNextSelectionSet_of_abstract_output
        hobject hchildObject hlookup hcomposite hinclude
    have hobjectContext :
        objectTypeNameBool schema fieldDefinition.outputType.namedType = true ->
          PathLocalSelectionSetCurrentContext childSelectionSet
            (fieldPairPathLocalNextSelectionSet schema parentType
              runtimeType fieldName rightArguments selectionSet) := by
      intro hreturnObject
      have hruntimeEq : runtimeType = fieldDefinition.outputType.namedType :=
        typeIncludesObjectBool_eq_of_objectTypeNameBool_true schema
          hreturnObject hinclude
      subst runtimeType
      have hallFields : selectionsAllFields childSelectionSet :=
        selectionSetNormal_allFields_of_object hchildNormal hreturnObject
      have hpruned :
          runtimePrunedSelectionSet schema
              fieldDefinition.outputType.namedType childSelectionSet =
            childSelectionSet :=
        runtimePrunedSelectionSet_eq_self_of_allFields schema
          fieldDefinition.outputType.namedType hallFields
      exact
        PathLocalSelectionSetCurrentContext.fieldPairPathLocalNextSelectionSet_field_child
          (schema := schema) (currentRuntimeType := parentType)
          (childRuntimeType := fieldDefinition.outputType.namedType)
          (targetField := fieldName) (responseName := responseName)
          (targetArguments := rightArguments) (arguments := arguments)
          (directives := directives) (selectionSet := selectionSet)
          (childSelectionSet := childSelectionSet)
          (currentSelectionSet := selectionSet)
          PathLocalSelectionSetCurrentContext.self hmem harguments hpruned
    have habstractContext :
        objectTypeNameBool schema fieldDefinition.outputType.namedType = false ->
          ∀ {bodyDirectives bodySelectionSet},
            Selection.inlineFragment (some runtimeType) bodyDirectives
              bodySelectionSet ∈ childSelectionSet ->
              PathLocalSelectionSetCurrentContext bodySelectionSet
                (fieldPairPathLocalNextSelectionSet schema parentType
                  runtimeType fieldName rightArguments selectionSet) := by
      intro _hreturnNonObject bodyDirectives bodySelectionSet hbodyMem
      exact
        PathLocalSelectionSetCurrentContext.fieldPairPathLocalNextSelectionSet_inlineFragment_body
          (schema := schema) (currentRuntimeType := parentType)
          (childRuntimeType := runtimeType)
          (childParentType := fieldDefinition.outputType.namedType)
          (targetField := fieldName) (responseName := responseName)
          (targetArguments := rightArguments) (arguments := arguments)
          (directives := directives) (bodyDirectives := bodyDirectives)
          (selectionSet := selectionSet) (childSelectionSet := childSelectionSet)
          (bodySelectionSet := bodySelectionSet)
          (currentSelectionSet := selectionSet)
          PathLocalSelectionSetCurrentContext.self hmem hbodyMem
          harguments hchildNormal hchildObject
    exact
      executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_of_valid_normal_runtimeSpine_support_context_fuel_ge
        schema rootSelectionSet leftInitialSelectionSet
        (fieldPairPathLocalNextSelectionSet schema parentType runtimeType
          fieldName rightArguments selectionSet)
        leftInitialSpine spine variableValues hschema
        fieldDefinition.outputType.namedType variableDefinitions
        childSelectionSet fuel runtimeType parentType fieldName fieldName
        leftArguments rightArguments runtimeType runtimeType
        FieldPairProbeTag.right
        (fieldPairPathLocalNextSelectionSet schema parentType runtimeType
          fieldName rightArguments selectionSet)
        spine hfuel hchildValid hchildFree hchildNormal hspineValid
        hchildSupport hobjectContext habstractContext

theorem
    executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_argument_target_child_of_valid_normal_support_context_field_mem
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ∀ parentType variableDefinitions
            (selectionSet currentSelectionSet : List Selection) fuel responseName
            fieldName runtimeType
            (targetArguments leftArguments rightArguments arguments : List Argument)
            (directives : List DirectiveApplication)
            (childSelectionSet : List Selection) (fieldDefinition : FieldDefinition)
            (spine : List NormalSelectionSetObservableFieldStep)
            (tag : FieldPairProbeTag),
          Validation.selectionSetValid schema variableDefinitions parentType selectionSet
          -> selectionSetDirectiveFree selectionSet
          -> selectionSetNormal schema parentType selectionSet
          -> objectTypeNameBool schema parentType = true
          -> PathLocalSupportValidNormal schema parentType currentSelectionSet
          -> PathLocalSelectionSetCurrentContext selectionSet currentSelectionSet
          -> Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ selectionSet
          -> Argument.argumentsEquivalent arguments targetArguments
          -> schema.lookupField parentType fieldName = some fieldDefinition
          -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
              = true
          -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType
                runtimeType
              = true
          -> SelectedFieldSpineRuntimeValid schema
              fieldDefinition.outputType.namedType runtimeType spine
          -> selectionSetDeepProbeFuel schema
                fieldDefinition.outputType.namedType childSelectionSet
              ≤ fuel
          -> ∃ responseFields errors,
              Execution.executeSelectionSetAsResponse schema
                (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                  (fieldPairSelectedPathProbeResolvers schema
                    leftInitialSelectionSet rightInitialSelectionSet
                    leftInitialSpine rightInitialSpine parentType fieldName
                    fieldName leftArguments rightArguments runtimeType
                    runtimeType)
                  parentType fieldName fieldName leftArguments rightArguments)
                variableValues (fuel + 1) runtimeType
                (projectionTargetResolverValue
                  (.object runtimeType
                    (FieldPairSelectedPathProbeRef.target tag
                      (fieldPairPathLocalNextSelectionSet schema parentType
                        runtimeType fieldName targetArguments currentSelectionSet)
                      spine)))
                childSelectionSet
              = ({
                    data := Execution.ResponseValue.object responseFields,
                    errors := errors
                  }
                  : Execution.Response) := by
  intro hschema parentType variableDefinitions selectionSet
    currentSelectionSet fuel responseName fieldName runtimeType
    targetArguments leftArguments rightArguments arguments directives
    childSelectionSet fieldDefinition spine tag hvalid hfree hnormal hobject
    hsupport hcontext hmem harguments hlookup hcomposite hinclude
    hspineValid hfuel
  rcases selectionSetValid_field_lookup_leaf_or_composite_child hvalid hmem with
    ⟨candidateDefinition, hcandidateLookup, hkind⟩
  have hdefinitionEq : candidateDefinition = fieldDefinition := by
    rw [hlookup] at hcandidateLookup
    exact (Option.some.inj hcandidateLookup).symm
  subst candidateDefinition
  rcases hkind with hleaf | hcompositeKind
  · have hleafComposite := hleaf.1
    rw [hcomposite] at hleafComposite
    simp at hleafComposite
  · have hchildValid :
        Validation.selectionSetValid schema variableDefinitions
          fieldDefinition.outputType.namedType childSelectionSet :=
      hcompositeKind.2.2
    have hchildFree : selectionSetDirectiveFree childSelectionSet :=
      selectionSetDirectiveFree_field_child_of_mem hfree hmem
    have hchildNormal :
        selectionSetNormal schema fieldDefinition.outputType.namedType
          childSelectionSet :=
      selectionSetNormal_field_child_of_mem_lookup hnormal hmem hlookup
    have hchildObject : objectTypeNameBool schema runtimeType = true :=
      objectTypeNameBool_of_typeIncludesObjectBool hschema hinclude
    have hchildSupport :
        PathLocalSupportValidNormal schema runtimeType
          (fieldPairPathLocalNextSelectionSet schema parentType runtimeType
            fieldName targetArguments currentSelectionSet) :=
      hsupport.fieldPairPathLocalNextSelectionSet_of_abstract_output
        hobject hchildObject hlookup hcomposite hinclude
    have hobjectContext :
        objectTypeNameBool schema fieldDefinition.outputType.namedType = true ->
          PathLocalSelectionSetCurrentContext childSelectionSet
            (fieldPairPathLocalNextSelectionSet schema parentType
              runtimeType fieldName targetArguments currentSelectionSet) := by
      intro hreturnObject
      have hruntimeEq : runtimeType = fieldDefinition.outputType.namedType :=
        typeIncludesObjectBool_eq_of_objectTypeNameBool_true schema
          hreturnObject hinclude
      subst runtimeType
      have hallFields : selectionsAllFields childSelectionSet :=
        selectionSetNormal_allFields_of_object hchildNormal hreturnObject
      have hpruned :
          runtimePrunedSelectionSet schema
              fieldDefinition.outputType.namedType childSelectionSet =
            childSelectionSet :=
        runtimePrunedSelectionSet_eq_self_of_allFields schema
          fieldDefinition.outputType.namedType hallFields
      exact
        PathLocalSelectionSetCurrentContext.fieldPairPathLocalNextSelectionSet_field_child
          (schema := schema) (currentRuntimeType := parentType)
          (childRuntimeType := fieldDefinition.outputType.namedType)
          (targetField := fieldName) (responseName := responseName)
          (targetArguments := targetArguments) (arguments := arguments)
          (directives := directives) (selectionSet := selectionSet)
          (childSelectionSet := childSelectionSet)
          (currentSelectionSet := currentSelectionSet) hcontext hmem
          harguments hpruned
    have habstractContext :
        objectTypeNameBool schema fieldDefinition.outputType.namedType = false ->
          ∀ {bodyDirectives bodySelectionSet},
            Selection.inlineFragment (some runtimeType) bodyDirectives
              bodySelectionSet ∈ childSelectionSet ->
              PathLocalSelectionSetCurrentContext bodySelectionSet
                (fieldPairPathLocalNextSelectionSet schema parentType
                  runtimeType fieldName targetArguments currentSelectionSet) := by
      intro _hreturnNonObject bodyDirectives bodySelectionSet hbodyMem
      exact
        PathLocalSelectionSetCurrentContext.fieldPairPathLocalNextSelectionSet_inlineFragment_body
          (schema := schema) (currentRuntimeType := parentType)
          (childRuntimeType := runtimeType)
          (childParentType := fieldDefinition.outputType.namedType)
          (targetField := fieldName) (responseName := responseName)
          (targetArguments := targetArguments) (arguments := arguments)
          (directives := directives) (bodyDirectives := bodyDirectives)
          (selectionSet := selectionSet) (childSelectionSet := childSelectionSet)
          (bodySelectionSet := bodySelectionSet)
          (currentSelectionSet := currentSelectionSet) hcontext hmem hbodyMem
          harguments hchildNormal hchildObject
    exact
      executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_of_valid_normal_runtimeSpine_support_context_fuel_ge
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftInitialSpine rightInitialSpine
        variableValues hschema fieldDefinition.outputType.namedType
        variableDefinitions childSelectionSet fuel runtimeType parentType
        fieldName fieldName leftArguments rightArguments runtimeType
        runtimeType tag
        (fieldPairPathLocalNextSelectionSet schema parentType runtimeType
          fieldName targetArguments currentSelectionSet)
        spine hfuel hchildValid hchildFree hchildNormal hspineValid
        hchildSupport hobjectContext habstractContext

theorem
    executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_target_child_of_valid_normal_support_context_field_mem
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ∀ parentType variableDefinitions
            (selectionSet currentSelectionSet : List Selection) fuel responseName
            fieldName runtimeType targetParent leftField rightField
            (targetArguments leftArguments rightArguments arguments : List Argument)
            (directives : List DirectiveApplication)
            (childSelectionSet : List Selection) (fieldDefinition : FieldDefinition)
            (leftRuntime rightRuntime : Name)
            (spine : List NormalSelectionSetObservableFieldStep)
            (tag : FieldPairProbeTag),
          Validation.selectionSetValid schema variableDefinitions parentType selectionSet
          -> selectionSetDirectiveFree selectionSet
          -> selectionSetNormal schema parentType selectionSet
          -> objectTypeNameBool schema parentType = true
          -> PathLocalSupportValidNormal schema parentType currentSelectionSet
          -> PathLocalSelectionSetCurrentContext selectionSet currentSelectionSet
          -> Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ selectionSet
          -> Argument.argumentsEquivalent arguments targetArguments
          -> schema.lookupField parentType fieldName = some fieldDefinition
          -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
              = true
          -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType
                runtimeType
              = true
          -> SelectedFieldSpineRuntimeValid schema
              fieldDefinition.outputType.namedType runtimeType spine
          -> selectionSetDeepProbeFuel schema
                fieldDefinition.outputType.namedType childSelectionSet
              ≤ fuel
          -> ∃ responseFields errors,
              Execution.executeSelectionSetAsResponse schema
                (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                  (fieldPairSelectedPathProbeResolvers schema
                    leftInitialSelectionSet rightInitialSelectionSet
                    leftInitialSpine rightInitialSpine targetParent leftField
                    rightField leftArguments rightArguments leftRuntime
                    rightRuntime)
                  targetParent leftField rightField leftArguments
                  rightArguments)
                variableValues (fuel + 1) runtimeType
                (projectionTargetResolverValue
                  (.object runtimeType
                    (FieldPairSelectedPathProbeRef.target tag
                      (fieldPairPathLocalNextSelectionSet schema parentType
                        runtimeType fieldName targetArguments
                        currentSelectionSet)
                      spine)))
                childSelectionSet
              = ({
                    data := Execution.ResponseValue.object responseFields,
                    errors := errors
                  }
                  : Execution.Response) := by
  intro hschema parentType variableDefinitions selectionSet
    currentSelectionSet fuel responseName fieldName runtimeType
    targetParent leftField rightField targetArguments leftArguments
    rightArguments arguments directives childSelectionSet fieldDefinition
    leftRuntime rightRuntime spine tag hvalid hfree hnormal hobject
    hsupport hcontext hmem harguments hlookup hcomposite hinclude
    hspineValid hfuel
  rcases selectionSetValid_field_lookup_leaf_or_composite_child hvalid hmem with
    ⟨candidateDefinition, hcandidateLookup, hkind⟩
  have hdefinitionEq : candidateDefinition = fieldDefinition := by
    rw [hlookup] at hcandidateLookup
    exact (Option.some.inj hcandidateLookup).symm
  subst candidateDefinition
  rcases hkind with hleaf | hcompositeKind
  · have hleafComposite := hleaf.1
    rw [hcomposite] at hleafComposite
    simp at hleafComposite
  · have hchildValid :
        Validation.selectionSetValid schema variableDefinitions
          fieldDefinition.outputType.namedType childSelectionSet :=
      hcompositeKind.2.2
    have hchildFree : selectionSetDirectiveFree childSelectionSet :=
      selectionSetDirectiveFree_field_child_of_mem hfree hmem
    have hchildNormal :
        selectionSetNormal schema fieldDefinition.outputType.namedType
          childSelectionSet :=
      selectionSetNormal_field_child_of_mem_lookup hnormal hmem hlookup
    have hchildObject : objectTypeNameBool schema runtimeType = true :=
      objectTypeNameBool_of_typeIncludesObjectBool hschema hinclude
    have hchildSupport :
        PathLocalSupportValidNormal schema runtimeType
          (fieldPairPathLocalNextSelectionSet schema parentType runtimeType
            fieldName targetArguments currentSelectionSet) :=
      hsupport.fieldPairPathLocalNextSelectionSet_of_abstract_output
        hobject hchildObject hlookup hcomposite hinclude
    have hobjectContext :
        objectTypeNameBool schema fieldDefinition.outputType.namedType = true ->
          PathLocalSelectionSetCurrentContext childSelectionSet
            (fieldPairPathLocalNextSelectionSet schema parentType
              runtimeType fieldName targetArguments currentSelectionSet) := by
      intro hreturnObject
      have hruntimeEq : runtimeType = fieldDefinition.outputType.namedType :=
        typeIncludesObjectBool_eq_of_objectTypeNameBool_true schema
          hreturnObject hinclude
      subst runtimeType
      have hallFields : selectionsAllFields childSelectionSet :=
        selectionSetNormal_allFields_of_object hchildNormal hreturnObject
      have hpruned :
          runtimePrunedSelectionSet schema
              fieldDefinition.outputType.namedType childSelectionSet =
            childSelectionSet :=
        runtimePrunedSelectionSet_eq_self_of_allFields schema
          fieldDefinition.outputType.namedType hallFields
      exact
        PathLocalSelectionSetCurrentContext.fieldPairPathLocalNextSelectionSet_field_child
          (schema := schema) (currentRuntimeType := parentType)
          (childRuntimeType := fieldDefinition.outputType.namedType)
          (targetField := fieldName) (responseName := responseName)
          (targetArguments := targetArguments) (arguments := arguments)
          (directives := directives) (selectionSet := selectionSet)
          (childSelectionSet := childSelectionSet)
          (currentSelectionSet := currentSelectionSet) hcontext hmem
          harguments hpruned
    have habstractContext :
        objectTypeNameBool schema fieldDefinition.outputType.namedType = false ->
          ∀ {bodyDirectives bodySelectionSet},
            Selection.inlineFragment (some runtimeType) bodyDirectives
              bodySelectionSet ∈ childSelectionSet ->
              PathLocalSelectionSetCurrentContext bodySelectionSet
                (fieldPairPathLocalNextSelectionSet schema parentType
                  runtimeType fieldName targetArguments
                  currentSelectionSet) := by
      intro _hreturnNonObject bodyDirectives bodySelectionSet hbodyMem
      exact
        PathLocalSelectionSetCurrentContext.fieldPairPathLocalNextSelectionSet_inlineFragment_body
          (schema := schema) (currentRuntimeType := parentType)
          (childRuntimeType := runtimeType)
          (childParentType := fieldDefinition.outputType.namedType)
          (targetField := fieldName) (responseName := responseName)
          (targetArguments := targetArguments) (arguments := arguments)
          (directives := directives) (bodyDirectives := bodyDirectives)
          (selectionSet := selectionSet) (childSelectionSet := childSelectionSet)
          (bodySelectionSet := bodySelectionSet)
          (currentSelectionSet := currentSelectionSet) hcontext hmem hbodyMem
          harguments hchildNormal hchildObject
    exact
      executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_of_valid_normal_runtimeSpine_support_context_fuel_ge
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftInitialSpine rightInitialSpine
        variableValues hschema fieldDefinition.outputType.namedType
        variableDefinitions childSelectionSet fuel runtimeType targetParent
        leftField rightField leftArguments rightArguments leftRuntime
        rightRuntime tag
        (fieldPairPathLocalNextSelectionSet schema parentType runtimeType
          fieldName targetArguments currentSelectionSet)
        spine hfuel hchildValid hchildFree hchildNormal hspineValid
        hchildSupport hobjectContext habstractContext

end GroundTypeNormalization

end NormalForm

end GraphQL
