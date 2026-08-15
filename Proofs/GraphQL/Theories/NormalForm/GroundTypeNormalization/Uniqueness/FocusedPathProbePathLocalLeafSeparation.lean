import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.FocusedPathProbePathLocalExecution

/-!
Leaf and response-name separation through path-local focused probes.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_leaf_field_of_field_children
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet currentSelectionSet
      : List Selection)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField parentType sourceRuntimeType : Name)
    (leftArguments rightArguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime : Name) {selectionSet : List Selection}
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
                ∧ (Execution.coerceArgumentValues schema variableValues
                    fieldDefinition.arguments arguments).isSuccess
                  = true
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
                                ∧ abstractRuntimeForFieldDeep? schema parentType
                                    fieldName parentType currentSelectionSet
                                  = some childRuntimeType))
                          ∧ schema.typeIncludesObjectBool
                              fieldDefinition.outputType.namedType childRuntimeType
                            = true
                          ∧ Execution.executeSelectionSetAsResponse schema
                              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                                (fieldPairPathLocalProbeResolvers schema
                                  leftInitialSelectionSet rightInitialSelectionSet
                                  targetParent leftField rightField leftArguments
                                  rightArguments leftRuntime rightRuntime)
                                targetParent leftField rightField leftArguments
                                rightArguments)
                              variableValues
                              (fuel - leafProbeFuel fieldDefinition.outputType)
                              childRuntimeType
                              (projectionTargetResolverValue
                                (.object childRuntimeType
                                  (FieldPairPathLocalProbeRef.target
                                    FieldPairProbeTag.left
                                    (fieldPairPathLocalNextSelectionSet schema
                                      parentType childRuntimeType fieldName
                                      arguments currentSelectionSet))))
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
                ∧ (Execution.coerceArgumentValues schema variableValues
                    fieldDefinition.arguments arguments).isSuccess
                  = true
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
                                ∧ abstractRuntimeForFieldDeep? schema parentType
                                    fieldName parentType currentSelectionSet
                                  = some childRuntimeType))
                          ∧ schema.typeIncludesObjectBool
                              fieldDefinition.outputType.namedType childRuntimeType
                            = true
                          ∧ Execution.executeSelectionSetAsResponse schema
                              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                                (fieldPairPathLocalProbeResolvers schema
                                  leftInitialSelectionSet rightInitialSelectionSet
                                  targetParent leftField rightField leftArguments
                                  rightArguments leftRuntime rightRuntime)
                                targetParent leftField rightField leftArguments
                                rightArguments)
                              variableValues
                              (fuel - leafProbeFuel fieldDefinition.outputType)
                              childRuntimeType
                              (projectionTargetResolverValue
                                (.object childRuntimeType
                                  (FieldPairPathLocalProbeRef.target
                                    FieldPairProbeTag.right
                                    (fieldPairPathLocalNextSelectionSet schema
                                      parentType childRuntimeType fieldName
                                      arguments currentSelectionSet))))
                              childSelectionSet
                            = ({
                                  data := Execution.ResponseValue.object responseFields,
                                  errors := childErrors
                                }
                                : Execution.Response))))
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
  intro hfree hnormal hobject hmem hlookup hfuel hleaf hleftChildren
    hrightChildren
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
  have hleftFieldOk :
      ∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
            childSelectionSet ∈ selectionSet ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema resolvers variableValues
              (fuel + 1) leftSource responseName
              [{
                parentType := parentType
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
        rightInitialSelectionSet currentSelectionSet variableValues fuel
        targetParent leftField rightField parentType sourceRuntimeType
        leftArguments rightArguments leftRuntime rightRuntime
        FieldPairProbeTag.left selectionSet hleftChildren
  have hrightFieldOk :
      ∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
            childSelectionSet ∈ selectionSet ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema resolvers variableValues
              (fuel + 1) rightSource responseName
              [{
                parentType := parentType
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
        rightInitialSelectionSet currentSelectionSet variableValues fuel
        targetParent leftField rightField parentType sourceRuntimeType
        leftArguments rightArguments leftRuntime rightRuntime
        FieldPairProbeTag.right selectionSet hrightChildren
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
      executeField_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_leaf
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet currentSelectionSet variableValues fuel
        targetParent leftField rightField parentType fieldName
        sourceRuntimeType responseName leftArguments rightArguments
        arguments leftRuntime rightRuntime FieldPairProbeTag.left
        childSelectionSet fieldDefinition hlookup
        (PathLocalSelectionSetFieldChildrenReady.argumentCoercion_of_mem_lookup
          hleftChildren hmem hlookup) hfuel hleaf
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
      executeField_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_leaf
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet currentSelectionSet variableValues fuel
        targetParent leftField rightField parentType fieldName
        sourceRuntimeType responseName leftArguments rightArguments
        arguments leftRuntime rightRuntime FieldPairProbeTag.right
        childSelectionSet fieldDefinition hlookup
        (PathLocalSelectionSetFieldChildrenReady.argumentCoercion_of_mem_lookup
          hrightChildren hmem hlookup) hfuel hleaf
  exact
    SemanticSeparation.responseData_not_semanticEquivalent_of_field_value_diff_of_field_ok
      resolvers resolvers variableValues (fuel + 1) leftSource rightSource
      hobject hnormal hnormal hfree hfree hmem hmem hleftTarget
      hrightTarget
      (leafProbeResponseValue_not_semanticEquivalent_of_ne
        fieldDefinition.outputType (by simp [FieldPairProbeTag.scalar]))
      hleftFieldOk hrightFieldOk

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_leaf_field_pair_of_field_children
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
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
      -> leafProbeFuel leftFieldDefinition.outputType ≤ fuel
      -> leafProbeFuel rightFieldDefinition.outputType ≤ fuel
      -> (TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ left
            -> ∃ fieldDefinition,
                schema.lookupField leftParentType fieldName = some fieldDefinition
                ∧ (Execution.coerceArgumentValues schema variableValues
                    fieldDefinition.arguments arguments).isSuccess
                  = true
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
                                ∧ abstractRuntimeForFieldDeep? schema
                                    leftParentType fieldName leftParentType
                                    leftCurrentSelectionSet
                                  = some childRuntimeType))
                          ∧ schema.typeIncludesObjectBool
                              fieldDefinition.outputType.namedType childRuntimeType
                            = true
                          ∧ Execution.executeSelectionSetAsResponse schema
                              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                                (fieldPairPathLocalProbeResolvers schema
                                  leftInitialSelectionSet rightInitialSelectionSet
                                  targetParent leftProbeField rightProbeField
                                  targetLeftArguments targetRightArguments
                                  leftRuntime rightRuntime)
                                targetParent leftProbeField rightProbeField
                                targetLeftArguments targetRightArguments)
                              variableValues
                              (fuel - leafProbeFuel fieldDefinition.outputType)
                              childRuntimeType
                              (projectionTargetResolverValue
                                (.object childRuntimeType
                                  (FieldPairPathLocalProbeRef.target
                                    FieldPairProbeTag.left
                                    (fieldPairPathLocalNextSelectionSet schema
                                      leftParentType childRuntimeType fieldName
                                      arguments leftCurrentSelectionSet))))
                              childSelectionSet
                            = ({
                                  data := Execution.ResponseValue.object responseFields,
                                  errors := childErrors
                                }
                                : Execution.Response))))
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ right
            -> ∃ fieldDefinition,
                schema.lookupField rightParentType fieldName = some fieldDefinition
                ∧ (Execution.coerceArgumentValues schema variableValues
                    fieldDefinition.arguments arguments).isSuccess
                  = true
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
                                ∧ abstractRuntimeForFieldDeep? schema
                                    rightParentType fieldName rightParentType
                                    rightCurrentSelectionSet
                                  = some childRuntimeType))
                          ∧ schema.typeIncludesObjectBool
                              fieldDefinition.outputType.namedType childRuntimeType
                            = true
                          ∧ Execution.executeSelectionSetAsResponse schema
                              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                                (fieldPairPathLocalProbeResolvers schema
                                  leftInitialSelectionSet rightInitialSelectionSet
                                  targetParent leftProbeField rightProbeField
                                  targetLeftArguments targetRightArguments
                                  leftRuntime rightRuntime)
                                targetParent leftProbeField rightProbeField
                                targetLeftArguments targetRightArguments)
                              variableValues
                              (fuel - leafProbeFuel fieldDefinition.outputType)
                              childRuntimeType
                              (projectionTargetResolverValue
                                (.object childRuntimeType
                                  (FieldPairPathLocalProbeRef.target
                                    FieldPairProbeTag.right
                                    (fieldPairPathLocalNextSelectionSet schema
                                      rightParentType childRuntimeType fieldName
                                      arguments rightCurrentSelectionSet))))
                              childSelectionSet
                            = ({
                                  data := Execution.ResponseValue.object responseFields,
                                  errors := childErrors
                                }
                                : Execution.Response))))
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
    hrightObject hleftMem hrightMem hleftLookup hrightLookup hleftFuel
    hrightFuel hleftLeaf hrightLeaf hleftChildren hrightChildren
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
      executeField_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_leaf
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftCurrentSelectionSet variableValues fuel
        targetParent leftProbeField rightProbeField leftParentType
        leftFieldName leftSourceRuntimeType responseName targetLeftArguments
        targetRightArguments leftArguments leftRuntime rightRuntime
        FieldPairProbeTag.left leftChildSelectionSet leftFieldDefinition
        hleftLookup
        (PathLocalSelectionSetFieldChildrenReady.argumentCoercion_of_mem_lookup
          hleftChildren hleftMem hleftLookup)
        hleftFuel hleftLeaf
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
      executeField_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_leaf
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet rightCurrentSelectionSet variableValues fuel
        targetParent leftProbeField rightProbeField rightParentType
        rightFieldName rightSourceRuntimeType responseName targetLeftArguments
        targetRightArguments rightArguments leftRuntime rightRuntime
        FieldPairProbeTag.right rightChildSelectionSet rightFieldDefinition
        hrightLookup
        (PathLocalSelectionSetFieldChildrenReady.argumentCoercion_of_mem_lookup
          hrightChildren hrightMem hrightLookup)
        hrightFuel hrightLeaf
  exact
    SemanticSeparation.responseData_not_semanticEquivalent_of_field_value_diff_of_field_ok_pair
      resolvers resolvers variableValues (fuel + 1) leftSource rightSource
      hleftObject hrightObject hleftNormal hrightNormal hleftFree
      hrightFree hleftMem hrightMem hleftTarget hrightTarget
      (leafProbeResponseValue_not_semanticEquivalent_of_ne_any
        leftFieldDefinition.outputType rightFieldDefinition.outputType
        (by simp [FieldPairProbeTag.scalar]))
      hleftFieldOk hrightFieldOk

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_leaf_field_pair_of_field_children_fuels
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
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
      -> leafProbeFuel leftFieldDefinition.outputType ≤ leftFuel
      -> leafProbeFuel rightFieldDefinition.outputType ≤ rightFuel
      -> (TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ left
            -> ∃ fieldDefinition,
                schema.lookupField leftParentType fieldName = some fieldDefinition
                ∧ (Execution.coerceArgumentValues schema variableValues
                    fieldDefinition.arguments arguments).isSuccess
                  = true
                ∧ leafProbeFuel fieldDefinition.outputType ≤ leftFuel
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
                                ∧ abstractRuntimeForFieldDeep? schema
                                    leftParentType fieldName leftParentType
                                    leftCurrentSelectionSet
                                  = some childRuntimeType))
                          ∧ schema.typeIncludesObjectBool
                              fieldDefinition.outputType.namedType childRuntimeType
                            = true
                          ∧ Execution.executeSelectionSetAsResponse schema
                              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                                (fieldPairPathLocalProbeResolvers schema
                                  leftInitialSelectionSet rightInitialSelectionSet
                                  targetParent leftProbeField rightProbeField
                                  targetLeftArguments targetRightArguments
                                  leftRuntime rightRuntime)
                                targetParent leftProbeField rightProbeField
                                targetLeftArguments targetRightArguments)
                              variableValues
                              (leftFuel - leafProbeFuel fieldDefinition.outputType)
                              childRuntimeType
                              (projectionTargetResolverValue
                                (.object childRuntimeType
                                  (FieldPairPathLocalProbeRef.target
                                    FieldPairProbeTag.left
                                    (fieldPairPathLocalNextSelectionSet schema
                                      leftParentType childRuntimeType fieldName
                                      arguments leftCurrentSelectionSet))))
                              childSelectionSet
                            = ({
                                  data := Execution.ResponseValue.object responseFields,
                                  errors := childErrors
                                }
                                : Execution.Response))))
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ right
            -> ∃ fieldDefinition,
                schema.lookupField rightParentType fieldName = some fieldDefinition
                ∧ (Execution.coerceArgumentValues schema variableValues
                    fieldDefinition.arguments arguments).isSuccess
                  = true
                ∧ leafProbeFuel fieldDefinition.outputType ≤ rightFuel
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
                                ∧ abstractRuntimeForFieldDeep? schema
                                    rightParentType fieldName rightParentType
                                    rightCurrentSelectionSet
                                  = some childRuntimeType))
                          ∧ schema.typeIncludesObjectBool
                              fieldDefinition.outputType.namedType childRuntimeType
                            = true
                          ∧ Execution.executeSelectionSetAsResponse schema
                              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                                (fieldPairPathLocalProbeResolvers schema
                                  leftInitialSelectionSet rightInitialSelectionSet
                                  targetParent leftProbeField rightProbeField
                                  targetLeftArguments targetRightArguments
                                  leftRuntime rightRuntime)
                                targetParent leftProbeField rightProbeField
                                targetLeftArguments targetRightArguments)
                              variableValues
                              (rightFuel - leafProbeFuel fieldDefinition.outputType)
                              childRuntimeType
                              (projectionTargetResolverValue
                                (.object childRuntimeType
                                  (FieldPairPathLocalProbeRef.target
                                    FieldPairProbeTag.right
                                    (fieldPairPathLocalNextSelectionSet schema
                                      rightParentType childRuntimeType fieldName
                                      arguments rightCurrentSelectionSet))))
                              childSelectionSet
                            = ({
                                  data := Execution.ResponseValue.object responseFields,
                                  errors := childErrors
                                }
                                : Execution.Response))))
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
    hrightObject hleftMem hrightMem hleftLookup hrightLookup hleftFuel
    hrightFuel hleftLeaf hrightLeaf hleftChildren hrightChildren
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
      executeField_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_leaf
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftCurrentSelectionSet variableValues
        leftFuel targetParent leftProbeField rightProbeField leftParentType
        leftFieldName leftSourceRuntimeType responseName targetLeftArguments
        targetRightArguments leftArguments leftRuntime rightRuntime
        FieldPairProbeTag.left leftChildSelectionSet leftFieldDefinition
        hleftLookup
        (PathLocalSelectionSetFieldChildrenReady.argumentCoercion_of_mem_lookup
          hleftChildren hleftMem hleftLookup)
        hleftFuel hleftLeaf
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
      executeField_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_leaf
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet rightCurrentSelectionSet variableValues
        rightFuel targetParent leftProbeField rightProbeField rightParentType
        rightFieldName rightSourceRuntimeType responseName
        targetLeftArguments targetRightArguments rightArguments leftRuntime
        rightRuntime FieldPairProbeTag.right rightChildSelectionSet
        rightFieldDefinition hrightLookup
        (PathLocalSelectionSetFieldChildrenReady.argumentCoercion_of_mem_lookup
          hrightChildren hrightMem hrightLookup)
        hrightFuel hrightLeaf
  exact
    SemanticSeparation.responseData_not_semanticEquivalent_of_field_value_diff_of_field_ok_pair_fuels
      resolvers resolvers variableValues (leftFuel + 1) (rightFuel + 1)
      leftSource rightSource hleftObject hrightObject hleftNormal
      hrightNormal hleftFree hrightFree hleftMem hrightMem hleftTarget
      hrightTarget
      (leafProbeResponseValue_not_semanticEquivalent_of_ne_any
        leftFieldDefinition.outputType rightFieldDefinition.outputType
        (by simp [FieldPairProbeTag.scalar]))
      hleftFieldOk hrightFieldOk

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_left_leaf_right_composite_field_pair_of_field_children
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
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
      -> leafProbeFuel leftFieldDefinition.outputType ≤ fuel
      -> (TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ left
            -> ∃ fieldDefinition,
                schema.lookupField leftParentType fieldName = some fieldDefinition
                ∧ (Execution.coerceArgumentValues schema variableValues
                    fieldDefinition.arguments arguments).isSuccess
                  = true
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
                                ∧ abstractRuntimeForFieldDeep? schema
                                    leftParentType fieldName leftParentType
                                    leftCurrentSelectionSet
                                  = some childRuntimeType))
                          ∧ schema.typeIncludesObjectBool
                              fieldDefinition.outputType.namedType childRuntimeType
                            = true
                          ∧ Execution.executeSelectionSetAsResponse schema
                              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                                (fieldPairPathLocalProbeResolvers schema
                                  leftInitialSelectionSet rightInitialSelectionSet
                                  targetParent leftProbeField rightProbeField
                                  targetLeftArguments targetRightArguments
                                  leftRuntime rightRuntime)
                                targetParent leftProbeField rightProbeField
                                targetLeftArguments targetRightArguments)
                              variableValues
                              (fuel - leafProbeFuel fieldDefinition.outputType)
                              childRuntimeType
                              (projectionTargetResolverValue
                                (.object childRuntimeType
                                  (FieldPairPathLocalProbeRef.target
                                    FieldPairProbeTag.left
                                    (fieldPairPathLocalNextSelectionSet schema
                                      leftParentType childRuntimeType fieldName
                                      arguments leftCurrentSelectionSet))))
                              childSelectionSet
                            = ({
                                  data := Execution.ResponseValue.object responseFields,
                                  errors := childErrors
                                }
                                : Execution.Response))))
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ right
            -> ∃ fieldDefinition,
                schema.lookupField rightParentType fieldName = some fieldDefinition
                ∧ (Execution.coerceArgumentValues schema variableValues
                    fieldDefinition.arguments arguments).isSuccess
                  = true
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
                                ∧ abstractRuntimeForFieldDeep? schema
                                    rightParentType fieldName rightParentType
                                    rightCurrentSelectionSet
                                  = some childRuntimeType))
                          ∧ schema.typeIncludesObjectBool
                              fieldDefinition.outputType.namedType childRuntimeType
                            = true
                          ∧ Execution.executeSelectionSetAsResponse schema
                              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                                (fieldPairPathLocalProbeResolvers schema
                                  leftInitialSelectionSet rightInitialSelectionSet
                                  targetParent leftProbeField rightProbeField
                                  targetLeftArguments targetRightArguments
                                  leftRuntime rightRuntime)
                                targetParent leftProbeField rightProbeField
                                targetLeftArguments targetRightArguments)
                              variableValues
                              (fuel - leafProbeFuel fieldDefinition.outputType)
                              childRuntimeType
                              (projectionTargetResolverValue
                                (.object childRuntimeType
                                  (FieldPairPathLocalProbeRef.target
                                    FieldPairProbeTag.right
                                    (fieldPairPathLocalNextSelectionSet schema
                                      rightParentType childRuntimeType fieldName
                                      arguments rightCurrentSelectionSet))))
                              childSelectionSet
                            = ({
                                  data := Execution.ResponseValue.object responseFields,
                                  errors := childErrors
                                }
                                : Execution.Response))))
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
    hrightObject hleftMem hrightMem hleftLookup hrightLookup hleftFuel
    hleftLeaf hrightComposite hleftChildren hrightChildren
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
      executeField_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_leaf
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftCurrentSelectionSet variableValues fuel
        targetParent leftProbeField rightProbeField leftParentType
        leftFieldName leftSourceRuntimeType responseName targetLeftArguments
        targetRightArguments leftArguments leftRuntime rightRuntime
        FieldPairProbeTag.left leftChildSelectionSet leftFieldDefinition
        hleftLookup
        (PathLocalSelectionSetFieldChildrenReady.argumentCoercion_of_mem_lookup
          hleftChildren hleftMem hleftLookup)
        hleftFuel hleftLeaf
  rcases
      hrightChildren responseName rightFieldName rightArguments
        rightDirectives rightChildSelectionSet hrightMem with
    ⟨rightFieldDefinition', hrightLookup', _hrightCoercion, hrightFuel,
      hrightKind⟩
  have hrightDefinitionEq :
      rightFieldDefinition' = rightFieldDefinition := by
    rw [hrightLookup] at hrightLookup'
    exact Option.some.inj hrightLookup'.symm
  subst rightFieldDefinition'
  rcases hrightKind with hrightLeaf | hrightChild
  · rw [hrightComposite] at hrightLeaf
    simp at hrightLeaf
  · rcases hrightChild with
      ⟨rightChildRuntime, rightChildFields, rightChildErrors,
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
        executeField_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_objectProbe_response_of_fuel_ge
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet rightCurrentSelectionSet variableValues fuel
          targetParent leftProbeField rightProbeField rightParentType
          rightFieldName rightSourceRuntimeType responseName
          targetLeftArguments targetRightArguments rightArguments leftRuntime
          rightRuntime FieldPairProbeTag.right rightChildSelectionSet
          rightFieldDefinition rightChildRuntime hrightLookup _hrightCoercion
          hrightRuntime
          hrightInclude hrightFuel]
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
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_left_leaf_right_composite_field_pair_of_field_children_fuels
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
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
      -> leafProbeFuel leftFieldDefinition.outputType ≤ leftFuel
      -> (TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ left
            -> ∃ fieldDefinition,
                schema.lookupField leftParentType fieldName = some fieldDefinition
                ∧ (Execution.coerceArgumentValues schema variableValues
                    fieldDefinition.arguments arguments).isSuccess
                  = true
                ∧ leafProbeFuel fieldDefinition.outputType ≤ leftFuel
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
                                ∧ abstractRuntimeForFieldDeep? schema
                                    leftParentType fieldName leftParentType
                                    leftCurrentSelectionSet
                                  = some childRuntimeType))
                          ∧ schema.typeIncludesObjectBool
                              fieldDefinition.outputType.namedType childRuntimeType
                            = true
                          ∧ Execution.executeSelectionSetAsResponse schema
                              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                                (fieldPairPathLocalProbeResolvers schema
                                  leftInitialSelectionSet rightInitialSelectionSet
                                  targetParent leftProbeField rightProbeField
                                  targetLeftArguments targetRightArguments
                                  leftRuntime rightRuntime)
                                targetParent leftProbeField rightProbeField
                                targetLeftArguments targetRightArguments)
                              variableValues
                              (leftFuel - leafProbeFuel fieldDefinition.outputType)
                              childRuntimeType
                              (projectionTargetResolverValue
                                (.object childRuntimeType
                                  (FieldPairPathLocalProbeRef.target
                                    FieldPairProbeTag.left
                                    (fieldPairPathLocalNextSelectionSet schema
                                      leftParentType childRuntimeType fieldName
                                      arguments leftCurrentSelectionSet))))
                              childSelectionSet
                            = ({
                                  data := Execution.ResponseValue.object responseFields,
                                  errors := childErrors
                                }
                                : Execution.Response))))
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ right
            -> ∃ fieldDefinition,
                schema.lookupField rightParentType fieldName = some fieldDefinition
                ∧ (Execution.coerceArgumentValues schema variableValues
                    fieldDefinition.arguments arguments).isSuccess
                  = true
                ∧ leafProbeFuel fieldDefinition.outputType ≤ rightFuel
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
                                ∧ abstractRuntimeForFieldDeep? schema
                                    rightParentType fieldName rightParentType
                                    rightCurrentSelectionSet
                                  = some childRuntimeType))
                          ∧ schema.typeIncludesObjectBool
                              fieldDefinition.outputType.namedType childRuntimeType
                            = true
                          ∧ Execution.executeSelectionSetAsResponse schema
                              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                                (fieldPairPathLocalProbeResolvers schema
                                  leftInitialSelectionSet rightInitialSelectionSet
                                  targetParent leftProbeField rightProbeField
                                  targetLeftArguments targetRightArguments
                                  leftRuntime rightRuntime)
                                targetParent leftProbeField rightProbeField
                                targetLeftArguments targetRightArguments)
                              variableValues
                              (rightFuel - leafProbeFuel fieldDefinition.outputType)
                              childRuntimeType
                              (projectionTargetResolverValue
                                (.object childRuntimeType
                                  (FieldPairPathLocalProbeRef.target
                                    FieldPairProbeTag.right
                                    (fieldPairPathLocalNextSelectionSet schema
                                      rightParentType childRuntimeType fieldName
                                      arguments rightCurrentSelectionSet))))
                              childSelectionSet
                            = ({
                                  data := Execution.ResponseValue.object responseFields,
                                  errors := childErrors
                                }
                                : Execution.Response))))
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
    hrightObject hleftMem hrightMem hleftLookup hrightLookup hleftFuel
    hleftLeaf hrightComposite hleftChildren hrightChildren
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
      executeField_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_leaf
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftCurrentSelectionSet variableValues
        leftFuel targetParent leftProbeField rightProbeField leftParentType
        leftFieldName leftSourceRuntimeType responseName targetLeftArguments
        targetRightArguments leftArguments leftRuntime rightRuntime
        FieldPairProbeTag.left leftChildSelectionSet leftFieldDefinition
        hleftLookup
        (PathLocalSelectionSetFieldChildrenReady.argumentCoercion_of_mem_lookup
          hleftChildren hleftMem hleftLookup)
        hleftFuel hleftLeaf
  rcases
      hrightChildren responseName rightFieldName rightArguments
        rightDirectives rightChildSelectionSet hrightMem with
    ⟨rightFieldDefinition', hrightLookup', _hrightCoercion, hrightFuel,
      hrightKind⟩
  have hrightDefinitionEq :
      rightFieldDefinition' = rightFieldDefinition := by
    rw [hrightLookup] at hrightLookup'
    exact Option.some.inj hrightLookup'.symm
  subst rightFieldDefinition'
  rcases hrightKind with hrightLeaf | hrightChild
  · rw [hrightComposite] at hrightLeaf
    simp at hrightLeaf
  · rcases hrightChild with
      ⟨rightChildRuntime, rightChildFields, rightChildErrors,
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
        executeField_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_objectProbe_response_of_fuel_ge
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet rightCurrentSelectionSet variableValues
          rightFuel targetParent leftProbeField rightProbeField
          rightParentType rightFieldName rightSourceRuntimeType responseName
          targetLeftArguments targetRightArguments rightArguments
          leftRuntime rightRuntime FieldPairProbeTag.right
          rightChildSelectionSet rightFieldDefinition rightChildRuntime
          hrightLookup _hrightCoercion hrightRuntime hrightInclude hrightFuel]
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
        hleftNormal hrightNormal hleftFree hrightFree hleftMem hrightMem
        hleftTarget hrightTarget hvalueNot hleftFieldOk hrightFieldOk

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_left_composite_right_leaf_field_pair_of_field_children
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
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
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ left
            -> ∃ fieldDefinition,
                schema.lookupField leftParentType fieldName = some fieldDefinition
                ∧ (Execution.coerceArgumentValues schema variableValues
                    fieldDefinition.arguments arguments).isSuccess
                  = true
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
                                ∧ abstractRuntimeForFieldDeep? schema
                                    leftParentType fieldName leftParentType
                                    leftCurrentSelectionSet
                                  = some childRuntimeType))
                          ∧ schema.typeIncludesObjectBool
                              fieldDefinition.outputType.namedType childRuntimeType
                            = true
                          ∧ Execution.executeSelectionSetAsResponse schema
                              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                                (fieldPairPathLocalProbeResolvers schema
                                  leftInitialSelectionSet rightInitialSelectionSet
                                  targetParent leftProbeField rightProbeField
                                  targetLeftArguments targetRightArguments
                                  leftRuntime rightRuntime)
                                targetParent leftProbeField rightProbeField
                                targetLeftArguments targetRightArguments)
                              variableValues
                              (fuel - leafProbeFuel fieldDefinition.outputType)
                              childRuntimeType
                              (projectionTargetResolverValue
                                (.object childRuntimeType
                                  (FieldPairPathLocalProbeRef.target
                                    FieldPairProbeTag.left
                                    (fieldPairPathLocalNextSelectionSet schema
                                      leftParentType childRuntimeType fieldName
                                      arguments leftCurrentSelectionSet))))
                              childSelectionSet
                            = ({
                                  data := Execution.ResponseValue.object responseFields,
                                  errors := childErrors
                                }
                                : Execution.Response))))
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ right
            -> ∃ fieldDefinition,
                schema.lookupField rightParentType fieldName = some fieldDefinition
                ∧ (Execution.coerceArgumentValues schema variableValues
                    fieldDefinition.arguments arguments).isSuccess
                  = true
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
                                ∧ abstractRuntimeForFieldDeep? schema
                                    rightParentType fieldName rightParentType
                                    rightCurrentSelectionSet
                                  = some childRuntimeType))
                          ∧ schema.typeIncludesObjectBool
                              fieldDefinition.outputType.namedType childRuntimeType
                            = true
                          ∧ Execution.executeSelectionSetAsResponse schema
                              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                                (fieldPairPathLocalProbeResolvers schema
                                  leftInitialSelectionSet rightInitialSelectionSet
                                  targetParent leftProbeField rightProbeField
                                  targetLeftArguments targetRightArguments
                                  leftRuntime rightRuntime)
                                targetParent leftProbeField rightProbeField
                                targetLeftArguments targetRightArguments)
                              variableValues
                              (fuel - leafProbeFuel fieldDefinition.outputType)
                              childRuntimeType
                              (projectionTargetResolverValue
                                (.object childRuntimeType
                                  (FieldPairPathLocalProbeRef.target
                                    FieldPairProbeTag.right
                                    (fieldPairPathLocalNextSelectionSet schema
                                      rightParentType childRuntimeType fieldName
                                      arguments rightCurrentSelectionSet))))
                              childSelectionSet
                            = ({
                                  data := Execution.ResponseValue.object responseFields,
                                  errors := childErrors
                                }
                                : Execution.Response))))
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
    hrightObject hleftMem hrightMem hleftLookup hrightLookup hrightFuel
    hleftComposite hrightLeaf hleftChildren hrightChildren
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
      executeField_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_leaf
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet rightCurrentSelectionSet variableValues fuel
        targetParent leftProbeField rightProbeField rightParentType
        rightFieldName rightSourceRuntimeType responseName targetLeftArguments
        targetRightArguments rightArguments leftRuntime rightRuntime
        FieldPairProbeTag.right rightChildSelectionSet rightFieldDefinition
        hrightLookup
        (PathLocalSelectionSetFieldChildrenReady.argumentCoercion_of_mem_lookup
          hrightChildren hrightMem hrightLookup)
        hrightFuel hrightLeaf
  rcases
      hleftChildren responseName leftFieldName leftArguments
        leftDirectives leftChildSelectionSet hleftMem with
    ⟨leftFieldDefinition', hleftLookup', _hleftCoercion, hleftFuel,
      hleftKind⟩
  have hleftDefinitionEq :
      leftFieldDefinition' = leftFieldDefinition := by
    rw [hleftLookup] at hleftLookup'
    exact Option.some.inj hleftLookup'.symm
  subst leftFieldDefinition'
  rcases hleftKind with hleftLeaf | hleftChild
  · rw [hleftComposite] at hleftLeaf
    simp at hleftLeaf
  · rcases hleftChild with
      ⟨leftChildRuntime, leftChildFields, leftChildErrors,
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
        executeField_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_objectProbe_response_of_fuel_ge
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet leftCurrentSelectionSet variableValues fuel
          targetParent leftProbeField rightProbeField leftParentType
          leftFieldName leftSourceRuntimeType responseName
          targetLeftArguments targetRightArguments leftArguments leftRuntime
          rightRuntime FieldPairProbeTag.left leftChildSelectionSet
          leftFieldDefinition leftChildRuntime hleftLookup _hleftCoercion
          hleftRuntime
          hleftInclude hleftFuel]
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
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_left_composite_right_leaf_field_pair_of_field_children_fuels
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
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
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ left
            -> ∃ fieldDefinition,
                schema.lookupField leftParentType fieldName = some fieldDefinition
                ∧ (Execution.coerceArgumentValues schema variableValues
                    fieldDefinition.arguments arguments).isSuccess
                  = true
                ∧ leafProbeFuel fieldDefinition.outputType ≤ leftFuel
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
                                ∧ abstractRuntimeForFieldDeep? schema
                                    leftParentType fieldName leftParentType
                                    leftCurrentSelectionSet
                                  = some childRuntimeType))
                          ∧ schema.typeIncludesObjectBool
                              fieldDefinition.outputType.namedType childRuntimeType
                            = true
                          ∧ Execution.executeSelectionSetAsResponse schema
                              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                                (fieldPairPathLocalProbeResolvers schema
                                  leftInitialSelectionSet rightInitialSelectionSet
                                  targetParent leftProbeField rightProbeField
                                  targetLeftArguments targetRightArguments
                                  leftRuntime rightRuntime)
                                targetParent leftProbeField rightProbeField
                                targetLeftArguments targetRightArguments)
                              variableValues
                              (leftFuel - leafProbeFuel fieldDefinition.outputType)
                              childRuntimeType
                              (projectionTargetResolverValue
                                (.object childRuntimeType
                                  (FieldPairPathLocalProbeRef.target
                                    FieldPairProbeTag.left
                                    (fieldPairPathLocalNextSelectionSet schema
                                      leftParentType childRuntimeType fieldName
                                      arguments leftCurrentSelectionSet))))
                              childSelectionSet
                            = ({
                                  data := Execution.ResponseValue.object responseFields,
                                  errors := childErrors
                                }
                                : Execution.Response))))
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ right
            -> ∃ fieldDefinition,
                schema.lookupField rightParentType fieldName = some fieldDefinition
                ∧ (Execution.coerceArgumentValues schema variableValues
                    fieldDefinition.arguments arguments).isSuccess
                  = true
                ∧ leafProbeFuel fieldDefinition.outputType ≤ rightFuel
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
                                ∧ abstractRuntimeForFieldDeep? schema
                                    rightParentType fieldName rightParentType
                                    rightCurrentSelectionSet
                                  = some childRuntimeType))
                          ∧ schema.typeIncludesObjectBool
                              fieldDefinition.outputType.namedType childRuntimeType
                            = true
                          ∧ Execution.executeSelectionSetAsResponse schema
                              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                                (fieldPairPathLocalProbeResolvers schema
                                  leftInitialSelectionSet rightInitialSelectionSet
                                  targetParent leftProbeField rightProbeField
                                  targetLeftArguments targetRightArguments
                                  leftRuntime rightRuntime)
                                targetParent leftProbeField rightProbeField
                                targetLeftArguments targetRightArguments)
                              variableValues
                              (rightFuel - leafProbeFuel fieldDefinition.outputType)
                              childRuntimeType
                              (projectionTargetResolverValue
                                (.object childRuntimeType
                                  (FieldPairPathLocalProbeRef.target
                                    FieldPairProbeTag.right
                                    (fieldPairPathLocalNextSelectionSet schema
                                      rightParentType childRuntimeType fieldName
                                      arguments rightCurrentSelectionSet))))
                              childSelectionSet
                            = ({
                                  data := Execution.ResponseValue.object responseFields,
                                  errors := childErrors
                                }
                                : Execution.Response))))
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
    hrightObject hleftMem hrightMem hleftLookup hrightLookup hrightFuel
    hleftComposite hrightLeaf hleftChildren hrightChildren
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
      executeField_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_leaf
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet rightCurrentSelectionSet variableValues
        rightFuel targetParent leftProbeField rightProbeField
        rightParentType rightFieldName rightSourceRuntimeType responseName
        targetLeftArguments targetRightArguments rightArguments leftRuntime
        rightRuntime FieldPairProbeTag.right rightChildSelectionSet
        rightFieldDefinition hrightLookup
        (PathLocalSelectionSetFieldChildrenReady.argumentCoercion_of_mem_lookup
          hrightChildren hrightMem hrightLookup)
        hrightFuel hrightLeaf
  rcases
      hleftChildren responseName leftFieldName leftArguments
        leftDirectives leftChildSelectionSet hleftMem with
    ⟨leftFieldDefinition', hleftLookup', _hleftCoercion, hleftFuel,
      hleftKind⟩
  have hleftDefinitionEq :
      leftFieldDefinition' = leftFieldDefinition := by
    rw [hleftLookup] at hleftLookup'
    exact Option.some.inj hleftLookup'.symm
  subst leftFieldDefinition'
  rcases hleftKind with hleftLeaf | hleftChild
  · rw [hleftComposite] at hleftLeaf
    simp at hleftLeaf
  · rcases hleftChild with
      ⟨leftChildRuntime, leftChildFields, leftChildErrors,
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
        executeField_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_objectProbe_response_of_fuel_ge
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet leftCurrentSelectionSet variableValues
          leftFuel targetParent leftProbeField rightProbeField leftParentType
          leftFieldName leftSourceRuntimeType responseName
          targetLeftArguments targetRightArguments leftArguments leftRuntime
          rightRuntime FieldPairProbeTag.left leftChildSelectionSet
          leftFieldDefinition leftChildRuntime hleftLookup _hleftCoercion
          hleftRuntime
          hleftInclude hleftFuel]
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
        hleftNormal hrightNormal hleftFree hrightFree hleftMem hrightMem
        hleftTarget hrightTarget hvalueNot hleftFieldOk hrightFieldOk

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_leaf_field_pair_of_valid_normal_support_context_fuel_ge
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftProbeField rightProbeField leftParentType rightParentType : Name)
    (targetLeftArguments targetRightArguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime : Name) {left right : List Selection}
    {responseName leftFieldName rightFieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {leftFieldDefinition rightFieldDefinition : FieldDefinition}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
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
      -> (TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool schema
          = false
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
  intro hschema hleftValid hrightValid hleftCoercion hrightCoercion hleftFree
    hrightFree hleftNormal
    hrightNormal hleftObject hrightObject hleftFuel hrightFuel hleftSupport
    hrightSupport hleftContext hrightContext hleftMem hrightMem hleftLookup
    hrightLookup hleftLeaf hrightLeaf
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
      hleftValid hleftCoercion hleftFree hleftNormal hleftObject hleftSupport
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
      (by omega) hrightFuel hrightValid hrightCoercion hrightFree hrightNormal
      hrightObject hrightSupport hrightContext
  exact
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_leaf_field_pair_of_field_children
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet leftCurrentSelectionSet
      rightCurrentSelectionSet variableValues fuel targetParent
      leftProbeField rightProbeField leftParentType rightParentType
      leftParentType rightParentType targetLeftArguments
      targetRightArguments leftRuntime rightRuntime hleftFree hrightFree
      hleftNormal hrightNormal hleftObject hrightObject hleftMem hrightMem
      hleftLookup hrightLookup
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
      hleftLeaf hrightLeaf hleftChildren hrightChildren

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_leaf_field_pair_of_valid_normal_support_context_fuel_ge_fuels
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (variableValues : Execution.VariableValues) (leftFuel rightFuel : Nat)
    (targetParent leftProbeField rightProbeField leftParentType rightParentType : Name)
    (targetLeftArguments targetRightArguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime : Name) {left right : List Selection}
    {responseName leftFieldName rightFieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {leftFieldDefinition rightFieldDefinition : FieldDefinition}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
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
      -> (TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool schema
          = false
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
  intro hschema hleftValid hrightValid hleftCoercion hrightCoercion hleftFree
    hrightFree hleftNormal
    hrightNormal hleftObject hrightObject hleftFuel hrightFuel hleftSupport
    hrightSupport hleftContext hrightContext hleftMem hrightMem hleftLookup
    hrightLookup hleftLeaf hrightLeaf
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
      hleftValid hleftCoercion hleftFree hleftNormal hleftObject hleftSupport
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
      (by omega) hrightFuel hrightValid hrightCoercion hrightFree hrightNormal
      hrightObject hrightSupport hrightContext
  exact
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_leaf_field_pair_of_field_children_fuels
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet leftCurrentSelectionSet
      rightCurrentSelectionSet variableValues leftFuel rightFuel
      targetParent leftProbeField rightProbeField leftParentType
      rightParentType leftParentType rightParentType targetLeftArguments
      targetRightArguments leftRuntime rightRuntime hleftFree hrightFree
      hleftNormal hrightNormal hleftObject hrightObject hleftMem hrightMem
      hleftLookup hrightLookup
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
      hleftLeaf hrightLeaf hleftChildren hrightChildren

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_left_responseName_diff_of_valid_normal_support_context_fuel_ge
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftProbeField rightProbeField leftParentType rightParentType : Name)
    (targetLeftArguments targetRightArguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime : Name) {left right : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication} {childSelectionSet : List Selection}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
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
      -> PathLocalSupportValidNormal schema leftParentType leftCurrentSelectionSet
      -> PathLocalSupportValidNormal schema rightParentType rightCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext left leftCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext right rightCurrentSelectionSet
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ left
      -> responseName ∉ right.filterMap Selection.responseName?
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
  intro hschema hleftValid hrightValid hleftCoercion hrightCoercion hleftFree
    hrightFree hleftNormal
    hrightNormal hleftObject hrightObject hleftFuel hrightFuel hleftSupport
    hrightSupport hleftContext hrightContext hleftMem hrightNoResponseName
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
      hleftValid hleftCoercion hleftFree hleftNormal hleftObject hleftSupport
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
      (by omega) hrightFuel hrightValid hrightCoercion hrightFree hrightNormal
      hrightObject hrightSupport hrightContext
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet
      (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
        rightInitialSelectionSet targetParent leftProbeField rightProbeField
        targetLeftArguments targetRightArguments leftRuntime rightRuntime)
      targetParent leftProbeField rightProbeField targetLeftArguments
      targetRightArguments
  let leftSource :=
    projectionTargetResolverValue
      (.object leftParentType
        (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
          leftCurrentSelectionSet))
  let rightSource :=
    projectionTargetResolverValue
      (.object rightParentType
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
        leftParentType targetLeftArguments targetRightArguments
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
        rightParentType targetLeftArguments targetRightArguments
        leftRuntime rightRuntime FieldPairProbeTag.right right
        hrightChildren
  exact
    SemanticSeparation.responseData_not_semanticEquivalent_of_left_responseName_diff_of_field_ok_sources_pair
      resolvers resolvers variableValues (fuel + 1) leftSource rightSource
      hleftObject hrightObject hleftNormal hrightNormal hleftFree
      hrightFree hleftMem hrightNoResponseName hleftFieldOk hrightFieldOk

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_left_responseName_diff_of_valid_normal_support_context_fuel_ge_fuels
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (variableValues : Execution.VariableValues) (leftFuel rightFuel : Nat)
    (targetParent leftProbeField rightProbeField leftParentType rightParentType : Name)
    (targetLeftArguments targetRightArguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime : Name) {left right : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication} {childSelectionSet : List Selection}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
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
      -> PathLocalSupportValidNormal schema leftParentType leftCurrentSelectionSet
      -> PathLocalSupportValidNormal schema rightParentType rightCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext left leftCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext right rightCurrentSelectionSet
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ left
      -> responseName ∉ right.filterMap Selection.responseName?
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
  intro hschema hleftValid hrightValid hleftCoercion hrightCoercion hleftFree
    hrightFree hleftNormal
    hrightNormal hleftObject hrightObject hleftFuel hrightFuel hleftSupport
    hrightSupport hleftContext hrightContext hleftMem hrightNoResponseName
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
      hleftValid hleftCoercion hleftFree hleftNormal hleftObject hleftSupport
      hleftContext
  have hrightChildren :
      PathLocalSelectionSetFieldChildrenReady schema rootSelectionSet
        leftInitialSelectionSet rightInitialSelectionSet variableValues
        rightFuel targetParent leftProbeField rightProbeField
        rightParentType targetLeftArguments targetRightArguments
        leftRuntime rightRuntime FieldPairProbeTag.right
        rightCurrentSelectionSet right :=
    pathLocalSelectionSetFieldChildrenReady_of_valid_normal_support_context_fuel_ge_size
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet variableValues hschema
      (SelectionSet.size right + 1) rightParentType
      rightVariableDefinitions right rightFuel targetParent leftProbeField
      rightProbeField targetLeftArguments targetRightArguments leftRuntime
      rightRuntime FieldPairProbeTag.right rightCurrentSelectionSet
      (by omega) hrightFuel hrightValid hrightCoercion hrightFree hrightNormal
      hrightObject hrightSupport hrightContext
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet
      (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
        rightInitialSelectionSet targetParent leftProbeField rightProbeField
        targetLeftArguments targetRightArguments leftRuntime rightRuntime)
      targetParent leftProbeField rightProbeField targetLeftArguments
      targetRightArguments
  let leftSource :=
    projectionTargetResolverValue
      (.object leftParentType
        (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
          leftCurrentSelectionSet))
  let rightSource :=
    projectionTargetResolverValue
      (.object rightParentType
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
        leftParentType leftParentType targetLeftArguments
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
        rightParentType rightParentType targetLeftArguments
        targetRightArguments leftRuntime rightRuntime FieldPairProbeTag.right
        right hrightChildren
  exact
    SemanticSeparation.responseData_not_semanticEquivalent_of_left_responseName_diff_of_field_ok_sources_pair_fuels
      resolvers resolvers variableValues (leftFuel + 1)
      (rightFuel + 1) leftSource rightSource hleftObject hrightObject
      hleftNormal hrightNormal hleftFree hrightFree hleftMem
      hrightNoResponseName hleftFieldOk hrightFieldOk

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_right_responseName_diff_of_valid_normal_support_context_fuel_ge
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftProbeField rightProbeField leftParentType rightParentType : Name)
    (targetLeftArguments targetRightArguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime : Name) {left right : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication} {childSelectionSet : List Selection}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
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
      -> PathLocalSupportValidNormal schema leftParentType leftCurrentSelectionSet
      -> PathLocalSupportValidNormal schema rightParentType rightCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext left leftCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext right rightCurrentSelectionSet
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ right
      -> responseName ∉ left.filterMap Selection.responseName?
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
  intro hschema hleftValid hrightValid hleftCoercion hrightCoercion hleftFree
    hrightFree hleftNormal
    hrightNormal hleftObject hrightObject hleftFuel hrightFuel hleftSupport
    hrightSupport hleftContext hrightContext hrightMem hleftNoResponseName
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
      hleftValid hleftCoercion hleftFree hleftNormal hleftObject hleftSupport
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
      (by omega) hrightFuel hrightValid hrightCoercion hrightFree hrightNormal
      hrightObject hrightSupport hrightContext
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet
      (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
        rightInitialSelectionSet targetParent leftProbeField rightProbeField
        targetLeftArguments targetRightArguments leftRuntime rightRuntime)
      targetParent leftProbeField rightProbeField targetLeftArguments
      targetRightArguments
  let leftSource :=
    projectionTargetResolverValue
      (.object leftParentType
        (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
          leftCurrentSelectionSet))
  let rightSource :=
    projectionTargetResolverValue
      (.object rightParentType
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
        leftParentType targetLeftArguments targetRightArguments
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
        rightParentType targetLeftArguments targetRightArguments
        leftRuntime rightRuntime FieldPairProbeTag.right right
        hrightChildren
  exact
    SemanticSeparation.responseData_not_semanticEquivalent_of_right_responseName_diff_of_field_ok_sources_pair
      resolvers resolvers variableValues (fuel + 1) leftSource rightSource
      hleftObject hrightObject hleftNormal hrightNormal hleftFree
      hrightFree hrightMem hleftNoResponseName hleftFieldOk hrightFieldOk

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_right_responseName_diff_of_valid_normal_support_context_fuel_ge_fuels
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (variableValues : Execution.VariableValues) (leftFuel rightFuel : Nat)
    (targetParent leftProbeField rightProbeField leftParentType rightParentType : Name)
    (targetLeftArguments targetRightArguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime : Name) {left right : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication} {childSelectionSet : List Selection}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
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
      -> PathLocalSupportValidNormal schema leftParentType leftCurrentSelectionSet
      -> PathLocalSupportValidNormal schema rightParentType rightCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext left leftCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext right rightCurrentSelectionSet
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ right
      -> responseName ∉ left.filterMap Selection.responseName?
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
  intro hschema hleftValid hrightValid hleftCoercion hrightCoercion hleftFree
    hrightFree hleftNormal
    hrightNormal hleftObject hrightObject hleftFuel hrightFuel hleftSupport
    hrightSupport hleftContext hrightContext hrightMem hleftNoResponseName
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
      hleftValid hleftCoercion hleftFree hleftNormal hleftObject hleftSupport
      hleftContext
  have hrightChildren :
      PathLocalSelectionSetFieldChildrenReady schema rootSelectionSet
        leftInitialSelectionSet rightInitialSelectionSet variableValues
        rightFuel targetParent leftProbeField rightProbeField
        rightParentType targetLeftArguments targetRightArguments
        leftRuntime rightRuntime FieldPairProbeTag.right
        rightCurrentSelectionSet right :=
    pathLocalSelectionSetFieldChildrenReady_of_valid_normal_support_context_fuel_ge_size
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet variableValues hschema
      (SelectionSet.size right + 1) rightParentType
      rightVariableDefinitions right rightFuel targetParent leftProbeField
      rightProbeField targetLeftArguments targetRightArguments leftRuntime
      rightRuntime FieldPairProbeTag.right rightCurrentSelectionSet
      (by omega) hrightFuel hrightValid hrightCoercion hrightFree hrightNormal
      hrightObject hrightSupport hrightContext
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet
      (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
        rightInitialSelectionSet targetParent leftProbeField rightProbeField
        targetLeftArguments targetRightArguments leftRuntime rightRuntime)
      targetParent leftProbeField rightProbeField targetLeftArguments
      targetRightArguments
  let leftSource :=
    projectionTargetResolverValue
      (.object leftParentType
        (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
          leftCurrentSelectionSet))
  let rightSource :=
    projectionTargetResolverValue
      (.object rightParentType
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
        leftParentType leftParentType targetLeftArguments
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
        rightParentType rightParentType targetLeftArguments
        targetRightArguments leftRuntime rightRuntime FieldPairProbeTag.right
        right hrightChildren
  exact
    SemanticSeparation.responseData_not_semanticEquivalent_of_right_responseName_diff_of_field_ok_sources_pair_fuels
      resolvers resolvers variableValues (leftFuel + 1)
      (rightFuel + 1) leftSource rightSource hleftObject hrightObject
      hleftNormal hrightNormal hleftFree hrightFree hrightMem
      hleftNoResponseName hleftFieldOk hrightFieldOk

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_left_object_leaf_of_valid_normal_support_context_fuel_ge
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftProbeField rightProbeField leftParentType rightParentType : Name)
    (targetLeftArguments targetRightArguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime : Name) {left right : List Selection}
    {responseName leftFieldName : Name} {leftArguments : List Argument}
    {leftDirectives : List DirectiveApplication} {leftChildSelectionSet : List Selection}
    {leftFieldDefinition : FieldDefinition}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
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
      -> PathLocalSupportValidNormal schema leftParentType leftCurrentSelectionSet
      -> PathLocalSupportValidNormal schema rightParentType rightCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext left leftCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext right rightCurrentSelectionSet
      -> Selection.field responseName leftFieldName leftArguments
            leftDirectives leftChildSelectionSet
          ∈ left
      -> schema.lookupField leftParentType leftFieldName = some leftFieldDefinition
      -> (TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool schema
          = false
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
  intro hschema hleftValid hrightValid hleftCoercion hrightCoercion hleftFree
    hrightFree hleftNormal
    hrightNormal hleftObject hrightObject hleftFuel hrightFuel hleftSupport
    hrightSupport hleftContext hrightContext hleftMem hleftLookup hleftLeaf
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
      hleftValid hleftCoercion hleftFree hleftNormal hleftObject hleftSupport
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
      (by omega) hrightFuel hrightValid hrightCoercion hrightFree hrightNormal
      hrightObject hrightSupport hrightContext
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
        responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_leaf_field_pair_of_valid_normal_support_context_fuel_ge
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet leftCurrentSelectionSet
          rightCurrentSelectionSet variableValues fuel targetParent
          leftProbeField rightProbeField leftParentType rightParentType
          targetLeftArguments targetRightArguments leftRuntime rightRuntime
          hschema hleftValid hrightValid hleftCoercion hrightCoercion
          hleftFree hrightFree hleftNormal
          hrightNormal hleftObject hrightObject hleftFuel hrightFuel
          hleftSupport hrightSupport hleftContext hrightContext hleftMem
          hrightMem hleftLookup hrightLookup hleftLeaf hrightLeaf
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
      exact
        responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_left_leaf_right_composite_field_pair_of_field_children
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet leftCurrentSelectionSet
          rightCurrentSelectionSet variableValues fuel targetParent
          leftProbeField rightProbeField leftParentType rightParentType
          leftParentType rightParentType targetLeftArguments
          targetRightArguments leftRuntime rightRuntime hleftFree hrightFree
          hleftNormal hrightNormal hleftObject hrightObject hleftMem
          hrightMem hleftLookup hrightLookup
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
          hleftLeaf hrightComposite hleftChildren hrightChildren
  · exact
      responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_left_responseName_diff_of_valid_normal_support_context_fuel_ge
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftCurrentSelectionSet
        rightCurrentSelectionSet variableValues fuel targetParent
        leftProbeField rightProbeField leftParentType rightParentType
        targetLeftArguments targetRightArguments leftRuntime rightRuntime
        hschema hleftValid hrightValid hleftCoercion hrightCoercion hleftFree
        hrightFree hleftNormal
        hrightNormal hleftObject hrightObject hleftFuel hrightFuel
        hleftSupport hrightSupport hleftContext hrightContext hleftMem
        hrightResponseName

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_left_leaf_right_composite_field_pair_of_valid_normal_support_context_fuel_ge
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftProbeField rightProbeField leftParentType rightParentType : Name)
    (targetLeftArguments targetRightArguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime : Name) {left right : List Selection}
    {responseName leftFieldName rightFieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {leftFieldDefinition rightFieldDefinition : FieldDefinition}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
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
      -> (TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool schema
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
  intro hschema hleftValid hrightValid hleftCoercion hrightCoercion hleftFree
    hrightFree hleftNormal
    hrightNormal hleftObject hrightObject hleftFuel hrightFuel hleftSupport
    hrightSupport hleftContext hrightContext hleftMem hrightMem hleftLookup
    hrightLookup hleftLeaf hrightComposite
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
      hleftValid hleftCoercion hleftFree hleftNormal hleftObject hleftSupport
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
      (by omega) hrightFuel hrightValid hrightCoercion hrightFree hrightNormal
      hrightObject hrightSupport hrightContext
  exact
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_left_leaf_right_composite_field_pair_of_field_children
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet leftCurrentSelectionSet
      rightCurrentSelectionSet variableValues fuel targetParent
      leftProbeField rightProbeField leftParentType rightParentType
      leftParentType rightParentType targetLeftArguments
      targetRightArguments leftRuntime rightRuntime hleftFree hrightFree
      hleftNormal hrightNormal hleftObject hrightObject hleftMem hrightMem
      hleftLookup hrightLookup
      (by
        have hlocal :=
          leafProbeFuel_le_selectionSetDeepProbeFuel_of_field_mem schema
            leftParentType (selectionSet := left)
            (responseName := responseName) (fieldName := leftFieldName)
            (arguments := leftArguments) (directives := leftDirectives)
            (childSelectionSet := leftChildSelectionSet)
            (fieldDefinition := leftFieldDefinition) hleftMem hleftLookup
        omega)
      hleftLeaf hrightComposite hleftChildren hrightChildren

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_left_composite_right_leaf_field_pair_of_valid_normal_support_context_fuel_ge
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftProbeField rightProbeField leftParentType rightParentType : Name)
    (targetLeftArguments targetRightArguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime : Name) {left right : List Selection}
    {responseName leftFieldName rightFieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {leftFieldDefinition rightFieldDefinition : FieldDefinition}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
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
      -> (TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool schema
          = false
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
  intro hschema hleftValid hrightValid hleftCoercion hrightCoercion hleftFree
    hrightFree hleftNormal
    hrightNormal hleftObject hrightObject hleftFuel hrightFuel hleftSupport
    hrightSupport hleftContext hrightContext hleftMem hrightMem hleftLookup
    hrightLookup hleftComposite hrightLeaf
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
      hleftValid hleftCoercion hleftFree hleftNormal hleftObject hleftSupport
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
      (by omega) hrightFuel hrightValid hrightCoercion hrightFree hrightNormal
      hrightObject hrightSupport hrightContext
  exact
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_left_composite_right_leaf_field_pair_of_field_children
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet leftCurrentSelectionSet
      rightCurrentSelectionSet variableValues fuel targetParent
      leftProbeField rightProbeField leftParentType rightParentType
      leftParentType rightParentType targetLeftArguments
      targetRightArguments leftRuntime rightRuntime hleftFree hrightFree
      hleftNormal hrightNormal hleftObject hrightObject hleftMem hrightMem
      hleftLookup hrightLookup
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
      hleftComposite hrightLeaf hleftChildren hrightChildren

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_left_leaf_right_composite_field_pair_of_valid_normal_support_context_fuel_ge_fuels
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (variableValues : Execution.VariableValues) (leftFuel rightFuel : Nat)
    (targetParent leftProbeField rightProbeField leftParentType rightParentType : Name)
    (targetLeftArguments targetRightArguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime : Name) {left right : List Selection}
    {responseName leftFieldName rightFieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {leftFieldDefinition rightFieldDefinition : FieldDefinition}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
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
      -> (TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool schema
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
  intro hschema hleftValid hrightValid hleftCoercion hrightCoercion hleftFree
    hrightFree hleftNormal
    hrightNormal hleftObject hrightObject hleftFuel hrightFuel hleftSupport
    hrightSupport hleftContext hrightContext hleftMem hrightMem hleftLookup
    hrightLookup hleftLeaf hrightComposite
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
      hleftValid hleftCoercion hleftFree hleftNormal hleftObject hleftSupport
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
      (by omega) hrightFuel hrightValid hrightCoercion hrightFree hrightNormal
      hrightObject hrightSupport hrightContext
  exact
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_left_leaf_right_composite_field_pair_of_field_children_fuels
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet leftCurrentSelectionSet
      rightCurrentSelectionSet variableValues leftFuel rightFuel
      targetParent leftProbeField rightProbeField leftParentType
      rightParentType leftParentType rightParentType targetLeftArguments
      targetRightArguments leftRuntime rightRuntime hleftFree hrightFree
      hleftNormal hrightNormal hleftObject hrightObject hleftMem hrightMem
      hleftLookup hrightLookup
      (by
        have hlocal :=
          leafProbeFuel_le_selectionSetDeepProbeFuel_of_field_mem schema
            leftParentType (selectionSet := left)
            (responseName := responseName) (fieldName := leftFieldName)
            (arguments := leftArguments) (directives := leftDirectives)
            (childSelectionSet := leftChildSelectionSet)
            (fieldDefinition := leftFieldDefinition) hleftMem hleftLookup
        omega)
      hleftLeaf hrightComposite hleftChildren hrightChildren

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_left_composite_right_leaf_field_pair_of_valid_normal_support_context_fuel_ge_fuels
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (variableValues : Execution.VariableValues) (leftFuel rightFuel : Nat)
    (targetParent leftProbeField rightProbeField leftParentType rightParentType : Name)
    (targetLeftArguments targetRightArguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime : Name) {left right : List Selection}
    {responseName leftFieldName rightFieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {leftFieldDefinition rightFieldDefinition : FieldDefinition}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
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
      -> (TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool schema
          = false
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
  intro hschema hleftValid hrightValid hleftCoercion hrightCoercion hleftFree
    hrightFree hleftNormal
    hrightNormal hleftObject hrightObject hleftFuel hrightFuel hleftSupport
    hrightSupport hleftContext hrightContext hleftMem hrightMem hleftLookup
    hrightLookup hleftComposite hrightLeaf
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
      hleftValid hleftCoercion hleftFree hleftNormal hleftObject hleftSupport
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
      (by omega) hrightFuel hrightValid hrightCoercion hrightFree hrightNormal
      hrightObject hrightSupport hrightContext
  exact
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_left_composite_right_leaf_field_pair_of_field_children_fuels
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet leftCurrentSelectionSet
      rightCurrentSelectionSet variableValues leftFuel rightFuel
      targetParent leftProbeField rightProbeField leftParentType
      rightParentType leftParentType rightParentType targetLeftArguments
      targetRightArguments leftRuntime rightRuntime hleftFree hrightFree
      hleftNormal hrightNormal hleftObject hrightObject hleftMem hrightMem
      hleftLookup hrightLookup
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
      hleftComposite hrightLeaf hleftChildren hrightChildren

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_left_object_leaf_of_valid_normal_support_context_fuel_ge_fuels
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (variableValues : Execution.VariableValues) (leftFuel rightFuel : Nat)
    (targetParent leftProbeField rightProbeField leftParentType rightParentType : Name)
    (targetLeftArguments targetRightArguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime : Name) {left right : List Selection}
    {responseName leftFieldName : Name} {leftArguments : List Argument}
    {leftDirectives : List DirectiveApplication} {leftChildSelectionSet : List Selection}
    {leftFieldDefinition : FieldDefinition}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
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
      -> PathLocalSupportValidNormal schema leftParentType leftCurrentSelectionSet
      -> PathLocalSupportValidNormal schema rightParentType rightCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext left leftCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext right rightCurrentSelectionSet
      -> Selection.field responseName leftFieldName leftArguments
            leftDirectives leftChildSelectionSet
          ∈ left
      -> schema.lookupField leftParentType leftFieldName = some leftFieldDefinition
      -> (TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool schema
          = false
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
  intro hschema hleftValid hrightValid hleftCoercion hrightCoercion hleftFree
    hrightFree hleftNormal
    hrightNormal hleftObject hrightObject hleftFuel hrightFuel hleftSupport
    hrightSupport hleftContext hrightContext hleftMem hleftLookup hleftLeaf
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
        responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_leaf_field_pair_of_valid_normal_support_context_fuel_ge_fuels
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet leftCurrentSelectionSet
          rightCurrentSelectionSet variableValues leftFuel rightFuel
          targetParent leftProbeField rightProbeField leftParentType
          rightParentType targetLeftArguments targetRightArguments
          leftRuntime rightRuntime hschema hleftValid hrightValid
          hleftCoercion hrightCoercion hleftFree hrightFree hleftNormal
          hrightNormal hleftObject
          hrightObject hleftFuel hrightFuel hleftSupport hrightSupport
          hleftContext hrightContext hleftMem hrightMem hleftLookup
          hrightLookup hleftLeaf hrightLeaf
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
      exact
        responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_left_leaf_right_composite_field_pair_of_valid_normal_support_context_fuel_ge_fuels
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet leftCurrentSelectionSet
          rightCurrentSelectionSet variableValues leftFuel rightFuel
          targetParent leftProbeField rightProbeField leftParentType
          rightParentType targetLeftArguments targetRightArguments
          leftRuntime rightRuntime hschema hleftValid hrightValid
          hleftCoercion hrightCoercion hleftFree hrightFree hleftNormal
          hrightNormal hleftObject
          hrightObject hleftFuel hrightFuel hleftSupport hrightSupport
          hleftContext hrightContext hleftMem hrightMem hleftLookup
          hrightLookup hleftLeaf hrightComposite
  · exact
      responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_left_responseName_diff_of_valid_normal_support_context_fuel_ge_fuels
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftCurrentSelectionSet
        rightCurrentSelectionSet variableValues leftFuel rightFuel
        targetParent leftProbeField rightProbeField leftParentType
        rightParentType targetLeftArguments targetRightArguments
        leftRuntime rightRuntime hschema hleftValid hrightValid hleftCoercion
        hrightCoercion hleftFree hrightFree hleftNormal hrightNormal hleftObject
        hrightObject
        hleftFuel hrightFuel hleftSupport hrightSupport hleftContext
        hrightContext hleftMem hrightResponseName

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_right_object_leaf_of_valid_normal_support_context_fuel_ge
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftProbeField rightProbeField leftParentType rightParentType : Name)
    (targetLeftArguments targetRightArguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime : Name) {left right : List Selection}
    {responseName rightFieldName : Name} {rightArguments : List Argument}
    {rightDirectives : List DirectiveApplication}
    {rightChildSelectionSet : List Selection} {rightFieldDefinition : FieldDefinition}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
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
      -> PathLocalSupportValidNormal schema leftParentType leftCurrentSelectionSet
      -> PathLocalSupportValidNormal schema rightParentType rightCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext left leftCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext right rightCurrentSelectionSet
      -> Selection.field responseName rightFieldName rightArguments
            rightDirectives rightChildSelectionSet
          ∈ right
      -> schema.lookupField rightParentType rightFieldName = some rightFieldDefinition
      -> (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool schema
          = false
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
  intro hschema hleftValid hrightValid hleftCoercion hrightCoercion hleftFree
    hrightFree hleftNormal
    hrightNormal hleftObject hrightObject hleftFuel hrightFuel hleftSupport
    hrightSupport hleftContext hrightContext hrightMem hrightLookup hrightLeaf
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
        responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_leaf_field_pair_of_valid_normal_support_context_fuel_ge
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet leftCurrentSelectionSet
          rightCurrentSelectionSet variableValues fuel targetParent
          leftProbeField rightProbeField leftParentType rightParentType
          targetLeftArguments targetRightArguments leftRuntime rightRuntime
          hschema hleftValid hrightValid hleftCoercion hrightCoercion
          hleftFree hrightFree hleftNormal
          hrightNormal hleftObject hrightObject hleftFuel hrightFuel
          hleftSupport hrightSupport hleftContext hrightContext hleftMem
          hrightMem hleftLookup hrightLookup hleftLeaf hrightLeaf
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
      exact
        responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_left_composite_right_leaf_field_pair_of_valid_normal_support_context_fuel_ge
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet leftCurrentSelectionSet
          rightCurrentSelectionSet variableValues fuel targetParent
          leftProbeField rightProbeField leftParentType rightParentType
          targetLeftArguments targetRightArguments leftRuntime rightRuntime
          hschema hleftValid hrightValid hleftCoercion hrightCoercion
          hleftFree hrightFree hleftNormal
          hrightNormal hleftObject hrightObject hleftFuel hrightFuel
          hleftSupport hrightSupport hleftContext hrightContext hleftMem
          hrightMem hleftLookup hrightLookup hleftComposite hrightLeaf
  · exact
      responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_right_responseName_diff_of_valid_normal_support_context_fuel_ge
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftCurrentSelectionSet
        rightCurrentSelectionSet variableValues fuel targetParent
        leftProbeField rightProbeField leftParentType rightParentType
        targetLeftArguments targetRightArguments leftRuntime rightRuntime
        hschema hleftValid hrightValid hleftCoercion hrightCoercion hleftFree
        hrightFree hleftNormal
        hrightNormal hleftObject hrightObject hleftFuel hrightFuel
        hleftSupport hrightSupport hleftContext hrightContext hrightMem
        hleftResponseName

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_right_object_leaf_of_valid_normal_support_context_fuel_ge_fuels
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet
      : List Selection)
    (variableValues : Execution.VariableValues) (leftFuel rightFuel : Nat)
    (targetParent leftProbeField rightProbeField leftParentType rightParentType : Name)
    (targetLeftArguments targetRightArguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime : Name) {left right : List Selection}
    {responseName rightFieldName : Name} {rightArguments : List Argument}
    {rightDirectives : List DirectiveApplication}
    {rightChildSelectionSet : List Selection} {rightFieldDefinition : FieldDefinition}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
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
      -> PathLocalSupportValidNormal schema leftParentType leftCurrentSelectionSet
      -> PathLocalSupportValidNormal schema rightParentType rightCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext left leftCurrentSelectionSet
      -> PathLocalSelectionSetCurrentContext right rightCurrentSelectionSet
      -> Selection.field responseName rightFieldName rightArguments
            rightDirectives rightChildSelectionSet
          ∈ right
      -> schema.lookupField rightParentType rightFieldName = some rightFieldDefinition
      -> (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool schema
          = false
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
  intro hschema hleftValid hrightValid hleftCoercion hrightCoercion hleftFree
    hrightFree hleftNormal
    hrightNormal hleftObject hrightObject hleftFuel hrightFuel hleftSupport
    hrightSupport hleftContext hrightContext hrightMem hrightLookup hrightLeaf
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
        responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_leaf_field_pair_of_valid_normal_support_context_fuel_ge_fuels
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet leftCurrentSelectionSet
          rightCurrentSelectionSet variableValues leftFuel rightFuel
          targetParent leftProbeField rightProbeField leftParentType
          rightParentType targetLeftArguments targetRightArguments
          leftRuntime rightRuntime hschema hleftValid hrightValid
          hleftCoercion hrightCoercion hleftFree hrightFree hleftNormal
          hrightNormal hleftObject
          hrightObject hleftFuel hrightFuel hleftSupport hrightSupport
          hleftContext hrightContext hleftMem hrightMem hleftLookup
          hrightLookup hleftLeaf hrightLeaf
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
      exact
        responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_left_composite_right_leaf_field_pair_of_valid_normal_support_context_fuel_ge_fuels
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet leftCurrentSelectionSet
          rightCurrentSelectionSet variableValues leftFuel rightFuel
          targetParent leftProbeField rightProbeField leftParentType
          rightParentType targetLeftArguments targetRightArguments
          leftRuntime rightRuntime hschema hleftValid hrightValid
          hleftCoercion hrightCoercion hleftFree hrightFree hleftNormal
          hrightNormal hleftObject
          hrightObject hleftFuel hrightFuel hleftSupport hrightSupport
          hleftContext hrightContext hleftMem hrightMem hleftLookup
          hrightLookup hleftComposite hrightLeaf
  · exact
      responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_right_responseName_diff_of_valid_normal_support_context_fuel_ge_fuels
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftCurrentSelectionSet
        rightCurrentSelectionSet variableValues leftFuel rightFuel
        targetParent leftProbeField rightProbeField leftParentType
        rightParentType targetLeftArguments targetRightArguments
        leftRuntime rightRuntime hschema hleftValid hrightValid hleftCoercion
        hrightCoercion hleftFree hrightFree hleftNormal hrightNormal hleftObject
        hrightObject
        hleftFuel hrightFuel hleftSupport hrightSupport hleftContext
        hrightContext hrightMem hleftResponseName

end GroundTypeNormalization

end NormalForm

end GraphQL
