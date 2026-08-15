import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.SyntaxDiff
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.FocusedPathProbe

/-!
Selected-path witnesses, parent lifts, and execution-context foundations.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

def SelectedPathTaggedSelectionSetsResponseDiffWitness
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (normalParentType runtimeType targetParent leftField rightField : Name)
    (leftArguments rightArguments : List Argument)
    (leftRuntime rightRuntime : Name)
    (leftCurrentSelectionSet rightCurrentSelectionSet : List Selection)
    (leftSpine rightSpine : List NormalSelectionSetObservableFieldStep)
    (leftSelectionSet rightSelectionSet : List Selection)
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
          leftSelectionSet
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
          rightSelectionSet
        = ({ data := Execution.ResponseValue.object rightFields, errors := rightErrors }
            : Execution.Response)
      ∧ ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.ResponseValue.object leftFields)
            (Execution.ResponseValue.object rightFields)

theorem
    responseData_not_semanticEquivalent_of_selectedPathTaggedSelectionSetsResponseDiffWitness
    {schema : Schema}
    {rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection}
    {leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep}
    {variableValues : Execution.VariableValues} {fuel : Nat}
    {normalParentType runtimeType targetParent leftField rightField : Name}
    {leftArguments rightArguments : List Argument} {leftRuntime rightRuntime : Name}
    {leftCurrentSelectionSet rightCurrentSelectionSet : List Selection}
    {leftSpine rightSpine : List NormalSelectionSetObservableFieldStep}
    {leftSelectionSet rightSelectionSet : List Selection}
    : SelectedPathTaggedSelectionSetsResponseDiffWitness schema
        rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
        leftInitialSpine rightInitialSpine variableValues fuel
        normalParentType runtimeType targetParent leftField rightField
        leftArguments rightArguments leftRuntime rightRuntime
        leftCurrentSelectionSet rightCurrentSelectionSet leftSpine rightSpine
        leftSelectionSet rightSelectionSet
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
              leftSelectionSet).data
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
              rightSelectionSet).data := by
  intro hwitness hsemantic
  rcases hwitness with
    ⟨_hinclude, leftFields, leftErrors, rightFields, rightErrors,
      hleft, hright, hnot⟩
  exact hnot (by simpa [hleft, hright] using hsemantic)

def SelectedPathTaggedSelectionSetsRightPrunedResponseDiffWitness
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (normalParentType runtimeType targetParent leftField rightField : Name)
    (leftArguments rightArguments : List Argument)
    (leftRuntime rightRuntime : Name)
    (leftCurrentSelectionSet rightCurrentSelectionSet : List Selection)
    (leftSpine rightSpine : List NormalSelectionSetObservableFieldStep)
    (leftSelectionSet rightSelectionSet : List Selection)
    : Prop :=
  schema.typeIncludesObjectBool normalParentType runtimeType = true
  ∧ ∃ leftFields leftErrors,
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
          leftSelectionSet
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
          rightSelectionSet
        = ({ data := Execution.ResponseValue.object [], errors := 0 }
            : Execution.Response)
      ∧ ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.ResponseValue.object leftFields)
            (Execution.ResponseValue.object [])

def SelectedPathTaggedSelectionSetsLeftPrunedResponseDiffWitness
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (normalParentType runtimeType targetParent leftField rightField : Name)
    (leftArguments rightArguments : List Argument)
    (leftRuntime rightRuntime : Name)
    (leftCurrentSelectionSet rightCurrentSelectionSet : List Selection)
    (leftSpine rightSpine : List NormalSelectionSetObservableFieldStep)
    (leftSelectionSet rightSelectionSet : List Selection)
    : Prop :=
  schema.typeIncludesObjectBool normalParentType runtimeType = true
  ∧ ∃ rightFields rightErrors,
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
          leftSelectionSet
        = ({ data := Execution.ResponseValue.object [], errors := 0 }
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
          rightSelectionSet
        = ({ data := Execution.ResponseValue.object rightFields, errors := rightErrors }
            : Execution.Response)
      ∧ ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.ResponseValue.object [])
            (Execution.ResponseValue.object rightFields)

theorem
    responseData_not_semanticEquivalent_of_selectedPathTaggedSelectionSetsRightPrunedResponseDiffWitness
    {schema : Schema}
    {rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection}
    {leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep}
    {variableValues : Execution.VariableValues} {fuel : Nat}
    {normalParentType runtimeType targetParent leftField rightField : Name}
    {leftArguments rightArguments : List Argument} {leftRuntime rightRuntime : Name}
    {leftCurrentSelectionSet rightCurrentSelectionSet : List Selection}
    {leftSpine rightSpine : List NormalSelectionSetObservableFieldStep}
    {leftSelectionSet rightSelectionSet : List Selection}
    : SelectedPathTaggedSelectionSetsRightPrunedResponseDiffWitness schema
        rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
        leftInitialSpine rightInitialSpine variableValues fuel
        normalParentType runtimeType targetParent leftField rightField
        leftArguments rightArguments leftRuntime rightRuntime
        leftCurrentSelectionSet rightCurrentSelectionSet leftSpine rightSpine
        leftSelectionSet rightSelectionSet
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
              leftSelectionSet).data
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
              rightSelectionSet).data := by
  intro hwitness hsemantic
  rcases hwitness with
    ⟨_hinclude, leftFields, leftErrors, hleft, hright, hnot⟩
  exact hnot (by simpa [hleft, hright] using hsemantic)

theorem
    responseData_not_semanticEquivalent_of_selectedPathTaggedSelectionSetsLeftPrunedResponseDiffWitness
    {schema : Schema}
    {rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection}
    {leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep}
    {variableValues : Execution.VariableValues} {fuel : Nat}
    {normalParentType runtimeType targetParent leftField rightField : Name}
    {leftArguments rightArguments : List Argument} {leftRuntime rightRuntime : Name}
    {leftCurrentSelectionSet rightCurrentSelectionSet : List Selection}
    {leftSpine rightSpine : List NormalSelectionSetObservableFieldStep}
    {leftSelectionSet rightSelectionSet : List Selection}
    : SelectedPathTaggedSelectionSetsLeftPrunedResponseDiffWitness schema
        rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
        leftInitialSpine rightInitialSpine variableValues fuel
        normalParentType runtimeType targetParent leftField rightField
        leftArguments rightArguments leftRuntime rightRuntime
        leftCurrentSelectionSet rightCurrentSelectionSet leftSpine rightSpine
        leftSelectionSet rightSelectionSet
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
              leftSelectionSet).data
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
              rightSelectionSet).data := by
  intro hwitness hsemantic
  rcases hwitness with
    ⟨_hinclude, rightFields, rightErrors, hleft, hright, hnot⟩
  exact hnot (by simpa [hleft, hright] using hsemantic)

theorem selectedPathTaggedSelectionSetsResponseDiffWitness_of_rightPruned
    {schema : Schema}
    {rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection}
    {leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep}
    {variableValues : Execution.VariableValues} {fuel : Nat}
    {normalParentType runtimeType targetParent leftField rightField : Name}
    {leftArguments rightArguments : List Argument}
    {leftRuntime rightRuntime : Name}
    {leftCurrentSelectionSet rightCurrentSelectionSet : List Selection}
    {leftSpine rightSpine : List NormalSelectionSetObservableFieldStep}
    {leftSelectionSet rightSelectionSet : List Selection}
    : SelectedPathTaggedSelectionSetsRightPrunedResponseDiffWitness schema
        rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
        leftInitialSpine rightInitialSpine variableValues fuel
        normalParentType runtimeType targetParent leftField rightField
        leftArguments rightArguments leftRuntime rightRuntime
        leftCurrentSelectionSet rightCurrentSelectionSet leftSpine rightSpine
        leftSelectionSet rightSelectionSet
      -> SelectedPathTaggedSelectionSetsResponseDiffWitness schema
          rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
          leftInitialSpine rightInitialSpine variableValues fuel
          normalParentType runtimeType targetParent leftField rightField
          leftArguments rightArguments leftRuntime rightRuntime
          leftCurrentSelectionSet rightCurrentSelectionSet leftSpine
          rightSpine leftSelectionSet rightSelectionSet := by
  intro hwitness
  rcases hwitness with
    ⟨hinclude, leftFields, leftErrors, hleftResponse, hrightResponse,
      hnot⟩
  exact ⟨hinclude, leftFields, leftErrors, [], 0, hleftResponse, hrightResponse, hnot⟩

theorem selectedPathTaggedSelectionSetsResponseDiffWitness_of_leftPruned
    {schema : Schema}
    {rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection}
    {leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep}
    {variableValues : Execution.VariableValues} {fuel : Nat}
    {normalParentType runtimeType targetParent leftField rightField : Name}
    {leftArguments rightArguments : List Argument}
    {leftRuntime rightRuntime : Name}
    {leftCurrentSelectionSet rightCurrentSelectionSet : List Selection}
    {leftSpine rightSpine : List NormalSelectionSetObservableFieldStep}
    {leftSelectionSet rightSelectionSet : List Selection}
    : SelectedPathTaggedSelectionSetsLeftPrunedResponseDiffWitness schema
        rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
        leftInitialSpine rightInitialSpine variableValues fuel
        normalParentType runtimeType targetParent leftField rightField
        leftArguments rightArguments leftRuntime rightRuntime
        leftCurrentSelectionSet rightCurrentSelectionSet leftSpine rightSpine
        leftSelectionSet rightSelectionSet
      -> SelectedPathTaggedSelectionSetsResponseDiffWitness schema
          rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
          leftInitialSpine rightInitialSpine variableValues fuel
          normalParentType runtimeType targetParent leftField rightField
          leftArguments rightArguments leftRuntime rightRuntime
          leftCurrentSelectionSet rightCurrentSelectionSet leftSpine
          rightSpine leftSelectionSet rightSelectionSet := by
  intro hwitness
  rcases hwitness with
    ⟨hinclude, rightFields, rightErrors, hleftResponse, hrightResponse,
      hnot⟩
  exact ⟨hinclude, [], 0, rightFields, rightErrors, hleftResponse, hrightResponse, hnot⟩

theorem
    not_selectionSetsDataEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_root_arguments_childWitness_of_field_ok
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (parentFuel : Nat)
    (parentType responseName fieldName : Name)
    (leftArguments rightArguments : List Argument) (runtimeType : Name)
    {left right : List Selection}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
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
      -> leafProbeFuel fieldDefinition.outputType ≤ parentFuel
      -> ¬ Argument.argumentsEquivalent leftArguments rightArguments
      -> SelectedPathTaggedSelectionSetsResponseDiffWitness schema
          rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
          leftInitialSpine rightInitialSpine variableValues
          (parentFuel - leafProbeFuel fieldDefinition.outputType)
          fieldDefinition.outputType.namedType runtimeType parentType fieldName
          fieldName leftArguments rightArguments runtimeType runtimeType
          leftInitialSelectionSet rightInitialSelectionSet leftInitialSpine
          rightInitialSpine leftChildSelectionSet rightChildSelectionSet
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
                      fieldName leftArguments rightArguments runtimeType runtimeType)
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
                      fieldName leftArguments rightArguments runtimeType runtimeType)
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
                = .ok ([(responseName, responseValue)], fieldErrors))
      -> ¬ selectionSetsDataEquivalent schema parentType left right := by
  intro hobject hleftNormal hrightNormal hleftFree hrightFree hleftMem
    hrightMem hlookup hfuel hargumentsDiff hchildWitness hleftFieldOk
    hrightFieldOk
  rcases hchildWitness with
    ⟨hinclude, leftChildFields, leftChildErrors, rightChildFields,
      rightChildErrors, hleftChildResponse, hrightChildResponse,
      hchildNot⟩
  exact
    not_selectionSetsDataEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_root_arguments_child_response_diff_of_field_ok
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet leftInitialSpine rightInitialSpine
      variableValues parentFuel parentType responseName fieldName
      leftArguments rightArguments runtimeType runtimeType hobject
      hleftNormal hrightNormal hleftFree hrightFree hleftMem hrightMem
      hlookup hinclude hinclude hfuel hargumentsDiff hleftChildResponse
      hrightChildResponse hchildNot hleftFieldOk hrightFieldOk

theorem
    not_selectionSetsDataEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_root_arguments_childWitness_of_valid_normal_append_context
    {schema : Schema}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    {parentType responseName fieldName runtimeType : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet left right : List Selection}
    {fieldDefinition : FieldDefinition}
    (leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues)
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions parentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
      -> selectionSetDirectiveFree left
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
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType runtimeType
          = true
      -> SelectedFieldSpineRuntimeValid schema
          fieldDefinition.outputType.namedType runtimeType leftInitialSpine
      -> SelectedFieldSpineRuntimeValid schema
          fieldDefinition.outputType.namedType runtimeType rightInitialSpine
      -> ¬ Argument.argumentsEquivalent leftArguments rightArguments
      -> SelectedPathTaggedSelectionSetsResponseDiffWitness schema
          [Selection.inlineFragment (some parentType) [] (left ++ right)]
          (fieldPairPathLocalNextSelectionSet schema parentType runtimeType
            fieldName leftArguments (left ++ right))
          (fieldPairPathLocalNextSelectionSet schema parentType runtimeType
            fieldName rightArguments (left ++ right))
          leftInitialSpine rightInitialSpine variableValues
          (selectionSetDeepProbeFuel schema parentType (left ++ right)
            - leafProbeFuel fieldDefinition.outputType)
          fieldDefinition.outputType.namedType runtimeType parentType fieldName
          fieldName leftArguments rightArguments runtimeType runtimeType
          (fieldPairPathLocalNextSelectionSet schema parentType runtimeType
            fieldName leftArguments (left ++ right))
          (fieldPairPathLocalNextSelectionSet schema parentType runtimeType
            fieldName rightArguments (left ++ right))
          leftInitialSpine rightInitialSpine leftChildSelectionSet
          rightChildSelectionSet
      -> ¬ selectionSetsDataEquivalent schema parentType left right := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hobject hleftMem hrightMem hlookup hcomposite hinclude
    hleftSpineValid hrightSpineValid hargumentsDiff hchildWitness
  let parentFuel := selectionSetDeepProbeFuel schema parentType (left ++ right)
  let rootSelectionSet : List Selection :=
    [Selection.inlineFragment (some parentType) [] (left ++ right)]
  let leftInitialSelectionSet : List Selection :=
    fieldPairPathLocalNextSelectionSet schema parentType runtimeType
      fieldName leftArguments (left ++ right)
  let rightInitialSelectionSet : List Selection :=
    fieldPairPathLocalNextSelectionSet schema parentType runtimeType
      fieldName rightArguments (left ++ right)
  have hleftFuel :
      selectionSetDeepProbeFuel schema parentType left ≤ parentFuel := by
    have hlocal := selectionSetDeepProbeFuel_le_append_left
      schema parentType left right
    dsimp [parentFuel]
    omega
  have hrightFuel :
      selectionSetDeepProbeFuel schema parentType right ≤ parentFuel := by
    have hlocal := selectionSetDeepProbeFuel_le_append_right
      schema parentType left right
    dsimp [parentFuel]
    omega
  have hleafFuel :
      leafProbeFuel fieldDefinition.outputType ≤ parentFuel := by
    have hlocal :=
      leafProbeFuel_le_selectionSetDeepProbeFuel_of_field_mem schema
        parentType (selectionSet := left ++ right)
        (responseName := responseName) (fieldName := fieldName)
        (arguments := leftArguments) (directives := leftDirectives)
        (childSelectionSet := leftChildSelectionSet)
        (fieldDefinition := fieldDefinition)
        (List.mem_append_left right hleftMem) hlookup
    dsimp [parentFuel]
    omega
  have hsupport :
      PathLocalSupportValidNormal schema parentType (left ++ right) :=
    PathLocalSupportValidNormal.append
      (PathLocalSupportValidNormal.of_valid_normal_self hleftValid
        hleftFree hleftNormal)
      (PathLocalSupportValidNormal.of_valid_normal_self hrightValid
        hrightFree hrightNormal)
  have hleftContext :
      PathLocalSelectionSetCurrentContext left (left ++ right) :=
    ⟨[], right, by simp⟩
  have hrightContext :
      PathLocalSelectionSetCurrentContext right (left ++ right) :=
    ⟨left, [], by simp⟩
  have hchildWitness' :
      SelectedPathTaggedSelectionSetsResponseDiffWitness schema
        rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
        leftInitialSpine rightInitialSpine variableValues
        (parentFuel - leafProbeFuel fieldDefinition.outputType)
        fieldDefinition.outputType.namedType runtimeType parentType fieldName
        fieldName leftArguments rightArguments runtimeType runtimeType
        leftInitialSelectionSet rightInitialSelectionSet leftInitialSpine
        rightInitialSpine leftChildSelectionSet rightChildSelectionSet := by
    simpa [rootSelectionSet, leftInitialSelectionSet,
      rightInitialSelectionSet, parentFuel] using hchildWitness
  rcases hchildWitness' with
    ⟨_hchildInclude, leftChildFields, leftChildErrors,
      rightChildFields, rightChildErrors, hleftChildResponse,
      hrightChildResponse, hchildNot⟩
  have hleftLeftTarget :
      ∀ currentResponseName arguments directives childSelectionSet,
        Selection.field currentResponseName fieldName arguments directives
            childSelectionSet ∈ left ->
        Argument.argumentsEquivalent arguments leftArguments ->
          ∃ childFields childErrors,
            Execution.executeSelectionSetAsResponse schema
                (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                  (fieldPairSelectedPathProbeResolvers schema
                    leftInitialSelectionSet rightInitialSelectionSet
                    leftInitialSpine rightInitialSpine parentType fieldName
                    fieldName leftArguments rightArguments runtimeType
                    runtimeType)
                  parentType fieldName fieldName leftArguments rightArguments)
                variableValues
                (parentFuel - leafProbeFuel fieldDefinition.outputType)
                runtimeType
                (projectionTargetResolverValue
                  (.object runtimeType
                    (FieldPairSelectedPathProbeRef.target
                      FieldPairProbeTag.left leftInitialSelectionSet
                      leftInitialSpine)))
                childSelectionSet =
              ({ data := Execution.ResponseValue.object childFields,
                 errors := childErrors } : Execution.Response) := by
    intro currentResponseName arguments directives childSelectionSet hmem
      harguments
    have hfieldDeepFuel :
        leafProbeFuel fieldDefinition.outputType
          + selectionSetDeepProbeFuel schema
            fieldDefinition.outputType.namedType childSelectionSet
          + 1 ≤ parentFuel := by
      have hlocal :=
        selectionSetDeepProbeFuel_field_mem schema parentType left
          currentResponseName fieldName arguments directives childSelectionSet
          fieldDefinition hmem hlookup
      omega
    let childFuel := parentFuel - leafProbeFuel fieldDefinition.outputType - 1
    have hchildFuel :
        selectionSetDeepProbeFuel schema
            fieldDefinition.outputType.namedType childSelectionSet ≤
          childFuel := by
      dsimp [childFuel]
      omega
    rcases
        executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_argument_target_child_of_valid_normal_support_context_field_mem
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet leftInitialSpine rightInitialSpine
          variableValues hschema (parentType := parentType)
          (variableDefinitions := leftVariableDefinitions)
          (selectionSet := left) (currentSelectionSet := left ++ right)
          (fuel := childFuel) (responseName := currentResponseName)
          (fieldName := fieldName) (runtimeType := runtimeType)
          (targetArguments := leftArguments)
          (leftArguments := leftArguments)
          (rightArguments := rightArguments) (arguments := arguments)
          (directives := directives) (childSelectionSet := childSelectionSet)
          (fieldDefinition := fieldDefinition) (spine := leftInitialSpine)
          (tag := FieldPairProbeTag.left) hleftValid hleftFree hleftNormal
          hobject hsupport hleftContext hmem harguments hlookup hcomposite
          hinclude hleftSpineValid hchildFuel with
      ⟨childFields, childErrors, hresponse⟩
    refine ⟨childFields, childErrors, ?_⟩
    have hfuelEq :
        childFuel + 1 =
          parentFuel - leafProbeFuel fieldDefinition.outputType := by
      dsimp [childFuel]
      omega
    simpa [leftInitialSelectionSet, hfuelEq] using hresponse
  have hleftRightTarget :
      ∀ currentResponseName arguments directives childSelectionSet,
        Selection.field currentResponseName fieldName arguments directives
            childSelectionSet ∈ left ->
        Argument.argumentsEquivalent arguments rightArguments ->
          ∃ childFields childErrors,
            Execution.executeSelectionSetAsResponse schema
                (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                  (fieldPairSelectedPathProbeResolvers schema
                    leftInitialSelectionSet rightInitialSelectionSet
                    leftInitialSpine rightInitialSpine parentType fieldName
                    fieldName leftArguments rightArguments runtimeType
                    runtimeType)
                  parentType fieldName fieldName leftArguments rightArguments)
                variableValues
                (parentFuel - leafProbeFuel fieldDefinition.outputType)
                runtimeType
                (projectionTargetResolverValue
                  (.object runtimeType
                    (FieldPairSelectedPathProbeRef.target
                      FieldPairProbeTag.right rightInitialSelectionSet
                      rightInitialSpine)))
                childSelectionSet =
              ({ data := Execution.ResponseValue.object childFields,
                 errors := childErrors } : Execution.Response) := by
    intro currentResponseName arguments directives childSelectionSet hmem
      harguments
    have hfieldDeepFuel :
        leafProbeFuel fieldDefinition.outputType
          + selectionSetDeepProbeFuel schema
            fieldDefinition.outputType.namedType childSelectionSet
          + 1 ≤ parentFuel := by
      have hlocal :=
        selectionSetDeepProbeFuel_field_mem schema parentType left
          currentResponseName fieldName arguments directives childSelectionSet
          fieldDefinition hmem hlookup
      omega
    let childFuel := parentFuel - leafProbeFuel fieldDefinition.outputType - 1
    have hchildFuel :
        selectionSetDeepProbeFuel schema
            fieldDefinition.outputType.namedType childSelectionSet ≤
          childFuel := by
      dsimp [childFuel]
      omega
    rcases
        executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_argument_target_child_of_valid_normal_support_context_field_mem
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet leftInitialSpine rightInitialSpine
          variableValues hschema (parentType := parentType)
          (variableDefinitions := leftVariableDefinitions)
          (selectionSet := left) (currentSelectionSet := left ++ right)
          (fuel := childFuel) (responseName := currentResponseName)
          (fieldName := fieldName) (runtimeType := runtimeType)
          (targetArguments := rightArguments)
          (leftArguments := leftArguments)
          (rightArguments := rightArguments) (arguments := arguments)
          (directives := directives) (childSelectionSet := childSelectionSet)
          (fieldDefinition := fieldDefinition) (spine := rightInitialSpine)
          (tag := FieldPairProbeTag.right) hleftValid hleftFree hleftNormal
          hobject hsupport hleftContext hmem harguments hlookup hcomposite
          hinclude hrightSpineValid hchildFuel with
      ⟨childFields, childErrors, hresponse⟩
    refine ⟨childFields, childErrors, ?_⟩
    have hfuelEq :
        childFuel + 1 =
          parentFuel - leafProbeFuel fieldDefinition.outputType := by
      dsimp [childFuel]
      omega
    simpa [rightInitialSelectionSet, hfuelEq] using hresponse
  have hrightLeftTarget :
      ∀ currentResponseName arguments directives childSelectionSet,
        Selection.field currentResponseName fieldName arguments directives
            childSelectionSet ∈ right ->
        Argument.argumentsEquivalent arguments leftArguments ->
          ∃ childFields childErrors,
            Execution.executeSelectionSetAsResponse schema
                (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                  (fieldPairSelectedPathProbeResolvers schema
                    leftInitialSelectionSet rightInitialSelectionSet
                    leftInitialSpine rightInitialSpine parentType fieldName
                    fieldName leftArguments rightArguments runtimeType
                    runtimeType)
                  parentType fieldName fieldName leftArguments rightArguments)
                variableValues
                (parentFuel - leafProbeFuel fieldDefinition.outputType)
                runtimeType
                (projectionTargetResolverValue
                  (.object runtimeType
                    (FieldPairSelectedPathProbeRef.target
                      FieldPairProbeTag.left leftInitialSelectionSet
                      leftInitialSpine)))
                childSelectionSet =
              ({ data := Execution.ResponseValue.object childFields,
                 errors := childErrors } : Execution.Response) := by
    intro currentResponseName arguments directives childSelectionSet hmem
      harguments
    have hfieldDeepFuel :
        leafProbeFuel fieldDefinition.outputType
          + selectionSetDeepProbeFuel schema
            fieldDefinition.outputType.namedType childSelectionSet
          + 1 ≤ parentFuel := by
      have hlocal :=
        selectionSetDeepProbeFuel_field_mem schema parentType right
          currentResponseName fieldName arguments directives childSelectionSet
          fieldDefinition hmem hlookup
      omega
    let childFuel := parentFuel - leafProbeFuel fieldDefinition.outputType - 1
    have hchildFuel :
        selectionSetDeepProbeFuel schema
            fieldDefinition.outputType.namedType childSelectionSet ≤
          childFuel := by
      dsimp [childFuel]
      omega
    rcases
        executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_argument_target_child_of_valid_normal_support_context_field_mem
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet leftInitialSpine rightInitialSpine
          variableValues hschema (parentType := parentType)
          (variableDefinitions := rightVariableDefinitions)
          (selectionSet := right) (currentSelectionSet := left ++ right)
          (fuel := childFuel) (responseName := currentResponseName)
          (fieldName := fieldName) (runtimeType := runtimeType)
          (targetArguments := leftArguments)
          (leftArguments := leftArguments)
          (rightArguments := rightArguments) (arguments := arguments)
          (directives := directives) (childSelectionSet := childSelectionSet)
          (fieldDefinition := fieldDefinition) (spine := leftInitialSpine)
          (tag := FieldPairProbeTag.left) hrightValid hrightFree
          hrightNormal hobject hsupport hrightContext hmem harguments hlookup
          hcomposite hinclude hleftSpineValid hchildFuel with
      ⟨childFields, childErrors, hresponse⟩
    refine ⟨childFields, childErrors, ?_⟩
    have hfuelEq :
        childFuel + 1 =
          parentFuel - leafProbeFuel fieldDefinition.outputType := by
      dsimp [childFuel]
      omega
    simpa [leftInitialSelectionSet, hfuelEq] using hresponse
  have hrightRightTarget :
      ∀ currentResponseName arguments directives childSelectionSet,
        Selection.field currentResponseName fieldName arguments directives
            childSelectionSet ∈ right ->
        Argument.argumentsEquivalent arguments rightArguments ->
          ∃ childFields childErrors,
            Execution.executeSelectionSetAsResponse schema
                (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                  (fieldPairSelectedPathProbeResolvers schema
                    leftInitialSelectionSet rightInitialSelectionSet
                    leftInitialSpine rightInitialSpine parentType fieldName
                    fieldName leftArguments rightArguments runtimeType
                    runtimeType)
                  parentType fieldName fieldName leftArguments rightArguments)
                variableValues
                (parentFuel - leafProbeFuel fieldDefinition.outputType)
                runtimeType
                (projectionTargetResolverValue
                  (.object runtimeType
                    (FieldPairSelectedPathProbeRef.target
                      FieldPairProbeTag.right rightInitialSelectionSet
                      rightInitialSpine)))
                childSelectionSet =
              ({ data := Execution.ResponseValue.object childFields,
                 errors := childErrors } : Execution.Response) := by
    intro currentResponseName arguments directives childSelectionSet hmem
      harguments
    have hfieldDeepFuel :
        leafProbeFuel fieldDefinition.outputType
          + selectionSetDeepProbeFuel schema
            fieldDefinition.outputType.namedType childSelectionSet
          + 1 ≤ parentFuel := by
      have hlocal :=
        selectionSetDeepProbeFuel_field_mem schema parentType right
          currentResponseName fieldName arguments directives childSelectionSet
          fieldDefinition hmem hlookup
      omega
    let childFuel := parentFuel - leafProbeFuel fieldDefinition.outputType - 1
    have hchildFuel :
        selectionSetDeepProbeFuel schema
            fieldDefinition.outputType.namedType childSelectionSet ≤
          childFuel := by
      dsimp [childFuel]
      omega
    rcases
        executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_argument_target_child_of_valid_normal_support_context_field_mem
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet leftInitialSpine rightInitialSpine
          variableValues hschema (parentType := parentType)
          (variableDefinitions := rightVariableDefinitions)
          (selectionSet := right) (currentSelectionSet := left ++ right)
          (fuel := childFuel) (responseName := currentResponseName)
          (fieldName := fieldName) (runtimeType := runtimeType)
          (targetArguments := rightArguments)
          (leftArguments := leftArguments)
          (rightArguments := rightArguments) (arguments := arguments)
          (directives := directives) (childSelectionSet := childSelectionSet)
          (fieldDefinition := fieldDefinition) (spine := rightInitialSpine)
          (tag := FieldPairProbeTag.right) hrightValid hrightFree
          hrightNormal hobject hsupport hrightContext hmem harguments hlookup
          hcomposite hinclude hrightSpineValid hchildFuel with
      ⟨childFields, childErrors, hresponse⟩
    refine ⟨childFields, childErrors, ?_⟩
    have hfuelEq :
        childFuel + 1 =
          parentFuel - leafProbeFuel fieldDefinition.outputType := by
      dsimp [childFuel]
      omega
    simpa [rightInitialSelectionSet, hfuelEq] using hresponse
  have hleftDeep :
      ∀ currentResponseName siblingFieldName arguments directives childSelectionSet,
        Selection.field currentResponseName siblingFieldName arguments directives
            childSelectionSet ∈ left ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema
              (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet
                (ProjectionResolverRef.filler :
                  ProjectionResolverRef FieldPairSelectedPathProbeRef))
              variableValues (parentFuel + 1)
              (projectionRootResolverValue
                (.object parentType FieldPairSelectedPathProbeRef.root))
              currentResponseName
              [{
                parentType := parentType,
                responseName := currentResponseName,
                fieldName := siblingFieldName,
                arguments := arguments,
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(currentResponseName, responseValue)], fieldErrors) := by
    intro currentResponseName siblingFieldName arguments directives
      childSelectionSet hmem
    simpa [rootSelectionSet, parentFuel] using
      left_selectionSet_deepSuccessFieldOk_append_framed_of_valid_normal_fuel_ge
        (schema := schema) (parentType := parentType)
        (left := left) (right := right)
        (leftVariableDefinitions := leftVariableDefinitions)
        (rightVariableDefinitions := rightVariableDefinitions)
        (ProjectionResolverRef.filler :
          ProjectionResolverRef FieldPairSelectedPathProbeRef)
        variableValues
        (projectionRootResolverValue
          (.object parentType FieldPairSelectedPathProbeRef.root))
        parentFuel hschema hleftValid hrightValid hleftFree hrightFree
        hleftNormal hrightNormal hobject (by simp [parentFuel])
        currentResponseName siblingFieldName arguments directives
        childSelectionSet hmem
  have hrightDeep :
      ∀ currentResponseName siblingFieldName arguments directives childSelectionSet,
        Selection.field currentResponseName siblingFieldName arguments directives
            childSelectionSet ∈ right ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema
              (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet
                (ProjectionResolverRef.filler :
                  ProjectionResolverRef FieldPairSelectedPathProbeRef))
              variableValues (parentFuel + 1)
              (projectionRootResolverValue
                (.object parentType FieldPairSelectedPathProbeRef.root))
              currentResponseName
              [{
                parentType := parentType,
                responseName := currentResponseName,
                fieldName := siblingFieldName,
                arguments := arguments,
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(currentResponseName, responseValue)], fieldErrors) := by
    intro currentResponseName siblingFieldName arguments directives
      childSelectionSet hmem
    simpa [rootSelectionSet, parentFuel] using
      right_selectionSet_deepSuccessFieldOk_append_framed_of_valid_normal_fuel_ge
        (schema := schema) (parentType := parentType)
        (left := left) (right := right)
        (leftVariableDefinitions := leftVariableDefinitions)
        (rightVariableDefinitions := rightVariableDefinitions)
        (ProjectionResolverRef.filler :
          ProjectionResolverRef FieldPairSelectedPathProbeRef)
        variableValues
        (projectionRootResolverValue
          (.object parentType FieldPairSelectedPathProbeRef.root))
        parentFuel hschema hleftValid hrightValid hleftFree hrightFree
        hleftNormal hrightNormal hobject (by simp [parentFuel])
        currentResponseName siblingFieldName arguments directives
        childSelectionSet hmem
  exact
    not_selectionSetsDataEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_root_arguments_child_response_diff_of_field_cases
      schema rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftInitialSpine rightInitialSpine variableValues parentFuel
      parentType responseName fieldName leftArguments rightArguments
      runtimeType runtimeType hobject hleftNormal hrightNormal hleftFree
      hrightFree hleftMem hrightMem hlookup hinclude hinclude hleafFuel
      hargumentsDiff hleftChildResponse hrightChildResponse hchildNot
      hleftLeftTarget hleftRightTarget hrightLeftTarget hrightRightTarget
      hleftDeep hrightDeep

theorem
    not_selectionSetsDataEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_root_arguments_object_output_childDataNot_of_valid_normal_append_context
    {schema : Schema}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    {parentType responseName fieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet left right : List Selection}
    {fieldDefinition : FieldDefinition}
    (leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues)
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions parentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
      -> selectionSetDirectiveFree left
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
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> objectTypeNameBool schema fieldDefinition.outputType.namedType = true
      -> SelectedFieldSpineRuntimeValid schema
          fieldDefinition.outputType.namedType
          fieldDefinition.outputType.namedType leftInitialSpine
      -> SelectedFieldSpineRuntimeValid schema
          fieldDefinition.outputType.namedType
          fieldDefinition.outputType.namedType rightInitialSpine
      -> ¬ Argument.argumentsEquivalent leftArguments rightArguments
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema
                [Selection.inlineFragment (some parentType) [] (left ++ right)]
                (fieldPairSelectedPathProbeResolvers schema
                  (fieldPairPathLocalNextSelectionSet schema parentType
                    fieldDefinition.outputType.namedType fieldName leftArguments
                    (left ++ right))
                  (fieldPairPathLocalNextSelectionSet schema parentType
                    fieldDefinition.outputType.namedType fieldName rightArguments
                    (left ++ right))
                  leftInitialSpine rightInitialSpine parentType fieldName
                  fieldName leftArguments rightArguments
                  fieldDefinition.outputType.namedType
                  fieldDefinition.outputType.namedType)
                parentType fieldName fieldName leftArguments rightArguments)
              variableValues
              (selectionSetDeepProbeFuel schema parentType (left ++ right)
                - leafProbeFuel fieldDefinition.outputType)
              fieldDefinition.outputType.namedType
              (projectionTargetResolverValue
                (.object fieldDefinition.outputType.namedType
                  (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
                    (fieldPairPathLocalNextSelectionSet schema parentType
                      fieldDefinition.outputType.namedType fieldName leftArguments
                      (left ++ right))
                    leftInitialSpine)))
              leftChildSelectionSet).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema
                [Selection.inlineFragment (some parentType) [] (left ++ right)]
                (fieldPairSelectedPathProbeResolvers schema
                  (fieldPairPathLocalNextSelectionSet schema parentType
                    fieldDefinition.outputType.namedType fieldName leftArguments
                    (left ++ right))
                  (fieldPairPathLocalNextSelectionSet schema parentType
                    fieldDefinition.outputType.namedType fieldName rightArguments
                    (left ++ right))
                  leftInitialSpine rightInitialSpine parentType fieldName
                  fieldName leftArguments rightArguments
                  fieldDefinition.outputType.namedType
                  fieldDefinition.outputType.namedType)
                parentType fieldName fieldName leftArguments rightArguments)
              variableValues
              (selectionSetDeepProbeFuel schema parentType (left ++ right)
                - leafProbeFuel fieldDefinition.outputType)
              fieldDefinition.outputType.namedType
              (projectionTargetResolverValue
                (.object fieldDefinition.outputType.namedType
                  (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                    (fieldPairPathLocalNextSelectionSet schema parentType
                      fieldDefinition.outputType.namedType fieldName rightArguments
                      (left ++ right))
                    rightInitialSpine)))
              rightChildSelectionSet).data
      -> ¬ selectionSetsDataEquivalent schema parentType left right := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hobject hleftMem hrightMem hlookup hcomposite
    hobjectOutput hleftSpineValid hrightSpineValid hargumentsDiff
    hchildDataNot
  let parentFuel := selectionSetDeepProbeFuel schema parentType (left ++ right)
  let rootSelectionSet : List Selection :=
    [Selection.inlineFragment (some parentType) [] (left ++ right)]
  let leftInitialSelectionSet : List Selection :=
    fieldPairPathLocalNextSelectionSet schema parentType
      fieldDefinition.outputType.namedType fieldName leftArguments
      (left ++ right)
  let rightInitialSelectionSet : List Selection :=
    fieldPairPathLocalNextSelectionSet schema parentType
      fieldDefinition.outputType.namedType fieldName rightArguments
      (left ++ right)
  let childFuel := parentFuel - leafProbeFuel fieldDefinition.outputType - 1
  have hinclude :
      schema.typeIncludesObjectBool fieldDefinition.outputType.namedType
        fieldDefinition.outputType.namedType = true :=
    typeIncludesObjectBool_self_of_objectTypeNameBool schema hobjectOutput
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
  have hsupport :
      PathLocalSupportValidNormal schema parentType (left ++ right) :=
    PathLocalSupportValidNormal.append
      (PathLocalSupportValidNormal.of_valid_normal_self hleftValid
        hleftFree hleftNormal)
      (PathLocalSupportValidNormal.of_valid_normal_self hrightValid
        hrightFree hrightNormal)
  have hleftContext :
      PathLocalSelectionSetCurrentContext left (left ++ right) :=
    ⟨[], right, by simp⟩
  have hrightContext :
      PathLocalSelectionSetCurrentContext right (left ++ right) :=
    ⟨left, [], by simp⟩
  have hleftChildSupport :
      PathLocalSupportValidNormal schema fieldDefinition.outputType.namedType
        leftInitialSelectionSet :=
    hsupport.fieldPairPathLocalNextSelectionSet_of_object_output hobject
      hobjectOutput hlookup rfl
  have hrightChildSupport :
      PathLocalSupportValidNormal schema fieldDefinition.outputType.namedType
        rightInitialSelectionSet :=
    hsupport.fieldPairPathLocalNextSelectionSet_of_object_output hobject
      hobjectOutput hlookup rfl
  have hleftAllFields : selectionsAllFields leftChildSelectionSet :=
    selectionSetNormal_allFields_of_object hleftChildNormal hobjectOutput
  have hrightAllFields : selectionsAllFields rightChildSelectionSet :=
    selectionSetNormal_allFields_of_object hrightChildNormal hobjectOutput
  have hleftPruned :
      runtimePrunedSelectionSet schema fieldDefinition.outputType.namedType
          leftChildSelectionSet =
        leftChildSelectionSet :=
    runtimePrunedSelectionSet_eq_self_of_allFields schema
      fieldDefinition.outputType.namedType hleftAllFields
  have hrightPruned :
      runtimePrunedSelectionSet schema fieldDefinition.outputType.namedType
          rightChildSelectionSet =
        rightChildSelectionSet :=
    runtimePrunedSelectionSet_eq_self_of_allFields schema
      fieldDefinition.outputType.namedType hrightAllFields
  have hleftChildContext :
      PathLocalSelectionSetCurrentContext leftChildSelectionSet
        leftInitialSelectionSet :=
    PathLocalSelectionSetCurrentContext.fieldPairPathLocalNextSelectionSet_field_child
      (schema := schema) (currentRuntimeType := parentType)
      (childRuntimeType := fieldDefinition.outputType.namedType)
      (targetField := fieldName) (responseName := responseName)
      (targetArguments := leftArguments) (arguments := leftArguments)
      (directives := leftDirectives) (selectionSet := left)
      (childSelectionSet := leftChildSelectionSet)
      (currentSelectionSet := left ++ right) hleftContext hleftMem
      (argumentsEquivalent_refl_forSyntaxDiff leftArguments) hleftPruned
  have hrightChildContext :
      PathLocalSelectionSetCurrentContext rightChildSelectionSet
        rightInitialSelectionSet :=
    PathLocalSelectionSetCurrentContext.fieldPairPathLocalNextSelectionSet_field_child
      (schema := schema) (currentRuntimeType := parentType)
      (childRuntimeType := fieldDefinition.outputType.namedType)
      (targetField := fieldName) (responseName := responseName)
      (targetArguments := rightArguments) (arguments := rightArguments)
      (directives := rightDirectives) (selectionSet := right)
      (childSelectionSet := rightChildSelectionSet)
      (currentSelectionSet := left ++ right) hrightContext hrightMem
      (argumentsEquivalent_refl_forSyntaxDiff rightArguments) hrightPruned
  have hleftChildFuel :
      selectionSetDeepProbeFuel schema fieldDefinition.outputType.namedType
          leftChildSelectionSet ≤ childFuel := by
    have hlocal :=
      selectionSetDeepProbeFuel_field_mem schema parentType (left ++ right)
        responseName fieldName leftArguments leftDirectives
        leftChildSelectionSet fieldDefinition
        (List.mem_append_left right hleftMem) hlookup
    dsimp [childFuel, parentFuel]
    omega
  have hrightChildFuel :
      selectionSetDeepProbeFuel schema fieldDefinition.outputType.namedType
          rightChildSelectionSet ≤ childFuel := by
    have hlocal :=
      selectionSetDeepProbeFuel_field_mem schema parentType (left ++ right)
        responseName fieldName rightArguments rightDirectives
        rightChildSelectionSet fieldDefinition
        (List.mem_append_right left hrightMem) hlookup
    dsimp [childFuel, parentFuel]
    omega
  have hchildFuelEq :
      childFuel + 1 = parentFuel - leafProbeFuel fieldDefinition.outputType := by
    dsimp [childFuel, parentFuel]
    have hlocal :=
      selectionSetDeepProbeFuel_field_mem schema parentType (left ++ right)
        responseName fieldName leftArguments leftDirectives
        leftChildSelectionSet fieldDefinition
        (List.mem_append_left right hleftMem) hlookup
    omega
  rcases
      executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_of_valid_normal_runtimeSpine_support_context_fuel_ge_size
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftInitialSpine rightInitialSpine
        variableValues hschema (SelectionSet.size leftChildSelectionSet + 1)
        fieldDefinition.outputType.namedType leftVariableDefinitions
        leftChildSelectionSet childFuel
        fieldDefinition.outputType.namedType parentType fieldName fieldName
        leftArguments rightArguments fieldDefinition.outputType.namedType
        fieldDefinition.outputType.namedType FieldPairProbeTag.left
        leftInitialSelectionSet leftInitialSpine (by omega) hleftChildFuel
        hleftChildValid hleftChildFree hleftChildNormal hleftSpineValid
        hleftChildSupport (fun _hobject => hleftChildContext)
        (fun hnonObject => by
          rw [hobjectOutput] at hnonObject
          simp at hnonObject) with
    ⟨leftChildFields, leftChildErrors, hleftChildResponseRaw⟩
  rcases
      executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_of_valid_normal_runtimeSpine_support_context_fuel_ge_size
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftInitialSpine rightInitialSpine
        variableValues hschema (SelectionSet.size rightChildSelectionSet + 1)
        fieldDefinition.outputType.namedType rightVariableDefinitions
        rightChildSelectionSet childFuel
        fieldDefinition.outputType.namedType parentType fieldName fieldName
        leftArguments rightArguments fieldDefinition.outputType.namedType
        fieldDefinition.outputType.namedType FieldPairProbeTag.right
        rightInitialSelectionSet rightInitialSpine (by omega) hrightChildFuel
        hrightChildValid hrightChildFree hrightChildNormal hrightSpineValid
        hrightChildSupport (fun _hobject => hrightChildContext)
        (fun hnonObject => by
          rw [hobjectOutput] at hnonObject
          simp at hnonObject) with
    ⟨rightChildFields, rightChildErrors, hrightChildResponseRaw⟩
  have hleftChildResponse :
      Execution.executeSelectionSetAsResponse schema
          (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
            (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
              rightInitialSelectionSet leftInitialSpine rightInitialSpine
              parentType fieldName fieldName leftArguments rightArguments
              fieldDefinition.outputType.namedType
              fieldDefinition.outputType.namedType)
            parentType fieldName fieldName leftArguments rightArguments)
          variableValues
          (parentFuel - leafProbeFuel fieldDefinition.outputType)
          fieldDefinition.outputType.namedType
          (projectionTargetResolverValue
            (.object fieldDefinition.outputType.namedType
              (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
                leftInitialSelectionSet leftInitialSpine)))
          leftChildSelectionSet =
        ({ data := Execution.ResponseValue.object leftChildFields,
           errors := leftChildErrors } : Execution.Response) := by
    simpa [hchildFuelEq] using hleftChildResponseRaw
  have hrightChildResponse :
      Execution.executeSelectionSetAsResponse schema
          (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
            (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
              rightInitialSelectionSet leftInitialSpine rightInitialSpine
              parentType fieldName fieldName leftArguments rightArguments
              fieldDefinition.outputType.namedType
              fieldDefinition.outputType.namedType)
            parentType fieldName fieldName leftArguments rightArguments)
          variableValues
          (parentFuel - leafProbeFuel fieldDefinition.outputType)
          fieldDefinition.outputType.namedType
          (projectionTargetResolverValue
            (.object fieldDefinition.outputType.namedType
              (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                rightInitialSelectionSet rightInitialSpine)))
          rightChildSelectionSet =
        ({ data := Execution.ResponseValue.object rightChildFields,
           errors := rightChildErrors } : Execution.Response) := by
    simpa [hchildFuelEq] using hrightChildResponseRaw
  have hchildNot :
      ¬ Execution.ResponseValue.semanticEquivalent
        (Execution.ResponseValue.object leftChildFields)
        (Execution.ResponseValue.object rightChildFields) := by
    intro hsemantic
    apply hchildDataNot
    simpa [rootSelectionSet, leftInitialSelectionSet,
      rightInitialSelectionSet, parentFuel, hleftChildResponse,
      hrightChildResponse] using hsemantic
  have hchildWitness :
      SelectedPathTaggedSelectionSetsResponseDiffWitness schema
        rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
        leftInitialSpine rightInitialSpine variableValues
        (parentFuel - leafProbeFuel fieldDefinition.outputType)
        fieldDefinition.outputType.namedType
        fieldDefinition.outputType.namedType parentType fieldName fieldName
        leftArguments rightArguments fieldDefinition.outputType.namedType
        fieldDefinition.outputType.namedType leftInitialSelectionSet
        rightInitialSelectionSet leftInitialSpine rightInitialSpine
        leftChildSelectionSet rightChildSelectionSet :=
    ⟨hinclude, leftChildFields, leftChildErrors, rightChildFields,
      rightChildErrors, hleftChildResponse, hrightChildResponse,
      hchildNot⟩
  exact
    not_selectionSetsDataEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_root_arguments_childWitness_of_valid_normal_append_context
      (schema := schema)
      (leftVariableDefinitions := leftVariableDefinitions)
      (rightVariableDefinitions := rightVariableDefinitions)
      (parentType := parentType) (responseName := responseName)
      (fieldName := fieldName)
      (runtimeType := fieldDefinition.outputType.namedType)
      (leftArguments := leftArguments)
      (rightArguments := rightArguments)
      (leftDirectives := leftDirectives)
      (rightDirectives := rightDirectives)
      (leftChildSelectionSet := leftChildSelectionSet)
      (rightChildSelectionSet := rightChildSelectionSet)
      (left := left) (right := right)
      (fieldDefinition := fieldDefinition) leftInitialSpine
      rightInitialSpine variableValues hschema hleftValid hrightValid
      hleftFree hrightFree hleftNormal hrightNormal hobject hleftMem
      hrightMem hlookup hcomposite hinclude hleftSpineValid
      hrightSpineValid hargumentsDiff hchildWitness

theorem
    not_selectionSetsDataEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_root_fieldName_object_output_childDataNot_of_valid_normal_append_context
    {schema : Schema}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    {parentType responseName leftFieldName rightFieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet left right : List Selection}
    {leftFieldDefinition rightFieldDefinition : FieldDefinition}
    {leftRuntimeType rightRuntimeType : Name}
    (leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues)
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions parentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> objectTypeNameBool schema parentType = true
      -> Selection.field responseName leftFieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName rightFieldName rightArguments rightDirectives
            rightChildSelectionSet
          ∈ right
      -> schema.lookupField parentType leftFieldName = some leftFieldDefinition
      -> schema.lookupField parentType rightFieldName = some rightFieldDefinition
      -> (TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> schema.typeIncludesObjectBool leftFieldDefinition.outputType.namedType
            leftRuntimeType
          = true
      -> schema.typeIncludesObjectBool rightFieldDefinition.outputType.namedType
            rightRuntimeType
          = true
      -> SelectedFieldSpineRuntimeValid schema
          leftFieldDefinition.outputType.namedType leftRuntimeType
          leftInitialSpine
      -> SelectedFieldSpineRuntimeValid schema
          rightFieldDefinition.outputType.namedType rightRuntimeType
          rightInitialSpine
      -> leftFieldName ≠ rightFieldName
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema
                [Selection.inlineFragment (some parentType) [] (left ++ right)]
                (fieldPairSelectedPathProbeResolvers schema
                  (fieldPairPathLocalNextSelectionSet schema parentType
                    leftRuntimeType leftFieldName leftArguments (left ++ right))
                  (fieldPairPathLocalNextSelectionSet schema parentType
                    rightRuntimeType rightFieldName rightArguments (left ++ right))
                  leftInitialSpine rightInitialSpine parentType leftFieldName
                  rightFieldName leftArguments rightArguments
                  leftRuntimeType rightRuntimeType)
                parentType leftFieldName rightFieldName leftArguments
                rightArguments)
              variableValues
              (selectionSetDeepProbeFuel schema parentType (left ++ right)
                - leafProbeFuel leftFieldDefinition.outputType)
              leftRuntimeType
              (projectionTargetResolverValue
                (.object leftRuntimeType
                  (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
                    (fieldPairPathLocalNextSelectionSet schema parentType
                      leftRuntimeType leftFieldName leftArguments (left ++ right))
                    leftInitialSpine)))
              leftChildSelectionSet).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema
                [Selection.inlineFragment (some parentType) [] (left ++ right)]
                (fieldPairSelectedPathProbeResolvers schema
                  (fieldPairPathLocalNextSelectionSet schema parentType
                    leftRuntimeType leftFieldName leftArguments (left ++ right))
                  (fieldPairPathLocalNextSelectionSet schema parentType
                    rightRuntimeType rightFieldName rightArguments (left ++ right))
                  leftInitialSpine rightInitialSpine parentType leftFieldName
                  rightFieldName leftArguments rightArguments
                  leftRuntimeType rightRuntimeType)
                parentType leftFieldName rightFieldName leftArguments
                rightArguments)
              variableValues
              (selectionSetDeepProbeFuel schema parentType (left ++ right)
                - leafProbeFuel rightFieldDefinition.outputType)
              rightRuntimeType
              (projectionTargetResolverValue
                (.object rightRuntimeType
                  (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                    (fieldPairPathLocalNextSelectionSet schema parentType
                      rightRuntimeType rightFieldName rightArguments (left ++ right))
                    rightInitialSpine)))
              rightChildSelectionSet).data
      -> ¬ selectionSetsDataEquivalent schema parentType left right := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hobject hleftMem hrightMem hleftLookup hrightLookup
    hleftComposite hrightComposite hleftInclude hrightInclude
    hleftSpineValid hrightSpineValid hfieldDiff hchildDataNot
  let parentFuel := selectionSetDeepProbeFuel schema parentType (left ++ right)
  let rootSelectionSet : List Selection :=
    [Selection.inlineFragment (some parentType) [] (left ++ right)]
  let leftInitialSelectionSet : List Selection :=
    fieldPairPathLocalNextSelectionSet schema parentType
      leftRuntimeType leftFieldName leftArguments (left ++ right)
  let rightInitialSelectionSet : List Selection :=
    fieldPairPathLocalNextSelectionSet schema parentType
      rightRuntimeType rightFieldName rightArguments (left ++ right)
  have hsupport :
      PathLocalSupportValidNormal schema parentType (left ++ right) :=
    PathLocalSupportValidNormal.append
      (PathLocalSupportValidNormal.of_valid_normal_self hleftValid
        hleftFree hleftNormal)
      (PathLocalSupportValidNormal.of_valid_normal_self hrightValid
        hrightFree hrightNormal)
  have hleftContext :
      PathLocalSelectionSetCurrentContext left (left ++ right) :=
    ⟨[], right, by simp⟩
  have hrightContext :
      PathLocalSelectionSetCurrentContext right (left ++ right) :=
    ⟨left, [], by simp⟩
  let leftChildFuel :=
    parentFuel - leafProbeFuel leftFieldDefinition.outputType - 1
  let rightChildFuel :=
    parentFuel - leafProbeFuel rightFieldDefinition.outputType - 1
  have hleftChildFuel :
      selectionSetDeepProbeFuel schema
          leftFieldDefinition.outputType.namedType leftChildSelectionSet ≤
        leftChildFuel := by
    have hlocal :=
      selectionSetDeepProbeFuel_field_mem schema parentType (left ++ right)
        responseName leftFieldName leftArguments leftDirectives
        leftChildSelectionSet leftFieldDefinition
        (List.mem_append_left right hleftMem) hleftLookup
    dsimp [leftChildFuel, parentFuel]
    omega
  have hrightChildFuel :
      selectionSetDeepProbeFuel schema
          rightFieldDefinition.outputType.namedType rightChildSelectionSet ≤
        rightChildFuel := by
    have hlocal :=
      selectionSetDeepProbeFuel_field_mem schema parentType (left ++ right)
        responseName rightFieldName rightArguments rightDirectives
        rightChildSelectionSet rightFieldDefinition
        (List.mem_append_right left hrightMem) hrightLookup
    dsimp [rightChildFuel, parentFuel]
    omega
  have hleftChildFuelEq :
      leftChildFuel + 1 =
        parentFuel - leafProbeFuel leftFieldDefinition.outputType := by
    have hlocal :=
      selectionSetDeepProbeFuel_field_mem schema parentType (left ++ right)
        responseName leftFieldName leftArguments leftDirectives
        leftChildSelectionSet leftFieldDefinition
        (List.mem_append_left right hleftMem) hleftLookup
    dsimp [leftChildFuel, parentFuel]
    omega
  have hrightChildFuelEq :
      rightChildFuel + 1 =
        parentFuel - leafProbeFuel rightFieldDefinition.outputType := by
    have hlocal :=
      selectionSetDeepProbeFuel_field_mem schema parentType (left ++ right)
        responseName rightFieldName rightArguments rightDirectives
        rightChildSelectionSet rightFieldDefinition
        (List.mem_append_right left hrightMem) hrightLookup
    dsimp [rightChildFuel, parentFuel]
    omega
  rcases
      executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_target_child_of_valid_normal_support_context_field_mem
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftInitialSpine rightInitialSpine
        variableValues hschema (parentType := parentType)
        (variableDefinitions := leftVariableDefinitions)
        (selectionSet := left) (currentSelectionSet := left ++ right)
        (fuel := leftChildFuel) (responseName := responseName)
        (fieldName := leftFieldName)
        (runtimeType := leftRuntimeType)
        (targetParent := parentType) (leftField := leftFieldName)
        (rightField := rightFieldName) (targetArguments := leftArguments)
        (leftArguments := leftArguments)
        (rightArguments := rightArguments) (arguments := leftArguments)
        (directives := leftDirectives)
        (childSelectionSet := leftChildSelectionSet)
        (fieldDefinition := leftFieldDefinition)
        (leftRuntime := leftRuntimeType)
        (rightRuntime := rightRuntimeType)
        (spine := leftInitialSpine) (tag := FieldPairProbeTag.left)
        hleftValid hleftFree hleftNormal hobject hsupport hleftContext
        hleftMem (argumentsEquivalent_refl_forSyntaxDiff leftArguments)
        hleftLookup hleftComposite hleftInclude hleftSpineValid
        hleftChildFuel with
    ⟨leftChildFields, leftChildErrors, hleftChildResponseRaw⟩
  rcases
      executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_target_child_of_valid_normal_support_context_field_mem
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftInitialSpine rightInitialSpine
        variableValues hschema (parentType := parentType)
        (variableDefinitions := rightVariableDefinitions)
        (selectionSet := right) (currentSelectionSet := left ++ right)
        (fuel := rightChildFuel) (responseName := responseName)
        (fieldName := rightFieldName)
        (runtimeType := rightRuntimeType)
        (targetParent := parentType) (leftField := leftFieldName)
        (rightField := rightFieldName) (targetArguments := rightArguments)
        (leftArguments := leftArguments)
        (rightArguments := rightArguments) (arguments := rightArguments)
        (directives := rightDirectives)
        (childSelectionSet := rightChildSelectionSet)
        (fieldDefinition := rightFieldDefinition)
        (leftRuntime := leftRuntimeType)
        (rightRuntime := rightRuntimeType)
        (spine := rightInitialSpine) (tag := FieldPairProbeTag.right)
        hrightValid hrightFree hrightNormal hobject hsupport hrightContext
        hrightMem (argumentsEquivalent_refl_forSyntaxDiff rightArguments)
        hrightLookup hrightComposite hrightInclude hrightSpineValid
        hrightChildFuel with
    ⟨rightChildFields, rightChildErrors, hrightChildResponseRaw⟩
  have hleftChildResponse :
      Execution.executeSelectionSetAsResponse schema
          (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
            (fieldPairSelectedPathProbeResolvers schema
              leftInitialSelectionSet rightInitialSelectionSet
              leftInitialSpine rightInitialSpine parentType leftFieldName
              rightFieldName leftArguments rightArguments
              leftRuntimeType rightRuntimeType)
            parentType leftFieldName rightFieldName leftArguments
            rightArguments)
          variableValues
          (parentFuel - leafProbeFuel leftFieldDefinition.outputType)
          leftRuntimeType
          (projectionTargetResolverValue
            (.object leftRuntimeType
              (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
                leftInitialSelectionSet leftInitialSpine)))
          leftChildSelectionSet =
        ({ data := Execution.ResponseValue.object leftChildFields,
           errors := leftChildErrors } : Execution.Response) := by
    simpa [hleftChildFuelEq] using hleftChildResponseRaw
  have hrightChildResponse :
      Execution.executeSelectionSetAsResponse schema
          (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
            (fieldPairSelectedPathProbeResolvers schema
              leftInitialSelectionSet rightInitialSelectionSet
              leftInitialSpine rightInitialSpine parentType leftFieldName
              rightFieldName leftArguments rightArguments
              leftRuntimeType rightRuntimeType)
            parentType leftFieldName rightFieldName leftArguments
            rightArguments)
          variableValues
          (parentFuel - leafProbeFuel rightFieldDefinition.outputType)
          rightRuntimeType
          (projectionTargetResolverValue
            (.object rightRuntimeType
              (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                rightInitialSelectionSet rightInitialSpine)))
          rightChildSelectionSet =
        ({ data := Execution.ResponseValue.object rightChildFields,
           errors := rightChildErrors } : Execution.Response) := by
    simpa [hrightChildFuelEq] using hrightChildResponseRaw
  have hchildNot :
      ¬ Execution.ResponseValue.semanticEquivalent
        (Execution.ResponseValue.object leftChildFields)
        (Execution.ResponseValue.object rightChildFields) := by
    intro hsemantic
    apply hchildDataNot
    simpa [rootSelectionSet, leftInitialSelectionSet,
      rightInitialSelectionSet, parentFuel, hleftChildResponse,
      hrightChildResponse] using hsemantic
  have hleftLeafFuel :
      leafProbeFuel leftFieldDefinition.outputType ≤ parentFuel := by
    have hlocal :=
      leafProbeFuel_le_selectionSetDeepProbeFuel_of_field_mem schema
        parentType (selectionSet := left ++ right)
        (responseName := responseName) (fieldName := leftFieldName)
        (arguments := leftArguments) (directives := leftDirectives)
        (childSelectionSet := leftChildSelectionSet)
        (fieldDefinition := leftFieldDefinition)
        (List.mem_append_left right hleftMem) hleftLookup
    dsimp [parentFuel]
    omega
  have hrightLeafFuel :
      leafProbeFuel rightFieldDefinition.outputType ≤ parentFuel := by
    have hlocal :=
      leafProbeFuel_le_selectionSetDeepProbeFuel_of_field_mem schema
        parentType (selectionSet := left ++ right)
        (responseName := responseName) (fieldName := rightFieldName)
        (arguments := rightArguments) (directives := rightDirectives)
        (childSelectionSet := rightChildSelectionSet)
        (fieldDefinition := rightFieldDefinition)
        (List.mem_append_right left hrightMem) hrightLookup
    dsimp [parentFuel]
    omega
  have hleftLeftTarget :
      ∀ currentResponseName arguments directives childSelectionSet,
        Selection.field currentResponseName leftFieldName arguments
            directives childSelectionSet ∈ left ->
        Argument.argumentsEquivalent arguments leftArguments ->
          ∃ childFields childErrors,
            Execution.executeSelectionSetAsResponse schema
                (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                  (fieldPairSelectedPathProbeResolvers schema
                    leftInitialSelectionSet rightInitialSelectionSet
                    leftInitialSpine rightInitialSpine parentType
                    leftFieldName rightFieldName leftArguments
                    rightArguments
                    leftRuntimeType rightRuntimeType)
                  parentType leftFieldName rightFieldName leftArguments
                  rightArguments)
                variableValues
                (parentFuel - leafProbeFuel leftFieldDefinition.outputType)
                leftRuntimeType
                (projectionTargetResolverValue
                  (.object leftRuntimeType
                    (FieldPairSelectedPathProbeRef.target
                      FieldPairProbeTag.left leftInitialSelectionSet
                      leftInitialSpine)))
                childSelectionSet =
              ({ data := Execution.ResponseValue.object childFields,
                 errors := childErrors } : Execution.Response) := by
    intro currentResponseName arguments directives childSelectionSet hmem
      harguments
    let childFuel :=
      parentFuel - leafProbeFuel leftFieldDefinition.outputType - 1
    have htargetFuel :
        selectionSetDeepProbeFuel schema
            leftFieldDefinition.outputType.namedType childSelectionSet ≤
          childFuel := by
      have hlocal :=
        selectionSetDeepProbeFuel_field_mem schema parentType left
          currentResponseName leftFieldName arguments directives
          childSelectionSet leftFieldDefinition hmem hleftLookup
      have happend :=
        selectionSetDeepProbeFuel_le_append_left schema parentType left right
      dsimp [childFuel, parentFuel]
      omega
    rcases
        executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_target_child_of_valid_normal_support_context_field_mem
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet leftInitialSpine rightInitialSpine
          variableValues hschema (parentType := parentType)
          (variableDefinitions := leftVariableDefinitions)
          (selectionSet := left) (currentSelectionSet := left ++ right)
          (fuel := childFuel) (responseName := currentResponseName)
          (fieldName := leftFieldName)
          (runtimeType := leftRuntimeType)
          (targetParent := parentType) (leftField := leftFieldName)
          (rightField := rightFieldName) (targetArguments := leftArguments)
          (leftArguments := leftArguments)
          (rightArguments := rightArguments) (arguments := arguments)
          (directives := directives) (childSelectionSet := childSelectionSet)
          (fieldDefinition := leftFieldDefinition)
          (leftRuntime := leftRuntimeType)
          (rightRuntime := rightRuntimeType)
          (spine := leftInitialSpine) (tag := FieldPairProbeTag.left)
          hleftValid hleftFree hleftNormal hobject hsupport hleftContext
          hmem harguments hleftLookup hleftComposite hleftInclude
          hleftSpineValid htargetFuel with
      ⟨childFields, childErrors, hresponse⟩
    refine ⟨childFields, childErrors, ?_⟩
    have hfuelEq :
        childFuel + 1 =
          parentFuel - leafProbeFuel leftFieldDefinition.outputType := by
      have hlocal :=
        selectionSetDeepProbeFuel_field_mem schema parentType left
          currentResponseName leftFieldName arguments directives
          childSelectionSet leftFieldDefinition hmem hleftLookup
      dsimp [childFuel, parentFuel]
      omega
    simpa [leftInitialSelectionSet, hfuelEq] using hresponse
  have hleftRightTarget :
      ∀ currentResponseName arguments directives childSelectionSet,
        Selection.field currentResponseName rightFieldName arguments
            directives childSelectionSet ∈ left ->
        Argument.argumentsEquivalent arguments rightArguments ->
          ∃ childFields childErrors,
            Execution.executeSelectionSetAsResponse schema
                (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                  (fieldPairSelectedPathProbeResolvers schema
                    leftInitialSelectionSet rightInitialSelectionSet
                    leftInitialSpine rightInitialSpine parentType
                    leftFieldName rightFieldName leftArguments
                    rightArguments
                    leftRuntimeType rightRuntimeType)
                  parentType leftFieldName rightFieldName leftArguments
                  rightArguments)
                variableValues
                (parentFuel - leafProbeFuel rightFieldDefinition.outputType)
                rightRuntimeType
                (projectionTargetResolverValue
                  (.object rightRuntimeType
                    (FieldPairSelectedPathProbeRef.target
                      FieldPairProbeTag.right rightInitialSelectionSet
                      rightInitialSpine)))
                childSelectionSet =
              ({ data := Execution.ResponseValue.object childFields,
                 errors := childErrors } : Execution.Response) := by
    intro currentResponseName arguments directives childSelectionSet hmem
      harguments
    let childFuel :=
      parentFuel - leafProbeFuel rightFieldDefinition.outputType - 1
    have htargetFuel :
        selectionSetDeepProbeFuel schema
            rightFieldDefinition.outputType.namedType childSelectionSet ≤
          childFuel := by
      have hlocal :=
        selectionSetDeepProbeFuel_field_mem schema parentType left
          currentResponseName rightFieldName arguments directives
          childSelectionSet rightFieldDefinition hmem hrightLookup
      have happend :=
        selectionSetDeepProbeFuel_le_append_left schema parentType left right
      dsimp [childFuel, parentFuel]
      omega
    rcases
        executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_target_child_of_valid_normal_support_context_field_mem
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet leftInitialSpine rightInitialSpine
          variableValues hschema (parentType := parentType)
          (variableDefinitions := leftVariableDefinitions)
          (selectionSet := left) (currentSelectionSet := left ++ right)
          (fuel := childFuel) (responseName := currentResponseName)
          (fieldName := rightFieldName)
          (runtimeType := rightRuntimeType)
          (targetParent := parentType) (leftField := leftFieldName)
          (rightField := rightFieldName) (targetArguments := rightArguments)
          (leftArguments := leftArguments)
          (rightArguments := rightArguments) (arguments := arguments)
          (directives := directives) (childSelectionSet := childSelectionSet)
          (fieldDefinition := rightFieldDefinition)
          (leftRuntime := leftRuntimeType)
          (rightRuntime := rightRuntimeType)
          (spine := rightInitialSpine) (tag := FieldPairProbeTag.right)
          hleftValid hleftFree hleftNormal hobject hsupport hleftContext
          hmem harguments hrightLookup hrightComposite hrightInclude
          hrightSpineValid htargetFuel with
      ⟨childFields, childErrors, hresponse⟩
    refine ⟨childFields, childErrors, ?_⟩
    have hfuelEq :
        childFuel + 1 =
          parentFuel - leafProbeFuel rightFieldDefinition.outputType := by
      have hlocal :=
        selectionSetDeepProbeFuel_field_mem schema parentType left
          currentResponseName rightFieldName arguments directives
          childSelectionSet rightFieldDefinition hmem hrightLookup
      dsimp [childFuel, parentFuel]
      omega
    simpa [rightInitialSelectionSet, hfuelEq] using hresponse
  have hrightLeftTarget :
      ∀ currentResponseName arguments directives childSelectionSet,
        Selection.field currentResponseName leftFieldName arguments
            directives childSelectionSet ∈ right ->
        Argument.argumentsEquivalent arguments leftArguments ->
          ∃ childFields childErrors,
            Execution.executeSelectionSetAsResponse schema
                (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                  (fieldPairSelectedPathProbeResolvers schema
                    leftInitialSelectionSet rightInitialSelectionSet
                    leftInitialSpine rightInitialSpine parentType
                    leftFieldName rightFieldName leftArguments
                    rightArguments
                    leftRuntimeType rightRuntimeType)
                  parentType leftFieldName rightFieldName leftArguments
                  rightArguments)
                variableValues
                (parentFuel - leafProbeFuel leftFieldDefinition.outputType)
                leftRuntimeType
                (projectionTargetResolverValue
                  (.object leftRuntimeType
                    (FieldPairSelectedPathProbeRef.target
                      FieldPairProbeTag.left leftInitialSelectionSet
                      leftInitialSpine)))
                childSelectionSet =
              ({ data := Execution.ResponseValue.object childFields,
                 errors := childErrors } : Execution.Response) := by
    intro currentResponseName arguments directives childSelectionSet hmem
      harguments
    let childFuel :=
      parentFuel - leafProbeFuel leftFieldDefinition.outputType - 1
    have htargetFuel :
        selectionSetDeepProbeFuel schema
            leftFieldDefinition.outputType.namedType childSelectionSet ≤
          childFuel := by
      have hlocal :=
        selectionSetDeepProbeFuel_field_mem schema parentType right
          currentResponseName leftFieldName arguments directives
          childSelectionSet leftFieldDefinition hmem hleftLookup
      have happend :=
        selectionSetDeepProbeFuel_le_append_right schema parentType left right
      dsimp [childFuel, parentFuel]
      omega
    rcases
        executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_target_child_of_valid_normal_support_context_field_mem
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet leftInitialSpine rightInitialSpine
          variableValues hschema (parentType := parentType)
          (variableDefinitions := rightVariableDefinitions)
          (selectionSet := right) (currentSelectionSet := left ++ right)
          (fuel := childFuel) (responseName := currentResponseName)
          (fieldName := leftFieldName)
          (runtimeType := leftRuntimeType)
          (targetParent := parentType) (leftField := leftFieldName)
          (rightField := rightFieldName) (targetArguments := leftArguments)
          (leftArguments := leftArguments)
          (rightArguments := rightArguments) (arguments := arguments)
          (directives := directives) (childSelectionSet := childSelectionSet)
          (fieldDefinition := leftFieldDefinition)
          (leftRuntime := leftRuntimeType)
          (rightRuntime := rightRuntimeType)
          (spine := leftInitialSpine) (tag := FieldPairProbeTag.left)
          hrightValid hrightFree hrightNormal hobject hsupport hrightContext
          hmem harguments hleftLookup hleftComposite hleftInclude
          hleftSpineValid htargetFuel with
      ⟨childFields, childErrors, hresponse⟩
    refine ⟨childFields, childErrors, ?_⟩
    have hfuelEq :
        childFuel + 1 =
          parentFuel - leafProbeFuel leftFieldDefinition.outputType := by
      have hlocal :=
        selectionSetDeepProbeFuel_field_mem schema parentType right
          currentResponseName leftFieldName arguments directives
          childSelectionSet leftFieldDefinition hmem hleftLookup
      dsimp [childFuel, parentFuel]
      omega
    simpa [leftInitialSelectionSet, hfuelEq] using hresponse
  have hrightRightTarget :
      ∀ currentResponseName arguments directives childSelectionSet,
        Selection.field currentResponseName rightFieldName arguments
            directives childSelectionSet ∈ right ->
        Argument.argumentsEquivalent arguments rightArguments ->
          ∃ childFields childErrors,
            Execution.executeSelectionSetAsResponse schema
                (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                  (fieldPairSelectedPathProbeResolvers schema
                    leftInitialSelectionSet rightInitialSelectionSet
                    leftInitialSpine rightInitialSpine parentType
                    leftFieldName rightFieldName leftArguments
                    rightArguments
                    leftRuntimeType rightRuntimeType)
                  parentType leftFieldName rightFieldName leftArguments
                  rightArguments)
                variableValues
                (parentFuel - leafProbeFuel rightFieldDefinition.outputType)
                rightRuntimeType
                (projectionTargetResolverValue
                  (.object rightRuntimeType
                    (FieldPairSelectedPathProbeRef.target
                      FieldPairProbeTag.right rightInitialSelectionSet
                      rightInitialSpine)))
                childSelectionSet =
              ({ data := Execution.ResponseValue.object childFields,
                 errors := childErrors } : Execution.Response) := by
    intro currentResponseName arguments directives childSelectionSet hmem
      harguments
    let childFuel :=
      parentFuel - leafProbeFuel rightFieldDefinition.outputType - 1
    have htargetFuel :
        selectionSetDeepProbeFuel schema
            rightFieldDefinition.outputType.namedType childSelectionSet ≤
          childFuel := by
      have hlocal :=
        selectionSetDeepProbeFuel_field_mem schema parentType right
          currentResponseName rightFieldName arguments directives
          childSelectionSet rightFieldDefinition hmem hrightLookup
      have happend :=
        selectionSetDeepProbeFuel_le_append_right schema parentType left right
      dsimp [childFuel, parentFuel]
      omega
    rcases
        executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_target_child_of_valid_normal_support_context_field_mem
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet leftInitialSpine rightInitialSpine
          variableValues hschema (parentType := parentType)
          (variableDefinitions := rightVariableDefinitions)
          (selectionSet := right) (currentSelectionSet := left ++ right)
          (fuel := childFuel) (responseName := currentResponseName)
          (fieldName := rightFieldName)
          (runtimeType := rightRuntimeType)
          (targetParent := parentType) (leftField := leftFieldName)
          (rightField := rightFieldName) (targetArguments := rightArguments)
          (leftArguments := leftArguments)
          (rightArguments := rightArguments) (arguments := arguments)
          (directives := directives) (childSelectionSet := childSelectionSet)
          (fieldDefinition := rightFieldDefinition)
          (leftRuntime := leftRuntimeType)
          (rightRuntime := rightRuntimeType)
          (spine := rightInitialSpine) (tag := FieldPairProbeTag.right)
          hrightValid hrightFree hrightNormal hobject hsupport hrightContext
          hmem harguments hrightLookup hrightComposite hrightInclude
          hrightSpineValid htargetFuel with
      ⟨childFields, childErrors, hresponse⟩
    refine ⟨childFields, childErrors, ?_⟩
    have hfuelEq :
        childFuel + 1 =
          parentFuel - leafProbeFuel rightFieldDefinition.outputType := by
      have hlocal :=
        selectionSetDeepProbeFuel_field_mem schema parentType right
          currentResponseName rightFieldName arguments directives
          childSelectionSet rightFieldDefinition hmem hrightLookup
      dsimp [childFuel, parentFuel]
      omega
    simpa [rightInitialSelectionSet, hfuelEq] using hresponse
  have hleftDeep :
      ∀ currentResponseName siblingFieldName arguments directives childSelectionSet,
        Selection.field currentResponseName siblingFieldName arguments directives
            childSelectionSet ∈ left ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema
              (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet
                (ProjectionResolverRef.filler :
                  ProjectionResolverRef FieldPairSelectedPathProbeRef))
              variableValues (parentFuel + 1)
              (projectionRootResolverValue
                (.object parentType FieldPairSelectedPathProbeRef.root))
              currentResponseName
              [{
                parentType := parentType,
                responseName := currentResponseName,
                fieldName := siblingFieldName,
                arguments := arguments,
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(currentResponseName, responseValue)], fieldErrors) := by
    intro currentResponseName siblingFieldName arguments directives
      childSelectionSet hmem
    simpa [rootSelectionSet, parentFuel] using
      left_selectionSet_deepSuccessFieldOk_append_framed_of_valid_normal_fuel_ge
        (schema := schema) (parentType := parentType)
        (left := left) (right := right)
        (leftVariableDefinitions := leftVariableDefinitions)
        (rightVariableDefinitions := rightVariableDefinitions)
        (ProjectionResolverRef.filler :
          ProjectionResolverRef FieldPairSelectedPathProbeRef)
        variableValues
        (projectionRootResolverValue
          (.object parentType FieldPairSelectedPathProbeRef.root))
        parentFuel hschema hleftValid hrightValid hleftFree hrightFree
        hleftNormal hrightNormal hobject (by simp [parentFuel])
        currentResponseName siblingFieldName arguments directives
        childSelectionSet hmem
  have hrightDeep :
      ∀ currentResponseName siblingFieldName arguments directives childSelectionSet,
        Selection.field currentResponseName siblingFieldName arguments directives
            childSelectionSet ∈ right ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema
              (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet
                (ProjectionResolverRef.filler :
                  ProjectionResolverRef FieldPairSelectedPathProbeRef))
              variableValues (parentFuel + 1)
              (projectionRootResolverValue
                (.object parentType FieldPairSelectedPathProbeRef.root))
              currentResponseName
              [{
                parentType := parentType,
                responseName := currentResponseName,
                fieldName := siblingFieldName,
                arguments := arguments,
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(currentResponseName, responseValue)], fieldErrors) := by
    intro currentResponseName siblingFieldName arguments directives
      childSelectionSet hmem
    simpa [rootSelectionSet, parentFuel] using
      right_selectionSet_deepSuccessFieldOk_append_framed_of_valid_normal_fuel_ge
        (schema := schema) (parentType := parentType)
        (left := left) (right := right)
        (leftVariableDefinitions := leftVariableDefinitions)
        (rightVariableDefinitions := rightVariableDefinitions)
        (ProjectionResolverRef.filler :
          ProjectionResolverRef FieldPairSelectedPathProbeRef)
        variableValues
        (projectionRootResolverValue
          (.object parentType FieldPairSelectedPathProbeRef.root))
        parentFuel hschema hleftValid hrightValid hleftFree hrightFree
        hleftNormal hrightNormal hobject (by simp [parentFuel])
        currentResponseName siblingFieldName arguments directives
        childSelectionSet hmem
  exact
    not_selectionSetsDataEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_root_fieldName_child_response_diff_of_field_cases
      schema rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftInitialSpine rightInitialSpine variableValues parentFuel
      parentType responseName leftFieldName rightFieldName leftArguments
      rightArguments leftRuntimeType rightRuntimeType hobject hleftNormal
      hrightNormal hleftFree hrightFree hleftMem hrightMem hleftLookup
      hrightLookup hleftInclude hrightInclude hleftLeafFuel
      hrightLeafFuel hfieldDiff hleftChildResponse hrightChildResponse
      hchildNot hleftLeftTarget hleftRightTarget hrightLeftTarget
      hrightRightTarget hleftDeep hrightDeep

theorem selectedPathTaggedSelectionSetsResponseDiffWitness_of_selectionSetWitness
    {schema : Schema}
    {rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection}
    {leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep}
    {variableValues : Execution.VariableValues} {fuel : Nat}
    {normalParentType runtimeType targetParent leftField rightField : Name}
    {leftArguments rightArguments : List Argument}
    {leftRuntime rightRuntime : Name}
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
      -> SelectedPathTaggedSelectionSetsResponseDiffWitness schema
          rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
          leftInitialSpine rightInitialSpine variableValues fuel
          normalParentType runtimeType targetParent leftField rightField
          leftArguments rightArguments leftRuntime rightRuntime
          leftCurrentSelectionSet rightCurrentSelectionSet leftSpine rightSpine
          selectionSet selectionSet := by
  intro hwitness
  simpa [SelectedPathTaggedSelectionSetResponseDiffWitness,
    SelectedPathTaggedSelectionSetsResponseDiffWitness] using hwitness

theorem
    selectedPathTaggedSelectionSetsResponseDiffWitness_of_observableResponsePath_valid_normal_pair_support_context_fuel_ge
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ∀ normalParentType leftCurrentSelectionSet rightCurrentSelectionSet
            (selectionSet : List Selection) {responsePath : List Name},
          NormalSelectionSetObservableResponsePath schema normalParentType
            selectionSet responsePath
          -> ∀ variableDefinitions fuel targetParent leftField rightField
                (leftArguments rightArguments : List Argument)
                (leftRuntime rightRuntime : Name),
              Validation.selectionSetValid schema variableDefinitions
                normalParentType selectionSet
              -> selectionSetDirectiveFree selectionSet
              -> selectionSetNormal schema normalParentType selectionSet
              -> selectionSetDeepProbeFuel schema normalParentType selectionSet ≤ fuel
              -> ∃ runtimeType fieldSpine,
                  schema.typeIncludesObjectBool normalParentType runtimeType = true
                  ∧ SelectedFieldSpineRuntimeValid schema normalParentType
                      runtimeType fieldSpine
                  ∧ (PathLocalSupportValidNormal schema runtimeType
                        leftCurrentSelectionSet
                      -> PathLocalSupportValidNormal schema runtimeType
                          rightCurrentSelectionSet
                      -> (objectTypeNameBool schema normalParentType = true
                          -> PathLocalSelectionSetCurrentContext selectionSet
                              leftCurrentSelectionSet)
                      -> (objectTypeNameBool schema normalParentType = true
                          -> PathLocalSelectionSetCurrentContext selectionSet
                              rightCurrentSelectionSet)
                      -> (objectTypeNameBool schema normalParentType = false
                          -> ∀ {directives bodySelectionSet},
                              Selection.inlineFragment (some runtimeType) directives
                                  bodySelectionSet
                                ∈ selectionSet
                              -> PathLocalSelectionSetCurrentContext bodySelectionSet
                                  leftCurrentSelectionSet)
                      -> (objectTypeNameBool schema normalParentType = false
                          -> ∀ {directives bodySelectionSet},
                              Selection.inlineFragment (some runtimeType) directives
                                  bodySelectionSet
                                ∈ selectionSet
                              -> PathLocalSelectionSetCurrentContext bodySelectionSet
                                  rightCurrentSelectionSet)
                      -> SelectedPathTaggedSelectionSetsResponseDiffWitness schema
                          rootSelectionSet leftInitialSelectionSet
                          rightInitialSelectionSet leftInitialSpine
                          rightInitialSpine variableValues (fuel + 1)
                          normalParentType runtimeType targetParent leftField
                          rightField leftArguments rightArguments leftRuntime
                          rightRuntime leftCurrentSelectionSet
                          rightCurrentSelectionSet fieldSpine fieldSpine
                          selectionSet selectionSet) := by
  intro hschema normalParentType leftCurrentSelectionSet
    rightCurrentSelectionSet selectionSet responsePath hpath
    variableDefinitions fuel targetParent leftField rightField
    leftArguments rightArguments leftRuntime rightRuntime hvalid hfree
    hnormal hfuel
  rcases
      selectedPathTaggedSelectionSetResponseDiffWitness_of_observableResponsePath_valid_normal_pair_support_context_fuel_ge
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftInitialSpine rightInitialSpine
        variableValues hschema normalParentType leftCurrentSelectionSet
        rightCurrentSelectionSet selectionSet hpath variableDefinitions
        fuel targetParent leftField rightField leftArguments
        rightArguments leftRuntime rightRuntime hvalid hfree hnormal
        hfuel with
    ⟨runtimeType, fieldSpine, hinclude, hspineValid, hwitness⟩
  refine ⟨runtimeType, fieldSpine, hinclude, hspineValid, ?_⟩
  intro hleftSupport hrightSupport hleftObjectContext
    hrightObjectContext hleftAbstractContext hrightAbstractContext
  exact
    selectedPathTaggedSelectionSetsResponseDiffWitness_of_selectionSetWitness
      (hwitness hleftSupport hrightSupport hleftObjectContext
        hrightObjectContext hleftAbstractContext hrightAbstractContext)

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_observableResponsePath_valid_normal_pair_support_context_fuel_ge
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ∀ normalParentType leftCurrentSelectionSet rightCurrentSelectionSet
            (selectionSet : List Selection) {responsePath : List Name},
          NormalSelectionSetObservableResponsePath schema normalParentType
            selectionSet responsePath
          -> ∀ variableDefinitions fuel targetParent leftField rightField
                (leftArguments rightArguments : List Argument)
                (leftRuntime rightRuntime : Name),
              Validation.selectionSetValid schema variableDefinitions
                normalParentType selectionSet
              -> selectionSetDirectiveFree selectionSet
              -> selectionSetNormal schema normalParentType selectionSet
              -> selectionSetDeepProbeFuel schema normalParentType selectionSet ≤ fuel
              -> ∃ runtimeType fieldSpine,
                  schema.typeIncludesObjectBool normalParentType runtimeType = true
                  ∧ SelectedFieldSpineRuntimeValid schema normalParentType
                      runtimeType fieldSpine
                  ∧ (PathLocalSupportValidNormal schema runtimeType
                        leftCurrentSelectionSet
                      -> PathLocalSupportValidNormal schema runtimeType
                          rightCurrentSelectionSet
                      -> (objectTypeNameBool schema normalParentType = true
                          -> PathLocalSelectionSetCurrentContext selectionSet
                              leftCurrentSelectionSet)
                      -> (objectTypeNameBool schema normalParentType = true
                          -> PathLocalSelectionSetCurrentContext selectionSet
                              rightCurrentSelectionSet)
                      -> (objectTypeNameBool schema normalParentType = false
                          -> ∀ {directives bodySelectionSet},
                              Selection.inlineFragment (some runtimeType) directives
                                  bodySelectionSet
                                ∈ selectionSet
                              -> PathLocalSelectionSetCurrentContext bodySelectionSet
                                  leftCurrentSelectionSet)
                      -> (objectTypeNameBool schema normalParentType = false
                          -> ∀ {directives bodySelectionSet},
                              Selection.inlineFragment (some runtimeType) directives
                                  bodySelectionSet
                                ∈ selectionSet
                              -> PathLocalSelectionSetCurrentContext bodySelectionSet
                                  rightCurrentSelectionSet)
                      -> ¬ Execution.ResponseValue.semanticEquivalent
                            (Execution.executeSelectionSetAsResponse schema
                              (fieldPairOrDeepSuccessResolvers schema
                                rootSelectionSet
                                (fieldPairSelectedPathProbeResolvers schema
                                  leftInitialSelectionSet rightInitialSelectionSet
                                  leftInitialSpine rightInitialSpine targetParent
                                  leftField rightField leftArguments
                                  rightArguments leftRuntime rightRuntime)
                                targetParent leftField rightField leftArguments
                                rightArguments)
                              variableValues (fuel + 1) runtimeType
                              (projectionTargetResolverValue
                                (.object runtimeType
                                  (FieldPairSelectedPathProbeRef.target
                                    FieldPairProbeTag.left leftCurrentSelectionSet
                                    fieldSpine)))
                              selectionSet).data
                            (Execution.executeSelectionSetAsResponse schema
                              (fieldPairOrDeepSuccessResolvers schema
                                rootSelectionSet
                                (fieldPairSelectedPathProbeResolvers schema
                                  leftInitialSelectionSet rightInitialSelectionSet
                                  leftInitialSpine rightInitialSpine targetParent
                                  leftField rightField leftArguments
                                  rightArguments leftRuntime rightRuntime)
                                targetParent leftField rightField leftArguments
                                rightArguments)
                              variableValues (fuel + 1) runtimeType
                              (projectionTargetResolverValue
                                (.object runtimeType
                                  (FieldPairSelectedPathProbeRef.target
                                    FieldPairProbeTag.right rightCurrentSelectionSet
                                    fieldSpine)))
                              selectionSet).data) := by
  intro hschema normalParentType leftCurrentSelectionSet
    rightCurrentSelectionSet selectionSet responsePath hpath
    variableDefinitions fuel targetParent leftField rightField
    leftArguments rightArguments leftRuntime rightRuntime hvalid hfree
    hnormal hfuel
  rcases
      selectedPathTaggedSelectionSetResponseDiffWitness_of_observableResponsePath_valid_normal_pair_support_context_fuel_ge
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftInitialSpine rightInitialSpine
        variableValues hschema normalParentType leftCurrentSelectionSet
        rightCurrentSelectionSet selectionSet hpath variableDefinitions
        fuel targetParent leftField rightField leftArguments
        rightArguments leftRuntime rightRuntime hvalid hfree hnormal
        hfuel with
    ⟨runtimeType, fieldSpine, hinclude, hspineValid, hwitness⟩
  refine ⟨runtimeType, fieldSpine, hinclude, hspineValid, ?_⟩
  intro hleftSupport hrightSupport hleftObjectContext
    hrightObjectContext hleftAbstractContext hrightAbstractContext
  exact
    responseData_not_semanticEquivalent_of_selectedPathTaggedSelectionSetsResponseDiffWitness
      (selectedPathTaggedSelectionSetsResponseDiffWitness_of_selectionSetWitness
        (hwitness hleftSupport hrightSupport hleftObjectContext
          hrightObjectContext hleftAbstractContext hrightAbstractContext))

theorem
    pathLocalSelectionSetObservableFieldSpineAtSelectedRuntime_of_valid_normal_nonempty
    {schema : Schema} {variableDefinitions : List VariableDefinition} {parentType : Name}
    {selectionSet : List Selection}
    : Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> selectionSet ≠ []
      -> ∃ runtimeType fieldSpine,
          schema.typeIncludesObjectBool parentType runtimeType = true
          ∧ SelectedFieldSpineRuntimeValid schema parentType runtimeType fieldSpine
          ∧ ∀ currentSelectionSet,
              PathLocalSelectionSetObservableFieldSpineAtSelectedRuntime schema
                parentType runtimeType currentSelectionSet selectionSet
                fieldSpine := by
  intro hvalid hnormal hnonempty
  let hobservableLeaf :=
    normalSelectionSetObservableLeaf_of_valid_normal_nonempty schema
      parentType variableDefinitions selectionSet hvalid hnormal hnonempty
  rcases normalSelectionSetObservableResponsePath_of_observableLeaf
      hobservableLeaf with
    ⟨responsePath, hobservablePath⟩
  rcases
      pathLocalSelectionSetObservableFieldSpineAtSelectedRuntime_of_observableResponsePath_valid_normal
        hobservablePath hvalid hnormal with
    ⟨runtimeType, fieldSpine, hinclude, hobservableSpine⟩
  exact ⟨
    runtimeType,
    fieldSpine,
    hinclude,
    selectedFieldSpineRuntimeValid_of_observableFieldSpineAtSelectedRuntime
      (hobservableSpine []),
    hobservableSpine
  ⟩

theorem selectedFieldSpineRuntimeValid_exists_of_valid_normal_object_nonempty
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType : Name} {selectionSet : List Selection}
    : Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> objectTypeNameBool schema parentType = true
      -> selectionSet ≠ []
      -> ∃ fieldSpine,
          SelectedFieldSpineRuntimeValid schema parentType parentType fieldSpine
          ∧ ∀ currentSelectionSet,
              PathLocalSelectionSetObservableFieldSpineAtSelectedRuntime schema
                parentType parentType currentSelectionSet selectionSet
                fieldSpine := by
  intro hvalid hnormal hobject hnonempty
  rcases
      pathLocalSelectionSetObservableFieldSpineAtSelectedRuntime_of_valid_normal_nonempty
        hvalid hnormal hnonempty with
    ⟨runtimeType, fieldSpine, hinclude, hspineValid, hobservable⟩
  have hruntimeEq : runtimeType = parentType :=
    typeIncludesObjectBool_eq_of_objectTypeNameBool_true schema hobject
      hinclude
  subst runtimeType
  exact ⟨fieldSpine, hspineValid, hobservable⟩

theorem selectedFieldSpineRuntimeValid_exists_of_observableResponsePath_valid_normal
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType : Name} {selectionSet : List Selection}
    {responsePath : List Name}
    : NormalSelectionSetObservableResponsePath schema parentType selectionSet responsePath
      -> Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> ∃ runtimeType fieldSpine,
          schema.typeIncludesObjectBool parentType runtimeType = true
          ∧ SelectedFieldSpineRuntimeValid schema parentType runtimeType fieldSpine
          ∧ ∀ currentSelectionSet,
              PathLocalSelectionSetObservableFieldSpineAtSelectedRuntime schema
                parentType runtimeType currentSelectionSet selectionSet
                fieldSpine := by
  intro hpath hvalid hnormal
  rcases
      pathLocalSelectionSetObservableFieldSpineAtSelectedRuntime_of_observableResponsePath_valid_normal
        hpath hvalid hnormal with
    ⟨runtimeType, fieldSpine, hinclude, hobservableSpine⟩
  exact ⟨
    runtimeType,
    fieldSpine,
    hinclude,
    selectedFieldSpineRuntimeValid_of_observableFieldSpineAtSelectedRuntime
      (hobservableSpine []),
    hobservableSpine
  ⟩

theorem
    selectionSetFieldsExecuteOk_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_of_valid_normal_runtimeSpine
    (schema : Schema) {variableDefinitions : List VariableDefinition}
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet currentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine spine
      : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField parentType sourceRuntimeType : Name)
    (leftArguments rightArguments : List Argument) (leftRuntime rightRuntime : Name)
    (tag : FieldPairProbeTag) (selectionSet : List Selection)
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> selectionSetDirectiveFree selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> objectTypeNameBool schema parentType = true
      -> selectionSetDeepProbeFuel schema parentType selectionSet ≤ fuel
      -> SelectedFieldSpineRuntimeValid schema parentType sourceRuntimeType spine
      -> PathLocalSupportValidNormal schema sourceRuntimeType currentSelectionSet
      -> PathLocalSelectionSetCurrentContext selectionSet currentSelectionSet
      -> ∀ responseName fieldName arguments directives childSelectionSet,
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
                  (.object sourceRuntimeType
                    (FieldPairSelectedPathProbeRef.target tag currentSelectionSet spine)))
                responseName
                [{
                  parentType := parentType
                  responseName := responseName
                  fieldName := fieldName
                  arguments := arguments
                  selectionSet := childSelectionSet
                }]
              = .ok ([(responseName, responseValue)], fieldErrors) := by
  intro hschema hvalid hfree hnormal hobject hfuel hspineValid hsupport
    hcontext
  have hready :
      SelectedPathSelectionSetFieldChildrenReady schema rootSelectionSet
        leftInitialSelectionSet rightInitialSelectionSet currentSelectionSet
        leftInitialSpine rightInitialSpine spine variableValues fuel
        targetParent leftField rightField parentType leftArguments
        rightArguments leftRuntime rightRuntime tag selectionSet :=
    selectedPathSelectionSetFieldChildrenReady_of_valid_normal_runtimeSpine_support_context_fuel_ge
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet leftInitialSpine rightInitialSpine
      variableValues hschema parentType variableDefinitions selectionSet
      fuel sourceRuntimeType targetParent leftField rightField
      leftArguments rightArguments leftRuntime rightRuntime tag
      currentSelectionSet spine hfuel hvalid hfree hnormal hobject
      hspineValid hsupport hcontext
  exact
    executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_field_ok_of_selectedPathFieldChildrenReady
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet currentSelectionSet leftInitialSpine
      rightInitialSpine spine variableValues fuel targetParent leftField
      rightField parentType sourceRuntimeType leftArguments rightArguments
      leftRuntime rightRuntime tag selectionSet hready

theorem objectOutputChildResponse_of_selectedPathFieldChildrenReady
    {schema : Schema}
    {rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      currentSelectionSet selectionSet
      : List Selection}
    {leftInitialSpine rightInitialSpine spine
      : List NormalSelectionSetObservableFieldStep}
    {variableValues : Execution.VariableValues}
    {fuel : Nat} {targetParent leftField rightField parentType : Name}
    {targetLeftArguments targetRightArguments : List Argument}
    {leftRuntime rightRuntime : Name} {tag : FieldPairProbeTag}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
    : SelectedPathSelectionSetFieldChildrenReady schema rootSelectionSet
        leftInitialSelectionSet rightInitialSelectionSet currentSelectionSet
        leftInitialSpine rightInitialSpine spine variableValues fuel
        targetParent leftField rightField parentType targetLeftArguments
        targetRightArguments leftRuntime rightRuntime tag selectionSet
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> objectTypeNameBool schema fieldDefinition.outputType.namedType = true
      -> ∃ responseFields childErrors,
          Execution.executeSelectionSetAsResponse schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairSelectedPathProbeResolvers schema
                leftInitialSelectionSet rightInitialSelectionSet
                leftInitialSpine rightInitialSpine targetParent leftField
                rightField targetLeftArguments targetRightArguments
                leftRuntime rightRuntime)
              targetParent leftField rightField targetLeftArguments
              targetRightArguments)
            variableValues (fuel - leafProbeFuel fieldDefinition.outputType)
            fieldDefinition.outputType.namedType
            (projectionTargetResolverValue
              (.object fieldDefinition.outputType.namedType
                (FieldPairSelectedPathProbeRef.target tag
                  (fieldPairPathLocalNextSelectionSet schema parentType
                    fieldDefinition.outputType.namedType fieldName
                    arguments currentSelectionSet)
                  (selectedObservableFieldSpineTailForRuntime
                    fieldDefinition.outputType.namedType fieldName
                    arguments spine))))
            childSelectionSet
          = ({
                data := Execution.ResponseValue.object responseFields,
                errors := childErrors
              }
              : Execution.Response) := by
  intro hready hmem hlookup hobjectOutput
  rcases hready responseName fieldName arguments directives
      childSelectionSet hmem with
    ⟨candidateDefinition, hcandidateLookup, _hfuel, hcase⟩
  have hcandidateEq : candidateDefinition = fieldDefinition := by
    rw [hlookup] at hcandidateLookup
    exact Option.some.inj hcandidateLookup.symm
  subst candidateDefinition
  rcases hcase with hleaf | hcase
  · have hcomposite :
        (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool
          schema = true :=
      typeRef_named_isCompositeBool_true_of_objectTypeNameBool hobjectOutput
    rw [hcomposite] at hleaf
    simp at hleaf
  rcases hcase with hselected | hcase
  · rcases hselected with
      ⟨childRuntimeType, tail, responseFields, childErrors, hselected,
        hruntimeCase, _hinclude, hchildResponse⟩
    rcases hruntimeCase with hobjectRuntime | habstractRuntime
    · rcases hobjectRuntime with ⟨_hobject, hruntimeEq⟩
      subst childRuntimeType
      refine ⟨responseFields, childErrors, ?_⟩
      simpa [selectedObservableFieldSpineTailForRuntime, hselected] using
        hchildResponse
    · rcases habstractRuntime with ⟨_hcomposite, hnonObject⟩
      rw [hobjectOutput] at hnonObject
      simp at hnonObject
  rcases hcase with hobjectCase | habstractFallback
  · rcases hobjectCase with
      ⟨responseFields, childErrors, _hobjectOutput, hchildResponse⟩
    exact ⟨responseFields, childErrors, hchildResponse⟩
  · rcases habstractFallback with
      ⟨_childRuntimeType, _responseFields, _childErrors,
        _hcomposite, hnonObject, _hselected, _hruntime, _hinclude,
        _hchildResponse⟩
    rw [hobjectOutput] at hnonObject
    simp at hnonObject

def SelectedPathCompositeFieldChildSource
    (schema : Schema) (parentType fieldName : Name)
    (arguments : List Argument) (currentSelectionSet : List Selection)
    (spine : List NormalSelectionSetObservableFieldStep)
    (fieldDefinition : FieldDefinition) (childRuntimeType : Name)
    (childSpine : List NormalSelectionSetObservableFieldStep)
    : Prop :=
  (selectedObservableFieldSpineNext? fieldName arguments spine
      = some (some childRuntimeType, childSpine)
    ∧ (((objectTypeNameBool schema fieldDefinition.outputType.namedType = true
          ∧ childRuntimeType = fieldDefinition.outputType.namedType)
        ∨ ((TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
              = true
            ∧ objectTypeNameBool schema fieldDefinition.outputType.namedType = false))))
  ∨ (objectTypeNameBool schema fieldDefinition.outputType.namedType = true
      ∧ childRuntimeType = fieldDefinition.outputType.namedType
      ∧ childSpine
        = selectedObservableFieldSpineTailForRuntime
            fieldDefinition.outputType.namedType fieldName arguments spine)
  ∨ ((TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema = true
      ∧ objectTypeNameBool schema fieldDefinition.outputType.namedType = false
      ∧ selectedObservableFieldSpineNext? fieldName arguments spine = none
      ∧ abstractRuntimeForFieldHeadDeep? schema parentType fieldName arguments
          parentType currentSelectionSet
        = some childRuntimeType
      ∧ childSpine = [])

def SelectedPathSelectionSetContextReady
    (schema : Schema) (normalParentType runtimeType : Name)
    (currentSelectionSet selectionSet : List Selection)
    : Prop :=
  (objectTypeNameBool schema normalParentType = true
    -> PathLocalSelectionSetCurrentContext selectionSet currentSelectionSet)
  ∧ (objectTypeNameBool schema normalParentType = false
      -> ∀ {directives bodySelectionSet},
          Selection.inlineFragment (some runtimeType) directives bodySelectionSet
            ∈ selectionSet
          -> PathLocalSelectionSetCurrentContext bodySelectionSet currentSelectionSet)

theorem selectedPathSelectionSetContextReady_of_object_context
    {schema : Schema} {parentType runtimeType : Name}
    {currentSelectionSet selectionSet : List Selection}
    : objectTypeNameBool schema parentType = true
      -> PathLocalSelectionSetCurrentContext selectionSet currentSelectionSet
      -> SelectedPathSelectionSetContextReady schema parentType runtimeType
          currentSelectionSet selectionSet := by
  intro hobject hcontext
  exact ⟨fun _hobject => hcontext,
    fun hnonObject => by
      intro directives bodySelectionSet hmem
      rw [hobject] at hnonObject
      simp at hnonObject⟩

theorem
    pathLocalSupportValidNormal_fieldPairPathLocalNextSelectionSet_of_selectedPathCompositeFieldChildSource
    {schema : Schema} {parentType fieldName : Name} {arguments : List Argument}
    {currentSelectionSet : List Selection}
    {spine : List NormalSelectionSetObservableFieldStep}
    {fieldDefinition : FieldDefinition} {childRuntimeType : Name}
    {childSpine : List NormalSelectionSetObservableFieldStep}
    : PathLocalSupportValidNormal schema parentType currentSelectionSet
      -> objectTypeNameBool schema parentType = true
      -> objectTypeNameBool schema childRuntimeType = true
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> SelectedPathCompositeFieldChildSource schema parentType fieldName
          arguments currentSelectionSet spine fieldDefinition childRuntimeType
          childSpine
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType
            childRuntimeType
          = true
      -> PathLocalSupportValidNormal schema childRuntimeType
          (fieldPairPathLocalNextSelectionSet schema parentType
            childRuntimeType fieldName arguments currentSelectionSet) := by
  intro hsupport hobject hchildObject hlookup hsource hinclude
  rcases hsource with hselected | hcase
  · rcases hselected with ⟨_hselected, hruntimeCase⟩
    rcases hruntimeCase with hobjectCase | habstractCase
    · rcases hobjectCase with ⟨hobjectOutput, hruntimeEq⟩
      subst childRuntimeType
      exact
        hsupport.fieldPairPathLocalNextSelectionSet_of_object_output
          hobject hobjectOutput hlookup rfl
    · rcases habstractCase with ⟨hcomposite, _hnonObject⟩
      exact
        hsupport.fieldPairPathLocalNextSelectionSet_of_abstract_output
          hobject hchildObject hlookup hcomposite hinclude
  rcases hcase with hobjectCase | habstractCase
  · rcases hobjectCase with ⟨hobjectOutput, hruntimeEq, _hspineEq⟩
    subst childRuntimeType
    exact
      hsupport.fieldPairPathLocalNextSelectionSet_of_object_output
        hobject hobjectOutput hlookup rfl
  · rcases habstractCase with
      ⟨hcomposite, _hnonObject, _hselectedNone, _hruntime, _hspineEq⟩
    exact
      hsupport.fieldPairPathLocalNextSelectionSet_of_abstract_output
        hobject hchildObject hlookup hcomposite hinclude

theorem
    selectedPathSelectionSetContextReady_fieldPairPathLocalNextSelectionSet_of_selectedPathCompositeFieldChildSource
    {schema : Schema} {parentType responseName fieldName : Name}
    {arguments : List Argument} {directives : List DirectiveApplication}
    {selectionSet childSelectionSet currentSelectionSet : List Selection}
    {fieldDefinition : FieldDefinition} {childRuntimeType : Name}
    {spine childSpine : List NormalSelectionSetObservableFieldStep}
    : PathLocalSelectionSetCurrentContext selectionSet currentSelectionSet
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> selectionSetNormal schema fieldDefinition.outputType.namedType childSelectionSet
      -> SelectedPathCompositeFieldChildSource schema parentType fieldName
          arguments currentSelectionSet spine fieldDefinition childRuntimeType
          childSpine
      -> objectTypeNameBool schema childRuntimeType = true
      -> SelectedPathSelectionSetContextReady schema
          fieldDefinition.outputType.namedType childRuntimeType
          (fieldPairPathLocalNextSelectionSet schema parentType
            childRuntimeType fieldName arguments currentSelectionSet)
          childSelectionSet := by
  intro hcontext hmem hlookup hchildNormal hsource hchildObject
  refine ⟨?_, ?_⟩
  · intro hchildParentObject
    have hpruned :
        runtimePrunedSelectionSet schema childRuntimeType
            childSelectionSet =
          childSelectionSet := by
      have hruntimeEq :
          childRuntimeType = fieldDefinition.outputType.namedType := by
        rcases hsource with hselected | hcase
        · rcases hselected with ⟨_hselected, hruntimeCase⟩
          rcases hruntimeCase with hobjectCase | habstractCase
          · exact hobjectCase.2
          · rcases habstractCase with ⟨_hcomposite, hnonObject⟩
            rw [hchildParentObject] at hnonObject
            simp at hnonObject
        · rcases hcase with hobjectCase | habstractCase
          · exact hobjectCase.2.1
          · rcases habstractCase with
              ⟨_hcomposite, hnonObject, _hselectedNone, _hruntime,
                _hspineEq⟩
            rw [hchildParentObject] at hnonObject
            simp at hnonObject
      subst childRuntimeType
      have hallFields : selectionsAllFields childSelectionSet :=
        selectionSetNormal_allFields_of_object hchildNormal
          hchildParentObject
      exact
        runtimePrunedSelectionSet_eq_self_of_allFields schema
          fieldDefinition.outputType.namedType hallFields
    exact
      PathLocalSelectionSetCurrentContext.fieldPairPathLocalNextSelectionSet_field_child
        (schema := schema) (currentRuntimeType := parentType)
        (childRuntimeType := childRuntimeType)
        (targetField := fieldName) (responseName := responseName)
        (targetArguments := arguments) (arguments := arguments)
        (directives := directives) (selectionSet := selectionSet)
        (childSelectionSet := childSelectionSet)
        (currentSelectionSet := currentSelectionSet) hcontext hmem
        (argumentsEquivalent_refl_forSyntaxDiff arguments) hpruned
  · intro _hchildParentNonObject bodyDirectives bodySelectionSet hbodyMem
    exact
      PathLocalSelectionSetCurrentContext.fieldPairPathLocalNextSelectionSet_inlineFragment_body
        (schema := schema) (currentRuntimeType := parentType)
        (childRuntimeType := childRuntimeType)
        (childParentType := fieldDefinition.outputType.namedType)
        (targetField := fieldName) (responseName := responseName)
        (targetArguments := arguments) (arguments := arguments)
        (directives := directives) (bodyDirectives := bodyDirectives)
        (selectionSet := selectionSet)
        (childSelectionSet := childSelectionSet)
        (bodySelectionSet := bodySelectionSet)
        (currentSelectionSet := currentSelectionSet) hcontext hmem
        hbodyMem (argumentsEquivalent_refl_forSyntaxDiff arguments)
        hchildNormal hchildObject

theorem
    executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_of_valid_normal_contextReady_fuel_ge_size
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ∀ size normalParentType variableDefinitions (selectionSet : List Selection)
            fuel runtimeType targetParent leftField rightField
            (leftArguments rightArguments : List Argument)
            (leftRuntime rightRuntime : Name) (tag : FieldPairProbeTag)
            (currentSelectionSet : List Selection)
            (spine : List NormalSelectionSetObservableFieldStep),
          SelectionSet.size selectionSet < size
          -> selectionSetDeepProbeFuel schema normalParentType selectionSet ≤ fuel
          -> Validation.selectionSetValid schema variableDefinitions normalParentType
              selectionSet
          -> selectionSetDirectiveFree selectionSet
          -> selectionSetNormal schema normalParentType selectionSet
          -> SelectedFieldSpineRuntimeValid schema normalParentType runtimeType spine
          -> PathLocalSupportValidNormal schema runtimeType currentSelectionSet
          -> SelectedPathSelectionSetContextReady schema normalParentType
              runtimeType currentSelectionSet selectionSet
          -> ∃ fields errors,
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
              = ({ data := Execution.ResponseValue.object fields, errors := errors }
                  : Execution.Response) := by
  intro hschema size normalParentType variableDefinitions selectionSet fuel
    runtimeType targetParent leftField rightField leftArguments
    rightArguments leftRuntime rightRuntime tag currentSelectionSet spine
    hsize hfuel hvalid hfree hnormal hspineValid hsupport hcontextReady
  exact
    executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_of_valid_normal_runtimeSpine_support_context_fuel_ge_size
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet leftInitialSpine rightInitialSpine
      variableValues hschema size normalParentType variableDefinitions
      selectionSet fuel runtimeType targetParent leftField rightField
      leftArguments rightArguments leftRuntime rightRuntime tag
      currentSelectionSet spine hsize hfuel hvalid hfree hnormal
      hspineValid hsupport
      (fun hobject => hcontextReady.1 hobject)
      (fun hnonObject {directives} {bodySelectionSet} hmem =>
        hcontextReady.2 hnonObject
          (directives := directives) (bodySelectionSet := bodySelectionSet)
          hmem)

end GroundTypeNormalization

end NormalForm

end GraphQL
