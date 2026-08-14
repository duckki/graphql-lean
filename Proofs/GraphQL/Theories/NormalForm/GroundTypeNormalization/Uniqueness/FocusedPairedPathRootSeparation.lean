import Proofs.GraphQL.Execution.ArgumentCoercion
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.FocusedPairedPathSeparation
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.RuntimeDataDiffWitness

/-!
Root separation lemmas for heterogeneous paired selected paths.

The paired path may choose different concrete child runtimes on the two sides.
These lemmas lift the resulting child-data distinction through a root field
whose arguments or field names distinguish the two resolver targets.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

theorem PathLocalSelectionSetCurrentContext.of_mem_flatten
    {selectionSet : List Selection} {members : List (List Selection)}
    : selectionSet ∈ members
      -> PathLocalSelectionSetCurrentContext selectionSet (List.flatten members) := by
  intro hmember
  induction members with
  | nil =>
      simp at hmember
  | cons head tail ih =>
      rcases List.mem_cons.mp hmember with hhead | htail
      · subst selectionSet
        exact ⟨[], List.flatten tail, by simp⟩
      · rcases ih htail with ⟨pref, suff, hcontext⟩
        exact ⟨head ++ pref, suff, by simp [hcontext, List.append_assoc]⟩

theorem
    selectionSetFieldsExecuteOk_fieldPairOrDeepSuccess_selectedPathProbe_root_of_valid_normal_member
    {schema : Schema} {parentType leftFieldName rightFieldName : Name}
    {leftArguments rightArguments : List Argument} {leftRuntime rightRuntime : Name}
    {leftFieldDefinition rightFieldDefinition : FieldDefinition}
    {members : List (List Selection)} {selectionSet : List Selection} {parentFuel : Nat}
    (leftSpine rightSpine : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues)
    : SchemaWellFormedness.schemaWellFormed schema
      -> (∀ memberSelectionSet,
            memberSelectionSet ∈ members
            -> ∃ variableDefinitions,
                Validation.selectionSetValid schema variableDefinitions parentType
                  memberSelectionSet
                ∧ selectionSetDirectiveFree memberSelectionSet
                ∧ selectionSetNormal schema parentType memberSelectionSet)
      -> selectionSet ∈ members
      -> objectTypeNameBool schema parentType = true
      -> selectionSetDeepProbeFuel schema parentType (List.flatten members) ≤ parentFuel
      -> schema.lookupField parentType leftFieldName = some leftFieldDefinition
      -> schema.lookupField parentType rightFieldName = some rightFieldDefinition
      -> (TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> schema.typeIncludesObjectBool leftFieldDefinition.outputType.namedType
            leftRuntime
          = true
      -> schema.typeIncludesObjectBool rightFieldDefinition.outputType.namedType
            rightRuntime
          = true
      -> SelectedFieldSpineRuntimeValid schema
          leftFieldDefinition.outputType.namedType leftRuntime leftSpine
      -> SelectedFieldSpineRuntimeValid schema
          rightFieldDefinition.outputType.namedType rightRuntime rightSpine
      -> leafProbeFuel leftFieldDefinition.outputType ≤ parentFuel
      -> leafProbeFuel rightFieldDefinition.outputType ≤ parentFuel
      -> selectionSetFieldsExecuteOk schema
          (fieldPairOrDeepSuccessResolvers schema
            [Selection.inlineFragment (some parentType) [] (List.flatten members)]
            (fieldPairSelectedPathProbeResolvers schema
              (fieldPairPathLocalNextSelectionSet schema parentType leftRuntime
                leftFieldName leftArguments (List.flatten members))
              (fieldPairPathLocalNextSelectionSet schema parentType rightRuntime
                rightFieldName rightArguments (List.flatten members))
              leftSpine rightSpine parentType leftFieldName rightFieldName
              leftArguments rightArguments leftRuntime rightRuntime)
            parentType leftFieldName rightFieldName leftArguments
            rightArguments)
          variableValues (parentFuel + 1) parentType
          (projectionRootResolverValue
            (.object parentType FieldPairSelectedPathProbeRef.root))
          selectionSet := by
  intro hschema hmembers hmember hobject hparentFuel hleftLookup
    hrightLookup hleftComposite hrightComposite hleftInclude hrightInclude
    hleftSpineValid hrightSpineValid hleftLeafFuel hrightLeafFuel
  rcases hmembers selectionSet hmember with
    ⟨variableDefinitions, hvalid, hfree, hnormal⟩
  have hsupport :
      PathLocalSupportValidNormal schema parentType (List.flatten members) :=
    ⟨members, rfl, hmembers⟩
  have hcontext :
      PathLocalSelectionSetCurrentContext selectionSet
        (List.flatten members) :=
    PathLocalSelectionSetCurrentContext.of_mem_flatten hmember
  have hleftTarget :
      ∀ responseName arguments directives childSelectionSet,
        Selection.field responseName leftFieldName arguments directives
            childSelectionSet ∈ selectionSet ->
        Argument.argumentsEquivalent
            (Execution.coerceArgumentValues schema variableValues
              leftFieldDefinition.arguments arguments)
            leftArguments ->
          ∃ childFields childErrors,
            Execution.executeSelectionSetAsResponse schema
                (fieldPairOrDeepSuccessResolvers schema
                  [Selection.inlineFragment (some parentType) []
                    (List.flatten members)]
                  (fieldPairSelectedPathProbeResolvers schema
                    (fieldPairPathLocalNextSelectionSet schema parentType
                      leftRuntime leftFieldName leftArguments
                      (List.flatten members))
                    (fieldPairPathLocalNextSelectionSet schema parentType
                      rightRuntime rightFieldName rightArguments
                      (List.flatten members))
                    leftSpine rightSpine parentType leftFieldName
                    rightFieldName leftArguments rightArguments leftRuntime
                    rightRuntime)
                  parentType leftFieldName rightFieldName leftArguments
                  rightArguments)
                variableValues
                (parentFuel - leafProbeFuel leftFieldDefinition.outputType)
                leftRuntime
                (projectionTargetResolverValue
                  (.object leftRuntime
                    (FieldPairSelectedPathProbeRef.target
                      FieldPairProbeTag.left
                      (fieldPairPathLocalNextSelectionSet schema parentType
                        leftRuntime leftFieldName leftArguments
                        (List.flatten members))
                      leftSpine)))
                childSelectionSet =
              ({ data := Execution.ResponseValue.object childFields,
                 errors := childErrors } : Execution.Response) := by
    intro responseName arguments directives childSelectionSet hfieldMem
      harguments
    let childFuel :=
      parentFuel - leafProbeFuel leftFieldDefinition.outputType - 1
    have htargetFuel :
        selectionSetDeepProbeFuel schema
            leftFieldDefinition.outputType.namedType childSelectionSet ≤
          childFuel := by
      have hlocal :=
        selectionSetDeepProbeFuel_field_mem schema parentType selectionSet
          responseName leftFieldName arguments directives childSelectionSet
          leftFieldDefinition hfieldMem hleftLookup
      have hselectionFuel :=
        selectionSetDeepProbeFuel_le_flatten_member schema parentType
          (members := members) (selectionSet := selectionSet) hmember
      dsimp [childFuel]
      omega
    rcases
        executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_target_child_of_valid_normal_support_context_field_mem
          schema
          [Selection.inlineFragment (some parentType) []
            (List.flatten members)]
          (fieldPairPathLocalNextSelectionSet schema parentType leftRuntime
            leftFieldName leftArguments (List.flatten members))
          (fieldPairPathLocalNextSelectionSet schema parentType rightRuntime
            rightFieldName rightArguments (List.flatten members))
          leftSpine rightSpine variableValues hschema (parentType := parentType)
          (variableDefinitions := variableDefinitions)
          (selectionSet := selectionSet)
          (currentSelectionSet := List.flatten members) (fuel := childFuel)
          (responseName := responseName) (fieldName := leftFieldName)
          (runtimeType := leftRuntime) (targetParent := parentType)
          (leftField := leftFieldName) (rightField := rightFieldName)
          (targetArguments := leftArguments)
          (leftArguments := leftArguments) (rightArguments := rightArguments)
          (arguments := arguments) (directives := directives)
          (childSelectionSet := childSelectionSet)
          (fieldDefinition := leftFieldDefinition)
          (leftRuntime := leftRuntime) (rightRuntime := rightRuntime)
          (spine := leftSpine) (tag := FieldPairProbeTag.left) hvalid hfree
          hnormal hobject hsupport hcontext hfieldMem harguments hleftLookup
          hleftComposite hleftInclude hleftSpineValid htargetFuel with
      ⟨childFields, childErrors, hresponse⟩
    refine ⟨childFields, childErrors, ?_⟩
    have hfuelEq :
        childFuel + 1 =
          parentFuel - leafProbeFuel leftFieldDefinition.outputType := by
      have hlocal :=
        selectionSetDeepProbeFuel_field_mem schema parentType selectionSet
          responseName leftFieldName arguments directives childSelectionSet
          leftFieldDefinition hfieldMem hleftLookup
      have hselectionFuel :=
        selectionSetDeepProbeFuel_le_flatten_member schema parentType
          (members := members) (selectionSet := selectionSet) hmember
      dsimp [childFuel]
      omega
    simpa [hfuelEq] using hresponse
  have hrightTarget :
      ∀ responseName arguments directives childSelectionSet,
        Selection.field responseName rightFieldName arguments directives
            childSelectionSet ∈ selectionSet ->
        Argument.argumentsEquivalent
            (Execution.coerceArgumentValues schema variableValues
              rightFieldDefinition.arguments arguments)
            rightArguments ->
          ∃ childFields childErrors,
            Execution.executeSelectionSetAsResponse schema
                (fieldPairOrDeepSuccessResolvers schema
                  [Selection.inlineFragment (some parentType) []
                    (List.flatten members)]
                  (fieldPairSelectedPathProbeResolvers schema
                    (fieldPairPathLocalNextSelectionSet schema parentType
                      leftRuntime leftFieldName leftArguments
                      (List.flatten members))
                    (fieldPairPathLocalNextSelectionSet schema parentType
                      rightRuntime rightFieldName rightArguments
                      (List.flatten members))
                    leftSpine rightSpine parentType leftFieldName
                    rightFieldName leftArguments rightArguments leftRuntime
                    rightRuntime)
                  parentType leftFieldName rightFieldName leftArguments
                  rightArguments)
                variableValues
                (parentFuel - leafProbeFuel rightFieldDefinition.outputType)
                rightRuntime
                (projectionTargetResolverValue
                  (.object rightRuntime
                    (FieldPairSelectedPathProbeRef.target
                      FieldPairProbeTag.right
                      (fieldPairPathLocalNextSelectionSet schema parentType
                        rightRuntime rightFieldName rightArguments
                        (List.flatten members))
                      rightSpine)))
                childSelectionSet =
              ({ data := Execution.ResponseValue.object childFields,
                 errors := childErrors } : Execution.Response) := by
    intro responseName arguments directives childSelectionSet hfieldMem
      harguments
    let childFuel :=
      parentFuel - leafProbeFuel rightFieldDefinition.outputType - 1
    have htargetFuel :
        selectionSetDeepProbeFuel schema
            rightFieldDefinition.outputType.namedType childSelectionSet ≤
          childFuel := by
      have hlocal :=
        selectionSetDeepProbeFuel_field_mem schema parentType selectionSet
          responseName rightFieldName arguments directives childSelectionSet
          rightFieldDefinition hfieldMem hrightLookup
      have hselectionFuel :=
        selectionSetDeepProbeFuel_le_flatten_member schema parentType
          (members := members) (selectionSet := selectionSet) hmember
      dsimp [childFuel]
      omega
    rcases
        executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_target_child_of_valid_normal_support_context_field_mem
          schema
          [Selection.inlineFragment (some parentType) []
            (List.flatten members)]
          (fieldPairPathLocalNextSelectionSet schema parentType leftRuntime
            leftFieldName leftArguments (List.flatten members))
          (fieldPairPathLocalNextSelectionSet schema parentType rightRuntime
            rightFieldName rightArguments (List.flatten members))
          leftSpine rightSpine variableValues hschema (parentType := parentType)
          (variableDefinitions := variableDefinitions)
          (selectionSet := selectionSet)
          (currentSelectionSet := List.flatten members) (fuel := childFuel)
          (responseName := responseName) (fieldName := rightFieldName)
          (runtimeType := rightRuntime) (targetParent := parentType)
          (leftField := leftFieldName) (rightField := rightFieldName)
          (targetArguments := rightArguments)
          (leftArguments := leftArguments) (rightArguments := rightArguments)
          (arguments := arguments) (directives := directives)
          (childSelectionSet := childSelectionSet)
          (fieldDefinition := rightFieldDefinition)
          (leftRuntime := leftRuntime) (rightRuntime := rightRuntime)
          (spine := rightSpine) (tag := FieldPairProbeTag.right) hvalid hfree
          hnormal hobject hsupport hcontext hfieldMem harguments hrightLookup
          hrightComposite hrightInclude hrightSpineValid htargetFuel with
      ⟨childFields, childErrors, hresponse⟩
    refine ⟨childFields, childErrors, ?_⟩
    have hfuelEq :
        childFuel + 1 =
          parentFuel - leafProbeFuel rightFieldDefinition.outputType := by
      have hlocal :=
        selectionSetDeepProbeFuel_field_mem schema parentType selectionSet
          responseName rightFieldName arguments directives childSelectionSet
          rightFieldDefinition hfieldMem hrightLookup
      have hselectionFuel :=
        selectionSetDeepProbeFuel_le_flatten_member schema parentType
          (members := members) (selectionSet := selectionSet) hmember
      dsimp [childFuel]
      omega
    simpa [hfuelEq] using hresponse
  have hdeep :=
    selectionSet_deepSuccessFieldOk_framed_of_valid_normal_members
      (ProjectionResolverRef.filler :
        ProjectionResolverRef FieldPairSelectedPathProbeRef)
      variableValues
      (projectionRootResolverValue
        (.object parentType FieldPairSelectedPathProbeRef.root))
      parentFuel hschema hmembers hmember hobject hparentFuel
  have hother :=
    selectionSetOtherFieldsExecuteOk_fieldPairOrDeepSuccess_selectedPathProbe_of_deepSuccessWithRef_ok
      schema
      [Selection.inlineFragment (some parentType) [] (List.flatten members)]
      (fieldPairPathLocalNextSelectionSet schema parentType leftRuntime
        leftFieldName leftArguments (List.flatten members))
      (fieldPairPathLocalNextSelectionSet schema parentType rightRuntime
        rightFieldName rightArguments (List.flatten members))
      leftSpine rightSpine variableValues (parentFuel + 1) parentType leftFieldName
      rightFieldName leftArguments rightArguments leftRuntime rightRuntime
      selectionSet hdeep
  exact
    selectionSetFieldsExecuteOk_fieldPairOrDeepSuccess_selectedPathProbe_of_field_cases
      schema
      [Selection.inlineFragment (some parentType) [] (List.flatten members)]
      (fieldPairPathLocalNextSelectionSet schema parentType leftRuntime
        leftFieldName leftArguments (List.flatten members))
      (fieldPairPathLocalNextSelectionSet schema parentType rightRuntime
        rightFieldName rightArguments (List.flatten members))
      leftSpine rightSpine variableValues parentFuel parentType leftFieldName
      rightFieldName leftArguments rightArguments leftRuntime rightRuntime
      leftFieldDefinition rightFieldDefinition selectionSet hleftLookup
      hrightLookup hleftInclude hrightInclude hleftLeafFuel hrightLeafFuel
      hleftTarget hrightTarget hother

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_root_field_head_child_response_diff_of_field_ok
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (leftSpine rightSpine : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (parentFuel : Nat)
    (parentType responseName leftFieldName rightFieldName : Name)
    (leftArguments rightArguments leftFieldArguments rightFieldArguments : List Argument)
    (leftRuntime rightRuntime : Name) {left right : List Selection}
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
      -> Selection.field responseName leftFieldName leftFieldArguments
            leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName rightFieldName rightFieldArguments
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
      -> Argument.argumentsEquivalent
          (Execution.coerceArgumentValues schema variableValues
            leftFieldDefinition.arguments leftFieldArguments)
          leftArguments
      -> Argument.argumentsEquivalent
          (Execution.coerceArgumentValues schema variableValues
            rightFieldDefinition.arguments rightFieldArguments)
          rightArguments
      -> (∀ arguments,
            Argument.argumentsEquivalent
              (Execution.coerceArgumentValues schema variableValues
                rightFieldDefinition.arguments arguments)
              rightArguments
            -> ¬ fieldProbeTarget parentType leftFieldName leftArguments parentType
                  rightFieldName
                  (Execution.coerceArgumentValues schema variableValues
                    rightFieldDefinition.arguments arguments))
      -> Execution.executeSelectionSetAsResponse schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet leftSpine rightSpine parentType
                leftFieldName rightFieldName leftArguments rightArguments
                leftRuntime rightRuntime)
              parentType leftFieldName rightFieldName leftArguments
              rightArguments)
            variableValues (parentFuel - leafProbeFuel leftFieldDefinition.outputType)
            leftRuntime
            (projectionTargetResolverValue
              (.object leftRuntime
                (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
                  leftInitialSelectionSet leftSpine)))
            leftChildSelectionSet
          = ({
                data := Execution.ResponseValue.object leftChildFields,
                errors := leftChildErrors
              }
              : Execution.Response)
      -> Execution.executeSelectionSetAsResponse schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet leftSpine rightSpine parentType
                leftFieldName rightFieldName leftArguments rightArguments
                leftRuntime rightRuntime)
              parentType leftFieldName rightFieldName leftArguments
              rightArguments)
            variableValues (parentFuel - leafProbeFuel rightFieldDefinition.outputType)
            rightRuntime
            (projectionTargetResolverValue
              (.object rightRuntime
                (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                  rightInitialSelectionSet rightSpine)))
            rightChildSelectionSet
          = ({
                data := Execution.ResponseValue.object rightChildFields,
                errors := rightChildErrors
              }
              : Execution.Response)
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.ResponseValue.object leftChildFields)
            (Execution.ResponseValue.object rightChildFields)
      -> selectionSetFieldsExecuteOk schema
          (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
            (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
              rightInitialSelectionSet leftSpine rightSpine parentType
              leftFieldName rightFieldName leftArguments rightArguments
              leftRuntime rightRuntime)
            parentType leftFieldName rightFieldName leftArguments rightArguments)
          variableValues (parentFuel + 1) parentType
          (projectionRootResolverValue
            (.object parentType FieldPairSelectedPathProbeRef.root)) left
      -> selectionSetFieldsExecuteOk schema
          (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
            (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
              rightInitialSelectionSet leftSpine rightSpine parentType
              leftFieldName rightFieldName leftArguments rightArguments
              leftRuntime rightRuntime)
            parentType leftFieldName rightFieldName leftArguments rightArguments)
          variableValues (parentFuel + 1) parentType
          (projectionRootResolverValue
            (.object parentType FieldPairSelectedPathProbeRef.root)) right
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSelectedPathProbeResolvers schema
                  leftInitialSelectionSet rightInitialSelectionSet leftSpine
                  rightSpine parentType leftFieldName rightFieldName
                  leftArguments rightArguments leftRuntime rightRuntime)
                parentType leftFieldName rightFieldName leftArguments
                rightArguments)
              variableValues (parentFuel + 1) parentType
              (projectionRootResolverValue
                (.object parentType FieldPairSelectedPathProbeRef.root)) left).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSelectedPathProbeResolvers schema
                  leftInitialSelectionSet rightInitialSelectionSet leftSpine
                  rightSpine parentType leftFieldName rightFieldName
                  leftArguments rightArguments leftRuntime rightRuntime)
                parentType leftFieldName rightFieldName leftArguments
                rightArguments)
              variableValues (parentFuel + 1) parentType
              (projectionRootResolverValue
                (.object parentType FieldPairSelectedPathProbeRef.root))
              right).data := by
  intro hobject hleftNormal hrightNormal hleftFree hrightFree hleftMem
    hrightMem hleftLookup hrightLookup hleftInclude hrightInclude
    hleftLeafFuel hrightLeafFuel hleftCoerced hrightCoerced
    hrightNotLeft hleftChildResponse
    hrightChildResponse hchildNot hleftFieldOk hrightFieldOk
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet
      (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
        rightInitialSelectionSet leftSpine rightSpine parentType
        leftFieldName rightFieldName leftArguments rightArguments
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
      Execution.executeField schema resolvers variableValues (parentFuel + 1) source
        responseName
        [{
          parentType := parentType
          responseName := responseName
          fieldName := leftFieldName
          arguments := leftFieldArguments
          selectionSet := leftChildSelectionSet
        }] =
      .ok ([(responseName, leftValue)], leftFieldErrors) := by
    dsimp [resolvers, source]
    have hleftChildRaw :
        Execution.selectionSetResultToResponse
          (Execution.executeCollectedFields schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairSelectedPathProbeResolvers schema
                leftInitialSelectionSet rightInitialSelectionSet leftSpine
                rightSpine parentType leftFieldName rightFieldName
                leftArguments rightArguments leftRuntime rightRuntime)
              parentType leftFieldName rightFieldName leftArguments
              rightArguments)
            variableValues (parentFuel - leafProbeFuel leftFieldDefinition.outputType)
            (projectionTargetResolverValue
              (.object leftRuntime
                (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
                  leftInitialSelectionSet leftSpine)))
            (Execution.collectFields schema variableValues leftRuntime
              (projectionTargetResolverValue
                (.object leftRuntime
                  (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
                    leftInitialSelectionSet leftSpine)))
              leftChildSelectionSet)) =
          ({ data := Execution.ResponseValue.object leftChildFields,
             errors := leftChildErrors } : Execution.Response) := by
      simpa [Execution.executeSelectionSetAsResponse, Execution.executeSelectionSet,
        Execution.executeRootSelectionSet] using hleftChildResponse
    have hfield :=
      executeField_fieldPairOrDeepSuccess_selectedPathProbe_left_root_response
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftSpine rightSpine variableValues
        (parentFuel - leafProbeFuel leftFieldDefinition.outputType)
        parentType leftFieldName rightFieldName responseName leftArguments
        rightArguments leftFieldArguments leftRuntime rightRuntime
        leftChildSelectionSet leftFieldDefinition
        hleftCoerced hleftLookup
        hleftInclude
    have hfuelEq :
        parentFuel - leafProbeFuel leftFieldDefinition.outputType
            + leafProbeFuel leftFieldDefinition.outputType + 1 =
          parentFuel + 1 := by
      omega
    simpa [hleftChildRaw, hleftWrapped, Execution.singleFieldResult,
      hfuelEq] using hfield
  have hrightTarget :
      Execution.executeField schema resolvers variableValues (parentFuel + 1) source
        responseName
        [{
          parentType := parentType
          responseName := responseName
          fieldName := rightFieldName
          arguments := rightFieldArguments
          selectionSet := rightChildSelectionSet
        }] =
      .ok ([(responseName, rightValue)], rightFieldErrors) := by
    dsimp [resolvers, source]
    have hrightChildRaw :
        Execution.selectionSetResultToResponse
          (Execution.executeCollectedFields schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairSelectedPathProbeResolvers schema
                leftInitialSelectionSet rightInitialSelectionSet leftSpine
                rightSpine parentType leftFieldName rightFieldName
                leftArguments rightArguments leftRuntime rightRuntime)
              parentType leftFieldName rightFieldName leftArguments
              rightArguments)
            variableValues (parentFuel - leafProbeFuel rightFieldDefinition.outputType)
            (projectionTargetResolverValue
              (.object rightRuntime
                (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                  rightInitialSelectionSet rightSpine)))
            (Execution.collectFields schema variableValues rightRuntime
              (projectionTargetResolverValue
                (.object rightRuntime
                  (FieldPairSelectedPathProbeRef.target
                    FieldPairProbeTag.right rightInitialSelectionSet
                    rightSpine)))
              rightChildSelectionSet)) =
          ({ data := Execution.ResponseValue.object rightChildFields,
             errors := rightChildErrors } : Execution.Response) := by
      simpa [Execution.executeSelectionSetAsResponse, Execution.executeSelectionSet,
        Execution.executeRootSelectionSet] using hrightChildResponse
    have hnotLeft :=
      hrightNotLeft rightFieldArguments hrightCoerced
    have hfield :=
      executeField_fieldPairOrDeepSuccess_selectedPathProbe_right_root_response_of_not_left
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftSpine rightSpine variableValues
        (parentFuel - leafProbeFuel rightFieldDefinition.outputType)
        parentType leftFieldName rightFieldName responseName leftArguments
        rightArguments rightFieldArguments leftRuntime rightRuntime
        rightChildSelectionSet rightFieldDefinition hnotLeft
        hrightCoerced hrightLookup
        hrightInclude
    have hfuelEq :
        parentFuel - leafProbeFuel rightFieldDefinition.outputType
            + leafProbeFuel rightFieldDefinition.outputType + 1 =
          parentFuel + 1 := by
      omega
    simpa [hrightChildRaw, hrightWrapped, Execution.singleFieldResult,
      hfuelEq] using hfield
  have hvalueNot :
      ¬ Execution.ResponseValue.semanticEquivalent leftValue rightValue :=
    wrapped_object_values_not_semanticEquivalent_of_child
      leftFieldDefinition.outputType rightFieldDefinition.outputType
      hleftWrapped hrightWrapped hchildNot
  simpa [resolvers, source] using
    SemanticSeparation.responseData_not_semanticEquivalent_of_field_value_diff_of_field_ok
      (schema := schema) (parentType := parentType) (left := left)
      (right := right) (responseName := responseName)
      (leftFieldName := leftFieldName) (rightFieldName := rightFieldName)
      (leftArguments := leftFieldArguments)
      (rightArguments := rightFieldArguments)
      (leftDirectives := leftDirectives) (rightDirectives := rightDirectives)
      (leftChildSelectionSet := leftChildSelectionSet)
      (rightChildSelectionSet := rightChildSelectionSet) resolvers resolvers
      variableValues (parentFuel + 1) source source hobject hleftNormal hrightNormal
      hleftFree hrightFree hleftMem hrightMem hleftTarget hrightTarget
      hvalueNot hleftFieldOk hrightFieldOk

theorem
    selectionSetContextualRuntimeDataDiffWitnessWithFuelGe_of_valid_normal_object_field_head_diff_composite_pairedPath_finiteSupport
    {schema : Schema}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    {parentType : Name} {left right : List Selection}
    {supportSelectionSets : List (List Selection)}
    {responseName leftFieldName rightFieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {leftFieldDefinition rightFieldDefinition : FieldDefinition} {minFuel : Nat}
    {variableValues : Execution.VariableValues}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions parentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> objectTypeNameBool schema parentType = true
      -> (∀ supportSelectionSet,
            supportSelectionSet ∈ supportSelectionSets
            -> ∃ variableDefinitions,
                Validation.selectionSetValid schema variableDefinitions parentType
                  supportSelectionSet
                ∧ selectionSetDirectiveFree supportSelectionSet
                ∧ selectionSetNormal schema parentType supportSelectionSet)
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
          = true
      -> (∀ arguments,
            Argument.argumentsEquivalent
              (Execution.coerceArgumentValues schema variableValues
                rightFieldDefinition.arguments arguments)
              (Execution.coerceArgumentValues schema variableValues
                rightFieldDefinition.arguments rightArguments)
            -> ¬ fieldProbeTarget parentType leftFieldName
                  (Execution.coerceArgumentValues schema variableValues
                    leftFieldDefinition.arguments leftArguments)
                  parentType rightFieldName
                  (Execution.coerceArgumentValues schema variableValues
                    rightFieldDefinition.arguments arguments))
      -> selectionSetContextualRuntimeDataDiffWitnessWithFuelGe schema
          parentType parentType left right
          (variableValues := variableValues)
          (fun selectionSet => selectionSet ∈ supportSelectionSets)
          minFuel := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hobject hsupportValid hleftMem hrightMem hleftLookup
    hrightLookup hleftComposite hrightComposite hrightNotLeft
  let members : List (List Selection) :=
    left :: right :: supportSelectionSets
  let currentSelectionSet : List Selection := List.flatten members
  let rootSelectionSet : List Selection :=
    [Selection.inlineFragment (some parentType) [] currentSelectionSet]
  let leftTargetArguments :=
    Execution.coerceArgumentValues schema variableValues leftFieldDefinition.arguments
      leftArguments
  let rightTargetArguments :=
    Execution.coerceArgumentValues schema variableValues rightFieldDefinition.arguments
      rightArguments
  let parentFuel :=
    max minFuel
      (selectionSetDeepProbeFuel schema parentType currentSelectionSet)
  let leftChildFuel :=
    parentFuel - leafProbeFuel leftFieldDefinition.outputType - 1
  let rightChildFuel :=
    parentFuel - leafProbeFuel rightFieldDefinition.outputType - 1
  have hmembers :
      ∀ memberSelectionSet,
        memberSelectionSet ∈ members ->
          ∃ variableDefinitions,
            Validation.selectionSetValid schema variableDefinitions
              parentType memberSelectionSet
            ∧ selectionSetDirectiveFree memberSelectionSet
            ∧ selectionSetNormal schema parentType memberSelectionSet := by
    intro memberSelectionSet hmember
    simp [members] at hmember
    rcases hmember with hleft | hright | hsupport
    · subst memberSelectionSet
      exact ⟨leftVariableDefinitions, hleftValid, hleftFree, hleftNormal⟩
    · subst memberSelectionSet
      exact ⟨rightVariableDefinitions, hrightValid, hrightFree,
        hrightNormal⟩
    · exact hsupportValid memberSelectionSet hsupport
  have hleftMember : left ∈ members := by simp [members]
  have hrightMember : right ∈ members := by simp [members]
  have hparentFuel :
      selectionSetDeepProbeFuel schema parentType currentSelectionSet ≤
        parentFuel := by
    dsimp [parentFuel]
    exact Nat.le_max_right _ _
  have hminFuel : minFuel ≤ parentFuel + 1 := by
    have hle : minFuel ≤ parentFuel := by
      dsimp [parentFuel]
      exact Nat.le_max_left _ _
    exact Nat.le_trans hle (Nat.le_succ _)
  have hinclude :
      schema.typeIncludesObjectBool parentType parentType = true :=
    typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject
  have hleftChildNonempty : leftChildSelectionSet ≠ [] :=
    selectionSet_nonempty_of_valid_field_mem_lookup_compositeBool
      hleftValid hleftMem hleftLookup hleftComposite
  have hrightChildNonempty : rightChildSelectionSet ≠ [] :=
    selectionSet_nonempty_of_valid_field_mem_lookup_compositeBool
      hrightValid hrightMem hrightLookup hrightComposite
  have hleftChildValid :
      Validation.selectionSetValid schema leftVariableDefinitions
        leftFieldDefinition.outputType.namedType leftChildSelectionSet :=
    selectionSetValid_field_child_of_mem_lookup hleftValid hleftMem
      hleftChildNonempty hleftLookup
  have hrightChildValid :
      Validation.selectionSetValid schema rightVariableDefinitions
        rightFieldDefinition.outputType.namedType rightChildSelectionSet :=
    selectionSetValid_field_child_of_mem_lookup hrightValid hrightMem
      hrightChildNonempty hrightLookup
  have hleftChildFree : selectionSetDirectiveFree leftChildSelectionSet :=
    selectionSetDirectiveFree_field_child_of_mem hleftFree hleftMem
  have hrightChildFree : selectionSetDirectiveFree rightChildSelectionSet :=
    selectionSetDirectiveFree_field_child_of_mem hrightFree hrightMem
  have hleftChildNormal :
      selectionSetNormal schema leftFieldDefinition.outputType.namedType
        leftChildSelectionSet :=
    selectionSetNormal_field_child_of_mem_lookup hleftNormal hleftMem
      hleftLookup
  have hrightChildNormal :
      selectionSetNormal schema rightFieldDefinition.outputType.namedType
        rightChildSelectionSet :=
    selectionSetNormal_field_child_of_mem_lookup hrightNormal hrightMem
      hrightLookup
  have hleftMemCurrent :
      Selection.field responseName leftFieldName leftArguments leftDirectives
        leftChildSelectionSet ∈ currentSelectionSet := by
    dsimp [currentSelectionSet]
    rw [List.mem_flatten]
    exact ⟨left, hleftMember, hleftMem⟩
  have hrightMemCurrent :
      Selection.field responseName rightFieldName rightArguments
        rightDirectives rightChildSelectionSet ∈ currentSelectionSet := by
    dsimp [currentSelectionSet]
    rw [List.mem_flatten]
    exact ⟨right, hrightMember, hrightMem⟩
  have hleftChildFuel :
      selectionSetDeepProbeFuel schema
          leftFieldDefinition.outputType.namedType leftChildSelectionSet ≤
        leftChildFuel := by
    have hlocal :=
      selectionSetDeepProbeFuel_field_mem schema parentType
        currentSelectionSet responseName leftFieldName leftArguments
        leftDirectives leftChildSelectionSet leftFieldDefinition
        hleftMemCurrent hleftLookup
    dsimp [leftChildFuel]
    omega
  have hrightChildFuel :
      selectionSetDeepProbeFuel schema
          rightFieldDefinition.outputType.namedType rightChildSelectionSet ≤
        rightChildFuel := by
    have hlocal :=
      selectionSetDeepProbeFuel_field_mem schema parentType
        currentSelectionSet responseName rightFieldName rightArguments
        rightDirectives rightChildSelectionSet rightFieldDefinition
        hrightMemCurrent hrightLookup
    dsimp [rightChildFuel]
    omega
  have hleftLeafFuel :
      leafProbeFuel leftFieldDefinition.outputType ≤ parentFuel := by
    have hlocal :=
      leafProbeFuel_le_selectionSetDeepProbeFuel_of_field_mem schema
        parentType hleftMemCurrent hleftLookup
    omega
  have hrightLeafFuel :
      leafProbeFuel rightFieldDefinition.outputType ≤ parentFuel := by
    have hlocal :=
      leafProbeFuel_le_selectionSetDeepProbeFuel_of_field_mem schema
        parentType hrightMemCurrent hrightLookup
    omega
  have hpairedPath :
      NormalSelectionSetPairedPath schema
        leftFieldDefinition.outputType.namedType
        rightFieldDefinition.outputType.namedType leftChildSelectionSet
        rightChildSelectionSet :=
    normalSelectionSetPairedPath_of_valid_normal_nonempty hleftChildValid
      hrightChildValid hleftChildNormal hrightChildNormal hleftChildNonempty
      hrightChildNonempty
  rcases
      normalSelectionSetPairedPathDataDiff_of_valid_normal schema
        rootSelectionSet variableValues leftChildFuel rightChildFuel parentType
        leftFieldName rightFieldName leftTargetArguments rightTargetArguments
        hschema
        hleftChildValid hrightChildValid hleftChildFree hrightChildFree
        hleftChildNormal hrightChildNormal hleftChildFuel hrightChildFuel
        hleftChildNonempty hrightChildNonempty hpairedPath with
    ⟨leftRuntime, rightRuntime, leftSpine, rightSpine,
      hleftSpineValid, hrightSpineValid, hdataBuilder⟩
  have hleftInclude :
      schema.typeIncludesObjectBool
        leftFieldDefinition.outputType.namedType leftRuntime = true :=
    selectedFieldSpineRuntimeValid_typeIncludes hleftSpineValid
  have hrightInclude :
      schema.typeIncludesObjectBool
        rightFieldDefinition.outputType.namedType rightRuntime = true :=
    selectedFieldSpineRuntimeValid_typeIncludes hrightSpineValid
  have hleftRuntimeObject : objectTypeNameBool schema leftRuntime = true :=
    objectTypeNameBool_of_typeIncludesObjectBool hschema hleftInclude
  have hrightRuntimeObject : objectTypeNameBool schema rightRuntime = true :=
    objectTypeNameBool_of_typeIncludesObjectBool hschema hrightInclude
  let leftInitialSelectionSet : List Selection :=
    fieldPairPathLocalNextSelectionSet schema parentType leftRuntime
      leftFieldName leftArguments currentSelectionSet
  let rightInitialSelectionSet : List Selection :=
    fieldPairPathLocalNextSelectionSet schema parentType rightRuntime
      rightFieldName rightArguments currentSelectionSet
  let leftRootSpine : List NormalSelectionSetObservableFieldStep :=
    ({ responseName := responseName, fieldName := leftFieldName,
       arguments := leftArguments, childRuntime := some leftRuntime } ::
      leftSpine)
  let rightRootSpine : List NormalSelectionSetObservableFieldStep :=
    ({ responseName := responseName, fieldName := rightFieldName,
       arguments := rightArguments, childRuntime := some rightRuntime } ::
      rightSpine)
  have hleftSource :
      SelectedPathCompositeFieldChildSource schema parentType leftFieldName
        leftArguments currentSelectionSet leftRootSpine leftFieldDefinition
        leftRuntime leftSpine := by
    simpa [leftRootSpine] using
      (selectedPathCompositeFieldChildSource_cons
        (schema := schema) (parentType := parentType)
        (responseName := responseName) (fieldName := leftFieldName)
        (arguments := leftArguments)
        (currentSelectionSet := currentSelectionSet)
        (fieldDefinition := leftFieldDefinition) (childRuntime := leftRuntime)
        (childSpine := leftSpine) hleftComposite hleftSpineValid)
  have hrightSource :
      SelectedPathCompositeFieldChildSource schema parentType rightFieldName
        rightArguments currentSelectionSet rightRootSpine
        rightFieldDefinition rightRuntime rightSpine := by
    simpa [rightRootSpine] using
      (selectedPathCompositeFieldChildSource_cons
        (schema := schema) (parentType := parentType)
        (responseName := responseName) (fieldName := rightFieldName)
        (arguments := rightArguments)
        (currentSelectionSet := currentSelectionSet)
        (fieldDefinition := rightFieldDefinition)
        (childRuntime := rightRuntime) (childSpine := rightSpine)
        hrightComposite hrightSpineValid)
  have hsupport :
      PathLocalSupportValidNormal schema parentType currentSelectionSet := by
    exact ⟨members, rfl, hmembers⟩
  have hleftContext :
      PathLocalSelectionSetCurrentContext left currentSelectionSet := by
    dsimp [currentSelectionSet]
    exact PathLocalSelectionSetCurrentContext.of_mem_flatten hleftMember
  have hrightContext :
      PathLocalSelectionSetCurrentContext right currentSelectionSet := by
    dsimp [currentSelectionSet]
    exact PathLocalSelectionSetCurrentContext.of_mem_flatten hrightMember
  have hleftChildSupport :
      PathLocalSupportValidNormal schema leftRuntime
        leftInitialSelectionSet :=
    pathLocalSupportValidNormal_fieldPairPathLocalNextSelectionSet_of_selectedPathCompositeFieldChildSource
      hsupport hobject hleftRuntimeObject hleftLookup hleftSource
      hleftInclude
  have hrightChildSupport :
      PathLocalSupportValidNormal schema rightRuntime
        rightInitialSelectionSet :=
    pathLocalSupportValidNormal_fieldPairPathLocalNextSelectionSet_of_selectedPathCompositeFieldChildSource
      hsupport hobject hrightRuntimeObject hrightLookup hrightSource
      hrightInclude
  have hleftChildContext :
      SelectedPathSelectionSetContextReady schema
        leftFieldDefinition.outputType.namedType leftRuntime
        leftInitialSelectionSet leftChildSelectionSet :=
    selectedPathSelectionSetContextReady_fieldPairPathLocalNextSelectionSet_of_selectedPathCompositeFieldChildSource
      hleftContext hleftMem hleftLookup hleftChildNormal hleftSource
      hleftRuntimeObject
  have hrightChildContext :
      SelectedPathSelectionSetContextReady schema
        rightFieldDefinition.outputType.namedType rightRuntime
        rightInitialSelectionSet rightChildSelectionSet :=
    selectedPathSelectionSetContextReady_fieldPairPathLocalNextSelectionSet_of_selectedPathCompositeFieldChildSource
      hrightContext hrightMem hrightLookup hrightChildNormal hrightSource
      hrightRuntimeObject
  have hchildDataDiff :=
    hdataBuilder leftInitialSelectionSet rightInitialSelectionSet leftSpine
      rightSpine leftRuntime rightRuntime leftInitialSelectionSet
      rightInitialSelectionSet hleftChildSupport hrightChildSupport
      hleftChildContext hrightChildContext
  have hleftChildFuelEq :
      leftChildFuel + 1 =
        parentFuel - leafProbeFuel leftFieldDefinition.outputType := by
    have hlocal :=
      selectionSetDeepProbeFuel_field_mem schema parentType
        currentSelectionSet responseName leftFieldName leftArguments
        leftDirectives leftChildSelectionSet leftFieldDefinition
        hleftMemCurrent hleftLookup
    dsimp [leftChildFuel]
    omega
  have hrightChildFuelEq :
      rightChildFuel + 1 =
        parentFuel - leafProbeFuel rightFieldDefinition.outputType := by
    have hlocal :=
      selectionSetDeepProbeFuel_field_mem schema parentType
        currentSelectionSet responseName rightFieldName rightArguments
        rightDirectives rightChildSelectionSet rightFieldDefinition
        hrightMemCurrent hrightLookup
    dsimp [rightChildFuel]
    omega
  rcases
      executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_target_child_of_valid_normal_support_context_field_mem
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftSpine rightSpine variableValues hschema
        (parentType := parentType)
        (variableDefinitions := leftVariableDefinitions)
        (selectionSet := left) (currentSelectionSet := currentSelectionSet)
        (fuel := leftChildFuel) (responseName := responseName)
        (fieldName := leftFieldName) (runtimeType := leftRuntime)
        (targetParent := parentType) (leftField := leftFieldName)
        (rightField := rightFieldName) (targetArguments := leftTargetArguments)
        (leftArguments := leftTargetArguments)
        (rightArguments := rightTargetArguments)
        (arguments := leftArguments) (directives := leftDirectives)
        (childSelectionSet := leftChildSelectionSet)
        (fieldDefinition := leftFieldDefinition)
        (leftRuntime := leftRuntime) (rightRuntime := rightRuntime)
        (spine := leftSpine) (tag := FieldPairProbeTag.left) hleftValid
        hleftFree hleftNormal hobject hsupport hleftContext hleftMem
        (argumentsEquivalent_refl_forSyntaxDiff leftTargetArguments)
        hleftLookup
        hleftComposite hleftInclude hleftSpineValid hleftChildFuel with
    ⟨leftChildFields, leftChildErrors, hleftChildResponseRaw⟩
  rcases
      executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_target_child_of_valid_normal_support_context_field_mem
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftSpine rightSpine variableValues hschema
        (parentType := parentType)
        (variableDefinitions := rightVariableDefinitions)
        (selectionSet := right) (currentSelectionSet := currentSelectionSet)
        (fuel := rightChildFuel) (responseName := responseName)
        (fieldName := rightFieldName) (runtimeType := rightRuntime)
        (targetParent := parentType) (leftField := leftFieldName)
        (rightField := rightFieldName) (targetArguments := rightTargetArguments)
        (leftArguments := leftTargetArguments)
        (rightArguments := rightTargetArguments)
        (arguments := rightArguments) (directives := rightDirectives)
        (childSelectionSet := rightChildSelectionSet)
        (fieldDefinition := rightFieldDefinition)
        (leftRuntime := leftRuntime) (rightRuntime := rightRuntime)
        (spine := rightSpine) (tag := FieldPairProbeTag.right) hrightValid
        hrightFree hrightNormal hobject hsupport hrightContext hrightMem
        (argumentsEquivalent_refl_forSyntaxDiff rightTargetArguments)
        hrightLookup
        hrightComposite hrightInclude hrightSpineValid hrightChildFuel with
    ⟨rightChildFields, rightChildErrors, hrightChildResponseRaw⟩
  have hleftChildResponse :
      Execution.executeSelectionSetAsResponse schema
          (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
            (fieldPairSelectedPathProbeResolvers schema
              leftInitialSelectionSet rightInitialSelectionSet leftSpine
              rightSpine parentType leftFieldName rightFieldName
              leftTargetArguments rightTargetArguments leftRuntime
              rightRuntime)
            parentType leftFieldName rightFieldName leftTargetArguments
            rightTargetArguments)
          variableValues (parentFuel - leafProbeFuel leftFieldDefinition.outputType)
          leftRuntime
          (projectionTargetResolverValue
            (.object leftRuntime
              (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
                leftInitialSelectionSet leftSpine)))
          leftChildSelectionSet =
        ({ data := Execution.ResponseValue.object leftChildFields,
           errors := leftChildErrors } : Execution.Response) := by
    rw [fieldPairPathLocalNextSelectionSet_eq_of_arguments schema parentType
      leftRuntime leftFieldName leftTargetArguments leftArguments
      currentSelectionSet] at hleftChildResponseRaw
    simpa [hleftChildFuelEq] using hleftChildResponseRaw
  have hrightChildResponse :
      Execution.executeSelectionSetAsResponse schema
          (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
            (fieldPairSelectedPathProbeResolvers schema
              leftInitialSelectionSet rightInitialSelectionSet leftSpine
              rightSpine parentType leftFieldName rightFieldName
              leftTargetArguments rightTargetArguments leftRuntime
              rightRuntime)
            parentType leftFieldName rightFieldName leftTargetArguments
            rightTargetArguments)
          variableValues (parentFuel - leafProbeFuel rightFieldDefinition.outputType)
          rightRuntime
          (projectionTargetResolverValue
            (.object rightRuntime
              (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                rightInitialSelectionSet rightSpine)))
          rightChildSelectionSet =
        ({ data := Execution.ResponseValue.object rightChildFields,
           errors := rightChildErrors } : Execution.Response) := by
    rw [fieldPairPathLocalNextSelectionSet_eq_of_arguments schema parentType
      rightRuntime rightFieldName rightTargetArguments rightArguments
      currentSelectionSet] at hrightChildResponseRaw
    simpa [hrightChildFuelEq] using hrightChildResponseRaw
  have hchildNot :
      ¬ Execution.ResponseValue.semanticEquivalent
        (Execution.ResponseValue.object leftChildFields)
        (Execution.ResponseValue.object rightChildFields) := by
    intro hsemantic
    exact hchildDataDiff.2.2.2.2 (by
      simpa [SelectedPathSelectionSetsResponseDataDiff,
        hleftChildResponse, hrightChildResponse, hleftChildFuelEq,
        hrightChildFuelEq] using hsemantic)
  have hleftFieldOk :=
    selectionSetFieldsExecuteOk_fieldPairOrDeepSuccess_selectedPathProbe_root_of_valid_normal_member
      (schema := schema) (parentType := parentType)
      (leftFieldName := leftFieldName) (rightFieldName := rightFieldName)
      (leftArguments := leftTargetArguments)
      (rightArguments := rightTargetArguments)
      (leftRuntime := leftRuntime) (rightRuntime := rightRuntime)
      (leftFieldDefinition := leftFieldDefinition)
      (rightFieldDefinition := rightFieldDefinition) (members := members)
      (selectionSet := left) (parentFuel := parentFuel) leftSpine rightSpine
      variableValues
      hschema hmembers hleftMember hobject hparentFuel hleftLookup
      hrightLookup hleftComposite hrightComposite hleftInclude hrightInclude
      hleftSpineValid hrightSpineValid hleftLeafFuel hrightLeafFuel
  rw [fieldPairPathLocalNextSelectionSet_eq_of_arguments schema parentType
    leftRuntime leftFieldName leftTargetArguments leftArguments
    currentSelectionSet,
    fieldPairPathLocalNextSelectionSet_eq_of_arguments schema parentType
      rightRuntime rightFieldName rightTargetArguments rightArguments
      currentSelectionSet] at hleftFieldOk
  have hrightFieldOk :=
    selectionSetFieldsExecuteOk_fieldPairOrDeepSuccess_selectedPathProbe_root_of_valid_normal_member
      (schema := schema) (parentType := parentType)
      (leftFieldName := leftFieldName) (rightFieldName := rightFieldName)
      (leftArguments := leftTargetArguments)
      (rightArguments := rightTargetArguments)
      (leftRuntime := leftRuntime) (rightRuntime := rightRuntime)
      (leftFieldDefinition := leftFieldDefinition)
      (rightFieldDefinition := rightFieldDefinition) (members := members)
      (selectionSet := right) (parentFuel := parentFuel) leftSpine rightSpine
      variableValues
      hschema hmembers hrightMember hobject hparentFuel hleftLookup
      hrightLookup hleftComposite hrightComposite hleftInclude hrightInclude
      hleftSpineValid hrightSpineValid hleftLeafFuel hrightLeafFuel
  rw [fieldPairPathLocalNextSelectionSet_eq_of_arguments schema parentType
    leftRuntime leftFieldName leftTargetArguments leftArguments
    currentSelectionSet,
    fieldPairPathLocalNextSelectionSet_eq_of_arguments schema parentType
      rightRuntime rightFieldName rightTargetArguments rightArguments
      currentSelectionSet] at hrightFieldOk
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet
      (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
        rightInitialSelectionSet leftSpine rightSpine parentType
        leftFieldName rightFieldName leftTargetArguments
        rightTargetArguments
        leftRuntime rightRuntime)
      parentType leftFieldName rightFieldName leftTargetArguments
      rightTargetArguments
  let source :=
    projectionRootResolverValue
      (.object parentType FieldPairSelectedPathProbeRef.root)
  have hdataNot :
      ¬ Execution.ResponseValue.semanticEquivalent
        (Execution.executeSelectionSetAsResponse schema resolvers variableValues (parentFuel + 1)
          parentType source left).data
        (Execution.executeSelectionSetAsResponse schema resolvers variableValues (parentFuel + 1)
          parentType source right).data := by
    simpa [resolvers, source, rootSelectionSet, currentSelectionSet] using
      responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_root_field_head_child_response_diff_of_field_ok
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftSpine rightSpine variableValues parentFuel parentType
        responseName leftFieldName rightFieldName leftTargetArguments
        rightTargetArguments leftArguments rightArguments leftRuntime
        rightRuntime hobject hleftNormal
        hrightNormal hleftFree hrightFree hleftMem hrightMem hleftLookup
        hrightLookup hleftInclude hrightInclude hleftLeafFuel
        hrightLeafFuel
        (argumentsEquivalent_refl_forSyntaxDiff leftTargetArguments)
        (argumentsEquivalent_refl_forSyntaxDiff rightTargetArguments)
        hrightNotLeft hleftChildResponse
        hrightChildResponse hchildNot
        (by simpa [currentSelectionSet] using hleftFieldOk)
        (by simpa [currentSelectionSet] using hrightFieldOk)
  refine ⟨
    hinclude,
    ProjectionResolverRef FieldPairSelectedPathProbeRef,
    resolvers,
    parentFuel + 1,
    ProjectionResolverRef.root FieldPairSelectedPathProbeRef.root,
    hminFuel,
    ?_,
    ?_
  ⟩
  · intro supportSelectionSet hsupportMember
    rcases hsupportValid supportSelectionSet hsupportMember with
      ⟨_variableDefinitions, _hvalid, hfree, hnormal⟩
    have hmember : supportSelectionSet ∈ members := by
      simp [members, hsupportMember]
    have hfieldOk :=
      selectionSetFieldsExecuteOk_fieldPairOrDeepSuccess_selectedPathProbe_root_of_valid_normal_member
        (schema := schema) (parentType := parentType)
        (leftFieldName := leftFieldName) (rightFieldName := rightFieldName)
        (leftArguments := leftTargetArguments)
        (rightArguments := rightTargetArguments)
        (leftRuntime := leftRuntime) (rightRuntime := rightRuntime)
        (leftFieldDefinition := leftFieldDefinition)
        (rightFieldDefinition := rightFieldDefinition) (members := members)
        (selectionSet := supportSelectionSet) (parentFuel := parentFuel)
        leftSpine rightSpine variableValues hschema hmembers hmember hobject hparentFuel
        hleftLookup hrightLookup hleftComposite hrightComposite hleftInclude
        hrightInclude hleftSpineValid hrightSpineValid hleftLeafFuel
        hrightLeafFuel
    rw [fieldPairPathLocalNextSelectionSet_eq_of_arguments schema parentType
      leftRuntime leftFieldName leftTargetArguments leftArguments
      currentSelectionSet,
      fieldPairPathLocalNextSelectionSet_eq_of_arguments schema parentType
        rightRuntime rightFieldName rightTargetArguments rightArguments
        currentSelectionSet] at hfieldOk
    simpa [resolvers, source, rootSelectionSet, currentSelectionSet,
      projectionRootResolverValue, projectionResolverValue] using
      (ExecutionSuccess.executeSelectionSetAsResponse_object_of_field_ok
        schema resolvers variableValues (parentFuel + 1) parentType source
        supportSelectionSet hfree hnormal hobject
        (by simpa [resolvers, source, rootSelectionSet, currentSelectionSet,
            leftInitialSelectionSet, rightInitialSelectionSet,
            selectionSetFieldsExecuteOk]
          using hfieldOk))
  · simpa [source, projectionRootResolverValue, projectionResolverValue]
      using hdataNot

theorem
    not_selectionSetsDataEquivalent_of_selectedPathProbe_root_arguments_child_data_diff
    {schema : Schema}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    {parentType responseName fieldName leftRuntime rightRuntime : Name}
    {leftArguments rightArguments leftFieldArguments rightFieldArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet left right : List Selection}
    {fieldDefinition : FieldDefinition}
    (leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep)
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions parentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> objectTypeNameBool schema parentType = true
      -> Selection.field responseName fieldName leftFieldArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName fieldName rightFieldArguments rightDirectives
            rightChildSelectionSet
          ∈ right
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType leftRuntime
          = true
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType rightRuntime
          = true
      -> SelectedFieldSpineRuntimeValid schema
          fieldDefinition.outputType.namedType leftRuntime leftInitialSpine
      -> SelectedFieldSpineRuntimeValid schema
          fieldDefinition.outputType.namedType rightRuntime rightInitialSpine
      -> ¬ Argument.argumentsEquivalent leftArguments rightArguments
      -> Argument.argumentsEquivalent
          (Execution.coerceArgumentValues schema [] fieldDefinition.arguments
            leftFieldArguments)
          leftArguments
      -> Argument.argumentsEquivalent
          (Execution.coerceArgumentValues schema [] fieldDefinition.arguments
            rightFieldArguments)
          rightArguments
      -> (let parentFuel := selectionSetDeepProbeFuel schema parentType (left ++ right)
          let rootSelectionSet :=
            [Selection.inlineFragment (some parentType) [] (left ++ right)]
          let leftInitialSelectionSet :=
            fieldPairPathLocalNextSelectionSet schema parentType leftRuntime
              fieldName leftFieldArguments (left ++ right)
          let rightInitialSelectionSet :=
            fieldPairPathLocalNextSelectionSet schema parentType rightRuntime
              fieldName rightFieldArguments (left ++ right)
          let variableValues : Execution.VariableValues := []
          ¬ Execution.ResponseValue.semanticEquivalent
              (Execution.executeSelectionSetAsResponse schema
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
                    (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
                      leftInitialSelectionSet leftInitialSpine)))
                leftChildSelectionSet).data
              (Execution.executeSelectionSetAsResponse schema
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
                    (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                      rightInitialSelectionSet rightInitialSpine)))
                rightChildSelectionSet).data)
      -> ¬ selectionSetsDataEquivalent schema parentType left right := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hobject hleftMem hrightMem hlookup hcomposite
    hleftInclude hrightInclude hleftSpineValid hrightSpineValid
    hargumentsDiff hleftCoerced hrightCoerced hchildDataNot
  let parentFuel := selectionSetDeepProbeFuel schema parentType (left ++ right)
  let rootSelectionSet : List Selection :=
    [Selection.inlineFragment (some parentType) [] (left ++ right)]
  let leftInitialSelectionSet : List Selection :=
    fieldPairPathLocalNextSelectionSet schema parentType leftRuntime
      fieldName leftFieldArguments (left ++ right)
  let rightInitialSelectionSet : List Selection :=
    fieldPairPathLocalNextSelectionSet schema parentType rightRuntime
      fieldName rightFieldArguments (left ++ right)
  let variableValues : Execution.VariableValues := []
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
        parentType (selectionSet := left) (responseName := responseName)
        (fieldName := fieldName) (arguments := leftFieldArguments)
        (directives := leftDirectives)
        (childSelectionSet := leftChildSelectionSet)
        (fieldDefinition := fieldDefinition) hleftMem hlookup
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
  have hleftLeftTarget :
      ∀ currentResponseName arguments directives childSelectionSet,
        Selection.field currentResponseName fieldName arguments directives
            childSelectionSet ∈ left ->
        Argument.argumentsEquivalent
            (Execution.coerceArgumentValues schema variableValues
              fieldDefinition.arguments arguments)
            leftArguments ->
          ∃ childFields childErrors,
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
        executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_target_child_of_valid_normal_support_context_field_mem
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet leftInitialSpine rightInitialSpine
          variableValues hschema (parentType := parentType)
          (variableDefinitions := leftVariableDefinitions)
          (selectionSet := left) (currentSelectionSet := left ++ right)
          (fuel := childFuel) (responseName := currentResponseName)
          (fieldName := fieldName) (runtimeType := leftRuntime)
          (targetParent := parentType) (leftField := fieldName)
          (rightField := fieldName) (targetArguments := leftArguments)
          (leftArguments := leftArguments)
          (rightArguments := rightArguments) (arguments := arguments)
          (directives := directives) (childSelectionSet := childSelectionSet)
          (fieldDefinition := fieldDefinition) (leftRuntime := leftRuntime)
          (rightRuntime := rightRuntime) (spine := leftInitialSpine)
          (tag := FieldPairProbeTag.left) hleftValid hleftFree hleftNormal
          hobject hsupport hleftContext hmem harguments hlookup hcomposite
          hleftInclude hleftSpineValid hchildFuel with
      ⟨childFields, childErrors, hresponse⟩
    refine ⟨childFields, childErrors, ?_⟩
    have hfuelEq :
        childFuel + 1 =
          parentFuel - leafProbeFuel fieldDefinition.outputType := by
      dsimp [childFuel]
      omega
    rw [fieldPairPathLocalNextSelectionSet_eq_of_arguments schema parentType
      leftRuntime fieldName leftArguments leftFieldArguments (left ++ right)]
      at hresponse
    simpa [leftInitialSelectionSet, hfuelEq] using hresponse
  have hleftRightTarget :
      ∀ currentResponseName arguments directives childSelectionSet,
        Selection.field currentResponseName fieldName arguments directives
            childSelectionSet ∈ left ->
        Argument.argumentsEquivalent
            (Execution.coerceArgumentValues schema variableValues
              fieldDefinition.arguments arguments)
            rightArguments ->
          ∃ childFields childErrors,
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
        executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_target_child_of_valid_normal_support_context_field_mem
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet leftInitialSpine rightInitialSpine
          variableValues hschema (parentType := parentType)
          (variableDefinitions := leftVariableDefinitions)
          (selectionSet := left) (currentSelectionSet := left ++ right)
          (fuel := childFuel) (responseName := currentResponseName)
          (fieldName := fieldName) (runtimeType := rightRuntime)
          (targetParent := parentType) (leftField := fieldName)
          (rightField := fieldName) (targetArguments := rightArguments)
          (leftArguments := leftArguments)
          (rightArguments := rightArguments) (arguments := arguments)
          (directives := directives) (childSelectionSet := childSelectionSet)
          (fieldDefinition := fieldDefinition) (leftRuntime := leftRuntime)
          (rightRuntime := rightRuntime) (spine := rightInitialSpine)
          (tag := FieldPairProbeTag.right) hleftValid hleftFree hleftNormal
          hobject hsupport hleftContext hmem harguments hlookup hcomposite
          hrightInclude hrightSpineValid hchildFuel with
      ⟨childFields, childErrors, hresponse⟩
    refine ⟨childFields, childErrors, ?_⟩
    have hfuelEq :
        childFuel + 1 =
          parentFuel - leafProbeFuel fieldDefinition.outputType := by
      dsimp [childFuel]
      omega
    rw [fieldPairPathLocalNextSelectionSet_eq_of_arguments schema parentType
      rightRuntime fieldName rightArguments rightFieldArguments (left ++ right)]
      at hresponse
    simpa [rightInitialSelectionSet, hfuelEq] using hresponse
  have hrightLeftTarget :
      ∀ currentResponseName arguments directives childSelectionSet,
        Selection.field currentResponseName fieldName arguments directives
            childSelectionSet ∈ right ->
        Argument.argumentsEquivalent
            (Execution.coerceArgumentValues schema variableValues
              fieldDefinition.arguments arguments)
            leftArguments ->
          ∃ childFields childErrors,
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
        executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_target_child_of_valid_normal_support_context_field_mem
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet leftInitialSpine rightInitialSpine
          variableValues hschema (parentType := parentType)
          (variableDefinitions := rightVariableDefinitions)
          (selectionSet := right) (currentSelectionSet := left ++ right)
          (fuel := childFuel) (responseName := currentResponseName)
          (fieldName := fieldName) (runtimeType := leftRuntime)
          (targetParent := parentType) (leftField := fieldName)
          (rightField := fieldName) (targetArguments := leftArguments)
          (leftArguments := leftArguments)
          (rightArguments := rightArguments) (arguments := arguments)
          (directives := directives) (childSelectionSet := childSelectionSet)
          (fieldDefinition := fieldDefinition) (leftRuntime := leftRuntime)
          (rightRuntime := rightRuntime) (spine := leftInitialSpine)
          (tag := FieldPairProbeTag.left) hrightValid hrightFree
          hrightNormal hobject hsupport hrightContext hmem harguments hlookup
          hcomposite hleftInclude hleftSpineValid hchildFuel with
      ⟨childFields, childErrors, hresponse⟩
    refine ⟨childFields, childErrors, ?_⟩
    have hfuelEq :
        childFuel + 1 =
          parentFuel - leafProbeFuel fieldDefinition.outputType := by
      dsimp [childFuel]
      omega
    rw [fieldPairPathLocalNextSelectionSet_eq_of_arguments schema parentType
      leftRuntime fieldName leftArguments leftFieldArguments (left ++ right)]
      at hresponse
    simpa [leftInitialSelectionSet, hfuelEq] using hresponse
  have hrightRightTarget :
      ∀ currentResponseName arguments directives childSelectionSet,
        Selection.field currentResponseName fieldName arguments directives
            childSelectionSet ∈ right ->
        Argument.argumentsEquivalent
            (Execution.coerceArgumentValues schema variableValues
              fieldDefinition.arguments arguments)
            rightArguments ->
          ∃ childFields childErrors,
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
        executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_target_child_of_valid_normal_support_context_field_mem
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet leftInitialSpine rightInitialSpine
          variableValues hschema (parentType := parentType)
          (variableDefinitions := rightVariableDefinitions)
          (selectionSet := right) (currentSelectionSet := left ++ right)
          (fuel := childFuel) (responseName := currentResponseName)
          (fieldName := fieldName) (runtimeType := rightRuntime)
          (targetParent := parentType) (leftField := fieldName)
          (rightField := fieldName) (targetArguments := rightArguments)
          (leftArguments := leftArguments)
          (rightArguments := rightArguments) (arguments := arguments)
          (directives := directives) (childSelectionSet := childSelectionSet)
          (fieldDefinition := fieldDefinition) (leftRuntime := leftRuntime)
          (rightRuntime := rightRuntime) (spine := rightInitialSpine)
          (tag := FieldPairProbeTag.right) hrightValid hrightFree
          hrightNormal hobject hsupport hrightContext hmem harguments hlookup
          hcomposite hrightInclude hrightSpineValid hchildFuel with
      ⟨childFields, childErrors, hresponse⟩
    refine ⟨childFields, childErrors, ?_⟩
    have hfuelEq :
        childFuel + 1 =
          parentFuel - leafProbeFuel fieldDefinition.outputType := by
      dsimp [childFuel]
      omega
    rw [fieldPairPathLocalNextSelectionSet_eq_of_arguments schema parentType
      rightRuntime fieldName rightArguments rightFieldArguments (left ++ right)]
      at hresponse
    simpa [rightInitialSelectionSet, hfuelEq] using hresponse
  rcases hleftLeftTarget responseName leftFieldArguments leftDirectives
      leftChildSelectionSet hleftMem
      hleftCoerced with
    ⟨leftChildFields, leftChildErrors, hleftChildResponse⟩
  rcases hrightRightTarget responseName rightFieldArguments rightDirectives
      rightChildSelectionSet hrightMem
      hrightCoerced with
    ⟨rightChildFields, rightChildErrors, hrightChildResponse⟩
  have hchildNot :
      ¬ Execution.ResponseValue.semanticEquivalent
        (Execution.ResponseValue.object leftChildFields)
        (Execution.ResponseValue.object rightChildFields) := by
    intro hsemantic
    apply hchildDataNot
    simpa [parentFuel, rootSelectionSet, leftInitialSelectionSet,
      rightInitialSelectionSet, variableValues, hleftChildResponse,
      hrightChildResponse] using hsemantic
  have hleftDeep :
      ∀ currentResponseName siblingFieldName arguments directives
          childSelectionSet,
        Selection.field currentResponseName siblingFieldName arguments
            directives childSelectionSet ∈ left ->
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
              }] =
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
      ∀ currentResponseName siblingFieldName arguments directives
          childSelectionSet,
        Selection.field currentResponseName siblingFieldName arguments
            directives childSelectionSet ∈ right ->
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
              }] =
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
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet leftInitialSpine rightInitialSpine
      variableValues parentFuel parentType responseName fieldName
      leftArguments rightArguments leftFieldArguments rightFieldArguments
      leftRuntime rightRuntime hobject
      hleftNormal hrightNormal hleftFree hrightFree hleftMem hrightMem
      hlookup hleftInclude hrightInclude hleafFuel hargumentsDiff
      hleftCoerced hrightCoerced
      hleftChildResponse hrightChildResponse hchildNot hleftLeftTarget
      hleftRightTarget hrightLeftTarget hrightRightTarget hleftDeep hrightDeep

theorem
    not_selectionSetsDataEquivalent_of_valid_normal_object_arguments_diff_composite_pairedPath
    {schema : Schema}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    {parentType responseName fieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet left right : List Selection}
    {fieldDefinition : FieldDefinition}
    : Execution.argumentCoercionReflectsSyntaxAtEmpty schema
      -> SchemaWellFormedness.schemaWellFormed schema
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
      -> ¬ Argument.argumentsEquivalent leftArguments rightArguments
      -> ¬ selectionSetsDataEquivalent schema parentType left right := by
  intro hcoercionReflects hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hobject hleftMem hrightMem hlookup hcomposite
    hargumentsDiff
  let parentFuel := selectionSetDeepProbeFuel schema parentType (left ++ right)
  let childFuel := parentFuel - leafProbeFuel fieldDefinition.outputType - 1
  let rootSelectionSet : List Selection :=
    [Selection.inlineFragment (some parentType) [] (left ++ right)]
  let variableValues : Execution.VariableValues := []
  let leftTargetArguments :=
    Execution.coerceArgumentValues schema [] fieldDefinition.arguments
      leftArguments
  let rightTargetArguments :=
    Execution.coerceArgumentValues schema [] fieldDefinition.arguments
      rightArguments
  have htargetArgumentsDiff :
      ¬ Argument.argumentsEquivalent leftTargetArguments
        rightTargetArguments := by
    intro hcoerced
    exact hargumentsDiff
      (hcoercionReflects fieldDefinition.arguments leftArguments
        rightArguments hcoerced)
  have hleftChildNonempty : leftChildSelectionSet ≠ [] :=
    selectionSet_nonempty_of_valid_field_mem_lookup_compositeBool
      hleftValid hleftMem hlookup hcomposite
  have hrightChildNonempty : rightChildSelectionSet ≠ [] :=
    selectionSet_nonempty_of_valid_field_mem_lookup_compositeBool
      hrightValid hrightMem hlookup hcomposite
  have hleftChildValid :
      Validation.selectionSetValid schema leftVariableDefinitions
        fieldDefinition.outputType.namedType leftChildSelectionSet :=
    selectionSetValid_field_child_of_mem_lookup hleftValid hleftMem
      hleftChildNonempty hlookup
  have hrightChildValid :
      Validation.selectionSetValid schema rightVariableDefinitions
        fieldDefinition.outputType.namedType rightChildSelectionSet :=
    selectionSetValid_field_child_of_mem_lookup hrightValid hrightMem
      hrightChildNonempty hlookup
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
  have hpairedPath :
      NormalSelectionSetPairedPath schema
        fieldDefinition.outputType.namedType
        fieldDefinition.outputType.namedType leftChildSelectionSet
        rightChildSelectionSet :=
    normalSelectionSetPairedPath_of_valid_normal_nonempty hleftChildValid
      hrightChildValid hleftChildNormal hrightChildNormal hleftChildNonempty
      hrightChildNonempty
  rcases
      normalSelectionSetPairedPathDataDiff_of_valid_normal schema
        rootSelectionSet variableValues childFuel childFuel parentType
        fieldName fieldName leftTargetArguments rightTargetArguments hschema
        hleftChildValid hrightChildValid hleftChildFree hrightChildFree
        hleftChildNormal hrightChildNormal hleftChildFuel hrightChildFuel
        hleftChildNonempty hrightChildNonempty hpairedPath with
    ⟨leftRuntime, rightRuntime, leftSpine, rightSpine,
      hleftSpineValid, hrightSpineValid, hdataBuilder⟩
  have hleftInclude :
      schema.typeIncludesObjectBool fieldDefinition.outputType.namedType
        leftRuntime = true :=
    selectedFieldSpineRuntimeValid_typeIncludes hleftSpineValid
  have hrightInclude :
      schema.typeIncludesObjectBool fieldDefinition.outputType.namedType
        rightRuntime = true :=
    selectedFieldSpineRuntimeValid_typeIncludes hrightSpineValid
  have hleftRuntimeObject :
      objectTypeNameBool schema leftRuntime = true :=
    objectTypeNameBool_of_typeIncludesObjectBool hschema hleftInclude
  have hrightRuntimeObject :
      objectTypeNameBool schema rightRuntime = true :=
    objectTypeNameBool_of_typeIncludesObjectBool hschema hrightInclude
  let leftInitialSelectionSet : List Selection :=
    fieldPairPathLocalNextSelectionSet schema parentType leftRuntime
      fieldName leftArguments (left ++ right)
  let rightInitialSelectionSet : List Selection :=
    fieldPairPathLocalNextSelectionSet schema parentType rightRuntime
      fieldName rightArguments (left ++ right)
  let leftRootSpine : List NormalSelectionSetObservableFieldStep :=
    ({ responseName := responseName, fieldName := fieldName,
       arguments := leftArguments, childRuntime := some leftRuntime } ::
      leftSpine)
  let rightRootSpine : List NormalSelectionSetObservableFieldStep :=
    ({ responseName := responseName, fieldName := fieldName,
       arguments := rightArguments, childRuntime := some rightRuntime } ::
      rightSpine)
  have hleftSource :
      SelectedPathCompositeFieldChildSource schema parentType fieldName
        leftArguments (left ++ right) leftRootSpine fieldDefinition
        leftRuntime leftSpine := by
    simpa [leftRootSpine] using
      (selectedPathCompositeFieldChildSource_cons
        (schema := schema) (parentType := parentType)
        (responseName := responseName) (fieldName := fieldName)
        (arguments := leftArguments) (currentSelectionSet := left ++ right)
        (fieldDefinition := fieldDefinition) (childRuntime := leftRuntime)
        (childSpine := leftSpine) hcomposite hleftSpineValid)
  have hrightSource :
      SelectedPathCompositeFieldChildSource schema parentType fieldName
        rightArguments (left ++ right) rightRootSpine fieldDefinition
        rightRuntime rightSpine := by
    simpa [rightRootSpine] using
      (selectedPathCompositeFieldChildSource_cons
        (schema := schema) (parentType := parentType)
        (responseName := responseName) (fieldName := fieldName)
        (arguments := rightArguments) (currentSelectionSet := left ++ right)
        (fieldDefinition := fieldDefinition) (childRuntime := rightRuntime)
        (childSpine := rightSpine) hcomposite hrightSpineValid)
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
      PathLocalSupportValidNormal schema leftRuntime
        leftInitialSelectionSet := by
    exact
      pathLocalSupportValidNormal_fieldPairPathLocalNextSelectionSet_of_selectedPathCompositeFieldChildSource
        hsupport hobject hleftRuntimeObject hlookup hleftSource hleftInclude
  have hrightChildSupport :
      PathLocalSupportValidNormal schema rightRuntime
        rightInitialSelectionSet := by
    exact
      pathLocalSupportValidNormal_fieldPairPathLocalNextSelectionSet_of_selectedPathCompositeFieldChildSource
        hsupport hobject hrightRuntimeObject hlookup hrightSource
        hrightInclude
  have hleftChildContext :
      SelectedPathSelectionSetContextReady schema
        fieldDefinition.outputType.namedType leftRuntime
        leftInitialSelectionSet leftChildSelectionSet := by
    exact
      selectedPathSelectionSetContextReady_fieldPairPathLocalNextSelectionSet_of_selectedPathCompositeFieldChildSource
        hleftContext hleftMem hlookup hleftChildNormal hleftSource
        hleftRuntimeObject
  have hrightChildContext :
      SelectedPathSelectionSetContextReady schema
        fieldDefinition.outputType.namedType rightRuntime
        rightInitialSelectionSet rightChildSelectionSet := by
    exact
      selectedPathSelectionSetContextReady_fieldPairPathLocalNextSelectionSet_of_selectedPathCompositeFieldChildSource
        hrightContext hrightMem hlookup hrightChildNormal hrightSource
        hrightRuntimeObject
  have hchildDataDiff :=
    hdataBuilder leftInitialSelectionSet rightInitialSelectionSet leftSpine
      rightSpine leftRuntime rightRuntime leftInitialSelectionSet
      rightInitialSelectionSet hleftChildSupport hrightChildSupport
      hleftChildContext hrightChildContext
  have hchildFuelEq :
      childFuel + 1 =
        parentFuel - leafProbeFuel fieldDefinition.outputType := by
    have hlocal :=
      selectionSetDeepProbeFuel_field_mem schema parentType (left ++ right)
        responseName fieldName leftArguments leftDirectives
        leftChildSelectionSet fieldDefinition
        (List.mem_append_left right hleftMem) hlookup
    dsimp [childFuel, parentFuel]
    omega
  have hchildDataNot :
      ¬ Execution.ResponseValue.semanticEquivalent
        (Execution.executeSelectionSetAsResponse schema
          (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
            (fieldPairSelectedPathProbeResolvers schema
              leftInitialSelectionSet rightInitialSelectionSet leftSpine
              rightSpine parentType fieldName fieldName leftTargetArguments
              rightTargetArguments leftRuntime rightRuntime)
            parentType fieldName fieldName leftTargetArguments
              rightTargetArguments)
          variableValues
          (parentFuel - leafProbeFuel fieldDefinition.outputType)
          leftRuntime
          (projectionTargetResolverValue
            (.object leftRuntime
              (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
                leftInitialSelectionSet leftSpine)))
          leftChildSelectionSet).data
        (Execution.executeSelectionSetAsResponse schema
          (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
            (fieldPairSelectedPathProbeResolvers schema
              leftInitialSelectionSet rightInitialSelectionSet leftSpine
              rightSpine parentType fieldName fieldName leftTargetArguments
              rightTargetArguments leftRuntime rightRuntime)
            parentType fieldName fieldName leftTargetArguments
              rightTargetArguments)
          variableValues
          (parentFuel - leafProbeFuel fieldDefinition.outputType)
          rightRuntime
          (projectionTargetResolverValue
            (.object rightRuntime
              (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                rightInitialSelectionSet rightSpine)))
          rightChildSelectionSet).data := by
    simpa [NormalSelectionSetPairedPathDataDiffAt,
      SelectedPathSelectionSetsResponseDataDiff, hchildFuelEq] using
      hchildDataDiff.2.2.2.2
  exact
    not_selectionSetsDataEquivalent_of_selectedPathProbe_root_arguments_child_data_diff
      (schema := schema)
      (leftVariableDefinitions := leftVariableDefinitions)
      (rightVariableDefinitions := rightVariableDefinitions)
      (parentType := parentType) (responseName := responseName)
      (fieldName := fieldName) (leftRuntime := leftRuntime)
      (rightRuntime := rightRuntime) (leftArguments := leftTargetArguments)
      (rightArguments := rightTargetArguments)
      (leftFieldArguments := leftArguments)
      (rightFieldArguments := rightArguments)
      (leftDirectives := leftDirectives)
      (rightDirectives := rightDirectives)
      (leftChildSelectionSet := leftChildSelectionSet)
      (rightChildSelectionSet := rightChildSelectionSet)
      (left := left) (right := right) (fieldDefinition := fieldDefinition)
      leftSpine rightSpine hschema hleftValid hrightValid hleftFree
      hrightFree hleftNormal hrightNormal hobject hleftMem hrightMem hlookup
      hcomposite hleftInclude hrightInclude hleftSpineValid
      hrightSpineValid htargetArgumentsDiff
      (argumentsEquivalent_refl_forSyntaxDiff leftTargetArguments)
      (argumentsEquivalent_refl_forSyntaxDiff rightTargetArguments) (by
        simpa [parentFuel, rootSelectionSet, leftInitialSelectionSet,
          rightInitialSelectionSet, variableValues, leftTargetArguments,
          rightTargetArguments] using hchildDataNot)

theorem
    not_selectionSetsDataEquivalent_of_valid_normal_object_fieldName_diff_composite_pairedPath
    {schema : Schema}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    {parentType responseName leftFieldName rightFieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet left right : List Selection}
    {leftFieldDefinition rightFieldDefinition : FieldDefinition}
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
      -> Selection.field responseName rightFieldName rightArguments
            rightDirectives rightChildSelectionSet
          ∈ right
      -> schema.lookupField parentType leftFieldName = some leftFieldDefinition
      -> schema.lookupField parentType rightFieldName = some rightFieldDefinition
      -> (TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> leftFieldName ≠ rightFieldName
      -> ¬ selectionSetsDataEquivalent schema parentType left right := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hobject hleftMem hrightMem hleftLookup hrightLookup
    hleftComposite hrightComposite hfieldDiff
  let parentFuel := selectionSetDeepProbeFuel schema parentType (left ++ right)
  let leftChildFuel :=
    parentFuel - leafProbeFuel leftFieldDefinition.outputType - 1
  let rightChildFuel :=
    parentFuel - leafProbeFuel rightFieldDefinition.outputType - 1
  let rootSelectionSet : List Selection :=
    [Selection.inlineFragment (some parentType) [] (left ++ right)]
  let variableValues : Execution.VariableValues := []
  let leftTargetArguments :=
    Execution.coerceArgumentValues schema variableValues
      leftFieldDefinition.arguments leftArguments
  let rightTargetArguments :=
    Execution.coerceArgumentValues schema variableValues
      rightFieldDefinition.arguments rightArguments
  have hleftChildNonempty : leftChildSelectionSet ≠ [] :=
    selectionSet_nonempty_of_valid_field_mem_lookup_compositeBool
      hleftValid hleftMem hleftLookup hleftComposite
  have hrightChildNonempty : rightChildSelectionSet ≠ [] :=
    selectionSet_nonempty_of_valid_field_mem_lookup_compositeBool
      hrightValid hrightMem hrightLookup hrightComposite
  have hleftChildValid :
      Validation.selectionSetValid schema leftVariableDefinitions
        leftFieldDefinition.outputType.namedType leftChildSelectionSet :=
    selectionSetValid_field_child_of_mem_lookup hleftValid hleftMem
      hleftChildNonempty hleftLookup
  have hrightChildValid :
      Validation.selectionSetValid schema rightVariableDefinitions
        rightFieldDefinition.outputType.namedType rightChildSelectionSet :=
    selectionSetValid_field_child_of_mem_lookup hrightValid hrightMem
      hrightChildNonempty hrightLookup
  have hleftChildFree : selectionSetDirectiveFree leftChildSelectionSet :=
    selectionSetDirectiveFree_field_child_of_mem hleftFree hleftMem
  have hrightChildFree : selectionSetDirectiveFree rightChildSelectionSet :=
    selectionSetDirectiveFree_field_child_of_mem hrightFree hrightMem
  have hleftChildNormal :
      selectionSetNormal schema leftFieldDefinition.outputType.namedType
        leftChildSelectionSet :=
    selectionSetNormal_field_child_of_mem_lookup hleftNormal hleftMem
      hleftLookup
  have hrightChildNormal :
      selectionSetNormal schema rightFieldDefinition.outputType.namedType
        rightChildSelectionSet :=
    selectionSetNormal_field_child_of_mem_lookup hrightNormal hrightMem
      hrightLookup
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
  have hpairedPath :
      NormalSelectionSetPairedPath schema
        leftFieldDefinition.outputType.namedType
        rightFieldDefinition.outputType.namedType leftChildSelectionSet
        rightChildSelectionSet :=
    normalSelectionSetPairedPath_of_valid_normal_nonempty hleftChildValid
      hrightChildValid hleftChildNormal hrightChildNormal hleftChildNonempty
      hrightChildNonempty
  rcases
      normalSelectionSetPairedPathDataDiff_of_valid_normal schema
        rootSelectionSet variableValues leftChildFuel rightChildFuel
        parentType leftFieldName rightFieldName leftTargetArguments
        rightTargetArguments hschema hleftChildValid hrightChildValid hleftChildFree
        hrightChildFree hleftChildNormal hrightChildNormal hleftChildFuel
        hrightChildFuel hleftChildNonempty hrightChildNonempty hpairedPath with
    ⟨leftRuntime, rightRuntime, leftSpine, rightSpine,
      hleftSpineValid, hrightSpineValid, hdataBuilder⟩
  have hleftInclude :
      schema.typeIncludesObjectBool
        leftFieldDefinition.outputType.namedType leftRuntime = true :=
    selectedFieldSpineRuntimeValid_typeIncludes hleftSpineValid
  have hrightInclude :
      schema.typeIncludesObjectBool
        rightFieldDefinition.outputType.namedType rightRuntime = true :=
    selectedFieldSpineRuntimeValid_typeIncludes hrightSpineValid
  have hleftRuntimeObject :
      objectTypeNameBool schema leftRuntime = true :=
    objectTypeNameBool_of_typeIncludesObjectBool hschema hleftInclude
  have hrightRuntimeObject :
      objectTypeNameBool schema rightRuntime = true :=
    objectTypeNameBool_of_typeIncludesObjectBool hschema hrightInclude
  let leftInitialSelectionSet : List Selection :=
    fieldPairPathLocalNextSelectionSet schema parentType leftRuntime
      leftFieldName leftArguments (left ++ right)
  let rightInitialSelectionSet : List Selection :=
    fieldPairPathLocalNextSelectionSet schema parentType rightRuntime
      rightFieldName rightArguments (left ++ right)
  let leftRootSpine : List NormalSelectionSetObservableFieldStep :=
    ({ responseName := responseName, fieldName := leftFieldName,
       arguments := leftArguments, childRuntime := some leftRuntime } ::
      leftSpine)
  let rightRootSpine : List NormalSelectionSetObservableFieldStep :=
    ({ responseName := responseName, fieldName := rightFieldName,
       arguments := rightArguments, childRuntime := some rightRuntime } ::
      rightSpine)
  have hleftSource :
      SelectedPathCompositeFieldChildSource schema parentType leftFieldName
        leftArguments (left ++ right) leftRootSpine leftFieldDefinition
        leftRuntime leftSpine := by
    simpa [leftRootSpine] using
      (selectedPathCompositeFieldChildSource_cons
        (schema := schema) (parentType := parentType)
        (responseName := responseName) (fieldName := leftFieldName)
        (arguments := leftArguments) (currentSelectionSet := left ++ right)
        (fieldDefinition := leftFieldDefinition) (childRuntime := leftRuntime)
        (childSpine := leftSpine) hleftComposite hleftSpineValid)
  have hrightSource :
      SelectedPathCompositeFieldChildSource schema parentType rightFieldName
        rightArguments (left ++ right) rightRootSpine rightFieldDefinition
        rightRuntime rightSpine := by
    simpa [rightRootSpine] using
      (selectedPathCompositeFieldChildSource_cons
        (schema := schema) (parentType := parentType)
        (responseName := responseName) (fieldName := rightFieldName)
        (arguments := rightArguments) (currentSelectionSet := left ++ right)
        (fieldDefinition := rightFieldDefinition)
        (childRuntime := rightRuntime) (childSpine := rightSpine)
        hrightComposite hrightSpineValid)
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
      PathLocalSupportValidNormal schema leftRuntime
        leftInitialSelectionSet :=
    pathLocalSupportValidNormal_fieldPairPathLocalNextSelectionSet_of_selectedPathCompositeFieldChildSource
      hsupport hobject hleftRuntimeObject hleftLookup hleftSource
      hleftInclude
  have hrightChildSupport :
      PathLocalSupportValidNormal schema rightRuntime
        rightInitialSelectionSet :=
    pathLocalSupportValidNormal_fieldPairPathLocalNextSelectionSet_of_selectedPathCompositeFieldChildSource
      hsupport hobject hrightRuntimeObject hrightLookup hrightSource
      hrightInclude
  have hleftChildContext :
      SelectedPathSelectionSetContextReady schema
        leftFieldDefinition.outputType.namedType leftRuntime
        leftInitialSelectionSet leftChildSelectionSet :=
    selectedPathSelectionSetContextReady_fieldPairPathLocalNextSelectionSet_of_selectedPathCompositeFieldChildSource
      hleftContext hleftMem hleftLookup hleftChildNormal hleftSource
      hleftRuntimeObject
  have hrightChildContext :
      SelectedPathSelectionSetContextReady schema
        rightFieldDefinition.outputType.namedType rightRuntime
        rightInitialSelectionSet rightChildSelectionSet :=
    selectedPathSelectionSetContextReady_fieldPairPathLocalNextSelectionSet_of_selectedPathCompositeFieldChildSource
      hrightContext hrightMem hrightLookup hrightChildNormal hrightSource
      hrightRuntimeObject
  have hchildDataDiff :=
    hdataBuilder leftInitialSelectionSet rightInitialSelectionSet leftSpine
      rightSpine leftRuntime rightRuntime leftInitialSelectionSet
      rightInitialSelectionSet hleftChildSupport hrightChildSupport
      hleftChildContext hrightChildContext
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
  have hchildDataNot :
      ¬ Execution.ResponseValue.semanticEquivalent
        (Execution.executeSelectionSetAsResponse schema
          (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
            (fieldPairSelectedPathProbeResolvers schema
              leftInitialSelectionSet rightInitialSelectionSet leftSpine
              rightSpine parentType leftFieldName rightFieldName
              leftTargetArguments rightTargetArguments leftRuntime rightRuntime)
            parentType leftFieldName rightFieldName leftTargetArguments
            rightTargetArguments)
          variableValues
          (parentFuel - leafProbeFuel leftFieldDefinition.outputType)
          leftRuntime
          (projectionTargetResolverValue
            (.object leftRuntime
              (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
                leftInitialSelectionSet leftSpine)))
          leftChildSelectionSet).data
        (Execution.executeSelectionSetAsResponse schema
          (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
            (fieldPairSelectedPathProbeResolvers schema
              leftInitialSelectionSet rightInitialSelectionSet leftSpine
              rightSpine parentType leftFieldName rightFieldName
              leftTargetArguments rightTargetArguments leftRuntime rightRuntime)
            parentType leftFieldName rightFieldName leftTargetArguments
            rightTargetArguments)
          variableValues
          (parentFuel - leafProbeFuel rightFieldDefinition.outputType)
          rightRuntime
          (projectionTargetResolverValue
            (.object rightRuntime
              (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                rightInitialSelectionSet rightSpine)))
          rightChildSelectionSet).data := by
    simpa [NormalSelectionSetPairedPathDataDiffAt,
      SelectedPathSelectionSetsResponseDataDiff, hleftChildFuelEq,
      hrightChildFuelEq] using hchildDataDiff.2.2.2.2
  exact
    not_selectionSetsDataEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_root_fieldName_object_output_childDataNot_of_valid_normal_append_context
      (schema := schema)
      (leftVariableDefinitions := leftVariableDefinitions)
      (rightVariableDefinitions := rightVariableDefinitions)
      (parentType := parentType) (responseName := responseName)
      (leftFieldName := leftFieldName) (rightFieldName := rightFieldName)
      (leftArguments := leftTargetArguments)
      (rightArguments := rightTargetArguments)
      (leftFieldArguments := leftArguments)
      (rightFieldArguments := rightArguments)
      (leftDirectives := leftDirectives)
      (rightDirectives := rightDirectives)
      (leftChildSelectionSet := leftChildSelectionSet)
      (rightChildSelectionSet := rightChildSelectionSet)
      (left := left) (right := right)
      (leftFieldDefinition := leftFieldDefinition)
      (rightFieldDefinition := rightFieldDefinition)
      (leftRuntimeType := leftRuntime) (rightRuntimeType := rightRuntime)
      leftSpine rightSpine variableValues hschema hleftValid hrightValid
      hleftFree hrightFree hleftNormal hrightNormal hobject hleftMem
      hrightMem hleftLookup hrightLookup hleftComposite hrightComposite
      hleftInclude hrightInclude hleftSpineValid hrightSpineValid hfieldDiff
      (argumentsEquivalent_refl_forSyntaxDiff leftTargetArguments)
      (argumentsEquivalent_refl_forSyntaxDiff rightTargetArguments)
      (by
        simpa [parentFuel, rootSelectionSet, leftInitialSelectionSet,
          rightInitialSelectionSet, leftTargetArguments,
          rightTargetArguments] using hchildDataNot)

end GroundTypeNormalization

end NormalForm

end GraphQL
