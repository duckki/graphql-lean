import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.CompositeRuntime
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.DataSeparation
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.DeepSuccess
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.DiffObservable
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.RuntimeCoherence
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.RuntimeDataDiffWitness

/-!
Finite-support contextual runtime witnesses used by observable-trace separation.

This module contains the leaf field-head, response-name, type-condition, and
abstract-child witness constructors needed by the final focused proof.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

theorem
    selectionSet_fieldPairProjectionFieldOk_framed_leaf_targets_of_valid_normal_members
    {schema : Schema} {parentType : Name} {members : List (List Selection)}
    {selectionSet : List Selection} (variableValues : Execution.VariableValues)
    (fuel : Nat) (leftField rightField : Name)
    (leftArguments rightArguments : List Argument)
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
      -> selectionSetDeepProbeFuel schema parentType (List.flatten members) ≤ fuel
      -> (∀ fieldDefinition,
            schema.lookupField parentType leftField = some fieldDefinition
            -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
                = false)
      -> (∀ fieldDefinition,
            schema.lookupField parentType rightField = some fieldDefinition
            -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
                = false)
      -> (∀ arguments,
            Argument.argumentsEquivalent arguments rightArguments
            -> ¬ fieldProbeTarget parentType leftField leftArguments parentType
                  rightField arguments)
      -> ∀ responseName fieldName arguments directives childSelectionSet,
          Selection.field responseName fieldName arguments directives childSelectionSet
            ∈ selectionSet
          -> ∃ responseValue fieldErrors,
              Execution.executeField schema
                (fieldPairOrDeepSuccessResolvers schema
                  [Selection.inlineFragment (some parentType) [] (List.flatten members)]
                  (fieldPairProbeResolvers schema
                    [Selection.inlineFragment (some parentType) [] (List.flatten members)]
                    parentType leftField rightField leftArguments rightArguments)
                  parentType leftField rightField leftArguments rightArguments)
                variableValues
                (fuel + 1)
                (projectionRootResolverValue
                  (.object parentType (none : Option FieldPairProbeTag)))
                responseName
                [{
                  parentType := parentType,
                  responseName := responseName,
                  fieldName := fieldName,
                  arguments := arguments,
                  selectionSet := childSelectionSet
                }]
              = .ok ([(responseName, responseValue)], fieldErrors) := by
  intro hschema hmembers hmember hobject hfuel hleftLeaf hrightLeaf
    hrightNotLeft responseName fieldName arguments directives
    childSelectionSet hmem
  let rootSelectionSet :=
    [Selection.inlineFragment (some parentType) [] (List.flatten members)]
  let base :=
    fieldPairProbeResolvers schema rootSelectionSet parentType leftField
      rightField leftArguments rightArguments
  rcases hmembers selectionSet hmember with
    ⟨variableDefinitions, hvalid, hfree, hnormal⟩
  rcases selectionSetValid_field_lookup_of_mem hvalid hmem with
    ⟨fieldDefinition, hlookup, _hargsValid, _hfieldSelectionValid⟩
  have hmemFlatten :
      Selection.field responseName fieldName arguments directives
        childSelectionSet ∈ List.flatten members := by
    rw [List.mem_flatten]
    exact ⟨selectionSet, hmember, hmem⟩
  by_cases htargetLeft :
      fieldProbeTarget parentType leftField leftArguments parentType fieldName
        arguments
  · rcases htargetLeft with ⟨_hparent, hfield, harguments⟩
    subst fieldName
    have hleaf := hleftLeaf fieldDefinition hlookup
    have hfuel :
        leafProbeFuel fieldDefinition.outputType ≤ fuel := by
      have hlocal :=
        leafProbeFuel_le_selectionSetDeepProbeFuel_of_field_mem schema
          parentType hmemFlatten hlookup
      omega
    refine ⟨
      leafProbeResponseValue fieldDefinition.outputType FieldPairProbeTag.left.scalar,
      0,
      ?_
    ⟩
    rw [executeField_fieldPairOrDeepSuccessResolvers_left_root
      schema rootSelectionSet base variableValues parentType leftField
      rightField responseName leftArguments rightArguments arguments
      (.object parentType (none : Option FieldPairProbeTag))
      childSelectionSet harguments (fuel + 1)]
    exact
      executeField_fieldPairProbe_left_root_leaf schema rootSelectionSet
        variableValues fuel parentType leftField rightField responseName
        leftArguments rightArguments arguments childSelectionSet fieldDefinition
        harguments hlookup hfuel hleaf
  · by_cases htargetRight :
        fieldProbeTarget parentType rightField rightArguments parentType
          fieldName arguments
    · rcases htargetRight with ⟨_hparent, hfield, harguments⟩
      subst fieldName
      have hnotLeft :
          ¬ fieldProbeTarget parentType leftField leftArguments parentType
            rightField arguments :=
        hrightNotLeft arguments harguments
      have hleaf := hrightLeaf fieldDefinition hlookup
      have hfuel :
          leafProbeFuel fieldDefinition.outputType ≤ fuel := by
        have hlocal :=
          leafProbeFuel_le_selectionSetDeepProbeFuel_of_field_mem schema
            parentType hmemFlatten hlookup
        omega
      refine ⟨
        leafProbeResponseValue fieldDefinition.outputType FieldPairProbeTag.right.scalar,
        0,
        ?_
      ⟩
      rw [executeField_fieldPairOrDeepSuccessResolvers_right_root
        schema rootSelectionSet base variableValues parentType leftField
        rightField responseName leftArguments rightArguments arguments
        (.object parentType (none : Option FieldPairProbeTag))
        childSelectionSet harguments (fuel + 1)]
      exact
        executeField_fieldPairProbe_right_root_leaf_of_not_left schema
          rootSelectionSet variableValues fuel parentType leftField
          rightField responseName leftArguments rightArguments arguments
          childSelectionSet fieldDefinition hnotLeft harguments hlookup
          hfuel hleaf
    · have hnotProjection :
          ¬ fieldPairProjectionTarget parentType leftField rightField
            leftArguments rightArguments parentType fieldName arguments := by
        intro hprojection
        rcases hprojection with ⟨_hparent, htarget⟩
        rcases htarget with hleft | hright
        · exact htargetLeft ⟨rfl, hleft.1, hleft.2⟩
        · exact htargetRight ⟨rfl, hright.1, hright.2⟩
      have hselectionFuel :
          selectionSetDeepProbeFuel schema parentType selectionSet
            ≤ fuel := by
        have hlocal :=
          selectionSetDeepProbeFuel_le_flatten_member schema parentType
            hmember
        omega
      have hpromote :
          ∀ targetParent targetField targetRuntimeType
              targetFieldDefinition,
            schema.lookupField targetParent targetField =
              some targetFieldDefinition ->
            (TypeRef.named
                targetFieldDefinition.outputType.namedType).isCompositeBool
              schema = true ->
            objectTypeNameBool schema
                targetFieldDefinition.outputType.namedType = false ->
            abstractRuntimeForFieldDeep? schema targetParent targetField
              parentType selectionSet = some targetRuntimeType ->
              ∃ runtimeType,
                abstractRuntimeForFieldDeep? schema targetParent targetField
                    targetParent rootSelectionSet =
                  some runtimeType
                  ∧ schema.typeIncludesObjectBool
                    targetFieldDefinition.outputType.namedType runtimeType =
                    true := by
        intro targetParent targetField targetRuntimeType
          targetFieldDefinition htargetLookup htargetComposite
          htargetNonObject hlocalRuntime
        exact
          abstractRuntimeForFieldDeep?_member_framed_promote_some_of_valid_normal_members
            (schema := schema) (currentParent := parentType)
            (targetParent := targetParent) (targetField := targetField)
            (targetRuntimeType := targetRuntimeType)
            (selectionSet := selectionSet) (members := members)
            (targetFieldDefinition := targetFieldDefinition)
            hmembers hmember htargetLookup htargetComposite
            htargetNonObject hlocalRuntime
      rcases
          deepFieldSelectionSetReadyWithRef_of_valid_normal_object_promoted_fuel_ge_size
            schema rootSelectionSet
            (ProjectionResolverRef.filler :
              ProjectionResolverRef (Option FieldPairProbeTag))
            variableValues hschema (SelectionSet.size selectionSet + 1)
            parentType variableDefinitions selectionSet fuel
            (by omega) hselectionFuel hvalid hfree hnormal hobject
            hpromote responseName fieldName arguments directives
            childSelectionSet hmem with
        ⟨fieldDefinition, hlookup, hleafFuel, hready⟩
      rcases
          executeField_deepSelectionSetSuccessWithRef_fieldDefinition_ok_of_ready_fuel_ge
            schema rootSelectionSet
            (ProjectionResolverRef.filler :
              ProjectionResolverRef (Option FieldPairProbeTag))
            variableValues fuel
            (.object parentType
              (ProjectionResolverRef.root
                (none : Option FieldPairProbeTag)))
            responseName parentType fieldName arguments childSelectionSet
            fieldDefinition hlookup hleafFuel hready with
        ⟨responseValue, fieldErrors, hdeep, _hnonNull⟩
      refine ⟨responseValue, fieldErrors, ?_⟩
      simp only [projectionRootResolverValue, projectionResolverValue]
      rw [executeField_fieldPairOrDeepSuccessResolvers_other_root_eq_deepSuccessWithRef
        schema rootSelectionSet base variableValues parentType leftField
        rightField parentType fieldName parentType responseName
        leftArguments rightArguments arguments
        (none : Option FieldPairProbeTag) childSelectionSet hnotProjection
        (fuel + 1)]
      exact hdeep

theorem
    selectionSet_fieldPairProjectionFieldOk_framed_left_leaf_right_composite_targets_of_valid_normal_members
    {schema : Schema} {parentType : Name} {members : List (List Selection)}
    {selectionSet : List Selection} (variableValues : Execution.VariableValues)
    (fuel : Nat) (leftField rightField : Name)
    (leftArguments rightArguments : List Argument)
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
      -> selectionSetDeepProbeFuel schema parentType (List.flatten members) ≤ fuel
      -> (∀ fieldDefinition,
            schema.lookupField parentType leftField = some fieldDefinition
            -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
                = false)
      -> (∀ fieldDefinition,
            schema.lookupField parentType rightField = some fieldDefinition
            -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
                = true)
      -> (∀ arguments,
            Argument.argumentsEquivalent arguments rightArguments
            -> ¬ fieldProbeTarget parentType leftField leftArguments parentType
                  rightField arguments)
      -> ∀ responseName fieldName arguments directives childSelectionSet,
          Selection.field responseName fieldName arguments directives childSelectionSet
            ∈ selectionSet
          -> ∃ responseValue fieldErrors,
              Execution.executeField schema
                (fieldPairOrDeepSuccessResolvers schema
                  [Selection.inlineFragment (some parentType) [] (List.flatten members)]
                  (fieldPairProbeResolvers schema
                    [Selection.inlineFragment (some parentType) [] (List.flatten members)]
                    parentType leftField rightField leftArguments rightArguments)
                  parentType leftField rightField leftArguments rightArguments)
                variableValues
                (fuel + 1)
                (projectionRootResolverValue
                  (.object parentType (none : Option FieldPairProbeTag)))
                responseName
                [{
                  parentType := parentType,
                  responseName := responseName,
                  fieldName := fieldName,
                  arguments := arguments,
                  selectionSet := childSelectionSet
                }]
              = .ok ([(responseName, responseValue)], fieldErrors) := by
  intro hschema hmembers hmember hobject hfuel hleftLeaf hrightComposite
    hrightNotLeft responseName fieldName arguments directives
    childSelectionSet hmem
  let rootSelectionSet :=
    [Selection.inlineFragment (some parentType) [] (List.flatten members)]
  let base :=
    fieldPairProbeResolvers schema rootSelectionSet parentType leftField
      rightField leftArguments rightArguments
  rcases hmembers selectionSet hmember with
    ⟨variableDefinitions, hvalid, hfree, hnormal⟩
  rcases selectionSetValid_field_lookup_of_mem hvalid hmem with
    ⟨fieldDefinition, hlookup, _hargsValid, _hfieldSelectionValid⟩
  have hmemFlatten :
      Selection.field responseName fieldName arguments directives
        childSelectionSet ∈ List.flatten members := by
    rw [List.mem_flatten]
    exact ⟨selectionSet, hmember, hmem⟩
  have hpromoteMember :
      selectionSetDeepPromotionAvailable schema rootSelectionSet parentType
        selectionSet := by
    intro targetParent targetField targetRuntimeType targetFieldDefinition
      htargetLookup htargetComposite htargetNonObject hlocalRuntime
    exact
      abstractRuntimeForFieldDeep?_member_framed_promote_some_of_valid_normal_members
        (schema := schema) (currentParent := parentType)
        (targetParent := targetParent) (targetField := targetField)
        (targetRuntimeType := targetRuntimeType)
        (selectionSet := selectionSet) (members := members)
        (targetFieldDefinition := targetFieldDefinition)
        hmembers hmember htargetLookup htargetComposite htargetNonObject
        hlocalRuntime
  have hheadPromoteMember :
      selectionSetDeepHeadPromotionAvailable schema rootSelectionSet
        parentType selectionSet := by
    intro targetParent targetField targetArguments targetRuntimeType
      targetFieldDefinition htargetLookup htargetComposite htargetNonObject
      hlocalRuntime
    exact
      abstractRuntimeForFieldHeadDeep?_member_framed_promote_some_of_valid_normal_members
        (schema := schema) (currentParent := parentType)
        (targetParent := targetParent) (targetField := targetField)
        (targetArguments := targetArguments)
        (targetRuntimeType := targetRuntimeType)
        (selectionSet := selectionSet) (members := members)
        (targetFieldDefinition := targetFieldDefinition)
        hmembers hmember htargetLookup htargetComposite htargetNonObject
        hlocalRuntime
  by_cases htargetLeft :
      fieldProbeTarget parentType leftField leftArguments parentType fieldName
        arguments
  · rcases htargetLeft with ⟨_hparent, hfield, harguments⟩
    subst fieldName
    have hleaf := hleftLeaf fieldDefinition hlookup
    have hfuel :
        leafProbeFuel fieldDefinition.outputType ≤ fuel := by
      have hlocal :=
        leafProbeFuel_le_selectionSetDeepProbeFuel_of_field_mem schema
          parentType hmemFlatten hlookup
      omega
    refine ⟨
      leafProbeResponseValue fieldDefinition.outputType FieldPairProbeTag.left.scalar,
      0,
      ?_
    ⟩
    rw [executeField_fieldPairOrDeepSuccessResolvers_left_root
      schema rootSelectionSet base variableValues parentType leftField
      rightField responseName leftArguments rightArguments arguments
      (.object parentType (none : Option FieldPairProbeTag))
      childSelectionSet harguments (fuel + 1)]
    exact
      executeField_fieldPairProbe_left_root_leaf schema rootSelectionSet
        variableValues fuel parentType leftField rightField responseName
        leftArguments rightArguments arguments childSelectionSet fieldDefinition
        harguments hlookup hfuel hleaf
  · by_cases htargetRight :
        fieldProbeTarget parentType rightField rightArguments parentType
          fieldName arguments
    · rcases htargetRight with ⟨_hparent, hfield, harguments⟩
      subst fieldName
      have hnotLeft :
          ¬ fieldProbeTarget parentType leftField leftArguments parentType
            rightField arguments :=
        hrightNotLeft arguments harguments
      have hcomposite := hrightComposite fieldDefinition hlookup
      have hleafFuel :
          leafProbeFuel fieldDefinition.outputType ≤ fuel := by
        have hlocal :=
          leafProbeFuel_le_selectionSetDeepProbeFuel_of_field_mem schema
            parentType hmemFlatten hlookup
        omega
      rcases
          fieldHeadCompositeRuntime_framed_members_of_valid_normal_mem
            hvalid hnormal hmembers hmember hmem hlookup hcomposite with
        ⟨runtimeType, hruntime, hinclude⟩
      have hchildValid :
          Validation.selectionSetValid schema variableDefinitions
            fieldDefinition.outputType.namedType childSelectionSet := by
        rcases selectionSetValid_field_lookup_leaf_or_composite_child
            hvalid hmem with
          ⟨candidateDefinition, hcandidateLookup, hkind⟩
        have hcandidateEq : candidateDefinition = fieldDefinition := by
          rw [hlookup] at hcandidateLookup
          exact Option.some.inj hcandidateLookup.symm
        subst candidateDefinition
        rcases hkind with hleaf | hcompositeKind
        · rw [hcomposite] at hleaf
          simp at hleaf
        · exact hcompositeKind.2.2
      have hchildFree : selectionSetDirectiveFree childSelectionSet :=
        selectionSetDirectiveFree_field_child_of_mem hfree hmem
      have hchildNormal :
          selectionSetNormal schema fieldDefinition.outputType.namedType
            childSelectionSet :=
        selectionSetNormal_field_child_of_mem_lookup hnormal hmem hlookup
      have hchildPromote :
          selectionSetDeepPromotionAvailable schema rootSelectionSet
            fieldDefinition.outputType.namedType childSelectionSet :=
        selectionSetDeepPromotionAvailable_field_child_of_mem hvalid hfree
          hnormal hmem hlookup hpromoteMember
      have hchildHeadPromote :
          selectionSetDeepHeadPromotionAvailable schema rootSelectionSet
            fieldDefinition.outputType.namedType childSelectionSet :=
        selectionSetDeepHeadPromotionAvailable_field_child_of_mem hvalid hfree
          hnormal hmem hlookup hheadPromoteMember
      have hchildFuel :
          selectionSetDeepProbeFuel schema
              fieldDefinition.outputType.namedType childSelectionSet
            ≤ fuel - leafProbeFuel fieldDefinition.outputType - 1 := by
        have hlocal :=
          selectionSetDeepProbeFuel_field_mem schema parentType
            (List.flatten members) responseName rightField arguments
            directives childSelectionSet fieldDefinition hmemFlatten hlookup
        omega
      have hchildSize :
          SelectionSet.size childSelectionSet <
            SelectionSet.size selectionSet + 1 := by
        have hlt :=
          selectionSet_size_field_child_lt_of_mem
            (responseName := responseName) (fieldName := rightField)
            (arguments := arguments) (directives := directives)
            (childSelectionSet := childSelectionSet)
            (selectionSet := selectionSet) hmem
        omega
      rcases
          executeSelectionSetAsResponse_fieldPairProbe_tagged_of_valid_normal_promoted_fuel_ge_size
            schema rootSelectionSet variableValues hschema
            (SelectionSet.size selectionSet + 1)
            fieldDefinition.outputType.namedType variableDefinitions
            childSelectionSet
            (fuel - leafProbeFuel fieldDefinition.outputType - 1)
            runtimeType parentType leftField rightField leftArguments
            rightArguments FieldPairProbeTag.right hchildSize hchildFuel
            hchildValid hchildFree hchildNormal hinclude hchildPromote
            hchildHeadPromote with
        ⟨childFields, childErrors, hchildResponseRaw⟩
      have hchildFuelEq :
          fuel - leafProbeFuel fieldDefinition.outputType - 1 + 1 =
            fuel - leafProbeFuel fieldDefinition.outputType := by
        have hlocal :=
          selectionSetDeepProbeFuel_field_mem schema parentType
            (List.flatten members) responseName rightField arguments
            directives childSelectionSet fieldDefinition hmemFlatten hlookup
        omega
      have hchildResponse :
          Execution.executeSelectionSetAsResponse schema
              (fieldPairProbeResolvers schema rootSelectionSet parentType
                leftField rightField leftArguments rightArguments)
              variableValues
              (fuel - leafProbeFuel fieldDefinition.outputType)
              runtimeType (.object runtimeType (some FieldPairProbeTag.right))
              childSelectionSet =
            ({ data := Execution.ResponseValue.object childFields,
               errors := childErrors } :
              Execution.Response) := by
        simpa [hchildFuelEq] using hchildResponseRaw
      rcases
          executeField_fieldPairProbe_right_root_objectProbe_ok_of_child_response
            schema rootSelectionSet variableValues fuel parentType leftField
            rightField responseName leftArguments rightArguments arguments
            childSelectionSet fieldDefinition runtimeType childFields
            childErrors hnotLeft harguments hlookup hruntime hinclude
            hleafFuel hchildResponse with
        ⟨responseValue, fieldErrors, hprobe, _hnonNull⟩
      refine ⟨responseValue, fieldErrors, ?_⟩
      rw [executeField_fieldPairOrDeepSuccessResolvers_right_root
        schema rootSelectionSet base variableValues parentType leftField
        rightField responseName leftArguments rightArguments arguments
        (.object parentType (none : Option FieldPairProbeTag))
        childSelectionSet harguments (fuel + 1)]
      exact hprobe
    · have hnotProjection :
          ¬ fieldPairProjectionTarget parentType leftField rightField
            leftArguments rightArguments parentType fieldName arguments := by
        intro hprojection
        rcases hprojection with ⟨_hparent, htarget⟩
        rcases htarget with hleft | hright
        · exact htargetLeft ⟨rfl, hleft.1, hleft.2⟩
        · exact htargetRight ⟨rfl, hright.1, hright.2⟩
      have hselectionFuel :
          selectionSetDeepProbeFuel schema parentType selectionSet
            ≤ fuel := by
        have hlocal :=
          selectionSetDeepProbeFuel_le_flatten_member schema parentType
            hmember
        omega
      rcases
          deepFieldSelectionSetReadyWithRef_of_valid_normal_object_promoted_fuel_ge_size
            schema rootSelectionSet
            (ProjectionResolverRef.filler :
              ProjectionResolverRef (Option FieldPairProbeTag))
            variableValues hschema (SelectionSet.size selectionSet + 1)
            parentType variableDefinitions selectionSet fuel
            (by omega) hselectionFuel hvalid hfree hnormal hobject
            hpromoteMember responseName fieldName arguments directives
            childSelectionSet hmem with
        ⟨fieldDefinition, hlookup, hleafFuel, hready⟩
      rcases
          executeField_deepSelectionSetSuccessWithRef_fieldDefinition_ok_of_ready_fuel_ge
            schema rootSelectionSet
            (ProjectionResolverRef.filler :
              ProjectionResolverRef (Option FieldPairProbeTag))
            variableValues fuel
            (.object parentType
              (ProjectionResolverRef.root
                (none : Option FieldPairProbeTag)))
            responseName parentType fieldName arguments childSelectionSet
            fieldDefinition hlookup hleafFuel hready with
        ⟨responseValue, fieldErrors, hdeep, _hnonNull⟩
      refine ⟨responseValue, fieldErrors, ?_⟩
      simp only [projectionRootResolverValue, projectionResolverValue]
      rw [executeField_fieldPairOrDeepSuccessResolvers_other_root_eq_deepSuccessWithRef
        schema rootSelectionSet base variableValues parentType leftField
        rightField parentType fieldName parentType responseName
        leftArguments rightArguments arguments
        (none : Option FieldPairProbeTag) childSelectionSet hnotProjection
        (fuel + 1)]
      exact hdeep

theorem
    selectionSetContextualRuntimeDataDiffWitnessWithFuelGe_of_valid_normal_object_arguments_diff_leaf_finiteSupport
    {schema : Schema}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    {parentType : Name} {left right : List Selection}
    {supportSelectionSets : List (List Selection)} {responseName fieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {fieldDefinition : FieldDefinition} {minFuel : Nat}
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
      -> selectionSetContextualRuntimeDataDiffWitnessWithFuelGe schema
          parentType parentType left right
          (fun selectionSet => selectionSet ∈ supportSelectionSets)
          minFuel := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hobject hsupportValid hleftMem hrightMem hlookup hleaf
    hargumentsDiff
  let members : List (List Selection) := left :: right :: supportSelectionSets
  let rootSelectionSet :=
    [Selection.inlineFragment (some parentType) [] (List.flatten members)]
  let variableValues : Execution.VariableValues := []
  let baseFuel :=
    max minFuel (selectionSetDeepProbeFuel schema parentType
      (List.flatten members))
  let source : Execution.ResolverValue
      (ProjectionResolverRef (Option FieldPairProbeTag)) :=
    projectionRootResolverValue
      (.object parentType (none : Option FieldPairProbeTag))
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet
      (fieldPairProbeResolvers schema rootSelectionSet parentType fieldName
        fieldName leftArguments rightArguments)
      parentType fieldName fieldName leftArguments rightArguments
  have hinclude :
      schema.typeIncludesObjectBool parentType parentType = true :=
    typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject
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
  have hbaseFuel :
      selectionSetDeepProbeFuel schema parentType (List.flatten members)
        ≤ baseFuel := by
    dsimp [baseFuel]
    exact Nat.le_max_right _ _
  have hminFuel : minFuel ≤ baseFuel + 1 := by
    have hle : minFuel ≤ baseFuel := by
      dsimp [baseFuel]
      exact Nat.le_max_left _ _
    exact Nat.le_trans hle (Nat.le_succ _)
  have hleafOfLookup :
      ∀ candidateFieldDefinition,
        schema.lookupField parentType fieldName =
          some candidateFieldDefinition ->
          (TypeRef.named
            candidateFieldDefinition.outputType.namedType).isCompositeBool
            schema = false := by
    intro candidateFieldDefinition hcandidate
    rw [hlookup] at hcandidate
    have hcandidateEq : candidateFieldDefinition = fieldDefinition :=
      Option.some.inj hcandidate.symm
    subst candidateFieldDefinition
    exact hleaf
  have hrightNotLeft :
      ∀ arguments,
        Argument.argumentsEquivalent arguments rightArguments ->
          ¬ fieldProbeTarget parentType fieldName leftArguments parentType
            fieldName arguments := by
    intro arguments hrightArgs hleftTarget
    rcases hleftTarget with ⟨_hparent, _hfield, hleftArgs⟩
    exact hargumentsDiff
      (argumentsEquivalent_trans
        (FieldMerge.argumentsEquivalent_symm hleftArgs) hrightArgs)
  have hleftFieldOk :
      ∀ currentResponseName currentFieldName arguments directives
          childSelectionSet,
        Selection.field currentResponseName currentFieldName arguments
            directives childSelectionSet ∈ left ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema resolvers variableValues
              (baseFuel + 1) source currentResponseName
              [{
                parentType := parentType,
                responseName := currentResponseName,
                fieldName := currentFieldName,
                arguments := arguments,
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(currentResponseName, responseValue)], fieldErrors) := by
    simpa [resolvers, source, rootSelectionSet] using
      selectionSet_fieldPairProjectionFieldOk_framed_leaf_targets_of_valid_normal_members
        (schema := schema) (parentType := parentType)
        (members := members) (selectionSet := left)
        variableValues baseFuel fieldName fieldName leftArguments
        rightArguments hschema hmembers (by simp [members]) hobject
        hbaseFuel hleafOfLookup hleafOfLookup hrightNotLeft
  have hrightFieldOk :
      ∀ currentResponseName currentFieldName arguments directives
          childSelectionSet,
        Selection.field currentResponseName currentFieldName arguments
            directives childSelectionSet ∈ right ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema resolvers variableValues
              (baseFuel + 1) source currentResponseName
              [{
                parentType := parentType,
                responseName := currentResponseName,
                fieldName := currentFieldName,
                arguments := arguments,
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(currentResponseName, responseValue)], fieldErrors) := by
    simpa [resolvers, source, rootSelectionSet] using
      selectionSet_fieldPairProjectionFieldOk_framed_leaf_targets_of_valid_normal_members
        (schema := schema) (parentType := parentType)
        (members := members) (selectionSet := right)
        variableValues baseFuel fieldName fieldName leftArguments
        rightArguments hschema hmembers (by simp [members]) hobject
        hbaseFuel hleafOfLookup hleafOfLookup hrightNotLeft
  have hleftMemFlatten :
      Selection.field responseName fieldName leftArguments leftDirectives
        leftChildSelectionSet ∈ List.flatten members := by
    rw [List.mem_flatten]
    exact ⟨left, by simp [members], hleftMem⟩
  have hrightMemFlatten :
      Selection.field responseName fieldName rightArguments rightDirectives
        rightChildSelectionSet ∈ List.flatten members := by
    rw [List.mem_flatten]
    exact ⟨right, by simp [members], hrightMem⟩
  have hleftFuel :
      leafProbeFuel fieldDefinition.outputType ≤ baseFuel := by
    have hlocal :=
      leafProbeFuel_le_selectionSetDeepProbeFuel_of_field_mem schema
        parentType hleftMemFlatten hlookup
    omega
  have hrightFuel :
      leafProbeFuel fieldDefinition.outputType ≤ baseFuel := by
    have hlocal :=
      leafProbeFuel_le_selectionSetDeepProbeFuel_of_field_mem schema
        parentType hrightMemFlatten hlookup
    omega
  have hleftTarget :
      Execution.executeField schema resolvers variableValues
        (baseFuel + 1) source responseName
        [{
          parentType := parentType,
          responseName := responseName,
          fieldName := fieldName,
          arguments := leftArguments,
          selectionSet := leftChildSelectionSet
        }]
      =
      .ok ([(responseName,
        leafProbeResponseValue fieldDefinition.outputType
          FieldPairProbeTag.left.scalar)], 0) := by
    dsimp [resolvers, source]
    rw [executeField_fieldPairOrDeepSuccessResolvers_left_root
      schema rootSelectionSet
      (fieldPairProbeResolvers schema rootSelectionSet parentType fieldName
        fieldName leftArguments rightArguments)
      variableValues parentType fieldName fieldName responseName
      leftArguments rightArguments leftArguments
      (.object parentType (none : Option FieldPairProbeTag))
      leftChildSelectionSet
      (argumentsEquivalent_refl_forSyntaxDiff leftArguments) (baseFuel + 1)]
    exact
      executeField_fieldPairProbe_left_root_leaf schema rootSelectionSet
        variableValues baseFuel parentType fieldName fieldName responseName
        leftArguments rightArguments leftArguments leftChildSelectionSet
        fieldDefinition (argumentsEquivalent_refl_forSyntaxDiff leftArguments)
        hlookup hleftFuel hleaf
  have hrightTarget :
      Execution.executeField schema resolvers variableValues
        (baseFuel + 1) source responseName
        [{
          parentType := parentType,
          responseName := responseName,
          fieldName := fieldName,
          arguments := rightArguments,
          selectionSet := rightChildSelectionSet
        }]
      =
      .ok ([(responseName,
        leafProbeResponseValue fieldDefinition.outputType
          FieldPairProbeTag.right.scalar)], 0) := by
    dsimp [resolvers, source]
    rw [executeField_fieldPairOrDeepSuccessResolvers_right_root
      schema rootSelectionSet
      (fieldPairProbeResolvers schema rootSelectionSet parentType fieldName
        fieldName leftArguments rightArguments)
      variableValues parentType fieldName fieldName responseName
      leftArguments rightArguments rightArguments
      (.object parentType (none : Option FieldPairProbeTag))
      rightChildSelectionSet
      (argumentsEquivalent_refl_forSyntaxDiff rightArguments)
      (baseFuel + 1)]
    exact
      executeField_fieldPairProbe_right_root_leaf_of_not_left schema
        rootSelectionSet variableValues baseFuel parentType fieldName
        fieldName responseName leftArguments rightArguments rightArguments
        rightChildSelectionSet fieldDefinition
        (hrightNotLeft rightArguments
          (argumentsEquivalent_refl_forSyntaxDiff rightArguments))
        (argumentsEquivalent_refl_forSyntaxDiff rightArguments) hlookup
        hrightFuel hleaf
  have hdataNot :
      ¬ Execution.ResponseValue.semanticEquivalent
        (Execution.executeSelectionSetAsResponse schema resolvers variableValues
          (baseFuel + 1) parentType source left).data
        (Execution.executeSelectionSetAsResponse schema resolvers variableValues
          (baseFuel + 1) parentType source right).data :=
    SemanticSeparation.responseData_not_semanticEquivalent_of_field_value_diff_of_field_ok
      resolvers resolvers variableValues (baseFuel + 1) source source hobject
      hleftNormal hrightNormal hleftFree hrightFree hleftMem hrightMem
      hleftTarget hrightTarget
      (leafProbeResponseValue_not_semanticEquivalent_of_ne
        fieldDefinition.outputType (by simp [FieldPairProbeTag.scalar]))
      hleftFieldOk hrightFieldOk
  refine ⟨
    hinclude,
    ProjectionResolverRef (Option FieldPairProbeTag),
    resolvers,
    variableValues,
    baseFuel + 1,
    ProjectionResolverRef.root (none : Option FieldPairProbeTag),
    hminFuel,
    ?_,
    ?_
  ⟩
  · intro supportSelectionSet hsupport
    rcases hsupportValid supportSelectionSet hsupport with
      ⟨supportVariableDefinitions, _hsupportValid, hsupportFree,
        hsupportNormal⟩
    have hsupportMember : supportSelectionSet ∈ members := by
      simp [members, hsupport]
    have hsupportFieldOk :
        ∀ currentResponseName currentFieldName arguments directives
            childSelectionSet,
          Selection.field currentResponseName currentFieldName arguments
              directives childSelectionSet ∈ supportSelectionSet ->
            ∃ responseValue fieldErrors,
              Execution.executeField schema resolvers variableValues
                (baseFuel + 1) source currentResponseName
                [{
                  parentType := parentType,
                  responseName := currentResponseName,
                  fieldName := currentFieldName,
                  arguments := arguments,
                  selectionSet := childSelectionSet
                }]
              =
              .ok ([(currentResponseName, responseValue)], fieldErrors) := by
      simpa [resolvers, source, rootSelectionSet] using
        selectionSet_fieldPairProjectionFieldOk_framed_leaf_targets_of_valid_normal_members
          (schema := schema) (parentType := parentType)
          (members := members) (selectionSet := supportSelectionSet)
          variableValues baseFuel fieldName fieldName leftArguments
          rightArguments hschema hmembers hsupportMember hobject hbaseFuel
          hleafOfLookup hleafOfLookup hrightNotLeft
    rcases
        ExecutionSuccess.executeSelectionSetAsResponse_object_of_field_ok schema
          resolvers variableValues (baseFuel + 1) parentType source
          supportSelectionSet hsupportFree hsupportNormal hobject
          hsupportFieldOk with
      ⟨supportFields, supportErrors, hsupportResponse⟩
    exact ⟨supportFields, supportErrors, by
      simpa [source, projectionRootResolverValue, projectionResolverValue]
        using hsupportResponse⟩
  · simpa [source, projectionRootResolverValue, projectionResolverValue]
      using hdataNot

theorem
    selectionSetContextualRuntimeDataDiffWitnessWithFuelGe_of_valid_normal_object_fieldName_diff_leaf_finiteSupport
    {schema : Schema}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    {parentType : Name} {left right : List Selection}
    {supportSelectionSets : List (List Selection)}
    {responseName leftFieldName rightFieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {leftFieldDefinition rightFieldDefinition : FieldDefinition} {minFuel : Nat}
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
      -> Selection.field responseName rightFieldName rightArguments rightDirectives
            rightChildSelectionSet
          ∈ right
      -> schema.lookupField parentType leftFieldName = some leftFieldDefinition
      -> schema.lookupField parentType rightFieldName = some rightFieldDefinition
      -> (TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> leftFieldName ≠ rightFieldName
      -> selectionSetContextualRuntimeDataDiffWitnessWithFuelGe schema
          parentType parentType left right
          (fun selectionSet => selectionSet ∈ supportSelectionSets)
          minFuel := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hobject hsupportValid hleftMem hrightMem hleftLookup
    hrightLookup hleftLeaf hrightLeaf hfieldDiff
  let members : List (List Selection) := left :: right :: supportSelectionSets
  let rootSelectionSet :=
    [Selection.inlineFragment (some parentType) [] (List.flatten members)]
  let variableValues : Execution.VariableValues := []
  let baseFuel :=
    max minFuel (selectionSetDeepProbeFuel schema parentType
      (List.flatten members))
  let source : Execution.ResolverValue
      (ProjectionResolverRef (Option FieldPairProbeTag)) :=
    projectionRootResolverValue
      (.object parentType (none : Option FieldPairProbeTag))
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet
      (fieldPairProbeResolvers schema rootSelectionSet parentType
        leftFieldName rightFieldName leftArguments rightArguments)
      parentType leftFieldName rightFieldName leftArguments rightArguments
  have hinclude :
      schema.typeIncludesObjectBool parentType parentType = true :=
    typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject
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
  have hbaseFuel :
      selectionSetDeepProbeFuel schema parentType (List.flatten members)
        ≤ baseFuel := by
    dsimp [baseFuel]
    exact Nat.le_max_right _ _
  have hminFuel : minFuel ≤ baseFuel + 1 := by
    have hle : minFuel ≤ baseFuel := by
      dsimp [baseFuel]
      exact Nat.le_max_left _ _
    exact Nat.le_trans hle (Nat.le_succ _)
  have hleftLeafOfLookup :
      ∀ candidateFieldDefinition,
        schema.lookupField parentType leftFieldName =
          some candidateFieldDefinition ->
          (TypeRef.named
            candidateFieldDefinition.outputType.namedType).isCompositeBool
            schema = false := by
    intro candidateFieldDefinition hcandidate
    rw [hleftLookup] at hcandidate
    have hcandidateEq : candidateFieldDefinition = leftFieldDefinition :=
      Option.some.inj hcandidate.symm
    subst candidateFieldDefinition
    exact hleftLeaf
  have hrightLeafOfLookup :
      ∀ candidateFieldDefinition,
        schema.lookupField parentType rightFieldName =
          some candidateFieldDefinition ->
          (TypeRef.named
            candidateFieldDefinition.outputType.namedType).isCompositeBool
            schema = false := by
    intro candidateFieldDefinition hcandidate
    rw [hrightLookup] at hcandidate
    have hcandidateEq : candidateFieldDefinition = rightFieldDefinition :=
      Option.some.inj hcandidate.symm
    subst candidateFieldDefinition
    exact hrightLeaf
  have hrightNotLeft :
      ∀ arguments,
        Argument.argumentsEquivalent arguments rightArguments ->
          ¬ fieldProbeTarget parentType leftFieldName leftArguments
            parentType rightFieldName arguments := by
    intro arguments _hrightArgs hleftTarget
    exact hfieldDiff hleftTarget.2.1.symm
  have hleftFieldOk :
      ∀ currentResponseName currentFieldName arguments directives
          childSelectionSet,
        Selection.field currentResponseName currentFieldName arguments
            directives childSelectionSet ∈ left ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema resolvers variableValues
              (baseFuel + 1) source currentResponseName
              [{
                parentType := parentType,
                responseName := currentResponseName,
                fieldName := currentFieldName,
                arguments := arguments,
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(currentResponseName, responseValue)], fieldErrors) := by
    simpa [resolvers, source, rootSelectionSet] using
      selectionSet_fieldPairProjectionFieldOk_framed_leaf_targets_of_valid_normal_members
        (schema := schema) (parentType := parentType)
        (members := members) (selectionSet := left)
        variableValues baseFuel leftFieldName rightFieldName leftArguments
        rightArguments hschema hmembers (by simp [members]) hobject
        hbaseFuel hleftLeafOfLookup hrightLeafOfLookup hrightNotLeft
  have hrightFieldOk :
      ∀ currentResponseName currentFieldName arguments directives
          childSelectionSet,
        Selection.field currentResponseName currentFieldName arguments
            directives childSelectionSet ∈ right ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema resolvers variableValues
              (baseFuel + 1) source currentResponseName
              [{
                parentType := parentType,
                responseName := currentResponseName,
                fieldName := currentFieldName,
                arguments := arguments,
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(currentResponseName, responseValue)], fieldErrors) := by
    simpa [resolvers, source, rootSelectionSet] using
      selectionSet_fieldPairProjectionFieldOk_framed_leaf_targets_of_valid_normal_members
        (schema := schema) (parentType := parentType)
        (members := members) (selectionSet := right)
        variableValues baseFuel leftFieldName rightFieldName leftArguments
        rightArguments hschema hmembers (by simp [members]) hobject
        hbaseFuel hleftLeafOfLookup hrightLeafOfLookup hrightNotLeft
  have hleftMemFlatten :
      Selection.field responseName leftFieldName leftArguments leftDirectives
        leftChildSelectionSet ∈ List.flatten members := by
    rw [List.mem_flatten]
    exact ⟨left, by simp [members], hleftMem⟩
  have hrightMemFlatten :
      Selection.field responseName rightFieldName rightArguments
        rightDirectives rightChildSelectionSet ∈ List.flatten members := by
    rw [List.mem_flatten]
    exact ⟨right, by simp [members], hrightMem⟩
  have hleftFuel :
      leafProbeFuel leftFieldDefinition.outputType ≤ baseFuel := by
    have hlocal :=
      leafProbeFuel_le_selectionSetDeepProbeFuel_of_field_mem schema
        parentType hleftMemFlatten hleftLookup
    omega
  have hrightFuel :
      leafProbeFuel rightFieldDefinition.outputType ≤ baseFuel := by
    have hlocal :=
      leafProbeFuel_le_selectionSetDeepProbeFuel_of_field_mem schema
        parentType hrightMemFlatten hrightLookup
    omega
  have hleftTarget :
      Execution.executeField schema resolvers variableValues
        (baseFuel + 1) source responseName
        [{
          parentType := parentType,
          responseName := responseName,
          fieldName := leftFieldName,
          arguments := leftArguments,
          selectionSet := leftChildSelectionSet
        }]
      =
      .ok ([(responseName,
        leafProbeResponseValue leftFieldDefinition.outputType
          FieldPairProbeTag.left.scalar)], 0) := by
    dsimp [resolvers, source]
    rw [executeField_fieldPairOrDeepSuccessResolvers_left_root
      schema rootSelectionSet
      (fieldPairProbeResolvers schema rootSelectionSet parentType
        leftFieldName rightFieldName leftArguments rightArguments)
      variableValues parentType leftFieldName rightFieldName responseName
      leftArguments rightArguments leftArguments
      (.object parentType (none : Option FieldPairProbeTag))
      leftChildSelectionSet
      (argumentsEquivalent_refl_forSyntaxDiff leftArguments) (baseFuel + 1)]
    exact
      executeField_fieldPairProbe_left_root_leaf schema rootSelectionSet
        variableValues baseFuel parentType leftFieldName rightFieldName
        responseName leftArguments rightArguments leftArguments
        leftChildSelectionSet leftFieldDefinition
        (argumentsEquivalent_refl_forSyntaxDiff leftArguments) hleftLookup
        hleftFuel hleftLeaf
  have hrightTarget :
      Execution.executeField schema resolvers variableValues
        (baseFuel + 1) source responseName
        [{
          parentType := parentType,
          responseName := responseName,
          fieldName := rightFieldName,
          arguments := rightArguments,
          selectionSet := rightChildSelectionSet
        }]
      =
      .ok ([(responseName,
        leafProbeResponseValue rightFieldDefinition.outputType
          FieldPairProbeTag.right.scalar)], 0) := by
    dsimp [resolvers, source]
    rw [executeField_fieldPairOrDeepSuccessResolvers_right_root
      schema rootSelectionSet
      (fieldPairProbeResolvers schema rootSelectionSet parentType
        leftFieldName rightFieldName leftArguments rightArguments)
      variableValues parentType leftFieldName rightFieldName responseName
      leftArguments rightArguments rightArguments
      (.object parentType (none : Option FieldPairProbeTag))
      rightChildSelectionSet
      (argumentsEquivalent_refl_forSyntaxDiff rightArguments)
      (baseFuel + 1)]
    exact
      executeField_fieldPairProbe_right_root_leaf_of_not_left schema
        rootSelectionSet variableValues baseFuel parentType leftFieldName
        rightFieldName responseName leftArguments rightArguments
        rightArguments rightChildSelectionSet rightFieldDefinition
        (hrightNotLeft rightArguments
          (argumentsEquivalent_refl_forSyntaxDiff rightArguments))
        (argumentsEquivalent_refl_forSyntaxDiff rightArguments) hrightLookup
        hrightFuel hrightLeaf
  have hdataNot :
      ¬ Execution.ResponseValue.semanticEquivalent
        (Execution.executeSelectionSetAsResponse schema resolvers variableValues
          (baseFuel + 1) parentType source left).data
        (Execution.executeSelectionSetAsResponse schema resolvers variableValues
          (baseFuel + 1) parentType source right).data :=
    SemanticSeparation.responseData_not_semanticEquivalent_of_field_value_diff_of_field_ok
      resolvers resolvers variableValues (baseFuel + 1) source source hobject
      hleftNormal hrightNormal hleftFree hrightFree hleftMem hrightMem
      hleftTarget hrightTarget
      (leafProbeResponseValue_not_semanticEquivalent_of_ne_any
        leftFieldDefinition.outputType rightFieldDefinition.outputType
        (by simp [FieldPairProbeTag.scalar]))
      hleftFieldOk hrightFieldOk
  refine ⟨
    hinclude,
    ProjectionResolverRef (Option FieldPairProbeTag),
    resolvers,
    variableValues,
    baseFuel + 1,
    ProjectionResolverRef.root (none : Option FieldPairProbeTag),
    hminFuel,
    ?_,
    ?_
  ⟩
  · intro supportSelectionSet hsupport
    rcases hsupportValid supportSelectionSet hsupport with
      ⟨_supportVariableDefinitions, _hsupportValid, hsupportFree,
        hsupportNormal⟩
    have hsupportMember : supportSelectionSet ∈ members := by
      simp [members, hsupport]
    have hsupportFieldOk :
        ∀ currentResponseName currentFieldName arguments directives
            childSelectionSet,
          Selection.field currentResponseName currentFieldName arguments
              directives childSelectionSet ∈ supportSelectionSet ->
            ∃ responseValue fieldErrors,
              Execution.executeField schema resolvers variableValues
                (baseFuel + 1) source currentResponseName
                [{
                  parentType := parentType,
                  responseName := currentResponseName,
                  fieldName := currentFieldName,
                  arguments := arguments,
                  selectionSet := childSelectionSet
                }]
              =
              .ok ([(currentResponseName, responseValue)], fieldErrors) := by
      simpa [resolvers, source, rootSelectionSet] using
        selectionSet_fieldPairProjectionFieldOk_framed_leaf_targets_of_valid_normal_members
          (schema := schema) (parentType := parentType)
          (members := members) (selectionSet := supportSelectionSet)
          variableValues baseFuel leftFieldName rightFieldName leftArguments
          rightArguments hschema hmembers hsupportMember hobject hbaseFuel
          hleftLeafOfLookup hrightLeafOfLookup hrightNotLeft
    rcases
        ExecutionSuccess.executeSelectionSetAsResponse_object_of_field_ok schema
          resolvers variableValues (baseFuel + 1) parentType source
          supportSelectionSet hsupportFree hsupportNormal hobject
          hsupportFieldOk with
      ⟨supportFields, supportErrors, hsupportResponse⟩
    exact ⟨supportFields, supportErrors, by
      simpa [source, projectionRootResolverValue, projectionResolverValue]
        using hsupportResponse⟩
  · simpa [source, projectionRootResolverValue, projectionResolverValue]
      using hdataNot

theorem
    selectionSetContextualRuntimeDataDiffWitnessWithFuelGe_of_valid_normal_object_fieldName_diff_left_leaf_right_composite_finiteSupport
    {schema : Schema}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    {parentType : Name} {left right : List Selection}
    {supportSelectionSets : List (List Selection)}
    {responseName leftFieldName rightFieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {leftFieldDefinition rightFieldDefinition : FieldDefinition} {minFuel : Nat}
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
      -> Selection.field responseName rightFieldName rightArguments rightDirectives
            rightChildSelectionSet
          ∈ right
      -> schema.lookupField parentType leftFieldName = some leftFieldDefinition
      -> schema.lookupField parentType rightFieldName = some rightFieldDefinition
      -> (TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> leftFieldName ≠ rightFieldName
      -> selectionSetContextualRuntimeDataDiffWitnessWithFuelGe schema
          parentType parentType left right
          (fun selectionSet => selectionSet ∈ supportSelectionSets)
          minFuel := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hobject hsupportValid hleftMem hrightMem hleftLookup
    hrightLookup hleftLeaf hrightComposite hfieldDiff
  let members : List (List Selection) := left :: right :: supportSelectionSets
  let rootSelectionSet :=
    [Selection.inlineFragment (some parentType) [] (List.flatten members)]
  let variableValues : Execution.VariableValues := []
  let baseFuel :=
    max minFuel (selectionSetDeepProbeFuel schema parentType
      (List.flatten members))
  let source : Execution.ResolverValue
      (ProjectionResolverRef (Option FieldPairProbeTag)) :=
    projectionRootResolverValue
      (.object parentType (none : Option FieldPairProbeTag))
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet
      (fieldPairProbeResolvers schema rootSelectionSet parentType
        leftFieldName rightFieldName leftArguments rightArguments)
      parentType leftFieldName rightFieldName leftArguments rightArguments
  have hinclude :
      schema.typeIncludesObjectBool parentType parentType = true :=
    typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject
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
  have hbaseFuel :
      selectionSetDeepProbeFuel schema parentType (List.flatten members)
        ≤ baseFuel := by
    dsimp [baseFuel]
    exact Nat.le_max_right _ _
  have hminFuel : minFuel ≤ baseFuel + 1 := by
    have hle : minFuel ≤ baseFuel := by
      dsimp [baseFuel]
      exact Nat.le_max_left _ _
    exact Nat.le_trans hle (Nat.le_succ _)
  have hleftLeafOfLookup :
      ∀ candidateFieldDefinition,
        schema.lookupField parentType leftFieldName =
          some candidateFieldDefinition ->
          (TypeRef.named
            candidateFieldDefinition.outputType.namedType).isCompositeBool
            schema = false := by
    intro candidateFieldDefinition hcandidate
    rw [hleftLookup] at hcandidate
    have hcandidateEq : candidateFieldDefinition = leftFieldDefinition :=
      Option.some.inj hcandidate.symm
    subst candidateFieldDefinition
    exact hleftLeaf
  have hrightCompositeOfLookup :
      ∀ candidateFieldDefinition,
        schema.lookupField parentType rightFieldName =
          some candidateFieldDefinition ->
          (TypeRef.named
            candidateFieldDefinition.outputType.namedType).isCompositeBool
            schema = true := by
    intro candidateFieldDefinition hcandidate
    rw [hrightLookup] at hcandidate
    have hcandidateEq : candidateFieldDefinition = rightFieldDefinition :=
      Option.some.inj hcandidate.symm
    subst candidateFieldDefinition
    exact hrightComposite
  have hrightNotLeft :
      ∀ arguments,
        Argument.argumentsEquivalent arguments rightArguments ->
          ¬ fieldProbeTarget parentType leftFieldName leftArguments
            parentType rightFieldName arguments := by
    intro arguments _hrightArgs hleftTarget
    exact hfieldDiff hleftTarget.2.1.symm
  have hleftFieldOk :
      ∀ currentResponseName currentFieldName arguments directives
          childSelectionSet,
        Selection.field currentResponseName currentFieldName arguments
            directives childSelectionSet ∈ left ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema resolvers variableValues
              (baseFuel + 1) source currentResponseName
              [{
                parentType := parentType,
                responseName := currentResponseName,
                fieldName := currentFieldName,
                arguments := arguments,
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(currentResponseName, responseValue)], fieldErrors) := by
    simpa [resolvers, source, rootSelectionSet] using
      selectionSet_fieldPairProjectionFieldOk_framed_left_leaf_right_composite_targets_of_valid_normal_members
        (schema := schema) (parentType := parentType)
        (members := members) (selectionSet := left)
        variableValues baseFuel leftFieldName rightFieldName leftArguments
        rightArguments hschema hmembers (by simp [members]) hobject
        hbaseFuel hleftLeafOfLookup hrightCompositeOfLookup hrightNotLeft
  have hrightFieldOk :
      ∀ currentResponseName currentFieldName arguments directives
          childSelectionSet,
        Selection.field currentResponseName currentFieldName arguments
            directives childSelectionSet ∈ right ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema resolvers variableValues
              (baseFuel + 1) source currentResponseName
              [{
                parentType := parentType,
                responseName := currentResponseName,
                fieldName := currentFieldName,
                arguments := arguments,
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(currentResponseName, responseValue)], fieldErrors) := by
    simpa [resolvers, source, rootSelectionSet] using
      selectionSet_fieldPairProjectionFieldOk_framed_left_leaf_right_composite_targets_of_valid_normal_members
        (schema := schema) (parentType := parentType)
        (members := members) (selectionSet := right)
        variableValues baseFuel leftFieldName rightFieldName leftArguments
        rightArguments hschema hmembers (by simp [members]) hobject
        hbaseFuel hleftLeafOfLookup hrightCompositeOfLookup hrightNotLeft
  have hleftMemFlatten :
      Selection.field responseName leftFieldName leftArguments leftDirectives
        leftChildSelectionSet ∈ List.flatten members := by
    rw [List.mem_flatten]
    exact ⟨left, by simp [members], hleftMem⟩
  have hrightMemFlatten :
      Selection.field responseName rightFieldName rightArguments
        rightDirectives rightChildSelectionSet ∈ List.flatten members := by
    rw [List.mem_flatten]
    exact ⟨right, by simp [members], hrightMem⟩
  have hleftFuel :
      leafProbeFuel leftFieldDefinition.outputType ≤ baseFuel := by
    have hlocal :=
      leafProbeFuel_le_selectionSetDeepProbeFuel_of_field_mem schema
        parentType hleftMemFlatten hleftLookup
    omega
  have hrightFuel :
      leafProbeFuel rightFieldDefinition.outputType ≤ baseFuel := by
    have hlocal :=
      leafProbeFuel_le_selectionSetDeepProbeFuel_of_field_mem schema
        parentType hrightMemFlatten hrightLookup
    omega
  have hleftTarget :
      Execution.executeField schema resolvers variableValues
        (baseFuel + 1) source responseName
        [{
          parentType := parentType,
          responseName := responseName,
          fieldName := leftFieldName,
          arguments := leftArguments,
          selectionSet := leftChildSelectionSet
        }]
      =
      .ok ([(responseName,
        leafProbeResponseValue leftFieldDefinition.outputType
          FieldPairProbeTag.left.scalar)], 0) := by
    dsimp [resolvers, source]
    rw [executeField_fieldPairOrDeepSuccessResolvers_left_root
      schema rootSelectionSet
      (fieldPairProbeResolvers schema rootSelectionSet parentType
        leftFieldName rightFieldName leftArguments rightArguments)
      variableValues parentType leftFieldName rightFieldName responseName
      leftArguments rightArguments leftArguments
      (.object parentType (none : Option FieldPairProbeTag))
      leftChildSelectionSet
      (argumentsEquivalent_refl_forSyntaxDiff leftArguments) (baseFuel + 1)]
    exact
      executeField_fieldPairProbe_left_root_leaf schema rootSelectionSet
        variableValues baseFuel parentType leftFieldName rightFieldName
        responseName leftArguments rightArguments leftArguments
        leftChildSelectionSet leftFieldDefinition
        (argumentsEquivalent_refl_forSyntaxDiff leftArguments) hleftLookup
        hleftFuel hleftLeaf
  have hrightPromote :
      selectionSetDeepPromotionAvailable schema rootSelectionSet parentType
        right := by
    intro targetParent targetField targetRuntimeType targetFieldDefinition
      htargetLookup htargetComposite htargetNonObject hlocalRuntime
    exact
      abstractRuntimeForFieldDeep?_member_framed_promote_some_of_valid_normal_members
        (schema := schema) (currentParent := parentType)
        (targetParent := targetParent) (targetField := targetField)
        (targetRuntimeType := targetRuntimeType)
        (selectionSet := right) (members := members)
        (targetFieldDefinition := targetFieldDefinition)
        hmembers (by simp [members]) htargetLookup htargetComposite
        htargetNonObject hlocalRuntime
  have hrightHeadPromote :
      selectionSetDeepHeadPromotionAvailable schema rootSelectionSet
        parentType right := by
    intro targetParent targetField targetArguments targetRuntimeType
      targetFieldDefinition htargetLookup htargetComposite htargetNonObject
      hlocalRuntime
    exact
      abstractRuntimeForFieldHeadDeep?_member_framed_promote_some_of_valid_normal_members
        (schema := schema) (currentParent := parentType)
        (targetParent := targetParent) (targetField := targetField)
        (targetArguments := targetArguments)
        (targetRuntimeType := targetRuntimeType)
        (selectionSet := right) (members := members)
        (targetFieldDefinition := targetFieldDefinition)
        hmembers (by simp [members]) htargetLookup htargetComposite
        htargetNonObject hlocalRuntime
  rcases
      fieldHeadCompositeRuntime_framed_members_of_valid_normal_mem
        hrightValid hrightNormal hmembers (by simp [members]) hrightMem
        hrightLookup hrightComposite with
    ⟨rightRuntime, hrightRuntime, hrightInclude⟩
  have hrightChildValid :
      Validation.selectionSetValid schema rightVariableDefinitions
        rightFieldDefinition.outputType.namedType rightChildSelectionSet := by
    rcases selectionSetValid_field_lookup_leaf_or_composite_child
        hrightValid hrightMem with
      ⟨candidateDefinition, hcandidateLookup, hkind⟩
    have hcandidateEq : candidateDefinition = rightFieldDefinition := by
      rw [hrightLookup] at hcandidateLookup
      exact Option.some.inj hcandidateLookup.symm
    subst candidateDefinition
    rcases hkind with hleaf | hcompositeKind
    · rw [hrightComposite] at hleaf
      simp at hleaf
    · exact hcompositeKind.2.2
  have hrightChildFree :
      selectionSetDirectiveFree rightChildSelectionSet :=
    selectionSetDirectiveFree_field_child_of_mem hrightFree hrightMem
  have hrightChildNormal :
      selectionSetNormal schema rightFieldDefinition.outputType.namedType
        rightChildSelectionSet :=
    selectionSetNormal_field_child_of_mem_lookup hrightNormal hrightMem
      hrightLookup
  have hrightChildPromote :
      selectionSetDeepPromotionAvailable schema rootSelectionSet
        rightFieldDefinition.outputType.namedType rightChildSelectionSet :=
    selectionSetDeepPromotionAvailable_field_child_of_mem hrightValid
      hrightFree hrightNormal hrightMem hrightLookup hrightPromote
  have hrightChildHeadPromote :
      selectionSetDeepHeadPromotionAvailable schema rootSelectionSet
        rightFieldDefinition.outputType.namedType rightChildSelectionSet :=
    selectionSetDeepHeadPromotionAvailable_field_child_of_mem hrightValid
      hrightFree hrightNormal hrightMem hrightLookup hrightHeadPromote
  have hrightChildFuel :
      selectionSetDeepProbeFuel schema
          rightFieldDefinition.outputType.namedType rightChildSelectionSet
        ≤ baseFuel - leafProbeFuel rightFieldDefinition.outputType - 1 := by
    have hlocal :=
      selectionSetDeepProbeFuel_field_mem schema parentType
        (List.flatten members) responseName rightFieldName rightArguments
        rightDirectives rightChildSelectionSet rightFieldDefinition
        hrightMemFlatten hrightLookup
    omega
  have hrightChildSize :
      SelectionSet.size rightChildSelectionSet < SelectionSet.size right + 1 := by
    have hlt :=
      selectionSet_size_field_child_lt_of_mem
        (responseName := responseName) (fieldName := rightFieldName)
        (arguments := rightArguments) (directives := rightDirectives)
        (childSelectionSet := rightChildSelectionSet)
        (selectionSet := right) hrightMem
    omega
  rcases
      executeSelectionSetAsResponse_fieldPairProbe_tagged_of_valid_normal_promoted_fuel_ge_size
        schema rootSelectionSet variableValues hschema
        (SelectionSet.size right + 1)
        rightFieldDefinition.outputType.namedType rightVariableDefinitions
        rightChildSelectionSet
        (baseFuel - leafProbeFuel rightFieldDefinition.outputType - 1)
        rightRuntime parentType leftFieldName rightFieldName leftArguments
        rightArguments FieldPairProbeTag.right hrightChildSize
        hrightChildFuel hrightChildValid hrightChildFree hrightChildNormal
        hrightInclude hrightChildPromote hrightChildHeadPromote with
    ⟨rightChildFields, rightChildErrors, hrightChildResponseRaw⟩
  have hrightChildFuelEq :
      baseFuel - leafProbeFuel rightFieldDefinition.outputType - 1 + 1 =
        baseFuel - leafProbeFuel rightFieldDefinition.outputType := by
    have hlocal :=
      selectionSetDeepProbeFuel_field_mem schema parentType
        (List.flatten members) responseName rightFieldName rightArguments
        rightDirectives rightChildSelectionSet rightFieldDefinition
        hrightMemFlatten hrightLookup
    omega
  have hrightChildResponse :
      Execution.executeSelectionSetAsResponse schema
          (fieldPairProbeResolvers schema rootSelectionSet parentType
            leftFieldName rightFieldName leftArguments rightArguments)
          variableValues
          (baseFuel - leafProbeFuel rightFieldDefinition.outputType)
          rightRuntime
          (.object rightRuntime (some FieldPairProbeTag.right))
          rightChildSelectionSet =
        ({ data := Execution.ResponseValue.object rightChildFields,
           errors := rightChildErrors } :
          Execution.Response) := by
    simpa [hrightChildFuelEq] using hrightChildResponseRaw
  rcases
      wrapTypeRefSelectionSetResult_ok_nonNull_of_object_response
        rightFieldDefinition.outputType rightChildFields rightChildErrors with
    ⟨rightResponseValue, rightFieldErrors, hrightWrapped, _hrightNonNull⟩
  have hrightTarget :
      Execution.executeField schema resolvers variableValues
        (baseFuel + 1) source responseName
        [{
          parentType := parentType,
          responseName := responseName,
          fieldName := rightFieldName,
          arguments := rightArguments,
          selectionSet := rightChildSelectionSet
        }]
      =
      .ok ([(responseName, rightResponseValue)], rightFieldErrors) := by
    dsimp [resolvers, source]
    rw [executeField_fieldPairOrDeepSuccessResolvers_right_root
      schema rootSelectionSet
      (fieldPairProbeResolvers schema rootSelectionSet parentType
        leftFieldName rightFieldName leftArguments rightArguments)
      variableValues parentType leftFieldName rightFieldName responseName
      leftArguments rightArguments rightArguments
      (.object parentType (none : Option FieldPairProbeTag))
      rightChildSelectionSet
      (argumentsEquivalent_refl_forSyntaxDiff rightArguments)
      (baseFuel + 1)]
    have hraw :=
      executeField_fieldPairProbe_right_root_objectProbe_response_of_not_left_of_fuel_ge
        schema rootSelectionSet variableValues baseFuel parentType
        leftFieldName rightFieldName responseName leftArguments rightArguments
        rightArguments rightChildSelectionSet rightFieldDefinition
        rightRuntime
        (hrightNotLeft rightArguments
          (argumentsEquivalent_refl_forSyntaxDiff rightArguments))
        (argumentsEquivalent_refl_forSyntaxDiff rightArguments)
        hrightLookup hrightRuntime hrightInclude hrightFuel
    rw [hraw, hrightChildResponse, hrightWrapped]
    simp [Execution.singleFieldResult]
  have hdataNot :
      ¬ Execution.ResponseValue.semanticEquivalent
        (Execution.executeSelectionSetAsResponse schema resolvers variableValues
          (baseFuel + 1) parentType source left).data
        (Execution.executeSelectionSetAsResponse schema resolvers variableValues
          (baseFuel + 1) parentType source right).data :=
    SemanticSeparation.responseData_not_semanticEquivalent_of_field_value_diff_of_field_ok
      resolvers resolvers variableValues (baseFuel + 1) source source hobject
      hleftNormal hrightNormal hleftFree hrightFree hleftMem hrightMem
      hleftTarget hrightTarget
      (leafProbeResponseValue_not_semanticEquivalent_wrapped_object_of_composite
        schema leftFieldDefinition.outputType rightFieldDefinition.outputType
        FieldPairProbeTag.left.scalar rightResponseValue rightFieldErrors
        rightChildFields rightChildErrors hleftLeaf hrightComposite
        hrightWrapped)
      hleftFieldOk hrightFieldOk
  refine ⟨
    hinclude,
    ProjectionResolverRef (Option FieldPairProbeTag),
    resolvers,
    variableValues,
    baseFuel + 1,
    ProjectionResolverRef.root (none : Option FieldPairProbeTag),
    hminFuel,
    ?_,
    ?_
  ⟩
  · intro supportSelectionSet hsupport
    rcases hsupportValid supportSelectionSet hsupport with
      ⟨_supportVariableDefinitions, _hsupportValid, hsupportFree,
        hsupportNormal⟩
    have hsupportMember : supportSelectionSet ∈ members := by
      simp [members, hsupport]
    have hsupportFieldOk :
        ∀ currentResponseName currentFieldName arguments directives
            childSelectionSet,
          Selection.field currentResponseName currentFieldName arguments
              directives childSelectionSet ∈ supportSelectionSet ->
            ∃ responseValue fieldErrors,
              Execution.executeField schema resolvers variableValues
                (baseFuel + 1) source currentResponseName
                [{
                  parentType := parentType,
                  responseName := currentResponseName,
                  fieldName := currentFieldName,
                  arguments := arguments,
                  selectionSet := childSelectionSet
                }]
              =
              .ok ([(currentResponseName, responseValue)], fieldErrors) := by
      simpa [resolvers, source, rootSelectionSet] using
        selectionSet_fieldPairProjectionFieldOk_framed_left_leaf_right_composite_targets_of_valid_normal_members
          (schema := schema) (parentType := parentType)
          (members := members) (selectionSet := supportSelectionSet)
          variableValues baseFuel leftFieldName rightFieldName leftArguments
          rightArguments hschema hmembers hsupportMember hobject hbaseFuel
          hleftLeafOfLookup hrightCompositeOfLookup hrightNotLeft
    rcases
        ExecutionSuccess.executeSelectionSetAsResponse_object_of_field_ok schema
          resolvers variableValues (baseFuel + 1) parentType source
          supportSelectionSet hsupportFree hsupportNormal hobject
          hsupportFieldOk with
      ⟨supportFields, supportErrors, hsupportResponse⟩
    exact ⟨supportFields, supportErrors, by
      simpa [source, projectionRootResolverValue, projectionResolverValue]
        using hsupportResponse⟩
  · simpa [source, projectionRootResolverValue, projectionResolverValue]
      using hdataNot

theorem
    selectionSetContextualRuntimeDataDiffWitnessWithFuelGe_of_valid_normal_object_left_responseName_diff_finiteSupport
    {schema : Schema}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    {parentType : Name} {left right : List Selection}
    {supportSelectionSets : List (List Selection)} {responseName fieldName : Name}
    {arguments : List Argument} {directives : List DirectiveApplication}
    {childSelectionSet : List Selection} {minFuel : Nat}
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
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ left
      -> responseName ∉ right.filterMap Selection.responseName?
      -> selectionSetContextualRuntimeDataDiffWitnessWithFuelGe schema
          parentType parentType left right
          (fun selectionSet => selectionSet ∈ supportSelectionSets)
          minFuel := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hobject hsupportValid hleftMem hrightNoResponseName
  let members : List (List Selection) := left :: right :: supportSelectionSets
  let rootSelectionSet :=
    [Selection.inlineFragment (some parentType) [] (List.flatten members)]
  let variableValues : Execution.VariableValues := []
  let source : Execution.ResolverValue PUnit :=
    .object parentType PUnit.unit
  let resolvers :=
    deepSelectionSetSuccessResolversWithRef schema rootSelectionSet
      PUnit.unit
  let baseFuel :=
    max minFuel (selectionSetDeepProbeFuel schema parentType
      (List.flatten members))
  have hinclude :
      schema.typeIncludesObjectBool parentType parentType = true :=
    typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject
  have hsource :
      ∃ runtimeType ref,
        source = Execution.ResolverValue.object runtimeType ref
          ∧ schema.typeIncludesObjectBool parentType runtimeType = true := by
    exact ⟨parentType, PUnit.unit, rfl, hinclude⟩
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
  have hpromoteOfMember :
      ∀ memberSelectionSet,
        memberSelectionSet ∈ members ->
        ∀ targetParent targetField targetRuntimeType targetFieldDefinition,
          schema.lookupField targetParent targetField =
            some targetFieldDefinition ->
          (TypeRef.named
              targetFieldDefinition.outputType.namedType).isCompositeBool
            schema = true ->
          objectTypeNameBool schema
              targetFieldDefinition.outputType.namedType = false ->
          abstractRuntimeForFieldDeep? schema targetParent targetField
            parentType memberSelectionSet = some targetRuntimeType ->
            ∃ runtimeType,
              abstractRuntimeForFieldDeep? schema targetParent targetField
                targetParent rootSelectionSet = some runtimeType
                ∧ schema.typeIncludesObjectBool
                  targetFieldDefinition.outputType.namedType runtimeType =
                  true := by
    intro memberSelectionSet hmember targetParent targetField
      targetRuntimeType targetFieldDefinition hlookup hcomposite hnonObject
      hlocalRuntime
    exact
      abstractRuntimeForFieldDeep?_member_framed_promote_some_of_valid_normal_members
        (schema := schema) (currentParent := parentType)
        (targetParent := targetParent) (targetField := targetField)
        (targetRuntimeType := targetRuntimeType)
        (selectionSet := memberSelectionSet) (members := members)
        (targetFieldDefinition := targetFieldDefinition)
        hmembers hmember hlookup hcomposite hnonObject hlocalRuntime
  have hleftFuel :
      selectionSetDeepProbeFuel schema parentType left ≤ baseFuel := by
    have hmemberFuel :=
      selectionSetDeepProbeFuel_le_flatten_member schema parentType
        (members := members) (selectionSet := left) (by simp [members])
    dsimp [baseFuel]
    omega
  have hrightFuel :
      selectionSetDeepProbeFuel schema parentType right ≤ baseFuel := by
    have hmemberFuel :=
      selectionSetDeepProbeFuel_le_flatten_member schema parentType
        (members := members) (selectionSet := right) (by simp [members])
    dsimp [baseFuel]
    omega
  rcases
      executeSelectionSetAsResponse_deepSelectionSetSuccessWithRef_valid_normal_object_promoted_fuel_ge
        schema rootSelectionSet PUnit.unit variableValues hschema parentType
        leftVariableDefinitions left baseFuel source hleftValid hleftFree
        hleftNormal hobject hsource
        (hpromoteOfMember left (by simp [members])) hleftFuel with
    ⟨leftFields, leftErrors, hleftExec⟩
  rcases
      executeSelectionSetAsResponse_deepSelectionSetSuccessWithRef_valid_normal_object_promoted_fuel_ge
        schema rootSelectionSet PUnit.unit variableValues hschema parentType
        rightVariableDefinitions right baseFuel source hrightValid hrightFree
        hrightNormal hobject hsource
        (hpromoteOfMember right (by simp [members])) hrightFuel with
    ⟨rightFields, rightErrors, hrightExec⟩
  have hleftResponseName :
      responseName ∈ left.filterMap Selection.responseName? :=
    SemanticSeparation.responseName_mem_filterMap_of_field_mem hleftMem
  have hleftCollect :
      responseName ∈
        (Execution.collectFields schema variableValues parentType source left).map
          Prod.fst :=
    (ExecutionKeys.collectFields_normal_object_key_mem_iff schema
      variableValues parentType source responseName hobject hleftNormal
      hleftFree).mpr hleftResponseName
  have hrightCollectNo :
      responseName ∉
        (Execution.collectFields schema variableValues parentType source right).map
          Prod.fst := by
    intro hrightCollect
    exact hrightNoResponseName
      ((ExecutionKeys.collectFields_normal_object_key_mem_iff schema
        variableValues parentType source responseName hobject hrightNormal
        hrightFree).mp hrightCollect)
  have hleftResponseKeys :=
    ExecutionResponseKeys.executeSelectionSetAsResponse_object_keys_eq_collectFields
      schema resolvers variableValues (baseFuel + 1) parentType source left
      hleftExec
  have hrightResponseKeys :=
    ExecutionResponseKeys.executeSelectionSetAsResponse_object_keys_eq_collectFields
      schema resolvers variableValues (baseFuel + 1) parentType source right
      hrightExec
  have hleftKey : responseName ∈ leftFields.map Prod.fst := by
    rw [hleftResponseKeys]
    exact hleftCollect
  have hrightNoKey : responseName ∉ rightFields.map Prod.fst := by
    intro hrightKey
    rw [hrightResponseKeys] at hrightKey
    exact hrightCollectNo hrightKey
  refine ⟨
    hinclude,
    PUnit,
    resolvers,
    variableValues,
    baseFuel + 1,
    PUnit.unit,
    ?_,
    ?_,
    ?_
  ⟩
  · dsimp [baseFuel]
    omega
  · intro supportSelectionSet hsupport
    rcases hsupportValid supportSelectionSet hsupport with
      ⟨supportVariableDefinitions, hsupportSelectionValid,
        hsupportFree, hsupportNormal⟩
    have hsupportMember : supportSelectionSet ∈ members := by
      simp [members, hsupport]
    have hsupportFuel :
        selectionSetDeepProbeFuel schema parentType supportSelectionSet
          ≤ baseFuel := by
      have hmemberFuel :=
        selectionSetDeepProbeFuel_le_flatten_member schema parentType
          (members := members) (selectionSet := supportSelectionSet)
          hsupportMember
      dsimp [baseFuel]
      omega
    exact
      executeSelectionSetAsResponse_deepSelectionSetSuccessWithRef_valid_normal_object_promoted_fuel_ge
        schema rootSelectionSet PUnit.unit variableValues hschema parentType
        supportVariableDefinitions supportSelectionSet baseFuel source
        hsupportSelectionValid hsupportFree hsupportNormal hobject hsource
        (hpromoteOfMember supportSelectionSet hsupportMember)
        hsupportFuel
  · intro hsemantic
    have hobjects :
        (Execution.ResponseValue.object leftFields).semanticEquivalent
          (Execution.ResponseValue.object rightFields) := by
      simpa [resolvers, source, hleftExec, hrightExec] using hsemantic
    exact (SemanticSeparation.responseValue_object_left_key_mismatch_not_semanticallyEquivalent
            hleftKey hrightNoKey)
            hobjects

theorem
    selectionSetContextualRuntimeDataDiffWitnessWithFuelGe_of_valid_normal_object_right_responseName_diff_finiteSupport
    {schema : Schema}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    {parentType : Name} {left right : List Selection}
    {supportSelectionSets : List (List Selection)} {responseName fieldName : Name}
    {arguments : List Argument} {directives : List DirectiveApplication}
    {childSelectionSet : List Selection} {minFuel : Nat}
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
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ right
      -> responseName ∉ left.filterMap Selection.responseName?
      -> selectionSetContextualRuntimeDataDiffWitnessWithFuelGe schema
          parentType parentType left right
          (fun selectionSet => selectionSet ∈ supportSelectionSets)
          minFuel := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hobject hsupportValid hrightMem hleftNoResponseName
  have hwitness :
      selectionSetContextualRuntimeDataDiffWitnessWithFuelGe schema
        parentType parentType right left
        (fun selectionSet => selectionSet ∈ supportSelectionSets)
        minFuel :=
    selectionSetContextualRuntimeDataDiffWitnessWithFuelGe_of_valid_normal_object_left_responseName_diff_finiteSupport
      (schema := schema)
      (leftVariableDefinitions := rightVariableDefinitions)
      (rightVariableDefinitions := leftVariableDefinitions)
      (parentType := parentType) (left := right) (right := left)
      (supportSelectionSets := supportSelectionSets)
      (responseName := responseName) (fieldName := fieldName)
      (arguments := arguments) (directives := directives)
      (childSelectionSet := childSelectionSet) (minFuel := minFuel)
      hschema hrightValid hleftValid hrightFree hleftFree hrightNormal
      hleftNormal hobject hsupportValid hrightMem hleftNoResponseName
  rcases hwitness with
    ⟨hinclude, ObjectRef, resolvers, variableValues, fuel, ref, hfuel,
      hsupport, hnot⟩
  exact ⟨
    hinclude,
    ObjectRef,
    resolvers,
    variableValues,
    fuel,
    ref,
    hfuel,
    hsupport,
    (by
      intro hsemantic
      exact hnot (responseValue_semanticEquivalent_symm hsemantic))
  ⟩

theorem
    selectionSetContextualRuntimeDataDiffWitnessWithFuelGe_of_valid_normal_abstract_left_typeCondition_diff_finiteSupport
    {schema : Schema}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    {parentType : Name} {left right : List Selection}
    {supportSelectionSets : List (List Selection)} {typeCondition : Name}
    {directives : List DirectiveApplication} {childSelectionSet : List Selection}
    {minFuel : Nat}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions parentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> objectTypeNameBool schema parentType = false
      -> (∀ supportSelectionSet,
            supportSelectionSet ∈ supportSelectionSets
            -> ∃ variableDefinitions,
                Validation.selectionSetValid schema variableDefinitions parentType
                  supportSelectionSet
                ∧ selectionSetDirectiveFree supportSelectionSet
                ∧ selectionSetNormal schema parentType supportSelectionSet)
      -> Selection.inlineFragment (some typeCondition) directives childSelectionSet ∈ left
      -> typeCondition ∉ right.filterMap inlineFragmentTypeCondition?
      -> selectionSetContextualRuntimeDataDiffWitnessWithFuelGe schema
          parentType typeCondition left right
          (fun selectionSet => selectionSet ∈ supportSelectionSets)
          minFuel := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hnonObject hsupportValid hleftMem hrightNoTypeCondition
  have hdirectives : directives = [] :=
    selectionSetDirectiveFree_inlineFragment_directives_nil_of_mem
      hleftFree hleftMem
  subst directives
  have hleftMemNil :
      Selection.inlineFragment (some typeCondition) [] childSelectionSet ∈
        left := hleftMem
  rcases selectionSetNormal_inlineFragment_child_of_mem hleftNormal
      hleftMemNil with
    ⟨htypeObjectProp, hchildNormal⟩
  have hoverlap : schema.typesOverlap parentType typeCondition :=
    selectionSetValid_inlineFragment_some_typesOverlap_of_mem hleftValid
      hleftMemNil
  have hinclude :
      schema.typeIncludesObjectBool parentType typeCondition = true :=
    typeIncludesObjectBool_of_typesOverlap_object schema hoverlap
      htypeObjectProp
  have htypeObject :
      objectTypeNameBool schema typeCondition = true :=
    objectTypeNameBool_of_typeIncludesObjectBool hschema hinclude
  let members : List (List Selection) := left :: right :: supportSelectionSets
  let rootSelectionSet :=
    [Selection.inlineFragment (some parentType) [] (List.flatten members)]
  let variableValues : Execution.VariableValues := []
  let source : Execution.ResolverValue PUnit :=
    .object typeCondition PUnit.unit
  let resolvers :=
    deepSelectionSetSuccessResolversWithRef schema rootSelectionSet
      PUnit.unit
  let baseFuel :=
    max minFuel (selectionSetDeepProbeFuel schema parentType
      (List.flatten members))
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
  have hpromoteOfMember :
      ∀ memberSelectionSet,
        memberSelectionSet ∈ members ->
        ∀ targetParent targetField targetRuntimeType targetFieldDefinition,
          schema.lookupField targetParent targetField =
            some targetFieldDefinition ->
          (TypeRef.named
              targetFieldDefinition.outputType.namedType).isCompositeBool
            schema = true ->
          objectTypeNameBool schema
              targetFieldDefinition.outputType.namedType = false ->
          abstractRuntimeForFieldDeep? schema targetParent targetField
            parentType memberSelectionSet = some targetRuntimeType ->
            ∃ runtimeType,
              abstractRuntimeForFieldDeep? schema targetParent targetField
                targetParent rootSelectionSet = some runtimeType
                ∧ schema.typeIncludesObjectBool
                  targetFieldDefinition.outputType.namedType runtimeType =
                  true := by
    intro memberSelectionSet hmember targetParent targetField
      targetRuntimeType targetFieldDefinition hlookup hcomposite htargetNonObject
      hlocalRuntime
    exact
      abstractRuntimeForFieldDeep?_member_framed_promote_some_of_valid_normal_members
        (schema := schema) (currentParent := parentType)
        (targetParent := targetParent) (targetField := targetField)
        (targetRuntimeType := targetRuntimeType)
        (selectionSet := memberSelectionSet) (members := members)
        (targetFieldDefinition := targetFieldDefinition)
        hmembers hmember hlookup hcomposite htargetNonObject hlocalRuntime
  have hchildValid :
      Validation.selectionSetValid schema leftVariableDefinitions
        typeCondition childSelectionSet :=
    selectionSetValid_inlineFragment_some_child_of_mem hleftValid
      hleftMemNil
  have hchildFree : selectionSetDirectiveFree childSelectionSet :=
    selectionSetDirectiveFree_inlineFragment_child_of_mem hleftFree
      hleftMemNil
  have hleftMemberFuel :
      selectionSetDeepProbeFuel schema parentType left ≤ baseFuel := by
    have hmemberFuel :=
      selectionSetDeepProbeFuel_le_flatten_member schema parentType
        (members := members) (selectionSet := left) (by simp [members])
    dsimp [baseFuel]
    omega
  have hchildFuel :
      selectionSetDeepProbeFuel schema typeCondition childSelectionSet
        ≤ baseFuel := by
    have hinlineFuel :=
      selectionSetDeepProbeFuel_inlineFragment_some_mem schema parentType
        left typeCondition [] childSelectionSet hleftMemNil
    omega
  have hchildPromote :
      ∀ targetParent targetField targetRuntimeType targetFieldDefinition,
        schema.lookupField targetParent targetField =
          some targetFieldDefinition ->
        (TypeRef.named
            targetFieldDefinition.outputType.namedType).isCompositeBool
          schema = true ->
        objectTypeNameBool schema
            targetFieldDefinition.outputType.namedType = false ->
        abstractRuntimeForFieldDeep? schema targetParent targetField
          typeCondition childSelectionSet = some targetRuntimeType ->
        ∃ runtimeType,
          abstractRuntimeForFieldDeep? schema targetParent targetField
            targetParent rootSelectionSet = some runtimeType
            ∧ schema.typeIncludesObjectBool
              targetFieldDefinition.outputType.namedType runtimeType =
              true := by
    intro targetParent targetField targetRuntimeType targetFieldDefinition
      hlookup hcomposite htargetNonObject hlocalRuntime
    rcases
        abstractRuntimeForFieldDeep?_inlineFragment_child_promote_some_of_valid_normal
          hleftValid hleftFree hleftNormal hleftMemNil hlookup hcomposite
          htargetNonObject hlocalRuntime with
      ⟨leftRuntimeType, hleftRuntime, _hleftInclude⟩
    exact
      hpromoteOfMember left (by simp [members]) targetParent targetField
        leftRuntimeType targetFieldDefinition hlookup hcomposite
        htargetNonObject hleftRuntime
  have hbodyReady :
      ∀ bodyResponseName bodyFieldName bodyArguments bodyDirectives
          bodyChildSelectionSet,
        Selection.field bodyResponseName bodyFieldName bodyArguments
            bodyDirectives bodyChildSelectionSet ∈ childSelectionSet ->
          ∃ bodyFieldDefinition,
            schema.lookupField typeCondition bodyFieldName =
              some bodyFieldDefinition
              ∧ leafProbeFuel bodyFieldDefinition.outputType ≤ baseFuel
              ∧ deepFieldSelectionSetExecutionReadyWithRef schema
                rootSelectionSet PUnit.unit variableValues
                (baseFuel - leafProbeFuel bodyFieldDefinition.outputType)
                typeCondition bodyResponseName bodyFieldName bodyArguments
                bodyChildSelectionSet bodyFieldDefinition := by
    intro bodyResponseName bodyFieldName bodyArguments bodyDirectives
      bodyChildSelectionSet hbodyFieldMem
    rcases selectionSetValid_field_lookup_of_mem hchildValid
        hbodyFieldMem with
      ⟨bodyFieldDefinition, hbodyLookup, _hbodyArguments,
        _hbodyFieldSelectionValid⟩
    have hleafFuel :
        leafProbeFuel bodyFieldDefinition.outputType ≤ baseFuel := by
      have hfieldFuel :=
        leafProbeFuel_le_selectionSetDeepProbeFuel_of_field_mem schema
          typeCondition (selectionSet := childSelectionSet)
          (responseName := bodyResponseName)
          (fieldName := bodyFieldName)
          (arguments := bodyArguments)
          (directives := bodyDirectives)
          (childSelectionSet := bodyChildSelectionSet)
          (fieldDefinition := bodyFieldDefinition)
          hbodyFieldMem hbodyLookup
      omega
    refine ⟨bodyFieldDefinition, hbodyLookup, hleafFuel, ?_⟩
    rcases
        deepFieldSelectionSetReadyWithRef_of_valid_normal_object_promoted_fuel_ge_size
          schema rootSelectionSet PUnit.unit variableValues hschema
          (SelectionSet.size childSelectionSet + 1) typeCondition
          leftVariableDefinitions childSelectionSet baseFuel (by omega)
          hchildFuel hchildValid hchildFree hchildNormal htypeObject
          hchildPromote bodyResponseName bodyFieldName bodyArguments
          bodyDirectives bodyChildSelectionSet hbodyFieldMem with
      ⟨candidateDefinition, hcandidateLookup, _hcandidateFuel,
        hcandidateReady⟩
    have hcandidateEq : candidateDefinition = bodyFieldDefinition := by
      rw [hbodyLookup] at hcandidateLookup
      exact (Option.some.inj hcandidateLookup).symm
    subst candidateDefinition
    exact hcandidateReady
  rcases
      executeSelectionSetAsResponse_deepSelectionSetSuccessWithRef_abstract_matching_inlineFragment_nonempty
        schema rootSelectionSet PUnit.unit variableValues baseFuel
        hnonObject htypeObject hleftFree hleftNormal hleftMemNil
        (selectionSetValid_inlineFragment_some_child_nonempty_of_mem
          hleftValid hleftMemNil)
        hbodyReady
    with
    ⟨leftResponseField, leftResponseFields, leftErrors, hleftExec⟩
  have hrightCollect :
      Execution.collectFields schema variableValues typeCondition source
        right = [] :=
    collectFields_inlineFragments_without_typeCondition_eq_nil_at_runtime_parent
      schema variableValues (normalParentType := parentType)
      (executionParentType := typeCondition) (runtimeType := typeCondition)
      PUnit.unit hnonObject hrightFree hrightNormal hrightNoTypeCondition
  have hrightExec :
      Execution.executeSelectionSetAsResponse schema resolvers variableValues
        (baseFuel + 1) typeCondition source right =
      ({ data := Execution.ResponseValue.object [], errors := 0 } :
        Execution.Response) := by
    simp [resolvers, source, Execution.executeSelectionSetAsResponse,
      Execution.selectionSetResultToResponse, Execution.executeSelectionSet,
      Execution.executeRootSelectionSet, hrightCollect,
      Execution.executeCollectedFields]
  refine ⟨
    hinclude,
    PUnit,
    resolvers,
    variableValues,
    baseFuel + 1,
    PUnit.unit,
    ?_,
    ?_,
    ?_
  ⟩
  · dsimp [baseFuel]
    omega
  · intro supportSelectionSet hsupport
    rcases hsupportValid supportSelectionSet hsupport with
      ⟨supportVariableDefinitions, hsupportSelectionValid,
        hsupportFree, hsupportNormal⟩
    have hsupportMember : supportSelectionSet ∈ members := by
      simp [members, hsupport]
    have hsupportFuel :
        selectionSetDeepProbeFuel schema parentType supportSelectionSet
          ≤ baseFuel := by
      have hmemberFuel :=
        selectionSetDeepProbeFuel_le_flatten_member schema parentType
          (members := members) (selectionSet := supportSelectionSet)
          hsupportMember
      dsimp [baseFuel]
      omega
    exact
      executeSelectionSetAsResponse_deepSelectionSetSuccessWithRef_valid_normal_promoted_fuel_ge_size
        schema rootSelectionSet PUnit.unit variableValues hschema
        (SelectionSet.size supportSelectionSet + 1) parentType
        supportVariableDefinitions supportSelectionSet baseFuel
        typeCondition (by omega) hsupportFuel hsupportSelectionValid
        hsupportFree hsupportNormal hinclude
        (hpromoteOfMember supportSelectionSet hsupportMember)
  · intro hsemantic
    have hobjects :
        (Execution.ResponseValue.object
            (leftResponseField :: leftResponseFields)).semanticEquivalent
          (Execution.ResponseValue.object []) := by
      simpa [resolvers, source, hleftExec, hrightExec] using hsemantic
    exact
      SemanticSeparation.responseValue_object_cons_not_semanticEquivalent_empty_object
        hobjects

theorem
    selectionSetContextualRuntimeDataDiffWitnessWithFuelGe_of_valid_normal_abstract_right_typeCondition_diff_finiteSupport
    {schema : Schema}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    {parentType : Name} {left right : List Selection}
    {supportSelectionSets : List (List Selection)} {typeCondition : Name}
    {directives : List DirectiveApplication} {childSelectionSet : List Selection}
    {minFuel : Nat}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions parentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> objectTypeNameBool schema parentType = false
      -> (∀ supportSelectionSet,
            supportSelectionSet ∈ supportSelectionSets
            -> ∃ variableDefinitions,
                Validation.selectionSetValid schema variableDefinitions parentType
                  supportSelectionSet
                ∧ selectionSetDirectiveFree supportSelectionSet
                ∧ selectionSetNormal schema parentType supportSelectionSet)
      -> Selection.inlineFragment (some typeCondition) directives childSelectionSet
          ∈ right
      -> typeCondition ∉ left.filterMap inlineFragmentTypeCondition?
      -> selectionSetContextualRuntimeDataDiffWitnessWithFuelGe schema
          parentType typeCondition left right
          (fun selectionSet => selectionSet ∈ supportSelectionSets)
          minFuel := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hnonObject hsupportValid hrightMem hleftNoTypeCondition
  exact
    selectionSetContextualRuntimeDataDiffWitnessWithFuelGe_symm
      (selectionSetContextualRuntimeDataDiffWitnessWithFuelGe_of_valid_normal_abstract_left_typeCondition_diff_finiteSupport
        (schema := schema)
        (leftVariableDefinitions := rightVariableDefinitions)
        (rightVariableDefinitions := leftVariableDefinitions)
        (parentType := parentType) (left := right) (right := left)
        (supportSelectionSets := supportSelectionSets)
        (typeCondition := typeCondition) (directives := directives)
        (childSelectionSet := childSelectionSet) (minFuel := minFuel)
        hschema hrightValid hleftValid hrightFree hleftFree hrightNormal
        hleftNormal hnonObject hsupportValid hrightMem hleftNoTypeCondition)

noncomputable def selectionSetTargetInlineFragmentSelectionSets (typeCondition : Name)
    : List Selection -> List (List Selection)
  | [] => []
  | Selection.inlineFragment (some headTypeCondition) _directives
      childSelectionSet :: rest => by
      classical
      exact
        if headTypeCondition = typeCondition then
          childSelectionSet ::
            selectionSetTargetInlineFragmentSelectionSets typeCondition rest
        else
          selectionSetTargetInlineFragmentSelectionSets typeCondition rest
  | _selection :: rest =>
      selectionSetTargetInlineFragmentSelectionSets typeCondition rest

noncomputable def splitTargetInlineFragmentSelectionSets
    (typeCondition : Name)
    (leftPref rightPref leftSuffix rightSuffix : List Selection)
    : List (List Selection) :=
  selectionSetTargetInlineFragmentSelectionSets typeCondition leftPref
  ++ selectionSetTargetInlineFragmentSelectionSets typeCondition rightPref
  ++ selectionSetTargetInlineFragmentSelectionSets typeCondition leftSuffix
  ++ selectionSetTargetInlineFragmentSelectionSets typeCondition rightSuffix

noncomputable def supportTargetInlineFragmentSelectionSets (typeCondition : Name)
    : List (List Selection) -> List (List Selection)
  | [] => []
  | selectionSet :: rest =>
      selectionSetTargetInlineFragmentSelectionSets typeCondition selectionSet
      ++ supportTargetInlineFragmentSelectionSets typeCondition rest

noncomputable def abstractChildSupportSelectionSets
    (typeCondition : Name)
    (leftPref rightPref leftSuffix rightSuffix : List Selection)
    (supportSelectionSets : List (List Selection))
    : List (List Selection) :=
  splitTargetInlineFragmentSelectionSets typeCondition leftPref rightPref
    leftSuffix rightSuffix
  ++ supportTargetInlineFragmentSelectionSets typeCondition supportSelectionSets

theorem selectionSetTargetInlineFragmentSelectionSets_mem
    {typeCondition : Name} {selectionSet childSelectionSet : List Selection}
    : childSelectionSet
        ∈ selectionSetTargetInlineFragmentSelectionSets typeCondition selectionSet
      -> ∃ directives,
          Selection.inlineFragment (some typeCondition) directives childSelectionSet
          ∈ selectionSet := by
  intro hmem
  induction selectionSet with
  | nil =>
      simp [selectionSetTargetInlineFragmentSelectionSets] at hmem
  | cons selection rest ih =>
      cases selection with
      | field responseName fieldName arguments directives headChildSelectionSet =>
          simp [selectionSetTargetInlineFragmentSelectionSets] at hmem
          rcases ih hmem with ⟨tailDirectives, htailMem⟩
          exact ⟨tailDirectives, List.mem_cons_of_mem _ htailMem⟩
      | inlineFragment maybeTypeCondition directives headChildSelectionSet =>
          cases maybeTypeCondition with
          | none =>
              simp [selectionSetTargetInlineFragmentSelectionSets] at hmem
              rcases ih hmem with ⟨tailDirectives, htailMem⟩
              exact ⟨tailDirectives, List.mem_cons_of_mem _ htailMem⟩
          | some headTypeCondition =>
              by_cases htarget : headTypeCondition = typeCondition
              · simp [selectionSetTargetInlineFragmentSelectionSets, htarget]
                  at hmem
                rcases hmem with hhead | htail
                · subst childSelectionSet
                  subst headTypeCondition
                  exact ⟨directives, by simp⟩
                · rcases ih htail with ⟨tailDirectives, htailMem⟩
                  exact ⟨tailDirectives, List.mem_cons_of_mem _ htailMem⟩
              · simp [selectionSetTargetInlineFragmentSelectionSets, htarget]
                  at hmem
                rcases ih hmem with ⟨tailDirectives, htailMem⟩
                exact ⟨tailDirectives, List.mem_cons_of_mem _ htailMem⟩

theorem selectionSetTargetInlineFragmentSelectionSets_of_mem
    {typeCondition : Name} {directives : List DirectiveApplication}
    {selectionSet childSelectionSet : List Selection}
    : Selection.inlineFragment (some typeCondition) directives childSelectionSet
        ∈ selectionSet
      -> childSelectionSet
          ∈ selectionSetTargetInlineFragmentSelectionSets typeCondition selectionSet := by
  intro hmem
  induction selectionSet with
  | nil =>
      simp at hmem
  | cons selection rest ih =>
      simp only [List.mem_cons] at hmem
      rcases hmem with hhead | htail
      · subst selection
        simp [selectionSetTargetInlineFragmentSelectionSets]
      · cases selection with
        | field responseName fieldName arguments headDirectives
            headChildSelectionSet =>
            simpa [selectionSetTargetInlineFragmentSelectionSets] using
              ih htail
        | inlineFragment maybeTypeCondition headDirectives
            headChildSelectionSet =>
            cases maybeTypeCondition with
            | none =>
                simpa [selectionSetTargetInlineFragmentSelectionSets] using
                  ih htail
            | some headTypeCondition =>
                by_cases htarget : headTypeCondition = typeCondition
                · simp [selectionSetTargetInlineFragmentSelectionSets,
                    htarget, ih htail]
                · simpa [selectionSetTargetInlineFragmentSelectionSets,
                    htarget] using ih htail

theorem selectionSetTargetInlineFragmentSelectionSets_child_valid_free_normal
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType typeCondition : Name}
    {selectionSet childSelectionSet : List Selection}
    : Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> selectionSetDirectiveFree selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> childSelectionSet
          ∈ selectionSetTargetInlineFragmentSelectionSets typeCondition selectionSet
      -> Validation.selectionSetValid schema variableDefinitions typeCondition
            childSelectionSet
          ∧ selectionSetDirectiveFree childSelectionSet
          ∧ selectionSetNormal schema typeCondition childSelectionSet := by
  intro hvalid hfree hnormal hmem
  rcases selectionSetTargetInlineFragmentSelectionSets_mem hmem with
    ⟨directives, hinlineMem⟩
  exact ⟨
    selectionSetValid_inlineFragment_some_child_of_mem hvalid hinlineMem,
    selectionSetDirectiveFree_inlineFragment_child_of_mem hfree hinlineMem,
    (selectionSetNormal_inlineFragment_child_of_mem hnormal hinlineMem).2
  ⟩

theorem selectionSetTargetInlineFragmentSelectionSets_child_valid_free_normal_of_subset
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType typeCondition : Name}
    {whole selectionSet childSelectionSet : List Selection}
    : (∀ directives childSelectionSet,
        Selection.inlineFragment (some typeCondition) directives childSelectionSet
          ∈ selectionSet
        -> Selection.inlineFragment (some typeCondition) directives childSelectionSet
            ∈ whole)
      -> Validation.selectionSetValid schema variableDefinitions parentType whole
      -> selectionSetDirectiveFree whole
      -> selectionSetNormal schema parentType whole
      -> childSelectionSet
          ∈ selectionSetTargetInlineFragmentSelectionSets typeCondition selectionSet
      -> Validation.selectionSetValid schema variableDefinitions typeCondition
            childSelectionSet
          ∧ selectionSetDirectiveFree childSelectionSet
          ∧ selectionSetNormal schema typeCondition childSelectionSet := by
  intro hsubset hvalid hfree hnormal hmem
  rcases selectionSetTargetInlineFragmentSelectionSets_mem hmem with
    ⟨directives, hinlineMem⟩
  have hwholeMem :=
    hsubset directives childSelectionSet hinlineMem
  exact ⟨
    selectionSetValid_inlineFragment_some_child_of_mem hvalid hwholeMem,
    selectionSetDirectiveFree_inlineFragment_child_of_mem hfree hwholeMem,
    (selectionSetNormal_inlineFragment_child_of_mem hnormal hwholeMem).2
  ⟩

theorem splitTargetInlineFragmentSelectionSets_child_exists_valid_free_normal
    {schema : Schema}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    {parentType typeCondition : Name}
    {leftPref rightPref leftSuffix rightSuffix : List Selection}
    {leftChildSelectionSet rightChildSelectionSet childSelectionSet : List Selection}
    : Validation.selectionSetValid schema leftVariableDefinitions parentType
        (leftPref
          ++ Selection.inlineFragment (some typeCondition) [] leftChildSelectionSet
              :: leftSuffix)
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType
          (rightPref
            ++ Selection.inlineFragment (some typeCondition) [] rightChildSelectionSet
                :: rightSuffix)
      -> selectionSetDirectiveFree
          (leftPref
            ++ Selection.inlineFragment (some typeCondition) [] leftChildSelectionSet
                :: leftSuffix)
      -> selectionSetDirectiveFree
          (rightPref
            ++ Selection.inlineFragment (some typeCondition) [] rightChildSelectionSet
                :: rightSuffix)
      -> selectionSetNormal schema parentType
          (leftPref
            ++ Selection.inlineFragment (some typeCondition) [] leftChildSelectionSet
                :: leftSuffix)
      -> selectionSetNormal schema parentType
          (rightPref
            ++ Selection.inlineFragment (some typeCondition) [] rightChildSelectionSet
                :: rightSuffix)
      -> childSelectionSet
          ∈ splitTargetInlineFragmentSelectionSets typeCondition leftPref
              rightPref leftSuffix rightSuffix
      -> ∃ variableDefinitions,
          Validation.selectionSetValid schema variableDefinitions typeCondition
            childSelectionSet
          ∧ selectionSetDirectiveFree childSelectionSet
          ∧ selectionSetNormal schema typeCondition childSelectionSet := by
  intro hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hmem
  simp [splitTargetInlineFragmentSelectionSets] at hmem
  rcases hmem with hleftPref | hrightPref | hleftSuffix | hrightSuffix
  · exact ⟨
      leftVariableDefinitions,
      selectionSetTargetInlineFragmentSelectionSets_child_valid_free_normal_of_subset
        (schema := schema) (parentType := parentType)
        (typeCondition := typeCondition)
        (whole :=
          leftPref
          ++ Selection.inlineFragment (some typeCondition) [] leftChildSelectionSet
              :: leftSuffix)
        (selectionSet := leftPref)
        (childSelectionSet := childSelectionSet)
        (by
          intro directives childSelectionSet hchildMem
          exact List.mem_append_left _ hchildMem)
        hleftValid hleftFree hleftNormal hleftPref
    ⟩
  · exact ⟨
      rightVariableDefinitions,
      selectionSetTargetInlineFragmentSelectionSets_child_valid_free_normal_of_subset
        (schema := schema) (parentType := parentType)
        (typeCondition := typeCondition)
        (whole :=
          rightPref
          ++ Selection.inlineFragment (some typeCondition) [] rightChildSelectionSet
              :: rightSuffix)
        (selectionSet := rightPref)
        (childSelectionSet := childSelectionSet)
        (by
          intro directives childSelectionSet hchildMem
          exact List.mem_append_left _ hchildMem)
        hrightValid hrightFree hrightNormal hrightPref
    ⟩
  · exact ⟨
      leftVariableDefinitions,
      selectionSetTargetInlineFragmentSelectionSets_child_valid_free_normal_of_subset
        (schema := schema) (parentType := parentType)
        (typeCondition := typeCondition)
        (whole :=
          leftPref
          ++ Selection.inlineFragment (some typeCondition) [] leftChildSelectionSet
              :: leftSuffix)
        (selectionSet := leftSuffix)
        (childSelectionSet := childSelectionSet)
        (by
          intro directives childSelectionSet hchildMem
          exact
            List.mem_append_right leftPref
              (List.mem_cons_of_mem
                (Selection.inlineFragment (some typeCondition) []
                  leftChildSelectionSet) hchildMem))
        hleftValid hleftFree hleftNormal hleftSuffix
    ⟩
  · exact ⟨
      rightVariableDefinitions,
      selectionSetTargetInlineFragmentSelectionSets_child_valid_free_normal_of_subset
        (schema := schema) (parentType := parentType)
        (typeCondition := typeCondition)
        (whole :=
          rightPref
          ++ Selection.inlineFragment (some typeCondition) [] rightChildSelectionSet
              :: rightSuffix)
        (selectionSet := rightSuffix)
        (childSelectionSet := childSelectionSet)
        (by
          intro directives childSelectionSet hchildMem
          exact
            List.mem_append_right rightPref
              (List.mem_cons_of_mem
                (Selection.inlineFragment (some typeCondition) []
                  rightChildSelectionSet) hchildMem))
        hrightValid hrightFree hrightNormal hrightSuffix
    ⟩

theorem
    selectionSetTargetInlineFragmentSelectionSets_subset_supportTargetInlineFragmentSelectionSets_of_mem
    {typeCondition : Name} {supportSelectionSets : List (List Selection)}
    {selectionSet childSelectionSet : List Selection}
    : selectionSet ∈ supportSelectionSets
      -> childSelectionSet
          ∈ selectionSetTargetInlineFragmentSelectionSets typeCondition selectionSet
      -> childSelectionSet
          ∈ supportTargetInlineFragmentSelectionSets typeCondition
              supportSelectionSets := by
  intro hselection hchild
  induction supportSelectionSets with
  | nil =>
      simp at hselection
  | cons head rest ih =>
      simp at hselection
      rcases hselection with hhead | htail
      · subst selectionSet
        simp [supportTargetInlineFragmentSelectionSets, hchild]
      · have hrest := ih htail
        simp [supportTargetInlineFragmentSelectionSets, hrest]

theorem supportTargetInlineFragmentSelectionSets_child_exists_valid_free_normal
    {schema : Schema} {parentType typeCondition : Name}
    {supportSelectionSets : List (List Selection)}
    {childSelectionSet : List Selection}
    : (∀ supportSelectionSet,
        supportSelectionSet ∈ supportSelectionSets
        -> ∃ variableDefinitions,
            Validation.selectionSetValid schema variableDefinitions parentType
              supportSelectionSet
            ∧ selectionSetDirectiveFree supportSelectionSet
            ∧ selectionSetNormal schema parentType supportSelectionSet)
      -> childSelectionSet
          ∈ supportTargetInlineFragmentSelectionSets typeCondition supportSelectionSets
      -> ∃ variableDefinitions,
          Validation.selectionSetValid schema variableDefinitions typeCondition
            childSelectionSet
          ∧ selectionSetDirectiveFree childSelectionSet
          ∧ selectionSetNormal schema typeCondition childSelectionSet := by
  intro hsupportValid hmem
  induction supportSelectionSets with
  | nil =>
      simp [supportTargetInlineFragmentSelectionSets] at hmem
  | cons supportSelectionSet rest ih =>
      simp [supportTargetInlineFragmentSelectionSets] at hmem
      rcases hmem with hhead | htail
      · rcases hsupportValid supportSelectionSet (by simp) with
          ⟨variableDefinitions, hvalid, hfree, hnormal⟩
        exact ⟨
          variableDefinitions,
          selectionSetTargetInlineFragmentSelectionSets_child_valid_free_normal
            hvalid hfree hnormal hhead
        ⟩
      · exact
          ih (by
            intro tailSupportSelectionSet htailSupport
            exact hsupportValid tailSupportSelectionSet
              (by simp [htailSupport])) htail

theorem
    selectionSetContextualRuntimeDataDiffWitnessWithFuelGe_of_valid_normal_abstract_child_contextualRuntimeDiff_split_finiteSupport
    {schema : Schema}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    {parentType typeCondition runtimeType : Name}
    {leftChildSelectionSet rightChildSelectionSet
      leftPref rightPref leftSuffix rightSuffix
      : List Selection}
    {supportSelectionSets : List (List Selection)} {minFuel : Nat}
    : Validation.selectionSetValid schema leftVariableDefinitions parentType
        (leftPref
          ++ Selection.inlineFragment (some typeCondition) [] leftChildSelectionSet
              :: leftSuffix)
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType
          (rightPref
            ++ Selection.inlineFragment (some typeCondition) [] rightChildSelectionSet
                :: rightSuffix)
      -> selectionSetDirectiveFree
          (leftPref
            ++ Selection.inlineFragment (some typeCondition) [] leftChildSelectionSet
                :: leftSuffix)
      -> selectionSetDirectiveFree
          (rightPref
            ++ Selection.inlineFragment (some typeCondition) [] rightChildSelectionSet
                :: rightSuffix)
      -> selectionSetNormal schema parentType
          (leftPref
            ++ Selection.inlineFragment (some typeCondition) [] leftChildSelectionSet
                :: leftSuffix)
      -> selectionSetNormal schema parentType
          (rightPref
            ++ Selection.inlineFragment (some typeCondition) [] rightChildSelectionSet
                :: rightSuffix)
      -> objectTypeNameBool schema parentType = false
      -> (∀ supportSelectionSet,
            supportSelectionSet ∈ supportSelectionSets
            -> ∃ variableDefinitions,
                Validation.selectionSetValid schema variableDefinitions parentType
                  supportSelectionSet
                ∧ selectionSetDirectiveFree supportSelectionSet
                ∧ selectionSetNormal schema parentType supportSelectionSet)
      -> selectionSetContextualRuntimeDataDiffWitnessWithFuelGe schema
          typeCondition runtimeType leftChildSelectionSet rightChildSelectionSet
          (fun childSelectionSet =>
            childSelectionSet
            ∈ abstractChildSupportSelectionSets typeCondition leftPref rightPref
                leftSuffix rightSuffix supportSelectionSets)
          minFuel
      -> selectionSetContextualRuntimeDataDiffWitnessWithFuelGe schema
          parentType runtimeType
          (leftPref
            ++ Selection.inlineFragment (some typeCondition) [] leftChildSelectionSet
                :: leftSuffix)
          (rightPref
            ++ Selection.inlineFragment (some typeCondition) [] rightChildSelectionSet
                :: rightSuffix)
          (fun selectionSet => selectionSet ∈ supportSelectionSets)
          minFuel := by
  intro hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hnonObject hsupportValid hwitness
  let leftSelectionSet :=
    leftPref ++ Selection.inlineFragment (some typeCondition) []
      leftChildSelectionSet :: leftSuffix
  let rightSelectionSet :=
    rightPref ++ Selection.inlineFragment (some typeCondition) []
      rightChildSelectionSet :: rightSuffix
  have hleftMem :
      Selection.inlineFragment (some typeCondition) []
        leftChildSelectionSet ∈ leftSelectionSet := by
    simp [leftSelectionSet]
  have hrightMem :
      Selection.inlineFragment (some typeCondition) []
        rightChildSelectionSet ∈ rightSelectionSet := by
    simp [rightSelectionSet]
  rcases selectionSetNormal_inlineFragment_child_of_mem hleftNormal
      hleftMem with
    ⟨htypeObject, _hleftChildNormal⟩
  have hparentOverlap : schema.typesOverlap parentType typeCondition :=
    selectionSetValid_inlineFragment_some_typesOverlap_of_mem hleftValid
      hleftMem
  have hparentInclude :
      schema.typeIncludesObjectBool parentType typeCondition = true :=
    typeIncludesObjectBool_of_typesOverlap_object schema hparentOverlap
      htypeObject
  have htypeObjectBool :
      objectTypeNameBool schema typeCondition = true :=
    objectTypeNameBool_eq_true_of_objectType_forNormality schema
      htypeObject
  let childSupport : List Selection -> Prop :=
    fun childSelectionSet =>
      childSelectionSet ∈
        abstractChildSupportSelectionSets typeCondition leftPref rightPref
          leftSuffix rightSuffix supportSelectionSets
  change
    selectionSetContextualRuntimeDataDiffWitnessWithFuelGe schema
      typeCondition runtimeType leftChildSelectionSet rightChildSelectionSet
      childSupport minFuel at hwitness
  rcases hwitness with
    ⟨hchildInclude, ObjectRef, resolvers, variableValues, fuel, ref,
      hfuel, hsupportResponse, hchildNot⟩
  have hruntimeEq : runtimeType = typeCondition :=
    typeIncludesObjectBool_eq_of_objectTypeNameBool_true schema
      htypeObjectBool hchildInclude
  subst runtimeType
  have happly :
      Execution.doesFragmentTypeApplyBool schema typeCondition
        (.object typeCondition ref) typeCondition = true :=
    doesFragmentTypeApplyBool_object_self schema (ref := ref)
      htypeObjectBool
  have hleftMiddle :
      Execution.executeSelectionSet schema resolvers variableValues fuel
        typeCondition (.object typeCondition ref) leftSelectionSet
      =
      Execution.executeSelectionSet schema resolvers variableValues fuel
        typeCondition (.object typeCondition ref)
        [Selection.inlineFragment (some typeCondition) []
          leftChildSelectionSet] :=
    executeSelectionSet_middle_inlineFragment_only_eq_singleton_at_runtime_parent
      schema resolvers variableValues fuel ref hnonObject htypeObjectBool
      hleftFree hleftNormal
  have hrightMiddle :
      Execution.executeSelectionSet schema resolvers variableValues fuel
        typeCondition (.object typeCondition ref) rightSelectionSet
      =
      Execution.executeSelectionSet schema resolvers variableValues fuel
        typeCondition (.object typeCondition ref)
        [Selection.inlineFragment (some typeCondition) []
          rightChildSelectionSet] :=
    executeSelectionSet_middle_inlineFragment_only_eq_singleton_at_runtime_parent
      schema resolvers variableValues fuel ref hnonObject htypeObjectBool
      hrightFree hrightNormal
  have hleftFlatten :
      Execution.executeSelectionSet schema resolvers variableValues fuel
        typeCondition (.object typeCondition ref)
        [Selection.inlineFragment (some typeCondition) []
          leftChildSelectionSet]
      =
      Execution.executeSelectionSet schema resolvers variableValues fuel
        typeCondition (.object typeCondition ref)
        leftChildSelectionSet := by
    simpa using
      executeSelectionSet_inlineFragment_some_directiveFree_apply_flatten
        schema resolvers variableValues fuel typeCondition typeCondition
        (.object typeCondition ref) leftChildSelectionSet [] happly
  have hrightFlatten :
      Execution.executeSelectionSet schema resolvers variableValues fuel
        typeCondition (.object typeCondition ref)
        [Selection.inlineFragment (some typeCondition) []
          rightChildSelectionSet]
      =
      Execution.executeSelectionSet schema resolvers variableValues fuel
        typeCondition (.object typeCondition ref)
        rightChildSelectionSet := by
    simpa using
      executeSelectionSet_inlineFragment_some_directiveFree_apply_flatten
        schema resolvers variableValues fuel typeCondition typeCondition
        (.object typeCondition ref) rightChildSelectionSet [] happly
  have hleftResponse :
      Execution.executeSelectionSetAsResponse schema resolvers variableValues fuel
        typeCondition (.object typeCondition ref) leftSelectionSet
      =
      Execution.executeSelectionSetAsResponse schema resolvers variableValues fuel
        typeCondition (.object typeCondition ref) leftChildSelectionSet := by
    simp [Execution.executeSelectionSetAsResponse, Execution.selectionSetResultToResponse,
      hleftMiddle, hleftFlatten]
  have hrightResponse :
      Execution.executeSelectionSetAsResponse schema resolvers variableValues fuel
        typeCondition (.object typeCondition ref) rightSelectionSet
      =
      Execution.executeSelectionSetAsResponse schema resolvers variableValues fuel
        typeCondition (.object typeCondition ref) rightChildSelectionSet := by
    simp [Execution.executeSelectionSetAsResponse, Execution.selectionSetResultToResponse,
      hrightMiddle, hrightFlatten]
  refine ⟨hparentInclude, ObjectRef, resolvers, variableValues, fuel, ref, hfuel, ?_, ?_⟩
  · intro supportSelectionSet hsupport
    rcases hsupportValid supportSelectionSet hsupport with
      ⟨_supportVariableDefinitions, _hsupportValid, hsupportFree,
        hsupportNormal⟩
    by_cases htypeMem :
        typeCondition ∈
          supportSelectionSet.filterMap inlineFragmentTypeCondition?
    · rcases
        selectionSetNormal_inlineFragment_mem_of_abstract_typeCondition_mem
          hsupportNormal hnonObject htypeMem with
        ⟨directives, supportChildSelectionSet, hsupportInlineMem⟩
      have hdirectives : directives = [] :=
        selectionSetDirectiveFree_inlineFragment_directives_nil_of_mem
          hsupportFree hsupportInlineMem
      subst directives
      rcases List.mem_iff_append.mp hsupportInlineMem with
        ⟨supportPref, supportSuffix, hsupportEq⟩
      subst supportSelectionSet
      have hsupportTarget :
          supportChildSelectionSet ∈
            supportTargetInlineFragmentSelectionSets typeCondition
              supportSelectionSets := by
        exact
          selectionSetTargetInlineFragmentSelectionSets_subset_supportTargetInlineFragmentSelectionSets_of_mem
            (selectionSet :=
              supportPref ++ Selection.inlineFragment (some typeCondition)
                [] supportChildSelectionSet :: supportSuffix)
            hsupport
            (selectionSetTargetInlineFragmentSelectionSets_of_mem
              (directives := []) hsupportInlineMem)
      have hchildSupport : childSupport supportChildSelectionSet := by
        simp [childSupport, abstractChildSupportSelectionSets,
          hsupportTarget]
      rcases hsupportResponse supportChildSelectionSet hchildSupport with
        ⟨supportFields, supportErrors, hsupportChildResponse⟩
      have hsupportMiddle :
          Execution.executeSelectionSet schema resolvers variableValues fuel
            typeCondition (.object typeCondition ref)
            (supportPref ++ Selection.inlineFragment (some typeCondition)
              [] supportChildSelectionSet :: supportSuffix)
          =
          Execution.executeSelectionSet schema resolvers variableValues fuel
            typeCondition (.object typeCondition ref)
            [Selection.inlineFragment (some typeCondition) []
              supportChildSelectionSet] :=
        executeSelectionSet_middle_inlineFragment_only_eq_singleton_at_runtime_parent
          schema resolvers variableValues fuel ref hnonObject
          htypeObjectBool hsupportFree hsupportNormal
      have hsupportFlatten :
          Execution.executeSelectionSet schema resolvers variableValues fuel
            typeCondition (.object typeCondition ref)
            [Selection.inlineFragment (some typeCondition) []
              supportChildSelectionSet]
          =
          Execution.executeSelectionSet schema resolvers variableValues fuel
            typeCondition (.object typeCondition ref)
            supportChildSelectionSet := by
        simpa using
          executeSelectionSet_inlineFragment_some_directiveFree_apply_flatten
            schema resolvers variableValues fuel typeCondition typeCondition
            (.object typeCondition ref) supportChildSelectionSet [] happly
      exact ⟨supportFields, supportErrors, by
        simpa [Execution.executeSelectionSetAsResponse, Execution.selectionSetResultToResponse,
          hsupportMiddle, hsupportFlatten] using hsupportChildResponse⟩
    · have hcollect :
          Execution.collectFields schema variableValues typeCondition
            (.object typeCondition ref) supportSelectionSet = [] :=
        collectFields_inlineFragments_without_typeCondition_eq_nil_at_runtime_parent
          schema variableValues (normalParentType := parentType)
          (executionParentType := typeCondition)
          (runtimeType := typeCondition) ref hnonObject hsupportFree
          hsupportNormal htypeMem
      exact ⟨[], 0, by
        simp [Execution.executeSelectionSetAsResponse, Execution.selectionSetResultToResponse,
          Execution.executeSelectionSet, Execution.executeRootSelectionSet,
          hcollect, Execution.executeCollectedFields]⟩
  · intro hsemantic
    exact hchildNot (by
      simpa [leftSelectionSet, rightSelectionSet, hleftResponse,
        hrightResponse] using hsemantic)

end GroundTypeNormalization

end NormalForm

end GraphQL
