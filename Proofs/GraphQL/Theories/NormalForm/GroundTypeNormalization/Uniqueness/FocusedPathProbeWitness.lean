import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.FocusedPathProbeSelectedExecution

/-!
Final selected-path and path-local response-difference witness constructors.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

theorem
    selectedPathSelectionSetFieldChildrenReady_of_valid_normal_runtimeSpine_support_context_fuel_ge
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
          -> objectTypeNameBool schema normalParentType = true
          -> SelectedFieldSpineRuntimeValid schema normalParentType runtimeType spine
          -> PathLocalSupportValidNormal schema runtimeType currentSelectionSet
          -> PathLocalSelectionSetCurrentContext selectionSet currentSelectionSet
          -> SelectedPathSelectionSetFieldChildrenReady schema rootSelectionSet
              leftInitialSelectionSet rightInitialSelectionSet
              currentSelectionSet leftInitialSpine rightInitialSpine spine
              variableValues fuel targetParent leftField rightField
              normalParentType leftArguments rightArguments leftRuntime
              rightRuntime tag selectionSet := by
  intro hschema normalParentType variableDefinitions selectionSet fuel
    runtimeType targetParent leftField rightField leftArguments
    rightArguments leftRuntime rightRuntime tag currentSelectionSet spine
    hfuel hvalid hfree hnormal hobject hspineValid hsupport hcontext
  have hinclude :
      schema.typeIncludesObjectBool normalParentType runtimeType = true :=
    selectedFieldSpineRuntimeValid_typeIncludes hspineValid
  have hruntimeEq : runtimeType = normalParentType :=
    typeIncludesObjectBool_eq_of_objectTypeNameBool_true schema hobject
      hinclude
  subst runtimeType
  intro responseName fieldName arguments directives childSelectionSet hmem
  rcases selectionSetValid_field_lookup_of_mem hvalid hmem with
    ⟨fieldDefinition, hlookup, _harguments, _hfieldSelectionValid⟩
  have hleafFuel : leafProbeFuel fieldDefinition.outputType ≤ fuel := by
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
      (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool
        schema = false
  · exact Or.inl hreturnLeaf
  · have hreturnComposite :
        (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool
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
    have hchildFuel :
        selectionSetDeepProbeFuel schema
            fieldDefinition.outputType.namedType childSelectionSet
          ≤ childFuel := by
      dsimp [childFuel]
      omega
    have hchildSizeSelf :
        SelectionSet.size childSelectionSet <
          SelectionSet.size childSelectionSet + 1 := by
      omega
    have hchildFree : selectionSetDirectiveFree childSelectionSet :=
      selectionSetDirectiveFree_field_child_of_mem hfree hmem
    have hchildNormal :
        selectionSetNormal schema fieldDefinition.outputType.namedType
          childSelectionSet :=
      selectionSetNormal_field_child_of_mem_lookup hnormal hmem hlookup
    by_cases hreturnObject :
        objectTypeNameBool schema fieldDefinition.outputType.namedType =
          true
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
      have hallFields : selectionsAllFields childSelectionSet :=
        selectionSetNormal_allFields_of_object hchildNormal hreturnObject
      have hpruned :
          runtimePrunedSelectionSet schema
              fieldDefinition.outputType.namedType childSelectionSet =
            childSelectionSet :=
        runtimePrunedSelectionSet_eq_self_of_allFields schema
          fieldDefinition.outputType.namedType hallFields
      have hchildSupport :
          PathLocalSupportValidNormal schema
            fieldDefinition.outputType.namedType
            (fieldPairPathLocalNextSelectionSet schema normalParentType
              fieldDefinition.outputType.namedType fieldName arguments
              currentSelectionSet) :=
        hsupport.fieldPairPathLocalNextSelectionSet_of_object_output
          hobject hreturnObject hlookup rfl
      have hchildContext :
          PathLocalSelectionSetCurrentContext childSelectionSet
            (fieldPairPathLocalNextSelectionSet schema normalParentType
              fieldDefinition.outputType.namedType fieldName arguments
              currentSelectionSet) :=
        PathLocalSelectionSetCurrentContext.fieldPairPathLocalNextSelectionSet_field_child
          (schema := schema) (currentRuntimeType := normalParentType)
          (childRuntimeType := fieldDefinition.outputType.namedType)
          (targetField := fieldName) (responseName := responseName)
          (targetArguments := arguments) (arguments := arguments)
          (directives := directives) (selectionSet := selectionSet)
          (childSelectionSet := childSelectionSet)
          (currentSelectionSet := currentSelectionSet)
          hcontext hmem (argumentsEquivalent_refl_forSyntaxDiff arguments)
          hpruned
      have htailCase :=
        selectedFieldSpineRuntimeValid_tailForRuntime_of_objectOutput
          (arguments := arguments) hspineValid hobject hlookup
          hreturnObject
      rcases htailCase with htailNil | htailValid
      · rcases
          executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_nil_of_valid_normal_support_context_fuel_ge_size
            schema rootSelectionSet leftInitialSelectionSet
            rightInitialSelectionSet leftInitialSpine rightInitialSpine
            variableValues hschema (SelectionSet.size childSelectionSet + 1)
            fieldDefinition.outputType.namedType variableDefinitions
            childSelectionSet childFuel
            fieldDefinition.outputType.namedType targetParent leftField
            rightField leftArguments rightArguments leftRuntime
            rightRuntime tag
            (fieldPairPathLocalNextSelectionSet schema normalParentType
              fieldDefinition.outputType.namedType fieldName arguments
              currentSelectionSet)
            hchildSizeSelf hchildFuel hchildValid hchildFree hchildNormal
            hchildInclude hchildSupport (fun _hobject => hchildContext)
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
          executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_of_valid_normal_runtimeSpine_support_context_fuel_ge_size
            schema rootSelectionSet leftInitialSelectionSet
            rightInitialSelectionSet leftInitialSpine rightInitialSpine
            variableValues hschema (SelectionSet.size childSelectionSet + 1)
            fieldDefinition.outputType.namedType variableDefinitions
            childSelectionSet childFuel
            fieldDefinition.outputType.namedType targetParent leftField
            rightField leftArguments rightArguments leftRuntime
            rightRuntime tag
            (fieldPairPathLocalNextSelectionSet schema normalParentType
              fieldDefinition.outputType.namedType fieldName arguments
              currentSelectionSet)
            (selectedObservableFieldSpineTailForRuntime
              fieldDefinition.outputType.namedType fieldName arguments spine)
            hchildSizeSelf hchildFuel hchildValid hchildFree hchildNormal
            htailValid hchildSupport (fun _hobject => hchildContext)
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
          objectTypeNameBool schema fieldDefinition.outputType.namedType =
            false := by
        cases h :
            objectTypeNameBool schema
              fieldDefinition.outputType.namedType <;>
          simp [h] at hreturnObject ⊢
      have hchildNonempty : childSelectionSet ≠ [] := by
        rcases
            selectionSetValid_field_lookup_leaf_or_composite_child hvalid
              hmem with
          ⟨candidateDefinition, hcandidateLookup, hkind⟩
        have hdefinitionEq : candidateDefinition = fieldDefinition := by
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
      cases hselected : selectedObservableFieldSpineNext? fieldName arguments spine with
      | none =>
          have hready :
              PathLocalSelectionSetHeadReady schema normalParentType
                currentSelectionSet selectionSet :=
            PathLocalSelectionSetCurrentContext.headReady_of_valid_normal
              hsupport.sound hcontext hvalid hnormal
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
                  normalParentType childRuntimeType fieldName arguments
                  currentSelectionSet) :=
            hsupport.fieldPairPathLocalNextSelectionSet_of_abstract_output
              hobject hchildObject hlookup hreturnComposite hchildInclude
          rcases
              executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_nil_of_valid_normal_support_context_fuel_ge_size
                schema rootSelectionSet leftInitialSelectionSet
                rightInitialSelectionSet leftInitialSpine rightInitialSpine
                variableValues hschema
                (SelectionSet.size childSelectionSet + 1)
                fieldDefinition.outputType.namedType variableDefinitions
                childSelectionSet childFuel childRuntimeType targetParent
                leftField rightField leftArguments rightArguments
                leftRuntime rightRuntime tag
                (fieldPairPathLocalNextSelectionSet schema
                  normalParentType childRuntimeType fieldName arguments
                  currentSelectionSet)
                hchildSizeSelf hchildFuel hchildValid hchildFree
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
                  hspineValid hobject hlookup hreturnComposite hselected)
          | some selectedRuntime =>
              rcases
                  selectedFieldSpineRuntimeValid_child_of_selectedNext
                    hspineValid hobject hlookup hselected with
                ⟨hruntimeCase, hchildInclude, htailValid⟩
              have hchildObject :
                  objectTypeNameBool schema selectedRuntime = true :=
                selectedFieldSpineRuntimeValid_runtime_object htailValid
              have hchildSupport :
                  PathLocalSupportValidNormal schema selectedRuntime
                    (fieldPairPathLocalNextSelectionSet schema
                      normalParentType selectedRuntime fieldName arguments
                      currentSelectionSet) :=
                hsupport.fieldPairPathLocalNextSelectionSet_of_abstract_output
                  hobject hchildObject hlookup hreturnComposite
                  hchildInclude
              rcases
                  executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_of_valid_normal_runtimeSpine_support_context_fuel_ge_size
                    schema rootSelectionSet leftInitialSelectionSet
                    rightInitialSelectionSet leftInitialSpine
                    rightInitialSpine variableValues hschema
                    (SelectionSet.size childSelectionSet + 1)
                    fieldDefinition.outputType.namedType
                    variableDefinitions childSelectionSet childFuel
                    selectedRuntime targetParent leftField rightField
                    leftArguments rightArguments leftRuntime rightRuntime
                    tag
                    (fieldPairPathLocalNextSelectionSet schema
                      normalParentType selectedRuntime fieldName arguments
                      currentSelectionSet)
                    tail hchildSizeSelf hchildFuel hchildValid
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

theorem
    selectedPathTaggedSelectionSetResponseDiffWitness_of_object_leaf_field_valid_normal_runtimeSpine_support_context_fuel_ge
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ∀ parentType variableDefinitions (selectionSet : List Selection)
            fuel targetParent leftField rightField
            (leftArguments rightArguments : List Argument)
            (leftRuntime rightRuntime : Name)
            (currentSelectionSet : List Selection)
            (spine : List NormalSelectionSetObservableFieldStep)
            {responseName fieldName : Name} {arguments : List Argument}
            {directives : List DirectiveApplication}
            {childSelectionSet : List Selection}
            {fieldDefinition : FieldDefinition},
          Validation.selectionSetValid schema variableDefinitions parentType selectionSet
          -> selectionSetDirectiveFree selectionSet
          -> selectionSetNormal schema parentType selectionSet
          -> objectTypeNameBool schema parentType = true
          -> selectionSetDeepProbeFuel schema parentType selectionSet ≤ fuel
          -> SelectedFieldSpineRuntimeValid schema parentType parentType spine
          -> PathLocalSupportValidNormal schema parentType currentSelectionSet
          -> PathLocalSelectionSetCurrentContext selectionSet currentSelectionSet
          -> Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ selectionSet
          -> schema.lookupField parentType fieldName = some fieldDefinition
          -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
              = false
          -> SelectedPathTaggedSelectionSetResponseDiffWitness schema
              rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
              leftInitialSpine rightInitialSpine variableValues (fuel + 1)
              parentType parentType targetParent leftField rightField
              leftArguments rightArguments leftRuntime rightRuntime
              currentSelectionSet currentSelectionSet spine spine selectionSet := by
  intro hschema parentType variableDefinitions selectionSet fuel
    targetParent leftField rightField leftArguments rightArguments
    leftRuntime rightRuntime currentSelectionSet spine responseName fieldName
    arguments directives childSelectionSet fieldDefinition hvalid hfree
    hnormal hobject hfuel hspineValid hsupport hcontext hmem hlookup hleaf
  have hinclude :
      schema.typeIncludesObjectBool parentType parentType = true :=
    typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject
  have hsize :
      SelectionSet.size selectionSet < SelectionSet.size selectionSet + 1 :=
    by omega
  have hleftReady :
      SelectedPathSelectionSetFieldChildrenReady schema rootSelectionSet
        leftInitialSelectionSet rightInitialSelectionSet currentSelectionSet
        leftInitialSpine rightInitialSpine spine variableValues fuel
        targetParent leftField rightField parentType leftArguments
        rightArguments leftRuntime rightRuntime FieldPairProbeTag.left
        selectionSet :=
    selectedPathSelectionSetFieldChildrenReady_of_valid_normal_runtimeSpine_support_context_fuel_ge
      schema rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftInitialSpine rightInitialSpine variableValues hschema parentType
      variableDefinitions selectionSet fuel parentType targetParent
      leftField rightField leftArguments rightArguments leftRuntime
      rightRuntime FieldPairProbeTag.left currentSelectionSet spine hfuel
      hvalid hfree hnormal hobject hspineValid hsupport hcontext
  have hrightReady :
      SelectedPathSelectionSetFieldChildrenReady schema rootSelectionSet
        leftInitialSelectionSet rightInitialSelectionSet currentSelectionSet
        leftInitialSpine rightInitialSpine spine variableValues fuel
        targetParent leftField rightField parentType leftArguments
        rightArguments leftRuntime rightRuntime FieldPairProbeTag.right
        selectionSet :=
    selectedPathSelectionSetFieldChildrenReady_of_valid_normal_runtimeSpine_support_context_fuel_ge
      schema rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftInitialSpine rightInitialSpine variableValues hschema parentType
      variableDefinitions selectionSet fuel parentType targetParent
      leftField rightField leftArguments rightArguments leftRuntime
      rightRuntime FieldPairProbeTag.right currentSelectionSet spine hfuel
      hvalid hfree hnormal hobject hspineValid hsupport hcontext
  have hleftFieldOk :=
    executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_field_ok_of_selectedPathFieldChildrenReady
      schema rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      currentSelectionSet leftInitialSpine rightInitialSpine spine
      variableValues fuel targetParent leftField rightField parentType
      parentType leftArguments rightArguments leftRuntime rightRuntime
      FieldPairProbeTag.left selectionSet hleftReady
  have hrightFieldOk :=
    executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_field_ok_of_selectedPathFieldChildrenReady
      schema rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      currentSelectionSet leftInitialSpine rightInitialSpine spine
      variableValues fuel targetParent leftField rightField parentType
      parentType leftArguments rightArguments leftRuntime rightRuntime
      FieldPairProbeTag.right selectionSet hrightReady
  have hnotData :
      ¬ Execution.ResponseValue.semanticEquivalent
        (Execution.executeSelectionSetAsResponse schema
          (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
            (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
              rightInitialSelectionSet leftInitialSpine rightInitialSpine
              targetParent leftField rightField leftArguments rightArguments
              leftRuntime rightRuntime)
            targetParent leftField rightField leftArguments rightArguments)
          variableValues (fuel + 1) parentType
          (projectionTargetResolverValue
            (.object parentType
              (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
                currentSelectionSet spine)))
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
            (.object parentType
              (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                currentSelectionSet spine)))
          selectionSet).data :=
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_leaf_field_of_field_ok
      schema rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      currentSelectionSet currentSelectionSet leftInitialSpine
      rightInitialSpine spine spine variableValues fuel targetParent
      leftField rightField parentType parentType parentType leftArguments
      rightArguments leftRuntime rightRuntime hfree hnormal hobject hmem
      hlookup
      (by
        have hlocal :=
          leafProbeFuel_le_selectionSetDeepProbeFuel_of_field_mem schema
            parentType (selectionSet := selectionSet)
            (responseName := responseName) (fieldName := fieldName)
            (arguments := arguments) (directives := directives)
            (childSelectionSet := childSelectionSet)
            (fieldDefinition := fieldDefinition) hmem hlookup
        omega)
      hleaf hleftFieldOk hrightFieldOk
  rcases
      executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_of_valid_normal_runtimeSpine_support_context_fuel_ge_size
        schema rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
        leftInitialSpine rightInitialSpine variableValues hschema
        (SelectionSet.size selectionSet + 1) parentType
        variableDefinitions selectionSet fuel parentType targetParent
        leftField rightField leftArguments rightArguments leftRuntime
        rightRuntime FieldPairProbeTag.left currentSelectionSet spine
        hsize hfuel hvalid hfree hnormal hspineValid hsupport
        (fun _hobject => hcontext)
        (fun hnonObject => by
          rw [hobject] at hnonObject
          simp at hnonObject) with
    ⟨leftFields, leftErrors, hleftResponse⟩
  rcases
      executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_of_valid_normal_runtimeSpine_support_context_fuel_ge_size
        schema rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
        leftInitialSpine rightInitialSpine variableValues hschema
        (SelectionSet.size selectionSet + 1) parentType
        variableDefinitions selectionSet fuel parentType targetParent
        leftField rightField leftArguments rightArguments leftRuntime
        rightRuntime FieldPairProbeTag.right currentSelectionSet spine
        hsize hfuel hvalid hfree hnormal hspineValid hsupport
        (fun _hobject => hcontext)
        (fun hnonObject => by
          rw [hobject] at hnonObject
          simp at hnonObject) with
    ⟨rightFields, rightErrors, hrightResponse⟩
  refine ⟨
    hinclude,
    leftFields,
    leftErrors,
    rightFields,
    rightErrors,
    hleftResponse,
    hrightResponse,
    ?_
  ⟩
  intro hsemantic
  exact hnotData (by
    simpa [hleftResponse, hrightResponse] using hsemantic)

theorem
    selectedPathTaggedSelectionSetResponseDiffWitness_of_object_leaf_field_valid_normal_runtimeSpine_pair_support_context_fuel_ge
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ∀ parentType variableDefinitions (selectionSet : List Selection)
            fuel targetParent leftField rightField
            (leftArguments rightArguments : List Argument)
            (leftRuntime rightRuntime : Name)
            (leftCurrentSelectionSet rightCurrentSelectionSet : List Selection)
            (leftSpine rightSpine : List NormalSelectionSetObservableFieldStep)
            {responseName fieldName : Name} {arguments : List Argument}
            {directives : List DirectiveApplication}
            {childSelectionSet : List Selection}
            {fieldDefinition : FieldDefinition},
          Validation.selectionSetValid schema variableDefinitions parentType selectionSet
          -> selectionSetDirectiveFree selectionSet
          -> selectionSetNormal schema parentType selectionSet
          -> objectTypeNameBool schema parentType = true
          -> selectionSetDeepProbeFuel schema parentType selectionSet ≤ fuel
          -> SelectedFieldSpineRuntimeValid schema parentType parentType leftSpine
          -> SelectedFieldSpineRuntimeValid schema parentType parentType rightSpine
          -> PathLocalSupportValidNormal schema parentType leftCurrentSelectionSet
          -> PathLocalSupportValidNormal schema parentType rightCurrentSelectionSet
          -> PathLocalSelectionSetCurrentContext selectionSet leftCurrentSelectionSet
          -> PathLocalSelectionSetCurrentContext selectionSet rightCurrentSelectionSet
          -> Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ selectionSet
          -> schema.lookupField parentType fieldName = some fieldDefinition
          -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
              = false
          -> SelectedPathTaggedSelectionSetResponseDiffWitness schema
              rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
              leftInitialSpine rightInitialSpine variableValues (fuel + 1)
              parentType parentType targetParent leftField rightField
              leftArguments rightArguments leftRuntime rightRuntime
              leftCurrentSelectionSet rightCurrentSelectionSet leftSpine
              rightSpine selectionSet := by
  intro hschema parentType variableDefinitions selectionSet fuel
    targetParent leftField rightField leftArguments rightArguments
    leftRuntime rightRuntime leftCurrentSelectionSet
    rightCurrentSelectionSet leftSpine rightSpine responseName fieldName
    arguments directives childSelectionSet fieldDefinition hvalid hfree
    hnormal hobject hfuel hleftSpineValid hrightSpineValid hleftSupport
    hrightSupport hleftContext hrightContext hmem hlookup hleaf
  have hinclude :
      schema.typeIncludesObjectBool parentType parentType = true :=
    typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject
  have hsize :
      SelectionSet.size selectionSet < SelectionSet.size selectionSet + 1 :=
    by omega
  have hleftReady :
      SelectedPathSelectionSetFieldChildrenReady schema rootSelectionSet
        leftInitialSelectionSet rightInitialSelectionSet leftCurrentSelectionSet
        leftInitialSpine rightInitialSpine leftSpine variableValues fuel
        targetParent leftField rightField parentType leftArguments
        rightArguments leftRuntime rightRuntime FieldPairProbeTag.left
        selectionSet :=
    selectedPathSelectionSetFieldChildrenReady_of_valid_normal_runtimeSpine_support_context_fuel_ge
      schema rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftInitialSpine rightInitialSpine variableValues hschema parentType
      variableDefinitions selectionSet fuel parentType targetParent
      leftField rightField leftArguments rightArguments leftRuntime
      rightRuntime FieldPairProbeTag.left leftCurrentSelectionSet leftSpine
      hfuel hvalid hfree hnormal hobject hleftSpineValid hleftSupport
      hleftContext
  have hrightReady :
      SelectedPathSelectionSetFieldChildrenReady schema rootSelectionSet
        leftInitialSelectionSet rightInitialSelectionSet
        rightCurrentSelectionSet leftInitialSpine rightInitialSpine
        rightSpine variableValues fuel targetParent leftField rightField
        parentType leftArguments rightArguments leftRuntime rightRuntime
        FieldPairProbeTag.right selectionSet :=
    selectedPathSelectionSetFieldChildrenReady_of_valid_normal_runtimeSpine_support_context_fuel_ge
      schema rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftInitialSpine rightInitialSpine variableValues hschema parentType
      variableDefinitions selectionSet fuel parentType targetParent
      leftField rightField leftArguments rightArguments leftRuntime
      rightRuntime FieldPairProbeTag.right rightCurrentSelectionSet
      rightSpine hfuel hvalid hfree hnormal hobject hrightSpineValid
      hrightSupport hrightContext
  have hleftFieldOk :=
    executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_field_ok_of_selectedPathFieldChildrenReady
      schema rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet leftInitialSpine rightInitialSpine leftSpine
      variableValues fuel targetParent leftField rightField parentType
      parentType leftArguments rightArguments leftRuntime rightRuntime
      FieldPairProbeTag.left selectionSet hleftReady
  have hrightFieldOk :=
    executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_field_ok_of_selectedPathFieldChildrenReady
      schema rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      rightCurrentSelectionSet leftInitialSpine rightInitialSpine rightSpine
      variableValues fuel targetParent leftField rightField parentType
      parentType leftArguments rightArguments leftRuntime rightRuntime
      FieldPairProbeTag.right selectionSet hrightReady
  have hnotData :
      ¬ Execution.ResponseValue.semanticEquivalent
        (Execution.executeSelectionSetAsResponse schema
          (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
            (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
              rightInitialSelectionSet leftInitialSpine rightInitialSpine
              targetParent leftField rightField leftArguments rightArguments
              leftRuntime rightRuntime)
            targetParent leftField rightField leftArguments rightArguments)
          variableValues (fuel + 1) parentType
          (projectionTargetResolverValue
            (.object parentType
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
            (.object parentType
              (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                rightCurrentSelectionSet rightSpine)))
          selectionSet).data :=
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_leaf_field_of_field_ok
      schema rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet leftInitialSpine
      rightInitialSpine leftSpine rightSpine variableValues fuel
      targetParent leftField rightField parentType parentType parentType
      leftArguments rightArguments leftRuntime rightRuntime hfree hnormal
      hobject hmem hlookup
      (by
        have hlocal :=
          leafProbeFuel_le_selectionSetDeepProbeFuel_of_field_mem schema
            parentType (selectionSet := selectionSet)
            (responseName := responseName) (fieldName := fieldName)
            (arguments := arguments) (directives := directives)
            (childSelectionSet := childSelectionSet)
            (fieldDefinition := fieldDefinition) hmem hlookup
        omega)
      hleaf hleftFieldOk hrightFieldOk
  rcases
      executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_of_valid_normal_runtimeSpine_support_context_fuel_ge_size
        schema rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
        leftInitialSpine rightInitialSpine variableValues hschema
        (SelectionSet.size selectionSet + 1) parentType
        variableDefinitions selectionSet fuel parentType targetParent
        leftField rightField leftArguments rightArguments leftRuntime
        rightRuntime FieldPairProbeTag.left leftCurrentSelectionSet
        leftSpine hsize hfuel hvalid hfree hnormal hleftSpineValid
        hleftSupport (fun _hobject => hleftContext)
        (fun hnonObject => by
          rw [hobject] at hnonObject
          simp at hnonObject) with
    ⟨leftFields, leftErrors, hleftResponse⟩
  rcases
      executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_of_valid_normal_runtimeSpine_support_context_fuel_ge_size
        schema rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
        leftInitialSpine rightInitialSpine variableValues hschema
        (SelectionSet.size selectionSet + 1) parentType
        variableDefinitions selectionSet fuel parentType targetParent
        leftField rightField leftArguments rightArguments leftRuntime
        rightRuntime FieldPairProbeTag.right rightCurrentSelectionSet
        rightSpine hsize hfuel hvalid hfree hnormal hrightSpineValid
        hrightSupport (fun _hobject => hrightContext)
        (fun hnonObject => by
          rw [hobject] at hnonObject
          simp at hnonObject) with
    ⟨rightFields, rightErrors, hrightResponse⟩
  refine ⟨
    hinclude,
    leftFields,
    leftErrors,
    rightFields,
    rightErrors,
    hleftResponse,
    hrightResponse,
    ?_
  ⟩
  intro hsemantic
  exact hnotData (by
    simpa [hleftResponse, hrightResponse] using hsemantic)

theorem
    selectedPathTaggedSelectionSetResponseDiffWitness_of_object_child_field_valid_normal_runtimeSpine_support_context_fuel_ge
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ∀ parentType variableDefinitions (selectionSet : List Selection)
            fuel targetParent leftField rightField
            (leftArguments rightArguments : List Argument)
            (leftRuntime rightRuntime : Name)
            (leftCurrentSelectionSet rightCurrentSelectionSet : List Selection)
            (leftSpine rightSpine : List NormalSelectionSetObservableFieldStep)
            {responseName fieldName : Name} {arguments : List Argument}
            {directives : List DirectiveApplication}
            {childSelectionSet : List Selection}
            {fieldDefinition : FieldDefinition} {runtimeType : Name}
            {leftTail rightTail : List NormalSelectionSetObservableFieldStep},
          Validation.selectionSetValid schema variableDefinitions parentType selectionSet
          -> selectionSetDirectiveFree selectionSet
          -> selectionSetNormal schema parentType selectionSet
          -> objectTypeNameBool schema parentType = true
          -> selectionSetDeepProbeFuel schema parentType selectionSet ≤ fuel
          -> SelectedFieldSpineRuntimeValid schema parentType parentType leftSpine
          -> SelectedFieldSpineRuntimeValid schema parentType parentType rightSpine
          -> PathLocalSupportValidNormal schema parentType leftCurrentSelectionSet
          -> PathLocalSupportValidNormal schema parentType rightCurrentSelectionSet
          -> PathLocalSelectionSetCurrentContext selectionSet leftCurrentSelectionSet
          -> PathLocalSelectionSetCurrentContext selectionSet rightCurrentSelectionSet
          -> Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ selectionSet
          -> schema.lookupField parentType fieldName = some fieldDefinition
          -> selectedObservableFieldSpineNext? fieldName arguments leftSpine
              = some (some runtimeType, leftTail)
          -> selectedObservableFieldSpineNext? fieldName arguments rightSpine
              = some (some runtimeType, rightTail)
          -> SelectedPathTaggedSelectionSetResponseDiffWitness schema
              rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
              leftInitialSpine rightInitialSpine variableValues
              (fuel - leafProbeFuel fieldDefinition.outputType)
              fieldDefinition.outputType.namedType runtimeType targetParent
              leftField rightField leftArguments rightArguments leftRuntime
              rightRuntime
              (fieldPairPathLocalNextSelectionSet schema parentType runtimeType
                fieldName arguments leftCurrentSelectionSet)
              (fieldPairPathLocalNextSelectionSet schema parentType runtimeType
                fieldName arguments rightCurrentSelectionSet)
              leftTail rightTail childSelectionSet
          -> SelectedPathTaggedSelectionSetResponseDiffWitness schema
              rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
              leftInitialSpine rightInitialSpine variableValues (fuel + 1)
              parentType parentType targetParent leftField rightField
              leftArguments rightArguments leftRuntime rightRuntime
              leftCurrentSelectionSet rightCurrentSelectionSet leftSpine
              rightSpine selectionSet := by
  intro hschema parentType variableDefinitions selectionSet fuel
    targetParent leftField rightField leftArguments rightArguments
    leftRuntime rightRuntime leftCurrentSelectionSet
    rightCurrentSelectionSet leftSpine rightSpine responseName fieldName
    arguments directives childSelectionSet fieldDefinition runtimeType
    leftTail rightTail hvalid hfree hnormal hobject hfuel
    hleftSpineValid hrightSpineValid hleftSupport hrightSupport
    hleftContext hrightContext hmem hlookup hleftSelected hrightSelected
    hchildWitness
  have hinclude :
      schema.typeIncludesObjectBool parentType parentType = true :=
    typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject
  rcases
      selectedFieldSpineRuntimeValid_child_of_selectedNext
        hleftSpineValid hobject hlookup hleftSelected with
    ⟨hruntime, hchildInclude, _hleftTailValid⟩
  have hleafFuel :
      leafProbeFuel fieldDefinition.outputType ≤ fuel := by
    have hlocal :=
      leafProbeFuel_le_selectionSetDeepProbeFuel_of_field_mem schema
        parentType (selectionSet := selectionSet)
        (responseName := responseName) (fieldName := fieldName)
        (arguments := arguments) (directives := directives)
        (childSelectionSet := childSelectionSet)
        (fieldDefinition := fieldDefinition) hmem hlookup
    omega
  rcases
      executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_of_valid_normal_runtimeSpine_support_context_fuel_ge_size
        schema rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
        leftInitialSpine rightInitialSpine variableValues hschema
        (SelectionSet.size selectionSet + 1) parentType
        variableDefinitions selectionSet fuel parentType targetParent
        leftField rightField leftArguments rightArguments leftRuntime
        rightRuntime FieldPairProbeTag.left leftCurrentSelectionSet
        leftSpine (by omega) hfuel hvalid hfree hnormal
        hleftSpineValid hleftSupport
        (fun _hobject => hleftContext)
        (fun hparentNonObject => by
          rw [hobject] at hparentNonObject
          simp at hparentNonObject) with
    ⟨leftFields, leftErrors, hleftResponse⟩
  rcases
      executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_of_valid_normal_runtimeSpine_support_context_fuel_ge_size
        schema rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
        leftInitialSpine rightInitialSpine variableValues hschema
        (SelectionSet.size selectionSet + 1) parentType
        variableDefinitions selectionSet fuel parentType targetParent
        leftField rightField leftArguments rightArguments leftRuntime
        rightRuntime FieldPairProbeTag.right rightCurrentSelectionSet
        rightSpine (by omega) hfuel hvalid hfree hnormal
        hrightSpineValid hrightSupport
        (fun _hobject => hrightContext)
        (fun hparentNonObject => by
          rw [hobject] at hparentNonObject
          simp at hparentNonObject) with
    ⟨rightFields, rightErrors, hrightResponse⟩
  rcases hchildWitness with
    ⟨_hchildInclude, leftChildFields, leftChildErrors,
      rightChildFields, rightChildErrors, hleftChildResponse,
      hrightChildResponse, hchildNot⟩
  have hleftReady :
      SelectedPathSelectionSetFieldChildrenReady schema rootSelectionSet
        leftInitialSelectionSet rightInitialSelectionSet
        leftCurrentSelectionSet leftInitialSpine rightInitialSpine
        leftSpine variableValues fuel targetParent leftField rightField
        parentType leftArguments rightArguments leftRuntime rightRuntime
        FieldPairProbeTag.left selectionSet :=
    selectedPathSelectionSetFieldChildrenReady_of_valid_normal_runtimeSpine_support_context_fuel_ge
      schema rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftInitialSpine rightInitialSpine variableValues hschema parentType
      variableDefinitions selectionSet fuel parentType targetParent
      leftField rightField leftArguments rightArguments leftRuntime
      rightRuntime FieldPairProbeTag.left leftCurrentSelectionSet
      leftSpine hfuel hvalid hfree hnormal hobject hleftSpineValid
      hleftSupport hleftContext
  have hrightReady :
      SelectedPathSelectionSetFieldChildrenReady schema rootSelectionSet
        leftInitialSelectionSet rightInitialSelectionSet
        rightCurrentSelectionSet leftInitialSpine rightInitialSpine
        rightSpine variableValues fuel targetParent leftField
        rightField parentType leftArguments rightArguments leftRuntime
        rightRuntime FieldPairProbeTag.right selectionSet :=
    selectedPathSelectionSetFieldChildrenReady_of_valid_normal_runtimeSpine_support_context_fuel_ge
      schema rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftInitialSpine rightInitialSpine variableValues hschema parentType
      variableDefinitions selectionSet fuel parentType targetParent
      leftField rightField leftArguments rightArguments leftRuntime
      rightRuntime FieldPairProbeTag.right rightCurrentSelectionSet
      rightSpine hfuel hvalid hfree hnormal hobject hrightSpineValid
      hrightSupport hrightContext
  have hleftFieldOk :=
    executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_field_ok_of_selectedPathFieldChildrenReady
      schema rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet leftInitialSpine rightInitialSpine
      leftSpine variableValues fuel targetParent leftField rightField
      parentType parentType leftArguments rightArguments leftRuntime
      rightRuntime FieldPairProbeTag.left selectionSet hleftReady
  have hrightFieldOk :=
    executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_field_ok_of_selectedPathFieldChildrenReady
      schema rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      rightCurrentSelectionSet leftInitialSpine rightInitialSpine
      rightSpine variableValues fuel targetParent leftField rightField
      parentType parentType leftArguments rightArguments leftRuntime
      rightRuntime FieldPairProbeTag.right selectionSet hrightReady
  have hdataNot :
      ¬ Execution.ResponseValue.semanticEquivalent
        (Execution.executeSelectionSetAsResponse schema
          (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
            (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
              rightInitialSelectionSet leftInitialSpine rightInitialSpine
              targetParent leftField rightField leftArguments rightArguments
              leftRuntime rightRuntime)
            targetParent leftField rightField leftArguments rightArguments)
          variableValues (fuel + 1) parentType
          (projectionTargetResolverValue
            (.object parentType
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
            (.object parentType
              (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                rightCurrentSelectionSet rightSpine)))
          selectionSet).data :=
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_child_field_of_field_ok
      schema rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet leftInitialSpine
      rightInitialSpine leftSpine rightSpine leftTail rightTail
      variableValues fuel targetParent leftField rightField parentType
      parentType parentType leftArguments rightArguments leftRuntime
      rightRuntime hfree hnormal hobject hmem hlookup hleftSelected
      hrightSelected hruntime hchildInclude hleafFuel hleftChildResponse
      hrightChildResponse hchildNot hleftFieldOk hrightFieldOk
  refine ⟨
    hinclude,
    leftFields,
    leftErrors,
    rightFields,
    rightErrors,
    hleftResponse,
    hrightResponse,
    ?_
  ⟩
  intro hsemantic
  exact hdataNot (by
    simpa [hleftResponse, hrightResponse] using hsemantic)

theorem
    selectedPathTaggedSelectionSetResponseDiffWitness_of_abstract_inlineFragment_body_valid_normal_runtimeSpine_support_context_fuel_ge
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ∀ normalParentType variableDefinitions (selectionSet : List Selection)
            fuel runtimeType targetParent leftField rightField
            (leftArguments rightArguments : List Argument)
            (leftRuntime rightRuntime : Name)
            (leftCurrentSelectionSet rightCurrentSelectionSet : List Selection)
            (leftSpine rightSpine : List NormalSelectionSetObservableFieldStep)
            {directives : List DirectiveApplication}
            {bodySelectionSet : List Selection},
          Validation.selectionSetValid schema variableDefinitions normalParentType
            selectionSet
          -> selectionSetDirectiveFree selectionSet
          -> selectionSetNormal schema normalParentType selectionSet
          -> objectTypeNameBool schema normalParentType = false
          -> objectTypeNameBool schema runtimeType = true
          -> schema.typeIncludesObjectBool normalParentType runtimeType = true
          -> selectionSetDeepProbeFuel schema normalParentType selectionSet ≤ fuel
          -> SelectedFieldSpineRuntimeValid schema normalParentType runtimeType leftSpine
          -> SelectedFieldSpineRuntimeValid schema normalParentType runtimeType rightSpine
          -> PathLocalSupportValidNormal schema runtimeType leftCurrentSelectionSet
          -> PathLocalSupportValidNormal schema runtimeType rightCurrentSelectionSet
          -> (∀ {bodyDirectives bodySelectionSet},
                Selection.inlineFragment (some runtimeType) bodyDirectives
                    bodySelectionSet
                  ∈ selectionSet
                -> PathLocalSelectionSetCurrentContext bodySelectionSet
                    leftCurrentSelectionSet)
          -> (∀ {bodyDirectives bodySelectionSet},
                Selection.inlineFragment (some runtimeType) bodyDirectives
                    bodySelectionSet
                  ∈ selectionSet
                -> PathLocalSelectionSetCurrentContext bodySelectionSet
                    rightCurrentSelectionSet)
          -> Selection.inlineFragment (some runtimeType) directives bodySelectionSet
              ∈ selectionSet
          -> SelectedPathTaggedSelectionSetResponseDiffWitness schema
              rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
              leftInitialSpine rightInitialSpine variableValues (fuel + 1)
              runtimeType runtimeType targetParent leftField rightField
              leftArguments rightArguments leftRuntime rightRuntime
              leftCurrentSelectionSet rightCurrentSelectionSet leftSpine
              rightSpine bodySelectionSet
          -> SelectedPathTaggedSelectionSetResponseDiffWitness schema
              rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
              leftInitialSpine rightInitialSpine variableValues (fuel + 1)
              normalParentType runtimeType targetParent leftField rightField
              leftArguments rightArguments leftRuntime rightRuntime
              leftCurrentSelectionSet rightCurrentSelectionSet leftSpine
              rightSpine selectionSet := by
  intro hschema normalParentType variableDefinitions selectionSet fuel
    runtimeType targetParent leftField rightField leftArguments
    rightArguments leftRuntime rightRuntime leftCurrentSelectionSet
    rightCurrentSelectionSet leftSpine rightSpine directives
    bodySelectionSet hvalid hfree hnormal hnonObject hruntimeObject
    hinclude hfuel hleftSpineValid hrightSpineValid hleftSupport
    hrightSupport hleftAbstractContext hrightAbstractContext hinlineMem
    hbodyWitness
  rcases
      executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_of_valid_normal_runtimeSpine_support_context_fuel_ge_size
        schema rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
        leftInitialSpine rightInitialSpine variableValues hschema
        (SelectionSet.size selectionSet + 1) normalParentType
        variableDefinitions selectionSet fuel runtimeType targetParent
        leftField rightField leftArguments rightArguments leftRuntime
        rightRuntime FieldPairProbeTag.left leftCurrentSelectionSet
        leftSpine (by omega) hfuel hvalid hfree hnormal
        hleftSpineValid hleftSupport
        (fun hparentObject => by
          rw [hnonObject] at hparentObject
          simp at hparentObject)
        (fun _hnonObject {bodyDirectives} {bodySelectionSet} bodyMem =>
          hleftAbstractContext
            (bodyDirectives := bodyDirectives)
            (bodySelectionSet := bodySelectionSet) bodyMem) with
    ⟨leftFields, leftErrors, hleftResponse⟩
  rcases
      executeSelectionSetAsResponse_fieldPairOrDeepSuccess_selectedPathProbe_tagged_of_valid_normal_runtimeSpine_support_context_fuel_ge_size
        schema rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
        leftInitialSpine rightInitialSpine variableValues hschema
        (SelectionSet.size selectionSet + 1) normalParentType
        variableDefinitions selectionSet fuel runtimeType targetParent
        leftField rightField leftArguments rightArguments leftRuntime
        rightRuntime FieldPairProbeTag.right rightCurrentSelectionSet
        rightSpine (by omega) hfuel hvalid hfree hnormal
        hrightSpineValid hrightSupport
        (fun hparentObject => by
          rw [hnonObject] at hparentObject
          simp at hparentObject)
        (fun _hnonObject {bodyDirectives} {bodySelectionSet} bodyMem =>
          hrightAbstractContext
            (bodyDirectives := bodyDirectives)
            (bodySelectionSet := bodySelectionSet) bodyMem) with
    ⟨rightFields, rightErrors, hrightResponse⟩
  rcases hbodyWitness with
    ⟨_hbodyInclude, leftBodyFields, leftBodyErrors, rightBodyFields,
      rightBodyErrors, hleftBodyResponse, hrightBodyResponse, hbodyNot⟩
  have hbodyDataNot :
      ¬ Execution.ResponseValue.semanticEquivalent
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
          bodySelectionSet).data := by
    intro hsemantic
    exact hbodyNot
      (by simpa [hleftBodyResponse, hrightBodyResponse] using hsemantic)
  have hdirectives : directives = [] :=
    selectionSetDirectiveFree_inlineFragment_directives_nil_of_mem hfree
      hinlineMem
  subst directives
  rcases List.mem_iff_append.mp hinlineMem with
    ⟨pref, suffix, hselectionSet⟩
  subst selectionSet
  have hdataNot :
      ¬ Execution.ResponseValue.semanticEquivalent
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
          (pref ++ Selection.inlineFragment (some runtimeType) []
            bodySelectionSet :: suffix)).data
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
          (pref ++ Selection.inlineFragment (some runtimeType) []
            bodySelectionSet :: suffix)).data :=
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_selectedPathProbe_tagged_abstract_inlineFragment_body
      schema rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      leftCurrentSelectionSet rightCurrentSelectionSet leftInitialSpine
      rightInitialSpine leftSpine rightSpine variableValues fuel
      targetParent leftField rightField normalParentType runtimeType
      leftArguments rightArguments leftRuntime rightRuntime hnonObject
      hruntimeObject hfree hnormal hbodyDataNot
  refine ⟨
    hinclude,
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
    selectedPathTaggedSelectionSetResponseDiffWitness_of_observableFieldSpineAtSelectedRuntime_valid_normal_runtimeSpine_support_context_fuel_ge
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ∀ normalParentType runtimeType currentSelectionSet
            (selectionSet : List Selection)
            (fieldSpine : List NormalSelectionSetObservableFieldStep),
          PathLocalSelectionSetObservableFieldSpineAtSelectedRuntime schema
            normalParentType runtimeType currentSelectionSet selectionSet
            fieldSpine
          -> ∀ variableDefinitions fuel targetParent leftField rightField
                (leftArguments rightArguments : List Argument)
                (leftRuntime rightRuntime : Name),
              Validation.selectionSetValid schema variableDefinitions
                normalParentType selectionSet
              -> selectionSetDirectiveFree selectionSet
              -> selectionSetNormal schema normalParentType selectionSet
              -> schema.typeIncludesObjectBool normalParentType runtimeType = true
              -> selectionSetDeepProbeFuel schema normalParentType selectionSet ≤ fuel
              -> PathLocalSupportValidNormal schema runtimeType currentSelectionSet
              -> (objectTypeNameBool schema normalParentType = true
                  -> PathLocalSelectionSetCurrentContext selectionSet currentSelectionSet)
              -> (objectTypeNameBool schema normalParentType = false
                  -> ∀ {directives bodySelectionSet},
                      Selection.inlineFragment (some runtimeType) directives
                          bodySelectionSet
                        ∈ selectionSet
                      -> PathLocalSelectionSetCurrentContext bodySelectionSet
                          currentSelectionSet)
              -> SelectedPathTaggedSelectionSetResponseDiffWitness schema
                  rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
                  leftInitialSpine rightInitialSpine variableValues (fuel + 1)
                  normalParentType runtimeType targetParent leftField rightField
                  leftArguments rightArguments leftRuntime rightRuntime
                  currentSelectionSet currentSelectionSet fieldSpine fieldSpine
                  selectionSet := by
  intro hschema normalParentType runtimeType currentSelectionSet
    selectionSet fieldSpine hobservable
  induction hobservable with
  | objectLeaf hobject hmem hlookup hleaf =>
      rename_i parentName responseName fieldName arguments directives
        currentSelectionSet childSelectionSet selectionSet fieldDefinition
      intro variableDefinitions fuel targetParent leftField rightField
        leftArguments rightArguments leftRuntime rightRuntime hvalid hfree
        hnormal _hinclude hfuel hsupport hobjectContext _habstractContext
      have hspineValid :
          SelectedFieldSpineRuntimeValid schema parentName parentName
            [{ responseName := responseName, fieldName := fieldName,
               arguments := arguments, childRuntime := none }] :=
        SelectedFieldSpineRuntimeValid.objectLeaf hobject hlookup hleaf
      exact
        selectedPathTaggedSelectionSetResponseDiffWitness_of_object_leaf_field_valid_normal_runtimeSpine_support_context_fuel_ge
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet leftInitialSpine rightInitialSpine
          variableValues hschema parentName variableDefinitions
          selectionSet fuel targetParent leftField rightField
          leftArguments rightArguments leftRuntime rightRuntime
          currentSelectionSet
          [{ responseName := responseName, fieldName := fieldName,
             arguments := arguments, childRuntime := none }]
          hvalid hfree hnormal hobject hfuel hspineValid hsupport
          (hobjectContext hobject) hmem hlookup hleaf
  | objectChild hobject hmem hlookup hcomposite hchild ih =>
      rename_i parentName childRuntimeType responseName fieldName arguments
        directives currentSelectionSet childSelectionSet selectionSet
        fieldDefinition childSpine
      intro variableDefinitions fuel targetParent leftField rightField
        leftArguments rightArguments leftRuntime rightRuntime hvalid hfree
        hnormal _hinclude hfuel hsupport hobjectContext _habstractContext
      have hreturnComposite :
          (TypeRef.named
              fieldDefinition.outputType.namedType).isCompositeBool schema =
            true := hcomposite
      have hchildSpineValid :
          SelectedFieldSpineRuntimeValid schema
            fieldDefinition.outputType.namedType childRuntimeType
            childSpine :=
        selectedFieldSpineRuntimeValid_of_observableFieldSpineAtSelectedRuntime
          hchild
      have hparentSpineValid :
          SelectedFieldSpineRuntimeValid schema parentName parentName
            ({ responseName := responseName, fieldName := fieldName,
               arguments := arguments,
               childRuntime := some childRuntimeType } :: childSpine) :=
        SelectedFieldSpineRuntimeValid.objectChild hobject hlookup
          hreturnComposite hchildSpineValid
      have hselected :
          selectedObservableFieldSpineNext? fieldName arguments
              ({ responseName := responseName, fieldName := fieldName,
                 arguments := arguments,
                 childRuntime := some childRuntimeType } :: childSpine) =
            some (some childRuntimeType, childSpine) := by
        simp [selectedObservableFieldSpineNext?,
          argumentsEquivalent_refl_forSyntaxDiff]
      have hfieldDeepFuel :
          leafProbeFuel fieldDefinition.outputType
            + selectionSetDeepProbeFuel schema
              fieldDefinition.outputType.namedType childSelectionSet
            + 1 ≤ fuel := by
        have hlocal :=
          selectionSetDeepProbeFuel_field_mem schema parentName
            selectionSet responseName fieldName arguments directives
            childSelectionSet fieldDefinition hmem hlookup
        omega
      let childFuel :=
        fuel - leafProbeFuel fieldDefinition.outputType - 1
      have hchildFuel :
          selectionSetDeepProbeFuel schema
              fieldDefinition.outputType.namedType childSelectionSet
            ≤ childFuel := by
        dsimp [childFuel]
        omega
      have hchildFuelEq :
          childFuel + 1 =
            fuel - leafProbeFuel fieldDefinition.outputType := by
        dsimp [childFuel]
        omega
      have hchildFree :
          selectionSetDirectiveFree childSelectionSet :=
        selectionSetDirectiveFree_field_child_of_mem hfree hmem
      have hchildNormal :
          selectionSetNormal schema fieldDefinition.outputType.namedType
            childSelectionSet :=
        selectionSetNormal_field_child_of_mem_lookup hnormal hmem hlookup
      have hchildInclude :
          schema.typeIncludesObjectBool
              fieldDefinition.outputType.namedType childRuntimeType =
            true :=
        pathLocalSelectionSetObservableFieldSpineAtSelectedRuntime_typeIncludes
          hchild
      have hchildObject :
          objectTypeNameBool schema childRuntimeType = true :=
        pathLocalSelectionSetObservableFieldSpineAtSelectedRuntime_runtime_object
          hchild
      by_cases hreturnObject :
          objectTypeNameBool schema
              fieldDefinition.outputType.namedType = true
      · have hchildRuntimeEq :
            childRuntimeType = fieldDefinition.outputType.namedType :=
          typeIncludesObjectBool_eq_of_objectTypeNameBool_true schema
            hreturnObject hchildInclude
        subst childRuntimeType
        have hchildValid :
            Validation.selectionSetValid schema variableDefinitions
              fieldDefinition.outputType.namedType childSelectionSet :=
          selectionSetValid_object_field_child_of_mem_lookup hvalid hmem
            hlookup hreturnObject
        have hchildSupport :
            PathLocalSupportValidNormal schema
              fieldDefinition.outputType.namedType
              (fieldPairPathLocalNextSelectionSet schema parentName
                fieldDefinition.outputType.namedType fieldName arguments
                currentSelectionSet) :=
          hsupport.fieldPairPathLocalNextSelectionSet_of_object_output
            hobject hreturnObject hlookup rfl
        have hallFields : selectionsAllFields childSelectionSet :=
          selectionSetNormal_allFields_of_object hchildNormal
            hreturnObject
        have hpruned :
            runtimePrunedSelectionSet schema
                fieldDefinition.outputType.namedType childSelectionSet =
              childSelectionSet :=
          runtimePrunedSelectionSet_eq_self_of_allFields schema
            fieldDefinition.outputType.namedType hallFields
        have hchildContext :
            PathLocalSelectionSetCurrentContext childSelectionSet
              (fieldPairPathLocalNextSelectionSet schema parentName
                fieldDefinition.outputType.namedType fieldName arguments
                currentSelectionSet) :=
          PathLocalSelectionSetCurrentContext.fieldPairPathLocalNextSelectionSet_field_child
            (schema := schema) (currentRuntimeType := parentName)
            (childRuntimeType := fieldDefinition.outputType.namedType)
            (targetField := fieldName) (responseName := responseName)
            (targetArguments := arguments) (arguments := arguments)
            (directives := directives) (selectionSet := selectionSet)
            (childSelectionSet := childSelectionSet)
            (currentSelectionSet := currentSelectionSet)
            (hobjectContext hobject) hmem
            (argumentsEquivalent_refl_forSyntaxDiff arguments) hpruned
        have hchildWitness :
            SelectedPathTaggedSelectionSetResponseDiffWitness schema
              rootSelectionSet leftInitialSelectionSet
              rightInitialSelectionSet leftInitialSpine rightInitialSpine
              variableValues
              (fuel - leafProbeFuel fieldDefinition.outputType)
              fieldDefinition.outputType.namedType
              fieldDefinition.outputType.namedType targetParent leftField
              rightField leftArguments rightArguments leftRuntime
              rightRuntime
              (fieldPairPathLocalNextSelectionSet schema parentName
                fieldDefinition.outputType.namedType fieldName arguments
                currentSelectionSet)
              (fieldPairPathLocalNextSelectionSet schema parentName
                fieldDefinition.outputType.namedType fieldName arguments
                currentSelectionSet)
              childSpine childSpine childSelectionSet := by
          have hraw :=
            ih variableDefinitions childFuel targetParent leftField
              rightField leftArguments rightArguments leftRuntime
              rightRuntime hchildValid hchildFree hchildNormal
              (typeIncludesObjectBool_self_of_objectTypeNameBool schema
                hreturnObject)
              hchildFuel hchildSupport
              (fun _hobject => hchildContext)
              (fun hnonObject => by
                rw [hreturnObject] at hnonObject
                simp at hnonObject)
          simpa [hchildFuelEq] using hraw
        exact
          selectedPathTaggedSelectionSetResponseDiffWitness_of_object_child_field_valid_normal_runtimeSpine_support_context_fuel_ge
            schema rootSelectionSet leftInitialSelectionSet
            rightInitialSelectionSet leftInitialSpine rightInitialSpine
            variableValues hschema parentName variableDefinitions
            selectionSet fuel targetParent leftField rightField
            leftArguments rightArguments leftRuntime rightRuntime
            currentSelectionSet currentSelectionSet
            ({ responseName := responseName, fieldName := fieldName,
               arguments := arguments,
               childRuntime := some fieldDefinition.outputType.namedType } ::
              childSpine)
            ({ responseName := responseName, fieldName := fieldName,
               arguments := arguments,
               childRuntime := some fieldDefinition.outputType.namedType } ::
              childSpine)
            hvalid hfree hnormal hobject hfuel hparentSpineValid
            hparentSpineValid hsupport hsupport (hobjectContext hobject)
            (hobjectContext hobject) hmem hlookup
            (by simpa using hselected) (by simpa using hselected)
            hchildWitness
      · have hreturnNonObject :
            objectTypeNameBool schema
                fieldDefinition.outputType.namedType = false := by
          cases h :
              objectTypeNameBool schema
                fieldDefinition.outputType.namedType <;>
            simp [h] at hreturnObject ⊢
        have hchildNonempty : childSelectionSet ≠ [] :=
          selectionSet_nonempty_of_pathLocalSelectionSetObservableFieldSpineAtSelectedRuntime
            hchild
        have hchildValid :
            Validation.selectionSetValid schema variableDefinitions
              fieldDefinition.outputType.namedType childSelectionSet :=
          selectionSetValid_field_child_of_mem_lookup hvalid hmem
            hchildNonempty hlookup
        have hchildSupport :
            PathLocalSupportValidNormal schema childRuntimeType
              (fieldPairPathLocalNextSelectionSet schema parentName
                childRuntimeType fieldName arguments currentSelectionSet) :=
          hsupport.fieldPairPathLocalNextSelectionSet_of_abstract_output
            hobject hchildObject hlookup hreturnComposite hchildInclude
        have hchildWitness :
            SelectedPathTaggedSelectionSetResponseDiffWitness schema
              rootSelectionSet leftInitialSelectionSet
              rightInitialSelectionSet leftInitialSpine rightInitialSpine
              variableValues
              (fuel - leafProbeFuel fieldDefinition.outputType)
              fieldDefinition.outputType.namedType childRuntimeType
              targetParent leftField rightField leftArguments rightArguments
              leftRuntime rightRuntime
              (fieldPairPathLocalNextSelectionSet schema parentName
                childRuntimeType fieldName arguments currentSelectionSet)
              (fieldPairPathLocalNextSelectionSet schema parentName
                childRuntimeType fieldName arguments currentSelectionSet)
              childSpine childSpine childSelectionSet := by
          have hraw :=
            ih variableDefinitions childFuel targetParent leftField
              rightField leftArguments rightArguments leftRuntime
              rightRuntime hchildValid hchildFree hchildNormal
              hchildInclude hchildFuel hchildSupport
              (fun hchildParentObject => by
                rw [hreturnNonObject] at hchildParentObject
                simp at hchildParentObject)
              (by
                intro _hchildParentNonObject
                intro bodyDirectives bodySelectionSet hbodyMem
                exact
                  PathLocalSelectionSetCurrentContext.fieldPairPathLocalNextSelectionSet_inlineFragment_body
                    (schema := schema)
                    (currentRuntimeType := parentName)
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
                    (hobjectContext hobject) hmem hbodyMem
                    (argumentsEquivalent_refl_forSyntaxDiff arguments)
                    hchildNormal hchildObject)
          simpa [hchildFuelEq] using hraw
        exact
          selectedPathTaggedSelectionSetResponseDiffWitness_of_object_child_field_valid_normal_runtimeSpine_support_context_fuel_ge
            schema rootSelectionSet leftInitialSelectionSet
            rightInitialSelectionSet leftInitialSpine rightInitialSpine
            variableValues hschema parentName variableDefinitions
            selectionSet fuel targetParent leftField rightField
            leftArguments rightArguments leftRuntime rightRuntime
            currentSelectionSet currentSelectionSet
            ({ responseName := responseName, fieldName := fieldName,
               arguments := arguments,
               childRuntime := some childRuntimeType } :: childSpine)
            ({ responseName := responseName, fieldName := fieldName,
               arguments := arguments,
               childRuntime := some childRuntimeType } :: childSpine)
            hvalid hfree hnormal hobject hfuel hparentSpineValid
            hparentSpineValid hsupport hsupport (hobjectContext hobject)
            (hobjectContext hobject) hmem hlookup hselected hselected
            hchildWitness
  | abstractInlineFragment hnonObject hruntimeObject hinclude hmem hchild ih =>
      rename_i parentName runtimeName directives currentSelectionSet
        childSelectionSet selectionSet childSpine
      intro variableDefinitions fuel targetParent leftField rightField
        leftArguments rightArguments leftRuntime rightRuntime hvalid hfree
        hnormal _hinclude hfuel hsupport _hobjectContext habstractContext
      have hchildSpineValid :
          SelectedFieldSpineRuntimeValid schema runtimeName runtimeName
            childSpine :=
        selectedFieldSpineRuntimeValid_of_observableFieldSpineAtSelectedRuntime
          hchild
      have hparentSpineValid :
          SelectedFieldSpineRuntimeValid schema parentName runtimeName
            childSpine :=
        SelectedFieldSpineRuntimeValid.abstractRuntime hnonObject
          hruntimeObject hinclude hchildSpineValid
      have hdirectives : directives = [] :=
        selectionSetDirectiveFree_inlineFragment_directives_nil_of_mem hfree
          hmem
      subst directives
      have hbodyValid :
          Validation.selectionSetValid schema variableDefinitions
            runtimeName childSelectionSet :=
        selectionSetValid_inlineFragment_some_child_of_mem hvalid hmem
      have hbodyFree : selectionSetDirectiveFree childSelectionSet :=
        selectionSetDirectiveFree_inlineFragment_child_of_mem hfree hmem
      have hbodyNormal :
          selectionSetNormal schema runtimeName childSelectionSet :=
        (selectionSetNormal_inlineFragment_child_of_mem hnormal hmem).2
      have hbodyFuel :
          selectionSetDeepProbeFuel schema runtimeName childSelectionSet
            ≤ fuel := by
        have hlocal :=
          selectionSetDeepProbeFuel_inlineFragment_some_mem schema
            parentName selectionSet runtimeName
            ([] : List DirectiveApplication) childSelectionSet hmem
        omega
      have hbodyInclude :
          schema.typeIncludesObjectBool runtimeName runtimeName = true :=
        typeIncludesObjectBool_self_of_objectTypeNameBool schema
          hruntimeObject
      have hbodyContext :
          PathLocalSelectionSetCurrentContext childSelectionSet
            currentSelectionSet :=
        habstractContext hnonObject hmem
      have hbodyWitness :
          SelectedPathTaggedSelectionSetResponseDiffWitness schema
            rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
            leftInitialSpine rightInitialSpine variableValues (fuel + 1)
            runtimeName runtimeName targetParent leftField rightField
            leftArguments rightArguments leftRuntime rightRuntime
            currentSelectionSet currentSelectionSet childSpine childSpine
            childSelectionSet :=
        ih variableDefinitions fuel targetParent leftField rightField
          leftArguments rightArguments leftRuntime rightRuntime hbodyValid
          hbodyFree hbodyNormal hbodyInclude hbodyFuel hsupport
          (fun _hobject => hbodyContext)
          (fun hbodyNonObject => by
            rw [hruntimeObject] at hbodyNonObject
            simp at hbodyNonObject)
      exact
        selectedPathTaggedSelectionSetResponseDiffWitness_of_abstract_inlineFragment_body_valid_normal_runtimeSpine_support_context_fuel_ge
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet leftInitialSpine rightInitialSpine
          variableValues hschema parentName variableDefinitions
          selectionSet fuel runtimeName targetParent leftField rightField
          leftArguments rightArguments leftRuntime rightRuntime
          currentSelectionSet currentSelectionSet childSpine childSpine
          hvalid hfree hnormal hnonObject hruntimeObject hinclude hfuel
          hparentSpineValid hparentSpineValid hsupport hsupport
          (fun {bodyDirectives} {bodySelectionSet} bodyMem =>
            habstractContext hnonObject
              (directives := bodyDirectives)
              (bodySelectionSet := bodySelectionSet) bodyMem)
          (fun {bodyDirectives} {bodySelectionSet} bodyMem =>
            habstractContext hnonObject
              (directives := bodyDirectives)
              (bodySelectionSet := bodySelectionSet) bodyMem)
          hmem hbodyWitness

theorem
    selectedPathTaggedSelectionSetResponseDiffWitness_of_observableFieldSpineAtSelectedRuntime_valid_normal_runtimeSpine_pair_support_context_fuel_ge
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ∀ normalParentType runtimeType leftCurrentSelectionSet
            rightCurrentSelectionSet (selectionSet : List Selection)
            (fieldSpine : List NormalSelectionSetObservableFieldStep),
          PathLocalSelectionSetObservableFieldSpineAtSelectedRuntime schema
            normalParentType runtimeType leftCurrentSelectionSet selectionSet
            fieldSpine
          -> ∀ variableDefinitions fuel targetParent leftField rightField
                (leftArguments rightArguments : List Argument)
                (leftRuntime rightRuntime : Name),
              Validation.selectionSetValid schema variableDefinitions
                normalParentType selectionSet
              -> selectionSetDirectiveFree selectionSet
              -> selectionSetNormal schema normalParentType selectionSet
              -> schema.typeIncludesObjectBool normalParentType runtimeType = true
              -> selectionSetDeepProbeFuel schema normalParentType selectionSet ≤ fuel
              -> PathLocalSupportValidNormal schema runtimeType leftCurrentSelectionSet
              -> PathLocalSupportValidNormal schema runtimeType rightCurrentSelectionSet
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
              -> SelectedPathTaggedSelectionSetResponseDiffWitness schema
                  rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
                  leftInitialSpine rightInitialSpine variableValues (fuel + 1)
                  normalParentType runtimeType targetParent leftField rightField
                  leftArguments rightArguments leftRuntime rightRuntime
                  leftCurrentSelectionSet rightCurrentSelectionSet fieldSpine
                  fieldSpine selectionSet := by
  intro hschema normalParentType runtimeType leftCurrentSelectionSet
    rightCurrentSelectionSet selectionSet fieldSpine hobservable
  induction hobservable generalizing rightCurrentSelectionSet with
  | objectLeaf hobject hmem hlookup hleaf =>
      rename_i parentName responseName fieldName arguments directives
        leftCurrentSelectionSet childSelectionSet selectionSet
        fieldDefinition
      intro variableDefinitions fuel targetParent leftField rightField
        leftArguments rightArguments leftRuntime rightRuntime hvalid hfree
        hnormal _hinclude hfuel hleftSupport hrightSupport
        hleftObjectContext hrightObjectContext _hleftAbstractContext
        _hrightAbstractContext
      have hspineValid :
          SelectedFieldSpineRuntimeValid schema parentName parentName
            [{ responseName := responseName, fieldName := fieldName,
               arguments := arguments, childRuntime := none }] :=
        SelectedFieldSpineRuntimeValid.objectLeaf hobject hlookup hleaf
      exact
        selectedPathTaggedSelectionSetResponseDiffWitness_of_object_leaf_field_valid_normal_runtimeSpine_pair_support_context_fuel_ge
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet leftInitialSpine rightInitialSpine
          variableValues hschema parentName variableDefinitions
          selectionSet fuel targetParent leftField rightField
          leftArguments rightArguments leftRuntime rightRuntime
          leftCurrentSelectionSet rightCurrentSelectionSet
          [{ responseName := responseName, fieldName := fieldName,
             arguments := arguments, childRuntime := none }]
          [{ responseName := responseName, fieldName := fieldName,
             arguments := arguments, childRuntime := none }]
          hvalid hfree hnormal hobject hfuel hspineValid hspineValid
          hleftSupport hrightSupport (hleftObjectContext hobject)
          (hrightObjectContext hobject) hmem hlookup hleaf
  | objectChild hobject hmem hlookup hcomposite hchild ih =>
      rename_i parentName childRuntimeType responseName fieldName arguments
        directives leftCurrentSelectionSet childSelectionSet selectionSet
        fieldDefinition childSpine
      intro variableDefinitions fuel targetParent leftField rightField
        leftArguments rightArguments leftRuntime rightRuntime hvalid hfree
        hnormal _hinclude hfuel hleftSupport hrightSupport
        hleftObjectContext hrightObjectContext _hleftAbstractContext
        _hrightAbstractContext
      have hreturnComposite :
          (TypeRef.named
              fieldDefinition.outputType.namedType).isCompositeBool schema =
            true := hcomposite
      have hchildSpineValid :
          SelectedFieldSpineRuntimeValid schema
            fieldDefinition.outputType.namedType childRuntimeType
            childSpine :=
        selectedFieldSpineRuntimeValid_of_observableFieldSpineAtSelectedRuntime
          hchild
      have hparentSpineValid :
          SelectedFieldSpineRuntimeValid schema parentName parentName
            ({ responseName := responseName, fieldName := fieldName,
               arguments := arguments,
               childRuntime := some childRuntimeType } :: childSpine) :=
        SelectedFieldSpineRuntimeValid.objectChild hobject hlookup
          hreturnComposite hchildSpineValid
      have hselected :
          selectedObservableFieldSpineNext? fieldName arguments
              ({ responseName := responseName, fieldName := fieldName,
                 arguments := arguments,
                 childRuntime := some childRuntimeType } :: childSpine) =
            some (some childRuntimeType, childSpine) := by
        simp [selectedObservableFieldSpineNext?,
          argumentsEquivalent_refl_forSyntaxDiff]
      have hfieldDeepFuel :
          leafProbeFuel fieldDefinition.outputType
            + selectionSetDeepProbeFuel schema
              fieldDefinition.outputType.namedType childSelectionSet
            + 1 ≤ fuel := by
        have hlocal :=
          selectionSetDeepProbeFuel_field_mem schema parentName
            selectionSet responseName fieldName arguments directives
            childSelectionSet fieldDefinition hmem hlookup
        omega
      let childFuel :=
        fuel - leafProbeFuel fieldDefinition.outputType - 1
      have hchildFuel :
          selectionSetDeepProbeFuel schema
              fieldDefinition.outputType.namedType childSelectionSet
            ≤ childFuel := by
        dsimp [childFuel]
        omega
      have hchildFuelEq :
          childFuel + 1 =
            fuel - leafProbeFuel fieldDefinition.outputType := by
        dsimp [childFuel]
        omega
      have hchildFree :
          selectionSetDirectiveFree childSelectionSet :=
        selectionSetDirectiveFree_field_child_of_mem hfree hmem
      have hchildNormal :
          selectionSetNormal schema fieldDefinition.outputType.namedType
            childSelectionSet :=
        selectionSetNormal_field_child_of_mem_lookup hnormal hmem hlookup
      have hchildInclude :
          schema.typeIncludesObjectBool
              fieldDefinition.outputType.namedType childRuntimeType =
            true :=
        pathLocalSelectionSetObservableFieldSpineAtSelectedRuntime_typeIncludes
          hchild
      have hchildObject :
          objectTypeNameBool schema childRuntimeType = true :=
        pathLocalSelectionSetObservableFieldSpineAtSelectedRuntime_runtime_object
          hchild
      by_cases hreturnObject :
          objectTypeNameBool schema
              fieldDefinition.outputType.namedType = true
      · have hchildRuntimeEq :
            childRuntimeType = fieldDefinition.outputType.namedType :=
          typeIncludesObjectBool_eq_of_objectTypeNameBool_true schema
            hreturnObject hchildInclude
        subst childRuntimeType
        have hchildValid :
            Validation.selectionSetValid schema variableDefinitions
              fieldDefinition.outputType.namedType childSelectionSet :=
          selectionSetValid_object_field_child_of_mem_lookup hvalid hmem
            hlookup hreturnObject
        have hleftChildSupport :
            PathLocalSupportValidNormal schema
              fieldDefinition.outputType.namedType
              (fieldPairPathLocalNextSelectionSet schema parentName
                fieldDefinition.outputType.namedType fieldName arguments
                leftCurrentSelectionSet) :=
          hleftSupport.fieldPairPathLocalNextSelectionSet_of_object_output
            hobject hreturnObject hlookup rfl
        have hrightChildSupport :
            PathLocalSupportValidNormal schema
              fieldDefinition.outputType.namedType
              (fieldPairPathLocalNextSelectionSet schema parentName
                fieldDefinition.outputType.namedType fieldName arguments
                rightCurrentSelectionSet) :=
          hrightSupport.fieldPairPathLocalNextSelectionSet_of_object_output
            hobject hreturnObject hlookup rfl
        have hallFields : selectionsAllFields childSelectionSet :=
          selectionSetNormal_allFields_of_object hchildNormal hreturnObject
        have hpruned :
            runtimePrunedSelectionSet schema
                fieldDefinition.outputType.namedType childSelectionSet =
              childSelectionSet :=
          runtimePrunedSelectionSet_eq_self_of_allFields schema
            fieldDefinition.outputType.namedType hallFields
        have hleftChildContext :
            PathLocalSelectionSetCurrentContext childSelectionSet
              (fieldPairPathLocalNextSelectionSet schema parentName
                fieldDefinition.outputType.namedType fieldName arguments
                leftCurrentSelectionSet) :=
          PathLocalSelectionSetCurrentContext.fieldPairPathLocalNextSelectionSet_field_child
            (schema := schema) (currentRuntimeType := parentName)
            (childRuntimeType := fieldDefinition.outputType.namedType)
            (targetField := fieldName) (responseName := responseName)
            (targetArguments := arguments) (arguments := arguments)
            (directives := directives) (selectionSet := selectionSet)
            (childSelectionSet := childSelectionSet)
            (currentSelectionSet := leftCurrentSelectionSet)
            (hleftObjectContext hobject) hmem
            (argumentsEquivalent_refl_forSyntaxDiff arguments) hpruned
        have hrightChildContext :
            PathLocalSelectionSetCurrentContext childSelectionSet
              (fieldPairPathLocalNextSelectionSet schema parentName
                fieldDefinition.outputType.namedType fieldName arguments
                rightCurrentSelectionSet) :=
          PathLocalSelectionSetCurrentContext.fieldPairPathLocalNextSelectionSet_field_child
            (schema := schema) (currentRuntimeType := parentName)
            (childRuntimeType := fieldDefinition.outputType.namedType)
            (targetField := fieldName) (responseName := responseName)
            (targetArguments := arguments) (arguments := arguments)
            (directives := directives) (selectionSet := selectionSet)
            (childSelectionSet := childSelectionSet)
            (currentSelectionSet := rightCurrentSelectionSet)
            (hrightObjectContext hobject) hmem
            (argumentsEquivalent_refl_forSyntaxDiff arguments) hpruned
        have hchildWitness :
            SelectedPathTaggedSelectionSetResponseDiffWitness schema
              rootSelectionSet leftInitialSelectionSet
              rightInitialSelectionSet leftInitialSpine rightInitialSpine
              variableValues
              (fuel - leafProbeFuel fieldDefinition.outputType)
              fieldDefinition.outputType.namedType
              fieldDefinition.outputType.namedType targetParent leftField
              rightField leftArguments rightArguments leftRuntime
              rightRuntime
              (fieldPairPathLocalNextSelectionSet schema parentName
                fieldDefinition.outputType.namedType fieldName arguments
                leftCurrentSelectionSet)
              (fieldPairPathLocalNextSelectionSet schema parentName
                fieldDefinition.outputType.namedType fieldName arguments
                rightCurrentSelectionSet)
              childSpine childSpine childSelectionSet := by
          have hraw :=
            ih
              (rightCurrentSelectionSet :=
                fieldPairPathLocalNextSelectionSet schema parentName
                  fieldDefinition.outputType.namedType fieldName arguments
                  rightCurrentSelectionSet)
              variableDefinitions childFuel targetParent leftField
              rightField leftArguments rightArguments leftRuntime
              rightRuntime hchildValid hchildFree hchildNormal
              (typeIncludesObjectBool_self_of_objectTypeNameBool schema
                hreturnObject)
              hchildFuel hleftChildSupport hrightChildSupport
              (fun _hobject => hleftChildContext)
              (fun _hobject => hrightChildContext)
              (fun hnonObject => by
                rw [hreturnObject] at hnonObject
                simp at hnonObject)
              (fun hnonObject => by
                rw [hreturnObject] at hnonObject
                simp at hnonObject)
          simpa [hchildFuelEq] using hraw
        exact
          selectedPathTaggedSelectionSetResponseDiffWitness_of_object_child_field_valid_normal_runtimeSpine_support_context_fuel_ge
            schema rootSelectionSet leftInitialSelectionSet
            rightInitialSelectionSet leftInitialSpine rightInitialSpine
            variableValues hschema parentName variableDefinitions
            selectionSet fuel targetParent leftField rightField
            leftArguments rightArguments leftRuntime rightRuntime
            leftCurrentSelectionSet rightCurrentSelectionSet
            ({ responseName := responseName, fieldName := fieldName,
               arguments := arguments,
               childRuntime := some fieldDefinition.outputType.namedType } ::
              childSpine)
            ({ responseName := responseName, fieldName := fieldName,
               arguments := arguments,
               childRuntime := some fieldDefinition.outputType.namedType } ::
              childSpine)
            hvalid hfree hnormal hobject hfuel hparentSpineValid
            hparentSpineValid hleftSupport hrightSupport
            (hleftObjectContext hobject) (hrightObjectContext hobject)
            hmem hlookup (by simpa using hselected)
            (by simpa using hselected) hchildWitness
      · have hreturnNonObject :
            objectTypeNameBool schema
                fieldDefinition.outputType.namedType = false := by
          cases h :
              objectTypeNameBool schema
                fieldDefinition.outputType.namedType <;>
            simp [h] at hreturnObject ⊢
        have hchildNonempty : childSelectionSet ≠ [] :=
          selectionSet_nonempty_of_pathLocalSelectionSetObservableFieldSpineAtSelectedRuntime
            hchild
        have hchildValid :
            Validation.selectionSetValid schema variableDefinitions
              fieldDefinition.outputType.namedType childSelectionSet :=
          selectionSetValid_field_child_of_mem_lookup hvalid hmem
            hchildNonempty hlookup
        have hleftChildSupport :
            PathLocalSupportValidNormal schema childRuntimeType
              (fieldPairPathLocalNextSelectionSet schema parentName
                childRuntimeType fieldName arguments leftCurrentSelectionSet) :=
          hleftSupport.fieldPairPathLocalNextSelectionSet_of_abstract_output
            hobject hchildObject hlookup hreturnComposite hchildInclude
        have hrightChildSupport :
            PathLocalSupportValidNormal schema childRuntimeType
              (fieldPairPathLocalNextSelectionSet schema parentName
                childRuntimeType fieldName arguments rightCurrentSelectionSet) :=
          hrightSupport.fieldPairPathLocalNextSelectionSet_of_abstract_output
            hobject hchildObject hlookup hreturnComposite hchildInclude
        have hchildWitness :
            SelectedPathTaggedSelectionSetResponseDiffWitness schema
              rootSelectionSet leftInitialSelectionSet
              rightInitialSelectionSet leftInitialSpine rightInitialSpine
              variableValues
              (fuel - leafProbeFuel fieldDefinition.outputType)
              fieldDefinition.outputType.namedType childRuntimeType
              targetParent leftField rightField leftArguments rightArguments
              leftRuntime rightRuntime
              (fieldPairPathLocalNextSelectionSet schema parentName
                childRuntimeType fieldName arguments leftCurrentSelectionSet)
              (fieldPairPathLocalNextSelectionSet schema parentName
                childRuntimeType fieldName arguments rightCurrentSelectionSet)
              childSpine childSpine childSelectionSet := by
          have hraw :=
            ih
              (rightCurrentSelectionSet :=
                fieldPairPathLocalNextSelectionSet schema parentName
                  childRuntimeType fieldName arguments
                  rightCurrentSelectionSet)
              variableDefinitions childFuel targetParent leftField
              rightField leftArguments rightArguments leftRuntime
              rightRuntime hchildValid hchildFree hchildNormal
              hchildInclude hchildFuel hleftChildSupport
              hrightChildSupport
              (fun hchildParentObject => by
                rw [hreturnNonObject] at hchildParentObject
                simp at hchildParentObject)
              (fun hchildParentObject => by
                rw [hreturnNonObject] at hchildParentObject
                simp at hchildParentObject)
              (by
                intro _hchildParentNonObject
                intro bodyDirectives bodySelectionSet hbodyMem
                exact
                  PathLocalSelectionSetCurrentContext.fieldPairPathLocalNextSelectionSet_inlineFragment_body
                    (schema := schema)
                    (currentRuntimeType := parentName)
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
                    (currentSelectionSet := leftCurrentSelectionSet)
                    (hleftObjectContext hobject) hmem hbodyMem
                    (argumentsEquivalent_refl_forSyntaxDiff arguments)
                    hchildNormal hchildObject)
              (by
                intro _hchildParentNonObject
                intro bodyDirectives bodySelectionSet hbodyMem
                exact
                  PathLocalSelectionSetCurrentContext.fieldPairPathLocalNextSelectionSet_inlineFragment_body
                    (schema := schema)
                    (currentRuntimeType := parentName)
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
                    (currentSelectionSet := rightCurrentSelectionSet)
                    (hrightObjectContext hobject) hmem hbodyMem
                    (argumentsEquivalent_refl_forSyntaxDiff arguments)
                    hchildNormal hchildObject)
          simpa [hchildFuelEq] using hraw
        exact
          selectedPathTaggedSelectionSetResponseDiffWitness_of_object_child_field_valid_normal_runtimeSpine_support_context_fuel_ge
            schema rootSelectionSet leftInitialSelectionSet
            rightInitialSelectionSet leftInitialSpine rightInitialSpine
            variableValues hschema parentName variableDefinitions
            selectionSet fuel targetParent leftField rightField
            leftArguments rightArguments leftRuntime rightRuntime
            leftCurrentSelectionSet rightCurrentSelectionSet
            ({ responseName := responseName, fieldName := fieldName,
               arguments := arguments,
               childRuntime := some childRuntimeType } :: childSpine)
            ({ responseName := responseName, fieldName := fieldName,
               arguments := arguments,
               childRuntime := some childRuntimeType } :: childSpine)
            hvalid hfree hnormal hobject hfuel hparentSpineValid
            hparentSpineValid hleftSupport hrightSupport
            (hleftObjectContext hobject) (hrightObjectContext hobject)
            hmem hlookup hselected hselected hchildWitness
  | abstractInlineFragment hnonObject hruntimeObject hinclude hmem hchild ih =>
      rename_i parentName runtimeName directives leftCurrentSelectionSet
        childSelectionSet selectionSet childSpine
      intro variableDefinitions fuel targetParent leftField rightField
        leftArguments rightArguments leftRuntime rightRuntime hvalid hfree
        hnormal _hinclude hfuel hleftSupport hrightSupport
        _hleftObjectContext _hrightObjectContext hleftAbstractContext
        hrightAbstractContext
      have hchildSpineValid :
          SelectedFieldSpineRuntimeValid schema runtimeName runtimeName
            childSpine :=
        selectedFieldSpineRuntimeValid_of_observableFieldSpineAtSelectedRuntime
          hchild
      have hparentSpineValid :
          SelectedFieldSpineRuntimeValid schema parentName runtimeName
            childSpine :=
        SelectedFieldSpineRuntimeValid.abstractRuntime hnonObject
          hruntimeObject hinclude hchildSpineValid
      have hdirectives : directives = [] :=
        selectionSetDirectiveFree_inlineFragment_directives_nil_of_mem hfree
          hmem
      subst directives
      have hbodyValid :
          Validation.selectionSetValid schema variableDefinitions
            runtimeName childSelectionSet :=
        selectionSetValid_inlineFragment_some_child_of_mem hvalid hmem
      have hbodyFree : selectionSetDirectiveFree childSelectionSet :=
        selectionSetDirectiveFree_inlineFragment_child_of_mem hfree hmem
      have hbodyNormal :
          selectionSetNormal schema runtimeName childSelectionSet :=
        (selectionSetNormal_inlineFragment_child_of_mem hnormal hmem).2
      have hbodyFuel :
          selectionSetDeepProbeFuel schema runtimeName childSelectionSet
            ≤ fuel := by
        have hlocal :=
          selectionSetDeepProbeFuel_inlineFragment_some_mem schema
            parentName selectionSet runtimeName
            ([] : List DirectiveApplication) childSelectionSet hmem
        omega
      have hbodyInclude :
          schema.typeIncludesObjectBool runtimeName runtimeName = true :=
        typeIncludesObjectBool_self_of_objectTypeNameBool schema
          hruntimeObject
      have hleftBodyContext :
          PathLocalSelectionSetCurrentContext childSelectionSet
            leftCurrentSelectionSet :=
        hleftAbstractContext hnonObject hmem
      have hrightBodyContext :
          PathLocalSelectionSetCurrentContext childSelectionSet
            rightCurrentSelectionSet :=
        hrightAbstractContext hnonObject hmem
      have hbodyWitness :
          SelectedPathTaggedSelectionSetResponseDiffWitness schema
            rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
            leftInitialSpine rightInitialSpine variableValues (fuel + 1)
            runtimeName runtimeName targetParent leftField rightField
            leftArguments rightArguments leftRuntime rightRuntime
            leftCurrentSelectionSet rightCurrentSelectionSet childSpine
            childSpine childSelectionSet :=
        ih
          (rightCurrentSelectionSet := rightCurrentSelectionSet)
          variableDefinitions fuel targetParent leftField rightField
          leftArguments rightArguments leftRuntime rightRuntime hbodyValid
          hbodyFree hbodyNormal hbodyInclude hbodyFuel hleftSupport
          hrightSupport (fun _hobject => hleftBodyContext)
          (fun _hobject => hrightBodyContext)
          (fun hbodyNonObject => by
            rw [hruntimeObject] at hbodyNonObject
            simp at hbodyNonObject)
          (fun hbodyNonObject => by
            rw [hruntimeObject] at hbodyNonObject
            simp at hbodyNonObject)
      exact
        selectedPathTaggedSelectionSetResponseDiffWitness_of_abstract_inlineFragment_body_valid_normal_runtimeSpine_support_context_fuel_ge
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet leftInitialSpine rightInitialSpine
          variableValues hschema parentName variableDefinitions
          selectionSet fuel runtimeName targetParent leftField rightField
          leftArguments rightArguments leftRuntime rightRuntime
          leftCurrentSelectionSet rightCurrentSelectionSet childSpine
          childSpine hvalid hfree hnormal hnonObject hruntimeObject hinclude
          hfuel hparentSpineValid hparentSpineValid hleftSupport
          hrightSupport
          (fun {bodyDirectives} {bodySelectionSet} bodyMem =>
            hleftAbstractContext hnonObject
              (directives := bodyDirectives)
              (bodySelectionSet := bodySelectionSet) bodyMem)
          (fun {bodyDirectives} {bodySelectionSet} bodyMem =>
            hrightAbstractContext hnonObject
              (directives := bodyDirectives)
              (bodySelectionSet := bodySelectionSet) bodyMem)
          hmem hbodyWitness

theorem
    selectedPathTaggedSelectionSetResponseDiffWitness_of_observableResponsePath_valid_normal_pair_support_context_fuel_ge
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
                      -> SelectedPathTaggedSelectionSetResponseDiffWitness schema
                          rootSelectionSet leftInitialSelectionSet
                          rightInitialSelectionSet leftInitialSpine
                          rightInitialSpine variableValues (fuel + 1)
                          normalParentType runtimeType targetParent leftField
                          rightField leftArguments rightArguments leftRuntime
                          rightRuntime leftCurrentSelectionSet
                          rightCurrentSelectionSet fieldSpine fieldSpine
                          selectionSet) := by
  intro hschema normalParentType leftCurrentSelectionSet
    rightCurrentSelectionSet selectionSet responsePath hpath
    variableDefinitions fuel targetParent leftField rightField
    leftArguments rightArguments leftRuntime rightRuntime hvalid hfree
    hnormal hfuel
  rcases
      pathLocalSelectionSetObservableFieldSpineAtSelectedRuntime_of_observableResponsePath_valid_normal
        hpath hvalid hnormal with
    ⟨runtimeType, fieldSpine, hinclude, hobservable⟩
  have hspineValid :
      SelectedFieldSpineRuntimeValid schema normalParentType runtimeType
        fieldSpine :=
    selectedFieldSpineRuntimeValid_of_observableFieldSpineAtSelectedRuntime
      (hobservable leftCurrentSelectionSet)
  refine ⟨runtimeType, fieldSpine, hinclude, hspineValid, ?_⟩
  intro hleftSupport hrightSupport hleftObjectContext
    hrightObjectContext hleftAbstractContext hrightAbstractContext
  exact
    selectedPathTaggedSelectionSetResponseDiffWitness_of_observableFieldSpineAtSelectedRuntime_valid_normal_runtimeSpine_pair_support_context_fuel_ge
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet leftInitialSpine rightInitialSpine
      variableValues hschema normalParentType runtimeType
      leftCurrentSelectionSet rightCurrentSelectionSet selectionSet
      fieldSpine (hobservable leftCurrentSelectionSet)
      variableDefinitions fuel targetParent leftField rightField
      leftArguments rightArguments leftRuntime rightRuntime hvalid hfree
      hnormal hinclude hfuel hleftSupport hrightSupport
      hleftObjectContext hrightObjectContext hleftAbstractContext
      hrightAbstractContext

theorem
    pathLocalTaggedSelectionSetResponseDiffWitness_of_object_leaf_field_valid_normal_support_context_fuel_ge
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (variableValues : Execution.VariableValues)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ∀ parentType variableDefinitions (selectionSet : List Selection)
            fuel targetParent leftField rightField
            (leftArguments rightArguments : List Argument)
            (leftRuntime rightRuntime : Name)
            (currentSelectionSet : List Selection)
            {responseName fieldName : Name} {arguments : List Argument}
            {directives : List DirectiveApplication}
            {childSelectionSet : List Selection}
            {fieldDefinition : FieldDefinition},
          Validation.selectionSetValid schema variableDefinitions parentType selectionSet
          -> selectionSetDirectiveFree selectionSet
          -> selectionSetNormal schema parentType selectionSet
          -> objectTypeNameBool schema parentType = true
          -> selectionSetDeepProbeFuel schema parentType selectionSet ≤ fuel
          -> PathLocalSupportValidNormal schema parentType currentSelectionSet
          -> PathLocalSelectionSetCurrentContext selectionSet currentSelectionSet
          -> Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ selectionSet
          -> schema.lookupField parentType fieldName = some fieldDefinition
          -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
              = false
          -> PathLocalTaggedSelectionSetResponseDiffWitness schema
              rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
              variableValues (fuel + 1) parentType parentType targetParent
              leftField rightField leftArguments rightArguments leftRuntime
              rightRuntime currentSelectionSet selectionSet := by
  intro hschema parentType variableDefinitions selectionSet fuel
    targetParent leftField rightField leftArguments rightArguments
    leftRuntime rightRuntime currentSelectionSet responseName fieldName
    arguments directives childSelectionSet fieldDefinition hvalid hfree
    hnormal hobject hfuel hsupport hcontext hmem hlookup hleaf
  have hinclude :
      schema.typeIncludesObjectBool parentType parentType = true :=
    typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject
  rcases
      executeSelectionSetAsResponse_fieldPairOrDeepSuccess_pathLocalProbe_tagged_of_valid_normal_support_context_fuel_ge_size
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet variableValues hschema
        (SelectionSet.size selectionSet + 1) parentType
        variableDefinitions selectionSet fuel parentType targetParent
        leftField rightField leftArguments rightArguments leftRuntime
        rightRuntime FieldPairProbeTag.left currentSelectionSet
        (by omega) hfuel hvalid hfree hnormal hinclude hsupport
        (fun _hobject => hcontext)
        (fun hparentNonObject => by
          rw [hobject] at hparentNonObject
          simp at hparentNonObject) with
    ⟨leftFields, leftErrors, hleftResponse⟩
  rcases
      executeSelectionSetAsResponse_fieldPairOrDeepSuccess_pathLocalProbe_tagged_of_valid_normal_support_context_fuel_ge_size
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet variableValues hschema
        (SelectionSet.size selectionSet + 1) parentType
        variableDefinitions selectionSet fuel parentType targetParent
        leftField rightField leftArguments rightArguments leftRuntime
        rightRuntime FieldPairProbeTag.right currentSelectionSet
        (by omega) hfuel hvalid hfree hnormal hinclude hsupport
        (fun _hobject => hcontext)
        (fun hparentNonObject => by
          rw [hobject] at hparentNonObject
          simp at hparentNonObject) with
    ⟨rightFields, rightErrors, hrightResponse⟩
  have hleftChildren :
      PathLocalSelectionSetFieldChildrenReady schema rootSelectionSet
        leftInitialSelectionSet rightInitialSelectionSet variableValues fuel
        targetParent leftField rightField parentType leftArguments
        rightArguments leftRuntime rightRuntime FieldPairProbeTag.left
        currentSelectionSet selectionSet :=
    pathLocalSelectionSetFieldChildrenReady_of_valid_normal_support_context_fuel_ge_size
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet variableValues hschema
      (SelectionSet.size selectionSet + 1) parentType variableDefinitions
      selectionSet fuel targetParent leftField rightField leftArguments
      rightArguments leftRuntime rightRuntime FieldPairProbeTag.left
      currentSelectionSet (by omega) hfuel hvalid hfree hnormal hobject
      hsupport hcontext
  have hrightChildren :
      PathLocalSelectionSetFieldChildrenReady schema rootSelectionSet
        leftInitialSelectionSet rightInitialSelectionSet variableValues fuel
        targetParent leftField rightField parentType leftArguments
        rightArguments leftRuntime rightRuntime FieldPairProbeTag.right
        currentSelectionSet selectionSet :=
    pathLocalSelectionSetFieldChildrenReady_of_valid_normal_support_context_fuel_ge_size
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet variableValues hschema
      (SelectionSet.size selectionSet + 1) parentType variableDefinitions
      selectionSet fuel targetParent leftField rightField leftArguments
      rightArguments leftRuntime rightRuntime FieldPairProbeTag.right
      currentSelectionSet (by omega) hfuel hvalid hfree hnormal hobject
      hsupport hcontext
  have hleafFuel :
      leafProbeFuel fieldDefinition.outputType ≤ fuel := by
    have hlocal :=
      leafProbeFuel_le_selectionSetDeepProbeFuel_of_field_mem schema
        parentType (selectionSet := selectionSet)
        (responseName := responseName) (fieldName := fieldName)
        (arguments := arguments) (directives := directives)
        (childSelectionSet := childSelectionSet)
        (fieldDefinition := fieldDefinition) hmem hlookup
    omega
  have hdataNot :
      ¬ Execution.ResponseValue.semanticEquivalent
        (Execution.executeSelectionSetAsResponse schema
          (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
            (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
              rightInitialSelectionSet targetParent leftField rightField
              leftArguments rightArguments leftRuntime rightRuntime)
            targetParent leftField rightField leftArguments rightArguments)
          variableValues (fuel + 1) parentType
          (projectionTargetResolverValue
            (.object parentType
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
            (.object parentType
              (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                currentSelectionSet)))
          selectionSet).data :=
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_leaf_field_of_field_children
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet currentSelectionSet variableValues fuel
      targetParent leftField rightField parentType parentType
      leftArguments rightArguments leftRuntime rightRuntime hfree hnormal
      hobject hmem hlookup hleafFuel hleaf hleftChildren hrightChildren
  refine ⟨
    hinclude,
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
    pathLocalTaggedSelectionSetResponseDiffWitness_of_object_child_field_valid_normal_support_context_fuel_ge
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (variableValues : Execution.VariableValues)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ∀ parentType variableDefinitions (selectionSet : List Selection)
            fuel targetParent leftField rightField
            (leftArguments rightArguments : List Argument)
            (leftRuntime rightRuntime : Name)
            (currentSelectionSet : List Selection)
            {responseName fieldName : Name} {arguments : List Argument}
            {directives : List DirectiveApplication}
            {childSelectionSet : List Selection}
            {fieldDefinition : FieldDefinition} {runtimeType : Name},
          Validation.selectionSetValid schema variableDefinitions parentType selectionSet
          -> selectionSetDirectiveFree selectionSet
          -> selectionSetNormal schema parentType selectionSet
          -> objectTypeNameBool schema parentType = true
          -> selectionSetDeepProbeFuel schema parentType selectionSet ≤ fuel
          -> PathLocalSupportValidNormal schema parentType currentSelectionSet
          -> PathLocalSelectionSetCurrentContext selectionSet currentSelectionSet
          -> Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ selectionSet
          -> schema.lookupField parentType fieldName = some fieldDefinition
          -> ((objectTypeNameBool schema fieldDefinition.outputType.namedType = true
                ∧ runtimeType = fieldDefinition.outputType.namedType)
              ∨ ((TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool
                      schema
                    = true
                  ∧ objectTypeNameBool schema fieldDefinition.outputType.namedType = false
                  ∧ abstractRuntimeForFieldHeadDeep? schema parentType fieldName
                      arguments parentType currentSelectionSet
                    = some runtimeType))
          -> PathLocalTaggedSelectionSetResponseDiffWitness schema
              rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
              variableValues (fuel - leafProbeFuel fieldDefinition.outputType)
              fieldDefinition.outputType.namedType runtimeType targetParent
              leftField rightField leftArguments rightArguments leftRuntime
              rightRuntime
              (fieldPairPathLocalNextSelectionSet schema parentType runtimeType
                fieldName arguments currentSelectionSet)
              childSelectionSet
          -> PathLocalTaggedSelectionSetResponseDiffWitness schema
              rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
              variableValues (fuel + 1) parentType parentType targetParent
              leftField rightField leftArguments rightArguments leftRuntime
              rightRuntime currentSelectionSet selectionSet := by
  intro hschema parentType variableDefinitions selectionSet fuel
    targetParent leftField rightField leftArguments rightArguments
    leftRuntime rightRuntime currentSelectionSet responseName fieldName
    arguments directives childSelectionSet fieldDefinition runtimeType
    hvalid hfree hnormal hobject hfuel hsupport hcontext hmem hlookup
    hruntime hchildWitness
  have hinclude :
      schema.typeIncludesObjectBool parentType parentType = true :=
    typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject
  rcases
      executeSelectionSetAsResponse_fieldPairOrDeepSuccess_pathLocalProbe_tagged_of_valid_normal_support_context_fuel_ge_size
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet variableValues hschema
        (SelectionSet.size selectionSet + 1) parentType
        variableDefinitions selectionSet fuel parentType targetParent
        leftField rightField leftArguments rightArguments leftRuntime
        rightRuntime FieldPairProbeTag.left currentSelectionSet
        (by omega) hfuel hvalid hfree hnormal hinclude hsupport
        (fun _hobject => hcontext)
        (fun hparentNonObject => by
          rw [hobject] at hparentNonObject
          simp at hparentNonObject) with
    ⟨leftFields, leftErrors, hleftResponse⟩
  rcases
      executeSelectionSetAsResponse_fieldPairOrDeepSuccess_pathLocalProbe_tagged_of_valid_normal_support_context_fuel_ge_size
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet variableValues hschema
        (SelectionSet.size selectionSet + 1) parentType
        variableDefinitions selectionSet fuel parentType targetParent
        leftField rightField leftArguments rightArguments leftRuntime
        rightRuntime FieldPairProbeTag.right currentSelectionSet
        (by omega) hfuel hvalid hfree hnormal hinclude hsupport
        (fun _hobject => hcontext)
        (fun hparentNonObject => by
          rw [hobject] at hparentNonObject
          simp at hparentNonObject) with
    ⟨rightFields, rightErrors, hrightResponse⟩
  rcases hchildWitness with
    ⟨_hchildInclude, leftChildFields, leftChildErrors, rightChildFields,
      rightChildErrors, hleftChildResponse, hrightChildResponse,
      hchildNot⟩
  have hleftChildren :
      PathLocalSelectionSetFieldChildrenReady schema rootSelectionSet
        leftInitialSelectionSet rightInitialSelectionSet variableValues fuel
        targetParent leftField rightField parentType leftArguments
        rightArguments leftRuntime rightRuntime FieldPairProbeTag.left
        currentSelectionSet selectionSet :=
    pathLocalSelectionSetFieldChildrenReady_of_valid_normal_support_context_fuel_ge_size
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet variableValues hschema
      (SelectionSet.size selectionSet + 1) parentType variableDefinitions
      selectionSet fuel targetParent leftField rightField leftArguments
      rightArguments leftRuntime rightRuntime FieldPairProbeTag.left
      currentSelectionSet (by omega) hfuel hvalid hfree hnormal hobject
      hsupport hcontext
  have hrightChildren :
      PathLocalSelectionSetFieldChildrenReady schema rootSelectionSet
        leftInitialSelectionSet rightInitialSelectionSet variableValues fuel
        targetParent leftField rightField parentType leftArguments
        rightArguments leftRuntime rightRuntime FieldPairProbeTag.right
        currentSelectionSet selectionSet :=
    pathLocalSelectionSetFieldChildrenReady_of_valid_normal_support_context_fuel_ge_size
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet variableValues hschema
      (SelectionSet.size selectionSet + 1) parentType variableDefinitions
      selectionSet fuel targetParent leftField rightField leftArguments
      rightArguments leftRuntime rightRuntime FieldPairProbeTag.right
      currentSelectionSet (by omega) hfuel hvalid hfree hnormal hobject
      hsupport hcontext
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet
      (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
        rightInitialSelectionSet targetParent leftField rightField
        leftArguments rightArguments leftRuntime rightRuntime)
      targetParent leftField rightField leftArguments rightArguments
  let leftSource :=
    projectionTargetResolverValue
      (.object parentType
        (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
          currentSelectionSet))
  let rightSource :=
    projectionTargetResolverValue
      (.object parentType
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
        targetParent leftField rightField parentType parentType
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
        targetParent leftField rightField parentType parentType
        leftArguments rightArguments leftRuntime rightRuntime
        FieldPairProbeTag.right selectionSet hrightChildren
  have hleafFuel :
      leafProbeFuel fieldDefinition.outputType ≤ fuel := by
    have hlocal :=
      leafProbeFuel_le_selectionSetDeepProbeFuel_of_field_mem schema
        parentType (selectionSet := selectionSet)
        (responseName := responseName) (fieldName := fieldName)
        (arguments := arguments) (directives := directives)
        (childSelectionSet := childSelectionSet)
        (fieldDefinition := fieldDefinition) hmem hlookup
    omega
  have hdataNot :
      ¬ Execution.ResponseValue.semanticEquivalent
        (Execution.executeSelectionSetAsResponse schema
          (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
            (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
              rightInitialSelectionSet targetParent leftField rightField
              leftArguments rightArguments leftRuntime rightRuntime)
            targetParent leftField rightField leftArguments rightArguments)
          variableValues (fuel + 1) parentType
          (projectionTargetResolverValue
            (.object parentType
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
            (.object parentType
              (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                currentSelectionSet)))
          selectionSet).data :=
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_child_field_of_field_ok_of_sound
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet currentSelectionSet variableValues fuel
      targetParent leftField rightField parentType parentType
      leftArguments rightArguments leftRuntime rightRuntime hfree hnormal
      hobject hmem hlookup hruntime hsupport.sound hleafFuel
      hleftChildResponse hrightChildResponse hchildNot hleftFieldOk
      hrightFieldOk
  refine ⟨
    hinclude,
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
    pathLocalTaggedSelectionSetResponseDiffWitness_of_abstract_inlineFragment_body_valid_normal_support_context_fuel_ge
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (variableValues : Execution.VariableValues)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ∀ normalParentType variableDefinitions (selectionSet : List Selection)
            fuel runtimeType targetParent leftField rightField
            (leftArguments rightArguments : List Argument)
            (leftRuntime rightRuntime : Name)
            (currentSelectionSet : List Selection)
            {directives : List DirectiveApplication}
            {bodySelectionSet : List Selection},
          Validation.selectionSetValid schema variableDefinitions normalParentType
            selectionSet
          -> selectionSetDirectiveFree selectionSet
          -> selectionSetNormal schema normalParentType selectionSet
          -> objectTypeNameBool schema normalParentType = false
          -> objectTypeNameBool schema runtimeType = true
          -> schema.typeIncludesObjectBool normalParentType runtimeType = true
          -> selectionSetDeepProbeFuel schema normalParentType selectionSet ≤ fuel
          -> PathLocalSupportValidNormal schema runtimeType currentSelectionSet
          -> (∀ {bodyDirectives bodySelectionSet},
                Selection.inlineFragment (some runtimeType) bodyDirectives
                    bodySelectionSet
                  ∈ selectionSet
                -> PathLocalSelectionSetCurrentContext bodySelectionSet
                    currentSelectionSet)
          -> Selection.inlineFragment (some runtimeType) directives bodySelectionSet
              ∈ selectionSet
          -> PathLocalTaggedSelectionSetResponseDiffWitness schema
              rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
              variableValues (fuel + 1) runtimeType runtimeType targetParent
              leftField rightField leftArguments rightArguments leftRuntime
              rightRuntime currentSelectionSet bodySelectionSet
          -> PathLocalTaggedSelectionSetResponseDiffWitness schema
              rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
              variableValues (fuel + 1) normalParentType runtimeType targetParent
              leftField rightField leftArguments rightArguments leftRuntime
              rightRuntime currentSelectionSet selectionSet := by
  intro hschema normalParentType variableDefinitions selectionSet fuel
    runtimeType targetParent leftField rightField leftArguments
    rightArguments leftRuntime rightRuntime currentSelectionSet directives
    bodySelectionSet hvalid hfree hnormal hnonObject hruntimeObject
    hinclude hfuel hsupport habstractContext hinlineMem hbodyWitness
  rcases
      executeSelectionSetAsResponse_fieldPairOrDeepSuccess_pathLocalProbe_tagged_of_valid_normal_support_context_fuel_ge_size
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet variableValues hschema
        (SelectionSet.size selectionSet + 1) normalParentType
        variableDefinitions selectionSet fuel runtimeType targetParent
        leftField rightField leftArguments rightArguments leftRuntime
        rightRuntime FieldPairProbeTag.left currentSelectionSet
        (by omega) hfuel hvalid hfree hnormal hinclude hsupport
        (fun hparentObject => by
          rw [hnonObject] at hparentObject
          simp at hparentObject)
        (fun _hnonObject {bodyDirectives} {bodySelectionSet} bodyMem =>
          habstractContext
            (bodyDirectives := bodyDirectives)
            (bodySelectionSet := bodySelectionSet) bodyMem) with
    ⟨leftFields, leftErrors, hleftResponse⟩
  rcases
      executeSelectionSetAsResponse_fieldPairOrDeepSuccess_pathLocalProbe_tagged_of_valid_normal_support_context_fuel_ge_size
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet variableValues hschema
        (SelectionSet.size selectionSet + 1) normalParentType
        variableDefinitions selectionSet fuel runtimeType targetParent
        leftField rightField leftArguments rightArguments leftRuntime
        rightRuntime FieldPairProbeTag.right currentSelectionSet
        (by omega) hfuel hvalid hfree hnormal hinclude hsupport
        (fun hparentObject => by
          rw [hnonObject] at hparentObject
          simp at hparentObject)
        (fun _hnonObject {bodyDirectives} {bodySelectionSet} bodyMem =>
          habstractContext
            (bodyDirectives := bodyDirectives)
            (bodySelectionSet := bodySelectionSet) bodyMem) with
    ⟨rightFields, rightErrors, hrightResponse⟩
  rcases hbodyWitness with
    ⟨_hbodyInclude, leftBodyFields, leftBodyErrors, rightBodyFields,
      rightBodyErrors, hleftBodyResponse, hrightBodyResponse, hbodyNot⟩
  have hbodyDataNot :
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
          bodySelectionSet).data := by
    intro hsemantic
    exact hbodyNot
      (by simpa [hleftBodyResponse, hrightBodyResponse] using hsemantic)
  have hdirectives : directives = [] :=
    selectionSetDirectiveFree_inlineFragment_directives_nil_of_mem hfree
      hinlineMem
  subst directives
  rcases List.mem_iff_append.mp hinlineMem with
    ⟨pref, suffix, hselectionSet⟩
  subst selectionSet
  have hdataNot :
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
                currentSelectionSet)))
          (pref ++ Selection.inlineFragment (some runtimeType) []
            bodySelectionSet :: suffix)).data
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
          (pref ++ Selection.inlineFragment (some runtimeType) []
            bodySelectionSet :: suffix)).data :=
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_tagged_abstract_inlineFragment_body
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet currentSelectionSet variableValues fuel
      targetParent leftField rightField normalParentType runtimeType
      leftArguments rightArguments leftRuntime rightRuntime hnonObject
      hruntimeObject hfree hnormal hbodyDataNot
  refine ⟨
    hinclude,
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
    pathLocalTaggedSelectionSetResponseDiffWitness_of_observableLeafAtRuntime_valid_normal_support_context_fuel_ge
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (variableValues : Execution.VariableValues)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ∀ normalParentType runtimeType currentSelectionSet
            (selectionSet : List Selection),
          PathLocalSelectionSetObservableLeafAtRuntime schema normalParentType
            runtimeType currentSelectionSet selectionSet
          -> ∀ variableDefinitions fuel targetParent leftField rightField
                (leftArguments rightArguments : List Argument)
                (leftRuntime rightRuntime : Name),
              Validation.selectionSetValid schema variableDefinitions
                normalParentType selectionSet
              -> selectionSetDirectiveFree selectionSet
              -> selectionSetNormal schema normalParentType selectionSet
              -> schema.typeIncludesObjectBool normalParentType runtimeType = true
              -> selectionSetDeepProbeFuel schema normalParentType selectionSet ≤ fuel
              -> PathLocalSupportValidNormal schema runtimeType currentSelectionSet
              -> (objectTypeNameBool schema normalParentType = true
                  -> PathLocalSelectionSetCurrentContext selectionSet currentSelectionSet)
              -> (objectTypeNameBool schema normalParentType = false
                  -> ∀ {directives bodySelectionSet},
                      Selection.inlineFragment (some runtimeType) directives
                          bodySelectionSet
                        ∈ selectionSet
                      -> PathLocalSelectionSetCurrentContext bodySelectionSet
                          currentSelectionSet)
              -> PathLocalTaggedSelectionSetResponseDiffWitness schema
                  rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
                  variableValues (fuel + 1) normalParentType runtimeType
                  targetParent leftField rightField leftArguments rightArguments
                  leftRuntime rightRuntime currentSelectionSet selectionSet := by
  intro hschema normalParentType runtimeType currentSelectionSet
    selectionSet hobservable
  induction hobservable with
  | objectLeaf hobject hmem hlookup hleaf =>
      rename_i parentName responseName fieldName arguments directives
        currentSelectionSet childSelectionSet selectionSet fieldDefinition
      intro variableDefinitions fuel targetParent leftField rightField
        leftArguments rightArguments leftRuntime rightRuntime hvalid hfree
        hnormal hinclude hfuel hsupport hobjectContext _habstractContext
      exact
        pathLocalTaggedSelectionSetResponseDiffWitness_of_object_leaf_field_valid_normal_support_context_fuel_ge
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet variableValues hschema parentName
          variableDefinitions selectionSet fuel targetParent leftField
          rightField leftArguments rightArguments leftRuntime rightRuntime
          currentSelectionSet hvalid hfree hnormal hobject hfuel hsupport
          (hobjectContext hobject) hmem hlookup hleaf
  | objectChild hobject hmem hlookup hcomposite hruntime hchild ih =>
      rename_i parentName childRuntimeType responseName fieldName arguments
        directives currentSelectionSet childSelectionSet selectionSet
        fieldDefinition
      intro variableDefinitions fuel targetParent leftField rightField
        leftArguments rightArguments leftRuntime rightRuntime hvalid hfree
        hnormal hinclude hfuel hsupport hobjectContext _habstractContext
      have hreturnComposite :
          (TypeRef.named
              fieldDefinition.outputType.namedType).isCompositeBool schema =
            true :=
        typeRef_named_isCompositeBool_of_isCompositeType hcomposite
      have hfieldDeepFuel :
          leafProbeFuel fieldDefinition.outputType
            + selectionSetDeepProbeFuel schema
              fieldDefinition.outputType.namedType childSelectionSet
            + 1 ≤ fuel := by
        have hlocal :=
          selectionSetDeepProbeFuel_field_mem schema parentName
            selectionSet responseName fieldName arguments directives
            childSelectionSet fieldDefinition hmem hlookup
        omega
      let childFuel :=
        fuel - leafProbeFuel fieldDefinition.outputType - 1
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
          selectionSetNormal schema fieldDefinition.outputType.namedType
            childSelectionSet :=
        selectionSetNormal_field_child_of_mem_lookup hnormal hmem hlookup
      have hchildSizeFuelEq :
          childFuel + 1 =
            fuel - leafProbeFuel fieldDefinition.outputType := by
        dsimp [childFuel]
        omega
      rcases hruntime with hobjectRuntime | habstractRuntime
      · rcases hobjectRuntime with ⟨hreturnObject, hchildRuntimeEq⟩
        subst childRuntimeType
        have hchildValid :
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
        have hchildSupport :
            PathLocalSupportValidNormal schema
              fieldDefinition.outputType.namedType
              (fieldPairPathLocalNextSelectionSet schema parentName
                fieldDefinition.outputType.namedType fieldName arguments
                currentSelectionSet) :=
          hsupport.fieldPairPathLocalNextSelectionSet_of_object_output
            hobject hreturnObject hlookup rfl
        have hallFields : selectionsAllFields childSelectionSet :=
          selectionSetNormal_allFields_of_object hchildNormal hreturnObject
        have hpruned :
            runtimePrunedSelectionSet schema
                fieldDefinition.outputType.namedType childSelectionSet =
              childSelectionSet :=
          runtimePrunedSelectionSet_eq_self_of_allFields schema
            fieldDefinition.outputType.namedType hallFields
        have hchildContext :
            PathLocalSelectionSetCurrentContext childSelectionSet
              (fieldPairPathLocalNextSelectionSet schema parentName
                fieldDefinition.outputType.namedType fieldName arguments
                currentSelectionSet) :=
          PathLocalSelectionSetCurrentContext.fieldPairPathLocalNextSelectionSet_field_child
            (schema := schema) (currentRuntimeType := parentName)
            (childRuntimeType := fieldDefinition.outputType.namedType)
            (targetField := fieldName) (responseName := responseName)
            (targetArguments := arguments) (arguments := arguments)
            (directives := directives) (selectionSet := selectionSet)
            (childSelectionSet := childSelectionSet)
            (currentSelectionSet := currentSelectionSet)
            (hobjectContext hobject) hmem
            (argumentsEquivalent_refl_forSyntaxDiff arguments) hpruned
        have hchildWitness :
            PathLocalTaggedSelectionSetResponseDiffWitness schema
              rootSelectionSet leftInitialSelectionSet
              rightInitialSelectionSet variableValues
              (fuel - leafProbeFuel fieldDefinition.outputType)
              fieldDefinition.outputType.namedType
              fieldDefinition.outputType.namedType targetParent leftField
              rightField leftArguments rightArguments leftRuntime
              rightRuntime
              (fieldPairPathLocalNextSelectionSet schema parentName
                fieldDefinition.outputType.namedType fieldName arguments
                currentSelectionSet)
              childSelectionSet := by
          have hraw :=
            ih variableDefinitions childFuel targetParent leftField
              rightField leftArguments rightArguments leftRuntime
              rightRuntime hchildValid hchildFree hchildNormal
              hchildInclude hchildFuel hchildSupport
              (fun _hobject => hchildContext)
              (fun hnonObject => by
                rw [hreturnObject] at hnonObject
                simp at hnonObject)
          simpa [hchildSizeFuelEq] using hraw
        exact
          pathLocalTaggedSelectionSetResponseDiffWitness_of_object_child_field_valid_normal_support_context_fuel_ge
            schema rootSelectionSet leftInitialSelectionSet
            rightInitialSelectionSet variableValues hschema parentName
            variableDefinitions selectionSet fuel targetParent leftField
            rightField leftArguments rightArguments leftRuntime rightRuntime
            currentSelectionSet hvalid hfree hnormal hobject hfuel hsupport
            (hobjectContext hobject) hmem hlookup
            (Or.inl ⟨hreturnObject, rfl⟩) hchildWitness
      · rcases habstractRuntime with
          ⟨hreturnComposite', hreturnNonObject, hruntimeHead⟩
        have hchildObject : objectTypeNameBool schema childRuntimeType = true :=
          objectTypeNameBool_of_typeIncludesObjectBool hschema
            (by
              have hready :
                  PathLocalSelectionSetHeadReady schema parentName
                    currentSelectionSet selectionSet :=
                PathLocalSelectionSetCurrentContext.headReady_of_valid_normal
                  hsupport.sound (hobjectContext hobject) hvalid hnormal
              rcases
                  hready responseName fieldName arguments directives
                    childSelectionSet fieldDefinition hmem hlookup
                    hreturnComposite hreturnNonObject with
                ⟨runtimeType', hruntime', hinclude'⟩
              have hruntimeEq : runtimeType' = childRuntimeType := by
                rw [hruntimeHead] at hruntime'
                exact Option.some.inj hruntime'.symm
              subst runtimeType'
              exact hinclude')
        have hchildInclude :
            schema.typeIncludesObjectBool
                fieldDefinition.outputType.namedType childRuntimeType =
              true := by
          have hready :
              PathLocalSelectionSetHeadReady schema parentName
                currentSelectionSet selectionSet :=
            PathLocalSelectionSetCurrentContext.headReady_of_valid_normal
              hsupport.sound (hobjectContext hobject) hvalid hnormal
          rcases
              hready responseName fieldName arguments directives
                childSelectionSet fieldDefinition hmem hlookup
                hreturnComposite hreturnNonObject with
            ⟨runtimeType', hruntime', hinclude'⟩
          have hruntimeEq : runtimeType' = childRuntimeType := by
            rw [hruntimeHead] at hruntime'
            exact Option.some.inj hruntime'.symm
          subst runtimeType'
          exact hinclude'
        have hchildNonempty : childSelectionSet ≠ [] :=
          selectionSet_nonempty_of_pathLocalSelectionSetObservableLeafAtRuntime
            hchild
        have hchildValid :
            Validation.selectionSetValid schema variableDefinitions
              fieldDefinition.outputType.namedType childSelectionSet :=
          selectionSetValid_field_child_of_mem_lookup hvalid hmem
            hchildNonempty hlookup
        have hchildSupport :
            PathLocalSupportValidNormal schema childRuntimeType
              (fieldPairPathLocalNextSelectionSet schema parentName
                childRuntimeType fieldName arguments currentSelectionSet) :=
          hsupport.fieldPairPathLocalNextSelectionSet_of_abstract_output
            hobject hchildObject hlookup hreturnComposite hchildInclude
        have hchildWitness :
            PathLocalTaggedSelectionSetResponseDiffWitness schema
              rootSelectionSet leftInitialSelectionSet
              rightInitialSelectionSet variableValues
              (fuel - leafProbeFuel fieldDefinition.outputType)
              fieldDefinition.outputType.namedType childRuntimeType
              targetParent leftField rightField leftArguments rightArguments
              leftRuntime rightRuntime
              (fieldPairPathLocalNextSelectionSet schema parentName
                childRuntimeType fieldName arguments currentSelectionSet)
              childSelectionSet := by
          have hraw :=
            ih variableDefinitions childFuel targetParent leftField
              rightField leftArguments rightArguments leftRuntime
              rightRuntime hchildValid hchildFree hchildNormal
              hchildInclude hchildFuel hchildSupport
              (fun hchildParentObject => by
                rw [hreturnNonObject] at hchildParentObject
                simp at hchildParentObject)
              (by
                intro _hchildParentNonObject
                intro bodyDirectives bodySelectionSet hbodyMem
                exact
                  PathLocalSelectionSetCurrentContext.fieldPairPathLocalNextSelectionSet_inlineFragment_body
                    (schema := schema)
                    (currentRuntimeType := parentName)
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
                    (hobjectContext hobject) hmem hbodyMem
                    (argumentsEquivalent_refl_forSyntaxDiff arguments)
                    hchildNormal hchildObject)
          simpa [hchildSizeFuelEq] using hraw
        exact
          pathLocalTaggedSelectionSetResponseDiffWitness_of_object_child_field_valid_normal_support_context_fuel_ge
            schema rootSelectionSet leftInitialSelectionSet
            rightInitialSelectionSet variableValues hschema parentName
            variableDefinitions selectionSet fuel targetParent leftField
            rightField leftArguments rightArguments leftRuntime rightRuntime
            currentSelectionSet hvalid hfree hnormal hobject hfuel hsupport
            (hobjectContext hobject) hmem hlookup
            (Or.inr ⟨hreturnComposite', hreturnNonObject, hruntimeHead⟩)
            hchildWitness
  | abstractInlineFragment hnonObject hruntimeObject hinclude hmem hchild
      ih =>
      rename_i parentName runtimeName directives currentSelectionSet
        childSelectionSet selectionSet
      intro variableDefinitions fuel targetParent leftField rightField
        leftArguments rightArguments leftRuntime rightRuntime hvalid hfree
        hnormal _hinclude hfuel hsupport _hobjectContext habstractContext
      have hdirectives : directives = [] :=
        selectionSetDirectiveFree_inlineFragment_directives_nil_of_mem hfree
          hmem
      subst directives
      have hbodyValid :
          Validation.selectionSetValid schema variableDefinitions runtimeName
            childSelectionSet :=
        selectionSetValid_inlineFragment_some_child_of_mem hvalid hmem
      have hbodyFree : selectionSetDirectiveFree childSelectionSet :=
        selectionSetDirectiveFree_inlineFragment_child_of_mem hfree hmem
      have hbodyNormal :
          selectionSetNormal schema runtimeName childSelectionSet :=
        (selectionSetNormal_inlineFragment_child_of_mem hnormal hmem).2
      have hbodyFuel :
          selectionSetDeepProbeFuel schema runtimeName childSelectionSet ≤
            fuel := by
        have hlocal :=
          selectionSetDeepProbeFuel_inlineFragment_some_mem schema
            parentName selectionSet runtimeName
            ([] : List DirectiveApplication) childSelectionSet hmem
        omega
      have hbodyInclude :
          schema.typeIncludesObjectBool runtimeName runtimeName = true :=
        typeIncludesObjectBool_self_of_objectTypeNameBool schema
          hruntimeObject
      have hbodyContext :
          PathLocalSelectionSetCurrentContext childSelectionSet
            currentSelectionSet :=
        habstractContext hnonObject hmem
      have hbodyWitness :
          PathLocalTaggedSelectionSetResponseDiffWitness schema
            rootSelectionSet leftInitialSelectionSet
            rightInitialSelectionSet variableValues (fuel + 1)
            runtimeName runtimeName targetParent leftField rightField
            leftArguments rightArguments leftRuntime rightRuntime
            currentSelectionSet childSelectionSet :=
        ih variableDefinitions fuel targetParent leftField rightField
          leftArguments rightArguments leftRuntime rightRuntime hbodyValid
          hbodyFree hbodyNormal hbodyInclude hbodyFuel hsupport
          (fun _hobject => hbodyContext)
          (fun hbodyNonObject => by
            rw [hruntimeObject] at hbodyNonObject
            simp at hbodyNonObject)
      exact
        pathLocalTaggedSelectionSetResponseDiffWitness_of_abstract_inlineFragment_body_valid_normal_support_context_fuel_ge
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet variableValues hschema parentName
          variableDefinitions selectionSet fuel runtimeName targetParent
          leftField rightField leftArguments rightArguments leftRuntime
          rightRuntime currentSelectionSet hvalid hfree hnormal hnonObject
          hruntimeObject hinclude hfuel hsupport
          (fun {directives} {bodySelectionSet} hbodyMem =>
            habstractContext hnonObject
              (directives := directives)
              (bodySelectionSet := bodySelectionSet) hbodyMem)
          hmem hbodyWitness

theorem
    responseData_not_semanticEquivalent_of_pathLocalProbe_observableLeafAtRuntime_valid_normal_support_context_fuel_ge
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (variableValues : Execution.VariableValues)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ∀ normalParentType runtimeType currentSelectionSet
            (selectionSet : List Selection),
          PathLocalSelectionSetObservableLeafAtRuntime schema normalParentType
            runtimeType currentSelectionSet selectionSet
          -> ∀ variableDefinitions fuel targetParent leftField rightField
                (leftArguments rightArguments : List Argument)
                (leftRuntime rightRuntime : Name),
              Validation.selectionSetValid schema variableDefinitions
                normalParentType selectionSet
              -> selectionSetDirectiveFree selectionSet
              -> selectionSetNormal schema normalParentType selectionSet
              -> schema.typeIncludesObjectBool normalParentType runtimeType = true
              -> selectionSetDeepProbeFuel schema normalParentType selectionSet ≤ fuel
              -> PathLocalSupportValidNormal schema runtimeType currentSelectionSet
              -> (objectTypeNameBool schema normalParentType = true
                  -> PathLocalSelectionSetCurrentContext selectionSet currentSelectionSet)
              -> (objectTypeNameBool schema normalParentType = false
                  -> ∀ {directives bodySelectionSet},
                      Selection.inlineFragment (some runtimeType) directives
                          bodySelectionSet
                        ∈ selectionSet
                      -> PathLocalSelectionSetCurrentContext bodySelectionSet
                          currentSelectionSet)
              -> ¬ Execution.ResponseValue.semanticEquivalent
                    (Execution.executeSelectionSetAsResponse schema
                      (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                        (fieldPairPathLocalProbeResolvers schema
                          leftInitialSelectionSet rightInitialSelectionSet
                          targetParent leftField rightField leftArguments
                          rightArguments leftRuntime rightRuntime)
                        targetParent leftField rightField leftArguments
                        rightArguments)
                      variableValues (fuel + 1) runtimeType
                      (projectionTargetResolverValue
                        (.object runtimeType
                          (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                            currentSelectionSet)))
                      selectionSet).data
                    (Execution.executeSelectionSetAsResponse schema
                      (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                        (fieldPairPathLocalProbeResolvers schema
                          leftInitialSelectionSet rightInitialSelectionSet
                          targetParent leftField rightField leftArguments
                          rightArguments leftRuntime rightRuntime)
                        targetParent leftField rightField leftArguments
                        rightArguments)
                      variableValues (fuel + 1) runtimeType
                      (projectionTargetResolverValue
                        (.object runtimeType
                          (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                            currentSelectionSet)))
                      selectionSet).data := by
  intro hschema normalParentType runtimeType currentSelectionSet
    selectionSet hobservable variableDefinitions fuel targetParent leftField
    rightField leftArguments rightArguments leftRuntime rightRuntime hvalid
    hfree hnormal hinclude hfuel hsupport hobjectContext
    habstractContext
  rcases
      pathLocalTaggedSelectionSetResponseDiffWitness_of_observableLeafAtRuntime_valid_normal_support_context_fuel_ge
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet variableValues hschema normalParentType
        runtimeType currentSelectionSet selectionSet hobservable
        variableDefinitions fuel targetParent leftField rightField
        leftArguments rightArguments leftRuntime rightRuntime hvalid hfree
        hnormal hinclude hfuel hsupport hobjectContext habstractContext with
    ⟨_hinclude, leftFields, leftErrors, rightFields, rightErrors,
      hleftResponse, hrightResponse, hnot⟩
  intro hsemantic
  exact hnot (by
    simpa [hleftResponse, hrightResponse] using hsemantic)

theorem
    not_selectionSetsDataEquivalent_of_pathLocalProbe_singleton_arguments_observableLeafAtRuntime
    {schema : Schema}
    {parentType responseName fieldName childParentType childRuntimeType : Name}
    {leftArguments rightArguments : List Argument}
    {childSelectionSet currentSelectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
    {childVariableDefinitions : List VariableDefinition}
    : SchemaWellFormedness.schemaWellFormed schema
      -> objectTypeNameBool schema parentType = true
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> fieldDefinition.outputType.namedType = childParentType
      -> Validation.selectionSetValid schema childVariableDefinitions
          childParentType childSelectionSet
      -> selectionSetDirectiveFree childSelectionSet
      -> selectionSetNormal schema childParentType childSelectionSet
      -> schema.typeIncludesObjectBool childParentType childRuntimeType = true
      -> PathLocalSelectionSetObservableLeafAtRuntime schema childParentType
          childRuntimeType currentSelectionSet childSelectionSet
      -> PathLocalSupportValidNormal schema childRuntimeType currentSelectionSet
      -> (objectTypeNameBool schema childParentType = true
          -> PathLocalSelectionSetCurrentContext childSelectionSet currentSelectionSet)
      -> (objectTypeNameBool schema childParentType = false
          -> ∀ {directives bodySelectionSet},
              Selection.inlineFragment (some childRuntimeType) directives bodySelectionSet
                ∈ childSelectionSet
              -> PathLocalSelectionSetCurrentContext bodySelectionSet currentSelectionSet)
      -> selectionSetDirectiveFree
          [Selection.field responseName fieldName leftArguments [] childSelectionSet]
      -> selectionSetDirectiveFree
          [Selection.field responseName fieldName rightArguments [] childSelectionSet]
      -> selectionSetNormal schema parentType
          [Selection.field responseName fieldName leftArguments [] childSelectionSet]
      -> selectionSetNormal schema parentType
          [Selection.field responseName fieldName rightArguments [] childSelectionSet]
      -> ¬ Argument.argumentsEquivalent leftArguments rightArguments
      -> ¬ selectionSetsDataEquivalent schema parentType
            [Selection.field responseName fieldName leftArguments [] childSelectionSet]
            [Selection.field responseName fieldName rightArguments []
              childSelectionSet] := by
  intro hschema hparentObject hlookup hreturnType hchildValid
    hchildFree hchildNormal hchildInclude hobservable hsupport
    hobjectContext habstractContext hleftFree hrightFree hleftNormal
    hrightNormal hargumentsDiff
  let rootSelectionSet : List Selection := []
  let variableValues : Execution.VariableValues := []
  let childFuel :=
    selectionSetDeepProbeFuel schema childParentType childSelectionSet
  let parentFuel := childFuel + 1 + leafProbeFuel fieldDefinition.outputType
  have hfieldInclude :
      schema.typeIncludesObjectBool fieldDefinition.outputType.namedType
        childRuntimeType = true := by
    subst childParentType
    exact hchildInclude
  rcases
      pathLocalTaggedSelectionSetResponseDiffWitness_of_observableLeafAtRuntime_valid_normal_support_context_fuel_ge
        schema rootSelectionSet currentSelectionSet currentSelectionSet
        variableValues hschema childParentType childRuntimeType
        currentSelectionSet childSelectionSet hobservable
        childVariableDefinitions childFuel parentType fieldName fieldName
        leftArguments rightArguments childRuntimeType childRuntimeType
        hchildValid hchildFree hchildNormal hchildInclude (by omega)
        hsupport hobjectContext habstractContext with
    ⟨_hinclude, leftChildFields, leftChildErrors, rightChildFields,
      rightChildErrors, hleftChildResponseRaw, hrightChildResponseRaw,
      hchildNot⟩
  have hparentFuelChild :
      parentFuel - leafProbeFuel fieldDefinition.outputType =
        childFuel + 1 := by
    dsimp [parentFuel]
    omega
  have hparentFuelLeaf :
      leafProbeFuel fieldDefinition.outputType ≤ parentFuel := by
    dsimp [parentFuel]
    omega
  have hleftChildResponse :
      Execution.executeSelectionSetAsResponse schema
          (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
            (fieldPairPathLocalProbeResolvers schema currentSelectionSet
              currentSelectionSet parentType fieldName fieldName
              leftArguments rightArguments childRuntimeType
              childRuntimeType)
            parentType fieldName fieldName leftArguments rightArguments)
          variableValues
          (parentFuel - leafProbeFuel fieldDefinition.outputType)
          childRuntimeType
          (projectionTargetResolverValue
            (.object childRuntimeType
              (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                currentSelectionSet)))
          childSelectionSet =
        ({ data := Execution.ResponseValue.object leftChildFields,
           errors := leftChildErrors } : Execution.Response) := by
    simpa [rootSelectionSet, variableValues, hparentFuelChild] using
      hleftChildResponseRaw
  have hrightChildResponse :
      Execution.executeSelectionSetAsResponse schema
          (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
            (fieldPairPathLocalProbeResolvers schema currentSelectionSet
              currentSelectionSet parentType fieldName fieldName
              leftArguments rightArguments childRuntimeType
              childRuntimeType)
            parentType fieldName fieldName leftArguments rightArguments)
          variableValues
          (parentFuel - leafProbeFuel fieldDefinition.outputType)
          childRuntimeType
          (projectionTargetResolverValue
            (.object childRuntimeType
              (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                currentSelectionSet)))
          childSelectionSet =
        ({ data := Execution.ResponseValue.object rightChildFields,
           errors := rightChildErrors } : Execution.Response) := by
    simpa [rootSelectionSet, variableValues, hparentFuelChild] using
      hrightChildResponseRaw
  have hleftFieldsOk :
      selectionSetFieldsExecuteOk schema
        (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
          (fieldPairPathLocalProbeResolvers schema currentSelectionSet
            currentSelectionSet parentType fieldName fieldName
            leftArguments rightArguments childRuntimeType childRuntimeType)
          parentType fieldName fieldName leftArguments rightArguments)
        variableValues (parentFuel + 1) parentType
        (projectionRootResolverValue
          (.object parentType FieldPairPathLocalProbeRef.root))
        [Selection.field responseName fieldName leftArguments []
          childSelectionSet] := by
    refine
      selectionSetFieldsExecuteOk_fieldPairOrDeepSuccess_pathLocalProbe_of_field_cases
        schema rootSelectionSet currentSelectionSet currentSelectionSet
        variableValues parentFuel parentType fieldName fieldName
        leftArguments rightArguments childRuntimeType childRuntimeType
        fieldDefinition fieldDefinition
        [Selection.field responseName fieldName leftArguments []
          childSelectionSet]
        hlookup hlookup hfieldInclude hfieldInclude hparentFuelLeaf
        hparentFuelLeaf ?_ ?_ ?_
    · intro responseName' arguments directives childSelectionSet' hmem
        _harguments
      have hfieldEq :
          Selection.field responseName' fieldName arguments directives
              childSelectionSet' =
            Selection.field responseName fieldName leftArguments []
              childSelectionSet := by
        simpa using hmem
      cases hfieldEq
      exact ⟨leftChildFields, leftChildErrors, hleftChildResponse⟩
    · intro responseName' arguments directives childSelectionSet' hmem
        harguments
      have hfieldEq :
          Selection.field responseName' fieldName arguments directives
              childSelectionSet' =
            Selection.field responseName fieldName leftArguments []
              childSelectionSet := by
        simpa using hmem
      cases hfieldEq
      exact False.elim (hargumentsDiff harguments)
    · intro responseName' fieldName' arguments directives childSelectionSet'
        hmem hnotProjection
      have hfieldEq :
          Selection.field responseName' fieldName' arguments directives
              childSelectionSet' =
            Selection.field responseName fieldName leftArguments []
              childSelectionSet := by
        simpa using hmem
      cases hfieldEq
      exact False.elim
        (hnotProjection
          ⟨rfl,
            Or.inl
              ⟨rfl, argumentsEquivalent_refl_forSyntaxDiff leftArguments⟩⟩)
  have hrightFieldsOk :
      selectionSetFieldsExecuteOk schema
        (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
          (fieldPairPathLocalProbeResolvers schema currentSelectionSet
            currentSelectionSet parentType fieldName fieldName
            leftArguments rightArguments childRuntimeType childRuntimeType)
          parentType fieldName fieldName leftArguments rightArguments)
        variableValues (parentFuel + 1) parentType
        (projectionRootResolverValue
          (.object parentType FieldPairPathLocalProbeRef.root))
        [Selection.field responseName fieldName rightArguments []
          childSelectionSet] := by
    refine
      selectionSetFieldsExecuteOk_fieldPairOrDeepSuccess_pathLocalProbe_of_field_cases
        schema rootSelectionSet currentSelectionSet currentSelectionSet
        variableValues parentFuel parentType fieldName fieldName
        leftArguments rightArguments childRuntimeType childRuntimeType
        fieldDefinition fieldDefinition
        [Selection.field responseName fieldName rightArguments []
          childSelectionSet]
        hlookup hlookup hfieldInclude hfieldInclude hparentFuelLeaf
        hparentFuelLeaf ?_ ?_ ?_
    · intro responseName' arguments directives childSelectionSet' hmem
        harguments
      have hfieldEq :
          Selection.field responseName' fieldName arguments directives
              childSelectionSet' =
            Selection.field responseName fieldName rightArguments []
              childSelectionSet := by
        simpa using hmem
      cases hfieldEq
      exact False.elim
        (hargumentsDiff (FieldMerge.argumentsEquivalent_symm harguments))
    · intro responseName' arguments directives childSelectionSet' hmem
        _harguments
      have hfieldEq :
          Selection.field responseName' fieldName arguments directives
              childSelectionSet' =
            Selection.field responseName fieldName rightArguments []
              childSelectionSet := by
        simpa using hmem
      cases hfieldEq
      exact ⟨rightChildFields, rightChildErrors, hrightChildResponse⟩
    · intro responseName' fieldName' arguments directives childSelectionSet'
        hmem hnotProjection
      have hfieldEq :
          Selection.field responseName' fieldName' arguments directives
              childSelectionSet' =
            Selection.field responseName fieldName rightArguments []
              childSelectionSet := by
        simpa using hmem
      cases hfieldEq
      exact False.elim
        (hnotProjection
          ⟨rfl,
            Or.inr
              ⟨rfl, argumentsEquivalent_refl_forSyntaxDiff rightArguments⟩⟩)
  exact
    not_selectionSetsDataEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_root_arguments_child_response_diff_of_field_ok
      (schema := schema) (rootSelectionSet := rootSelectionSet)
      (leftInitialSelectionSet := currentSelectionSet)
      (rightInitialSelectionSet := currentSelectionSet)
      (variableValues := variableValues) (parentFuel := parentFuel)
      (parentType := parentType) (responseName := responseName)
      (fieldName := fieldName) (leftArguments := leftArguments)
      (rightArguments := rightArguments) (leftRuntime := childRuntimeType)
      (rightRuntime := childRuntimeType)
      (left := [Selection.field responseName fieldName leftArguments []
        childSelectionSet])
      (right := [Selection.field responseName fieldName rightArguments []
        childSelectionSet])
      (leftDirectives := []) (rightDirectives := [])
      (leftChildSelectionSet := childSelectionSet)
      (rightChildSelectionSet := childSelectionSet)
      (fieldDefinition := fieldDefinition)
      hparentObject hleftNormal hrightNormal hleftFree hrightFree
      (by simp) (by simp) hlookup hfieldInclude hfieldInclude
      hparentFuelLeaf hargumentsDiff hleftChildResponse hrightChildResponse
      hchildNot hleftFieldsOk hrightFieldsOk

theorem
    not_selectionSetsDataEquivalent_of_pathLocalProbe_singleton_arguments_child_object_leaf
    {schema : Schema} {parentType responseName fieldName childParentType : Name}
    {leftArguments rightArguments childArguments : List Argument}
    {childSelectionSet grandChildSelectionSet : List Selection}
    {fieldDefinition childFieldDefinition : FieldDefinition}
    {childResponseName childFieldName : Name}
    {childDirectives : List DirectiveApplication}
    {childVariableDefinitions : List VariableDefinition}
    : SchemaWellFormedness.schemaWellFormed schema
      -> objectTypeNameBool schema parentType = true
      -> objectTypeNameBool schema childParentType = true
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> fieldDefinition.outputType.namedType = childParentType
      -> Validation.selectionSetValid schema childVariableDefinitions
          childParentType childSelectionSet
      -> selectionSetDirectiveFree childSelectionSet
      -> selectionSetNormal schema childParentType childSelectionSet
      -> Selection.field childResponseName childFieldName childArguments
            childDirectives grandChildSelectionSet
          ∈ childSelectionSet
      -> schema.lookupField childParentType childFieldName = some childFieldDefinition
      -> (TypeRef.named childFieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> selectionSetDirectiveFree
          [Selection.field responseName fieldName leftArguments [] childSelectionSet]
      -> selectionSetDirectiveFree
          [Selection.field responseName fieldName rightArguments [] childSelectionSet]
      -> selectionSetNormal schema parentType
          [Selection.field responseName fieldName leftArguments [] childSelectionSet]
      -> selectionSetNormal schema parentType
          [Selection.field responseName fieldName rightArguments [] childSelectionSet]
      -> ¬ Argument.argumentsEquivalent leftArguments rightArguments
      -> ¬ selectionSetsDataEquivalent schema parentType
            [Selection.field responseName fieldName leftArguments [] childSelectionSet]
            [Selection.field responseName fieldName rightArguments []
              childSelectionSet] := by
  intro hschema hparentObject hchildObject hlookup hreturnType hchildValid
    hchildFree hchildNormal hchildLeafMem hchildLeafLookup hchildLeaf
    hleftFree hrightFree hleftNormal hrightNormal hargumentsDiff
  have hchildInclude :
      schema.typeIncludesObjectBool childParentType childParentType = true :=
    typeIncludesObjectBool_self_of_objectTypeNameBool schema hchildObject
  have hobservable :
      PathLocalSelectionSetObservableLeafAtRuntime schema childParentType
        childParentType childSelectionSet childSelectionSet :=
    PathLocalSelectionSetObservableLeafAtRuntime.objectLeaf hchildObject
      hchildLeafMem hchildLeafLookup hchildLeaf
  have hsupport :
      PathLocalSupportValidNormal schema childParentType childSelectionSet :=
    PathLocalSupportValidNormal.of_valid_normal_self hchildValid hchildFree
      hchildNormal
  exact
    not_selectionSetsDataEquivalent_of_pathLocalProbe_singleton_arguments_observableLeafAtRuntime
      hschema hparentObject hlookup hreturnType hchildValid hchildFree
      hchildNormal hchildInclude hobservable hsupport
      (fun _hobject => PathLocalSelectionSetCurrentContext.self)
      (fun hchildNonObject => by
        rw [hchildObject] at hchildNonObject
        simp at hchildNonObject)
      hleftFree hrightFree hleftNormal hrightNormal hargumentsDiff

end GroundTypeNormalization

end NormalForm

end GraphQL
