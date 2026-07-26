import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.FocusedPathProbeContext

/-!
Execution and parent-lift lemmas for path-local focused probes.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

theorem executeSelectionSetAsResponse_fieldPairOrDeepSuccess_pathLocalProbe_tagged_of_valid_normal_support_context_fuel_ge_size
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
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
                  (fieldPairPathLocalProbeResolvers schema
                    leftInitialSelectionSet rightInitialSelectionSet targetParent
                    leftField rightField leftArguments rightArguments
                    leftRuntime rightRuntime)
                  targetParent leftField rightField leftArguments
                  rightArguments)
                variableValues (fuel + 1) runtimeType
                (projectionTargetResolverValue
                  (.object runtimeType
                    (FieldPairPathLocalProbeRef.target tag currentSelectionSet)))
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
        have hsound :
            PathLocalCurrentRuntimeSound schema
              (normalParentType, currentSelectionSet) :=
          hsupport.sound
        have hcontext :
            PathLocalSelectionSetCurrentContext selectionSet
              currentSelectionSet :=
          hobjectContext hparentObject
        refine
          executeSelectionSetAsResponse_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_of_field_children_of_sound
            schema rootSelectionSet leftInitialSelectionSet
            rightInitialSelectionSet currentSelectionSet variableValues fuel
            targetParent leftField rightField normalParentType
            normalParentType leftArguments rightArguments leftRuntime
            rightRuntime tag selectionSet hfree hnormal hparentObject
            hsound ?_
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
                (childRuntimeType := fieldDefinition.outputType.namedType)
                (targetField := fieldName) (responseName := responseName)
                (targetArguments := arguments) (arguments := arguments)
                (directives := directives) (selectionSet := selectionSet)
                (childSelectionSet := childSelectionSet)
                (currentSelectionSet := currentSelectionSet)
                hcontext hmem (argumentsEquivalent_refl_forSyntaxDiff
                  arguments) hpruned
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
            refine
              Or.inr
                ⟨fieldDefinition.outputType.namedType, responseFields,
                  errors, ?_, ?_⟩
            · exact Or.inl ⟨hreturnObject, rfl⟩
            · simpa [hchildFuelEq] using hchildResponse
          · have hreturnNonObject :
                objectTypeNameBool schema
                    fieldDefinition.outputType.namedType = false := by
              cases h :
                  objectTypeNameBool schema
                    fieldDefinition.outputType.namedType <;>
                simp [h] at hreturnObject ⊢
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
            refine
              Or.inr
                ⟨childRuntimeType, responseFields, errors, ?_, ?_⟩
            · exact
                Or.inr ⟨hreturnComposite, hreturnNonObject, hruntime⟩
            · simpa [hchildFuelEq] using hchildResponse
      · have hparentNonObject :
            objectTypeNameBool schema normalParentType = false := by
          cases h : objectTypeNameBool schema normalParentType <;>
            simp [h] at hparentObject ⊢
        refine
          executeSelectionSetAsResponse_fieldPairOrDeepSuccess_pathLocalProbe_tagged_abstract_of_runtime_inlineFragment_body_response
            schema rootSelectionSet leftInitialSelectionSet
            rightInitialSelectionSet currentSelectionSet variableValues fuel
            targetParent leftField rightField normalParentType runtimeType
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

def PathLocalSelectionSetFieldChildrenReady
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (variableValues : Execution.VariableValues)
    (fuel : Nat) (targetParent leftField rightField parentType : Name)
    (leftArguments rightArguments : List Argument)
    (leftRuntime rightRuntime : Name) (tag : FieldPairProbeTag)
    (currentSelectionSet selectionSet : List Selection)
    : Prop :=
  ∀ responseName fieldName arguments directives childSelectionSet,
    Selection.field responseName fieldName arguments directives childSelectionSet
      ∈ selectionSet
    -> ∃ fieldDefinition,
        schema.lookupField parentType fieldName = some fieldDefinition
        ∧ leafProbeFuel fieldDefinition.outputType ≤ fuel
        ∧ ((TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
              = false
            ∨ ∃ childRuntimeType responseFields childErrors,
                (((objectTypeNameBool schema fieldDefinition.outputType.namedType = true
                      ∧ childRuntimeType = fieldDefinition.outputType.namedType)
                    ∨ ((TypeRef.named
                            fieldDefinition.outputType.namedType).isCompositeBool
                            schema
                          = true
                        ∧ objectTypeNameBool schema fieldDefinition.outputType.namedType
                          = false
                        ∧ abstractRuntimeForFieldHeadDeep? schema parentType
                            fieldName arguments parentType currentSelectionSet
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
                          (FieldPairPathLocalProbeRef.target tag
                            (fieldPairPathLocalNextSelectionSet schema
                              parentType childRuntimeType fieldName arguments
                              currentSelectionSet))))
                      childSelectionSet
                    = ({
                          data := Execution.ResponseValue.object responseFields,
                          errors := childErrors
                        }
                        : Execution.Response)))

theorem typeRef_named_isCompositeBool_true_of_objectTypeNameBool
    {schema : Schema} {typeName : Name}
    : objectTypeNameBool schema typeName = true
      -> (TypeRef.named typeName).isCompositeBool schema = true := by
  intro hobject
  cases hlookup : schema.lookupType typeName <;>
    simp [objectTypeNameBool, TypeRef.isCompositeBool, TypeRef.namedType,
      hlookup] at hobject ⊢
  next typeDefinition =>
    cases typeDefinition <;>
      simp at hobject ⊢

theorem PathLocalSelectionSetFieldChildrenReady.response_of_mem_lookup_runtime
    {schema : Schema}
    {rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection}
    {variableValues : Execution.VariableValues}
    {fuel : Nat} {targetParent leftField rightField parentType : Name}
    {leftArguments rightArguments : List Argument}
    {leftRuntime rightRuntime : Name} {tag : FieldPairProbeTag}
    {currentSelectionSet selectionSet : List Selection}
    {responseName fieldName runtimeType : Name}
    {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
    : PathLocalSelectionSetFieldChildrenReady schema rootSelectionSet
        leftInitialSelectionSet rightInitialSelectionSet variableValues fuel
        targetParent leftField rightField parentType leftArguments
        rightArguments leftRuntime rightRuntime tag currentSelectionSet
        selectionSet
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
      -> ∃ responseFields childErrors,
          schema.typeIncludesObjectBool fieldDefinition.outputType.namedType runtimeType
            = true
          ∧ leafProbeFuel fieldDefinition.outputType ≤ fuel
          ∧ Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema
                  leftInitialSelectionSet rightInitialSelectionSet targetParent
                  leftField rightField leftArguments rightArguments leftRuntime
                  rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues
              (fuel - leafProbeFuel fieldDefinition.outputType)
              runtimeType
              (projectionTargetResolverValue
                (.object runtimeType
                  (FieldPairPathLocalProbeRef.target tag
                    (fieldPairPathLocalNextSelectionSet schema parentType
                      runtimeType fieldName arguments currentSelectionSet))))
              childSelectionSet
            = ({
                  data := Execution.ResponseValue.object responseFields,
                  errors := childErrors
                }
                : Execution.Response) := by
  intro hready hmem hlookup hruntime
  rcases hready responseName fieldName arguments directives childSelectionSet
      hmem with
    ⟨candidateDefinition, hcandidateLookup, hfuel, hcase⟩
  have hcandidateEq : candidateDefinition = fieldDefinition := by
    rw [hlookup] at hcandidateLookup
    exact Option.some.inj hcandidateLookup.symm
  subst candidateDefinition
  have hcomposite :
      (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool
        schema = true := by
    rcases hruntime with hobject | habstract
    · exact typeRef_named_isCompositeBool_true_of_objectTypeNameBool
        hobject.1
    · exact habstract.1
  rcases hcase with hleaf | hchild
  · rw [hcomposite] at hleaf
    simp at hleaf
  · rcases hchild with
      ⟨childRuntimeType, responseFields, childErrors, hreadyRuntime,
        hinclude, hresponse⟩
    have hruntimeEq : childRuntimeType = runtimeType := by
      rcases hreadyRuntime with hreadyObject | hreadyAbstract
      · rcases hruntime with hobject | habstract
        · rw [hreadyObject.2, hobject.2]
        · rw [habstract.2.1] at hreadyObject
          simp at hreadyObject
      · rcases hruntime with hobject | habstract
        · rw [hobject.1] at hreadyAbstract
          simp at hreadyAbstract
        · have hsome :
              some childRuntimeType = some runtimeType := by
            rw [← hreadyAbstract.2.2, ← habstract.2.2]
          exact Option.some.inj hsome
    subst childRuntimeType
    exact ⟨responseFields, childErrors, hinclude, hfuel, hresponse⟩

theorem executeSelectionSetAsResponse_fieldPairOrDeepSuccess_pathLocalProbe_target_child_of_valid_normal_context_fuel_ge
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet currentSelectionSet
      : List Selection)
    (variableValues : Execution.VariableValues)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ∀ {variableDefinitions : List VariableDefinition}
            {parentType runtimeType targetParent leftField rightField
              responseName fieldName
              : Name}
            {targetLeftArguments targetRightArguments targetArguments arguments
              : List Argument}
            {directives : List DirectiveApplication}
            {leftRuntime rightRuntime : Name}
            {selectionSet childSelectionSet : List Selection}
            {fieldDefinition : FieldDefinition} {fuel : Nat}
            {tag : FieldPairProbeTag},
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
              = true
          -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType
                runtimeType
              = true
          -> Argument.argumentsEquivalent arguments targetArguments
          -> ∃ responseFields childErrors,
              Execution.executeSelectionSetAsResponse schema
                (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                  (fieldPairPathLocalProbeResolvers schema
                    leftInitialSelectionSet rightInitialSelectionSet
                    targetParent leftField rightField targetLeftArguments
                    targetRightArguments leftRuntime rightRuntime)
                  targetParent leftField rightField targetLeftArguments
                  targetRightArguments)
                variableValues (fuel - leafProbeFuel fieldDefinition.outputType)
                runtimeType
                (projectionTargetResolverValue
                  (.object runtimeType
                    (FieldPairPathLocalProbeRef.target tag
                      (fieldPairPathLocalNextSelectionSet schema parentType
                        runtimeType fieldName targetArguments
                        currentSelectionSet))))
                childSelectionSet
              = ({
                    data := Execution.ResponseValue.object responseFields,
                    errors := childErrors
                  }
                  : Execution.Response) := by
  intro hschema variableDefinitions parentType runtimeType targetParent
    leftField rightField responseName fieldName targetLeftArguments
    targetRightArguments targetArguments arguments directives leftRuntime
    rightRuntime selectionSet childSelectionSet fieldDefinition fuel tag
    hvalid hfree hnormal hparentObject hfuel hsupport hcontext hmem hlookup
    hcomposite hinclude harguments
  have hruntimeObject : objectTypeNameBool schema runtimeType = true :=
    objectTypeNameBool_of_typeIncludesObjectBool hschema hinclude
  rcases
      selectionSetValid_field_lookup_leaf_or_composite_child hvalid hmem with
    ⟨candidateDefinition, hcandidateLookup, hkind⟩
  have hcandidateEq : candidateDefinition = fieldDefinition := by
    rw [hlookup] at hcandidateLookup
    exact Option.some.inj hcandidateLookup.symm
  subst candidateDefinition
  rcases hkind with hleaf | hchildComposite
  · rw [hcomposite] at hleaf
    simp at hleaf
  · have hchildValid :
        Validation.selectionSetValid schema variableDefinitions
          fieldDefinition.outputType.namedType childSelectionSet :=
      hchildComposite.2.2
    have hchildFree : selectionSetDirectiveFree childSelectionSet :=
      selectionSetDirectiveFree_field_child_of_mem hfree hmem
    have hchildNormal :
        selectionSetNormal schema fieldDefinition.outputType.namedType
          childSelectionSet :=
      selectionSetNormal_field_child_of_mem_lookup hnormal hmem hlookup
    have hfieldDeepFuel :
        leafProbeFuel fieldDefinition.outputType
          + selectionSetDeepProbeFuel schema
            fieldDefinition.outputType.namedType childSelectionSet
          + 1 ≤ fuel := by
      have hlocal :=
        selectionSetDeepProbeFuel_field_mem schema parentType
          selectionSet responseName fieldName arguments directives
          childSelectionSet fieldDefinition hmem hlookup
      omega
    let childFuel := fuel - leafProbeFuel fieldDefinition.outputType - 1
    have hchildFuel :
        selectionSetDeepProbeFuel schema
            fieldDefinition.outputType.namedType childSelectionSet ≤
          childFuel := by
      dsimp [childFuel]
      omega
    have hchildFuelEq :
        childFuel + 1 = fuel - leafProbeFuel fieldDefinition.outputType := by
      dsimp [childFuel]
      omega
    have hchildSupport :
        PathLocalSupportValidNormal schema runtimeType
          (fieldPairPathLocalNextSelectionSet schema parentType runtimeType
            fieldName targetArguments currentSelectionSet) :=
      hsupport.fieldPairPathLocalNextSelectionSet_of_abstract_output
        hparentObject hruntimeObject hlookup hcomposite hinclude
    rcases
        executeSelectionSetAsResponse_fieldPairOrDeepSuccess_pathLocalProbe_tagged_of_valid_normal_support_context_fuel_ge_size
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet variableValues hschema
          (SelectionSet.size childSelectionSet + 1)
          fieldDefinition.outputType.namedType variableDefinitions
          childSelectionSet childFuel runtimeType targetParent leftField
          rightField targetLeftArguments targetRightArguments leftRuntime
          rightRuntime tag
          (fieldPairPathLocalNextSelectionSet schema parentType
            runtimeType fieldName targetArguments currentSelectionSet)
          (by omega) hchildFuel hchildValid hchildFree hchildNormal
          hinclude hchildSupport
          (by
            intro hchildParentObject
            have hallFields : selectionsAllFields childSelectionSet :=
              selectionSetNormal_allFields_of_object hchildNormal
                hchildParentObject
            have hpruned :
                runtimePrunedSelectionSet schema runtimeType
                    childSelectionSet =
                  childSelectionSet := by
              have hruntimeEq :
                  runtimeType = fieldDefinition.outputType.namedType :=
                typeIncludesObjectBool_eq_of_objectTypeNameBool_true schema
                  hchildParentObject hinclude
              subst runtimeType
              exact
                runtimePrunedSelectionSet_eq_self_of_allFields schema
                  fieldDefinition.outputType.namedType hallFields
            exact
              PathLocalSelectionSetCurrentContext.fieldPairPathLocalNextSelectionSet_field_child
                (schema := schema) (currentRuntimeType := parentType)
                (childRuntimeType := runtimeType) (targetField := fieldName)
                (responseName := responseName)
                (targetArguments := targetArguments) (arguments := arguments)
                (directives := directives) (selectionSet := selectionSet)
                (childSelectionSet := childSelectionSet)
                (currentSelectionSet := currentSelectionSet)
                hcontext hmem harguments hpruned)
          (by
            intro _hchildParentNonObject bodyDirectives bodySelectionSet
              hbodyMem
            exact
              PathLocalSelectionSetCurrentContext.fieldPairPathLocalNextSelectionSet_inlineFragment_body
                (schema := schema) (currentRuntimeType := parentType)
                (childRuntimeType := runtimeType)
                (childParentType := fieldDefinition.outputType.namedType)
                (targetField := fieldName) (responseName := responseName)
                (targetArguments := targetArguments) (arguments := arguments)
                (directives := directives) (bodyDirectives := bodyDirectives)
                (selectionSet := selectionSet)
                (childSelectionSet := childSelectionSet)
                (bodySelectionSet := bodySelectionSet)
                (currentSelectionSet := currentSelectionSet)
                hcontext hmem hbodyMem harguments hchildNormal
                hruntimeObject) with
      ⟨responseFields, childErrors, hresponse⟩
    exact ⟨responseFields, childErrors, by
      simpa [hchildFuelEq] using hresponse⟩

theorem pathLocalSelectionSetFieldChildrenReady_of_valid_normal_support_context_fuel_ge_size
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (variableValues : Execution.VariableValues)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ∀ n parentType variableDefinitions (selectionSet : List Selection)
            fuel targetParent leftField rightField
            (leftArguments rightArguments : List Argument)
            (leftRuntime rightRuntime : Name) (tag : FieldPairProbeTag)
            (currentSelectionSet : List Selection),
          SelectionSet.size selectionSet < n
          -> selectionSetDeepProbeFuel schema parentType selectionSet ≤ fuel
          -> Validation.selectionSetValid schema variableDefinitions parentType
              selectionSet
          -> selectionSetDirectiveFree selectionSet
          -> selectionSetNormal schema parentType selectionSet
          -> objectTypeNameBool schema parentType = true
          -> PathLocalSupportValidNormal schema parentType currentSelectionSet
          -> PathLocalSelectionSetCurrentContext selectionSet currentSelectionSet
          -> PathLocalSelectionSetFieldChildrenReady schema rootSelectionSet
              leftInitialSelectionSet rightInitialSelectionSet variableValues fuel
              targetParent leftField rightField parentType leftArguments
              rightArguments leftRuntime rightRuntime tag currentSelectionSet
              selectionSet := by
  intro hschema n parentType variableDefinitions selectionSet fuel
    targetParent leftField rightField leftArguments rightArguments leftRuntime
    rightRuntime tag currentSelectionSet hsize hfuel hvalid hfree hnormal
    hparentObject hsupport hcontext
  intro responseName fieldName arguments directives childSelectionSet hmem
  rcases selectionSetValid_field_lookup_of_mem hvalid hmem with
    ⟨fieldDefinition, hlookup, _harguments, _hfieldSelectionValid⟩
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
  refine ⟨fieldDefinition, hlookup, hleafFuel, ?_⟩
  by_cases hreturnLeaf :
      (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool
        schema = false
  · exact Or.inl hreturnLeaf
  · have hreturnComposite :
        (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool
          schema = true := by
      cases h :
          (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool
            schema <;>
        simp [h] at hreturnLeaf ⊢
    have hfieldDeepFuel :
        leafProbeFuel fieldDefinition.outputType
          + selectionSetDeepProbeFuel schema
            fieldDefinition.outputType.namedType childSelectionSet
          + 1 ≤ fuel := by
      have hlocal :=
        selectionSetDeepProbeFuel_field_mem schema parentType selectionSet
          responseName fieldName arguments directives childSelectionSet
          fieldDefinition hmem hlookup
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
        selectionSetNormal schema fieldDefinition.outputType.namedType
          childSelectionSet :=
      selectionSetNormal_field_child_of_mem_lookup hnormal hmem hlookup
    by_cases hreturnObject :
        objectTypeNameBool schema fieldDefinition.outputType.namedType = true
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
            (fieldPairPathLocalNextSelectionSet schema parentType
              fieldDefinition.outputType.namedType fieldName arguments
              currentSelectionSet) :=
        hsupport.fieldPairPathLocalNextSelectionSet_of_object_output
          hparentObject hreturnObject hlookup rfl
      have hchildContext :
          PathLocalSelectionSetCurrentContext childSelectionSet
            (fieldPairPathLocalNextSelectionSet schema parentType
              fieldDefinition.outputType.namedType fieldName arguments
              currentSelectionSet) :=
        PathLocalSelectionSetCurrentContext.fieldPairPathLocalNextSelectionSet_field_child
          (schema := schema) (currentRuntimeType := parentType)
          (childRuntimeType := fieldDefinition.outputType.namedType)
          (targetField := fieldName) (responseName := responseName)
          (targetArguments := arguments) (arguments := arguments)
          (directives := directives) (selectionSet := selectionSet)
          (childSelectionSet := childSelectionSet)
          (currentSelectionSet := currentSelectionSet)
          hcontext hmem (argumentsEquivalent_refl_forSyntaxDiff arguments)
          hpruned
      rcases
          executeSelectionSetAsResponse_fieldPairOrDeepSuccess_pathLocalProbe_tagged_of_valid_normal_support_context_fuel_ge_size
            schema rootSelectionSet leftInitialSelectionSet
            rightInitialSelectionSet variableValues hschema n
            fieldDefinition.outputType.namedType variableDefinitions
            childSelectionSet childFuel
            fieldDefinition.outputType.namedType targetParent leftField
            rightField leftArguments rightArguments leftRuntime rightRuntime
            tag
            (fieldPairPathLocalNextSelectionSet schema parentType
              fieldDefinition.outputType.namedType fieldName arguments
              currentSelectionSet)
            hchildSize hchildFuel hchildValid hchildFree hchildNormal
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
      refine
        Or.inr
          ⟨fieldDefinition.outputType.namedType, responseFields, errors,
            ?_, ?_⟩
      · exact Or.inl ⟨hreturnObject, rfl⟩
      · exact ⟨hchildInclude, by
          simpa [hchildFuelEq] using hchildResponse⟩
    · have hreturnNonObject :
          objectTypeNameBool schema
              fieldDefinition.outputType.namedType = false := by
        cases h :
            objectTypeNameBool schema fieldDefinition.outputType.namedType <;>
          simp [h] at hreturnObject ⊢
      have hsound :
          PathLocalCurrentRuntimeSound schema
            (parentType, currentSelectionSet) :=
        hsupport.sound
      have hready :
          PathLocalSelectionSetHeadReady schema parentType
            currentSelectionSet selectionSet :=
        PathLocalSelectionSetCurrentContext.headReady_of_valid_normal
          hsound hcontext hvalid hnormal
      rcases
          hready responseName fieldName arguments directives childSelectionSet
            fieldDefinition hmem hlookup hreturnComposite hreturnNonObject with
        ⟨childRuntimeType, hruntime, hchildInclude⟩
      have hchildObject :
          objectTypeNameBool schema childRuntimeType = true :=
        objectTypeNameBool_of_typeIncludesObjectBool hschema hchildInclude
      have hchildNonempty : childSelectionSet ≠ [] := by
        rcases
            selectionSetValid_field_lookup_leaf_or_composite_child hvalid
              hmem with
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
            (fieldPairPathLocalNextSelectionSet schema parentType
              childRuntimeType fieldName arguments currentSelectionSet) :=
        hsupport.fieldPairPathLocalNextSelectionSet_of_abstract_output
          hparentObject hchildObject hlookup hreturnComposite hchildInclude
      rcases
          executeSelectionSetAsResponse_fieldPairOrDeepSuccess_pathLocalProbe_tagged_of_valid_normal_support_context_fuel_ge_size
            schema rootSelectionSet leftInitialSelectionSet
            rightInitialSelectionSet variableValues hschema n
            fieldDefinition.outputType.namedType variableDefinitions
            childSelectionSet childFuel childRuntimeType targetParent
            leftField rightField leftArguments rightArguments leftRuntime
            rightRuntime tag
            (fieldPairPathLocalNextSelectionSet schema parentType
              childRuntimeType fieldName arguments currentSelectionSet)
            hchildSize hchildFuel hchildValid hchildFree hchildNormal
            hchildInclude hchildSupport
            (fun hchildParentObject => by
              rw [hreturnNonObject] at hchildParentObject
              simp at hchildParentObject)
            (by
              intro _hchildParentNonObject
              intro bodyDirectives bodySelectionSet hbodyMem
              exact
                PathLocalSelectionSetCurrentContext.fieldPairPathLocalNextSelectionSet_inlineFragment_body
                  (schema := schema)
                  (currentRuntimeType := parentType)
                  (childRuntimeType := childRuntimeType)
                  (childParentType := fieldDefinition.outputType.namedType)
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
      refine
        Or.inr ⟨childRuntimeType, responseFields, errors, ?_, ?_⟩
      · exact Or.inr ⟨hreturnComposite, hreturnNonObject, hruntime⟩
      · exact ⟨hchildInclude, by
          simpa [hchildFuelEq] using hchildResponse⟩

theorem NormalSelectionSetObservableLeaf.mono
    {schema : Schema} {parentType : Name}
    {selectionSet superSet : List Selection}
    : (∀ selection, selection ∈ selectionSet -> selection ∈ superSet)
      -> NormalSelectionSetObservableLeaf schema parentType selectionSet
      -> NormalSelectionSetObservableLeaf schema parentType superSet := by
  intro hsubset hleaf
  cases hleaf with
  | objectLeaf hobject hmem hlookup hleaf =>
      exact
        NormalSelectionSetObservableLeaf.objectLeaf hobject
          (hsubset _ hmem) hlookup hleaf
  | objectChild hobject hmem hlookup hcomposite hchild =>
      exact
        NormalSelectionSetObservableLeaf.objectChild hobject
          (hsubset _ hmem) hlookup hcomposite hchild
  | abstractInlineFragment hnonObject hmem hchild =>
      exact
        NormalSelectionSetObservableLeaf.abstractInlineFragment hnonObject
          (hsubset _ hmem) hchild

theorem NormalSelectionSetObservableLeaf.append_context
    {schema : Schema} {parentType : Name}
    {selectionSet : List Selection} {pref suff : List Selection}
    : NormalSelectionSetObservableLeaf schema parentType selectionSet
      -> NormalSelectionSetObservableLeaf schema parentType
          (pref ++ selectionSet ++ suff) := by
  intro hleaf
  exact
    hleaf.mono (fun selection hmem =>
      List.mem_append.mpr
        (Or.inl (List.mem_append.mpr (Or.inr hmem))))

theorem normalSelectionSetObservableLeaf_of_firstFieldChildByHead?_field_mem
    {schema : Schema} {childParentType targetField responseName : Name}
    {targetArguments arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    : Selection.field responseName targetField arguments directives childSelectionSet
        ∈ selectionSet
      -> Argument.argumentsEquivalent arguments targetArguments
      -> NormalSelectionSetObservableLeaf schema childParentType childSelectionSet
      -> ∃ mergedSelectionSet,
          firstFieldChildByHead? targetField targetArguments selectionSet
            = some mergedSelectionSet
          ∧ NormalSelectionSetObservableLeaf schema childParentType
              mergedSelectionSet := by
  intro hmem harguments hleaf
  rcases
      firstFieldChildByHead?_field_mem_append_context
        hmem harguments with
    ⟨mergedSelectionSet, pref, suff, hmerged, hcontext⟩
  refine ⟨mergedSelectionSet, hmerged, ?_⟩
  rw [hcontext]
  exact hleaf.append_context

theorem normalSelectionSetObservableLeaf_of_firstFieldChildByHeadAtRuntime?_field_mem
    {schema : Schema}
    {currentRuntimeType childRuntimeType targetField responseName : Name}
    {targetArguments arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    : Selection.field responseName targetField arguments directives childSelectionSet
        ∈ selectionSet
      -> Argument.argumentsEquivalent arguments targetArguments
      -> NormalSelectionSetObservableLeaf schema childRuntimeType
          (runtimePrunedSelectionSet schema childRuntimeType childSelectionSet)
      -> ∃ mergedSelectionSet,
          firstFieldChildByHeadAtRuntime? schema currentRuntimeType
              childRuntimeType targetField targetArguments selectionSet
            = some mergedSelectionSet
          ∧ NormalSelectionSetObservableLeaf schema childRuntimeType
              mergedSelectionSet := by
  intro hmem harguments hleaf
  rcases
      firstFieldChildByHeadAtRuntime?_field_mem_append_context
        (schema := schema) (currentRuntimeType := currentRuntimeType)
        (childRuntimeType := childRuntimeType)
        (targetField := targetField) hmem harguments with
    ⟨mergedSelectionSet, pref, suff, hmerged, hcontext⟩
  refine ⟨mergedSelectionSet, hmerged, ?_⟩
  rw [hcontext]
  exact hleaf.append_context

theorem normalSelectionSetObservableLeaf_of_fieldPairPathLocalNextSelectionSet_field_mem
    {schema : Schema}
    {currentRuntimeType childRuntimeType targetField responseName : Name}
    {targetArguments arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    : Selection.field responseName targetField arguments directives childSelectionSet
        ∈ selectionSet
      -> Argument.argumentsEquivalent arguments targetArguments
      -> NormalSelectionSetObservableLeaf schema childRuntimeType
          (runtimePrunedSelectionSet schema childRuntimeType childSelectionSet)
      -> NormalSelectionSetObservableLeaf schema childRuntimeType
          (fieldPairPathLocalNextSelectionSet schema currentRuntimeType
            childRuntimeType targetField targetArguments selectionSet) := by
  intro hmem harguments hleaf
  rcases
      normalSelectionSetObservableLeaf_of_firstFieldChildByHeadAtRuntime?_field_mem
        (schema := schema) (currentRuntimeType := currentRuntimeType)
        (childRuntimeType := childRuntimeType)
        (targetField := targetField) hmem harguments hleaf with
    ⟨mergedSelectionSet, hmerged, hmergedLeaf⟩
  have hnext :
      fieldPairPathLocalNextSelectionSet schema currentRuntimeType
          childRuntimeType targetField targetArguments selectionSet =
        mergedSelectionSet := by
    simp [fieldPairPathLocalNextSelectionSet, hmerged]
  simpa [hnext] using hmergedLeaf

theorem normalSelectionSetObservableLeaf_of_valid_normal_composite_field_mem
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType responseName fieldName : Name}
    {arguments : List Argument} {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
    : Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> NormalSelectionSetObservableLeaf schema
          fieldDefinition.outputType.namedType childSelectionSet := by
  intro hvalid hnormal hmem hlookup hcomposite
  rcases selectionSetValid_field_lookup_leaf_or_composite_child hvalid
      hmem with
    ⟨candidateDefinition, hcandidateLookup, hkind⟩
  have hcandidateEq : candidateDefinition = fieldDefinition := by
    rw [hlookup] at hcandidateLookup
    exact Option.some.inj hcandidateLookup.symm
  subst candidateDefinition
  rcases hkind with hleaf | hcompositeKind
  · rw [hcomposite] at hleaf
    simp at hleaf
  · have hchildNormal :
        selectionSetNormal schema fieldDefinition.outputType.namedType
          childSelectionSet :=
      selectionSetNormal_field_child_of_mem_lookup hnormal hmem hlookup
    exact
      normalSelectionSetObservableLeaf_of_valid_normal_nonempty schema
        fieldDefinition.outputType.namedType variableDefinitions
        childSelectionSet hcompositeKind.2.2 hchildNormal
        hcompositeKind.2.1

theorem normalSelectionSetObservableLeaf_of_fieldPairPathLocalNextSelectionSet_object_output_of_valid_normal_field_mem
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {currentRuntimeType responseName fieldName : Name}
    {targetArguments arguments : List Argument} {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection} {fieldDefinition : FieldDefinition}
    : Validation.selectionSetValid schema variableDefinitions currentRuntimeType
        selectionSet
      -> selectionSetNormal schema currentRuntimeType selectionSet
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> Argument.argumentsEquivalent arguments targetArguments
      -> schema.lookupField currentRuntimeType fieldName = some fieldDefinition
      -> objectTypeNameBool schema fieldDefinition.outputType.namedType = true
      -> NormalSelectionSetObservableLeaf schema
          fieldDefinition.outputType.namedType
          (fieldPairPathLocalNextSelectionSet schema currentRuntimeType
            fieldDefinition.outputType.namedType fieldName targetArguments
            selectionSet) := by
  intro hvalid hnormal hmem harguments hlookup hobject
  have hcomposite :
      (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool
        schema = true :=
    typeRef_named_isCompositeBool_true_of_objectTypeNameBool hobject
  have hchildLeaf :
      NormalSelectionSetObservableLeaf schema
        fieldDefinition.outputType.namedType childSelectionSet :=
    normalSelectionSetObservableLeaf_of_valid_normal_composite_field_mem
      hvalid hnormal hmem hlookup hcomposite
  have hchildNormal :
      selectionSetNormal schema fieldDefinition.outputType.namedType
        childSelectionSet :=
    selectionSetNormal_field_child_of_mem_lookup hnormal hmem hlookup
  have hallFields : selectionsAllFields childSelectionSet :=
    selectionSetNormal_allFields_of_object hchildNormal hobject
  have hpruned :
      runtimePrunedSelectionSet schema fieldDefinition.outputType.namedType
          childSelectionSet =
        childSelectionSet :=
    runtimePrunedSelectionSet_eq_self_of_allFields schema
      fieldDefinition.outputType.namedType hallFields
  exact
    normalSelectionSetObservableLeaf_of_fieldPairPathLocalNextSelectionSet_field_mem
      (schema := schema) (currentRuntimeType := currentRuntimeType)
      (childRuntimeType := fieldDefinition.outputType.namedType)
      (targetField := fieldName) hmem harguments (by
        simpa [hpruned] using hchildLeaf)

theorem normalSelectionSetObservableLeaf_of_valid_normal_fieldName_composite_mem
    {schema : Schema}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    {parentType responseName leftFieldName rightFieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet left right : List Selection}
    {leftFieldDefinition rightFieldDefinition : FieldDefinition}
    : Validation.selectionSetValid schema leftVariableDefinitions parentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> Selection.field responseName leftFieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName rightFieldName rightArguments rightDirectives
            rightChildSelectionSet
          ∈ right
      -> schema.lookupField parentType leftFieldName = some leftFieldDefinition
      -> schema.lookupField parentType rightFieldName = some rightFieldDefinition
      -> ((TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool schema
            = true
          ∨ (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool
              schema
            = true)
      -> NormalSelectionSetObservableLeaf schema
            leftFieldDefinition.outputType.namedType leftChildSelectionSet
          ∨ NormalSelectionSetObservableLeaf schema
              rightFieldDefinition.outputType.namedType rightChildSelectionSet := by
  intro hleftValid hrightValid hleftNormal hrightNormal hleftMem hrightMem
    hleftLookup hrightLookup hcomposite
  rcases hcomposite with hleftComposite | hrightComposite
  · exact
      Or.inl
        (normalSelectionSetObservableLeaf_of_valid_normal_composite_field_mem
          hleftValid hleftNormal hleftMem hleftLookup hleftComposite)
  · exact
      Or.inr
        (normalSelectionSetObservableLeaf_of_valid_normal_composite_field_mem
          hrightValid hrightNormal hrightMem hrightLookup hrightComposite)

theorem normalSelectionSetObservableLeaf_pair_of_valid_normal_arguments_composite_mem
    {schema : Schema}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    {parentType responseName fieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet left right : List Selection}
    {fieldDefinition : FieldDefinition}
    : Validation.selectionSetValid schema leftVariableDefinitions parentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> Selection.field responseName fieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName fieldName rightArguments rightDirectives
            rightChildSelectionSet
          ∈ right
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> NormalSelectionSetObservableLeaf schema
            fieldDefinition.outputType.namedType leftChildSelectionSet
          ∧ NormalSelectionSetObservableLeaf schema
              fieldDefinition.outputType.namedType rightChildSelectionSet := by
  intro hleftValid hrightValid hleftNormal hrightNormal hleftMem hrightMem
    hlookup hcomposite
  exact
    ⟨normalSelectionSetObservableLeaf_of_valid_normal_composite_field_mem
        hleftValid hleftNormal hleftMem hlookup hcomposite,
      normalSelectionSetObservableLeaf_of_valid_normal_composite_field_mem
        hrightValid hrightNormal hrightMem hlookup hcomposite⟩

theorem not_fieldProbeTarget_of_fieldName_ne
    {targetParent leftField rightField : Name}
    {leftArguments arguments : List Argument}
    : leftField ≠ rightField
      -> ¬ fieldProbeTarget targetParent leftField leftArguments targetParent
            rightField arguments := by
  intro hfieldDiff htarget
  exact hfieldDiff htarget.2.1.symm

theorem not_fieldProbeTarget_of_arguments_not_equivalent
    {targetParent fieldName : Name}
    {leftArguments rightArguments arguments : List Argument}
    : ¬ Argument.argumentsEquivalent leftArguments rightArguments
      -> Argument.argumentsEquivalent arguments rightArguments
      -> ¬ fieldProbeTarget targetParent fieldName leftArguments targetParent
            fieldName arguments := by
  intro hargumentsDiff hrightArgs hleftTarget
  rcases hleftTarget with ⟨_hparent, _hfield, hleftArgs⟩
  exact hargumentsDiff
    (argumentsEquivalent_trans
      (FieldMerge.argumentsEquivalent_symm hleftArgs) hrightArgs)

theorem responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_taggedPair
    {schema : Schema}
    {rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection}
    {variableValues : Execution.VariableValues} {leftFuel rightFuel : Nat}
    {leftParentType rightParentType leftRuntime rightRuntime targetParent
      leftField rightField
      : Name}
    {leftArguments rightArguments : List Argument}
    {leftCurrentSelectionSet rightCurrentSelectionSet left right : List Selection}
    : ¬ Execution.ResponseValue.semanticEquivalent
          (Execution.executeSelectionSetAsResponse schema
            (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
              rightInitialSelectionSet targetParent leftField rightField
              leftArguments rightArguments leftRuntime rightRuntime)
            variableValues leftFuel leftParentType
            (.object leftRuntime
              (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                leftCurrentSelectionSet))
            left).data
          (Execution.executeSelectionSetAsResponse schema
            (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
              rightInitialSelectionSet targetParent leftField rightField
              leftArguments rightArguments leftRuntime rightRuntime)
            variableValues rightFuel rightParentType
            (.object rightRuntime
              (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                rightCurrentSelectionSet))
            right).data
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet targetParent leftField rightField
                  leftArguments rightArguments leftRuntime rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues leftFuel leftParentType
              (projectionTargetResolverValue
                (.object leftRuntime
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                    leftCurrentSelectionSet)))
              left).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet targetParent leftField rightField
                  leftArguments rightArguments leftRuntime rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues rightFuel rightParentType
              (projectionTargetResolverValue
                (.object rightRuntime
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                    rightCurrentSelectionSet)))
              right).data := by
  intro hraw hsemantic
  have hleftProjection :=
    executeSelectionSetAsResponse_fieldPairOrDeepSuccessResolvers_projectionTargetResolverValue
      schema rootSelectionSet
      (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
        rightInitialSelectionSet targetParent leftField rightField
        leftArguments rightArguments leftRuntime rightRuntime)
      variableValues leftFuel targetParent leftField rightField
      leftArguments rightArguments leftParentType
      (.object leftRuntime
        (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
          leftCurrentSelectionSet))
      left
  have hrightProjection :=
    executeSelectionSetAsResponse_fieldPairOrDeepSuccessResolvers_projectionTargetResolverValue
      schema rootSelectionSet
      (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
        rightInitialSelectionSet targetParent leftField rightField
        leftArguments rightArguments leftRuntime rightRuntime)
      variableValues rightFuel targetParent leftField rightField
      leftArguments rightArguments rightParentType
      (.object rightRuntime
        (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
          rightCurrentSelectionSet))
      right
  exact hraw (by
    simpa [hleftProjection, hrightProjection] using hsemantic)

theorem executeField_fieldPairOrDeepSuccess_pathLocalProbe_other_root_ok_of_deepSuccessWithRef_ok
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (variableValues : Execution.VariableValues) (parentFuel : Nat)
    (targetParent leftField rightField : Name)
    (leftArguments rightArguments arguments : List Argument)
    (leftRuntime rightRuntime : Name) (responseName fieldName : Name)
    (childSelectionSet : List Selection) (responseValue : Execution.ResponseValue)
    (fieldErrors : Nat)
    : ¬ fieldPairProjectionTarget targetParent leftField rightField
          leftArguments rightArguments targetParent fieldName arguments
      -> Execution.executeField schema
            (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet
              (ProjectionResolverRef.filler
                : ProjectionResolverRef FieldPairPathLocalProbeRef))
            variableValues parentFuel
            (projectionRootResolverValue
              (.object targetParent FieldPairPathLocalProbeRef.root))
            responseName
            [{
              parentType := targetParent,
              responseName := responseName,
              fieldName := fieldName,
              arguments := arguments,
              selectionSet := childSelectionSet
            }]
          = .ok ([(responseName, responseValue)], fieldErrors)
      -> Execution.executeField schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet targetParent leftField rightField
                leftArguments rightArguments leftRuntime rightRuntime)
              targetParent leftField rightField leftArguments rightArguments)
            variableValues parentFuel
            (projectionRootResolverValue
              (.object targetParent FieldPairPathLocalProbeRef.root))
            responseName
            [{
              parentType := targetParent,
              responseName := responseName,
              fieldName := fieldName,
              arguments := arguments,
              selectionSet := childSelectionSet
            }]
          = .ok ([(responseName, responseValue)], fieldErrors) := by
  intro hnotProjection hdeep
  simp only [projectionRootResolverValue, projectionResolverValue] at hdeep ⊢
  rw [executeField_fieldPairOrDeepSuccessResolvers_other_root_eq_deepSuccessWithRef
    schema rootSelectionSet
    (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
      rightInitialSelectionSet targetParent leftField rightField
      leftArguments rightArguments leftRuntime rightRuntime)
    variableValues targetParent leftField rightField targetParent
    fieldName targetParent responseName leftArguments rightArguments
    arguments FieldPairPathLocalProbeRef.root childSelectionSet
    hnotProjection parentFuel]
  exact hdeep

theorem selectionSetOtherFieldsExecuteOk_fieldPairOrDeepSuccess_pathLocalProbe_of_deepSuccessWithRef_ok
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (variableValues : Execution.VariableValues) (parentFuel : Nat)
    (targetParent leftField rightField : Name)
    (leftArguments rightArguments : List Argument) (leftRuntime rightRuntime : Name)
    (selectionSet : List Selection)
    : (∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
        -> ∃ responseValue fieldErrors,
            Execution.executeField schema
              (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet
                (ProjectionResolverRef.filler
                  : ProjectionResolverRef FieldPairPathLocalProbeRef))
              variableValues parentFuel
              (projectionRootResolverValue
                (.object targetParent FieldPairPathLocalProbeRef.root))
              responseName
              [{
                parentType := targetParent,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet := childSelectionSet
              }]
            = .ok ([(responseName, responseValue)], fieldErrors))
      -> ∀ responseName fieldName arguments directives childSelectionSet,
          Selection.field responseName fieldName arguments directives childSelectionSet
            ∈ selectionSet
          -> ¬ fieldPairProjectionTarget targetParent leftField rightField
                leftArguments rightArguments targetParent fieldName arguments
          -> ∃ responseValue fieldErrors,
              Execution.executeField schema
                (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                  (fieldPairPathLocalProbeResolvers schema
                    leftInitialSelectionSet rightInitialSelectionSet
                    targetParent leftField rightField leftArguments
                    rightArguments leftRuntime rightRuntime)
                  targetParent leftField rightField leftArguments
                  rightArguments)
                variableValues parentFuel
                (projectionRootResolverValue
                  (.object targetParent FieldPairPathLocalProbeRef.root))
                responseName
                [{
                  parentType := targetParent,
                  responseName := responseName,
                  fieldName := fieldName,
                  arguments := arguments,
                  selectionSet := childSelectionSet
                }]
              = .ok ([(responseName, responseValue)], fieldErrors) := by
  intro hdeep responseName fieldName arguments directives childSelectionSet
    hmem hnotProjection
  rcases hdeep responseName fieldName arguments directives childSelectionSet
      hmem with
    ⟨responseValue, fieldErrors, hdeepOk⟩
  exact
    ⟨responseValue, fieldErrors,
      executeField_fieldPairOrDeepSuccess_pathLocalProbe_other_root_ok_of_deepSuccessWithRef_ok
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet variableValues parentFuel targetParent
        leftField rightField leftArguments rightArguments arguments
        leftRuntime rightRuntime responseName fieldName childSelectionSet
        responseValue fieldErrors hnotProjection hdeepOk⟩

theorem not_selectionSetsDataEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_root_arguments_child_response_diff_of_field_ok
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
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
              (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet parentType fieldName fieldName
                leftArguments rightArguments leftRuntime rightRuntime)
              parentType fieldName fieldName leftArguments rightArguments)
            variableValues
            (parentFuel - leafProbeFuel fieldDefinition.outputType)
            leftRuntime
            (projectionTargetResolverValue
              (.object leftRuntime
                (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                  leftInitialSelectionSet)))
            leftChildSelectionSet
          = ({
                data := Execution.ResponseValue.object leftChildFields,
                errors := leftChildErrors
              }
              : Execution.Response)
      -> Execution.executeSelectionSetAsResponse schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet parentType fieldName fieldName
                leftArguments rightArguments leftRuntime rightRuntime)
              parentType fieldName fieldName leftArguments rightArguments)
            variableValues
            (parentFuel - leafProbeFuel fieldDefinition.outputType)
            rightRuntime
            (projectionTargetResolverValue
              (.object rightRuntime
                (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                  rightInitialSelectionSet)))
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
                    (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                      rightInitialSelectionSet parentType fieldName fieldName
                      leftArguments rightArguments leftRuntime rightRuntime)
                    parentType fieldName fieldName leftArguments rightArguments)
                  variableValues (parentFuel + 1)
                  (projectionRootResolverValue
                    (.object parentType FieldPairPathLocalProbeRef.root))
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
                    (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                      rightInitialSelectionSet parentType fieldName fieldName
                      leftArguments rightArguments leftRuntime rightRuntime)
                    parentType fieldName fieldName leftArguments rightArguments)
                  variableValues (parentFuel + 1)
                  (projectionRootResolverValue
                    (.object parentType FieldPairPathLocalProbeRef.root))
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
      (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
        rightInitialSelectionSet parentType fieldName fieldName
        leftArguments rightArguments leftRuntime rightRuntime)
      parentType fieldName fieldName leftArguments rightArguments
  let source :=
    projectionRootResolverValue
      (.object parentType FieldPairPathLocalProbeRef.root)
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
              (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet parentType fieldName fieldName
                leftArguments rightArguments leftRuntime rightRuntime)
              parentType fieldName fieldName leftArguments rightArguments)
            variableValues
            (parentFuel - leafProbeFuel fieldDefinition.outputType)
            (projectionTargetResolverValue
              (.object leftRuntime
                (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                  leftInitialSelectionSet)))
            (Execution.collectFields schema variableValues leftRuntime
              (projectionTargetResolverValue
                (.object leftRuntime
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                    leftInitialSelectionSet)))
              leftChildSelectionSet))
        =
        ({ data := Execution.ResponseValue.object leftChildFields,
           errors := leftChildErrors } : Execution.Response) := by
      simpa [Execution.executeSelectionSetAsResponse, Execution.executeSelectionSet,
        Execution.executeRootSelectionSet] using hleftChildResponse
    have hfield :=
      executeField_fieldPairOrDeepSuccess_pathLocalProbe_left_root_response
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet variableValues
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
              (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet parentType fieldName fieldName
                leftArguments rightArguments leftRuntime rightRuntime)
              parentType fieldName fieldName leftArguments rightArguments)
            variableValues
            (parentFuel - leafProbeFuel fieldDefinition.outputType)
            (projectionTargetResolverValue
              (.object rightRuntime
                (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                  rightInitialSelectionSet)))
            (Execution.collectFields schema variableValues rightRuntime
              (projectionTargetResolverValue
                (.object rightRuntime
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                    rightInitialSelectionSet)))
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
      executeField_fieldPairOrDeepSuccess_pathLocalProbe_right_root_response_of_not_left
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet variableValues
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
  have hsource :
      ∃ runtimeType ref,
        source = Execution.ResolverValue.object runtimeType ref
          ∧ schema.typeIncludesObjectBool parentType runtimeType = true := by
    refine
      ⟨parentType, ProjectionResolverRef.root FieldPairPathLocalProbeRef.root,
        ?_, typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject⟩
    simp [source, projectionRootResolverValue, projectionResolverValue]
  exact
    SemanticSeparation.not_selectionSetsDataEquivalent_of_responseName_value_diff_of_field_ok
      resolvers variableValues (parentFuel + 1) source hsource hobject
      hleftNormal hrightNormal hleftFree hrightFree hleftMem hrightMem
      hleftTarget hrightTarget hvalueNot hleftFieldOk hrightFieldOk

theorem not_selectionSetsDataEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_root_fieldName_child_response_diff_of_field_ok
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
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
              (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet parentType leftFieldName rightFieldName
                leftArguments rightArguments leftRuntime rightRuntime)
              parentType leftFieldName rightFieldName leftArguments
              rightArguments)
            variableValues
            (parentFuel - leafProbeFuel leftFieldDefinition.outputType)
            leftRuntime
            (projectionTargetResolverValue
              (.object leftRuntime
                (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                  leftInitialSelectionSet)))
            leftChildSelectionSet
          = ({
                data := Execution.ResponseValue.object leftChildFields,
                errors := leftChildErrors
              }
              : Execution.Response)
      -> Execution.executeSelectionSetAsResponse schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet parentType leftFieldName rightFieldName
                leftArguments rightArguments leftRuntime rightRuntime)
              parentType leftFieldName rightFieldName leftArguments
              rightArguments)
            variableValues
            (parentFuel - leafProbeFuel rightFieldDefinition.outputType)
            rightRuntime
            (projectionTargetResolverValue
              (.object rightRuntime
                (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                  rightInitialSelectionSet)))
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
                    (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                      rightInitialSelectionSet parentType leftFieldName
                      rightFieldName leftArguments rightArguments leftRuntime
                      rightRuntime)
                    parentType leftFieldName rightFieldName leftArguments
                    rightArguments)
                  variableValues (parentFuel + 1)
                  (projectionRootResolverValue
                    (.object parentType FieldPairPathLocalProbeRef.root))
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
                    (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                      rightInitialSelectionSet parentType leftFieldName
                      rightFieldName leftArguments rightArguments leftRuntime
                      rightRuntime)
                    parentType leftFieldName rightFieldName leftArguments
                    rightArguments)
                  variableValues (parentFuel + 1)
                  (projectionRootResolverValue
                    (.object parentType FieldPairPathLocalProbeRef.root))
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
    hrightChildResponse hchildNot hleftFieldOk hrightFieldOk
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet
      (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
        rightInitialSelectionSet parentType leftFieldName rightFieldName
        leftArguments rightArguments leftRuntime rightRuntime)
      parentType leftFieldName rightFieldName leftArguments rightArguments
  let source :=
    projectionRootResolverValue
      (.object parentType FieldPairPathLocalProbeRef.root)
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
              (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet parentType leftFieldName
                rightFieldName leftArguments rightArguments leftRuntime
                rightRuntime)
              parentType leftFieldName rightFieldName leftArguments
              rightArguments)
            variableValues
            (parentFuel - leafProbeFuel leftFieldDefinition.outputType)
            (projectionTargetResolverValue
              (.object leftRuntime
                (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                  leftInitialSelectionSet)))
            (Execution.collectFields schema variableValues leftRuntime
              (projectionTargetResolverValue
                (.object leftRuntime
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                    leftInitialSelectionSet)))
              leftChildSelectionSet))
        =
        ({ data := Execution.ResponseValue.object leftChildFields,
           errors := leftChildErrors } : Execution.Response) := by
      simpa [Execution.executeSelectionSetAsResponse, Execution.executeSelectionSet,
        Execution.executeRootSelectionSet] using hleftChildResponse
    have hfield :=
      executeField_fieldPairOrDeepSuccess_pathLocalProbe_left_root_response
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet variableValues
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
              (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet parentType leftFieldName
                rightFieldName leftArguments rightArguments leftRuntime
                rightRuntime)
              parentType leftFieldName rightFieldName leftArguments
              rightArguments)
            variableValues
            (parentFuel - leafProbeFuel rightFieldDefinition.outputType)
            (projectionTargetResolverValue
              (.object rightRuntime
                (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                  rightInitialSelectionSet)))
            (Execution.collectFields schema variableValues rightRuntime
              (projectionTargetResolverValue
                (.object rightRuntime
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                    rightInitialSelectionSet)))
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
      executeField_fieldPairOrDeepSuccess_pathLocalProbe_right_root_response_of_not_left
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet variableValues
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
  have hsource :
      ∃ runtimeType ref,
        source = Execution.ResolverValue.object runtimeType ref
          ∧ schema.typeIncludesObjectBool parentType runtimeType = true := by
    refine
      ⟨parentType, ProjectionResolverRef.root FieldPairPathLocalProbeRef.root,
        ?_, typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject⟩
    simp [source, projectionRootResolverValue, projectionResolverValue]
  exact
    SemanticSeparation.not_selectionSetsDataEquivalent_of_responseName_value_diff_of_field_ok
      resolvers variableValues (parentFuel + 1) source hsource hobject
      hleftNormal hrightNormal hleftFree hrightFree hleftMem hrightMem
      hleftTarget hrightTarget hvalueNot hleftFieldOk hrightFieldOk

theorem not_selectionSetsDataEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_root_arguments_child_response_diff_of_field_cases
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
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
              (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet parentType fieldName fieldName
                leftArguments rightArguments leftRuntime rightRuntime)
              parentType fieldName fieldName leftArguments rightArguments)
            variableValues
            (parentFuel - leafProbeFuel fieldDefinition.outputType)
            leftRuntime
            (projectionTargetResolverValue
              (.object leftRuntime
                (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                  leftInitialSelectionSet)))
            leftChildSelectionSet
          = ({
                data := Execution.ResponseValue.object leftChildFields,
                errors := leftChildErrors
              }
              : Execution.Response)
      -> Execution.executeSelectionSetAsResponse schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet parentType fieldName fieldName
                leftArguments rightArguments leftRuntime rightRuntime)
              parentType fieldName fieldName leftArguments rightArguments)
            variableValues
            (parentFuel - leafProbeFuel fieldDefinition.outputType)
            rightRuntime
            (projectionTargetResolverValue
              (.object rightRuntime
                (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                  rightInitialSelectionSet)))
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
                    (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                      rightInitialSelectionSet parentType fieldName fieldName
                      leftArguments rightArguments leftRuntime rightRuntime)
                    parentType fieldName fieldName leftArguments rightArguments)
                  variableValues
                  (parentFuel - leafProbeFuel fieldDefinition.outputType)
                  leftRuntime
                  (projectionTargetResolverValue
                    (.object leftRuntime
                      (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                        leftInitialSelectionSet)))
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
                    (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                      rightInitialSelectionSet parentType fieldName fieldName
                      leftArguments rightArguments leftRuntime rightRuntime)
                    parentType fieldName fieldName leftArguments rightArguments)
                  variableValues
                  (parentFuel - leafProbeFuel fieldDefinition.outputType)
                  rightRuntime
                  (projectionTargetResolverValue
                    (.object rightRuntime
                      (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                        rightInitialSelectionSet)))
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
                    (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                      rightInitialSelectionSet parentType fieldName fieldName
                      leftArguments rightArguments leftRuntime rightRuntime)
                    parentType fieldName fieldName leftArguments rightArguments)
                  variableValues
                  (parentFuel - leafProbeFuel fieldDefinition.outputType)
                  leftRuntime
                  (projectionTargetResolverValue
                    (.object leftRuntime
                      (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                        leftInitialSelectionSet)))
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
                    (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                      rightInitialSelectionSet parentType fieldName fieldName
                      leftArguments rightArguments leftRuntime rightRuntime)
                    parentType fieldName fieldName leftArguments rightArguments)
                  variableValues
                  (parentFuel - leafProbeFuel fieldDefinition.outputType)
                  rightRuntime
                  (projectionTargetResolverValue
                    (.object rightRuntime
                      (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                        rightInitialSelectionSet)))
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
                      : ProjectionResolverRef FieldPairPathLocalProbeRef))
                  variableValues (parentFuel + 1)
                  (projectionRootResolverValue
                    (.object parentType FieldPairPathLocalProbeRef.root))
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
                      : ProjectionResolverRef FieldPairPathLocalProbeRef))
                  variableValues (parentFuel + 1)
                  (projectionRootResolverValue
                    (.object parentType FieldPairPathLocalProbeRef.root))
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
                (fieldPairPathLocalProbeResolvers schema
                  leftInitialSelectionSet rightInitialSelectionSet parentType
                  fieldName fieldName leftArguments rightArguments
                  leftRuntime rightRuntime)
                parentType fieldName fieldName leftArguments rightArguments)
              variableValues (parentFuel + 1)
              (projectionRootResolverValue
                (.object parentType FieldPairPathLocalProbeRef.root))
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
    selectionSetOtherFieldsExecuteOk_fieldPairOrDeepSuccess_pathLocalProbe_of_deepSuccessWithRef_ok
      schema rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      variableValues (parentFuel + 1) parentType fieldName fieldName
      leftArguments rightArguments leftRuntime rightRuntime left hleftDeep
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
                (fieldPairPathLocalProbeResolvers schema
                  leftInitialSelectionSet rightInitialSelectionSet parentType
                  fieldName fieldName leftArguments rightArguments
                  leftRuntime rightRuntime)
                parentType fieldName fieldName leftArguments rightArguments)
              variableValues (parentFuel + 1)
              (projectionRootResolverValue
                (.object parentType FieldPairPathLocalProbeRef.root))
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
    selectionSetOtherFieldsExecuteOk_fieldPairOrDeepSuccess_pathLocalProbe_of_deepSuccessWithRef_ok
      schema rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      variableValues (parentFuel + 1) parentType fieldName fieldName
      leftArguments rightArguments leftRuntime rightRuntime right hrightDeep
  have hleftFieldOk :
      ∀ responseName siblingFieldName arguments directives childSelectionSet,
        Selection.field responseName siblingFieldName arguments directives
            childSelectionSet ∈ left ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema
                  leftInitialSelectionSet rightInitialSelectionSet parentType
                  fieldName fieldName leftArguments rightArguments
                  leftRuntime rightRuntime)
                parentType fieldName fieldName leftArguments rightArguments)
              variableValues (parentFuel + 1)
              (projectionRootResolverValue
                (.object parentType FieldPairPathLocalProbeRef.root))
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
    selectionSetFieldsExecuteOk_fieldPairOrDeepSuccess_pathLocalProbe_of_field_cases
      schema rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      variableValues parentFuel parentType fieldName fieldName leftArguments
      rightArguments leftRuntime rightRuntime fieldDefinition fieldDefinition
      left hlookup hlookup hleftInclude hrightInclude hfuel hfuel
      hleftLeftTarget hleftRightTarget hleftOther
  have hrightFieldOk :
      ∀ responseName siblingFieldName arguments directives childSelectionSet,
        Selection.field responseName siblingFieldName arguments directives
            childSelectionSet ∈ right ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema
                  leftInitialSelectionSet rightInitialSelectionSet parentType
                  fieldName fieldName leftArguments rightArguments
                  leftRuntime rightRuntime)
                parentType fieldName fieldName leftArguments rightArguments)
              variableValues (parentFuel + 1)
              (projectionRootResolverValue
                (.object parentType FieldPairPathLocalProbeRef.root))
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
    selectionSetFieldsExecuteOk_fieldPairOrDeepSuccess_pathLocalProbe_of_field_cases
      schema rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      variableValues parentFuel parentType fieldName fieldName leftArguments
      rightArguments leftRuntime rightRuntime fieldDefinition fieldDefinition
      right hlookup hlookup hleftInclude hrightInclude hfuel hfuel
      hrightLeftTarget hrightRightTarget hrightOther
  exact
    not_selectionSetsDataEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_root_arguments_child_response_diff_of_field_ok
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet variableValues parentFuel parentType
      responseName fieldName leftArguments rightArguments leftRuntime
      rightRuntime hobject hleftNormal hrightNormal hleftFree hrightFree
      hleftMem hrightMem hlookup hleftInclude hrightInclude hfuel
      hargumentsDiff hleftChildResponse hrightChildResponse hchildNot
      hleftFieldOk hrightFieldOk

theorem not_selectionSetsDataEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_root_fieldName_child_response_diff_of_field_cases
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
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
              (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet parentType leftFieldName rightFieldName
                leftArguments rightArguments leftRuntime rightRuntime)
              parentType leftFieldName rightFieldName leftArguments
              rightArguments)
            variableValues
            (parentFuel - leafProbeFuel leftFieldDefinition.outputType)
            leftRuntime
            (projectionTargetResolverValue
              (.object leftRuntime
                (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                  leftInitialSelectionSet)))
            leftChildSelectionSet
          = ({
                data := Execution.ResponseValue.object leftChildFields,
                errors := leftChildErrors
              }
              : Execution.Response)
      -> Execution.executeSelectionSetAsResponse schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet parentType leftFieldName rightFieldName
                leftArguments rightArguments leftRuntime rightRuntime)
              parentType leftFieldName rightFieldName leftArguments
              rightArguments)
            variableValues
            (parentFuel - leafProbeFuel rightFieldDefinition.outputType)
            rightRuntime
            (projectionTargetResolverValue
              (.object rightRuntime
                (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                  rightInitialSelectionSet)))
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
                    (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                      rightInitialSelectionSet parentType leftFieldName
                      rightFieldName leftArguments rightArguments leftRuntime
                      rightRuntime)
                    parentType leftFieldName rightFieldName leftArguments
                    rightArguments)
                  variableValues
                  (parentFuel - leafProbeFuel leftFieldDefinition.outputType)
                  leftRuntime
                  (projectionTargetResolverValue
                    (.object leftRuntime
                      (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                        leftInitialSelectionSet)))
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
                    (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                      rightInitialSelectionSet parentType leftFieldName
                      rightFieldName leftArguments rightArguments leftRuntime
                      rightRuntime)
                    parentType leftFieldName rightFieldName leftArguments
                    rightArguments)
                  variableValues
                  (parentFuel - leafProbeFuel rightFieldDefinition.outputType)
                  rightRuntime
                  (projectionTargetResolverValue
                    (.object rightRuntime
                      (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                        rightInitialSelectionSet)))
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
                    (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                      rightInitialSelectionSet parentType leftFieldName
                      rightFieldName leftArguments rightArguments leftRuntime
                      rightRuntime)
                    parentType leftFieldName rightFieldName leftArguments
                    rightArguments)
                  variableValues
                  (parentFuel - leafProbeFuel leftFieldDefinition.outputType)
                  leftRuntime
                  (projectionTargetResolverValue
                    (.object leftRuntime
                      (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                        leftInitialSelectionSet)))
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
                    (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                      rightInitialSelectionSet parentType leftFieldName
                      rightFieldName leftArguments rightArguments leftRuntime
                      rightRuntime)
                    parentType leftFieldName rightFieldName leftArguments
                    rightArguments)
                  variableValues
                  (parentFuel - leafProbeFuel rightFieldDefinition.outputType)
                  rightRuntime
                  (projectionTargetResolverValue
                    (.object rightRuntime
                      (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                        rightInitialSelectionSet)))
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
                      : ProjectionResolverRef FieldPairPathLocalProbeRef))
                  variableValues (parentFuel + 1)
                  (projectionRootResolverValue
                    (.object parentType FieldPairPathLocalProbeRef.root))
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
                      : ProjectionResolverRef FieldPairPathLocalProbeRef))
                  variableValues (parentFuel + 1)
                  (projectionRootResolverValue
                    (.object parentType FieldPairPathLocalProbeRef.root))
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
                (fieldPairPathLocalProbeResolvers schema
                  leftInitialSelectionSet rightInitialSelectionSet parentType
                  leftFieldName rightFieldName leftArguments rightArguments
                  leftRuntime rightRuntime)
                parentType leftFieldName rightFieldName leftArguments
                rightArguments)
              variableValues (parentFuel + 1)
              (projectionRootResolverValue
                (.object parentType FieldPairPathLocalProbeRef.root))
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
    selectionSetOtherFieldsExecuteOk_fieldPairOrDeepSuccess_pathLocalProbe_of_deepSuccessWithRef_ok
      schema rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      variableValues (parentFuel + 1) parentType leftFieldName
      rightFieldName leftArguments rightArguments leftRuntime rightRuntime
      left hleftDeep
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
                (fieldPairPathLocalProbeResolvers schema
                  leftInitialSelectionSet rightInitialSelectionSet parentType
                  leftFieldName rightFieldName leftArguments rightArguments
                  leftRuntime rightRuntime)
                parentType leftFieldName rightFieldName leftArguments
                rightArguments)
              variableValues (parentFuel + 1)
              (projectionRootResolverValue
                (.object parentType FieldPairPathLocalProbeRef.root))
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
    selectionSetOtherFieldsExecuteOk_fieldPairOrDeepSuccess_pathLocalProbe_of_deepSuccessWithRef_ok
      schema rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      variableValues (parentFuel + 1) parentType leftFieldName
      rightFieldName leftArguments rightArguments leftRuntime rightRuntime
      right hrightDeep
  have hleftFieldOk :
      ∀ responseName siblingFieldName arguments directives childSelectionSet,
        Selection.field responseName siblingFieldName arguments directives
            childSelectionSet ∈ left ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema
                  leftInitialSelectionSet rightInitialSelectionSet parentType
                  leftFieldName rightFieldName leftArguments rightArguments
                  leftRuntime rightRuntime)
                parentType leftFieldName rightFieldName leftArguments
                rightArguments)
              variableValues (parentFuel + 1)
              (projectionRootResolverValue
                (.object parentType FieldPairPathLocalProbeRef.root))
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
    selectionSetFieldsExecuteOk_fieldPairOrDeepSuccess_pathLocalProbe_of_field_cases
      schema rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      variableValues parentFuel parentType leftFieldName rightFieldName
      leftArguments rightArguments leftRuntime rightRuntime leftFieldDefinition
      rightFieldDefinition left hleftLookup hrightLookup hleftInclude
      hrightInclude hleftFuel hrightFuel hleftLeftTarget hleftRightTarget
      hleftOther
  have hrightFieldOk :
      ∀ responseName siblingFieldName arguments directives childSelectionSet,
        Selection.field responseName siblingFieldName arguments directives
            childSelectionSet ∈ right ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema
                  leftInitialSelectionSet rightInitialSelectionSet parentType
                  leftFieldName rightFieldName leftArguments rightArguments
                  leftRuntime rightRuntime)
                parentType leftFieldName rightFieldName leftArguments
                rightArguments)
              variableValues (parentFuel + 1)
              (projectionRootResolverValue
                (.object parentType FieldPairPathLocalProbeRef.root))
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
    selectionSetFieldsExecuteOk_fieldPairOrDeepSuccess_pathLocalProbe_of_field_cases
      schema rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      variableValues parentFuel parentType leftFieldName rightFieldName
      leftArguments rightArguments leftRuntime rightRuntime leftFieldDefinition
      rightFieldDefinition right hleftLookup hrightLookup hleftInclude
      hrightInclude hleftFuel hrightFuel hrightLeftTarget hrightRightTarget
      hrightOther
  exact
    not_selectionSetsDataEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_root_fieldName_child_response_diff_of_field_ok
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet variableValues parentFuel parentType
      responseName leftFieldName rightFieldName leftArguments rightArguments
      leftRuntime rightRuntime hobject hleftNormal hrightNormal hleftFree
      hrightFree hleftMem hrightMem hleftLookup hrightLookup hleftInclude
      hrightInclude hleftFuel hrightFuel hfieldDiff hleftChildResponse
      hrightChildResponse hchildNot hleftFieldOk hrightFieldOk

theorem not_selectionSetsDataEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_root_arguments_child_data_diff_of_valid_normal_append_context_fuel_ge
    {schema : Schema}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    {parentType responseName fieldName leftRuntime rightRuntime : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet left right : List Selection}
    {fieldDefinition : FieldDefinition} {parentFuel : Nat}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions parentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> objectTypeNameBool schema parentType = true
      -> selectionSetDeepProbeFuel schema parentType (left ++ right) ≤ parentFuel
      -> Selection.field responseName fieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName fieldName rightArguments rightDirectives
            rightChildSelectionSet
          ∈ right
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType leftRuntime
          = true
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType rightRuntime
          = true
      -> ¬ Argument.argumentsEquivalent leftArguments rightArguments
      -> (let rootSelectionSet :=
            [Selection.inlineFragment (some parentType) [] (left ++ right)]
          let leftInitialSelectionSet :=
            fieldPairPathLocalNextSelectionSet schema parentType leftRuntime
              fieldName leftArguments (left ++ right)
          let rightInitialSelectionSet :=
            fieldPairPathLocalNextSelectionSet schema parentType rightRuntime
              fieldName rightArguments (left ++ right)
          let variableValues : Execution.VariableValues := []
          ¬ Execution.ResponseValue.semanticEquivalent
              (Execution.executeSelectionSetAsResponse schema
                (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                  (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                    rightInitialSelectionSet parentType fieldName fieldName
                    leftArguments rightArguments leftRuntime rightRuntime)
                  parentType fieldName fieldName leftArguments rightArguments)
                variableValues (parentFuel - leafProbeFuel fieldDefinition.outputType)
                leftRuntime
                (projectionTargetResolverValue
                  (.object leftRuntime
                    (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                      leftInitialSelectionSet)))
                leftChildSelectionSet).data
              (Execution.executeSelectionSetAsResponse schema
                (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                  (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                    rightInitialSelectionSet parentType fieldName fieldName
                    leftArguments rightArguments leftRuntime rightRuntime)
                  parentType fieldName fieldName leftArguments rightArguments)
                variableValues (parentFuel - leafProbeFuel fieldDefinition.outputType)
                rightRuntime
                (projectionTargetResolverValue
                  (.object rightRuntime
                    (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                      rightInitialSelectionSet)))
                rightChildSelectionSet).data)
      -> ¬ selectionSetsDataEquivalent schema parentType left right := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hparentObject hfuelAppend hleftMem hrightMem hlookup
    hcomposite hleftInclude hrightInclude hargumentsDiff hchildDataNot
  let rootSelectionSet : List Selection :=
    [Selection.inlineFragment (some parentType) [] (left ++ right)]
  let leftInitialSelectionSet : List Selection :=
    fieldPairPathLocalNextSelectionSet schema parentType leftRuntime
      fieldName leftArguments (left ++ right)
  let rightInitialSelectionSet : List Selection :=
    fieldPairPathLocalNextSelectionSet schema parentType rightRuntime
      fieldName rightArguments (left ++ right)
  let variableValues : Execution.VariableValues := []
  have hleftFuel :
      selectionSetDeepProbeFuel schema parentType left ≤ parentFuel := by
    have hlocal := selectionSetDeepProbeFuel_le_append_left
      schema parentType left right
    omega
  have hrightFuel :
      selectionSetDeepProbeFuel schema parentType right ≤ parentFuel := by
    have hlocal := selectionSetDeepProbeFuel_le_append_right
      schema parentType left right
    omega
  have hleafFuel :
      leafProbeFuel fieldDefinition.outputType ≤ parentFuel := by
    have hlocal :=
      leafProbeFuel_le_selectionSetDeepProbeFuel_of_field_mem schema
        parentType (selectionSet := left) (responseName := responseName)
        (fieldName := fieldName) (arguments := leftArguments)
        (directives := leftDirectives)
        (childSelectionSet := leftChildSelectionSet)
        (fieldDefinition := fieldDefinition) hleftMem hlookup
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
  rcases
      executeSelectionSetAsResponse_fieldPairOrDeepSuccess_pathLocalProbe_target_child_of_valid_normal_context_fuel_ge
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet (left ++ right) variableValues hschema
        (variableDefinitions := leftVariableDefinitions)
        (parentType := parentType) (runtimeType := leftRuntime)
        (targetParent := parentType) (leftField := fieldName)
        (rightField := fieldName) (responseName := responseName)
        (fieldName := fieldName) (targetLeftArguments := leftArguments)
        (targetRightArguments := rightArguments)
        (targetArguments := leftArguments) (arguments := leftArguments)
        (directives := leftDirectives) (leftRuntime := leftRuntime)
        (rightRuntime := rightRuntime) (selectionSet := left)
        (childSelectionSet := leftChildSelectionSet)
        (fieldDefinition := fieldDefinition) (fuel := parentFuel)
        (tag := FieldPairProbeTag.left)
        hleftValid hleftFree hleftNormal hparentObject hleftFuel
        hsupport hleftContext hleftMem hlookup hcomposite hleftInclude
        (argumentsEquivalent_refl_forSyntaxDiff leftArguments) with
    ⟨leftChildFields, leftChildErrors, hleftChildResponse⟩
  rcases
      executeSelectionSetAsResponse_fieldPairOrDeepSuccess_pathLocalProbe_target_child_of_valid_normal_context_fuel_ge
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet (left ++ right) variableValues hschema
        (variableDefinitions := rightVariableDefinitions)
        (parentType := parentType) (runtimeType := rightRuntime)
        (targetParent := parentType) (leftField := fieldName)
        (rightField := fieldName) (responseName := responseName)
        (fieldName := fieldName) (targetLeftArguments := leftArguments)
        (targetRightArguments := rightArguments)
        (targetArguments := rightArguments) (arguments := rightArguments)
        (directives := rightDirectives) (leftRuntime := leftRuntime)
        (rightRuntime := rightRuntime) (selectionSet := right)
        (childSelectionSet := rightChildSelectionSet)
        (fieldDefinition := fieldDefinition) (fuel := parentFuel)
        (tag := FieldPairProbeTag.right)
        hrightValid hrightFree hrightNormal hparentObject hrightFuel
        hsupport hrightContext hrightMem hlookup hcomposite hrightInclude
        (argumentsEquivalent_refl_forSyntaxDiff rightArguments) with
    ⟨rightChildFields, rightChildErrors, hrightChildResponse⟩
  have hchildNot :
      ¬ Execution.ResponseValue.semanticEquivalent
        (Execution.ResponseValue.object leftChildFields)
        (Execution.ResponseValue.object rightChildFields) := by
    intro hsemantic
    exact hchildDataNot (by
      simpa [rootSelectionSet, leftInitialSelectionSet,
        rightInitialSelectionSet, variableValues, hleftChildResponse,
        hrightChildResponse] using hsemantic)
  have hleftLeftTarget :
      ∀ responseName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
            childSelectionSet ∈ left ->
        Argument.argumentsEquivalent arguments leftArguments ->
          ∃ childFields childErrors,
            Execution.executeSelectionSetAsResponse schema
                (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                  (fieldPairPathLocalProbeResolvers schema
                    leftInitialSelectionSet rightInitialSelectionSet parentType
                    fieldName fieldName leftArguments rightArguments
                    leftRuntime rightRuntime)
                  parentType fieldName fieldName leftArguments rightArguments)
                variableValues
                (parentFuel - leafProbeFuel fieldDefinition.outputType)
                leftRuntime
                (projectionTargetResolverValue
                  (.object leftRuntime
                    (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                      leftInitialSelectionSet)))
                childSelectionSet =
              ({ data := Execution.ResponseValue.object childFields,
                 errors := childErrors } : Execution.Response) := by
    intro currentResponseName arguments directives childSelectionSet hmem
      harguments
    simpa [rootSelectionSet, leftInitialSelectionSet, variableValues] using
      executeSelectionSetAsResponse_fieldPairOrDeepSuccess_pathLocalProbe_target_child_of_valid_normal_context_fuel_ge
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet (left ++ right) variableValues hschema
        (variableDefinitions := leftVariableDefinitions)
        (parentType := parentType) (runtimeType := leftRuntime)
        (targetParent := parentType) (leftField := fieldName)
        (rightField := fieldName) (responseName := currentResponseName)
        (fieldName := fieldName) (targetLeftArguments := leftArguments)
        (targetRightArguments := rightArguments)
        (targetArguments := leftArguments) (arguments := arguments)
        (directives := directives) (leftRuntime := leftRuntime)
        (rightRuntime := rightRuntime) (selectionSet := left)
        (childSelectionSet := childSelectionSet)
        (fieldDefinition := fieldDefinition) (fuel := parentFuel)
        (tag := FieldPairProbeTag.left)
        hleftValid hleftFree hleftNormal hparentObject hleftFuel
        hsupport hleftContext hmem hlookup hcomposite hleftInclude
        harguments
  have hleftRightTarget :
      ∀ responseName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
            childSelectionSet ∈ left ->
        Argument.argumentsEquivalent arguments rightArguments ->
          ∃ childFields childErrors,
            Execution.executeSelectionSetAsResponse schema
                (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                  (fieldPairPathLocalProbeResolvers schema
                    leftInitialSelectionSet rightInitialSelectionSet parentType
                    fieldName fieldName leftArguments rightArguments
                    leftRuntime rightRuntime)
                  parentType fieldName fieldName leftArguments rightArguments)
                variableValues
                (parentFuel - leafProbeFuel fieldDefinition.outputType)
                rightRuntime
                (projectionTargetResolverValue
                  (.object rightRuntime
                    (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                      rightInitialSelectionSet)))
                childSelectionSet =
              ({ data := Execution.ResponseValue.object childFields,
                 errors := childErrors } : Execution.Response) := by
    intro currentResponseName arguments directives childSelectionSet hmem
      harguments
    simpa [rootSelectionSet, rightInitialSelectionSet, variableValues] using
      executeSelectionSetAsResponse_fieldPairOrDeepSuccess_pathLocalProbe_target_child_of_valid_normal_context_fuel_ge
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet (left ++ right) variableValues hschema
        (variableDefinitions := leftVariableDefinitions)
        (parentType := parentType) (runtimeType := rightRuntime)
        (targetParent := parentType) (leftField := fieldName)
        (rightField := fieldName) (responseName := currentResponseName)
        (fieldName := fieldName) (targetLeftArguments := leftArguments)
        (targetRightArguments := rightArguments)
        (targetArguments := rightArguments) (arguments := arguments)
        (directives := directives) (leftRuntime := leftRuntime)
        (rightRuntime := rightRuntime) (selectionSet := left)
        (childSelectionSet := childSelectionSet)
        (fieldDefinition := fieldDefinition) (fuel := parentFuel)
        (tag := FieldPairProbeTag.right)
        hleftValid hleftFree hleftNormal hparentObject hleftFuel
        hsupport hleftContext hmem hlookup hcomposite hrightInclude
        harguments
  have hrightLeftTarget :
      ∀ responseName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
            childSelectionSet ∈ right ->
        Argument.argumentsEquivalent arguments leftArguments ->
          ∃ childFields childErrors,
            Execution.executeSelectionSetAsResponse schema
                (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                  (fieldPairPathLocalProbeResolvers schema
                    leftInitialSelectionSet rightInitialSelectionSet parentType
                    fieldName fieldName leftArguments rightArguments
                    leftRuntime rightRuntime)
                  parentType fieldName fieldName leftArguments rightArguments)
                variableValues
                (parentFuel - leafProbeFuel fieldDefinition.outputType)
                leftRuntime
                (projectionTargetResolverValue
                  (.object leftRuntime
                    (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                      leftInitialSelectionSet)))
                childSelectionSet =
              ({ data := Execution.ResponseValue.object childFields,
                 errors := childErrors } : Execution.Response) := by
    intro currentResponseName arguments directives childSelectionSet hmem
      harguments
    simpa [rootSelectionSet, leftInitialSelectionSet, variableValues] using
      executeSelectionSetAsResponse_fieldPairOrDeepSuccess_pathLocalProbe_target_child_of_valid_normal_context_fuel_ge
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet (left ++ right) variableValues hschema
        (variableDefinitions := rightVariableDefinitions)
        (parentType := parentType) (runtimeType := leftRuntime)
        (targetParent := parentType) (leftField := fieldName)
        (rightField := fieldName) (responseName := currentResponseName)
        (fieldName := fieldName) (targetLeftArguments := leftArguments)
        (targetRightArguments := rightArguments)
        (targetArguments := leftArguments) (arguments := arguments)
        (directives := directives) (leftRuntime := leftRuntime)
        (rightRuntime := rightRuntime) (selectionSet := right)
        (childSelectionSet := childSelectionSet)
        (fieldDefinition := fieldDefinition) (fuel := parentFuel)
        (tag := FieldPairProbeTag.left)
        hrightValid hrightFree hrightNormal hparentObject hrightFuel
        hsupport hrightContext hmem hlookup hcomposite hleftInclude
        harguments
  have hrightRightTarget :
      ∀ responseName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
            childSelectionSet ∈ right ->
        Argument.argumentsEquivalent arguments rightArguments ->
          ∃ childFields childErrors,
            Execution.executeSelectionSetAsResponse schema
                (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                  (fieldPairPathLocalProbeResolvers schema
                    leftInitialSelectionSet rightInitialSelectionSet parentType
                    fieldName fieldName leftArguments rightArguments
                    leftRuntime rightRuntime)
                  parentType fieldName fieldName leftArguments rightArguments)
                variableValues
                (parentFuel - leafProbeFuel fieldDefinition.outputType)
                rightRuntime
                (projectionTargetResolverValue
                  (.object rightRuntime
                    (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                      rightInitialSelectionSet)))
                childSelectionSet =
              ({ data := Execution.ResponseValue.object childFields,
                 errors := childErrors } : Execution.Response) := by
    intro currentResponseName arguments directives childSelectionSet hmem
      harguments
    simpa [rootSelectionSet, rightInitialSelectionSet, variableValues] using
      executeSelectionSetAsResponse_fieldPairOrDeepSuccess_pathLocalProbe_target_child_of_valid_normal_context_fuel_ge
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet (left ++ right) variableValues hschema
        (variableDefinitions := rightVariableDefinitions)
        (parentType := parentType) (runtimeType := rightRuntime)
        (targetParent := parentType) (leftField := fieldName)
        (rightField := fieldName) (responseName := currentResponseName)
        (fieldName := fieldName) (targetLeftArguments := leftArguments)
        (targetRightArguments := rightArguments)
        (targetArguments := rightArguments) (arguments := arguments)
        (directives := directives) (leftRuntime := leftRuntime)
        (rightRuntime := rightRuntime) (selectionSet := right)
        (childSelectionSet := childSelectionSet)
        (fieldDefinition := fieldDefinition) (fuel := parentFuel)
        (tag := FieldPairProbeTag.right)
        hrightValid hrightFree hrightNormal hparentObject hrightFuel
        hsupport hrightContext hmem hlookup hcomposite hrightInclude
        harguments
  have hleftDeep :
      ∀ responseName siblingFieldName arguments directives childSelectionSet,
        Selection.field responseName siblingFieldName arguments directives
            childSelectionSet ∈ left ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema
              (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet
                (ProjectionResolverRef.filler :
                  ProjectionResolverRef FieldPairPathLocalProbeRef))
              variableValues (parentFuel + 1)
              (projectionRootResolverValue
                (.object parentType FieldPairPathLocalProbeRef.root))
              responseName
              [{
                parentType := parentType,
                responseName := responseName,
                fieldName := siblingFieldName,
                arguments := arguments,
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(responseName, responseValue)], fieldErrors) := by
    intro currentResponseName siblingFieldName arguments directives
      childSelectionSet hmem
    simpa [rootSelectionSet, variableValues] using
      left_selectionSet_deepSuccessFieldOk_append_framed_of_valid_normal_fuel_ge
        (schema := schema) (parentType := parentType)
        (left := left) (right := right)
        (leftVariableDefinitions := leftVariableDefinitions)
        (rightVariableDefinitions := rightVariableDefinitions)
        (ProjectionResolverRef.filler :
          ProjectionResolverRef FieldPairPathLocalProbeRef)
        variableValues
        (projectionRootResolverValue
          (.object parentType FieldPairPathLocalProbeRef.root))
        parentFuel hschema hleftValid hrightValid hleftFree hrightFree
        hleftNormal hrightNormal hparentObject hfuelAppend
        currentResponseName siblingFieldName arguments directives
        childSelectionSet hmem
  have hrightDeep :
      ∀ responseName siblingFieldName arguments directives childSelectionSet,
        Selection.field responseName siblingFieldName arguments directives
            childSelectionSet ∈ right ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema
              (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet
                (ProjectionResolverRef.filler :
                  ProjectionResolverRef FieldPairPathLocalProbeRef))
              variableValues (parentFuel + 1)
              (projectionRootResolverValue
                (.object parentType FieldPairPathLocalProbeRef.root))
              responseName
              [{
                parentType := parentType,
                responseName := responseName,
                fieldName := siblingFieldName,
                arguments := arguments,
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(responseName, responseValue)], fieldErrors) := by
    intro currentResponseName siblingFieldName arguments directives
      childSelectionSet hmem
    simpa [rootSelectionSet, variableValues] using
      right_selectionSet_deepSuccessFieldOk_append_framed_of_valid_normal_fuel_ge
        (schema := schema) (parentType := parentType)
        (left := left) (right := right)
        (leftVariableDefinitions := leftVariableDefinitions)
        (rightVariableDefinitions := rightVariableDefinitions)
        (ProjectionResolverRef.filler :
          ProjectionResolverRef FieldPairPathLocalProbeRef)
        variableValues
        (projectionRootResolverValue
          (.object parentType FieldPairPathLocalProbeRef.root))
        parentFuel hschema hleftValid hrightValid hleftFree hrightFree
        hleftNormal hrightNormal hparentObject hfuelAppend
        currentResponseName siblingFieldName arguments directives
        childSelectionSet hmem
  exact
    not_selectionSetsDataEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_root_arguments_child_response_diff_of_field_cases
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet variableValues parentFuel parentType
      responseName fieldName leftArguments rightArguments leftRuntime
      rightRuntime hparentObject hleftNormal hrightNormal hleftFree
      hrightFree hleftMem hrightMem hlookup hleftInclude hrightInclude
      hleafFuel hargumentsDiff hleftChildResponse hrightChildResponse
      hchildNot hleftLeftTarget hleftRightTarget hrightLeftTarget
      hrightRightTarget hleftDeep hrightDeep

theorem not_selectionSetsDataEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_root_fieldName_child_data_diff_of_valid_normal_append_context_fuel_ge
    {schema : Schema}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    {parentType responseName leftFieldName rightFieldName leftRuntime rightRuntime : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet left right : List Selection}
    {leftFieldDefinition rightFieldDefinition : FieldDefinition} {parentFuel : Nat}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions parentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> objectTypeNameBool schema parentType = true
      -> selectionSetDeepProbeFuel schema parentType (left ++ right) ≤ parentFuel
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
      -> schema.typeIncludesObjectBool leftFieldDefinition.outputType.namedType
            leftRuntime
          = true
      -> schema.typeIncludesObjectBool rightFieldDefinition.outputType.namedType
            rightRuntime
          = true
      -> leftFieldName ≠ rightFieldName
      -> (let rootSelectionSet :=
            [Selection.inlineFragment (some parentType) [] (left ++ right)]
          let leftInitialSelectionSet :=
            fieldPairPathLocalNextSelectionSet schema parentType leftRuntime
              leftFieldName leftArguments (left ++ right)
          let rightInitialSelectionSet :=
            fieldPairPathLocalNextSelectionSet schema parentType rightRuntime
              rightFieldName rightArguments (left ++ right)
          let variableValues : Execution.VariableValues := []
          ¬ Execution.ResponseValue.semanticEquivalent
              (Execution.executeSelectionSetAsResponse schema
                (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                  (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                    rightInitialSelectionSet parentType leftFieldName
                    rightFieldName leftArguments rightArguments leftRuntime
                    rightRuntime)
                  parentType leftFieldName rightFieldName leftArguments
                  rightArguments)
                variableValues
                (parentFuel - leafProbeFuel leftFieldDefinition.outputType)
                leftRuntime
                (projectionTargetResolverValue
                  (.object leftRuntime
                    (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                      leftInitialSelectionSet)))
                leftChildSelectionSet).data
              (Execution.executeSelectionSetAsResponse schema
                (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                  (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                    rightInitialSelectionSet parentType leftFieldName
                    rightFieldName leftArguments rightArguments leftRuntime
                    rightRuntime)
                  parentType leftFieldName rightFieldName leftArguments
                  rightArguments)
                variableValues
                (parentFuel - leafProbeFuel rightFieldDefinition.outputType)
                rightRuntime
                (projectionTargetResolverValue
                  (.object rightRuntime
                    (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                      rightInitialSelectionSet)))
                rightChildSelectionSet).data)
      -> ¬ selectionSetsDataEquivalent schema parentType left right := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hparentObject hfuelAppend hleftMem hrightMem hleftLookup
    hrightLookup hleftComposite hrightComposite hleftInclude hrightInclude
    hfieldDiff hchildDataNot
  let rootSelectionSet : List Selection :=
    [Selection.inlineFragment (some parentType) [] (left ++ right)]
  let leftInitialSelectionSet : List Selection :=
    fieldPairPathLocalNextSelectionSet schema parentType leftRuntime
      leftFieldName leftArguments (left ++ right)
  let rightInitialSelectionSet : List Selection :=
    fieldPairPathLocalNextSelectionSet schema parentType rightRuntime
      rightFieldName rightArguments (left ++ right)
  let variableValues : Execution.VariableValues := []
  have hleftFuel :
      selectionSetDeepProbeFuel schema parentType left ≤ parentFuel := by
    have hlocal := selectionSetDeepProbeFuel_le_append_left
      schema parentType left right
    omega
  have hrightFuel :
      selectionSetDeepProbeFuel schema parentType right ≤ parentFuel := by
    have hlocal := selectionSetDeepProbeFuel_le_append_right
      schema parentType left right
    omega
  have hleftLeafFuel :
      leafProbeFuel leftFieldDefinition.outputType ≤ parentFuel := by
    have hlocal :=
      leafProbeFuel_le_selectionSetDeepProbeFuel_of_field_mem schema
        parentType (selectionSet := left) (responseName := responseName)
        (fieldName := leftFieldName) (arguments := leftArguments)
        (directives := leftDirectives)
        (childSelectionSet := leftChildSelectionSet)
        (fieldDefinition := leftFieldDefinition) hleftMem hleftLookup
    omega
  have hrightLeafFuel :
      leafProbeFuel rightFieldDefinition.outputType ≤ parentFuel := by
    have hlocal :=
      leafProbeFuel_le_selectionSetDeepProbeFuel_of_field_mem schema
        parentType (selectionSet := right) (responseName := responseName)
        (fieldName := rightFieldName) (arguments := rightArguments)
        (directives := rightDirectives)
        (childSelectionSet := rightChildSelectionSet)
        (fieldDefinition := rightFieldDefinition) hrightMem hrightLookup
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
  rcases
      executeSelectionSetAsResponse_fieldPairOrDeepSuccess_pathLocalProbe_target_child_of_valid_normal_context_fuel_ge
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet (left ++ right) variableValues hschema
        (variableDefinitions := leftVariableDefinitions)
        (parentType := parentType) (runtimeType := leftRuntime)
        (targetParent := parentType) (leftField := leftFieldName)
        (rightField := rightFieldName) (responseName := responseName)
        (fieldName := leftFieldName) (targetLeftArguments := leftArguments)
        (targetRightArguments := rightArguments)
        (targetArguments := leftArguments) (arguments := leftArguments)
        (directives := leftDirectives) (leftRuntime := leftRuntime)
        (rightRuntime := rightRuntime) (selectionSet := left)
        (childSelectionSet := leftChildSelectionSet)
        (fieldDefinition := leftFieldDefinition) (fuel := parentFuel)
        (tag := FieldPairProbeTag.left)
        hleftValid hleftFree hleftNormal hparentObject hleftFuel
        hsupport hleftContext hleftMem hleftLookup hleftComposite
        hleftInclude (argumentsEquivalent_refl_forSyntaxDiff leftArguments)
    with
    ⟨leftChildFields, leftChildErrors, hleftChildResponse⟩
  rcases
      executeSelectionSetAsResponse_fieldPairOrDeepSuccess_pathLocalProbe_target_child_of_valid_normal_context_fuel_ge
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet (left ++ right) variableValues hschema
        (variableDefinitions := rightVariableDefinitions)
        (parentType := parentType) (runtimeType := rightRuntime)
        (targetParent := parentType) (leftField := leftFieldName)
        (rightField := rightFieldName) (responseName := responseName)
        (fieldName := rightFieldName)
        (targetLeftArguments := leftArguments)
        (targetRightArguments := rightArguments)
        (targetArguments := rightArguments) (arguments := rightArguments)
        (directives := rightDirectives) (leftRuntime := leftRuntime)
        (rightRuntime := rightRuntime) (selectionSet := right)
        (childSelectionSet := rightChildSelectionSet)
        (fieldDefinition := rightFieldDefinition) (fuel := parentFuel)
        (tag := FieldPairProbeTag.right)
        hrightValid hrightFree hrightNormal hparentObject hrightFuel
        hsupport hrightContext hrightMem hrightLookup hrightComposite
        hrightInclude (argumentsEquivalent_refl_forSyntaxDiff rightArguments)
    with
    ⟨rightChildFields, rightChildErrors, hrightChildResponse⟩
  have hchildNot :
      ¬ Execution.ResponseValue.semanticEquivalent
        (Execution.ResponseValue.object leftChildFields)
        (Execution.ResponseValue.object rightChildFields) := by
    intro hsemantic
    exact hchildDataNot (by
      simpa [rootSelectionSet, leftInitialSelectionSet,
        rightInitialSelectionSet, variableValues, hleftChildResponse,
        hrightChildResponse] using hsemantic)
  have hleftLeftTarget :
      ∀ responseName arguments directives childSelectionSet,
        Selection.field responseName leftFieldName arguments directives
            childSelectionSet ∈ left ->
        Argument.argumentsEquivalent arguments leftArguments ->
          ∃ childFields childErrors,
            Execution.executeSelectionSetAsResponse schema
                (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                  (fieldPairPathLocalProbeResolvers schema
                    leftInitialSelectionSet rightInitialSelectionSet
                    parentType leftFieldName rightFieldName leftArguments
                    rightArguments leftRuntime rightRuntime)
                  parentType leftFieldName rightFieldName leftArguments
                  rightArguments)
                variableValues
                (parentFuel - leafProbeFuel leftFieldDefinition.outputType)
                leftRuntime
                (projectionTargetResolverValue
                  (.object leftRuntime
                    (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                      leftInitialSelectionSet)))
                childSelectionSet =
              ({ data := Execution.ResponseValue.object childFields,
                 errors := childErrors } : Execution.Response) := by
    intro currentResponseName arguments directives childSelectionSet hmem
      harguments
    simpa [rootSelectionSet, leftInitialSelectionSet, variableValues] using
      executeSelectionSetAsResponse_fieldPairOrDeepSuccess_pathLocalProbe_target_child_of_valid_normal_context_fuel_ge
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet (left ++ right) variableValues hschema
        (variableDefinitions := leftVariableDefinitions)
        (parentType := parentType) (runtimeType := leftRuntime)
        (targetParent := parentType) (leftField := leftFieldName)
        (rightField := rightFieldName) (responseName := currentResponseName)
        (fieldName := leftFieldName) (targetLeftArguments := leftArguments)
        (targetRightArguments := rightArguments)
        (targetArguments := leftArguments) (arguments := arguments)
        (directives := directives) (leftRuntime := leftRuntime)
        (rightRuntime := rightRuntime) (selectionSet := left)
        (childSelectionSet := childSelectionSet)
        (fieldDefinition := leftFieldDefinition) (fuel := parentFuel)
        (tag := FieldPairProbeTag.left)
        hleftValid hleftFree hleftNormal hparentObject hleftFuel
        hsupport hleftContext hmem hleftLookup hleftComposite hleftInclude
        harguments
  have hleftRightTarget :
      ∀ responseName arguments directives childSelectionSet,
        Selection.field responseName rightFieldName arguments directives
            childSelectionSet ∈ left ->
        Argument.argumentsEquivalent arguments rightArguments ->
          ∃ childFields childErrors,
            Execution.executeSelectionSetAsResponse schema
                (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                  (fieldPairPathLocalProbeResolvers schema
                    leftInitialSelectionSet rightInitialSelectionSet
                    parentType leftFieldName rightFieldName leftArguments
                    rightArguments leftRuntime rightRuntime)
                  parentType leftFieldName rightFieldName leftArguments
                  rightArguments)
                variableValues
                (parentFuel - leafProbeFuel rightFieldDefinition.outputType)
                rightRuntime
                (projectionTargetResolverValue
                  (.object rightRuntime
                    (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                      rightInitialSelectionSet)))
                childSelectionSet =
              ({ data := Execution.ResponseValue.object childFields,
                 errors := childErrors } : Execution.Response) := by
    intro currentResponseName arguments directives childSelectionSet hmem
      harguments
    simpa [rootSelectionSet, rightInitialSelectionSet, variableValues] using
      executeSelectionSetAsResponse_fieldPairOrDeepSuccess_pathLocalProbe_target_child_of_valid_normal_context_fuel_ge
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet (left ++ right) variableValues hschema
        (variableDefinitions := leftVariableDefinitions)
        (parentType := parentType) (runtimeType := rightRuntime)
        (targetParent := parentType) (leftField := leftFieldName)
        (rightField := rightFieldName) (responseName := currentResponseName)
        (fieldName := rightFieldName)
        (targetLeftArguments := leftArguments)
        (targetRightArguments := rightArguments)
        (targetArguments := rightArguments) (arguments := arguments)
        (directives := directives) (leftRuntime := leftRuntime)
        (rightRuntime := rightRuntime) (selectionSet := left)
        (childSelectionSet := childSelectionSet)
        (fieldDefinition := rightFieldDefinition) (fuel := parentFuel)
        (tag := FieldPairProbeTag.right)
        hleftValid hleftFree hleftNormal hparentObject hleftFuel
        hsupport hleftContext hmem hrightLookup hrightComposite
        hrightInclude harguments
  have hrightLeftTarget :
      ∀ responseName arguments directives childSelectionSet,
        Selection.field responseName leftFieldName arguments directives
            childSelectionSet ∈ right ->
        Argument.argumentsEquivalent arguments leftArguments ->
          ∃ childFields childErrors,
            Execution.executeSelectionSetAsResponse schema
                (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                  (fieldPairPathLocalProbeResolvers schema
                    leftInitialSelectionSet rightInitialSelectionSet
                    parentType leftFieldName rightFieldName leftArguments
                    rightArguments leftRuntime rightRuntime)
                  parentType leftFieldName rightFieldName leftArguments
                  rightArguments)
                variableValues
                (parentFuel - leafProbeFuel leftFieldDefinition.outputType)
                leftRuntime
                (projectionTargetResolverValue
                  (.object leftRuntime
                    (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                      leftInitialSelectionSet)))
                childSelectionSet =
              ({ data := Execution.ResponseValue.object childFields,
                 errors := childErrors } : Execution.Response) := by
    intro currentResponseName arguments directives childSelectionSet hmem
      harguments
    simpa [rootSelectionSet, leftInitialSelectionSet, variableValues] using
      executeSelectionSetAsResponse_fieldPairOrDeepSuccess_pathLocalProbe_target_child_of_valid_normal_context_fuel_ge
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet (left ++ right) variableValues hschema
        (variableDefinitions := rightVariableDefinitions)
        (parentType := parentType) (runtimeType := leftRuntime)
        (targetParent := parentType) (leftField := leftFieldName)
        (rightField := rightFieldName) (responseName := currentResponseName)
        (fieldName := leftFieldName) (targetLeftArguments := leftArguments)
        (targetRightArguments := rightArguments)
        (targetArguments := leftArguments) (arguments := arguments)
        (directives := directives) (leftRuntime := leftRuntime)
        (rightRuntime := rightRuntime) (selectionSet := right)
        (childSelectionSet := childSelectionSet)
        (fieldDefinition := leftFieldDefinition) (fuel := parentFuel)
        (tag := FieldPairProbeTag.left)
        hrightValid hrightFree hrightNormal hparentObject hrightFuel
        hsupport hrightContext hmem hleftLookup hleftComposite hleftInclude
        harguments
  have hrightRightTarget :
      ∀ responseName arguments directives childSelectionSet,
        Selection.field responseName rightFieldName arguments directives
            childSelectionSet ∈ right ->
        Argument.argumentsEquivalent arguments rightArguments ->
          ∃ childFields childErrors,
            Execution.executeSelectionSetAsResponse schema
                (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                  (fieldPairPathLocalProbeResolvers schema
                    leftInitialSelectionSet rightInitialSelectionSet
                    parentType leftFieldName rightFieldName leftArguments
                    rightArguments leftRuntime rightRuntime)
                  parentType leftFieldName rightFieldName leftArguments
                  rightArguments)
                variableValues
                (parentFuel - leafProbeFuel rightFieldDefinition.outputType)
                rightRuntime
                (projectionTargetResolverValue
                  (.object rightRuntime
                    (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                      rightInitialSelectionSet)))
                childSelectionSet =
              ({ data := Execution.ResponseValue.object childFields,
                 errors := childErrors } : Execution.Response) := by
    intro currentResponseName arguments directives childSelectionSet hmem
      harguments
    simpa [rootSelectionSet, rightInitialSelectionSet, variableValues] using
      executeSelectionSetAsResponse_fieldPairOrDeepSuccess_pathLocalProbe_target_child_of_valid_normal_context_fuel_ge
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet (left ++ right) variableValues hschema
        (variableDefinitions := rightVariableDefinitions)
        (parentType := parentType) (runtimeType := rightRuntime)
        (targetParent := parentType) (leftField := leftFieldName)
        (rightField := rightFieldName) (responseName := currentResponseName)
        (fieldName := rightFieldName)
        (targetLeftArguments := leftArguments)
        (targetRightArguments := rightArguments)
        (targetArguments := rightArguments) (arguments := arguments)
        (directives := directives) (leftRuntime := leftRuntime)
        (rightRuntime := rightRuntime) (selectionSet := right)
        (childSelectionSet := childSelectionSet)
        (fieldDefinition := rightFieldDefinition) (fuel := parentFuel)
        (tag := FieldPairProbeTag.right)
        hrightValid hrightFree hrightNormal hparentObject hrightFuel
        hsupport hrightContext hmem hrightLookup hrightComposite
        hrightInclude harguments
  have hleftDeep :
      ∀ responseName siblingFieldName arguments directives childSelectionSet,
        Selection.field responseName siblingFieldName arguments directives
            childSelectionSet ∈ left ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema
              (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet
                (ProjectionResolverRef.filler :
                  ProjectionResolverRef FieldPairPathLocalProbeRef))
              variableValues (parentFuel + 1)
              (projectionRootResolverValue
                (.object parentType FieldPairPathLocalProbeRef.root))
              responseName
              [{
                parentType := parentType,
                responseName := responseName,
                fieldName := siblingFieldName,
                arguments := arguments,
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(responseName, responseValue)], fieldErrors) := by
    intro currentResponseName siblingFieldName arguments directives
      childSelectionSet hmem
    simpa [rootSelectionSet, variableValues] using
      left_selectionSet_deepSuccessFieldOk_append_framed_of_valid_normal_fuel_ge
        (schema := schema) (parentType := parentType)
        (left := left) (right := right)
        (leftVariableDefinitions := leftVariableDefinitions)
        (rightVariableDefinitions := rightVariableDefinitions)
        (ProjectionResolverRef.filler :
          ProjectionResolverRef FieldPairPathLocalProbeRef)
        variableValues
        (projectionRootResolverValue
          (.object parentType FieldPairPathLocalProbeRef.root))
        parentFuel hschema hleftValid hrightValid hleftFree hrightFree
        hleftNormal hrightNormal hparentObject hfuelAppend
        currentResponseName siblingFieldName arguments directives
        childSelectionSet hmem
  have hrightDeep :
      ∀ responseName siblingFieldName arguments directives childSelectionSet,
        Selection.field responseName siblingFieldName arguments directives
            childSelectionSet ∈ right ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema
              (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet
                (ProjectionResolverRef.filler :
                  ProjectionResolverRef FieldPairPathLocalProbeRef))
              variableValues (parentFuel + 1)
              (projectionRootResolverValue
                (.object parentType FieldPairPathLocalProbeRef.root))
              responseName
              [{
                parentType := parentType,
                responseName := responseName,
                fieldName := siblingFieldName,
                arguments := arguments,
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(responseName, responseValue)], fieldErrors) := by
    intro currentResponseName siblingFieldName arguments directives
      childSelectionSet hmem
    simpa [rootSelectionSet, variableValues] using
      right_selectionSet_deepSuccessFieldOk_append_framed_of_valid_normal_fuel_ge
        (schema := schema) (parentType := parentType)
        (left := left) (right := right)
        (leftVariableDefinitions := leftVariableDefinitions)
        (rightVariableDefinitions := rightVariableDefinitions)
        (ProjectionResolverRef.filler :
          ProjectionResolverRef FieldPairPathLocalProbeRef)
        variableValues
        (projectionRootResolverValue
          (.object parentType FieldPairPathLocalProbeRef.root))
        parentFuel hschema hleftValid hrightValid hleftFree hrightFree
        hleftNormal hrightNormal hparentObject hfuelAppend
        currentResponseName siblingFieldName arguments directives
        childSelectionSet hmem
  exact
    not_selectionSetsDataEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_root_fieldName_child_response_diff_of_field_cases
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet variableValues parentFuel parentType
      responseName leftFieldName rightFieldName leftArguments rightArguments
      leftRuntime rightRuntime hparentObject hleftNormal hrightNormal
      hleftFree hrightFree hleftMem hrightMem hleftLookup hrightLookup
      hleftInclude hrightInclude hleftLeafFuel hrightLeafFuel hfieldDiff
      hleftChildResponse hrightChildResponse hchildNot hleftLeftTarget
      hleftRightTarget hrightLeftTarget hrightRightTarget hleftDeep
      hrightDeep

end GroundTypeNormalization

end NormalForm

end GraphQL
