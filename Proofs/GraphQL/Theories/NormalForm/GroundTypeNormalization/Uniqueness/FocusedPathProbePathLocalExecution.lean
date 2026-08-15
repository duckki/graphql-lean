import Proofs.GraphQL.Execution.ArgumentCoercion
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.FocusedPathProbeContext

/-!
Execution and parent-lift lemmas for path-local focused probes.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

theorem
    executeSelectionSetAsResponse_fieldPairOrDeepSuccess_pathLocalProbe_tagged_of_valid_normal_support_context_fuel_ge_size
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (variableValues : Execution.VariableValues)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ∀ n normalParentType variableDefinitions (selectionSet : List Selection)
            fuel runtimeType targetParent leftField rightField
            (leftArguments rightArguments : Execution.CoercedArguments)
            (leftRuntime rightRuntime : Name) (tag : FieldPairProbeTag)
            (currentSelectionSet : List Selection),
          SelectionSet.size selectionSet < n
          -> selectionSetDeepProbeFuel schema normalParentType selectionSet ≤ fuel
          -> Validation.selectionSetValid schema variableDefinitions normalParentType
              selectionSet
          -> selectionSetArgumentsCoercibleInPossibleTypes schema variableValues
              normalParentType selectionSet
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
        _hfuel _hvalid _hcoercion _hfree _hnormal _hinclude _hsupport
        _hobjectContext _habstractContext
      omega
  | succ n ih =>
      intro normalParentType variableDefinitions selectionSet fuel runtimeType
        targetParent leftField rightField leftArguments rightArguments
        leftRuntime rightRuntime tag currentSelectionSet hsize hfuel hvalid
        hcoercion hfree hnormal hinclude hsupport hobjectContext habstractContext
      have hruntimeObject :
          objectTypeNameBool schema runtimeType = true :=
        objectTypeNameBool_of_typeIncludesObjectBool hschema hinclude
      have hruntimeCoercion :
          selectionSetArgumentsCoercible schema variableValues runtimeType
            selectionSet :=
        hcoercion runtimeType hinclude
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
          ⟨fieldDefinition, hlookup, hargumentsValid, _hfieldSelectionValid⟩
        have hfieldCoercion :=
          selectionSetArgumentsCoercible_field_success_of_directiveFree
            hruntimeCoercion hfree hmem hlookup
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
        refine ⟨fieldDefinition, hlookup, hfieldCoercion, hleafFuel, ?_⟩
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
          have hchildCoercion :
              selectionSetArgumentsCoercibleInPossibleTypes schema variableValues
                fieldDefinition.outputType.namedType childSelectionSet :=
            selectionSetArgumentsCoercible_field_children_of_directiveFree
              hruntimeCoercion hfree hmem hlookup
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
              by
                have hcoercedSupport :=
                  hsupport.fieldPairPathLocalNextSelectionSet_of_object_output
                    (targetArguments := Execution.coercedArgumentsForField schema
                      variableValues normalParentType fieldName arguments)
                    hparentObject hreturnObject hlookup rfl
                rw [← fieldPairPathLocalNextSelectionSet_eq_of_arguments schema
                  normalParentType fieldDefinition.outputType.namedType fieldName
                  arguments
                    (Execution.coercedArgumentsForField schema variableValues
                      normalParentType fieldName arguments) currentSelectionSet] at hcoercedSupport
                exact hcoercedSupport
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
                hcontext hmem hpruned
            rcases
                ih fieldDefinition.outputType.namedType variableDefinitions
                  childSelectionSet childFuel
                  fieldDefinition.outputType.namedType targetParent
                  leftField rightField leftArguments rightArguments
                  leftRuntime rightRuntime tag
                  (fieldPairPathLocalNextSelectionSet schema
                    normalParentType fieldDefinition.outputType.namedType
                    fieldName arguments currentSelectionSet)
                  hchildSize hchildFuel hchildValid hchildCoercion hchildFree
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
              by
                have hcoercedSupport :=
                  hsupport.fieldPairPathLocalNextSelectionSet_of_abstract_output
                    (targetArguments := Execution.coercedArgumentsForField schema
                      variableValues normalParentType fieldName arguments)
                    hparentObject hchildObject hlookup hreturnComposite
                    hchildInclude
                rw [← fieldPairPathLocalNextSelectionSet_eq_of_arguments schema
                  normalParentType childRuntimeType fieldName arguments
                    (Execution.coercedArgumentsForField schema variableValues
                      normalParentType fieldName arguments) currentSelectionSet] at hcoercedSupport
                exact hcoercedSupport
            rcases
                ih fieldDefinition.outputType.namedType variableDefinitions
                  childSelectionSet childFuel childRuntimeType targetParent
                  leftField rightField leftArguments rightArguments
                  leftRuntime rightRuntime tag
                  (fieldPairPathLocalNextSelectionSet schema
                    normalParentType childRuntimeType fieldName arguments
                    currentSelectionSet)
                  hchildSize hchildFuel hchildValid hchildCoercion hchildFree
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
                      hcontext hmem hbodyMem hchildNormal hchildObject) with
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
        have hbodyCoercion :
            selectionSetArgumentsCoercibleInPossibleTypes schema variableValues
              runtimeType bodySelectionSet :=
          selectionSetArgumentsCoercibleInPossibleTypes_of_object hruntimeObject
            (selectionSetArgumentsCoercible_inlineFragment_child_of_directiveFree
              hruntimeCoercion hfree hinlineMem hbodyInclude)
        rcases
            ih runtimeType variableDefinitions bodySelectionSet fuel
              runtimeType targetParent leftField rightField leftArguments
              rightArguments leftRuntime rightRuntime tag
              currentSelectionSet hbodySize hbodyFuel hbodyValid hbodyCoercion hbodyFree
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
    (leftArguments rightArguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime : Name) (tag : FieldPairProbeTag)
    (currentSelectionSet selectionSet : List Selection)
    : Prop :=
  ∀ responseName fieldName arguments directives childSelectionSet,
    Selection.field responseName fieldName arguments directives childSelectionSet
      ∈ selectionSet
    -> ∃ fieldDefinition,
        schema.lookupField parentType fieldName = some fieldDefinition
        ∧ (Execution.coerceArgumentValues schema variableValues
            fieldDefinition.arguments arguments).isSuccess
          = true
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

theorem PathLocalSelectionSetFieldChildrenReady.argumentCoercion_of_mem_lookup
    {schema : Schema}
    {rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection}
    {variableValues : Execution.VariableValues}
    {fuel : Nat} {targetParent leftField rightField parentType : Name}
    {leftArguments rightArguments : Execution.CoercedArguments}
    {leftRuntime rightRuntime : Name} {tag : FieldPairProbeTag}
    {currentSelectionSet selectionSet : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet : List Selection} {fieldDefinition : FieldDefinition}
    : PathLocalSelectionSetFieldChildrenReady schema rootSelectionSet
        leftInitialSelectionSet rightInitialSelectionSet variableValues fuel
        targetParent leftField rightField parentType leftArguments
        rightArguments leftRuntime rightRuntime tag currentSelectionSet selectionSet
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> (Execution.coerceArgumentValues schema variableValues
            fieldDefinition.arguments arguments).isSuccess
          = true := by
  intro hready hmem hlookup
  rcases hready responseName fieldName arguments directives childSelectionSet hmem with
    ⟨candidate, hcandidateLookup, hcoercion, _hfuel, _hchild⟩
  have hcandidate : candidate = fieldDefinition := by
    rw [hlookup] at hcandidateLookup
    exact Option.some.inj hcandidateLookup.symm
  subst candidate
  exact hcoercion

theorem PathLocalSelectionSetFieldChildrenReady.response_of_mem_lookup_runtime
    {schema : Schema}
    {rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection}
    {variableValues : Execution.VariableValues}
    {fuel : Nat} {targetParent leftField rightField parentType : Name}
    {leftArguments rightArguments : Execution.CoercedArguments}
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
              ∧ abstractRuntimeForFieldDeep? schema parentType fieldName
                  parentType currentSelectionSet
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
                      runtimeType fieldName arguments
                      currentSelectionSet))))
              childSelectionSet
            = ({
                  data := Execution.ResponseValue.object responseFields,
                  errors := childErrors
                }
                : Execution.Response) := by
  intro hready hmem hlookup hruntime
  rcases hready responseName fieldName arguments directives childSelectionSet
      hmem with
    ⟨candidateDefinition, hcandidateLookup, _hcoercion, hfuel, hcase⟩
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

theorem
    executeSelectionSetAsResponse_fieldPairOrDeepSuccess_pathLocalProbe_target_child_of_valid_normal_context_fuel_ge
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet currentSelectionSet
      : List Selection)
    (variableValues : Execution.VariableValues)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ∀ {variableDefinitions : List VariableDefinition}
            {parentType runtimeType targetParent leftField rightField
              responseName fieldName
              : Name}
            {targetLeftArguments targetRightArguments : Execution.CoercedArguments}
            {PathArgumentType : Type} {pathArguments : List PathArgumentType}
            {arguments : List Argument}
            {directives : List DirectiveApplication}
            {leftRuntime rightRuntime : Name}
            {selectionSet childSelectionSet : List Selection}
            {fieldDefinition : FieldDefinition} {fuel : Nat}
            {tag : FieldPairProbeTag},
          Validation.selectionSetValid schema variableDefinitions parentType selectionSet
          -> selectionSetArgumentsCoercible schema variableValues parentType selectionSet
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
                        runtimeType fieldName pathArguments
                        currentSelectionSet))))
                childSelectionSet
              = ({
                    data := Execution.ResponseValue.object responseFields,
                    errors := childErrors
                  }
                  : Execution.Response) := by
  intro hschema variableDefinitions parentType runtimeType targetParent
    leftField rightField responseName fieldName targetLeftArguments
    targetRightArguments PathArgumentType pathArguments arguments directives leftRuntime
    rightRuntime selectionSet childSelectionSet fieldDefinition fuel tag
    hvalid hcoercion hfree hnormal hparentObject hfuel hsupport hcontext hmem hlookup
    hcomposite hinclude
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
            fieldName pathArguments currentSelectionSet) :=
      by
        have hcoercedSupport :=
          hsupport.fieldPairPathLocalNextSelectionSet_of_abstract_output
            (targetArguments := targetLeftArguments)
            hparentObject hruntimeObject hlookup hcomposite hinclude
        rw [← fieldPairPathLocalNextSelectionSet_eq_of_arguments schema parentType
          runtimeType fieldName pathArguments targetLeftArguments currentSelectionSet] at hcoercedSupport
        exact hcoercedSupport
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
            runtimeType fieldName pathArguments currentSelectionSet)
          (by omega) hchildFuel hchildValid
          (selectionSetArgumentsCoercible_field_children_of_directiveFree
            hcoercion hfree hmem hlookup)
          hchildFree hchildNormal
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
                (targetArguments := pathArguments) (arguments := arguments)
                (directives := directives) (selectionSet := selectionSet)
                (childSelectionSet := childSelectionSet)
                (currentSelectionSet := currentSelectionSet)
                hcontext hmem hpruned)
          (by
            intro _hchildParentNonObject bodyDirectives bodySelectionSet
              hbodyMem
            exact
              PathLocalSelectionSetCurrentContext.fieldPairPathLocalNextSelectionSet_inlineFragment_body
                (schema := schema) (currentRuntimeType := parentType)
                (childRuntimeType := runtimeType)
                (childParentType := fieldDefinition.outputType.namedType)
                (targetField := fieldName) (responseName := responseName)
                (targetArguments := pathArguments) (arguments := arguments)
                (directives := directives) (bodyDirectives := bodyDirectives)
                (selectionSet := selectionSet)
                (childSelectionSet := childSelectionSet)
                (bodySelectionSet := bodySelectionSet)
                (currentSelectionSet := currentSelectionSet)
                hcontext hmem hbodyMem hchildNormal
                hruntimeObject) with
      ⟨responseFields, childErrors, hresponse⟩
    exact ⟨responseFields, childErrors, by
      simpa [hchildFuelEq] using hresponse⟩

theorem
    pathLocalSelectionSetFieldChildrenReady_of_valid_normal_support_context_fuel_ge_size
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (variableValues : Execution.VariableValues)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ∀ n parentType variableDefinitions (selectionSet : List Selection)
            fuel targetParent leftField rightField
            (leftArguments rightArguments : Execution.CoercedArguments)
            (leftRuntime rightRuntime : Name) (tag : FieldPairProbeTag)
            (currentSelectionSet : List Selection),
          SelectionSet.size selectionSet < n
          -> selectionSetDeepProbeFuel schema parentType selectionSet ≤ fuel
          -> Validation.selectionSetValid schema variableDefinitions parentType
              selectionSet
          -> selectionSetArgumentsCoercible schema variableValues parentType selectionSet
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
    rightRuntime tag currentSelectionSet hsize hfuel hvalid hcoercion hfree hnormal
    hparentObject hsupport hcontext
  intro responseName fieldName arguments directives childSelectionSet hmem
  rcases selectionSetValid_field_lookup_of_mem hvalid hmem with
    ⟨fieldDefinition, hlookup, hargumentsValid, _hfieldSelectionValid⟩
  have hfieldCoercion :=
    selectionSetArgumentsCoercible_field_success_of_directiveFree
      hcoercion hfree hmem hlookup
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
  refine ⟨fieldDefinition, hlookup, hfieldCoercion, hleafFuel, ?_⟩
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
    have hchildCoercion :
        selectionSetArgumentsCoercibleInPossibleTypes schema variableValues
          fieldDefinition.outputType.namedType childSelectionSet :=
      selectionSetArgumentsCoercible_field_children_of_directiveFree
        hcoercion hfree hmem hlookup
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
        by
          have hcoercedSupport :=
            hsupport.fieldPairPathLocalNextSelectionSet_of_object_output
              (targetArguments := Execution.coercedArgumentsForField schema
                variableValues parentType fieldName arguments)
              hparentObject hreturnObject hlookup rfl
          rw [← fieldPairPathLocalNextSelectionSet_eq_of_arguments schema parentType
            fieldDefinition.outputType.namedType fieldName arguments
              (Execution.coercedArgumentsForField schema variableValues parentType
                fieldName arguments) currentSelectionSet] at hcoercedSupport
          exact hcoercedSupport
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
          hcontext hmem hpruned
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
            hchildSize hchildFuel hchildValid hchildCoercion hchildFree hchildNormal
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
        by
          have hcoercedSupport :=
            hsupport.fieldPairPathLocalNextSelectionSet_of_abstract_output
              (targetArguments := Execution.coercedArgumentsForField schema
                variableValues parentType fieldName arguments)
              hparentObject hchildObject hlookup hreturnComposite hchildInclude
          rw [← fieldPairPathLocalNextSelectionSet_eq_of_arguments schema parentType
            childRuntimeType fieldName arguments
              (Execution.coercedArgumentsForField schema variableValues parentType
                fieldName arguments) currentSelectionSet] at hcoercedSupport
          exact hcoercedSupport
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
            hchildSize hchildFuel hchildValid hchildCoercion hchildFree hchildNormal
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
                  hcontext hmem hbodyMem hchildNormal hchildObject) with
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
    {targetArguments : Execution.CoercedArguments} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    : Selection.field responseName targetField arguments directives childSelectionSet
        ∈ selectionSet
      -> NormalSelectionSetObservableLeaf schema childParentType childSelectionSet
      -> ∃ mergedSelectionSet,
          firstFieldChildByHead? targetField targetArguments selectionSet
            = some mergedSelectionSet
          ∧ NormalSelectionSetObservableLeaf schema childParentType
              mergedSelectionSet := by
  intro hmem hleaf
  rcases
      firstFieldChildByHead?_field_mem_append_context
        (targetArguments := targetArguments)
        hmem with
    ⟨mergedSelectionSet, pref, suff, hmerged, hcontext⟩
  refine ⟨mergedSelectionSet, hmerged, ?_⟩
  rw [hcontext]
  exact hleaf.append_context

theorem normalSelectionSetObservableLeaf_of_firstFieldChildByHeadAtRuntime?_field_mem
    {schema : Schema}
    {currentRuntimeType childRuntimeType targetField responseName : Name}
    {targetArguments : Execution.CoercedArguments} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    : Selection.field responseName targetField arguments directives childSelectionSet
        ∈ selectionSet
      -> NormalSelectionSetObservableLeaf schema childRuntimeType
          (runtimePrunedSelectionSet schema childRuntimeType childSelectionSet)
      -> ∃ mergedSelectionSet,
          firstFieldChildByHeadAtRuntime? schema currentRuntimeType
              childRuntimeType targetField targetArguments selectionSet
            = some mergedSelectionSet
          ∧ NormalSelectionSetObservableLeaf schema childRuntimeType
              mergedSelectionSet := by
  intro hmem hleaf
  rcases
      firstFieldChildByHeadAtRuntime?_field_mem_append_context
        (schema := schema) (currentRuntimeType := currentRuntimeType)
        (childRuntimeType := childRuntimeType)
        (targetField := targetField) (targetArguments := targetArguments) hmem with
    ⟨mergedSelectionSet, pref, suff, hmerged, hcontext⟩
  refine ⟨mergedSelectionSet, hmerged, ?_⟩
  rw [hcontext]
  exact hleaf.append_context

theorem normalSelectionSetObservableLeaf_of_fieldPairPathLocalNextSelectionSet_field_mem
    {schema : Schema}
    {currentRuntimeType childRuntimeType targetField responseName : Name}
    {targetArguments : Execution.CoercedArguments} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    : Selection.field responseName targetField arguments directives childSelectionSet
        ∈ selectionSet
      -> NormalSelectionSetObservableLeaf schema childRuntimeType
          (runtimePrunedSelectionSet schema childRuntimeType childSelectionSet)
      -> NormalSelectionSetObservableLeaf schema childRuntimeType
          (fieldPairPathLocalNextSelectionSet schema currentRuntimeType
            childRuntimeType targetField targetArguments selectionSet) := by
  intro hmem hleaf
  rcases
      normalSelectionSetObservableLeaf_of_firstFieldChildByHeadAtRuntime?_field_mem
        (schema := schema) (currentRuntimeType := currentRuntimeType)
        (childRuntimeType := childRuntimeType)
        (targetField := targetField) (targetArguments := targetArguments)
        hmem hleaf with
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

theorem
    normalSelectionSetObservableLeaf_of_fieldPairPathLocalNextSelectionSet_object_output_of_valid_normal_field_mem
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {currentRuntimeType responseName fieldName : Name}
    {targetArguments : Execution.CoercedArguments} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection} {fieldDefinition : FieldDefinition}
    : Validation.selectionSetValid schema variableDefinitions currentRuntimeType
        selectionSet
      -> selectionSetNormal schema currentRuntimeType selectionSet
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> schema.lookupField currentRuntimeType fieldName = some fieldDefinition
      -> objectTypeNameBool schema fieldDefinition.outputType.namedType = true
      -> NormalSelectionSetObservableLeaf schema
          fieldDefinition.outputType.namedType
          (fieldPairPathLocalNextSelectionSet schema currentRuntimeType
            fieldDefinition.outputType.namedType fieldName targetArguments
            selectionSet) := by
  intro hvalid hnormal hmem hlookup hobject
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
      (targetField := fieldName) (targetArguments := targetArguments) hmem (by
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
  exact ⟨
    normalSelectionSetObservableLeaf_of_valid_normal_composite_field_mem
      hleftValid hleftNormal hleftMem hlookup hcomposite,
    normalSelectionSetObservableLeaf_of_valid_normal_composite_field_mem
      hrightValid hrightNormal hrightMem hlookup hcomposite
  ⟩

theorem not_fieldProbeTarget_of_fieldName_ne
    {targetParent leftField rightField : Name}
    {leftArguments arguments : Execution.CoercedArguments}
    : leftField ≠ rightField
      -> ¬ fieldProbeTarget targetParent leftField leftArguments targetParent
            rightField arguments := by
  intro hfieldDiff htarget
  exact hfieldDiff htarget.2.1.symm

theorem not_fieldProbeTarget_of_arguments_not_equivalent
    {targetParent fieldName : Name}
    {leftArguments rightArguments arguments : Execution.CoercedArguments}
    : ¬ Execution.CoercedArgument.argumentsEquivalent leftArguments rightArguments
      -> Execution.CoercedArgument.argumentsEquivalent arguments rightArguments
      -> ¬ fieldProbeTarget targetParent fieldName leftArguments targetParent
            fieldName arguments := by
  intro hargumentsDiff hrightArgs hleftTarget
  rcases hleftTarget with ⟨_hparent, _hfield, hleftArgs⟩
  exact hargumentsDiff
    (Execution.CoercedArgument.argumentsEquivalent_trans
      (Execution.CoercedArgument.argumentsEquivalent_symm hleftArgs) hrightArgs)

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_taggedPair
    {schema : Schema}
    {rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection}
    {variableValues : Execution.VariableValues} {leftFuel rightFuel : Nat}
    {leftParentType rightParentType leftRuntime rightRuntime targetParent
      leftField rightField
      : Name}
    {leftArguments rightArguments : Execution.CoercedArguments}
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

theorem
    executeField_fieldPairOrDeepSuccess_pathLocalProbe_other_root_ok_of_deepSuccessWithRef_ok
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (variableValues : Execution.VariableValues) (parentFuel : Nat)
    (targetParent leftField rightField : Name)
    (leftArguments rightArguments : Execution.CoercedArguments)
    (arguments : List Argument) (leftRuntime rightRuntime : Name)
    (responseName fieldName : Name) (childSelectionSet : List Selection)
    (responseValue : Execution.ResponseValue) (fieldErrors : Nat)
    : (∀ fieldDefinition coercedArguments,
        schema.lookupField targetParent fieldName = some fieldDefinition
        -> Execution.coerceArgumentValues schema variableValues
              fieldDefinition.arguments arguments
            = .success coercedArguments
        -> ¬ fieldPairProjectionTarget targetParent leftField rightField
              leftArguments rightArguments targetParent fieldName
              coercedArguments)
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

theorem
    selectionSetOtherFieldsExecuteOk_fieldPairOrDeepSuccess_pathLocalProbe_of_deepSuccessWithRef_ok
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (variableValues : Execution.VariableValues) (parentFuel : Nat)
    (targetParent leftField rightField : Name)
    (leftArguments rightArguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime : Name) (selectionSet : List Selection)
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
          -> (∀ fieldDefinition coercedArguments,
                schema.lookupField targetParent fieldName = some fieldDefinition
                -> Execution.coerceArgumentValues schema variableValues
                      fieldDefinition.arguments arguments
                    = .success coercedArguments
                -> ¬ fieldPairProjectionTarget targetParent leftField rightField
                      leftArguments rightArguments targetParent fieldName
                      coercedArguments)
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
  exact ⟨
    responseValue,
    fieldErrors,
    executeField_fieldPairOrDeepSuccess_pathLocalProbe_other_root_ok_of_deepSuccessWithRef_ok
      schema rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      variableValues parentFuel targetParent leftField rightField leftArguments
      rightArguments arguments leftRuntime rightRuntime responseName fieldName
      childSelectionSet responseValue fieldErrors hnotProjection hdeepOk
  ⟩

theorem
    not_selectionSetsDataEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_root_arguments_child_response_diff_of_field_ok
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (variableValues : Execution.VariableValues) (parentFuel : Nat)
    (parentType responseName fieldName : Name)
    (leftArguments rightArguments : List Argument)
    (leftTargetArguments rightTargetArguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime : Name) {left right : List Selection}
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
      -> (Execution.coerceArgumentValues schema variableValues
            fieldDefinition.arguments leftArguments).isSuccess
          = true
      -> (Execution.coerceArgumentValues schema variableValues
            fieldDefinition.arguments rightArguments).isSuccess
          = true
      -> Execution.CoercedArgument.argumentsEquivalent
          (Execution.coercedArgumentsForField schema variableValues parentType
            fieldName leftArguments)
          leftTargetArguments
      -> Execution.CoercedArgument.argumentsEquivalent
          (Execution.coercedArgumentsForField schema variableValues parentType
            fieldName rightArguments)
          rightTargetArguments
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType leftRuntime
          = true
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType rightRuntime
          = true
      -> leafProbeFuel fieldDefinition.outputType ≤ parentFuel
      -> ¬ Execution.CoercedArgument.argumentsEquivalent leftTargetArguments
            rightTargetArguments
      -> Execution.executeSelectionSetAsResponse schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet parentType fieldName fieldName
                leftTargetArguments rightTargetArguments leftRuntime rightRuntime)
              parentType fieldName fieldName leftTargetArguments rightTargetArguments)
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
                leftTargetArguments rightTargetArguments leftRuntime rightRuntime)
              parentType fieldName fieldName leftTargetArguments rightTargetArguments)
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
                      leftTargetArguments rightTargetArguments leftRuntime rightRuntime)
                    parentType fieldName fieldName leftTargetArguments
                    rightTargetArguments)
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
                      leftTargetArguments rightTargetArguments leftRuntime rightRuntime)
                    parentType fieldName fieldName leftTargetArguments
                    rightTargetArguments)
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
    hrightMem hlookup hleftCoercion hrightCoercion hleftArguments
    hrightArguments hleftInclude hrightInclude hfuel hargumentsDiff
    hleftChildResponse hrightChildResponse hchildNot hleftFieldOk
    hrightFieldOk
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet
      (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
        rightInitialSelectionSet parentType fieldName fieldName
        leftTargetArguments rightTargetArguments leftRuntime rightRuntime)
      parentType fieldName fieldName leftTargetArguments rightTargetArguments
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
                leftTargetArguments rightTargetArguments leftRuntime rightRuntime)
              parentType fieldName fieldName leftTargetArguments rightTargetArguments)
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
        parentType fieldName fieldName responseName leftTargetArguments
        rightTargetArguments leftArguments leftRuntime rightRuntime
        leftChildSelectionSet fieldDefinition
        hleftArguments
        hlookup hleftCoercion hleftInclude
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
                leftTargetArguments rightTargetArguments leftRuntime rightRuntime)
              parentType fieldName fieldName leftTargetArguments rightTargetArguments)
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
        ¬ fieldProbeTarget parentType fieldName leftTargetArguments parentType
          fieldName
          (Execution.coercedArgumentsForField schema variableValues parentType
            fieldName rightArguments) :=
      not_fieldProbeTarget_of_arguments_not_equivalent hargumentsDiff
        hrightArguments
    have hfield :=
      executeField_fieldPairOrDeepSuccess_pathLocalProbe_right_root_response_of_not_left
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet variableValues
        (parentFuel - leafProbeFuel fieldDefinition.outputType)
        parentType fieldName fieldName responseName leftTargetArguments
        rightTargetArguments rightArguments leftRuntime rightRuntime
        rightChildSelectionSet fieldDefinition hnotLeft
        hrightArguments
        hlookup hrightCoercion hrightInclude
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
    refine ⟨
      parentType,
      ProjectionResolverRef.root FieldPairPathLocalProbeRef.root,
      ?_,
      typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject
    ⟩
    simp [source, projectionRootResolverValue, projectionResolverValue]
  exact
    SemanticSeparation.not_selectionSetsDataEquivalent_of_responseName_value_diff_of_field_ok
      resolvers variableValues (parentFuel + 1) source hsource hobject
      hleftNormal hrightNormal hleftFree hrightFree hleftMem hrightMem
      hleftTarget hrightTarget hvalueNot hleftFieldOk hrightFieldOk

theorem
    not_selectionSetsDataEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_root_fieldName_child_response_diff_of_field_ok
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (variableValues : Execution.VariableValues) (parentFuel : Nat)
    (parentType responseName leftFieldName rightFieldName : Name)
    (leftArguments rightArguments : List Argument)
    (leftTargetArguments rightTargetArguments : Execution.CoercedArguments)
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
      -> Selection.field responseName leftFieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName rightFieldName rightArguments
            rightDirectives rightChildSelectionSet
          ∈ right
      -> schema.lookupField parentType leftFieldName = some leftFieldDefinition
      -> schema.lookupField parentType rightFieldName = some rightFieldDefinition
      -> (Execution.coerceArgumentValues schema variableValues
            leftFieldDefinition.arguments leftArguments).isSuccess
          = true
      -> (Execution.coerceArgumentValues schema variableValues
            rightFieldDefinition.arguments rightArguments).isSuccess
          = true
      -> Execution.CoercedArgument.argumentsEquivalent
          (Execution.coercedArgumentsForField schema variableValues parentType
            leftFieldName leftArguments)
          leftTargetArguments
      -> Execution.CoercedArgument.argumentsEquivalent
          (Execution.coercedArgumentsForField schema variableValues parentType
            rightFieldName rightArguments)
          rightTargetArguments
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
                leftTargetArguments rightTargetArguments leftRuntime rightRuntime)
              parentType leftFieldName rightFieldName leftTargetArguments
              rightTargetArguments)
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
                leftTargetArguments rightTargetArguments leftRuntime rightRuntime)
              parentType leftFieldName rightFieldName leftTargetArguments
              rightTargetArguments)
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
                      rightFieldName leftTargetArguments rightTargetArguments leftRuntime
                      rightRuntime)
                    parentType leftFieldName rightFieldName leftTargetArguments
                    rightTargetArguments)
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
                      rightFieldName leftTargetArguments rightTargetArguments leftRuntime
                      rightRuntime)
                    parentType leftFieldName rightFieldName leftTargetArguments
                    rightTargetArguments)
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
    hrightMem hleftLookup hrightLookup hleftCoercion hrightCoercion
    hleftArguments hrightArguments hleftInclude hrightInclude
    hleftFuel hrightFuel hfieldDiff hleftChildResponse
    hrightChildResponse hchildNot hleftFieldOk hrightFieldOk
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet
      (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
        rightInitialSelectionSet parentType leftFieldName rightFieldName
        leftTargetArguments rightTargetArguments leftRuntime rightRuntime)
      parentType leftFieldName rightFieldName leftTargetArguments
      rightTargetArguments
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
                rightFieldName leftTargetArguments rightTargetArguments leftRuntime
                rightRuntime)
              parentType leftFieldName rightFieldName leftTargetArguments
              rightTargetArguments)
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
        parentType leftFieldName rightFieldName responseName leftTargetArguments
        rightTargetArguments leftArguments leftRuntime rightRuntime
        leftChildSelectionSet leftFieldDefinition
        hleftArguments
        hleftLookup hleftCoercion hleftInclude
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
                rightFieldName leftTargetArguments rightTargetArguments leftRuntime
                rightRuntime)
              parentType leftFieldName rightFieldName leftTargetArguments
              rightTargetArguments)
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
        ¬ fieldProbeTarget parentType leftFieldName leftTargetArguments parentType
          rightFieldName
          (Execution.coercedArgumentsForField schema variableValues parentType
            rightFieldName rightArguments) :=
      not_fieldProbeTarget_of_fieldName_ne hfieldDiff
    have hfield :=
      executeField_fieldPairOrDeepSuccess_pathLocalProbe_right_root_response_of_not_left
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet variableValues
        (parentFuel - leafProbeFuel rightFieldDefinition.outputType)
        parentType leftFieldName rightFieldName responseName leftTargetArguments
        rightTargetArguments rightArguments leftRuntime rightRuntime
        rightChildSelectionSet rightFieldDefinition hnotLeft
        hrightArguments
        hrightLookup hrightCoercion hrightInclude
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
    refine ⟨
      parentType,
      ProjectionResolverRef.root FieldPairPathLocalProbeRef.root,
      ?_,
      typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject
    ⟩
    simp [source, projectionRootResolverValue, projectionResolverValue]
  exact
    SemanticSeparation.not_selectionSetsDataEquivalent_of_responseName_value_diff_of_field_ok
      resolvers variableValues (parentFuel + 1) source hsource hobject
      hleftNormal hrightNormal hleftFree hrightFree hleftMem hrightMem
      hleftTarget hrightTarget hvalueNot hleftFieldOk hrightFieldOk

theorem
    not_selectionSetsDataEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_root_arguments_child_response_diff_of_field_cases
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (variableValues : Execution.VariableValues) (parentFuel : Nat)
    (parentType responseName fieldName : Name)
    (leftSyntaxArguments rightSyntaxArguments : List Argument)
    (leftArguments rightArguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime : Name) {left right : List Selection}
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
      -> Selection.field responseName fieldName leftSyntaxArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName fieldName rightSyntaxArguments rightDirectives
            rightChildSelectionSet
          ∈ right
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> selectionSetArgumentCoercionSucceeds schema variableValues parentType left
      -> selectionSetArgumentCoercionSucceeds schema variableValues parentType right
      -> Execution.CoercedArgument.argumentsEquivalent
          (Execution.coercedArgumentsForField schema variableValues parentType
            fieldName leftSyntaxArguments)
          leftArguments
      -> Execution.CoercedArgument.argumentsEquivalent
          (Execution.coercedArgumentsForField schema variableValues parentType
            fieldName rightSyntaxArguments)
          rightArguments
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType leftRuntime
          = true
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType rightRuntime
          = true
      -> leafProbeFuel fieldDefinition.outputType ≤ parentFuel
      -> ¬ Execution.CoercedArgument.argumentsEquivalent leftArguments rightArguments
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
            -> Execution.CoercedArgument.argumentsEquivalent
                (Execution.coercedArgumentsForField schema variableValues
                  parentType fieldName arguments)
                leftArguments
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
            -> Execution.CoercedArgument.argumentsEquivalent
                (Execution.coercedArgumentsForField schema variableValues
                  parentType fieldName arguments)
                rightArguments
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
            -> Execution.CoercedArgument.argumentsEquivalent
                (Execution.coercedArgumentsForField schema variableValues
                  parentType fieldName arguments)
                leftArguments
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
            -> Execution.CoercedArgument.argumentsEquivalent
                (Execution.coercedArgumentsForField schema variableValues
                  parentType fieldName arguments)
                rightArguments
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
    hrightMem hlookup hleftCoercion hrightCoercion hleftArguments
    hrightArguments hleftInclude hrightInclude hfuel hargumentsDiff
    hleftChildResponse hrightChildResponse hchildNot hleftLeftTarget
    hleftRightTarget hrightLeftTarget hrightRightTarget hleftDeep
    hrightDeep
  have hleftOther :
      ∀ responseName siblingFieldName arguments directives childSelectionSet,
        Selection.field responseName siblingFieldName arguments directives
            childSelectionSet ∈ left ->
        ¬ fieldPairProjectionTarget parentType fieldName fieldName
            leftArguments rightArguments parentType siblingFieldName
            (Execution.coercedArgumentsForField schema variableValues
              parentType siblingFieldName arguments) ->
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
            .ok ([(responseName, responseValue)], fieldErrors) := by
    intro responseName siblingFieldName arguments directives childSelectionSet
      hmem hnotProjection
    apply
      selectionSetOtherFieldsExecuteOk_fieldPairOrDeepSuccess_pathLocalProbe_of_deepSuccessWithRef_ok
        schema rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
        variableValues (parentFuel + 1) parentType fieldName fieldName
        leftArguments rightArguments leftRuntime rightRuntime left hleftDeep
        responseName siblingFieldName arguments directives childSelectionSet hmem
    intro siblingFieldDefinition coercedArguments hsiblingLookup hcoercion
    rw [Execution.coercedArgumentsForField_eq_of_success schema variableValues
      parentType siblingFieldName arguments siblingFieldDefinition
      coercedArguments hsiblingLookup hcoercion] at hnotProjection
    exact hnotProjection
  have hrightOther :
      ∀ responseName siblingFieldName arguments directives childSelectionSet,
        Selection.field responseName siblingFieldName arguments directives
            childSelectionSet ∈ right ->
        ¬ fieldPairProjectionTarget parentType fieldName fieldName
            leftArguments rightArguments parentType siblingFieldName
            (Execution.coercedArgumentsForField schema variableValues
              parentType siblingFieldName arguments) ->
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
            .ok ([(responseName, responseValue)], fieldErrors) := by
    intro responseName siblingFieldName arguments directives childSelectionSet
      hmem hnotProjection
    apply
      selectionSetOtherFieldsExecuteOk_fieldPairOrDeepSuccess_pathLocalProbe_of_deepSuccessWithRef_ok
        schema rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
        variableValues (parentFuel + 1) parentType fieldName fieldName
        leftArguments rightArguments leftRuntime rightRuntime right hrightDeep
        responseName siblingFieldName arguments directives childSelectionSet hmem
    intro siblingFieldDefinition coercedArguments hsiblingLookup hcoercion
    rw [Execution.coercedArgumentsForField_eq_of_success schema variableValues
      parentType siblingFieldName arguments siblingFieldDefinition
      coercedArguments hsiblingLookup hcoercion] at hnotProjection
    exact hnotProjection
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
      hleftCoercion hleftLeftTarget hleftRightTarget hleftOther
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
      hrightCoercion hrightLeftTarget hrightRightTarget hrightOther
  exact
    not_selectionSetsDataEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_root_arguments_child_response_diff_of_field_ok
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet variableValues parentFuel parentType
      responseName fieldName leftSyntaxArguments rightSyntaxArguments leftArguments
      rightArguments leftRuntime rightRuntime hobject hleftNormal hrightNormal
      hleftFree hrightFree hleftMem hrightMem hlookup
      (hleftCoercion responseName fieldName leftSyntaxArguments leftDirectives
        leftChildSelectionSet hleftMem fieldDefinition hlookup)
      (hrightCoercion responseName fieldName rightSyntaxArguments rightDirectives
        rightChildSelectionSet hrightMem fieldDefinition hlookup)
      hleftArguments hrightArguments hleftInclude hrightInclude hfuel
      hargumentsDiff hleftChildResponse hrightChildResponse hchildNot
      hleftFieldOk hrightFieldOk

theorem
    not_selectionSetsDataEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_root_fieldName_child_response_diff_of_field_cases
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (variableValues : Execution.VariableValues) (parentFuel : Nat)
    (parentType responseName leftFieldName rightFieldName : Name)
    (leftSyntaxArguments rightSyntaxArguments : List Argument)
    (leftArguments rightArguments : Execution.CoercedArguments)
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
      -> Selection.field responseName leftFieldName leftSyntaxArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName rightFieldName rightSyntaxArguments
            rightDirectives rightChildSelectionSet
          ∈ right
      -> schema.lookupField parentType leftFieldName = some leftFieldDefinition
      -> schema.lookupField parentType rightFieldName = some rightFieldDefinition
      -> selectionSetArgumentCoercionSucceeds schema variableValues parentType left
      -> selectionSetArgumentCoercionSucceeds schema variableValues parentType right
      -> Execution.CoercedArgument.argumentsEquivalent
          (Execution.coercedArgumentsForField schema variableValues parentType
            leftFieldName leftSyntaxArguments)
          leftArguments
      -> Execution.CoercedArgument.argumentsEquivalent
          (Execution.coercedArgumentsForField schema variableValues parentType
            rightFieldName rightSyntaxArguments)
          rightArguments
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
            -> Execution.CoercedArgument.argumentsEquivalent
                (Execution.coercedArgumentsForField schema variableValues
                  parentType leftFieldName arguments)
                leftArguments
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
            -> Execution.CoercedArgument.argumentsEquivalent
                (Execution.coercedArgumentsForField schema variableValues
                  parentType rightFieldName arguments)
                rightArguments
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
            -> Execution.CoercedArgument.argumentsEquivalent
                (Execution.coercedArgumentsForField schema variableValues
                  parentType leftFieldName arguments)
                leftArguments
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
            -> Execution.CoercedArgument.argumentsEquivalent
                (Execution.coercedArgumentsForField schema variableValues
                  parentType rightFieldName arguments)
                rightArguments
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
    hrightMem hleftLookup hrightLookup hleftCoercion hrightCoercion
    hleftArguments hrightArguments hleftInclude hrightInclude hleftFuel
    hrightFuel hfieldDiff hleftChildResponse
    hrightChildResponse hchildNot hleftLeftTarget hleftRightTarget
    hrightLeftTarget hrightRightTarget hleftDeep hrightDeep
  have hleftOther :
      ∀ responseName siblingFieldName arguments directives childSelectionSet,
        Selection.field responseName siblingFieldName arguments directives
            childSelectionSet ∈ left ->
        ¬ fieldPairProjectionTarget parentType leftFieldName rightFieldName
            leftArguments rightArguments parentType siblingFieldName
            (Execution.coercedArgumentsForField schema variableValues
              parentType siblingFieldName arguments) ->
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
            .ok ([(responseName, responseValue)], fieldErrors) := by
    intro responseName siblingFieldName arguments directives childSelectionSet
      hmem hnotProjection
    apply
      selectionSetOtherFieldsExecuteOk_fieldPairOrDeepSuccess_pathLocalProbe_of_deepSuccessWithRef_ok
        schema rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
        variableValues (parentFuel + 1) parentType leftFieldName
        rightFieldName leftArguments rightArguments leftRuntime rightRuntime
        left hleftDeep responseName siblingFieldName arguments directives
        childSelectionSet hmem
    intro siblingFieldDefinition coercedArguments hsiblingLookup hcoercion
    rw [Execution.coercedArgumentsForField_eq_of_success schema variableValues
      parentType siblingFieldName arguments siblingFieldDefinition
      coercedArguments hsiblingLookup hcoercion] at hnotProjection
    exact hnotProjection
  have hrightOther :
      ∀ responseName siblingFieldName arguments directives childSelectionSet,
        Selection.field responseName siblingFieldName arguments directives
            childSelectionSet ∈ right ->
        ¬ fieldPairProjectionTarget parentType leftFieldName rightFieldName
            leftArguments rightArguments parentType siblingFieldName
            (Execution.coercedArgumentsForField schema variableValues
              parentType siblingFieldName arguments) ->
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
            .ok ([(responseName, responseValue)], fieldErrors) := by
    intro responseName siblingFieldName arguments directives childSelectionSet
      hmem hnotProjection
    apply
      selectionSetOtherFieldsExecuteOk_fieldPairOrDeepSuccess_pathLocalProbe_of_deepSuccessWithRef_ok
        schema rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
        variableValues (parentFuel + 1) parentType leftFieldName
        rightFieldName leftArguments rightArguments leftRuntime rightRuntime
        right hrightDeep responseName siblingFieldName arguments directives
        childSelectionSet hmem
    intro siblingFieldDefinition coercedArguments hsiblingLookup hcoercion
    rw [Execution.coercedArgumentsForField_eq_of_success schema variableValues
      parentType siblingFieldName arguments siblingFieldDefinition
      coercedArguments hsiblingLookup hcoercion] at hnotProjection
    exact hnotProjection
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
      hrightInclude hleftFuel hrightFuel hleftCoercion hleftLeftTarget
      hleftRightTarget
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
      hrightInclude hleftFuel hrightFuel hrightCoercion hrightLeftTarget
      hrightRightTarget
      hrightOther
  exact
    not_selectionSetsDataEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_root_fieldName_child_response_diff_of_field_ok
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet variableValues parentFuel parentType
      responseName leftFieldName rightFieldName leftSyntaxArguments
      rightSyntaxArguments leftArguments rightArguments leftRuntime rightRuntime
      hobject hleftNormal hrightNormal hleftFree hrightFree hleftMem hrightMem
      hleftLookup hrightLookup
      (hleftCoercion responseName leftFieldName leftSyntaxArguments
        leftDirectives leftChildSelectionSet hleftMem leftFieldDefinition
        hleftLookup)
      (hrightCoercion responseName rightFieldName rightSyntaxArguments
        rightDirectives rightChildSelectionSet hrightMem rightFieldDefinition
        hrightLookup)
      hleftArguments hrightArguments hleftInclude hrightInclude hleftFuel
      hrightFuel hfieldDiff hleftChildResponse
      hrightChildResponse hchildNot hleftFieldOk hrightFieldOk

theorem
    not_selectionSetsDataEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_root_arguments_child_data_diff_of_valid_normal_append_context_fuel_ge
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
      -> selectionSetArgumentsCoercible schema [] parentType left
      -> selectionSetArgumentsCoercible schema [] parentType right
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
      -> Execution.argumentCoercionReflectsSyntaxAtEmpty schema
      -> ¬ Argument.argumentsEquivalent leftArguments rightArguments
      -> (let rootSelectionSet :=
            [Selection.inlineFragment (some parentType) [] (left ++ right)]
          let variableValues : Execution.VariableValues := []
          let leftTargetArguments :=
            Execution.coercedArgumentsForField schema variableValues parentType
              fieldName leftArguments
          let rightTargetArguments :=
            Execution.coercedArgumentsForField schema variableValues parentType
              fieldName rightArguments
          let leftInitialSelectionSet :=
            fieldPairPathLocalNextSelectionSet schema parentType leftRuntime
              fieldName leftTargetArguments (left ++ right)
          let rightInitialSelectionSet :=
            fieldPairPathLocalNextSelectionSet schema parentType rightRuntime
              fieldName rightTargetArguments (left ++ right)
          ¬ Execution.ResponseValue.semanticEquivalent
              (Execution.executeSelectionSetAsResponse schema
                (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                  (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                    rightInitialSelectionSet parentType fieldName fieldName
                    leftTargetArguments rightTargetArguments leftRuntime rightRuntime)
                  parentType fieldName fieldName leftTargetArguments
                  rightTargetArguments)
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
                    leftTargetArguments rightTargetArguments leftRuntime rightRuntime)
                  parentType fieldName fieldName leftTargetArguments
                  rightTargetArguments)
                variableValues (parentFuel - leafProbeFuel fieldDefinition.outputType)
                rightRuntime
                (projectionTargetResolverValue
                  (.object rightRuntime
                    (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                      rightInitialSelectionSet)))
                rightChildSelectionSet).data)
      -> ¬ selectionSetsDataEquivalent schema parentType left right := by
  intro hschema hleftValid hrightValid hleftCoercion hrightCoercion hleftFree
    hrightFree hleftNormal hrightNormal hparentObject hfuelAppend hleftMem
    hrightMem hlookup hcomposite hleftInclude hrightInclude hreflect
    hargumentsDiff hchildDataNot
  let rootSelectionSet : List Selection :=
    [Selection.inlineFragment (some parentType) [] (left ++ right)]
  let variableValues : Execution.VariableValues := []
  have hleftCoercionAtValues :
      selectionSetArgumentsCoercible schema variableValues parentType left := by
    simpa [variableValues] using hleftCoercion
  have hrightCoercionAtValues :
      selectionSetArgumentsCoercible schema variableValues parentType right := by
    simpa [variableValues] using hrightCoercion
  let leftTargetArguments : Execution.CoercedArguments :=
    Execution.coercedArgumentsForField schema variableValues parentType
      fieldName leftArguments
  let rightTargetArguments : Execution.CoercedArguments :=
    Execution.coercedArgumentsForField schema variableValues parentType
      fieldName rightArguments
  let leftInitialSelectionSet : List Selection :=
    fieldPairPathLocalNextSelectionSet schema parentType leftRuntime
      fieldName leftTargetArguments (left ++ right)
  let rightInitialSelectionSet : List Selection :=
    fieldPairPathLocalNextSelectionSet schema parentType rightRuntime
      fieldName rightTargetArguments (left ++ right)
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
  have hleftArgumentSuccess :
      (Execution.coerceArgumentValues schema variableValues
        fieldDefinition.arguments leftArguments).isSuccess = true := by
    exact selectionSetArgumentsCoercible_field_success_of_directiveFree
      hleftCoercionAtValues hleftFree hleftMem hlookup
  have hrightArgumentSuccess :
      (Execution.coerceArgumentValues schema variableValues
        fieldDefinition.arguments rightArguments).isSuccess = true := by
    exact selectionSetArgumentsCoercible_field_success_of_directiveFree
      hrightCoercionAtValues hrightFree hrightMem hlookup
  have htargetArgumentsDiff :
      ¬ Execution.CoercedArgument.argumentsEquivalent leftTargetArguments
          rightTargetArguments := by
    intro htargets
    have hleftResult :=
      Execution.coerceArgumentValues_equivalent_success_of_coercedArgumentsForField
        schema variableValues parentType fieldName leftArguments fieldDefinition
        leftTargetArguments hlookup hleftArgumentSuccess
        (by
          simpa [leftTargetArguments] using
            Execution.CoercedArgument.argumentsEquivalent_refl
              leftTargetArguments)
    have hrightResult :=
      Execution.coerceArgumentValues_equivalent_success_of_coercedArgumentsForField
        schema variableValues parentType fieldName rightArguments fieldDefinition
        rightTargetArguments hlookup hrightArgumentSuccess
        (by
          simpa [rightTargetArguments] using
            Execution.CoercedArgument.argumentsEquivalent_refl
              rightTargetArguments)
    have htargetsResult : Execution.ArgumentCoercionResult.equivalent
        (.success leftTargetArguments) (.success rightTargetArguments) :=
      htargets
    exact hargumentsDiff (hreflect fieldDefinition.arguments leftArguments
      rightArguments
      (Execution.ArgumentCoercionResult.equivalent_trans hleftResult
        (Execution.ArgumentCoercionResult.equivalent_trans htargetsResult
          (Execution.ArgumentCoercionResult.equivalent_symm hrightResult))))
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
        (fieldName := fieldName) (targetLeftArguments := leftTargetArguments)
        (targetRightArguments := rightTargetArguments)
        (pathArguments := leftTargetArguments)
        (arguments := leftArguments)
        (directives := leftDirectives) (leftRuntime := leftRuntime)
        (rightRuntime := rightRuntime) (selectionSet := left)
        (childSelectionSet := leftChildSelectionSet)
        (fieldDefinition := fieldDefinition) (fuel := parentFuel)
        (tag := FieldPairProbeTag.left)
        hleftValid hleftCoercionAtValues hleftFree hleftNormal hparentObject hleftFuel
        hsupport hleftContext hleftMem hlookup hcomposite hleftInclude with
    ⟨leftChildFields, leftChildErrors, hleftChildResponse⟩
  rcases
      executeSelectionSetAsResponse_fieldPairOrDeepSuccess_pathLocalProbe_target_child_of_valid_normal_context_fuel_ge
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet (left ++ right) variableValues hschema
        (variableDefinitions := rightVariableDefinitions)
        (parentType := parentType) (runtimeType := rightRuntime)
        (targetParent := parentType) (leftField := fieldName)
        (rightField := fieldName) (responseName := responseName)
        (fieldName := fieldName) (targetLeftArguments := leftTargetArguments)
        (targetRightArguments := rightTargetArguments)
        (pathArguments := rightTargetArguments)
        (arguments := rightArguments)
        (directives := rightDirectives) (leftRuntime := leftRuntime)
        (rightRuntime := rightRuntime) (selectionSet := right)
        (childSelectionSet := rightChildSelectionSet)
        (fieldDefinition := fieldDefinition) (fuel := parentFuel)
        (tag := FieldPairProbeTag.right)
        hrightValid hrightCoercionAtValues hrightFree hrightNormal hparentObject
        hrightFuel
        hsupport hrightContext hrightMem hlookup hcomposite hrightInclude with
    ⟨rightChildFields, rightChildErrors, hrightChildResponse⟩
  have hchildNot :
      ¬ Execution.ResponseValue.semanticEquivalent
        (Execution.ResponseValue.object leftChildFields)
        (Execution.ResponseValue.object rightChildFields) := by
    intro hsemantic
    apply hchildDataNot
    rw [hleftChildResponse, hrightChildResponse]
    exact hsemantic
  have hleftLeftTarget :
      ∀ responseName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
            childSelectionSet ∈ left ->
        Execution.CoercedArgument.argumentsEquivalent
            (Execution.coercedArgumentsForField schema variableValues parentType
              fieldName arguments)
            leftTargetArguments ->
          ∃ childFields childErrors,
            Execution.executeSelectionSetAsResponse schema
                (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                  (fieldPairPathLocalProbeResolvers schema
                    leftInitialSelectionSet rightInitialSelectionSet parentType
                    fieldName fieldName leftTargetArguments rightTargetArguments
                    leftRuntime rightRuntime)
                  parentType fieldName fieldName leftTargetArguments
                  rightTargetArguments)
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
        (fieldName := fieldName) (targetLeftArguments := leftTargetArguments)
        (targetRightArguments := rightTargetArguments)
        (pathArguments := leftTargetArguments)
        (arguments := arguments)
        (directives := directives) (leftRuntime := leftRuntime)
        (rightRuntime := rightRuntime) (selectionSet := left)
        (childSelectionSet := childSelectionSet)
        (fieldDefinition := fieldDefinition) (fuel := parentFuel)
        (tag := FieldPairProbeTag.left)
        hleftValid hleftCoercionAtValues hleftFree hleftNormal hparentObject hleftFuel
        hsupport hleftContext hmem hlookup hcomposite hleftInclude
  have hleftRightTarget :
      ∀ responseName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
            childSelectionSet ∈ left ->
        Execution.CoercedArgument.argumentsEquivalent
            (Execution.coercedArgumentsForField schema variableValues parentType
              fieldName arguments)
            rightTargetArguments ->
          ∃ childFields childErrors,
            Execution.executeSelectionSetAsResponse schema
                (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                  (fieldPairPathLocalProbeResolvers schema
                    leftInitialSelectionSet rightInitialSelectionSet parentType
                    fieldName fieldName leftTargetArguments rightTargetArguments
                    leftRuntime rightRuntime)
                  parentType fieldName fieldName leftTargetArguments
                  rightTargetArguments)
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
        (fieldName := fieldName) (targetLeftArguments := leftTargetArguments)
        (targetRightArguments := rightTargetArguments)
        (pathArguments := rightTargetArguments)
        (arguments := arguments)
        (directives := directives) (leftRuntime := leftRuntime)
        (rightRuntime := rightRuntime) (selectionSet := left)
        (childSelectionSet := childSelectionSet)
        (fieldDefinition := fieldDefinition) (fuel := parentFuel)
        (tag := FieldPairProbeTag.right)
        hleftValid hleftCoercionAtValues hleftFree hleftNormal hparentObject hleftFuel
        hsupport hleftContext hmem hlookup hcomposite hrightInclude
  have hrightLeftTarget :
      ∀ responseName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
            childSelectionSet ∈ right ->
        Execution.CoercedArgument.argumentsEquivalent
            (Execution.coercedArgumentsForField schema variableValues parentType
              fieldName arguments)
            leftTargetArguments ->
          ∃ childFields childErrors,
            Execution.executeSelectionSetAsResponse schema
                (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                  (fieldPairPathLocalProbeResolvers schema
                    leftInitialSelectionSet rightInitialSelectionSet parentType
                    fieldName fieldName leftTargetArguments rightTargetArguments
                    leftRuntime rightRuntime)
                  parentType fieldName fieldName leftTargetArguments
                  rightTargetArguments)
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
        (fieldName := fieldName) (targetLeftArguments := leftTargetArguments)
        (targetRightArguments := rightTargetArguments)
        (pathArguments := leftTargetArguments)
        (arguments := arguments)
        (directives := directives) (leftRuntime := leftRuntime)
        (rightRuntime := rightRuntime) (selectionSet := right)
        (childSelectionSet := childSelectionSet)
        (fieldDefinition := fieldDefinition) (fuel := parentFuel)
        (tag := FieldPairProbeTag.left)
        hrightValid hrightCoercionAtValues hrightFree hrightNormal hparentObject
        hrightFuel
        hsupport hrightContext hmem hlookup hcomposite hleftInclude
  have hrightRightTarget :
      ∀ responseName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
            childSelectionSet ∈ right ->
        Execution.CoercedArgument.argumentsEquivalent
            (Execution.coercedArgumentsForField schema variableValues parentType
              fieldName arguments)
            rightTargetArguments ->
          ∃ childFields childErrors,
            Execution.executeSelectionSetAsResponse schema
                (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                  (fieldPairPathLocalProbeResolvers schema
                    leftInitialSelectionSet rightInitialSelectionSet parentType
                    fieldName fieldName leftTargetArguments rightTargetArguments
                    leftRuntime rightRuntime)
                  parentType fieldName fieldName leftTargetArguments
                  rightTargetArguments)
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
        (fieldName := fieldName) (targetLeftArguments := leftTargetArguments)
        (targetRightArguments := rightTargetArguments)
        (pathArguments := rightTargetArguments)
        (arguments := arguments)
        (directives := directives) (leftRuntime := leftRuntime)
        (rightRuntime := rightRuntime) (selectionSet := right)
        (childSelectionSet := childSelectionSet)
        (fieldDefinition := fieldDefinition) (fuel := parentFuel)
        (tag := FieldPairProbeTag.right)
        hrightValid hrightCoercionAtValues hrightFree hrightNormal hparentObject
        hrightFuel
        hsupport hrightContext hmem hlookup hcomposite hrightInclude
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
        parentFuel hschema hleftValid hrightValid hleftCoercionAtValues
        hleftFree hrightFree
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
        parentFuel hschema hleftValid hrightValid hrightCoercionAtValues
        hleftFree hrightFree
        hleftNormal hrightNormal hparentObject hfuelAppend
        currentResponseName siblingFieldName arguments directives
        childSelectionSet hmem
  exact
    not_selectionSetsDataEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_root_arguments_child_response_diff_of_field_cases
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet variableValues parentFuel parentType
      responseName fieldName leftArguments rightArguments leftTargetArguments
      rightTargetArguments leftRuntime rightRuntime hparentObject hleftNormal
      hrightNormal hleftFree hrightFree hleftMem hrightMem hlookup
      (selectionSetArgumentCoercionSucceeds_of_argumentsCoercible
        hleftCoercionAtValues hleftFree)
      (selectionSetArgumentCoercionSucceeds_of_argumentsCoercible
        hrightCoercionAtValues hrightFree)
      (by
        simpa [leftTargetArguments] using
          Execution.CoercedArgument.argumentsEquivalent_refl leftTargetArguments)
      (by
        simpa [rightTargetArguments] using
          Execution.CoercedArgument.argumentsEquivalent_refl rightTargetArguments)
      hleftInclude hrightInclude hleafFuel htargetArgumentsDiff
      hleftChildResponse hrightChildResponse hchildNot
      (by
        intro responseName arguments directives childSelectionSet hmem harguments
        exact hleftLeftTarget responseName arguments directives childSelectionSet
          hmem (by
            simpa [Execution.coercedArgumentsForField, hlookup] using harguments))
      (by
        intro responseName arguments directives childSelectionSet hmem harguments
        exact hleftRightTarget responseName arguments directives childSelectionSet
          hmem (by
            simpa [Execution.coercedArgumentsForField, hlookup] using harguments))
      (by
        intro responseName arguments directives childSelectionSet hmem harguments
        exact hrightLeftTarget responseName arguments directives childSelectionSet
          hmem (by
            simpa [Execution.coercedArgumentsForField, hlookup] using harguments))
      (by
        intro responseName arguments directives childSelectionSet hmem harguments
        exact hrightRightTarget responseName arguments directives childSelectionSet
          hmem (by
            simpa [Execution.coercedArgumentsForField, hlookup] using harguments))
      hleftDeep hrightDeep

theorem
    not_selectionSetsDataEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_root_fieldName_child_data_diff_of_valid_normal_append_context_fuel_ge
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
      -> selectionSetArgumentsCoercible schema [] parentType left
      -> selectionSetArgumentsCoercible schema [] parentType right
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
          let variableValues : Execution.VariableValues := []
          let leftTargetArguments :=
            Execution.coercedArgumentsForField schema variableValues parentType
              leftFieldName leftArguments
          let rightTargetArguments :=
            Execution.coercedArgumentsForField schema variableValues parentType
              rightFieldName rightArguments
          let leftInitialSelectionSet :=
            fieldPairPathLocalNextSelectionSet schema parentType leftRuntime
              leftFieldName leftTargetArguments (left ++ right)
          let rightInitialSelectionSet :=
            fieldPairPathLocalNextSelectionSet schema parentType rightRuntime
              rightFieldName rightTargetArguments (left ++ right)
          ¬ Execution.ResponseValue.semanticEquivalent
              (Execution.executeSelectionSetAsResponse schema
                (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                  (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                    rightInitialSelectionSet parentType leftFieldName
                    rightFieldName leftTargetArguments rightTargetArguments
                    leftRuntime rightRuntime)
                  parentType leftFieldName rightFieldName leftTargetArguments
                  rightTargetArguments)
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
                    rightFieldName leftTargetArguments rightTargetArguments
                    leftRuntime rightRuntime)
                  parentType leftFieldName rightFieldName leftTargetArguments
                  rightTargetArguments)
                variableValues
                (parentFuel - leafProbeFuel rightFieldDefinition.outputType)
                rightRuntime
                (projectionTargetResolverValue
                  (.object rightRuntime
                    (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                      rightInitialSelectionSet)))
                rightChildSelectionSet).data)
      -> ¬ selectionSetsDataEquivalent schema parentType left right := by
  intro hschema hleftValid hrightValid hleftCoercion hrightCoercion hleftFree
    hrightFree hleftNormal hrightNormal hparentObject hfuelAppend hleftMem
    hrightMem hleftLookup hrightLookup hleftComposite hrightComposite
    hleftInclude hrightInclude hfieldDiff hchildDataNot
  let rootSelectionSet : List Selection :=
    [Selection.inlineFragment (some parentType) [] (left ++ right)]
  let variableValues : Execution.VariableValues := []
  have hleftCoercionAtValues :
      selectionSetArgumentsCoercible schema variableValues parentType left := by
    simpa [variableValues] using hleftCoercion
  have hrightCoercionAtValues :
      selectionSetArgumentsCoercible schema variableValues parentType right := by
    simpa [variableValues] using hrightCoercion
  let leftTargetArguments : Execution.CoercedArguments :=
    Execution.coercedArgumentsForField schema variableValues parentType
      leftFieldName leftArguments
  let rightTargetArguments : Execution.CoercedArguments :=
    Execution.coercedArgumentsForField schema variableValues parentType
      rightFieldName rightArguments
  let leftInitialSelectionSet : List Selection :=
    fieldPairPathLocalNextSelectionSet schema parentType leftRuntime
      leftFieldName leftTargetArguments (left ++ right)
  let rightInitialSelectionSet : List Selection :=
    fieldPairPathLocalNextSelectionSet schema parentType rightRuntime
      rightFieldName rightTargetArguments (left ++ right)
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
        (fieldName := leftFieldName)
        (targetLeftArguments := leftTargetArguments)
        (targetRightArguments := rightTargetArguments)
        (pathArguments := leftTargetArguments)
        (arguments := leftArguments)
        (directives := leftDirectives) (leftRuntime := leftRuntime)
        (rightRuntime := rightRuntime) (selectionSet := left)
        (childSelectionSet := leftChildSelectionSet)
        (fieldDefinition := leftFieldDefinition) (fuel := parentFuel)
        (tag := FieldPairProbeTag.left)
        hleftValid hleftCoercionAtValues hleftFree hleftNormal hparentObject hleftFuel
        hsupport hleftContext hleftMem hleftLookup hleftComposite
        hleftInclude
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
        (targetLeftArguments := leftTargetArguments)
        (targetRightArguments := rightTargetArguments)
        (pathArguments := rightTargetArguments)
        (arguments := rightArguments)
        (directives := rightDirectives) (leftRuntime := leftRuntime)
        (rightRuntime := rightRuntime) (selectionSet := right)
        (childSelectionSet := rightChildSelectionSet)
        (fieldDefinition := rightFieldDefinition) (fuel := parentFuel)
        (tag := FieldPairProbeTag.right)
        hrightValid hrightCoercionAtValues hrightFree hrightNormal hparentObject
        hrightFuel
        hsupport hrightContext hrightMem hrightLookup hrightComposite
        hrightInclude
    with
    ⟨rightChildFields, rightChildErrors, hrightChildResponse⟩
  have hchildNot :
      ¬ Execution.ResponseValue.semanticEquivalent
        (Execution.ResponseValue.object leftChildFields)
        (Execution.ResponseValue.object rightChildFields) := by
    intro hsemantic
    apply hchildDataNot
    rw [hleftChildResponse, hrightChildResponse]
    exact hsemantic
  have hleftLeftTarget :
      ∀ responseName arguments directives childSelectionSet,
        Selection.field responseName leftFieldName arguments directives
            childSelectionSet ∈ left ->
        Execution.CoercedArgument.argumentsEquivalent
            (Execution.coercedArgumentsForField schema variableValues parentType
              leftFieldName arguments)
            leftTargetArguments ->
          ∃ childFields childErrors,
            Execution.executeSelectionSetAsResponse schema
                (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                  (fieldPairPathLocalProbeResolvers schema
                    leftInitialSelectionSet rightInitialSelectionSet
                    parentType leftFieldName rightFieldName leftTargetArguments
                    rightTargetArguments leftRuntime rightRuntime)
                  parentType leftFieldName rightFieldName leftTargetArguments
                  rightTargetArguments)
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
        (fieldName := leftFieldName)
        (targetLeftArguments := leftTargetArguments)
        (targetRightArguments := rightTargetArguments)
        (pathArguments := leftTargetArguments)
        (arguments := arguments)
        (directives := directives) (leftRuntime := leftRuntime)
        (rightRuntime := rightRuntime) (selectionSet := left)
        (childSelectionSet := childSelectionSet)
        (fieldDefinition := leftFieldDefinition) (fuel := parentFuel)
        (tag := FieldPairProbeTag.left)
        hleftValid hleftCoercionAtValues hleftFree hleftNormal hparentObject hleftFuel
        hsupport hleftContext hmem hleftLookup hleftComposite hleftInclude
  have hleftRightTarget :
      ∀ responseName arguments directives childSelectionSet,
        Selection.field responseName rightFieldName arguments directives
            childSelectionSet ∈ left ->
        Execution.CoercedArgument.argumentsEquivalent
            (Execution.coercedArgumentsForField schema variableValues parentType
              rightFieldName arguments)
            rightTargetArguments ->
          ∃ childFields childErrors,
            Execution.executeSelectionSetAsResponse schema
                (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                  (fieldPairPathLocalProbeResolvers schema
                    leftInitialSelectionSet rightInitialSelectionSet
                    parentType leftFieldName rightFieldName leftTargetArguments
                    rightTargetArguments leftRuntime rightRuntime)
                  parentType leftFieldName rightFieldName leftTargetArguments
                  rightTargetArguments)
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
        (targetLeftArguments := leftTargetArguments)
        (targetRightArguments := rightTargetArguments)
        (pathArguments := rightTargetArguments)
        (arguments := arguments)
        (directives := directives) (leftRuntime := leftRuntime)
        (rightRuntime := rightRuntime) (selectionSet := left)
        (childSelectionSet := childSelectionSet)
        (fieldDefinition := rightFieldDefinition) (fuel := parentFuel)
        (tag := FieldPairProbeTag.right)
        hleftValid hleftCoercionAtValues hleftFree hleftNormal hparentObject hleftFuel
        hsupport hleftContext hmem hrightLookup hrightComposite
        hrightInclude
  have hrightLeftTarget :
      ∀ responseName arguments directives childSelectionSet,
        Selection.field responseName leftFieldName arguments directives
            childSelectionSet ∈ right ->
        Execution.CoercedArgument.argumentsEquivalent
            (Execution.coercedArgumentsForField schema variableValues parentType
              leftFieldName arguments)
            leftTargetArguments ->
          ∃ childFields childErrors,
            Execution.executeSelectionSetAsResponse schema
                (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                  (fieldPairPathLocalProbeResolvers schema
                    leftInitialSelectionSet rightInitialSelectionSet
                    parentType leftFieldName rightFieldName leftTargetArguments
                    rightTargetArguments leftRuntime rightRuntime)
                  parentType leftFieldName rightFieldName leftTargetArguments
                  rightTargetArguments)
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
        (fieldName := leftFieldName)
        (targetLeftArguments := leftTargetArguments)
        (targetRightArguments := rightTargetArguments)
        (pathArguments := leftTargetArguments)
        (arguments := arguments)
        (directives := directives) (leftRuntime := leftRuntime)
        (rightRuntime := rightRuntime) (selectionSet := right)
        (childSelectionSet := childSelectionSet)
        (fieldDefinition := leftFieldDefinition) (fuel := parentFuel)
        (tag := FieldPairProbeTag.left)
        hrightValid hrightCoercionAtValues hrightFree hrightNormal hparentObject
        hrightFuel
        hsupport hrightContext hmem hleftLookup hleftComposite hleftInclude
  have hrightRightTarget :
      ∀ responseName arguments directives childSelectionSet,
        Selection.field responseName rightFieldName arguments directives
            childSelectionSet ∈ right ->
        Execution.CoercedArgument.argumentsEquivalent
            (Execution.coercedArgumentsForField schema variableValues parentType
              rightFieldName arguments)
            rightTargetArguments ->
          ∃ childFields childErrors,
            Execution.executeSelectionSetAsResponse schema
                (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                  (fieldPairPathLocalProbeResolvers schema
                    leftInitialSelectionSet rightInitialSelectionSet
                    parentType leftFieldName rightFieldName leftTargetArguments
                    rightTargetArguments leftRuntime rightRuntime)
                  parentType leftFieldName rightFieldName leftTargetArguments
                  rightTargetArguments)
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
        (targetLeftArguments := leftTargetArguments)
        (targetRightArguments := rightTargetArguments)
        (pathArguments := rightTargetArguments)
        (arguments := arguments)
        (directives := directives) (leftRuntime := leftRuntime)
        (rightRuntime := rightRuntime) (selectionSet := right)
        (childSelectionSet := childSelectionSet)
        (fieldDefinition := rightFieldDefinition) (fuel := parentFuel)
        (tag := FieldPairProbeTag.right)
        hrightValid hrightCoercionAtValues hrightFree hrightNormal hparentObject
        hrightFuel
        hsupport hrightContext hmem hrightLookup hrightComposite
        hrightInclude
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
        parentFuel hschema hleftValid hrightValid hleftCoercionAtValues
        hleftFree hrightFree
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
        parentFuel hschema hleftValid hrightValid hrightCoercionAtValues
        hleftFree hrightFree
        hleftNormal hrightNormal hparentObject hfuelAppend
        currentResponseName siblingFieldName arguments directives
        childSelectionSet hmem
  exact
    not_selectionSetsDataEquivalent_of_fieldPairOrDeepSuccess_pathLocalProbe_root_fieldName_child_response_diff_of_field_cases
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet variableValues parentFuel parentType
      responseName leftFieldName rightFieldName leftArguments rightArguments
      leftTargetArguments rightTargetArguments leftRuntime rightRuntime
      hparentObject hleftNormal hrightNormal hleftFree hrightFree hleftMem
      hrightMem hleftLookup hrightLookup
      (selectionSetArgumentCoercionSucceeds_of_argumentsCoercible
        hleftCoercionAtValues hleftFree)
      (selectionSetArgumentCoercionSucceeds_of_argumentsCoercible
        hrightCoercionAtValues hrightFree)
      (by
        simpa [leftTargetArguments] using
          Execution.CoercedArgument.argumentsEquivalent_refl leftTargetArguments)
      (by
        simpa [rightTargetArguments] using
          Execution.CoercedArgument.argumentsEquivalent_refl rightTargetArguments)
      hleftInclude hrightInclude hleftLeafFuel hrightLeafFuel hfieldDiff
      hleftChildResponse hrightChildResponse hchildNot
      (by
        intro responseName arguments directives childSelectionSet hmem harguments
        exact hleftLeftTarget responseName arguments directives childSelectionSet
          hmem (by
            simpa [Execution.coercedArgumentsForField, hleftLookup] using
              harguments))
      (by
        intro responseName arguments directives childSelectionSet hmem harguments
        exact hleftRightTarget responseName arguments directives childSelectionSet
          hmem (by
            simpa [Execution.coercedArgumentsForField, hrightLookup] using
              harguments))
      (by
        intro responseName arguments directives childSelectionSet hmem harguments
        exact hrightLeftTarget responseName arguments directives childSelectionSet
          hmem (by
            simpa [Execution.coercedArgumentsForField, hleftLookup] using
              harguments))
      (by
        intro responseName arguments directives childSelectionSet hmem harguments
        exact hrightRightTarget responseName arguments directives childSelectionSet
          hmem (by
            simpa [Execution.coercedArgumentsForField, hrightLookup] using
              harguments))
      hleftDeep hrightDeep

end GroundTypeNormalization

end NormalForm

end GraphQL
