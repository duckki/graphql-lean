import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.ExecutionSuccess
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.ProbeTags
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.Readiness

/-!
Selection-set success helpers for tagged uniqueness probes.

These lemmas package the field-level tagged probe execution facts into the
`field_ok` shape consumed by the semantic-separation helpers.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

def selectionSetDeepHeadPromotionAvailable
    (schema : Schema) (rootSelectionSet : List Selection)
    (parentType : Name) (selectionSet : List Selection)
    : Prop :=
  ∀ abstractTargetParent abstractTargetField targetArguments targetRuntimeType
      targetFieldDefinition,
    schema.lookupField abstractTargetParent abstractTargetField
      = some targetFieldDefinition
    -> (TypeRef.named targetFieldDefinition.outputType.namedType).isCompositeBool schema
        = true
    -> objectTypeNameBool schema targetFieldDefinition.outputType.namedType = false
    -> abstractRuntimeForFieldHeadDeep? schema abstractTargetParent
          abstractTargetField targetArguments parentType selectionSet
        = some targetRuntimeType
    -> ∃ runtimeType,
        abstractRuntimeForFieldHeadDeep? schema abstractTargetParent
            abstractTargetField targetArguments abstractTargetParent
            rootSelectionSet
          = some runtimeType
        ∧ schema.typeIncludesObjectBool
            targetFieldDefinition.outputType.namedType runtimeType
          = true

theorem executeField_fieldPairProbe_tagged_object_field_ok_of_field_children
    (schema : Schema) (rootSelectionSet : List Selection)
    (variableValues : Execution.VariableValues)
    (fuel : Nat) (targetParent leftField rightField parentType sourceRuntimeType : Name)
    (leftArguments rightArguments : List Argument)
    (tag : FieldPairProbeTag)
    (selectionSet : List Selection)
    : (∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
        -> ∃ fieldDefinition,
            schema.lookupField parentType fieldName = some fieldDefinition
            ∧ leafProbeFuel fieldDefinition.outputType ≤ fuel
            ∧ ((TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
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
                          (.object childRuntimeType (some tag))
                          childSelectionSet
                        = ({
                              data := Execution.ResponseValue.object responseFields,
                              errors := childErrors
                            }
                            : Execution.Response))))
      -> ∀ responseName fieldName arguments directives childSelectionSet,
          Selection.field responseName fieldName arguments directives childSelectionSet
            ∈ selectionSet
          -> ∃ responseValue fieldErrors,
              Execution.executeField schema
                (fieldPairProbeResolvers schema rootSelectionSet targetParent
                  leftField rightField leftArguments rightArguments)
                variableValues (fuel + 1)
                (.object sourceRuntimeType (some tag)) responseName
                [{
                  parentType := parentType
                  responseName := responseName
                  fieldName := fieldName
                  arguments := arguments
                  selectionSet := childSelectionSet
                }]
              = .ok ([(responseName, responseValue)], fieldErrors) := by
  intro hchildren responseName fieldName arguments directives
    childSelectionSet hmem
  rcases hchildren responseName fieldName arguments directives
      childSelectionSet hmem with
    ⟨fieldDefinition, hlookup, hfuel, hleafOrChild⟩
  rcases hleafOrChild with hleaf | hchild
  · refine
      ⟨leafProbeResponseValue fieldDefinition.outputType tag.scalar, 0,
        ?_⟩
    exact
      executeField_fieldPairProbe_tagged_object_leaf schema rootSelectionSet
        variableValues fuel targetParent leftField rightField parentType
        fieldName sourceRuntimeType responseName leftArguments
        rightArguments arguments tag childSelectionSet fieldDefinition
        hlookup hfuel hleaf
  · rcases hchild with
      ⟨childRuntimeType, responseFields, childErrors, hruntime, hinclude,
        hchildResponse⟩
    rcases
        executeField_fieldPairProbe_tagged_object_objectProbe_ok_of_child_response
          schema rootSelectionSet variableValues fuel targetParent
          leftField rightField parentType fieldName sourceRuntimeType
          responseName leftArguments rightArguments arguments tag
          childSelectionSet fieldDefinition childRuntimeType responseFields
          childErrors hlookup hruntime hinclude hfuel hchildResponse with
      ⟨responseValue, fieldErrors, hexecute, _hnonNull⟩
    exact ⟨responseValue, fieldErrors, hexecute⟩

theorem executeSelectionSetAsResponse_fieldPairProbe_tagged_object_of_field_children
    (schema : Schema) (rootSelectionSet : List Selection)
    (variableValues : Execution.VariableValues)
    (fuel : Nat) (targetParent leftField rightField parentType sourceRuntimeType : Name)
    (leftArguments rightArguments : List Argument)
    (tag : FieldPairProbeTag)
    (selectionSet : List Selection)
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
                              (.object childRuntimeType (some tag))
                              childSelectionSet
                            = ({
                                  data := Execution.ResponseValue.object responseFields,
                                  errors := childErrors
                                }
                                : Execution.Response))))
      -> ∃ responseFields errors,
          Execution.executeSelectionSetAsResponse schema
            (fieldPairProbeResolvers schema rootSelectionSet targetParent
              leftField rightField leftArguments rightArguments)
            variableValues (fuel + 1) parentType
            (.object sourceRuntimeType (some tag)) selectionSet
          = ({ data := Execution.ResponseValue.object responseFields, errors := errors }
              : Execution.Response) := by
  intro hfree hnormal hobject hchildren
  let resolvers :=
    fieldPairProbeResolvers schema rootSelectionSet targetParent leftField
      rightField leftArguments rightArguments
  have hfieldOk :
      ∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
            childSelectionSet ∈ selectionSet ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema resolvers variableValues (fuel + 1)
              (.object sourceRuntimeType (some tag)) responseName
              [{
                parentType := parentType
                responseName := responseName
                fieldName := fieldName
                arguments := arguments
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(responseName, responseValue)], fieldErrors) := by
    intro responseName fieldName arguments directives childSelectionSet hmem
    rcases hchildren responseName fieldName arguments directives
        childSelectionSet hmem with
      ⟨fieldDefinition, hlookup, hfuel, hleafOrChild⟩
    rcases hleafOrChild with hleaf | hchild
    · refine
        ⟨leafProbeResponseValue fieldDefinition.outputType tag.scalar, 0,
          ?_⟩
      exact
        executeField_fieldPairProbe_tagged_object_leaf schema rootSelectionSet
          variableValues fuel targetParent leftField rightField parentType
          fieldName sourceRuntimeType responseName leftArguments
          rightArguments arguments tag childSelectionSet fieldDefinition
          hlookup hfuel hleaf
    · rcases hchild with
        ⟨childRuntimeType, responseFields, childErrors, hruntime, hinclude,
          hchildResponse⟩
      rcases
          executeField_fieldPairProbe_tagged_object_objectProbe_ok_of_child_response
            schema rootSelectionSet variableValues fuel targetParent
            leftField rightField parentType fieldName sourceRuntimeType
            responseName leftArguments rightArguments arguments tag
            childSelectionSet fieldDefinition childRuntimeType responseFields
            childErrors hlookup hruntime hinclude hfuel hchildResponse with
        ⟨responseValue, fieldErrors, hexecute, _hnonNull⟩
      exact ⟨responseValue, fieldErrors, hexecute⟩
  exact
    ExecutionSuccess.executeSelectionSetAsResponse_object_of_field_ok schema
      resolvers variableValues (fuel + 1) parentType
      (.object sourceRuntimeType (some tag)) selectionSet hfree hnormal
      hobject hfieldOk

theorem
    executeSelectionSetAsResponse_fieldPairProbe_tagged_abstract_of_inlineFragment_body_children
    (schema : Schema) (rootSelectionSet : List Selection)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField : Name)
    (leftArguments rightArguments : List Argument) (tag : FieldPairProbeTag)
    {normalParentType runtimeType : Name} {selectionSet : List Selection}
    : objectTypeNameBool schema normalParentType = false
      -> objectTypeNameBool schema runtimeType = true
      -> selectionSetDirectiveFree selectionSet
      -> selectionSetNormal schema normalParentType selectionSet
      -> (∀ typeCondition bodySelectionSet,
            Selection.inlineFragment (some typeCondition) [] bodySelectionSet
              ∈ selectionSet
            -> ∀ bodyResponseName bodyFieldName bodyArguments bodyDirectives
                  bodyChildSelectionSet,
                Selection.field bodyResponseName bodyFieldName bodyArguments
                    bodyDirectives bodyChildSelectionSet
                  ∈ bodySelectionSet
                -> ∃ bodyFieldDefinition,
                    schema.lookupField typeCondition bodyFieldName
                      = some bodyFieldDefinition
                    ∧ leafProbeFuel bodyFieldDefinition.outputType ≤ fuel
                    ∧ ((TypeRef.named
                            bodyFieldDefinition.outputType.namedType).isCompositeBool
                            schema
                          = false
                        ∨ ∃ childRuntimeType responseFields childErrors,
                            (((objectTypeNameBool schema
                                      bodyFieldDefinition.outputType.namedType
                                    = true
                                  ∧ childRuntimeType
                                    = bodyFieldDefinition.outputType.namedType)
                                ∨ ((TypeRef.named
                                        bodyFieldDefinition.outputType.namedType).isCompositeBool
                                        schema
                                      = true
                                    ∧ objectTypeNameBool schema
                                        bodyFieldDefinition.outputType.namedType
                                      = false
                                    ∧ abstractRuntimeForFieldHeadDeep? schema
                                        typeCondition bodyFieldName bodyArguments
                                        typeCondition rootSelectionSet
                                      = some childRuntimeType))
                              ∧ schema.typeIncludesObjectBool
                                  bodyFieldDefinition.outputType.namedType
                                  childRuntimeType
                                = true
                              ∧ Execution.executeSelectionSetAsResponse schema
                                  (fieldPairProbeResolvers schema rootSelectionSet
                                    targetParent leftField rightField leftArguments
                                    rightArguments)
                                  variableValues
                                  (fuel - leafProbeFuel bodyFieldDefinition.outputType)
                                  childRuntimeType
                                  (.object childRuntimeType (some tag))
                                  bodyChildSelectionSet
                                = ({
                                      data :=
                                        Execution.ResponseValue.object responseFields,
                                      errors := childErrors
                                    }
                                    : Execution.Response))))
      -> ∃ responseFields errors,
          Execution.executeSelectionSetAsResponse schema
            (fieldPairProbeResolvers schema rootSelectionSet targetParent
              leftField rightField leftArguments rightArguments)
            variableValues (fuel + 1) runtimeType
            (.object runtimeType (some tag)) selectionSet
          = ({ data := Execution.ResponseValue.object responseFields, errors := errors }
              : Execution.Response) := by
  intro hnonObject hruntimeObject hfree hnormal hbodyChildren
  let resolvers :=
    fieldPairProbeResolvers schema rootSelectionSet targetParent leftField
      rightField leftArguments rightArguments
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
            have hbodyFree : selectionSetDirectiveFree bodySelectionSet :=
              selectionSetDirectiveFree_inlineFragment_child_of_mem hfree
                hinlineMem
            have hbodyNormal :
                selectionSetNormal schema runtimeType bodySelectionSet :=
              (selectionSetNormal_inlineFragment_child_of_mem hnormal
                hinlineMem).2
            rcases
                executeSelectionSetAsResponse_fieldPairProbe_tagged_object_of_field_children
                  schema rootSelectionSet variableValues fuel targetParent
                  leftField rightField runtimeType runtimeType leftArguments
                  rightArguments tag bodySelectionSet hbodyFree hbodyNormal
                  hruntimeObject
                  (by
                    intro bodyResponseName bodyFieldName bodyArguments
                      bodyDirectives bodyChildSelectionSet hfieldMem
                    exact
                      hbodyChildren runtimeType bodySelectionSet hinlineMem
                        bodyResponseName bodyFieldName bodyArguments
                        bodyDirectives bodyChildSelectionSet hfieldMem) with
              ⟨bodyFields, bodyErrors, hbodyResponse⟩
            have hmiddle :
                Execution.executeSelectionSet schema resolvers variableValues
                  (fuel + 1) runtimeType (.object runtimeType (some tag))
                  (pref ++ Selection.inlineFragment (some runtimeType) []
                    bodySelectionSet :: suffix)
                =
                Execution.executeSelectionSet schema resolvers variableValues
                  (fuel + 1) runtimeType (.object runtimeType (some tag))
                  [Selection.inlineFragment (some runtimeType) []
                    bodySelectionSet] :=
              executeSelectionSet_middle_inlineFragment_only_eq_singleton_at_runtime_parent
                schema resolvers variableValues (fuel + 1) (some tag)
                hnonObject hruntimeObject hfree hnormal
            have happly :
                Execution.doesFragmentTypeApplyBool schema runtimeType
                  (.object runtimeType (some tag)) runtimeType = true :=
              doesFragmentTypeApplyBool_object_self schema
                (ref := some tag) hruntimeObject
            have hflatten :
                Execution.executeSelectionSet schema resolvers variableValues
                  (fuel + 1) runtimeType (.object runtimeType (some tag))
                  [Selection.inlineFragment (some runtimeType) []
                    bodySelectionSet]
                =
                Execution.executeSelectionSet schema resolvers variableValues
                  (fuel + 1) runtimeType (.object runtimeType (some tag))
                  bodySelectionSet := by
              simpa using
                executeSelectionSet_inlineFragment_some_directiveFree_apply_flatten
                  schema resolvers variableValues (fuel + 1) runtimeType
                  runtimeType (.object runtimeType (some tag))
                  bodySelectionSet [] happly
            refine ⟨bodyFields, bodyErrors, ?_⟩
            calc
              Execution.executeSelectionSetAsResponse schema resolvers variableValues
                  (fuel + 1) runtimeType (.object runtimeType (some tag))
                  (pref ++ Selection.inlineFragment (some runtimeType) []
                    bodySelectionSet :: suffix)
                  =
                Execution.executeSelectionSetAsResponse schema resolvers variableValues
                  (fuel + 1) runtimeType (.object runtimeType (some tag))
                  [Selection.inlineFragment (some runtimeType) []
                    bodySelectionSet] := by
                    simp [Execution.executeSelectionSetAsResponse, hmiddle]
              _ =
                Execution.executeSelectionSetAsResponse schema resolvers variableValues
                  (fuel + 1) runtimeType (.object runtimeType (some tag))
                  bodySelectionSet := by
                    simp [Execution.executeSelectionSetAsResponse, hflatten]
              _ = ({ data := Execution.ResponseValue.object bodyFields, errors := bodyErrors } : Execution.Response) :=
                    hbodyResponse
  · have hcollect :
        Execution.collectFields schema variableValues runtimeType
          (.object runtimeType (some tag)) selectionSet = [] :=
      collectFields_inlineFragments_without_typeCondition_eq_nil_at_runtime_parent
        schema variableValues (normalParentType := normalParentType)
        (executionParentType := runtimeType) (runtimeType := runtimeType)
        (some tag) hnonObject hfree hnormal hruntimeMem
    refine ⟨[], 0, ?_⟩
    simp [Execution.executeSelectionSetAsResponse, Execution.selectionSetResultToResponse,
      Execution.executeSelectionSet, Execution.executeRootSelectionSet,
      hcollect, Execution.executeCollectedFields]

theorem
    executeSelectionSetAsResponse_fieldPairProbe_tagged_of_valid_normal_promoted_fuel_ge_size
    (schema : Schema) (rootSelectionSet : List Selection)
    (variableValues : Execution.VariableValues)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ∀ n parentType variableDefinitions (selectionSet : List Selection)
            fuel sourceRuntimeType targetParent leftField rightField
            (leftArguments rightArguments : List Argument)
            (tag : FieldPairProbeTag),
          SelectionSet.size selectionSet < n
          -> selectionSetDeepProbeFuel schema parentType selectionSet ≤ fuel
          -> Validation.selectionSetValid schema variableDefinitions parentType
              selectionSet
          -> selectionSetDirectiveFree selectionSet
          -> selectionSetNormal schema parentType selectionSet
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
          -> ∃ responseFields errors,
              Execution.executeSelectionSetAsResponse schema
                (fieldPairProbeResolvers schema rootSelectionSet targetParent
                  leftField rightField leftArguments rightArguments)
                variableValues (fuel + 1) sourceRuntimeType
                (.object sourceRuntimeType (some tag)) selectionSet
              = ({
                    data := Execution.ResponseValue.object responseFields,
                    errors := errors
                  }
                  : Execution.Response) := by
  intro hschema n
  induction n with
  | zero =>
      intro parentType variableDefinitions selectionSet fuel sourceRuntimeType
        targetParent leftField rightField leftArguments rightArguments tag
        hsize _hfuel _hvalid _hfree _hnormal _hinclude _hpromote
        _hheadPromote
      omega
  | succ n ih =>
      intro parentType variableDefinitions selectionSet fuel sourceRuntimeType
        targetParent leftField rightField leftArguments rightArguments tag
        hsize hfuel hvalid hfree hnormal hinclude hpromote hheadPromote
      have hsourceObject :
          objectTypeNameBool schema sourceRuntimeType = true :=
        objectTypeNameBool_of_typeIncludesObjectBool hschema hinclude
      by_cases hparentObject :
          objectTypeNameBool schema parentType = true
      · have hsourceEq : sourceRuntimeType = parentType :=
          typeIncludesObjectBool_eq_of_objectTypeNameBool_true schema
            hparentObject hinclude
        subst sourceRuntimeType
        refine
          executeSelectionSetAsResponse_fieldPairProbe_tagged_object_of_field_children
            schema rootSelectionSet variableValues fuel targetParent
            leftField rightField parentType parentType leftArguments
            rightArguments tag selectionSet hfree hnormal hparentObject ?_
        intro responseName fieldName arguments directives childSelectionSet
          hmem
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
              selectionSetDeepProbeFuel_field_mem schema parentType
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
          have hchildFree : selectionSetDirectiveFree childSelectionSet :=
            selectionSetDirectiveFree_field_child_of_mem hfree hmem
          have hchildNormal :
              selectionSetNormal schema fieldDefinition.outputType.namedType
                childSelectionSet :=
            selectionSetNormal_field_child_of_mem_lookup hnormal hmem hlookup
          have hchildPromote :
              ∀ abstractTargetParent abstractTargetField targetRuntimeType
                  targetFieldDefinition,
                schema.lookupField abstractTargetParent abstractTargetField =
                  some targetFieldDefinition ->
                (TypeRef.named
                    targetFieldDefinition.outputType.namedType).isCompositeBool
                  schema = true ->
                objectTypeNameBool schema
                    targetFieldDefinition.outputType.namedType = false ->
                abstractRuntimeForFieldDeep? schema abstractTargetParent
                  abstractTargetField fieldDefinition.outputType.namedType
                  childSelectionSet = some targetRuntimeType ->
                  ∃ runtimeType,
                    abstractRuntimeForFieldDeep? schema abstractTargetParent
                      abstractTargetField abstractTargetParent
                      rootSelectionSet = some runtimeType
                      ∧ schema.typeIncludesObjectBool
                        targetFieldDefinition.outputType.namedType
                        runtimeType = true := by
            intro abstractTargetParent abstractTargetField targetRuntimeType
              targetFieldDefinition htargetLookup htargetComposite
              htargetNonObject hlocalRuntime
            rcases
                abstractRuntimeForFieldDeep?_object_field_child_promote_some_of_valid_normal
                  hvalid hfree hnormal hmem hlookup htargetLookup
                  htargetComposite htargetNonObject hlocalRuntime with
              ⟨parentRuntimeType, hparentRuntime, _hparentInclude⟩
            exact
              hpromote abstractTargetParent abstractTargetField
                parentRuntimeType targetFieldDefinition htargetLookup
                htargetComposite htargetNonObject hparentRuntime
          have hchildHeadPromote :
              selectionSetDeepHeadPromotionAvailable schema rootSelectionSet
                fieldDefinition.outputType.namedType childSelectionSet := by
            intro abstractTargetParent abstractTargetField targetArguments
              targetRuntimeType targetFieldDefinition htargetLookup
              htargetComposite htargetNonObject hlocalRuntime
            rcases
                abstractRuntimeForFieldHeadDeep?_object_field_child_promote_some_of_valid_normal
                  hvalid hfree hnormal hmem hlookup hlocalRuntime with
              ⟨parentRuntimeType, hparentRuntime⟩
            exact
              hheadPromote abstractTargetParent abstractTargetField
                targetArguments parentRuntimeType targetFieldDefinition
                htargetLookup htargetComposite htargetNonObject
                hparentRuntime
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
            rcases
                ih fieldDefinition.outputType.namedType variableDefinitions
                  childSelectionSet childFuel
                  fieldDefinition.outputType.namedType targetParent leftField
                  rightField leftArguments rightArguments tag hchildSize
                  hchildFuel hchildValid hchildFree hchildNormal
                  hchildInclude hchildPromote hchildHeadPromote with
              ⟨responseFields, errors, hchildResponse⟩
            have hchildFuelEq :
                childFuel + 1 =
                  fuel - leafProbeFuel fieldDefinition.outputType := by
              dsimp [childFuel]
              omega
            refine
              Or.inr
                ⟨fieldDefinition.outputType.namedType, responseFields,
                  errors, ?_, hchildInclude, ?_⟩
            · exact Or.inl ⟨hreturnObject, rfl⟩
            · simpa [hchildFuelEq] using hchildResponse
          · have hreturnNonObject :
                objectTypeNameBool schema
                    fieldDefinition.outputType.namedType = false := by
              cases h :
                  objectTypeNameBool schema
                    fieldDefinition.outputType.namedType <;>
                simp [h] at hreturnObject ⊢
            rcases
                abstractRuntimeForFieldHeadDeep?_some_of_valid_normal_abstract_mem_lookup
                  hvalid hnormal hmem hlookup hreturnComposite
                  hreturnNonObject with
              ⟨localRuntimeType, hlocalRuntime, _hlocalInclude⟩
            rcases
                hheadPromote parentType fieldName arguments localRuntimeType
                  fieldDefinition hlookup hreturnComposite hreturnNonObject
                  hlocalRuntime with
              ⟨runtimeType, hruntime, hruntimeInclude⟩
            have hchildNonempty : childSelectionSet ≠ [] := by
              rcases
                  selectionSetValid_field_lookup_leaf_or_composite_child
                    hvalid hmem with
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
            rcases
                ih fieldDefinition.outputType.namedType variableDefinitions
                  childSelectionSet childFuel runtimeType targetParent
                  leftField rightField leftArguments rightArguments tag
                  hchildSize hchildFuel hchildValid hchildFree hchildNormal
                  hruntimeInclude hchildPromote hchildHeadPromote with
              ⟨responseFields, errors, hchildResponse⟩
            have hchildFuelEq :
                childFuel + 1 =
                  fuel - leafProbeFuel fieldDefinition.outputType := by
              dsimp [childFuel]
              omega
            refine
              Or.inr
                ⟨runtimeType, responseFields, errors, ?_,
                  hruntimeInclude, ?_⟩
            · exact
                Or.inr ⟨hreturnComposite, hreturnNonObject, hruntime⟩
            · simpa [hchildFuelEq] using hchildResponse
      · have hparentNonObject :
            objectTypeNameBool schema parentType = false := by
          cases h : objectTypeNameBool schema parentType <;>
            simp [h] at hparentObject ⊢
        refine
          executeSelectionSetAsResponse_fieldPairProbe_tagged_abstract_of_inlineFragment_body_children
            schema rootSelectionSet variableValues fuel targetParent
            leftField rightField leftArguments rightArguments tag
            (normalParentType := parentType)
            (runtimeType := sourceRuntimeType)
            (selectionSet := selectionSet) hparentNonObject
            hsourceObject hfree hnormal ?_
        intro typeCondition bodySelectionSet hinlineMem bodyResponseName
          bodyFieldName bodyArguments bodyDirectives bodyChildSelectionSet
          hbodyFieldMem
        have hbodyValid :
            Validation.selectionSetValid schema variableDefinitions
              typeCondition bodySelectionSet :=
          selectionSetValid_inlineFragment_some_child_of_mem hvalid
            hinlineMem
        have hbodyFree : selectionSetDirectiveFree bodySelectionSet :=
          selectionSetDirectiveFree_inlineFragment_child_of_mem hfree
            hinlineMem
        rcases selectionSetNormal_inlineFragment_child_of_mem hnormal
            hinlineMem with
          ⟨htypeObject, hbodyNormal⟩
        have hbodyObject :
            objectTypeNameBool schema typeCondition = true :=
          objectTypeNameBool_eq_true_of_objectType_forNormality schema
            htypeObject
        have hinlineFuel :
            selectionSetDeepProbeFuel schema typeCondition bodySelectionSet
              ≤ fuel := by
          have hlocal :=
            selectionSetDeepProbeFuel_inlineFragment_some_mem schema
              parentType selectionSet typeCondition
              ([] : List DirectiveApplication) bodySelectionSet hinlineMem
          omega
        have hbodyPromote :
            ∀ abstractTargetParent abstractTargetField targetRuntimeType
                targetFieldDefinition,
              schema.lookupField abstractTargetParent abstractTargetField =
                some targetFieldDefinition ->
              (TypeRef.named
                  targetFieldDefinition.outputType.namedType).isCompositeBool
                schema = true ->
              objectTypeNameBool schema
                  targetFieldDefinition.outputType.namedType = false ->
              abstractRuntimeForFieldDeep? schema abstractTargetParent
                abstractTargetField typeCondition bodySelectionSet =
                some targetRuntimeType ->
                ∃ runtimeType,
                  abstractRuntimeForFieldDeep? schema abstractTargetParent
                    abstractTargetField abstractTargetParent
                    rootSelectionSet = some runtimeType
                    ∧ schema.typeIncludesObjectBool
                      targetFieldDefinition.outputType.namedType
                      runtimeType = true := by
          intro abstractTargetParent abstractTargetField targetRuntimeType
            targetFieldDefinition htargetLookup htargetComposite
            htargetNonObject hbodyLocalRuntime
          rcases
              abstractRuntimeForFieldDeep?_inlineFragment_child_promote_some_of_valid_normal
                hvalid hfree hnormal hinlineMem htargetLookup
                htargetComposite htargetNonObject hbodyLocalRuntime with
            ⟨childRuntimeType, hchildRuntime, _hchildInclude⟩
          exact
            hpromote abstractTargetParent abstractTargetField
              childRuntimeType targetFieldDefinition htargetLookup
              htargetComposite htargetNonObject hchildRuntime
        have hbodyHeadPromote :
            selectionSetDeepHeadPromotionAvailable schema rootSelectionSet
              typeCondition bodySelectionSet := by
          intro abstractTargetParent abstractTargetField targetArguments
            targetRuntimeType targetFieldDefinition htargetLookup
            htargetComposite htargetNonObject hbodyLocalRuntime
          rcases
              abstractRuntimeForFieldHeadDeep?_inlineFragment_child_promote_some_of_valid_normal
                hvalid hfree hnormal hinlineMem hbodyLocalRuntime with
            ⟨childRuntimeType, hchildRuntime⟩
          exact
            hheadPromote abstractTargetParent abstractTargetField
              targetArguments childRuntimeType targetFieldDefinition
              htargetLookup htargetComposite htargetNonObject hchildRuntime
        rcases selectionSetValid_field_lookup_of_mem hbodyValid
            hbodyFieldMem with
          ⟨bodyFieldDefinition, hbodyLookup, _hbodyArguments,
            _hbodyFieldSelectionValid⟩
        have hbodyLeafFuel :
            leafProbeFuel bodyFieldDefinition.outputType ≤ fuel := by
          have hfieldFuel :=
            leafProbeFuel_le_selectionSetDeepProbeFuel_of_field_mem schema
              typeCondition (selectionSet := bodySelectionSet)
              (responseName := bodyResponseName)
              (fieldName := bodyFieldName)
              (arguments := bodyArguments)
              (directives := bodyDirectives)
              (childSelectionSet := bodyChildSelectionSet)
              (fieldDefinition := bodyFieldDefinition)
              hbodyFieldMem hbodyLookup
          omega
        refine ⟨bodyFieldDefinition, hbodyLookup, hbodyLeafFuel, ?_⟩
        by_cases hreturnLeaf :
            (TypeRef.named
                bodyFieldDefinition.outputType.namedType).isCompositeBool
              schema = false
        · exact Or.inl hreturnLeaf
        · have hreturnComposite :
              (TypeRef.named
                  bodyFieldDefinition.outputType.namedType).isCompositeBool
                schema = true := by
            cases h :
                (TypeRef.named
                    bodyFieldDefinition.outputType.namedType).isCompositeBool
                  schema <;>
              simp [h] at hreturnLeaf ⊢
          have hfieldDeepFuel :
              leafProbeFuel bodyFieldDefinition.outputType
                + selectionSetDeepProbeFuel schema
                  bodyFieldDefinition.outputType.namedType
                  bodyChildSelectionSet
                + 1 ≤ fuel := by
            have hlocal :=
              selectionSetDeepProbeFuel_field_mem schema typeCondition
                bodySelectionSet bodyResponseName bodyFieldName
                bodyArguments bodyDirectives bodyChildSelectionSet
                bodyFieldDefinition hbodyFieldMem hbodyLookup
            omega
          let childFuel :=
            fuel - leafProbeFuel bodyFieldDefinition.outputType - 1
          have hchildSize :
              SelectionSet.size bodyChildSelectionSet < n := by
            have hbodyLt :=
              selectionSet_size_inlineFragment_child_lt_of_mem
                (typeCondition := some typeCondition)
                (directives := ([] : List DirectiveApplication))
                (childSelectionSet := bodySelectionSet)
                (selectionSet := selectionSet) hinlineMem
            have hfieldLt :=
              selectionSet_size_field_child_lt_of_mem
                (responseName := bodyResponseName)
                (fieldName := bodyFieldName)
                (arguments := bodyArguments)
                (directives := bodyDirectives)
                (childSelectionSet := bodyChildSelectionSet)
                (selectionSet := bodySelectionSet) hbodyFieldMem
            omega
          have hchildFuel :
              selectionSetDeepProbeFuel schema
                  bodyFieldDefinition.outputType.namedType
                  bodyChildSelectionSet
                ≤ childFuel := by
            dsimp [childFuel]
            omega
          have hchildFree :
              selectionSetDirectiveFree bodyChildSelectionSet :=
            selectionSetDirectiveFree_field_child_of_mem hbodyFree
              hbodyFieldMem
          have hchildNormal :
              selectionSetNormal schema
                bodyFieldDefinition.outputType.namedType
                bodyChildSelectionSet :=
            selectionSetNormal_field_child_of_mem_lookup hbodyNormal
              hbodyFieldMem hbodyLookup
          have hchildPromote :
              ∀ abstractTargetParent abstractTargetField targetRuntimeType
                  targetFieldDefinition,
                schema.lookupField abstractTargetParent abstractTargetField =
                  some targetFieldDefinition ->
                (TypeRef.named
                    targetFieldDefinition.outputType.namedType).isCompositeBool
                  schema = true ->
                objectTypeNameBool schema
                    targetFieldDefinition.outputType.namedType = false ->
                abstractRuntimeForFieldDeep? schema abstractTargetParent
                  abstractTargetField
                  bodyFieldDefinition.outputType.namedType
                  bodyChildSelectionSet = some targetRuntimeType ->
                  ∃ runtimeType,
                    abstractRuntimeForFieldDeep? schema abstractTargetParent
                      abstractTargetField abstractTargetParent
                      rootSelectionSet = some runtimeType
                      ∧ schema.typeIncludesObjectBool
                        targetFieldDefinition.outputType.namedType
                        runtimeType = true := by
            intro abstractTargetParent abstractTargetField targetRuntimeType
              targetFieldDefinition htargetLookup htargetComposite
              htargetNonObject hlocalRuntime
            rcases
                abstractRuntimeForFieldDeep?_object_field_child_promote_some_of_valid_normal
                  hbodyValid hbodyFree hbodyNormal hbodyFieldMem
                  hbodyLookup htargetLookup htargetComposite
                  htargetNonObject hlocalRuntime with
              ⟨bodyRuntimeType, hbodyRuntime, _hbodyInclude⟩
            exact
              hbodyPromote abstractTargetParent abstractTargetField
                bodyRuntimeType targetFieldDefinition htargetLookup
                htargetComposite htargetNonObject hbodyRuntime
          have hchildHeadPromote :
              selectionSetDeepHeadPromotionAvailable schema rootSelectionSet
                bodyFieldDefinition.outputType.namedType
                bodyChildSelectionSet := by
            intro abstractTargetParent abstractTargetField targetArguments
              targetRuntimeType targetFieldDefinition htargetLookup
              htargetComposite htargetNonObject hlocalRuntime
            rcases
                abstractRuntimeForFieldHeadDeep?_object_field_child_promote_some_of_valid_normal
                  hbodyValid hbodyFree hbodyNormal hbodyFieldMem
                  hbodyLookup hlocalRuntime with
              ⟨bodyRuntimeType, hbodyRuntime⟩
            exact
              hbodyHeadPromote abstractTargetParent abstractTargetField
                targetArguments bodyRuntimeType targetFieldDefinition
                htargetLookup htargetComposite htargetNonObject
                hbodyRuntime
          by_cases hreturnObject :
              objectTypeNameBool schema
                  bodyFieldDefinition.outputType.namedType = true
          · have hchildValid :
                Validation.selectionSetValid schema variableDefinitions
                  bodyFieldDefinition.outputType.namedType
                  bodyChildSelectionSet :=
              selectionSetValid_object_field_child_of_mem_lookup hbodyValid
                hbodyFieldMem hbodyLookup hreturnObject
            have hchildInclude :
                schema.typeIncludesObjectBool
                    bodyFieldDefinition.outputType.namedType
                    bodyFieldDefinition.outputType.namedType = true :=
              typeIncludesObjectBool_self_of_objectTypeNameBool schema
                hreturnObject
            rcases
                ih bodyFieldDefinition.outputType.namedType
                  variableDefinitions bodyChildSelectionSet childFuel
                  bodyFieldDefinition.outputType.namedType targetParent
                  leftField rightField leftArguments rightArguments tag
                  hchildSize hchildFuel hchildValid hchildFree
                  hchildNormal hchildInclude hchildPromote
                  hchildHeadPromote with
              ⟨responseFields, errors, hchildResponse⟩
            have hchildFuelEq :
                childFuel + 1 =
                  fuel - leafProbeFuel bodyFieldDefinition.outputType := by
              dsimp [childFuel]
              omega
            refine
              Or.inr
                ⟨bodyFieldDefinition.outputType.namedType, responseFields,
                  errors, ?_, hchildInclude, ?_⟩
            · exact Or.inl ⟨hreturnObject, rfl⟩
            · simpa [hchildFuelEq] using hchildResponse
          · have hreturnNonObject :
                objectTypeNameBool schema
                    bodyFieldDefinition.outputType.namedType = false := by
              cases h :
                  objectTypeNameBool schema
                    bodyFieldDefinition.outputType.namedType <;>
                simp [h] at hreturnObject ⊢
            rcases
                abstractRuntimeForFieldHeadDeep?_some_of_valid_normal_abstract_mem_lookup
                  hbodyValid hbodyNormal hbodyFieldMem hbodyLookup
                  hreturnComposite hreturnNonObject with
              ⟨localRuntimeType, hlocalRuntime, _hlocalInclude⟩
            rcases
                hbodyHeadPromote typeCondition bodyFieldName bodyArguments
                  localRuntimeType
                  bodyFieldDefinition hbodyLookup hreturnComposite
                  hreturnNonObject hlocalRuntime with
              ⟨runtimeType, hruntime, hruntimeInclude⟩
            have hchildNonempty : bodyChildSelectionSet ≠ [] := by
              rcases
                  selectionSetValid_field_lookup_leaf_or_composite_child
                    hbodyValid hbodyFieldMem with
                ⟨candidateDefinition, hcandidateLookup, hkind⟩
              have hdefinitionEq :
                  candidateDefinition = bodyFieldDefinition := by
                rw [hbodyLookup] at hcandidateLookup
                exact (Option.some.inj hcandidateLookup).symm
              subst candidateDefinition
              rcases hkind with hleaf | hcomposite
              · have hleafComposite := hleaf.1
                rw [hreturnComposite] at hleafComposite
                simp at hleafComposite
              · exact hcomposite.2.1
            have hchildValid :
                Validation.selectionSetValid schema variableDefinitions
                  bodyFieldDefinition.outputType.namedType
                  bodyChildSelectionSet :=
              selectionSetValid_field_child_of_mem_lookup hbodyValid
                hbodyFieldMem hchildNonempty hbodyLookup
            rcases
                ih bodyFieldDefinition.outputType.namedType
                  variableDefinitions bodyChildSelectionSet childFuel
                  runtimeType targetParent leftField rightField
                  leftArguments rightArguments tag hchildSize hchildFuel
                  hchildValid hchildFree hchildNormal hruntimeInclude
                  hchildPromote hchildHeadPromote with
              ⟨responseFields, errors, hchildResponse⟩
            have hchildFuelEq :
                childFuel + 1 =
                  fuel - leafProbeFuel bodyFieldDefinition.outputType := by
              dsimp [childFuel]
              omega
            refine
              Or.inr
                ⟨runtimeType, responseFields, errors, ?_,
                  hruntimeInclude, ?_⟩
            · exact
                Or.inr ⟨hreturnComposite, hreturnNonObject, hruntime⟩
            · simpa [hchildFuelEq] using hchildResponse

theorem
    executeSelectionSetAsResponse_fieldPairProbe_tagged_of_valid_normal_promoted_deepProbeFuel
    (schema : Schema) (rootSelectionSet : List Selection)
    (variableValues : Execution.VariableValues)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ∀ parentType variableDefinitions (selectionSet : List Selection)
            sourceRuntimeType targetParent leftField rightField
            (leftArguments rightArguments : List Argument)
            (tag : FieldPairProbeTag),
          Validation.selectionSetValid schema variableDefinitions parentType selectionSet
          -> selectionSetDirectiveFree selectionSet
          -> selectionSetNormal schema parentType selectionSet
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
          -> ∃ responseFields errors,
              Execution.executeSelectionSetAsResponse schema
                (fieldPairProbeResolvers schema rootSelectionSet targetParent
                  leftField rightField leftArguments rightArguments)
                variableValues
                (selectionSetDeepProbeFuel schema parentType selectionSet + 1)
                sourceRuntimeType (.object sourceRuntimeType (some tag))
                selectionSet
              = ({
                    data := Execution.ResponseValue.object responseFields,
                    errors := errors
                  }
                  : Execution.Response) := by
  intro hschema parentType variableDefinitions selectionSet sourceRuntimeType
    targetParent leftField rightField leftArguments rightArguments tag hvalid
    hfree hnormal hinclude hpromote hheadPromote
  exact
    executeSelectionSetAsResponse_fieldPairProbe_tagged_of_valid_normal_promoted_fuel_ge_size
      schema rootSelectionSet variableValues hschema
      (SelectionSet.size selectionSet + 1) parentType variableDefinitions
      selectionSet (selectionSetDeepProbeFuel schema parentType selectionSet)
      sourceRuntimeType targetParent leftField rightField leftArguments
      rightArguments tag (by omega) (by omega) hvalid hfree hnormal
      hinclude hpromote
      hheadPromote

theorem
    executeField_fieldPairProbe_tagged_object_field_ok_of_valid_normal_promoted_fuel_ge
    (schema : Schema) (rootSelectionSet : List Selection)
    (variableValues : Execution.VariableValues)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ∀ parentType variableDefinitions (selectionSet : List Selection)
            fuel sourceRuntimeType targetParent leftField rightField
            (leftArguments rightArguments : List Argument)
            (tag : FieldPairProbeTag),
          selectionSetDeepProbeFuel schema parentType selectionSet ≤ fuel
          -> Validation.selectionSetValid schema variableDefinitions parentType
              selectionSet
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
          -> ∀ responseName fieldName arguments directives childSelectionSet,
              Selection.field responseName fieldName arguments directives
                  childSelectionSet
                ∈ selectionSet
              -> ∃ responseValue fieldErrors,
                  Execution.executeField schema
                    (fieldPairProbeResolvers schema rootSelectionSet targetParent
                      leftField rightField leftArguments rightArguments)
                    variableValues
                    (fuel + 1)
                    (.object sourceRuntimeType (some tag)) responseName
                    [{
                      parentType := parentType,
                      responseName := responseName,
                      fieldName := fieldName,
                      arguments := arguments,
                      selectionSet := childSelectionSet
                    }]
                  = .ok ([(responseName, responseValue)], fieldErrors) := by
  intro hschema parentType variableDefinitions selectionSet
    fuel sourceRuntimeType targetParent leftField rightField leftArguments
    rightArguments tag hfuel hvalid hfree hnormal hobject hinclude hpromote
    hheadPromote
  refine
    executeField_fieldPairProbe_tagged_object_field_ok_of_field_children
      schema rootSelectionSet variableValues fuel targetParent leftField
      rightField parentType sourceRuntimeType leftArguments rightArguments
      tag selectionSet ?_
  intro responseName fieldName arguments directives childSelectionSet hmem
  rcases selectionSetValid_field_lookup_of_mem hvalid hmem with
    ⟨fieldDefinition, hlookup, _harguments, _hfieldSelectionValid⟩
  have hleafFuel :
      leafProbeFuel fieldDefinition.outputType ≤ fuel := by
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
      have hlocal :
          leafProbeFuel fieldDefinition.outputType
            + selectionSetDeepProbeFuel schema
              fieldDefinition.outputType.namedType childSelectionSet
            + 1
            ≤ selectionSetDeepProbeFuel schema parentType selectionSet :=
        selectionSetDeepProbeFuel_field_mem schema parentType
          selectionSet responseName fieldName arguments directives
          childSelectionSet fieldDefinition hmem hlookup
      omega
    let childFuel := fuel - leafProbeFuel fieldDefinition.outputType - 1
    have hchildSize :
        SelectionSet.size childSelectionSet <
          SelectionSet.size selectionSet := by
      exact
        selectionSet_size_field_child_lt_of_mem
          (responseName := responseName) (fieldName := fieldName)
          (arguments := arguments) (directives := directives)
          (childSelectionSet := childSelectionSet)
          (selectionSet := selectionSet) hmem
    have hchildFuel :
        selectionSetDeepProbeFuel schema
            fieldDefinition.outputType.namedType childSelectionSet
          ≤ childFuel := by
      dsimp [childFuel]
      omega
    have hchildFree : selectionSetDirectiveFree childSelectionSet :=
      selectionSetDirectiveFree_field_child_of_mem hfree hmem
    have hchildNormal :
        selectionSetNormal schema fieldDefinition.outputType.namedType
          childSelectionSet :=
      selectionSetNormal_field_child_of_mem_lookup hnormal hmem hlookup
    have hchildPromote :
        ∀ abstractTargetParent abstractTargetField targetRuntimeType
            targetFieldDefinition,
          schema.lookupField abstractTargetParent abstractTargetField =
            some targetFieldDefinition ->
          (TypeRef.named
              targetFieldDefinition.outputType.namedType).isCompositeBool
            schema = true ->
          objectTypeNameBool schema
              targetFieldDefinition.outputType.namedType = false ->
          abstractRuntimeForFieldDeep? schema abstractTargetParent
            abstractTargetField fieldDefinition.outputType.namedType
            childSelectionSet = some targetRuntimeType ->
          ∃ runtimeType,
            abstractRuntimeForFieldDeep? schema abstractTargetParent
              abstractTargetField abstractTargetParent rootSelectionSet =
              some runtimeType
              ∧ schema.typeIncludesObjectBool
                targetFieldDefinition.outputType.namedType runtimeType =
                true := by
      intro abstractTargetParent abstractTargetField targetRuntimeType
        targetFieldDefinition htargetLookup htargetComposite
        htargetNonObject hlocalRuntime
      rcases
          abstractRuntimeForFieldDeep?_object_field_child_promote_some_of_valid_normal
            hvalid hfree hnormal hmem hlookup htargetLookup
            htargetComposite htargetNonObject hlocalRuntime with
        ⟨parentRuntimeType, hparentRuntime, _hparentInclude⟩
      exact
        hpromote abstractTargetParent abstractTargetField
          parentRuntimeType targetFieldDefinition htargetLookup
          htargetComposite htargetNonObject hparentRuntime
    have hchildHeadPromote :
        selectionSetDeepHeadPromotionAvailable schema rootSelectionSet
          fieldDefinition.outputType.namedType childSelectionSet := by
      intro abstractTargetParent abstractTargetField targetArguments
        targetRuntimeType targetFieldDefinition htargetLookup
        htargetComposite htargetNonObject hlocalRuntime
      rcases
          abstractRuntimeForFieldHeadDeep?_object_field_child_promote_some_of_valid_normal
            hvalid hfree hnormal hmem hlookup hlocalRuntime with
        ⟨parentRuntimeType, hparentRuntime⟩
      exact
        hheadPromote abstractTargetParent abstractTargetField
          targetArguments parentRuntimeType targetFieldDefinition
          htargetLookup htargetComposite htargetNonObject hparentRuntime
    by_cases hreturnObject :
        objectTypeNameBool schema fieldDefinition.outputType.namedType = true
    · have hchildValid :
          Validation.selectionSetValid schema variableDefinitions
            fieldDefinition.outputType.namedType childSelectionSet :=
        selectionSetValid_object_field_child_of_mem_lookup hvalid hmem
          hlookup hreturnObject
      have hchildInclude :
          schema.typeIncludesObjectBool fieldDefinition.outputType.namedType
            fieldDefinition.outputType.namedType = true :=
        typeIncludesObjectBool_self_of_objectTypeNameBool schema
          hreturnObject
      rcases
          executeSelectionSetAsResponse_fieldPairProbe_tagged_of_valid_normal_promoted_fuel_ge_size
            schema rootSelectionSet variableValues hschema
            (SelectionSet.size selectionSet)
            fieldDefinition.outputType.namedType variableDefinitions
            childSelectionSet childFuel
            fieldDefinition.outputType.namedType targetParent leftField
            rightField leftArguments rightArguments tag hchildSize
            hchildFuel hchildValid hchildFree hchildNormal hchildInclude
            hchildPromote hchildHeadPromote with
        ⟨responseFields, errors, hchildResponse⟩
      have hchildFuelEq :
          childFuel + 1 =
            fuel - leafProbeFuel fieldDefinition.outputType := by
        dsimp [childFuel]
        omega
      refine
        Or.inr
          ⟨fieldDefinition.outputType.namedType, responseFields, errors,
            ?_, hchildInclude, ?_⟩
      · exact Or.inl ⟨hreturnObject, rfl⟩
      · simpa [hchildFuelEq] using hchildResponse
    · have hreturnNonObject :
          objectTypeNameBool schema
              fieldDefinition.outputType.namedType = false := by
        cases h :
            objectTypeNameBool schema
              fieldDefinition.outputType.namedType <;>
          simp [h] at hreturnObject ⊢
      rcases
          abstractRuntimeForFieldHeadDeep?_some_of_valid_normal_abstract_mem_lookup
            hvalid hnormal hmem hlookup hreturnComposite
            hreturnNonObject with
        ⟨localRuntimeType, hlocalRuntime, _hlocalInclude⟩
      rcases
          hheadPromote parentType fieldName arguments localRuntimeType
            fieldDefinition hlookup hreturnComposite hreturnNonObject
            hlocalRuntime with
        ⟨runtimeType, hruntime, hruntimeInclude⟩
      have hchildNonempty : childSelectionSet ≠ [] := by
        rcases
            selectionSetValid_field_lookup_leaf_or_composite_child
              hvalid hmem with
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
      rcases
          executeSelectionSetAsResponse_fieldPairProbe_tagged_of_valid_normal_promoted_fuel_ge_size
            schema rootSelectionSet variableValues hschema
            (SelectionSet.size selectionSet)
            fieldDefinition.outputType.namedType variableDefinitions
            childSelectionSet childFuel runtimeType targetParent leftField
            rightField leftArguments rightArguments tag hchildSize
            hchildFuel hchildValid hchildFree hchildNormal
            hruntimeInclude hchildPromote hchildHeadPromote with
        ⟨responseFields, errors, hchildResponse⟩
      have hchildFuelEq :
          childFuel + 1 =
            fuel - leafProbeFuel fieldDefinition.outputType := by
        dsimp [childFuel]
        omega
      refine
        Or.inr
          ⟨runtimeType, responseFields, errors, ?_, hruntimeInclude, ?_⟩
      · exact Or.inr ⟨hreturnComposite, hreturnNonObject, hruntime⟩
      · simpa [hchildFuelEq] using hchildResponse

theorem
    executeField_fieldPairProbe_tagged_object_field_ok_of_valid_normal_promoted_deepProbeFuel
    (schema : Schema) (rootSelectionSet : List Selection)
    (variableValues : Execution.VariableValues)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ∀ parentType variableDefinitions (selectionSet : List Selection)
            sourceRuntimeType targetParent leftField rightField
            (leftArguments rightArguments : List Argument)
            (tag : FieldPairProbeTag),
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
          -> ∀ responseName fieldName arguments directives childSelectionSet,
              Selection.field responseName fieldName arguments directives
                  childSelectionSet
                ∈ selectionSet
              -> ∃ responseValue fieldErrors,
                  Execution.executeField schema
                    (fieldPairProbeResolvers schema rootSelectionSet targetParent
                      leftField rightField leftArguments rightArguments)
                    variableValues
                    (selectionSetDeepProbeFuel schema parentType selectionSet + 1)
                    (.object sourceRuntimeType (some tag)) responseName
                    [{
                      parentType := parentType,
                      responseName := responseName,
                      fieldName := fieldName,
                      arguments := arguments,
                      selectionSet := childSelectionSet
                    }]
                  = .ok ([(responseName, responseValue)], fieldErrors) := by
  intro hschema parentType variableDefinitions selectionSet sourceRuntimeType
    targetParent leftField rightField leftArguments rightArguments tag hvalid
    hfree hnormal hobject hinclude hpromote hheadPromote
  exact
    executeField_fieldPairProbe_tagged_object_field_ok_of_valid_normal_promoted_fuel_ge
      schema rootSelectionSet variableValues hschema parentType
      variableDefinitions selectionSet
      (selectionSetDeepProbeFuel schema parentType selectionSet)
      sourceRuntimeType targetParent leftField rightField leftArguments
      rightArguments tag (by omega) hvalid hfree hnormal hobject hinclude
      hpromote hheadPromote

end GroundTypeNormalization

end NormalForm

end GraphQL
