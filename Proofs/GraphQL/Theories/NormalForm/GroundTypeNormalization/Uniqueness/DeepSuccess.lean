import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.Readiness

/-!
Selection-set success helpers for deep uniqueness probes.

These lemmas generalize the object-only deep-success readiness theorem to the
abstract-parent case used when lifting differences through abstract fields.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

theorem executeSelectionSetAsResponse_deepSelectionSetSuccessWithRef_abstract_matching_inlineFragment_nonempty
    {ObjectRef : Type} (schema : Schema) (rootSelectionSet : List Selection)
    (objectRef : ObjectRef) (variableValues : Execution.VariableValues) (fuel : Nat)
    {normalParentType runtimeType : Name} {selectionSet bodySelectionSet : List Selection}
    : objectTypeNameBool schema normalParentType = false
      -> objectTypeNameBool schema runtimeType = true
      -> selectionSetDirectiveFree selectionSet
      -> selectionSetNormal schema normalParentType selectionSet
      -> Selection.inlineFragment (some runtimeType) [] bodySelectionSet ∈ selectionSet
      -> bodySelectionSet ≠ []
      -> (∀ bodyResponseName bodyFieldName bodyArguments bodyDirectives
              bodyChildSelectionSet,
            Selection.field bodyResponseName bodyFieldName bodyArguments
                bodyDirectives bodyChildSelectionSet
              ∈ bodySelectionSet
            -> ∃ bodyFieldDefinition,
                schema.lookupField runtimeType bodyFieldName = some bodyFieldDefinition
                ∧ leafProbeFuel bodyFieldDefinition.outputType ≤ fuel
                ∧ deepFieldSelectionSetExecutionReadyWithRef schema
                    rootSelectionSet objectRef variableValues
                    (fuel - leafProbeFuel bodyFieldDefinition.outputType)
                    runtimeType bodyResponseName bodyFieldName bodyArguments
                    bodyChildSelectionSet bodyFieldDefinition)
      -> ∃ responseField responseFields errors,
          Execution.executeSelectionSetAsResponse schema
            (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet objectRef)
            variableValues (fuel + 1) runtimeType
            (.object runtimeType objectRef) selectionSet
          = ({
                data :=
                  Execution.ResponseValue.object (responseField :: responseFields),
                errors := errors
              }
              : Execution.Response) := by
  intro hnonObject hruntimeObject hfree hnormal hinlineMem hbodyNonempty
    hbodyReady
  rcases List.mem_iff_append.mp hinlineMem with
    ⟨pref, suffix, hselectionSet⟩
  subst selectionSet
  have hinlineMem' :
      Selection.inlineFragment (some runtimeType) [] bodySelectionSet ∈
        pref ++ Selection.inlineFragment (some runtimeType) []
          bodySelectionSet :: suffix := by
    exact List.mem_append_right _ (by simp)
  rcases selectionSetNormal_inlineFragment_child_of_mem hnormal
      hinlineMem' with
    ⟨_htypeObject, hbodyNormal⟩
  have hbodyFree : selectionSetDirectiveFree bodySelectionSet :=
    selectionSetDirectiveFree_inlineFragment_child_of_mem hfree
      hinlineMem'
  rcases selectionSetNormal_field_mem_of_object_nonempty hbodyNormal
      hruntimeObject hbodyNonempty with
    ⟨bodyResponseName, bodyFieldName, bodyArguments, bodyDirectives,
      bodyChildSelectionSet, hbodyFieldMem⟩
  have hsource :
      ∃ runtimeType' ref',
        (Execution.ResolverValue.object runtimeType objectRef :
          Execution.ResolverValue ObjectRef)
          =
            Execution.ResolverValue.object runtimeType' ref'
          ∧ schema.typeIncludesObjectBool runtimeType runtimeType' =
            true := by
    exact
      ⟨runtimeType, objectRef, rfl,
        typeIncludesObjectBool_self_of_objectTypeNameBool schema
          hruntimeObject⟩
  rcases
      executeSelectionSet_deepSelectionSetSuccessWithRef_deepFieldReady
        schema rootSelectionSet objectRef variableValues fuel runtimeType
        (.object runtimeType objectRef) bodySelectionSet hbodyFree
        hbodyNormal hruntimeObject hsource hbodyReady with
    ⟨bodyFields, bodyErrors, hbodyExecute, hbodyKeys⟩
  have hbodyResponseNameMem :
      bodyResponseName ∈ bodyFields.map Prod.fst := by
    rw [hbodyKeys]
    exact List.mem_filterMap.mpr
      ⟨Selection.field bodyResponseName bodyFieldName bodyArguments
          bodyDirectives bodyChildSelectionSet,
        hbodyFieldMem,
        by simp [Selection.responseName?]⟩
  cases bodyFields with
  | nil =>
      simp at hbodyResponseNameMem
  | cons responseField responseFields =>
      have hmiddle :
          Execution.executeSelectionSet schema
            (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet
              objectRef)
            variableValues (fuel + 1) runtimeType
            (.object runtimeType objectRef)
            (pref ++ Selection.inlineFragment (some runtimeType) []
              bodySelectionSet :: suffix)
          =
          Execution.executeSelectionSet schema
            (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet
              objectRef)
            variableValues (fuel + 1) runtimeType
            (.object runtimeType objectRef)
            [Selection.inlineFragment (some runtimeType) []
              bodySelectionSet] :=
        executeSelectionSet_middle_inlineFragment_only_eq_singleton_at_runtime_parent
          schema
          (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet
            objectRef)
          variableValues (fuel + 1) objectRef hnonObject
          hruntimeObject hfree hnormal
      have happly :
          Execution.doesFragmentTypeApplyBool schema runtimeType
            (.object runtimeType objectRef) runtimeType = true :=
        doesFragmentTypeApplyBool_object_self schema (ref := objectRef)
          hruntimeObject
      have hflatten :
          Execution.executeSelectionSet schema
            (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet
              objectRef)
            variableValues (fuel + 1) runtimeType
            (.object runtimeType objectRef)
            [Selection.inlineFragment (some runtimeType) []
              bodySelectionSet]
          =
          Execution.executeSelectionSet schema
            (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet
              objectRef)
            variableValues (fuel + 1) runtimeType
            (.object runtimeType objectRef) bodySelectionSet := by
        simpa using
          executeSelectionSet_inlineFragment_some_directiveFree_apply_flatten
            schema
            (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet
              objectRef)
            variableValues (fuel + 1) runtimeType runtimeType
            (.object runtimeType objectRef) bodySelectionSet [] happly
      refine ⟨responseField, responseFields, bodyErrors, ?_⟩
      simp [Execution.executeSelectionSetAsResponse, Execution.selectionSetResultToResponse,
        hmiddle, hflatten, hbodyExecute]

theorem executeSelectionSetAsResponse_deepSelectionSetSuccessWithRef_valid_normal_promoted_fuel_ge_size
    {ObjectRef : Type} (schema : Schema) (rootSelectionSet : List Selection)
    (objectRef : ObjectRef) (variableValues : Execution.VariableValues)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ∀ n parentType variableDefinitions (selectionSet : List Selection)
            fuel sourceRuntimeType,
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
          -> ∃ responseFields errors,
              Execution.executeSelectionSetAsResponse schema
                (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet
                  objectRef)
                variableValues (fuel + 1) sourceRuntimeType
                (.object sourceRuntimeType objectRef) selectionSet
              = ({
                    data := Execution.ResponseValue.object responseFields,
                    errors := errors
                  }
                  : Execution.Response) := by
  intro hschema n
  induction n with
  | zero =>
      intro parentType variableDefinitions selectionSet fuel sourceRuntimeType
        hsize _hfuel _hvalid _hfree _hnormal _hinclude _hpromote
      omega
  | succ n ih =>
      intro parentType variableDefinitions selectionSet fuel sourceRuntimeType
        hsize hfuel hvalid hfree hnormal hinclude hpromote
      have hsourceObject :
          objectTypeNameBool schema sourceRuntimeType = true :=
        objectTypeNameBool_of_typeIncludesObjectBool hschema hinclude
      by_cases hparentObject : objectTypeNameBool schema parentType = true
      · have hsourceEq : sourceRuntimeType = parentType :=
          typeIncludesObjectBool_eq_of_objectTypeNameBool_true schema
            hparentObject hinclude
        subst sourceRuntimeType
        have hsource :
            ∃ runtimeType ref,
              (Execution.ResolverValue.object parentType objectRef :
                Execution.ResolverValue ObjectRef)
                =
                  Execution.ResolverValue.object runtimeType ref
                ∧ schema.typeIncludesObjectBool parentType runtimeType =
                  true := by
          exact ⟨parentType, objectRef, rfl, hinclude⟩
        exact
          executeSelectionSetAsResponse_deepSelectionSetSuccessWithRef_valid_normal_object_promoted_fuel_ge
            schema rootSelectionSet objectRef variableValues hschema
            parentType variableDefinitions selectionSet fuel
            (.object parentType objectRef) hvalid hfree hnormal
            hparentObject hsource hpromote hfuel
      · have hparentNonObject :
            objectTypeNameBool schema parentType = false := by
          cases h : objectTypeNameBool schema parentType <;>
            simp [h] at hparentObject ⊢
        by_cases hruntimeMem :
            sourceRuntimeType ∈
              selectionSet.filterMap inlineFragmentTypeCondition?
        · rcases List.mem_filterMap.mp hruntimeMem with
            ⟨selection, hselectionMem, hselectionRuntime⟩
          cases selection with
          | field responseName fieldName arguments directives
              childSelectionSet =>
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
                  have hinlineMem :
                      Selection.inlineFragment (some sourceRuntimeType) []
                          bodySelectionSet ∈ selectionSet :=
                    hselectionMem
                  have hbodyValid :
                      Validation.selectionSetValid schema variableDefinitions
                        sourceRuntimeType bodySelectionSet :=
                    selectionSetValid_inlineFragment_some_child_of_mem hvalid
                      hinlineMem
                  have hbodyFree :
                      selectionSetDirectiveFree bodySelectionSet :=
                    selectionSetDirectiveFree_inlineFragment_child_of_mem
                      hfree hinlineMem
                  rcases
                      selectionSetNormal_inlineFragment_child_of_mem hnormal
                        hinlineMem with
                    ⟨_htypeObject, hbodyNormal⟩
                  have hbodyFuel :
                      selectionSetDeepProbeFuel schema sourceRuntimeType
                          bodySelectionSet
                        ≤ fuel := by
                    have hlocal :=
                      selectionSetDeepProbeFuel_inlineFragment_some_mem
                        schema parentType selectionSet sourceRuntimeType []
                        bodySelectionSet hinlineMem
                    omega
                  have hbodyPromote :
                      ∀ abstractTargetParent abstractTargetField
                          targetRuntimeType targetFieldDefinition,
                        schema.lookupField abstractTargetParent
                            abstractTargetField =
                          some targetFieldDefinition ->
                        (TypeRef.named
                            targetFieldDefinition.outputType.namedType).isCompositeBool
                          schema = true ->
                        objectTypeNameBool schema
                            targetFieldDefinition.outputType.namedType =
                          false ->
                        abstractRuntimeForFieldDeep? schema
                          abstractTargetParent abstractTargetField
                          sourceRuntimeType bodySelectionSet =
                          some targetRuntimeType ->
                        ∃ runtimeType,
                          abstractRuntimeForFieldDeep? schema
                              abstractTargetParent abstractTargetField
                              abstractTargetParent rootSelectionSet =
                            some runtimeType
                            ∧ schema.typeIncludesObjectBool
                              targetFieldDefinition.outputType.namedType
                              runtimeType = true := by
                    intro abstractTargetParent abstractTargetField
                      targetRuntimeType targetFieldDefinition htargetLookup
                      htargetComposite htargetNonObject hbodyRuntime
                    rcases
                        abstractRuntimeForFieldDeep?_inlineFragment_child_promote_some_of_valid_normal
                          hvalid hfree hnormal hinlineMem htargetLookup
                          htargetComposite htargetNonObject hbodyRuntime with
                      ⟨childRuntimeType, hchildRuntime, _hchildInclude⟩
                    exact
                      hpromote abstractTargetParent abstractTargetField
                        childRuntimeType targetFieldDefinition htargetLookup
                        htargetComposite htargetNonObject hchildRuntime
                  rcases
                      executeSelectionSetAsResponse_deepSelectionSetSuccessWithRef_abstract_matching_inlineFragment_nonempty
                        schema rootSelectionSet objectRef variableValues
                        fuel hparentNonObject hsourceObject hfree hnormal
                        hinlineMem
                        (selectionSetValid_inlineFragment_some_child_nonempty_of_mem
                          hvalid hinlineMem)
                        (by
                          intro bodyResponseName bodyFieldName bodyArguments
                            bodyDirectives bodyChildSelectionSet hbodyFieldMem
                          rcases
                              selectionSetValid_field_lookup_of_mem
                                hbodyValid hbodyFieldMem with
                            ⟨bodyFieldDefinition, hbodyLookup,
                              _hbodyArguments, _hbodyFieldSelectionValid⟩
                          have hleafFuel :
                              leafProbeFuel bodyFieldDefinition.outputType
                                ≤ fuel := by
                            have hfieldFuel :=
                              leafProbeFuel_le_selectionSetDeepProbeFuel_of_field_mem
                                schema sourceRuntimeType
                                (selectionSet := bodySelectionSet)
                                (responseName := bodyResponseName)
                                (fieldName := bodyFieldName)
                                (arguments := bodyArguments)
                                (directives := bodyDirectives)
                                (childSelectionSet :=
                                  bodyChildSelectionSet)
                                (fieldDefinition := bodyFieldDefinition)
                                hbodyFieldMem hbodyLookup
                            omega
                          refine
                            ⟨bodyFieldDefinition, hbodyLookup,
                              hleafFuel, ?_⟩
                          rcases
                            deepFieldSelectionSetReadyWithRef_of_valid_normal_object_promoted_fuel_ge_size
                              schema rootSelectionSet objectRef
                              variableValues hschema
                              (SelectionSet.size bodySelectionSet + 1)
                              sourceRuntimeType variableDefinitions
                              bodySelectionSet fuel (by omega) hbodyFuel
                              hbodyValid hbodyFree hbodyNormal
                              hsourceObject hbodyPromote bodyResponseName
                              bodyFieldName bodyArguments bodyDirectives
                              bodyChildSelectionSet hbodyFieldMem with
                            ⟨candidateDefinition, hcandidateLookup,
                              _hcandidateFuel, hcandidateReady⟩
                          have hcandidateEq :
                              candidateDefinition = bodyFieldDefinition := by
                            rw [hbodyLookup] at hcandidateLookup
                            exact (Option.some.inj hcandidateLookup).symm
                          subst candidateDefinition
                          exact hcandidateReady) with
                    ⟨responseField, responseFields, errors, hexecute⟩
                  exact
                    ⟨responseField :: responseFields, errors, by
                      simpa using hexecute⟩
        · have hcollect :
              Execution.collectFields schema variableValues sourceRuntimeType
                (.object sourceRuntimeType objectRef) selectionSet = [] :=
            collectFields_inlineFragments_without_typeCondition_eq_nil_at_runtime_parent
              schema variableValues (normalParentType := parentType)
              (executionParentType := sourceRuntimeType)
              (runtimeType := sourceRuntimeType) objectRef
              hparentNonObject hfree hnormal hruntimeMem
          refine ⟨[], 0, ?_⟩
          simp [Execution.executeSelectionSetAsResponse, Execution.selectionSetResultToResponse,
            Execution.executeSelectionSet, Execution.executeRootSelectionSet,
            hcollect, Execution.executeCollectedFields]

theorem executeSelectionSetAsResponse_deepSelectionSetSuccessWithRef_valid_normal_promoted_deepProbeFuel
    {ObjectRef : Type} (schema : Schema) (rootSelectionSet : List Selection)
    (objectRef : ObjectRef) (variableValues : Execution.VariableValues)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ∀ parentType variableDefinitions (selectionSet : List Selection)
            sourceRuntimeType,
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
          -> ∃ responseFields errors,
              Execution.executeSelectionSetAsResponse schema
                (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet
                  objectRef)
                variableValues
                (selectionSetDeepProbeFuel schema parentType selectionSet + 1)
                sourceRuntimeType (.object sourceRuntimeType objectRef)
                selectionSet
              = ({
                    data := Execution.ResponseValue.object responseFields,
                    errors := errors
                  }
                  : Execution.Response) := by
  intro hschema parentType variableDefinitions selectionSet sourceRuntimeType
    hvalid hfree hnormal hinclude hpromote
  exact
    executeSelectionSetAsResponse_deepSelectionSetSuccessWithRef_valid_normal_promoted_fuel_ge_size
      schema rootSelectionSet objectRef variableValues hschema
      (SelectionSet.size selectionSet + 1) parentType variableDefinitions
      selectionSet (selectionSetDeepProbeFuel schema parentType selectionSet)
      sourceRuntimeType (by omega) (by omega) hvalid hfree hnormal
      hinclude hpromote

end GroundTypeNormalization

end NormalForm

end GraphQL
