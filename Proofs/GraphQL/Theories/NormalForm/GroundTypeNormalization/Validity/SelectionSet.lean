import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Validity.Support

/-! Selection-set validity preservation for ground-type normalization. -/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

theorem normalizeSelectionSet_normalizedValid_of_typeConditionFeasible
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    : ∀ parentType selectionSet,
      ∀ typeConditions,
        schema.objectType parentType
        -> objectSatisfiesTypeConditionStack schema parentType typeConditions
        -> selectionSetSemanticsReady schema parentType selectionSet
        -> Validation.selectionSetValidInPossibleTypes schema
            variableDefinitions parentType selectionSet
        -> FieldMerge.fieldsInSetCanMerge schema parentType selectionSet
        -> selectionSetDirectiveFree selectionSet
        -> selectionSetTypeConditionFeasible schema parentType typeConditions
            .allFields selectionSet
        -> NormalizedSelectionSetValid schema variableDefinitions parentType
            (normalizeSelectionSet schema parentType selectionSet) := by
  intro parentType selectionSet
  induction parentType, selectionSet using normalizeSelectionSet.induct schema with
  | case1 parentType =>
      intro _typeConditions _hobject _hstack _hready _himplementation
        _hmerge _hfree _hfeasible
      simpa [normalizeSelectionSet] using
        normalizedSelectionSetValid_nil schema variableDefinitions parentType
  | case2 parentType rest responseName fieldName arguments directives
      subselections hlookup hrest =>
      intro typeConditions hobject hstack hready himplementation hmerge hfree
        hfeasible
      have htailImplementation :
          Validation.selectionSetValidInPossibleTypes schema
            variableDefinitions parentType rest :=
        selectionSetValidInPossibleTypes_tail himplementation
      have htailReady :
          selectionSetSemanticsReady schema parentType rest :=
        selectionSetSemanticsReady_tail hready
      have htailMerge :
          FieldMerge.fieldsInSetCanMerge schema parentType rest :=
        fieldsInSetCanMerge_tail schema parentType
          (Selection.field responseName fieldName arguments directives
            subselections)
          rest hmerge
      have hrestFree :
          selectionSetDirectiveFree rest :=
        selectionSetDirectiveFree_tail hfree
      have hfilteredReady :
          selectionSetSemanticsReady schema parentType
            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        selectionSetSemanticsReady_withoutFieldSelectionsWithResponseName schema
          responseName parentType rest htailReady
      have hfilteredImplementation :
          Validation.selectionSetValidInPossibleTypes schema
            variableDefinitions parentType
            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        selectionSetValidInPossibleTypes_withoutFieldSelectionsWithResponseName
          schema responseName variableDefinitions parentType rest
          htailImplementation
      have hfilteredMerge :
          FieldMerge.fieldsInSetCanMerge schema parentType
            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        fieldsInSetCanMerge_withoutFieldSelectionsWithResponseName schema
          responseName parentType rest htailMerge
      have hfilteredFree :
          selectionSetDirectiveFree
            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        withoutFieldSelectionsWithResponseName_directiveFree schema responseName rest
          hrestFree
      have hfilteredFeasible :
          selectionSetTypeConditionFeasible schema parentType typeConditions
            .allFields
            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        selectionSetTypeConditionFeasible_withoutFieldSelectionsWithResponseName
          schema responseName parentType typeConditions rest
          (selectionSetTypeConditionFeasible_tail hfeasible)
      simpa [normalizeSelectionSet, hlookup] using
        hrest typeConditions hobject hstack hfilteredReady
          hfilteredImplementation hfilteredMerge hfilteredFree hfilteredFeasible
  | case3 parentType rest responseName fieldName arguments directives
      subselections fieldDefinition hlookup matching mergedSubselections
      returnType hrest hmerged hpossible =>
      intro typeConditions hobject hstack hready himplementation hmerge hfree
        hfeasible
      let normalizedSubselections :=
        if objectTypeNameBool schema returnType then
          normalizeSelectionSet schema returnType mergedSubselections
        else
          possibleTypeNormalizations schema
            (schema.getPossibleTypes returnType) mergedSubselections
      have hselectionFree :=
        selectionSetDirectiveFree_head hfree
      have hrestFree :
          selectionSetDirectiveFree rest :=
        selectionSetDirectiveFree_tail hfree
      have hdirectives : directives = [] := hselectionFree.1
      subst directives
      have hsubselectionsFree : selectionSetDirectiveFree subselections :=
        hselectionFree.2
      have htailReady :
          selectionSetSemanticsReady schema parentType rest :=
        selectionSetSemanticsReady_tail hready
      have htailImplementation :
          Validation.selectionSetValidInPossibleTypes schema
            variableDefinitions parentType rest :=
        selectionSetValidInPossibleTypes_tail himplementation
      have htailMerge :
          FieldMerge.fieldsInSetCanMerge schema parentType rest :=
        fieldsInSetCanMerge_tail schema parentType
          (Selection.field responseName fieldName arguments []
            subselections)
          rest hmerge
      have hfilteredReady :
          selectionSetSemanticsReady schema parentType
            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        selectionSetSemanticsReady_withoutFieldSelectionsWithResponseName schema
          responseName parentType rest htailReady
      have hfilteredImplementation :
          Validation.selectionSetValidInPossibleTypes schema
            variableDefinitions parentType
            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        selectionSetValidInPossibleTypes_withoutFieldSelectionsWithResponseName
          schema responseName variableDefinitions parentType rest
          htailImplementation
      have hfilteredMerge :
          FieldMerge.fieldsInSetCanMerge schema parentType
            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        fieldsInSetCanMerge_withoutFieldSelectionsWithResponseName schema
          responseName parentType rest htailMerge
      have hfilteredFree :
          selectionSetDirectiveFree
            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        withoutFieldSelectionsWithResponseName_directiveFree schema responseName rest
          hrestFree
      have htailFeasible :
          selectionSetTypeConditionFeasible schema parentType typeConditions
            .allFields rest :=
        selectionSetTypeConditionFeasible_tail hfeasible
      have hfilteredFeasible :
          selectionSetTypeConditionFeasible schema parentType typeConditions
            .allFields
            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        selectionSetTypeConditionFeasible_withoutFieldSelectionsWithResponseName
          schema responseName parentType typeConditions rest htailFeasible
      have hnormalizedRest :
          NormalizedSelectionSetValid schema variableDefinitions parentType
            (normalizeSelectionSet schema parentType
              (withoutFieldSelectionsWithResponseName schema responseName rest)) :=
        hrest typeConditions hobject hstack hfilteredReady
          hfilteredImplementation hfilteredMerge hfilteredFree hfilteredFeasible
      have hlookupValid :
          selectionSetLookupValid schema parentType
            (Selection.field responseName fieldName arguments []
              subselections :: rest) :=
        selectionSetLookupValid_of_selectionSetSemanticsReady
          (Selection.field responseName fieldName arguments []
            subselections :: rest)
          hready
      have hmatchingFree :
          selectionSetDirectiveFree matching := by
        subst matching
        exact fieldSelectionsWithResponseNameInScope_directiveFree schema parentType
          responseName rest hrestFree
      have hmergedFree :
          selectionSetDirectiveFree mergedSubselections := by
        subst mergedSubselections
        exact selectionSetDirectiveFree_append hsubselectionsFree
          (selectionSetDirectiveFree_mergeSelectionSets hmatchingFree)
      have hheadFeasible :
          selectionTypeConditionFeasible schema parentType typeConditions
            .allFields
            (Selection.field responseName fieldName arguments []
              subselections) := by
        simpa [selectionSetTypeConditionFeasible] using hfeasible.1
      have hmergedFeasible :
          ∀ objectType,
            objectType ∈ schema.getPossibleTypes returnType ->
              selectionSetTypeConditionFeasible schema objectType [objectType]
                .allFields mergedSubselections := by
        intro objectType hobjectType
        have hheadChildFeasible :
            selectionSetTypeConditionFeasible schema objectType [objectType]
              .allFields subselections :=
          selectionTypeConditionFeasible_field_child_branch_forObject
            schema hheadFeasible hstack hlookup
            (by simpa [returnType] using hobjectType)
        have hmatchingChildFeasible :
            selectionSetTypeConditionFeasible schema objectType [objectType]
              .allFields (mergeSelectionSets matching) := by
          subst matching
          apply
            selectionSetTypeConditionFeasible_mergeSelectionSets_fieldSelectionsWithResponseNameInScope
          intro matchedFieldName matchedArguments matchedDirectives
            matchedSubselections hmatched
          have hsame :
              matchedFieldName = fieldName :=
            fieldSelectionsWithResponseNameInScope_matching_same_field_of_canMerge_object_lookupValid
              schema parentType responseName fieldName arguments subselections
              rest hobject hlookupValid hmerge matchedFieldName
              matchedArguments matchedDirectives matchedSubselections hmatched
          subst matchedFieldName
          exact
            fieldSelectionsWithResponseNameInScope_field_child_branch_forObject
              schema parentType responseName hobject hstack rest
              htailFeasible fieldName matchedArguments matchedDirectives
              matchedSubselections fieldDefinition objectType hmatched hlookup
              (by simpa [returnType] using hobjectType)
        subst mergedSubselections
        exact selectionSetTypeConditionFeasible_append hheadChildFeasible
          hmatchingChildFeasible
      have hnormalizedSubselectionsValid :
          NormalizedSelectionSetValid schema variableDefinitions returnType
            normalizedSubselections := by
        subst normalizedSubselections
        by_cases hreturnObject : objectTypeNameBool schema returnType = true
        · have hreturnObjectType :
              schema.objectType returnType :=
            objectType_of_objectTypeNameBool_eq_true schema hreturnObject
          have hinclude :
              schema.typeIncludesObjectBool
                fieldDefinition.outputType.namedType returnType = true := by
            simpa [returnType] using
              object_typeIncludesObjectBool_self schema hreturnObjectType
          have hchildReady :
              selectionSetSemanticsReady schema returnType
                mergedSubselections :=
            selectionSetSemanticsReady_fieldHead_merged_of_child_object
              schema parentType responseName fieldName returnType arguments
              subselections rest fieldDefinition hobject hready hlookupValid
              hmerge hlookup (by simpa [returnType] using hinclude)
          have hchildImplementation :
              Validation.selectionSetValidInPossibleTypes schema
                variableDefinitions returnType mergedSubselections :=
            selectionSetValidInPossibleTypes_fieldHead_merged_of_child_object
              schema variableDefinitions parentType responseName fieldName
              returnType arguments subselections rest fieldDefinition hobject
              hlookupValid himplementation hmerge hlookup
              (by simpa [returnType] using hinclude)
          have hchildMerge :
              FieldMerge.fieldsInSetCanMerge schema returnType
                mergedSubselections :=
            fieldsInSetCanMerge_fieldHead_merged_of_canMerge_object_lookupValid
              schema parentType responseName fieldName returnType arguments
              subselections rest fieldDefinition hobject hlookupValid hmerge
              hlookup
          simpa [hreturnObject] using
            hmerged [returnType] hreturnObjectType
              (objectSatisfiesTypeConditionStack_singleton_of_object_forValidity
                schema hreturnObjectType)
              hchildReady hchildImplementation
              hchildMerge hmergedFree
              (hmergedFeasible returnType
                (by
                  simpa [returnType] using
                    (List.contains_iff_mem.mp
                      (object_typeIncludesObjectBool_self schema
                        hreturnObjectType))))
        · have hreturnObjectFalse :
              objectTypeNameBool schema returnType = false := by
            cases hmatch : objectTypeNameBool schema returnType
            · rfl
            · contradiction
          simp [hreturnObjectFalse]
          apply possibleTypeNormalizations_normalizedValid schema
            variableDefinitions returnType
            (schema.getPossibleTypes returnType) mergedSubselections
          · intro objectType hobjectType
            exact
              SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
                hschema returnType objectType hobjectType
          · intro objectType hobjectType
            exact hobjectType
          · intro objectType hobjectType
            have hobjectBranch :
                schema.objectType objectType :=
              SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
                hschema returnType objectType hobjectType
            have hinclude :
                schema.typeIncludesObjectBool
                  fieldDefinition.outputType.namedType objectType = true :=
              List.contains_iff_mem.mpr (by simpa [returnType] using hobjectType)
            have hchildReady :
                selectionSetSemanticsReady schema objectType
                  mergedSubselections :=
              selectionSetSemanticsReady_fieldHead_merged_of_child_object
                schema parentType responseName fieldName objectType arguments
                subselections rest fieldDefinition hobject hready hlookupValid
                hmerge hlookup (by simpa [returnType] using hinclude)
            have hchildImplementation :
                Validation.selectionSetValidInPossibleTypes schema
                  variableDefinitions objectType mergedSubselections :=
              selectionSetValidInPossibleTypes_fieldHead_merged_of_child_object
                schema variableDefinitions parentType responseName fieldName
                objectType arguments subselections rest fieldDefinition hobject
                hlookupValid himplementation hmerge hlookup
                (by simpa [returnType] using hinclude)
            have hchildMerge :
                FieldMerge.fieldsInSetCanMerge schema objectType
                  mergedSubselections :=
              fieldsInSetCanMerge_fieldHead_merged_of_canMerge_object_lookupValid
                schema parentType responseName fieldName objectType arguments
                subselections rest fieldDefinition hobject hlookupValid hmerge
                hlookup
            exact hpossible objectType [objectType] hobjectBranch
              (objectSatisfiesTypeConditionStack_singleton_of_object_forValidity
                schema hobjectBranch)
              hchildReady
              hchildImplementation hchildMerge hmergedFree
              (hmergedFeasible objectType hobjectType)
          · have hreturnLookup :
                selectionSetLookupValid schema returnType
                  mergedSubselections := by
              subst mergedSubselections
              simpa [returnType] using
                selectionSetLookupValid_fieldHead_merged_of_returnType
                  schema variableDefinitions parentType responseName fieldName
                  arguments subselections rest fieldDefinition hobject
                  hlookupValid himplementation hmerge hlookup
            have hreadyBranches :
                ∀ objectType,
                  objectType ∈ schema.getPossibleTypes returnType ->
                    selectionSetSemanticsReady schema objectType
                      mergedSubselections := by
              intro objectType hobjectType
              have hinclude :
                  schema.typeIncludesObjectBool
                    fieldDefinition.outputType.namedType objectType = true :=
                List.contains_iff_mem.mpr
                  (by simpa [returnType] using hobjectType)
              exact
                selectionSetSemanticsReady_fieldHead_merged_of_child_object
                  schema parentType responseName fieldName objectType arguments
                  subselections rest fieldDefinition hobject hready
                  hlookupValid hmerge hlookup
                  (by simpa [returnType] using hinclude)
            have hmergeReturn :
                FieldMerge.fieldsInSetCanMerge schema returnType
                  mergedSubselections := by
              subst mergedSubselections
              exact
                fieldsInSetCanMerge_fieldHead_merged_of_canMerge_object_lookupValid
                  schema parentType responseName fieldName returnType arguments
                  subselections rest fieldDefinition hobject hlookupValid hmerge
                  hlookup
            exact
              normalizedDistinctBranchesPairwiseMerge_of_abstractMerge
                schema variableDefinitions hschema returnType
                (schema.getPossibleTypes returnType) mergedSubselections
                (by
                  intro objectType hobjectType
                  exact
                    SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
                      hschema returnType objectType hobjectType)
                (by
                  intro objectType hobjectType
                  exact hobjectType)
                hreturnLookup hreadyBranches hmergeReturn
      have hnilIfLeaf :
          leafTypeNameBool schema fieldDefinition.outputType.namedType = true ->
            normalizedSubselections = [] := by
        intro hleaf
        subst normalizedSubselections
        have hobjectFalse :
            objectTypeNameBool schema returnType = false :=
          objectTypeNameBool_eq_false_of_isLeafType schema
            (by
              have hleafType :=
                leafTypeNameBool_eq_true_isLeafType schema
                  (by simpa [returnType] using hleaf)
              simpa [returnType] using hleafType)
        have hpossibleNil :
            schema.getPossibleTypes returnType = [] :=
          possibleTypes_eq_nil_of_leafTypeNameBool schema
            (by simpa [returnType] using hleaf)
        simp [hobjectFalse, hpossibleNil, possibleTypeNormalizations]
      have hnormalizedSubselectionsPossible :
          ∀ objectType,
            objectType ∈ schema.getPossibleTypes
                fieldDefinition.outputType.namedType ->
              Validation.selectionSetValidInPossibleTypes schema
                variableDefinitions objectType normalizedSubselections := by
        intro objectType hobjectType
        subst normalizedSubselections
        by_cases hreturnObject : objectTypeNameBool schema returnType = true
        · have hreturnObjectType :
              schema.objectType returnType :=
            objectType_of_objectTypeNameBool_eq_true schema hreturnObject
          have hobjectEq : objectType = returnType :=
            object_typeIncludesObjectBool_eq_self schema hreturnObjectType
              (List.contains_iff_mem.mpr (by simpa [returnType] using hobjectType))
          subst objectType
          simpa [hreturnObject] using
            hnormalizedSubselectionsValid.validInPossibleTypes
        · have hreturnObjectFalse :
              objectTypeNameBool schema returnType = false := by
            cases hmatch : objectTypeNameBool schema returnType
            · rfl
            · contradiction
          simp [hreturnObjectFalse]
          apply possibleTypeNormalizations_validInPossibleTypes
            (parentType := objectType)
          · intro branchType hbranchType
            exact
              SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
                hschema returnType branchType hbranchType
          · intro branchType hbranchType
            have hbranchObject :
                schema.objectType branchType :=
              SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
                hschema returnType branchType hbranchType
            have hinclude :
                schema.typeIncludesObjectBool
                  fieldDefinition.outputType.namedType branchType = true :=
              List.contains_iff_mem.mpr (by simpa [returnType] using hbranchType)
            have hchildReady :
                selectionSetSemanticsReady schema branchType
                  mergedSubselections :=
              selectionSetSemanticsReady_fieldHead_merged_of_child_object
                schema parentType responseName fieldName branchType arguments
                subselections rest fieldDefinition hobject hready hlookupValid
                hmerge hlookup (by simpa [returnType] using hinclude)
            have hchildImplementation :
                Validation.selectionSetValidInPossibleTypes schema
                  variableDefinitions branchType mergedSubselections :=
              selectionSetValidInPossibleTypes_fieldHead_merged_of_child_object
                schema variableDefinitions parentType responseName fieldName
                branchType arguments subselections rest fieldDefinition hobject
                hlookupValid himplementation hmerge hlookup
                (by simpa [returnType] using hinclude)
            have hchildMerge :
                FieldMerge.fieldsInSetCanMerge schema branchType
                  mergedSubselections :=
              fieldsInSetCanMerge_fieldHead_merged_of_canMerge_object_lookupValid
                schema parentType responseName fieldName branchType arguments
                subselections rest fieldDefinition hobject hlookupValid hmerge
                hlookup
            exact hpossible branchType [branchType] hbranchObject
              (objectSatisfiesTypeConditionStack_singleton_of_object_forValidity
                schema hbranchObject)
              hchildReady
              hchildImplementation hchildMerge hmergedFree
              (hmergedFeasible branchType hbranchType)
      have hsubselectionsNonemptyOfComposite :
          schema.isCompositeType fieldDefinition.outputType.namedType ->
            subselections ≠ [] := by
        intro hcomposite
        have hsourceImplementation :
            Validation.selectionValidInPossibleTypes schema variableDefinitions
              parentType
              (Selection.field responseName fieldName arguments []
                subselections) :=
          selectionSetValidInPossibleTypes_head himplementation
        have hsourceSelection :
            Validation.selectionValid schema variableDefinitions parentType
              (Selection.field responseName fieldName arguments []
                subselections) := by
          simpa [Validation.selectionValidInPossibleTypes, hlookup] using
            hsourceImplementation.1
        rcases Validation.selectionValid_field_lookup hsourceSelection with
          ⟨sourceDefinition, hsourceLookup, _harguments, hsourceChild⟩
        have hdefinitionEq : sourceDefinition = fieldDefinition := by
          rw [hlookup] at hsourceLookup
          cases hsourceLookup
          rfl
        subst sourceDefinition
        have hsubselectionsNonempty : subselections ≠ [] := by
          simp [Validation.fieldSelectionSetValid] at hsourceChild
          rcases hsourceChild.2 with hleaf | hcompositeChild
          · exact False.elim
              (isLeafType_not_isCompositeType hleaf.1 hcomposite)
          · exact hcompositeChild.2.1
        exact hsubselectionsNonempty
      have hmergedNonemptyOfComposite :
          schema.isCompositeType fieldDefinition.outputType.namedType ->
            mergedSubselections ≠ [] := by
        intro hcomposite hnil
        have hsubselectionsNonempty :
            subselections ≠ [] :=
          hsubselectionsNonemptyOfComposite hcomposite
        subst mergedSubselections
        cases subselections with
        | nil =>
            exact hsubselectionsNonempty rfl
        | cons selection rest =>
            simp at hnil
      have hnormalizedSubselectionsNonempty :
          schema.isCompositeType fieldDefinition.outputType.namedType ->
            normalizedSubselections ≠ [] := by
        intro hcomposite
        have hmergedNonempty :
            mergedSubselections ≠ [] :=
          hmergedNonemptyOfComposite hcomposite
        have hsubselectionsNonempty :
            subselections ≠ [] :=
          hsubselectionsNonemptyOfComposite hcomposite
        have hheadChildContains :
            selectionSetContainsTypeConditionFeasibleField schema [returnType]
              subselections :=
          by
            simpa [returnType] using
              selectionTypeConditionFeasible_field_child_contains_forObject
                schema hheadFeasible hstack hlookup
                hsubselectionsNonempty
        have hmergedContains :
            selectionSetContainsTypeConditionFeasibleField schema [returnType]
              mergedSubselections := by
          subst mergedSubselections
          exact
            selectionSetContainsTypeConditionFeasibleField_append_left_forValidity
              schema [returnType] hheadChildContains
        subst normalizedSubselections
        by_cases hreturnObject : objectTypeNameBool schema returnType = true
        · have hreturnObjectType :
              schema.objectType returnType :=
            objectType_of_objectTypeNameBool_eq_true schema hreturnObject
          have hinclude :
              schema.typeIncludesObjectBool
                fieldDefinition.outputType.namedType returnType = true := by
            simpa [returnType] using
              object_typeIncludesObjectBool_self schema hreturnObjectType
          have hchildReady :
              selectionSetSemanticsReady schema returnType
                mergedSubselections :=
            selectionSetSemanticsReady_fieldHead_merged_of_child_object
              schema parentType responseName fieldName returnType arguments
              subselections rest fieldDefinition hobject hready hlookupValid
              hmerge hlookup (by simpa [returnType] using hinclude)
          simpa [hreturnObject] using
            normalizeSelectionSet_ne_nil_of_contains schema
              returnType mergedSubselections hreturnObjectType hchildReady
              hmergedContains
        · have hreturnObjectFalse :
              objectTypeNameBool schema returnType = false := by
            cases hmatch : objectTypeNameBool schema returnType
            · rfl
            · contradiction
          simp [hreturnObjectFalse]
          rcases
            selectionSetContainsTypeConditionFeasibleField_replace_base_with_object
              schema hschema returnType [] mergedSubselections
              (by simpa using hmergedContains) with
            ⟨objectType, hobjectType, hbranchObject, hbranchContains⟩
          have hinclude :
              schema.typeIncludesObjectBool
                fieldDefinition.outputType.namedType objectType = true :=
            List.contains_iff_mem.mpr
              (by simpa [returnType] using hobjectType)
          have hchildReady :
              selectionSetSemanticsReady schema objectType
                mergedSubselections :=
            selectionSetSemanticsReady_fieldHead_merged_of_child_object
              schema parentType responseName fieldName objectType arguments
              subselections rest fieldDefinition hobject hready hlookupValid
              hmerge hlookup (by simpa [returnType] using hinclude)
          exact
            possibleTypeNormalizations_ne_nil_of_branch_forValidity schema
              (by simpa [returnType] using hobjectType)
              (normalizeSelectionSet_ne_nil_of_contains schema
                objectType mergedSubselections hbranchObject hchildReady
                (by simpa using hbranchContains))
      have hconsNormalizedValid
          (hnonempty :
            schema.isCompositeType fieldDefinition.outputType.namedType ->
              normalizedSubselections ≠ []) :
          NormalizedSelectionSetValid schema variableDefinitions parentType
            (Selection.field responseName fieldName arguments []
                normalizedSubselections ::
              normalizeSelectionSet schema parentType
                (withoutFieldSelectionsWithResponseName schema responseName
                  rest)) := by
        have hnormalizedFieldImplementation :
            Validation.selectionValidInPossibleTypes schema variableDefinitions
              parentType
              (Selection.field responseName fieldName arguments []
                normalizedSubselections) :=
          normalizedField_selectionValidInPossibleTypes
            (selectionSetValidInPossibleTypes_head himplementation)
            hlookup hnormalizedSubselectionsValid.selectionSetValid
            hnonempty
            hnormalizedSubselectionsValid.validInPossibleTypes
            hnormalizedSubselectionsPossible
            hnilIfLeaf
        have himplementation :
            Validation.selectionSetValidInPossibleTypes schema
              variableDefinitions parentType
              (Selection.field responseName fieldName arguments []
                  normalizedSubselections ::
                normalizeSelectionSet schema parentType
                  (withoutFieldSelectionsWithResponseName schema responseName
                    rest)) :=
          selectionSetValidInPossibleTypes_cons
            hnormalizedFieldImplementation
            hnormalizedRest.validInPossibleTypes
        have hselectionSetValid :
            Validation.selectionSetValid schema variableDefinitions parentType
              (Selection.field responseName fieldName arguments []
                  normalizedSubselections ::
                normalizeSelectionSet schema parentType
                  (withoutFieldSelectionsWithResponseName schema responseName
                    rest)) :=
          selectionSetValid_of_allFields_validInPossibleTypes schema
            variableDefinitions parentType
            (Selection.field responseName fieldName arguments []
                normalizedSubselections ::
              normalizeSelectionSet schema parentType
                (withoutFieldSelectionsWithResponseName schema responseName
                  rest))
            (by
              intro selection hselection
              simp at hselection
              rcases hselection with hhead | htail
              · subst selection
                simp [Selection.isField]
              · exact normalizeSelectionSet_allFields schema parentType
                  (withoutFieldSelectionsWithResponseName schema responseName
                    rest)
                  selection htail)
            himplementation
        have hrestFreeResponse :
            selectionSetResponseNameFree schema parentType responseName
              (normalizeSelectionSet schema parentType
                (withoutFieldSelectionsWithResponseName schema responseName
                  rest)) :=
          normalizeSelectionSet_responseNameFree schema parentType responseName
            (withoutFieldSelectionsWithResponseName schema responseName rest)
            (withoutFieldSelectionsWithResponseName_responseNameFree schema
              parentType responseName rest)
        have hfieldMergePair :
            FieldMerge.fieldsInSetCanMerge schema parentType
                (Selection.field responseName fieldName arguments []
                    normalizedSubselections ::
                  normalizeSelectionSet schema parentType
                    (withoutFieldSelectionsWithResponseName schema responseName
                      rest))
              ∧ ∀ mergeParent,
                FieldMerge.fieldsInSetCanMerge schema mergeParent
                ((Selection.field responseName fieldName arguments []
                      normalizedSubselections ::
                    normalizeSelectionSet schema parentType
                      (withoutFieldSelectionsWithResponseName schema responseName
                        rest))
                  ++
                  (Selection.field responseName fieldName arguments []
                      normalizedSubselections ::
                    normalizeSelectionSet schema parentType
                      (withoutFieldSelectionsWithResponseName schema responseName
                        rest))) := by
          apply fieldsInSetCanMerge_field_cons_of_rest_responseNameFree
          · exact hschema
          · exact hlookup
          · exact FieldMerge.sameResponseShape_refl schema
              fieldDefinition.outputType
              (SchemaWellFormedness.schemaWellFormed_lookupField_outputType
                hschema hlookup)
          · exact argumentsEquivalent_refl arguments
          · intro objectType
            exact hnormalizedSubselectionsValid.fieldsCanMergeSelf objectType
          · exact hnormalizedRest.fieldsCanMerge
          · exact hnormalizedRest.fieldsCanMergeSelf
          · exact normalizeSelectionSet_allFields schema parentType
              (withoutFieldSelectionsWithResponseName schema responseName rest)
          · exact hrestFreeResponse
        exact ⟨hselectionSetValid, himplementation, hfieldMergePair.1,
          fun mergeParent => hfieldMergePair.2 mergeParent⟩
      have hfinal :
          NormalizedSelectionSetValid schema variableDefinitions parentType
            (normalizedFieldWithRest schema returnType responseName fieldName
              arguments [] normalizedSubselections
              (normalizeSelectionSet schema parentType
                (withoutFieldSelectionsWithResponseName schema responseName
                  rest))) := by
        simpa [normalizedFieldWithRest, normalizedField] using
          hconsNormalizedValid hnormalizedSubselectionsNonempty
      rw [normalizeSelectionSet.eq_2, hlookup]
      change NormalizedSelectionSetValid schema variableDefinitions parentType
        (normalizedFieldWithRest schema returnType responseName fieldName
          arguments [] normalizedSubselections
          (normalizeSelectionSet schema parentType
            (withoutFieldSelectionsWithResponseName schema responseName rest)))
      exact hfinal
  | case4 parentType rest directives subselections happend =>
      intro typeConditions hobject hstack hready himplementation hmerge hfree
        hfeasible
      have hselectionFree :=
        selectionSetDirectiveFree_head hfree
      have hdirectives : directives = [] := hselectionFree.1
      subst directives
      have hrestFree :=
        selectionSetDirectiveFree_tail hfree
      have hbodyReady :
          selectionSetSemanticsReady schema parentType subselections := by
        have hhead :
            selectionSemanticsReady schema parentType
              (Selection.inlineFragment none [] subselections) := by
          unfold selectionSetSemanticsReady at hready
          exact hready _ (by simp)
        simpa [selectionSemanticsReady] using hhead
      have hbodyImplementation :
          Validation.selectionSetValidInPossibleTypes schema
            variableDefinitions parentType subselections := by
        have hhead :=
          selectionSetValidInPossibleTypes_head himplementation
        have hparentPossible :
            parentType ∈ schema.getPossibleTypes parentType :=
          List.contains_iff_mem.mp
            (object_typeIncludesObjectBool_self schema hobject)
        simpa [Validation.selectionValidInPossibleTypes] using hhead
          parentType hparentPossible
      have htailReady :=
        selectionSetSemanticsReady_tail hready
      have htailImplementation :=
        selectionSetValidInPossibleTypes_tail himplementation
      have hbodyTailReady :
          selectionSetSemanticsReady schema parentType
            (subselections ++ rest) :=
        selectionSetSemanticsReady_append hbodyReady htailReady
      have hbodyTailImplementation :
          Validation.selectionSetValidInPossibleTypes schema
            variableDefinitions parentType (subselections ++ rest) :=
        selectionSetValidInPossibleTypes_append hbodyImplementation
          htailImplementation
      have hbodyTailMerge :
          FieldMerge.fieldsInSetCanMerge schema parentType
            (subselections ++ rest) :=
        fieldsInSetCanMerge_inlineFragment_none_flatten schema parentType
          subselections rest hmerge
      have hbodyTailFree :
          selectionSetDirectiveFree (subselections ++ rest) :=
        selectionSetDirectiveFree_append hselectionFree.2 hrestFree
      have hbodyFeasible :
          selectionSetTypeConditionFeasible schema parentType typeConditions
            .allFields subselections := by
        simpa [selectionSetTypeConditionFeasible,
          selectionTypeConditionFeasible] using hfeasible.1
      have htailFeasible :
          selectionSetTypeConditionFeasible schema parentType typeConditions
            .allFields rest :=
        selectionSetTypeConditionFeasible_tail hfeasible
      have hbodyTailFeasible :
          selectionSetTypeConditionFeasible schema parentType typeConditions
            .allFields
            (subselections ++ rest) :=
        selectionSetTypeConditionFeasible_append hbodyFeasible htailFeasible
      simpa [normalizeSelectionSet] using
        happend typeConditions hobject hstack hbodyTailReady
          hbodyTailImplementation hbodyTailMerge hbodyTailFree
          hbodyTailFeasible
  | case5 parentType rest typeCondition directives subselections hoverlap
      _hrest happend =>
      intro typeConditions hobject hstack hready himplementation hmerge hfree
        hfeasible
      have hselectionFree :=
        selectionSetDirectiveFree_head hfree
      have hdirectives : directives = [] := hselectionFree.1
      subst directives
      have hrestFree :=
        selectionSetDirectiveFree_tail hfree
      have hheadReady :
          selectionSemanticsReady schema parentType
            (Selection.inlineFragment (some typeCondition) []
              subselections) := by
        unfold selectionSetSemanticsReady at hready
        exact hready _ (by simp)
      have hbodyReady :
          selectionSetSemanticsReady schema parentType subselections := by
        have hpair :
            selectionSetLookupValid schema typeCondition subselections
              ∧ (schema.typesOverlapBool parentType typeCondition = true ->
                selectionSetSemanticsReady schema parentType subselections) := by
          simpa [selectionSemanticsReady] using hheadReady
        exact hpair.2 hoverlap
      have hheadImplementation :=
        selectionSetValidInPossibleTypes_head himplementation
      have hbodyImplementation :
          Validation.selectionSetValidInPossibleTypes schema
            variableDefinitions parentType subselections := by
        have hfragment :
            ∀ objectType,
              objectType ∈ schema.getPossibleTypes typeCondition ->
                Validation.selectionSetValidInPossibleTypes schema
                  variableDefinitions objectType subselections := by
          simpa [Validation.selectionValidInPossibleTypes] using
            hheadImplementation hoverlap
        have hparentPossible :
            parentType ∈ schema.getPossibleTypes typeCondition :=
          List.contains_iff_mem.mp
            (typeIncludesObjectBool_of_object_typesOverlapBool schema
              hobject hoverlap)
        exact hfragment parentType hparentPossible
      have htailReady :=
        selectionSetSemanticsReady_tail hready
      have htailImplementation :=
        selectionSetValidInPossibleTypes_tail himplementation
      have hbodyTailReady :
          selectionSetSemanticsReady schema parentType
            (subselections ++ rest) :=
        selectionSetSemanticsReady_append hbodyReady htailReady
      have hbodyTailImplementation :
          Validation.selectionSetValidInPossibleTypes schema
            variableDefinitions parentType (subselections ++ rest) :=
        selectionSetValidInPossibleTypes_append hbodyImplementation
          htailImplementation
      have hlookupBodyType :
          selectionSetLookupValid schema typeCondition subselections := by
        have hpair :
            selectionSetLookupValid schema typeCondition subselections
              ∧ (schema.typesOverlapBool parentType typeCondition = true ->
                selectionSetSemanticsReady schema parentType subselections) := by
          simpa [selectionSemanticsReady] using hheadReady
        exact hpair.1
      have hlookupBodyParent :
          selectionSetLookupValid schema parentType subselections :=
        selectionSetLookupValid_of_selectionSetSemanticsReady subselections
          hbodyReady
      have hlookupRest :
          selectionSetLookupValid schema parentType rest :=
        selectionSetLookupValid_of_selectionSetSemanticsReady rest htailReady
      have hbodyTailMerge :
          FieldMerge.fieldsInSetCanMerge schema parentType
            (subselections ++ rest) :=
        fieldsInSetCanMerge_inlineFragment_some_overlap_flatten_object
          schema parentType typeCondition subselections rest hschema hobject
          hoverlap hlookupBodyParent hlookupBodyType hlookupRest hmerge
      have hbodyTailFree :
          selectionSetDirectiveFree (subselections ++ rest) :=
        selectionSetDirectiveFree_append hselectionFree.2 hrestFree
      have hbodyFeasible :
          selectionSetTypeConditionFeasible schema parentType
            (typeCondition :: typeConditions) .allFields subselections := by
        simpa [selectionSetTypeConditionFeasible,
          selectionTypeConditionFeasible] using hfeasible.1
      have htailFeasible :
          selectionSetTypeConditionFeasible schema parentType typeConditions
            .allFields rest :=
        selectionSetTypeConditionFeasible_tail hfeasible
      have htailFeasibleInBodyStack :
          selectionSetTypeConditionFeasible schema parentType
            (typeCondition :: typeConditions) .allFields rest :=
        selectionSetTypeConditionFeasible_of_stack_subset schema
          (fun candidate hcandidate =>
            List.mem_cons_of_mem typeCondition hcandidate)
          rest htailFeasible
      have hbodyTailFeasible :
          selectionSetTypeConditionFeasible schema parentType
            (typeCondition :: typeConditions) .allFields
            (subselections ++ rest) :=
        selectionSetTypeConditionFeasible_append hbodyFeasible
          htailFeasibleInBodyStack
      have hstackBody :
          objectSatisfiesTypeConditionStack schema parentType
            (typeCondition :: typeConditions) :=
        objectSatisfiesTypeConditionStack_cons_of_overlap_forValidity
          schema hobject hstack hoverlap
      simpa [normalizeSelectionSet, hoverlap] using
        happend (typeCondition :: typeConditions) hobject hstackBody
          hbodyTailReady hbodyTailImplementation hbodyTailMerge
          hbodyTailFree hbodyTailFeasible
  | case6 parentType rest typeCondition directives subselections hoverlap
      hrest =>
      intro typeConditions hobject hstack hready himplementation hmerge hfree
        hfeasible
      have htailReady :=
        selectionSetSemanticsReady_tail hready
      have htailImplementation :=
        selectionSetValidInPossibleTypes_tail himplementation
      have htailMerge :
          FieldMerge.fieldsInSetCanMerge schema parentType rest :=
        fieldsInSetCanMerge_tail schema parentType
          (Selection.inlineFragment (some typeCondition) directives
            subselections)
          rest hmerge
      have htailFree :=
        selectionSetDirectiveFree_tail hfree
      have htailFeasible :
          selectionSetTypeConditionFeasible schema parentType typeConditions
            .allFields rest :=
        selectionSetTypeConditionFeasible_tail hfeasible
      have hfalse :
          schema.typesOverlapBool parentType typeCondition = false := by
        cases hmatch : schema.typesOverlapBool parentType typeCondition
        · rfl
        · contradiction
      simpa [normalizeSelectionSet, hfalse] using
        hrest typeConditions hobject hstack htailReady htailImplementation
          htailMerge htailFree htailFeasible

theorem normalizeSelectionSet_normalizedValid
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hfeasibleAll : selectionSetsTypeConditionFeasibleInEveryNormalizerScope schema)
    : ∀ parentType selectionSet,
        schema.objectType parentType
        -> selectionSetSemanticsReady schema parentType selectionSet
        -> Validation.selectionSetValidInPossibleTypes schema
            variableDefinitions parentType selectionSet
        -> FieldMerge.fieldsInSetCanMerge schema parentType selectionSet
        -> selectionSetDirectiveFree selectionSet
        -> NormalizedSelectionSetValid schema variableDefinitions parentType
            (normalizeSelectionSet schema parentType selectionSet) := by
  intro parentType selectionSet hobject hready himplementation hmerge hfree
  have hstack :
      objectSatisfiesTypeConditionStack schema parentType [parentType] :=
    objectSatisfiesTypeConditionStack_singleton_of_object_forValidity
      schema hobject
  have hfeasible :
      selectionSetTypeConditionFeasible schema parentType [parentType]
        .allFields selectionSet := by
    cases selectionSet with
    | nil =>
        simp [selectionSetTypeConditionFeasible]
    | cons selection rest =>
        exact (hfeasibleAll parentType (selection :: rest) (by simp)).2
  exact
    normalizeSelectionSet_normalizedValid_of_typeConditionFeasible schema
      variableDefinitions hschema parentType selectionSet [parentType] hobject
      hstack hready himplementation hmerge hfree hfeasible

mutual
  def selectionInlineFragmentsNonempty : Selection -> Prop
    | .field _responseName _fieldName _arguments _directives selectionSet =>
        selectionSetInlineFragmentsNonempty selectionSet
    | .inlineFragment _typeCondition _directives selectionSet =>
        selectionSet ≠ [] ∧ selectionSetInlineFragmentsNonempty selectionSet

  def selectionSetInlineFragmentsNonempty (selectionSet : List Selection) : Prop :=
    ∀ selection, selection ∈ selectionSet -> selectionInlineFragmentsNonempty selection
end

mutual
  theorem selectionInlineFragmentsNonempty_of_selectionValid
      (schema : Schema) (variableDefinitions : List VariableDefinition)
      : ∀ parentType selection,
          Validation.selectionValid schema variableDefinitions parentType selection
          -> selectionInlineFragmentsNonempty selection
    | parentType,
      .field _responseName _fieldName _arguments _directives selectionSet,
      hvalid => by
        unfold selectionInlineFragmentsNonempty
        rcases Validation.selectionValid_field_lookup hvalid with
          ⟨fieldDefinition, _hlookup, _harguments, hchild⟩
        simp [Validation.fieldSelectionSetValid] at hchild
        rcases hchild.2 with hleaf | hcomposite
        · rw [hleaf.2]
          unfold selectionSetInlineFragmentsNonempty
          intro selection hselection
          cases hselection
        · exact
            selectionSetInlineFragmentsNonempty_of_selectionSetValid
              schema variableDefinitions
              fieldDefinition.outputType.namedType selectionSet
              hcomposite.2.2
    | parentType,
      .inlineFragment none _directives selectionSet, hvalid => by
        unfold selectionInlineFragmentsNonempty
        have hvalid' := hvalid
        simp [Validation.selectionValid] at hvalid'
        exact ⟨hvalid'.2.1,
          selectionSetInlineFragmentsNonempty_of_selectionSetValid
            schema variableDefinitions parentType selectionSet hvalid'.2.2⟩
    | _parentType,
      .inlineFragment (some typeCondition) _directives selectionSet,
      hvalid => by
        unfold selectionInlineFragmentsNonempty
        have hvalid' := hvalid
        simp [Validation.selectionValid] at hvalid'
        exact ⟨hvalid'.2.2.2.1,
          selectionSetInlineFragmentsNonempty_of_selectionSetValid
            schema variableDefinitions typeCondition selectionSet
            hvalid'.2.2.2.2⟩

  theorem selectionSetInlineFragmentsNonempty_of_selectionSetValid
      (schema : Schema) (variableDefinitions : List VariableDefinition)
      : ∀ parentType selectionSet,
          Validation.selectionSetValid schema variableDefinitions parentType selectionSet
          -> selectionSetInlineFragmentsNonempty selectionSet
    | parentType, selectionSet, hvalid => by
        unfold selectionSetInlineFragmentsNonempty
        unfold Validation.selectionSetValid at hvalid
        intro selection hselection
        exact selectionInlineFragmentsNonempty_of_selectionValid schema
          variableDefinitions parentType selection (hvalid selection hselection)
end

end GroundTypeNormalization

end NormalForm

end GraphQL
