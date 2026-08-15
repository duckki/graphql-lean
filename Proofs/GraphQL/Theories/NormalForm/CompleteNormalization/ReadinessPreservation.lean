import Proofs.GraphQL.Theories.ExecutionReadiness
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.BoolCaseWrappers
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.OperationWrappers
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.OperationVariables
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Uniqueness.BoolCases
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Validity.Branches.Filter
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Validity.Variables
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.ReadinessPreservation

/-!
Argument-coercion readiness facts for complete normalization.

Boolean filtering removes only selections that are disabled in the represented
runtime case. Consequently, readiness of the filtered branch reflects to the
source selection set when the runtime Boolean environment agrees with that case.
-/

namespace GraphQL

namespace NormalForm

namespace CompleteNormalization

open GroundTypeNormalization

private theorem selectionSetRemovedResponseReady_of_filteredSource
    (schema : Schema) (variableValues : Execution.VariableValues)
    (variableDefinitions : List VariableDefinition)
    (parentType responseName fieldName : Name) (arguments : List Argument)
    (subselections rest : List Selection) (fieldDefinition : FieldDefinition)
    (typeConditions : List Name)
    (hobject : schema.objectType parentType)
    (hparent : parentType ∈ typeConditions)
    (hlookupValid
      : selectionSetLookupValid schema parentType
          (Selection.field responseName fieldName arguments [] subselections :: rest))
    (hsource
      : selectionSetFilteredCurrentSourceValid schema variableDefinitions parentType
          (Selection.field responseName fieldName arguments [] subselections :: rest))
    (hmerge
      : FieldMerge.fieldsInSetCanMerge schema parentType
          (Selection.field responseName fieldName arguments [] subselections :: rest))
    (hfeasible
      : selectionSetTypeConditionFeasible schema parentType
          typeConditions
          (Selection.field responseName fieldName arguments [] subselections :: rest))
    (hlookup : schema.lookupField parentType fieldName = some fieldDefinition)
    (hheadSuccess
      : (Execution.coerceArgumentValues schema variableValues
          fieldDefinition.arguments arguments).isSuccess
        = true)
    (hmergedReady
      : ∀ runtimeType,
          schema.typeIncludesObjectBool fieldDefinition.outputType.namedType runtimeType
            = true
          -> selectionSetArgumentsCoercible schema variableValues runtimeType
              (subselections
                ++ mergeSelectionSets
                    (fieldSelectionsWithResponseNameInScope
                      schema parentType responseName rest)))
    : GroundTypeNormalization.selectionSetRemovedResponseReady schema variableValues
        parentType responseName rest := by
  apply
    GroundTypeNormalization.selectionSetRemovedResponseReady_of_all_fields schema
      variableValues parentType responseName rest
  intro field hfield
  rcases GroundTypeNormalization.allFieldsWithResponseName_mem_field responseName rest
      field hfield with
    ⟨matchedFieldName, matchedArguments, matchedDirectives, matchedSubselections,
      rfl⟩
  have hscoped :
      Selection.field responseName matchedFieldName matchedArguments
          matchedDirectives matchedSubselections
        ∈ fieldSelectionsWithResponseNameInScope schema
            parentType responseName rest :=
    GroundTypeNormalization.allFieldsWithResponseName_mem_scoped schema responseName
      parentType typeConditions rest _ hobject hparent hfeasible.2 hfield
  have hsameField : matchedFieldName = fieldName :=
    fieldSelectionsWithResponseNameInScope_matching_same_field_of_canMerge_object_lookupValid
      schema parentType responseName fieldName arguments subselections rest hobject
      hlookupValid hmerge matchedFieldName matchedArguments matchedDirectives
      matchedSubselections hscoped
  have hargumentsEquivalent :
      Argument.argumentsEquivalent arguments matchedArguments :=
    GroundTypeNormalization.fieldSelectionsWithResponseNameInScope_matching_argumentsEquivalent
      schema parentType responseName fieldName arguments subselections rest hobject
      hlookupValid hmerge matchedFieldName matchedArguments matchedDirectives
      matchedSubselections hscoped
  have hheadSource := selectionSetFilteredCurrentSourceValid_head hsource
  have hheadNodup : (arguments.map Argument.name).Nodup := by
    rcases hheadSource with
      ⟨_directives, sourceDirectives, sourceChildren, sourceDefinition,
        sourceLookup, sourceValid, _children⟩
    have hdefinition : sourceDefinition = fieldDefinition := by
      rw [hlookup] at sourceLookup
      exact Option.some.inj sourceLookup.symm
    subst sourceDefinition
    have hnodup := Execution.selectionArgumentsNodup_of_selectionValid sourceValid.1
    simpa [Execution.selectionArgumentsNodup] using hnodup.1
  have htailSource := selectionSetFilteredCurrentSourceValid_tail hsource
  have hmatchedSource :=
    fieldSelectionsWithResponseNameInScope_field_filteredCurrentSourceValid
      schema variableDefinitions parentType responseName rest htailSource
      matchedFieldName matchedArguments matchedDirectives matchedSubselections hscoped
  have hmatchedNodup : (matchedArguments.map Argument.name).Nodup := by
    rcases hmatchedSource with
      ⟨_directives, sourceDirectives, sourceChildren, sourceDefinition,
        sourceLookup, sourceValid, _children⟩
    have hdefinition : sourceDefinition = fieldDefinition := by
      rw [hsameField, hlookup] at sourceLookup
      exact Option.some.inj sourceLookup.symm
    subst sourceDefinition
    have hnodup := Execution.selectionArgumentsNodup_of_selectionValid sourceValid.1
    simpa [Execution.selectionArgumentsNodup] using hnodup.1
  subst matchedFieldName
  intro _hdirectives definition hmatchedLookup
  have hdefinition : definition = fieldDefinition := by
    rw [hlookup] at hmatchedLookup
    exact Option.some.inj hmatchedLookup.symm
  subst definition
  constructor
  · exact fieldArgumentCoercionSucceeds_of_equivalent hheadNodup
      hmatchedNodup hargumentsEquivalent hheadSuccess
  · intro runtimeType hinclude
    have hmerged := hmergedReady runtimeType hinclude
    have hmatchingReady :
        selectionSetArgumentsCoercible schema variableValues runtimeType
          (mergeSelectionSets
            (fieldSelectionsWithResponseNameInScope schema
              parentType responseName rest)) :=
      (selectionSetArgumentsCoercible_append schema variableValues runtimeType
        subselections
        (mergeSelectionSets
          (fieldSelectionsWithResponseNameInScope schema
            parentType responseName rest))).1 hmerged |>.2
    exact
      GroundTypeNormalization.selectionSetArgumentsCoercible_mergeSelectionSets_of_mem
        hmatchingReady hscoped rfl

private theorem selectionSet_size_tail_lt_cons_for_completeReadiness
    (selection : Selection) (rest : List Selection)
    : SelectionSet.size rest < SelectionSet.size (selection :: rest) := by
  cases selection <;> simp [SelectionSet.size, Selection.size]
  all_goals omega

private theorem selectionSet_size_child_lt_cons_field_for_completeReadiness
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (children rest : List Selection)
    : SelectionSet.size children
      < SelectionSet.size
          (Selection.field responseName fieldName arguments directives children
            :: rest) := by
  simp [SelectionSet.size, Selection.size]
  omega

private theorem selectionSet_size_child_lt_cons_inline_for_completeReadiness
    (typeCondition : Option Name) (directives : List DirectiveApplication)
    (children rest : List Selection)
    : SelectionSet.size children
      < SelectionSet.size
          (Selection.inlineFragment typeCondition directives children :: rest) := by
  simp [SelectionSet.size, Selection.size]
  omega

theorem selectionSetArgumentsCoercible_of_normalizeFilteredSelectionSet
    (schema : Schema) (variableValues : Execution.VariableValues)
    (variableDefinitions : List VariableDefinition)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    : ∀ parentType selectionSet,
      ∀ typeConditions,
        schema.objectType parentType
        -> parentType ∈ typeConditions
        -> objectSatisfiesTypeConditionStack schema parentType typeConditions
        -> selectionSetSemanticsReady schema parentType selectionSet
        -> selectionSetFilteredCurrentSourceValid schema variableDefinitions
            parentType selectionSet
        -> FieldMerge.fieldsInSetCanMerge schema parentType selectionSet
        -> selectionSetDirectiveFree selectionSet
        -> selectionSetTypeConditionFeasible schema parentType typeConditions selectionSet
        -> selectionSetArgumentsCoercible schema variableValues parentType
            (normalizeSelectionSet schema parentType selectionSet)
        -> selectionSetArgumentsCoercible schema variableValues parentType
            selectionSet := by
  intro parentType selectionSet
  induction parentType, selectionSet using normalizeSelectionSet.induct schema with
  | case1 parentType =>
      intro _typeConditions _hobject _hparent _hstack _hready _hsource
        _hmerge _hfree _hfeasible _hnormalized
      simp [selectionSetArgumentsCoercible]
  | case2 parentType rest responseName fieldName arguments directives
      subselections hlookup _hrest =>
      intro _typeConditions _hobject _hparent _hstack hready _hsource
        _hmerge _hfree _hfeasible _hnormalized
      have hlookupValid :
          selectionSetLookupValid schema parentType
            (Selection.field responseName fieldName arguments directives
              subselections :: rest) :=
        selectionSetLookupValid_of_selectionSetSemanticsReady
          (Selection.field responseName fieldName arguments directives
            subselections :: rest) hready
      exact False.elim
        (selectionSetLookupValid_field_head_lookup_none_false hlookupValid hlookup)
  | case3 parentType rest responseName fieldName arguments directives
      subselections fieldDefinition hlookup matching mergedSubselections
      returnType hrest hmerged hpossible =>
      intro typeConditions hobject hparent hstack hready hsource hmerge
        hfree hfeasible hnormalized
      let normalizedSubselections :=
        if objectTypeNameBool schema returnType then
          normalizeSelectionSet schema returnType mergedSubselections
        else
          possibleTypeNormalizations schema
            (schema.getPossibleTypes returnType) mergedSubselections
      have hselectionFree := selectionSetDirectiveFree_head hfree
      have hdirectives : directives = [] := hselectionFree.1
      subst directives
      have hsubselectionsFree : selectionSetDirectiveFree subselections :=
        hselectionFree.2
      have hrestFree := selectionSetDirectiveFree_tail hfree
      have htailReady := selectionSetSemanticsReady_tail hready
      have htailSource := selectionSetFilteredCurrentSourceValid_tail hsource
      have htailMerge :=
        fieldsInSetCanMerge_tail schema parentType
          (Selection.field responseName fieldName arguments [] subselections) rest
          hmerge
      have htailFeasible := selectionSetTypeConditionFeasible_tail hfeasible
      have hfilteredReady :=
        selectionSetSemanticsReady_withoutFieldSelectionsWithResponseName schema
          responseName parentType rest htailReady
      have hfilteredSource :=
        selectionSetFilteredCurrentSourceValid_withoutFieldSelectionsWithResponseName
          schema responseName parentType variableDefinitions rest htailSource
      have hfilteredMerge :=
        fieldsInSetCanMerge_withoutFieldSelectionsWithResponseName schema responseName
          parentType rest htailMerge
      have hfilteredFree :=
        withoutFieldSelectionsWithResponseName_directiveFree schema responseName rest
          hrestFree
      have hfilteredFeasible :=
        selectionSetTypeConditionFeasible_withoutFieldSelectionsWithResponseName
          schema responseName parentType typeConditions rest htailFeasible
      have hlookupValid :
          selectionSetLookupValid schema parentType
            (Selection.field responseName fieldName arguments [] subselections :: rest) :=
        selectionSetLookupValid_of_selectionSetSemanticsReady
          (Selection.field responseName fieldName arguments [] subselections :: rest)
          hready
      have hmatchingFree : selectionSetDirectiveFree matching := by
        subst matching
        exact fieldSelectionsWithResponseNameInScope_directiveFree schema parentType
          responseName rest hrestFree
      have hmergedFree : selectionSetDirectiveFree mergedSubselections := by
        subst mergedSubselections
        exact selectionSetDirectiveFree_append hsubselectionsFree
          (selectionSetDirectiveFree_mergeSelectionSets hmatchingFree)
      have hheadFeasible :
          selectionTypeConditionFeasible schema parentType typeConditions
            (Selection.field responseName fieldName arguments [] subselections) := by
        simpa [selectionSetTypeConditionFeasible] using hfeasible.1
      have hmergedFeasible : ∀ objectType,
          objectType ∈ schema.getPossibleTypes returnType
          -> selectionSetTypeConditionFeasible schema objectType [objectType]
              mergedSubselections := by
        intro objectType hobjectType
        have hheadChildFeasible :=
          selectionTypeConditionFeasible_field_child_branch_forObject schema
            hheadFeasible hstack hlookup (by simpa [returnType] using hobjectType)
        have hmatchingChildFeasible :
            selectionSetTypeConditionFeasible schema objectType [objectType]
              (mergeSelectionSets matching) := by
          subst matching
          apply
            selectionSetTypeConditionFeasible_mergeSelectionSets_fieldSelectionsWithResponseNameInScope
          intro matchedFieldName matchedArguments matchedDirectives
            matchedSubselections hmatched
          have hsame :=
            fieldSelectionsWithResponseNameInScope_matching_same_field_of_canMerge_object_lookupValid
              schema parentType responseName fieldName arguments subselections rest
              hobject hlookupValid hmerge matchedFieldName matchedArguments
              matchedDirectives matchedSubselections hmatched
          subst matchedFieldName
          exact fieldSelectionsWithResponseNameInScope_field_child_branch_forObject
            schema parentType responseName hobject hstack rest htailFeasible fieldName
            matchedArguments matchedDirectives matchedSubselections fieldDefinition
            objectType hmatched hlookup (by simpa [returnType] using hobjectType)
        subst mergedSubselections
        exact selectionSetTypeConditionFeasible_append hheadChildFeasible
          hmatchingChildFeasible
      have hmergedSource : ∀ objectType,
          objectType ∈ schema.getPossibleTypes returnType
          -> selectionSetFilteredCurrentSourceValid schema variableDefinitions
              objectType mergedSubselections := by
        intro objectType hobjectType
        exact selectionSetFilteredCurrentSourceValid_fieldHead_merged_of_child_object
          schema variableDefinitions parentType responseName fieldName objectType
          arguments subselections rest fieldDefinition hobject hlookupValid hsource
          hmerge hlookup (by simpa [returnType] using hobjectType)
      have hmergedSemanticReady : ∀ objectType,
          objectType ∈ schema.getPossibleTypes returnType
          -> selectionSetSemanticsReady schema objectType mergedSubselections := by
        intro objectType hobjectType
        exact selectionSetSemanticsReady_fieldHead_merged_of_child_object schema
          parentType responseName fieldName objectType arguments subselections rest
          fieldDefinition hobject hready hlookupValid hmerge hlookup
          (List.contains_iff_mem.mpr (by simpa [returnType] using hobjectType))
      have hmergedMerge : ∀ objectType,
          objectType ∈ schema.getPossibleTypes returnType
          -> FieldMerge.fieldsInSetCanMerge schema objectType mergedSubselections := by
        intro objectType _hobjectType
        exact fieldsInSetCanMerge_fieldHead_merged_of_canMerge_object_lookupValid
          schema parentType responseName fieldName objectType arguments subselections
          rest fieldDefinition hobject hlookupValid hmerge hlookup
      rw [normalizeSelectionSet.eq_2, hlookup] at hnormalized
      change selectionSetArgumentsCoercible schema variableValues parentType
        (Selection.field responseName fieldName arguments [] normalizedSubselections
          :: normalizeSelectionSet schema parentType
            (withoutFieldSelectionsWithResponseName schema responseName rest)) at hnormalized
      rcases hnormalized with ⟨hnormalizedHead, hnormalizedRest⟩
      have hnormalizedField :=
        hnormalizedHead (by simp [Execution.selectionDirectivesAllowBool])
          fieldDefinition hlookup
      have hfilteredCoercible :=
        hrest typeConditions hobject hparent hstack hfilteredReady
          hfilteredSource hfilteredMerge hfilteredFree hfilteredFeasible
          hnormalizedRest
      have hmergedCoercible : ∀ runtimeType,
          schema.typeIncludesObjectBool returnType runtimeType = true
          -> selectionSetArgumentsCoercible schema variableValues runtimeType
              mergedSubselections := by
        intro runtimeType hinclude
        have hruntimeMem : runtimeType ∈ schema.getPossibleTypes returnType :=
          List.contains_iff_mem.mp hinclude
        have hruntimeObject : schema.objectType runtimeType :=
          SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects hschema
            returnType runtimeType hruntimeMem
        have hruntimeStack :
            objectSatisfiesTypeConditionStack schema runtimeType [runtimeType] :=
          objectSatisfiesTypeConditionStack_singleton_of_object_forValidity schema
            hruntimeObject
        by_cases hreturnObject : objectTypeNameBool schema returnType = true
        · have hreturnObjectType : schema.objectType returnType :=
            objectType_of_objectTypeNameBool_eq_true schema hreturnObject
          have hruntimeEq : runtimeType = returnType :=
            object_typeIncludesObjectBool_eq_self schema hreturnObjectType hinclude
          subst runtimeType
          have hnormalizedChild :
              selectionSetArgumentsCoercible schema variableValues returnType
                (normalizeSelectionSet schema returnType mergedSubselections) := by
            simpa [normalizedSubselections, hreturnObject] using
              hnormalizedField.2 returnType hinclude
          exact hmerged [returnType] hreturnObjectType (by simp)
            hruntimeStack (hmergedSemanticReady returnType hruntimeMem)
            (hmergedSource returnType hruntimeMem)
            (hmergedMerge returnType hruntimeMem) hmergedFree
            (hmergedFeasible returnType hruntimeMem) hnormalizedChild
        · have hreturnObjectFalse : objectTypeNameBool schema returnType = false := by
            cases hmatch : objectTypeNameBool schema returnType
            · rfl
            · contradiction
          by_cases hcontains :
              selectionSetContainsTypeConditionFeasibleField schema [runtimeType]
                mergedSubselections
          · have hnormalizedChildNonempty :
                normalizeSelectionSet schema runtimeType mergedSubselections ≠ [] :=
              normalizeSelectionSet_ne_nil_of_contains schema runtimeType
                mergedSubselections hruntimeObject
                (hmergedSemanticReady runtimeType hruntimeMem) hcontains
            have hbranchesReady :
                selectionSetArgumentsCoercible schema variableValues runtimeType
                  (possibleTypeNormalizations schema
                    (schema.getPossibleTypes returnType) mergedSubselections) := by
              simpa [normalizedSubselections, hreturnObjectFalse] using
                hnormalizedField.2 runtimeType hinclude
            have hnormalizedChild :=
              selectionSetArgumentsCoercible_possibleTypeNormalizations_branch
                schema variableValues runtimeType (schema.getPossibleTypes returnType)
                mergedSubselections hruntimeObject hruntimeMem hnormalizedChildNonempty
                hbranchesReady
            exact hpossible runtimeType [runtimeType] hruntimeObject (by simp)
              hruntimeStack (hmergedSemanticReady runtimeType hruntimeMem)
              (hmergedSource runtimeType hruntimeMem)
              (hmergedMerge runtimeType hruntimeMem) hmergedFree
              (hmergedFeasible runtimeType hruntimeMem) hnormalizedChild
          · exact selectionSetArgumentsCoercible_of_no_feasible_field schema
              variableValues runtimeType [runtimeType] mergedSubselections
              (hmergedFeasible runtimeType hruntimeMem) hcontains
      have hremovedCoercible :=
        selectionSetRemovedResponseReady_of_filteredSource schema variableValues
          variableDefinitions parentType responseName fieldName arguments
          subselections rest fieldDefinition typeConditions hobject hparent
          hlookupValid hsource hmerge hfeasible hlookup hnormalizedField.1
          (by simpa [returnType] using hmergedCoercible)
      have hsourceRest :=
        selectionSetArgumentsCoercible_of_filtered_and_removed schema variableValues
          parentType responseName rest hfilteredCoercible hremovedCoercible
      constructor
      · intro _hdirectives definition hdefinitionLookup
        have hdefinition : definition = fieldDefinition := by
          rw [hlookup] at hdefinitionLookup
          exact Option.some.inj hdefinitionLookup.symm
        subst definition
        exact ⟨hnormalizedField.1, by
          intro runtimeType hinclude
          exact
            ((selectionSetArgumentsCoercible_append schema variableValues runtimeType
              subselections (mergeSelectionSets matching)).1
                (hmergedCoercible runtimeType
                  (by simpa [returnType] using hinclude))).1⟩
      · exact hsourceRest
  | case4 parentType rest directives subselections happend =>
      intro typeConditions hobject hparent hstack hready hsource hmerge
        hfree hfeasible hnormalized
      have hselectionFree := selectionSetDirectiveFree_head hfree
      have hdirectives : directives = [] := hselectionFree.1
      subst directives
      have hrestFree := selectionSetDirectiveFree_tail hfree
      have hheadReady :
          selectionSemanticsReady schema parentType
            (Selection.inlineFragment none [] subselections) := by
        unfold selectionSetSemanticsReady at hready
        exact hready _ (by simp)
      have hbodyReady : selectionSetSemanticsReady schema parentType subselections := by
        simpa [selectionSemanticsReady] using hheadReady
      have hheadSource := selectionSetFilteredCurrentSourceValid_head hsource
      have hbodySource :
          selectionSetFilteredCurrentSourceValid schema variableDefinitions
            parentType subselections := by
        simpa [selectionFilteredCurrentSourceValid] using hheadSource.2
      have htailReady := selectionSetSemanticsReady_tail hready
      have htailSource := selectionSetFilteredCurrentSourceValid_tail hsource
      have hbodyTailReady := selectionSetSemanticsReady_append hbodyReady htailReady
      have hbodyTailSource :=
        selectionSetFilteredCurrentSourceValid_append hbodySource htailSource
      have hbodyTailMerge :=
        fieldsInSetCanMerge_inlineFragment_none_flatten schema parentType subselections
          rest hmerge
      have hbodyTailFree :=
        selectionSetDirectiveFree_append hselectionFree.2 hrestFree
      have hbodyFeasible :
          selectionSetTypeConditionFeasible schema parentType typeConditions
            subselections := by
        simpa [selectionSetTypeConditionFeasible, selectionTypeConditionFeasible] using
          hfeasible.1
      have htailFeasible := selectionSetTypeConditionFeasible_tail hfeasible
      have hbodyTailFeasible :=
        selectionSetTypeConditionFeasible_append hbodyFeasible htailFeasible
      have happendCoercible := happend typeConditions hobject hparent hstack
        hbodyTailReady hbodyTailSource hbodyTailMerge hbodyTailFree
        hbodyTailFeasible (by simpa [normalizeSelectionSet] using hnormalized)
      have hparts :=
        (selectionSetArgumentsCoercible_append schema variableValues parentType
          subselections rest).1 happendCoercible
      exact ⟨by
          intro _hdirectives _htypeCondition
          exact hparts.1,
        hparts.2⟩
  | case5 parentType rest typeCondition directives subselections hoverlap
      _hrest happend =>
      intro typeConditions hobject hparent hstack hready hsource hmerge
        hfree hfeasible hnormalized
      have hselectionFree := selectionSetDirectiveFree_head hfree
      have hdirectives : directives = [] := hselectionFree.1
      subst directives
      have hrestFree := selectionSetDirectiveFree_tail hfree
      have hheadReady :
          selectionSemanticsReady schema parentType
            (Selection.inlineFragment (some typeCondition) [] subselections) := by
        unfold selectionSetSemanticsReady at hready
        exact hready _ (by simp)
      have hbodyReady : selectionSetSemanticsReady schema parentType subselections := by
        have hpair :
            selectionSetLookupValid schema typeCondition subselections
              ∧ (schema.typesOverlapBool parentType typeCondition = true ->
                selectionSetSemanticsReady schema parentType subselections) := by
          simpa [selectionSemanticsReady] using hheadReady
        exact hpair.2 hoverlap
      have hheadSource := selectionSetFilteredCurrentSourceValid_head hsource
      have hbodySource :
          selectionSetFilteredCurrentSourceValid schema variableDefinitions
            parentType subselections := by
        simpa [selectionFilteredCurrentSourceValid] using hheadSource.2 hoverlap
      have htailReady := selectionSetSemanticsReady_tail hready
      have htailSource := selectionSetFilteredCurrentSourceValid_tail hsource
      have hbodyTailReady := selectionSetSemanticsReady_append hbodyReady htailReady
      have hbodyTailSource :=
        selectionSetFilteredCurrentSourceValid_append hbodySource htailSource
      have hlookupBodyType : selectionSetLookupValid schema typeCondition subselections := by
        have hpair :
            selectionSetLookupValid schema typeCondition subselections
              ∧ (schema.typesOverlapBool parentType typeCondition = true ->
                selectionSetSemanticsReady schema parentType subselections) := by
          simpa [selectionSemanticsReady] using hheadReady
        exact hpair.1
      have hlookupBodyParent :=
        selectionSetLookupValid_of_selectionSetSemanticsReady subselections hbodyReady
      have hlookupRest :=
        selectionSetLookupValid_of_selectionSetSemanticsReady rest htailReady
      have hbodyTailMerge :=
        fieldsInSetCanMerge_inlineFragment_some_overlap_flatten_object schema
          parentType typeCondition subselections rest hschema hobject hoverlap
          hlookupBodyParent hlookupBodyType hlookupRest hmerge
      have hbodyTailFree :=
        selectionSetDirectiveFree_append hselectionFree.2 hrestFree
      have hbodyFeasible :
          selectionSetTypeConditionFeasible schema parentType
            (typeCondition :: typeConditions) subselections := by
        simpa [selectionSetTypeConditionFeasible, selectionTypeConditionFeasible] using
          hfeasible.1
      have htailFeasible := selectionSetTypeConditionFeasible_tail hfeasible
      have hbodyFeasibleOuter :=
        selectionSetTypeConditionFeasible_of_stack_subset schema
          (fun candidate hcandidate =>
            List.mem_cons_of_mem typeCondition hcandidate)
          subselections hbodyFeasible
      have hbodyTailFeasible :=
        selectionSetTypeConditionFeasible_append hbodyFeasibleOuter htailFeasible
      have happendCoercible := happend typeConditions hobject hparent hstack
        hbodyTailReady hbodyTailSource hbodyTailMerge hbodyTailFree
        hbodyTailFeasible
        (by simpa [normalizeSelectionSet, hoverlap] using hnormalized)
      have hparts :=
        (selectionSetArgumentsCoercible_append schema variableValues parentType
          subselections rest).1 happendCoercible
      exact ⟨by
          intro _hdirectives _htypeCondition
          exact hparts.1,
        hparts.2⟩
  | case6 parentType rest typeCondition directives subselections hoverlap hrest =>
      intro typeConditions hobject hparent hstack hready hsource hmerge
        hfree hfeasible hnormalized
      have htailReady := selectionSetSemanticsReady_tail hready
      have htailSource := selectionSetFilteredCurrentSourceValid_tail hsource
      have htailMerge :=
        fieldsInSetCanMerge_tail schema parentType
          (Selection.inlineFragment (some typeCondition) directives subselections)
          rest hmerge
      have htailFree := selectionSetDirectiveFree_tail hfree
      have htailFeasible := selectionSetTypeConditionFeasible_tail hfeasible
      have hfalse : schema.typesOverlapBool parentType typeCondition = false := by
        cases hmatch : schema.typesOverlapBool parentType typeCondition
        · rfl
        · contradiction
      have hrestCoercible := hrest typeConditions hobject hparent hstack htailReady
        htailSource htailMerge htailFree htailFeasible
        (by simpa [normalizeSelectionSet, hfalse] using hnormalized)
      have hbodyFeasible :
          selectionSetTypeConditionFeasible schema parentType
            (typeCondition :: typeConditions) subselections := by
        simpa [selectionSetTypeConditionFeasible, selectionTypeConditionFeasible] using
          hfeasible.1
      have hbodyContainsFalse :
          ¬ selectionSetContainsTypeConditionFeasibleField schema
            (typeCondition :: typeConditions) subselections := by
        intro hcontains
        have hstackFeasible :=
          typeConditionStackFeasible_of_selectionSetContains_forValidity schema
            (typeCondition :: typeConditions) subselections hcontains
        have htrue :=
          typesOverlapBool_true_of_feasible_cons_stack_containing_object schema
            hobject hparent hstackFeasible
        rw [hfalse] at htrue
        contradiction
      have hbodyCoercible :=
        selectionSetArgumentsCoercible_of_no_feasible_field schema variableValues
          parentType (typeCondition :: typeConditions) subselections hbodyFeasible
          hbodyContainsFalse
      exact ⟨by
          intro _hdirectives _htypeCondition
          exact hbodyCoercible,
        hrestCoercible⟩

theorem selectionSetArgumentsCoercible_filterSelectionSetBoolCase
    (schema : Schema) (variableValues : Execution.VariableValues)
    (boolCase : BoolCase) (operation : Operation) (parentType : Name)
    : ∀ selectionSet,
        variableValuesAgreeWithCase variableValues boolCase (operationBoolVars operation)
        -> (∀ varName,
              varName ∈ selectionSetBooleanVariables selectionSet
              -> varName ∈ selectionSetBooleanVariables operation.selectionSet)
        -> selectionSetArgumentsCoercible schema variableValues parentType selectionSet
        -> selectionSetArgumentsCoercible schema variableValues parentType
            (filterSelectionSetBoolCase boolCase selectionSet)
  | [], _hagrees, _hvariables, _hsource => by
      simp [filterSelectionSetBoolCase, selectionSetArgumentsCoercible]
  | Selection.field responseName fieldName arguments directives children :: rest,
      hagrees, hvariables, hsource => by
      have hdirectiveVariables : ∀ varName,
          varName ∈ directivesBooleanVariables directives
          -> varName ∈ selectionSetBooleanVariables operation.selectionSet := by
        intro varName hmem
        exact hvariables varName (by
          simp [selectionSetBooleanVariables, selectionBooleanVariables, hmem])
      have hchildVariables : ∀ varName,
          varName ∈ selectionSetBooleanVariables children
          -> varName ∈ selectionSetBooleanVariables operation.selectionSet := by
        intro varName hmem
        exact hvariables varName (by
          simp [selectionSetBooleanVariables, selectionBooleanVariables, hmem])
      have hrestVariables : ∀ varName,
          varName ∈ selectionSetBooleanVariables rest
          -> varName ∈ selectionSetBooleanVariables operation.selectionSet := by
        intro varName hmem
        exact hvariables varName (by
          simp [selectionSetBooleanVariables, selectionBooleanVariables, hmem])
      have hallowEq :
          directivesAllowIn boolCase directives
            = Execution.selectionDirectivesAllowBool variableValues directives :=
        directivesAllowInCase_eq_execution_of_operationVariables
          variableValues boolCase operation directives hagrees hdirectiveVariables
      by_cases hallow : directivesAllowIn boolCase directives = true
      · have hexecutionAllow :
            Execution.selectionDirectivesAllowBool variableValues directives = true := by
          rw [← hallowEq]
          exact hallow
        have hsourceField := hsource.1 hexecutionAllow
        have hfilteredRest :=
          selectionSetArgumentsCoercible_filterSelectionSetBoolCase schema
            variableValues boolCase operation parentType rest hagrees hrestVariables
            hsource.2
        cases children with
        | nil =>
            have hfilteredField :
                selectionArgumentsCoercible schema variableValues parentType
                  (.field responseName fieldName arguments [] []) := by
              intro _hdirectives definition hlookup
              exact hsourceField definition hlookup
            simpa [filterSelectionSetBoolCase, hallow,
              selectionSetArgumentsCoercible] using
              And.intro hfilteredField hfilteredRest
        | cons child children =>
            have hfilteredChildren : ∀ runtimeType definition,
                schema.lookupField parentType fieldName = some definition
                -> schema.typeIncludesObjectBool definition.outputType.namedType
                    runtimeType = true
                -> selectionSetArgumentsCoercible schema variableValues runtimeType
                    (filterSelectionSetBoolCase boolCase (child :: children)) := by
              intro runtimeType definition hlookup hinclude
              exact selectionSetArgumentsCoercible_filterSelectionSetBoolCase schema
                variableValues boolCase operation runtimeType (child :: children)
                hagrees hchildVariables
                ((hsourceField definition hlookup).2 runtimeType hinclude)
            cases hchildren :
                filterSelectionSetBoolCase boolCase (child :: children) with
            | nil =>
                have hfilteredField :
                    selectionArgumentsCoercible schema variableValues parentType
                      (.field responseName fieldName arguments [] []) := by
                  intro _hdirectives definition hlookup
                  refine ⟨(hsourceField definition hlookup).1, ?_⟩
                  intro runtimeType hinclude
                  simp [selectionSetArgumentsCoercible]
                simpa [filterSelectionSetBoolCase, hallow, hchildren,
                  selectionSetArgumentsCoercible] using
                  And.intro hfilteredField hfilteredRest
            | cons filteredChild filteredChildren =>
                have hfilteredField :
                    selectionArgumentsCoercible schema variableValues parentType
                      (.field responseName fieldName arguments []
                        (filteredChild :: filteredChildren)) := by
                  intro _hdirectives definition hlookup
                  refine ⟨(hsourceField definition hlookup).1, ?_⟩
                  intro runtimeType hinclude
                  simpa [hchildren] using
                    hfilteredChildren runtimeType definition hlookup hinclude
                simpa [filterSelectionSetBoolCase, hallow, hchildren,
                  selectionSetArgumentsCoercible] using
                  And.intro hfilteredField hfilteredRest
      · have hallowFalse : directivesAllowIn boolCase directives = false := by
          cases hmatch : directivesAllowIn boolCase directives
          · rfl
          · contradiction
        simpa [filterSelectionSetBoolCase, hallowFalse] using
          selectionSetArgumentsCoercible_filterSelectionSetBoolCase schema
            variableValues boolCase operation parentType rest hagrees hrestVariables
            hsource.2
  | Selection.inlineFragment typeCondition directives children :: rest,
      hagrees, hvariables, hsource => by
      have hdirectiveVariables : ∀ varName,
          varName ∈ directivesBooleanVariables directives
          -> varName ∈ selectionSetBooleanVariables operation.selectionSet := by
        intro varName hmem
        exact hvariables varName (by
          simp [selectionSetBooleanVariables, selectionBooleanVariables, hmem])
      have hchildVariables : ∀ varName,
          varName ∈ selectionSetBooleanVariables children
          -> varName ∈ selectionSetBooleanVariables operation.selectionSet := by
        intro varName hmem
        exact hvariables varName (by
          simp [selectionSetBooleanVariables, selectionBooleanVariables, hmem])
      have hrestVariables : ∀ varName,
          varName ∈ selectionSetBooleanVariables rest
          -> varName ∈ selectionSetBooleanVariables operation.selectionSet := by
        intro varName hmem
        exact hvariables varName (by
          simp [selectionSetBooleanVariables, selectionBooleanVariables, hmem])
      have hallowEq :
          directivesAllowIn boolCase directives
            = Execution.selectionDirectivesAllowBool variableValues directives :=
        directivesAllowInCase_eq_execution_of_operationVariables
          variableValues boolCase operation directives hagrees hdirectiveVariables
      by_cases hallow : directivesAllowIn boolCase directives = true
      · have hexecutionAllow :
            Execution.selectionDirectivesAllowBool variableValues directives = true := by
          rw [← hallowEq]
          exact hallow
        have hfilteredRest :=
          selectionSetArgumentsCoercible_filterSelectionSetBoolCase schema
            variableValues boolCase operation parentType rest hagrees hrestVariables
            hsource.2
        cases hchildren : filterSelectionSetBoolCase boolCase children with
        | nil =>
            simpa [filterSelectionSetBoolCase, hallow, hchildren] using hfilteredRest
        | cons child restChildren =>
            have hfilteredChildren :=
              selectionSetArgumentsCoercible_filterSelectionSetBoolCase schema
                variableValues boolCase operation parentType children hagrees
                hchildVariables
            have hfilteredFragment :
                selectionArgumentsCoercible schema variableValues parentType
                  (.inlineFragment typeCondition [] (child :: restChildren)) := by
              intro _hdirectives htypeCondition
              simpa [hchildren] using
                hfilteredChildren (hsource.1 hexecutionAllow htypeCondition)
            simpa [filterSelectionSetBoolCase, hallow, hchildren,
              selectionSetArgumentsCoercible] using
              And.intro hfilteredFragment hfilteredRest
      · have hallowFalse : directivesAllowIn boolCase directives = false := by
          cases hmatch : directivesAllowIn boolCase directives
          · rfl
          · contradiction
        simpa [filterSelectionSetBoolCase, hallowFalse] using
          selectionSetArgumentsCoercible_filterSelectionSetBoolCase schema
            variableValues boolCase operation parentType rest hagrees hrestVariables
            hsource.2
termination_by selectionSet => SelectionSet.size selectionSet
decreasing_by
  all_goals
    simp_wf
    simp_all [SelectionSet.size, Selection.size]
    try omega

theorem selectionSetArgumentsCoercible_of_filterSelectionSetBoolCase
    (schema : Schema) (variableValues : Execution.VariableValues)
    (boolCase : BoolCase) (operation : Operation) (parentType : Name)
    : ∀ selectionSet,
        variableValuesAgreeWithCase variableValues boolCase (operationBoolVars operation)
        -> (∀ varName,
              varName ∈ selectionSetBooleanVariables selectionSet
              -> varName ∈ selectionSetBooleanVariables operation.selectionSet)
        -> selectionSetArgumentsCoercible schema variableValues parentType
            (filterSelectionSetBoolCase boolCase selectionSet)
        -> selectionSetArgumentsCoercible schema variableValues parentType selectionSet
  | [], _hagrees, _hvariables, _hfiltered => by
      simp [selectionSetArgumentsCoercible]
  | Selection.field responseName fieldName arguments directives children :: rest,
      hagrees, hvariables, hfiltered => by
      have hdirectiveVariables : ∀ varName,
          varName ∈ directivesBooleanVariables directives
          -> varName ∈ selectionSetBooleanVariables operation.selectionSet := by
        intro varName hmem
        exact hvariables varName (by
          simp [selectionSetBooleanVariables, selectionBooleanVariables, hmem])
      have hchildVariables : ∀ varName,
          varName ∈ selectionSetBooleanVariables children
          -> varName ∈ selectionSetBooleanVariables operation.selectionSet := by
        intro varName hmem
        exact hvariables varName (by
          simp [selectionSetBooleanVariables, selectionBooleanVariables, hmem])
      have hrestVariables : ∀ varName,
          varName ∈ selectionSetBooleanVariables rest
          -> varName ∈ selectionSetBooleanVariables operation.selectionSet := by
        intro varName hmem
        exact hvariables varName (by
          simp [selectionSetBooleanVariables, selectionBooleanVariables, hmem])
      have hallowEq :
          directivesAllowIn boolCase directives
            = Execution.selectionDirectivesAllowBool variableValues directives :=
        directivesAllowInCase_eq_execution_of_operationVariables
          variableValues boolCase operation directives hagrees hdirectiveVariables
      by_cases hallow : directivesAllowIn boolCase directives = true
      · have hexecutionAllow :
            Execution.selectionDirectivesAllowBool variableValues directives = true := by
          rw [← hallowEq]
          exact hallow
        cases children with
        | nil =>
            have hparts :
                selectionArgumentsCoercible schema variableValues parentType
                    (.field responseName fieldName arguments [] [])
                  ∧ selectionSetArgumentsCoercible schema variableValues parentType
                    (filterSelectionSetBoolCase boolCase rest) := by
              simpa [filterSelectionSetBoolCase, hallow,
                selectionSetArgumentsCoercible] using hfiltered
            constructor
            · intro _hdirectives definition hlookup
              exact hparts.1 (by
                simp [Execution.selectionDirectivesAllowBool]) definition hlookup
            · exact
                selectionSetArgumentsCoercible_of_filterSelectionSetBoolCase
                  schema variableValues boolCase operation parentType rest hagrees
                  hrestVariables hparts.2
        | cons child children =>
            cases hfilteredChildren :
                filterSelectionSetBoolCase boolCase (child :: children) with
            | nil =>
                have hparts :
                    selectionArgumentsCoercible schema variableValues parentType
                        (.field responseName fieldName arguments [] [])
                      ∧ selectionSetArgumentsCoercible schema variableValues parentType
                        (filterSelectionSetBoolCase boolCase rest) := by
                  simpa [filterSelectionSetBoolCase, hallow, hfilteredChildren,
                    selectionSetArgumentsCoercible] using hfiltered
                constructor
                · intro _hdirectives definition hlookup
                  have hfield := hparts.1 (by
                    simp [Execution.selectionDirectivesAllowBool]) definition hlookup
                  exact ⟨hfield.1, by
                    intro runtimeType hinclude
                    exact
                      selectionSetArgumentsCoercible_of_filterSelectionSetBoolCase
                        schema variableValues boolCase operation runtimeType
                        (child :: children) hagrees hchildVariables
                        (by simp [hfilteredChildren, selectionSetArgumentsCoercible])⟩
                · exact
                    selectionSetArgumentsCoercible_of_filterSelectionSetBoolCase
                      schema variableValues boolCase operation parentType rest hagrees
                      hrestVariables hparts.2
            | cons filteredChild filteredChildren =>
                have hparts :
                    selectionArgumentsCoercible schema variableValues parentType
                        (.field responseName fieldName arguments []
                          (filteredChild :: filteredChildren))
                      ∧ selectionSetArgumentsCoercible schema variableValues parentType
                        (filterSelectionSetBoolCase boolCase rest) := by
                  simpa [filterSelectionSetBoolCase, hallow, hfilteredChildren,
                    selectionSetArgumentsCoercible] using hfiltered
                constructor
                · intro _hdirectives definition hlookup
                  have hfield := hparts.1 (by
                    simp [Execution.selectionDirectivesAllowBool]) definition hlookup
                  exact ⟨hfield.1, by
                    intro runtimeType hinclude
                    exact
                      selectionSetArgumentsCoercible_of_filterSelectionSetBoolCase
                        schema variableValues boolCase operation runtimeType
                        (child :: children) hagrees hchildVariables
                        (by simpa [hfilteredChildren] using
                          hfield.2 runtimeType hinclude)⟩
                · exact
                    selectionSetArgumentsCoercible_of_filterSelectionSetBoolCase
                      schema variableValues boolCase operation parentType rest hagrees
                      hrestVariables hparts.2
      · have hallowFalse : directivesAllowIn boolCase directives = false := by
          cases hmatch : directivesAllowIn boolCase directives
          · rfl
          · contradiction
        have hexecutionFalse :
            Execution.selectionDirectivesAllowBool variableValues directives = false := by
          rw [← hallowEq]
          exact hallowFalse
        constructor
        · intro hexecutionTrue _definition _hlookup
          rw [hexecutionFalse] at hexecutionTrue
          contradiction
        · exact
            selectionSetArgumentsCoercible_of_filterSelectionSetBoolCase
              schema variableValues boolCase operation parentType rest hagrees
              hrestVariables (by
                simpa [filterSelectionSetBoolCase, hallowFalse] using hfiltered)
  | Selection.inlineFragment typeCondition directives children :: rest,
      hagrees, hvariables, hfiltered => by
      have hdirectiveVariables : ∀ varName,
          varName ∈ directivesBooleanVariables directives
          -> varName ∈ selectionSetBooleanVariables operation.selectionSet := by
        intro varName hmem
        exact hvariables varName (by
          simp [selectionSetBooleanVariables, selectionBooleanVariables, hmem])
      have hchildVariables : ∀ varName,
          varName ∈ selectionSetBooleanVariables children
          -> varName ∈ selectionSetBooleanVariables operation.selectionSet := by
        intro varName hmem
        exact hvariables varName (by
          simp [selectionSetBooleanVariables, selectionBooleanVariables, hmem])
      have hrestVariables : ∀ varName,
          varName ∈ selectionSetBooleanVariables rest
          -> varName ∈ selectionSetBooleanVariables operation.selectionSet := by
        intro varName hmem
        exact hvariables varName (by
          simp [selectionSetBooleanVariables, selectionBooleanVariables, hmem])
      have hallowEq :
          directivesAllowIn boolCase directives
            = Execution.selectionDirectivesAllowBool variableValues directives :=
        directivesAllowInCase_eq_execution_of_operationVariables
          variableValues boolCase operation directives hagrees hdirectiveVariables
      by_cases hallow : directivesAllowIn boolCase directives = true
      · cases hfilteredChildren : filterSelectionSetBoolCase boolCase children with
        | nil =>
            have hrestFiltered :
                selectionSetArgumentsCoercible schema variableValues parentType
                  (filterSelectionSetBoolCase boolCase rest) := by
              simpa [filterSelectionSetBoolCase, hallow, hfilteredChildren] using
                hfiltered
            constructor
            · intro _hdirectives _htypeCondition
              exact
                selectionSetArgumentsCoercible_of_filterSelectionSetBoolCase
                  schema variableValues boolCase operation parentType children hagrees
                  hchildVariables
                  (by simp [hfilteredChildren, selectionSetArgumentsCoercible])
            · exact
                selectionSetArgumentsCoercible_of_filterSelectionSetBoolCase
                  schema variableValues boolCase operation parentType rest hagrees
                  hrestVariables hrestFiltered
        | cons filteredChild filteredChildren =>
            have hparts :
                selectionArgumentsCoercible schema variableValues parentType
                    (.inlineFragment typeCondition []
                      (filteredChild :: filteredChildren))
                  ∧ selectionSetArgumentsCoercible schema variableValues parentType
                    (filterSelectionSetBoolCase boolCase rest) := by
              simpa [filterSelectionSetBoolCase, hallow, hfilteredChildren,
                selectionSetArgumentsCoercible] using hfiltered
            constructor
            · intro _hdirectives htypeCondition
              have hfilteredReady := hparts.1 (by
                simp [Execution.selectionDirectivesAllowBool]) htypeCondition
              exact
                selectionSetArgumentsCoercible_of_filterSelectionSetBoolCase
                  schema variableValues boolCase operation parentType children hagrees
                  hchildVariables
                  (by simpa [hfilteredChildren] using hfilteredReady)
            · exact
                selectionSetArgumentsCoercible_of_filterSelectionSetBoolCase
                  schema variableValues boolCase operation parentType rest hagrees
                  hrestVariables hparts.2
      · have hallowFalse : directivesAllowIn boolCase directives = false := by
          cases hmatch : directivesAllowIn boolCase directives
          · rfl
          · contradiction
        have hexecutionFalse :
            Execution.selectionDirectivesAllowBool variableValues directives = false := by
          rw [← hallowEq]
          exact hallowFalse
        constructor
        · intro hexecutionTrue _htypeCondition
          rw [hexecutionFalse] at hexecutionTrue
          contradiction
        · exact
            selectionSetArgumentsCoercible_of_filterSelectionSetBoolCase
              schema variableValues boolCase operation parentType rest hagrees
              hrestVariables (by
                simpa [filterSelectionSetBoolCase, hallowFalse] using hfiltered)
termination_by selectionSet => SelectionSet.size selectionSet
decreasing_by
  all_goals
    simp_wf
    simp_all [SelectionSet.size, Selection.size]
    try omega

theorem selectionSetArgumentsCoercible_of_wrapWithBoolCase
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name) (selectionSet : List Selection)
    : ∀ boolCase,
        (∀ varName value,
          (varName, value) ∈ boolCase
          -> Execution.inputValueBoolean? variableValues (.variable varName) = some value)
        -> selectionSetArgumentsCoercible schema variableValues parentType
            (wrapWithBoolCase boolCase selectionSet)
        -> selectionSetArgumentsCoercible schema variableValues parentType selectionSet
  | [], _hagrees, hready => hready
  | (varName, value) :: rest, hagrees, hready => by
      have hchildren :
          selectionSetArgumentsCoercible schema variableValues parentType
            (wrapWithBoolCase rest selectionSet) :=
        hready.1
          (selectionDirectivesAllowBool_boolCaseBit_of_agrees variableValues
            varName value (hagrees varName value (by simp))) trivial
      exact selectionSetArgumentsCoercible_of_wrapWithBoolCase schema variableValues
        parentType selectionSet rest
        (by
          intro candidate candidateValue hmem
          exact hagrees candidate candidateValue (by simp [hmem]))
        hchildren

theorem selectionSetArgumentsCoercible_wrapWithBoolCase_of_complete
    (schema : Schema) (variableValues : Execution.VariableValues)
    (variables : List BoolVar) (parentType : Name) (selectionSet : List Selection)
    (hcomplete : boolVarsComplete variables variableValues)
    : ∀ boolCase,
        (∀ varName value, (varName, value) ∈ boolCase -> varName ∈ variables)
        -> ((∀ varName value,
              (varName, value) ∈ boolCase
              -> Execution.inputValueBoolean? variableValues (.variable varName)
                  = some value)
            -> selectionSetArgumentsCoercible schema variableValues parentType
                selectionSet)
        -> selectionSetArgumentsCoercible schema variableValues parentType
            (wrapWithBoolCase boolCase selectionSet)
  | [], _hcaseVariables, hbody => hbody (by simp)
  | (varName, value) :: rest, hcaseVariables, hbody => by
      rcases hcomplete varName (hcaseVariables varName value (by simp)) with
        ⟨actual, hactual⟩
      have hselection :
          selectionArgumentsCoercible schema variableValues parentType
            (.inlineFragment none [directiveForBit varName value]
              (wrapWithBoolCase rest selectionSet)) := by
        by_cases heq : actual = value
        · subst actual
          intro _hdirectives _htypeCondition
          exact selectionSetArgumentsCoercible_wrapWithBoolCase_of_complete schema
            variableValues variables parentType selectionSet hcomplete rest
            (by
              intro candidate candidateValue hmem
              exact hcaseVariables candidate candidateValue (by simp [hmem]))
            (by
              intro hagrees
              apply hbody
              intro candidate candidateValue hmem
              rcases List.mem_cons.mp hmem with hhead | htail
              · cases hhead
                exact hactual
              · exact hagrees candidate candidateValue htail)
        · have hactualOpposite : actual = !value := by
            cases actual <;> cases value <;> simp_all
          subst actual
          intro hallow _htypeCondition
          have hfalse :=
            selectionDirectivesAllowBool_boolCaseBit_of_mismatch variableValues
              varName value hactual
          rw [hfalse] at hallow
          contradiction
      change selectionSetArgumentsCoercible schema variableValues parentType
        [Selection.inlineFragment none [directiveForBit varName value]
          (wrapWithBoolCase rest selectionSet)]
      exact ⟨hselection, by trivial⟩

private theorem completeNormalizeBranches_argumentsCoercible
    (schema : Schema) (variableValues : Execution.VariableValues)
    (operation : Operation)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hrootObject : schema.objectType (operation.rootType schema))
    (hsourceReady
      : selectionSetSemanticsReady schema (operation.rootType schema)
          operation.selectionSet)
    (hsourceMerge
      : FieldMerge.fieldsInSetCanMerge schema (operation.rootType schema)
          operation.selectionSet)
    (hsourceCoercible
      : selectionSetArgumentsCoercible schema variableValues
          (operation.rootType schema) operation.selectionSet)
    (hcomplete : boolVarsComplete (operationBoolVars operation) variableValues)
    : ∀ cases : List BoolCase,
        (∀ boolCase,
          boolCase ∈ cases
          -> completeNormalBoolCase (operationBoolVars operation) boolCase)
        -> selectionSetArgumentsCoercible schema variableValues
            (operation.rootType schema)
            (List.flatten
              (cases.map
                fun boolCase =>
                  match normalizeBoolCaseForType schema boolCase
                          (operation.rootType schema) operation.selectionSet with
                  | [] => []
                  | selection :: rest =>
                      wrapWithBoolCase boolCase (selection :: rest)))
  | [], _hcases => by
      simp [selectionSetArgumentsCoercible]
  | boolCase :: cases, hcases => by
      have hcase := hcases boolCase (by simp)
      have hrestCases : ∀ candidate,
          candidate ∈ cases
          -> completeNormalBoolCase (operationBoolVars operation) candidate := by
        intro candidate hmem
        exact hcases candidate (by simp [hmem])
      have hrestReady :=
        completeNormalizeBranches_argumentsCoercible schema variableValues operation
          hschema hrootObject hsourceReady hsourceMerge hsourceCoercible hcomplete
          cases hrestCases
      have hbranchReady :
          selectionSetArgumentsCoercible schema variableValues
            (operation.rootType schema)
            (match normalizeBoolCaseForType schema boolCase
                (operation.rootType schema) operation.selectionSet with
              | [] => []
              | selection :: rest =>
                  wrapWithBoolCase boolCase (selection :: rest)) := by
        cases hnormalized : normalizeBoolCaseForType schema boolCase
            (operation.rootType schema) operation.selectionSet with
        | nil => simp [selectionSetArgumentsCoercible]
        | cons selection rest =>
            apply selectionSetArgumentsCoercible_wrapWithBoolCase_of_complete
              schema variableValues (operationBoolVars operation)
              (operation.rootType schema) (selection :: rest) hcomplete boolCase
            · intro varName value hpair
              exact (hcase.2.2 varName).1
                (List.mem_map.mpr ⟨(varName, value), hpair, rfl⟩)
            · intro hagrees
              have hfilteredCoercible :
                  selectionSetArgumentsCoercible schema variableValues
                    (operation.rootType schema)
                    (filterSelectionSetBoolCase boolCase operation.selectionSet) :=
                selectionSetArgumentsCoercible_filterSelectionSetBoolCase schema
                  variableValues boolCase operation (operation.rootType schema)
                  operation.selectionSet
                  (by
                    intro varName hmem
                    have hcaseVar : varName ∈ boolCase.map Prod.fst :=
                      (hcase.2.2 varName).2 hmem
                    rcases List.mem_map.mp hcaseVar with
                      ⟨⟨candidate, value⟩, hpair, hname⟩
                    change candidate = varName at hname
                    subst candidate
                    exact (hagrees varName value hpair).trans
                      (BoolCase.lookup?_eq_of_pair_mem_nodup hcase.2.1 hpair).symm)
                  (by intro _varName hmem; exact hmem) hsourceCoercible
              have hfilteredReady :
                  selectionSetSemanticsReady schema (operation.rootType schema)
                    (filterSelectionSetBoolCase boolCase operation.selectionSet) :=
                filterSelectionSetBoolCase_selectionSetSemanticsReady schema boolCase
                  (operation.rootType schema) operation.selectionSet hsourceReady
              have hfilteredMerge :
                  FieldMerge.fieldsInSetCanMerge schema (operation.rootType schema)
                    (filterSelectionSetBoolCase boolCase operation.selectionSet) :=
                fieldsInSetCanMerge_filterSelectionSetBoolCase schema boolCase
                  hsourceMerge
              have hfilteredFree :
                  selectionSetDirectiveFree
                    (filterSelectionSetBoolCase boolCase operation.selectionSet) :=
                filterSelectionSetBoolCase_directiveFree schema boolCase
                  operation.selectionSet
              have hnormalizedReady :=
                selectionSetArgumentsCoercible_normalizeSelectionSetAt schema
                  variableValues hschema (operation.rootType schema)
                  (filterSelectionSetBoolCase boolCase operation.selectionSet)
                  hrootObject hfilteredReady hfilteredMerge hfilteredFree
                  hfilteredCoercible
              change normalizeSelectionSet schema (operation.rootType schema)
                  (filterSelectionSetBoolCase boolCase operation.selectionSet)
                = selection :: rest at hnormalized
              rw [hnormalized] at hnormalizedReady
              exact hnormalizedReady
      simpa [selectionSetArgumentsCoercible] using
        (selectionSetArgumentsCoercible_append schema variableValues
          (operation.rootType schema) _ _).2 ⟨hbranchReady, hrestReady⟩

theorem normalizeBoolCaseForType_argumentsCoercible_of_completeRoot
    (schema : Schema) (variableValues : Execution.VariableValues)
    (variables : List BoolVar) (parentType : Name) (selectionSet : List Selection)
    (boolCase : BoolCase)
    (hvariablesNodup : variables.Nodup)
    (hcase : boolCase ∈ allBoolCases variables)
    (hagrees : variableValuesAgreeWithCase variableValues boolCase variables)
    (hroot
      : selectionSetArgumentsCoercible schema variableValues parentType
          (completeNormalizeRootSelectionSet schema variables parentType selectionSet))
    : selectionSetArgumentsCoercible schema variableValues parentType
        (normalizeBoolCaseForType schema boolCase parentType selectionSet) := by
  cases hnormalized
        : normalizeBoolCaseForType schema boolCase parentType selectionSet with
  | nil =>
      simp [selectionSetArgumentsCoercible]
  | cons selection rest =>
      have hwrapped :
          selectionSetArgumentsCoercible schema variableValues parentType
            (wrapWithBoolCase boolCase (selection :: rest)) := by
        apply selectionSetArgumentsCoercible_of_subset hroot
        intro candidate hcandidate
        unfold completeNormalizeRootSelectionSet
        apply List.mem_flatten.mpr
        refine ⟨wrapWithBoolCase boolCase (selection :: rest), ?_, hcandidate⟩
        apply List.mem_map.mpr
        refine ⟨boolCase, hcase, ?_⟩
        simp [normalizeBoolCaseForType] at hnormalized
        simp [hnormalized]
      have hcomplete : completeNormalBoolCase variables boolCase :=
        completeNormalBoolCase_of_mem_allBoolCases
          hvariablesNodup hcase
      exact selectionSetArgumentsCoercible_of_wrapWithBoolCase schema variableValues
        parentType (selection :: rest) boolCase
        (by
          intro varName value hpair
          exact inputValueBoolean?_eq_of_agrees_completeNormalBoolCase
            hcomplete hagrees hpair)
        (by simpa [hnormalized] using hwrapped)

theorem operationArgumentsCoercible_of_completeNormalizeOperation
    (schema : Schema) (operation : Operation)
    (suppliedValues : Execution.VariableValues)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hvalid : Validation.operationDefinitionValid schema operation)
    (hfields : operationFieldsValidInPossibleTypes schema operation)
    (hboolFeasible : operationBoolTypeConditionFeasible schema operation)
    (hcomplete : operationBoolVarsComplete operation suppliedValues)
    (hnormalized
      : operationArgumentsCoercible schema suppliedValues
          (completeNormalizeOperation schema operation))
    : operationArgumentsCoercible schema suppliedValues operation := by
  let effectiveValues := Execution.coerceVariableValues operation suppliedValues
  have hrootObject : schema.objectType (operation.rootType schema) :=
    operation_root_object_of_valid hschema hvalid
  have hsourceReady :
      selectionSetSemanticsReady schema (operation.rootType schema)
        operation.selectionSet :=
    operation_selectionSetSemanticsReady_of_valid hschema hvalid
  have hsourceImplementation :
      Validation.selectionSetValidInPossibleTypes schema
        operation.variableDefinitions (operation.rootType schema)
        operation.selectionSet := by
    simpa [operationFieldsValidInPossibleTypes] using hfields
  have hsourceMerge :
      FieldMerge.fieldsInSetCanMerge schema (operation.rootType schema)
        operation.selectionSet :=
    Validation.operationDefinitionValid_fieldsInSetCanMerge hvalid
  have heffectiveComplete : operationBoolVarsComplete operation effectiveValues :=
    operationBoolVarsComplete_coerceVariableValues operation suppliedValues hcomplete
  rcases operationBoolVarsComplete_caseForVariableValues effectiveValues operation
      heffectiveComplete with
    ⟨boolCase, hcase, hagrees⟩
  have hfilteredReady :
      selectionSetSemanticsReady schema (operation.rootType schema)
        (filterSelectionSetBoolCase boolCase operation.selectionSet) :=
    filterSelectionSetBoolCase_selectionSetSemanticsReady schema boolCase
      (operation.rootType schema) operation.selectionSet hsourceReady
  have hfilteredSource :
      selectionSetFilteredCurrentSourceValid schema operation.variableDefinitions
        (operation.rootType schema)
        (filterSelectionSetBoolCase boolCase operation.selectionSet) :=
    selectionSetFilteredCurrentSourceValid_filterSelectionSetBoolCase
      schema operation.variableDefinitions hschema boolCase
      (operation.rootType schema) hrootObject operation.selectionSet
      hsourceImplementation
  have hfilteredMerge :
      FieldMerge.fieldsInSetCanMerge schema (operation.rootType schema)
        (filterSelectionSetBoolCase boolCase operation.selectionSet) :=
    fieldsInSetCanMerge_filterSelectionSetBoolCase schema boolCase hsourceMerge
  have hfilteredFree :
      selectionSetDirectiveFree
        (filterSelectionSetBoolCase boolCase operation.selectionSet) :=
    filterSelectionSetBoolCase_directiveFree schema boolCase operation.selectionSet
  have hcaseFeasible :
      selectionSetBoolTypeConditionFeasibleInCase schema
        (operation.rootType schema) [(operation.rootType schema)] boolCase
        operation.selectionSet :=
    operationBoolTypeConditionFeasible_inCase hboolFeasible hcase
  have hfilteredFeasible :
      selectionSetTypeConditionFeasible schema (operation.rootType schema)
        [(operation.rootType schema)]
        (filterSelectionSetBoolCase boolCase operation.selectionSet) :=
    selectionSetTypeConditionFeasible_filterSelectionSetBoolCase schema boolCase
      (operation.rootType schema) [(operation.rootType schema)]
      operation.selectionSet hcaseFeasible
  have hrootStack :
      objectSatisfiesTypeConditionStack schema (operation.rootType schema)
        [(operation.rootType schema)] :=
    objectSatisfiesTypeConditionStack_singleton_of_object_forValidity schema
      hrootObject
  have hnormalizedRoot :
      selectionSetArgumentsCoercible schema effectiveValues
        (operation.rootType schema)
        (completeNormalizeRootSelectionSet schema (operationBoolVars operation)
          (operation.rootType schema) operation.selectionSet) := by
    have hvalues :
        Execution.coerceVariableValues
            (completeNormalizeOperation schema operation) suppliedValues
          = effectiveValues := by
      simp [effectiveValues, Execution.coerceVariableValues,
        completeNormalizeOperation_variableDefinitions]
    unfold operationArgumentsCoercible at hnormalized
    rw [hvalues, completeNormalizeOperation_rootType,
      completeNormalizeOperation_selectionSet] at hnormalized
    exact hnormalized
  have hnormalizedCase :
      selectionSetArgumentsCoercible schema effectiveValues
        (operation.rootType schema)
        (normalizeBoolCaseForType schema boolCase (operation.rootType schema)
          operation.selectionSet) :=
    normalizeBoolCaseForType_argumentsCoercible_of_completeRoot schema
      effectiveValues (operationBoolVars operation) (operation.rootType schema)
      operation.selectionSet boolCase (operationBoolVars_nodup operation) hcase
      hagrees hnormalizedRoot
  have hfilteredCoercible :
      selectionSetArgumentsCoercible schema effectiveValues
        (operation.rootType schema)
        (filterSelectionSetBoolCase boolCase operation.selectionSet) := by
    apply selectionSetArgumentsCoercible_of_normalizeFilteredSelectionSet schema
      effectiveValues operation.variableDefinitions hschema
      (operation.rootType schema)
      (filterSelectionSetBoolCase boolCase operation.selectionSet)
      [(operation.rootType schema)] hrootObject (by simp) hrootStack
      hfilteredReady hfilteredSource hfilteredMerge hfilteredFree
      hfilteredFeasible
    simpa [normalizeBoolCaseForType] using hnormalizedCase
  unfold operationArgumentsCoercible
  exact selectionSetArgumentsCoercible_of_filterSelectionSetBoolCase schema
    effectiveValues boolCase operation (operation.rootType schema)
    operation.selectionSet hagrees (by intro _varName hmem; exact hmem)
    hfilteredCoercible

theorem operationArgumentsCoercible_completeNormalizeOperation
    (schema : Schema) (operation : Operation)
    (suppliedValues : Execution.VariableValues)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hvalid : Validation.operationDefinitionValid schema operation)
    (hcomplete : operationBoolVarsComplete operation suppliedValues)
    (hsource : operationArgumentsCoercible schema suppliedValues operation)
    : operationArgumentsCoercible schema suppliedValues
        (completeNormalizeOperation schema operation) := by
  let effectiveValues := Execution.coerceVariableValues operation suppliedValues
  have hrootObject : schema.objectType (operation.rootType schema) :=
    operation_root_object_of_valid hschema hvalid
  have hsourceReady :
      selectionSetSemanticsReady schema (operation.rootType schema)
        operation.selectionSet :=
    operation_selectionSetSemanticsReady_of_valid hschema hvalid
  have hsourceMerge :
      FieldMerge.fieldsInSetCanMerge schema (operation.rootType schema)
        operation.selectionSet :=
    Validation.operationDefinitionValid_fieldsInSetCanMerge hvalid
  have heffectiveComplete :
      boolVarsComplete (operationBoolVars operation) effectiveValues :=
    operationBoolVarsComplete_coerceVariableValues operation suppliedValues hcomplete
  have hsourceEffective :
      selectionSetArgumentsCoercible schema effectiveValues
        (operation.rootType schema) operation.selectionSet := by
    simpa [operationArgumentsCoercible, effectiveValues] using hsource
  have hnormalizedSelection :
      selectionSetArgumentsCoercible schema effectiveValues
        (operation.rootType schema)
        (completeNormalizeRootSelectionSet schema (operationBoolVars operation)
          (operation.rootType schema) operation.selectionSet) := by
    unfold completeNormalizeRootSelectionSet
    exact completeNormalizeBranches_argumentsCoercible schema effectiveValues
      operation hschema hrootObject hsourceReady hsourceMerge hsourceEffective
      heffectiveComplete (allBoolCases (operationBoolVars operation))
      (by
        intro boolCase hcase
        exact completeNormalBoolCase_of_mem_allBoolCases
          (operationBoolVars_nodup operation) hcase)
  have hvalues :
      Execution.coerceVariableValues
          (completeNormalizeOperation schema operation) suppliedValues
        = effectiveValues := by
    simp [effectiveValues, Execution.coerceVariableValues,
      completeNormalizeOperation_variableDefinitions]
  unfold operationArgumentsCoercible
  rw [hvalues, completeNormalizeOperation_rootType,
    completeNormalizeOperation_selectionSet]
  exact hnormalizedSelection

end CompleteNormalization

end NormalForm

end GraphQL
