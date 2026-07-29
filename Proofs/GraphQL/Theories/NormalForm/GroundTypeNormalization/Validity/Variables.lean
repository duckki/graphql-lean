import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Validity.SelectionSet
import Proofs.GraphQL.Validation.Variables

/-! Variable-use preservation for ground-type normalization. -/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

theorem selectionSetVariables_append (left right : List Selection)
    : Validation.selectionSetVariables (left ++ right)
      = Validation.selectionSetVariables left
        ++ Validation.selectionSetVariables right := by
  induction left with
  | nil =>
      simp [Validation.selectionSetVariables]
  | cons selection rest ih =>
      simp [Validation.selectionSetVariables, ih, List.append_assoc]

theorem mergeSelectionSets_append_for_variables (left right : List Selection)
    : mergeSelectionSets (left ++ right)
      = mergeSelectionSets left ++ mergeSelectionSets right := by
  induction left with
  | nil =>
      simp [mergeSelectionSets]
  | cons selection rest ih =>
      simp [mergeSelectionSets, ih, List.append_assoc]

theorem selectionSetVariables_mergeSelectionSets_mem_of_mem {variableName : Name}
    : ∀ selections selection,
        selection ∈ selections
        -> variableName ∈ Validation.selectionSetVariables selection.subselections
        -> variableName ∈ Validation.selectionSetVariables (mergeSelectionSets selections)
  | [], _selection, hselection, _hvariable => by
      cases hselection
  | candidate :: rest, selection, hselection, hvariable => by
      rcases List.mem_cons.mp hselection with heq | hrest
      · subst candidate
        rw [mergeSelectionSets]
        rw [selectionSetVariables_append]
        exact List.mem_append_left _ hvariable
      · rw [mergeSelectionSets]
        rw [selectionSetVariables_append]
        exact List.mem_append_right _
          (selectionSetVariables_mergeSelectionSets_mem_of_mem
            rest selection hrest hvariable)

theorem selectionSetVariables_mergeSelectionSets_exists_of_mem {variableName : Name}
    : ∀ selections,
        variableName ∈ Validation.selectionSetVariables (mergeSelectionSets selections)
        -> ∃ selection,
            selection ∈ selections
            ∧ variableName ∈ Validation.selectionSetVariables selection.subselections
  | [], hvariable => by
      simp [mergeSelectionSets, Validation.selectionSetVariables] at hvariable
  | selection :: rest, hvariable => by
      rw [mergeSelectionSets, selectionSetVariables_append] at hvariable
      rcases List.mem_append.mp hvariable with hhead | htail
      · exact ⟨selection, by simp, hhead⟩
      · rcases
          selectionSetVariables_mergeSelectionSets_exists_of_mem rest htail with
          ⟨candidate, hcandidate, hcandidateVariable⟩
        exact ⟨candidate, by simp [hcandidate], hcandidateVariable⟩

mutual
  theorem selectionContainsTypeConditionFeasibleField_of_variable
      (schema : Schema) (variableName : Name)
      (parentType : Name) (typeConditions : List Name)
      : ∀ selection,
          selectionDirectiveFree selection
          -> selectionTypeConditionFeasible schema parentType typeConditions selection
          -> variableName ∈ Validation.selectionVariables selection
          -> selectionContainsTypeConditionFeasibleField schema typeConditions selection
    | .field responseName fieldName arguments directives selectionSet,
      _hfree, hfeasible, _hvariable => by
        exact hfeasible.1
    | .inlineFragment none directives selectionSet,
      hfree, hfeasible, hvariable => by
        have hdirectives : directives = [] := hfree.1
        subst directives
        have hbodyVariable :
            variableName ∈ Validation.selectionSetVariables selectionSet := by
          simpa [Validation.selectionVariables,
            Validation.directivesVariables] using hvariable
        exact
          selectionSetContainsTypeConditionFeasibleField_of_variable
            schema variableName parentType typeConditions selectionSet
              hfree.2 hfeasible hbodyVariable
    | .inlineFragment (some typeCondition) directives selectionSet,
      hfree, hfeasible, hvariable => by
        have hdirectives : directives = [] := hfree.1
        subst directives
        have hbodyVariable :
            variableName ∈ Validation.selectionSetVariables selectionSet := by
          simpa [Validation.selectionVariables,
            Validation.directivesVariables] using hvariable
        exact
          selectionSetContainsTypeConditionFeasibleField_of_variable
            schema variableName parentType (typeCondition :: typeConditions)
              selectionSet hfree.2 hfeasible hbodyVariable

  theorem selectionSetContainsTypeConditionFeasibleField_of_variable
      (schema : Schema) (variableName : Name)
      (parentType : Name) (typeConditions : List Name)
      : ∀ selectionSet,
          selectionSetDirectiveFree selectionSet
          -> selectionSetTypeConditionFeasible schema parentType typeConditions
              selectionSet
          -> variableName ∈ Validation.selectionSetVariables selectionSet
          -> selectionSetContainsTypeConditionFeasibleField schema typeConditions
              selectionSet
    | [], _hfree, _hfeasible, hvariable => by
        simp [Validation.selectionSetVariables] at hvariable
    | selection :: rest, hfree, hfeasible, hvariable => by
        simp only [Validation.selectionSetVariables, List.mem_append] at hvariable
        rcases hvariable with hhead | htail
        · exact Or.inl
            (selectionContainsTypeConditionFeasibleField_of_variable
              schema variableName parentType typeConditions selection
                hfree.1 hfeasible.1 hhead)
        · exact Or.inr
            (selectionSetContainsTypeConditionFeasibleField_of_variable
              schema variableName parentType typeConditions rest
                hfree.2 hfeasible.2 htail)
end

theorem typesOverlapBool_true_of_feasible_cons_stack_containing_object
    (schema : Schema) {parentType typeCondition : Name}
    {typeConditions : List Name}
    : schema.objectType parentType
      -> parentType ∈ typeConditions
      -> typeConditionStackFeasible schema (typeCondition :: typeConditions)
      -> schema.typesOverlapBool parentType typeCondition = true := by
  intro hobject hparent hfeasible
  rcases hfeasible with ⟨objectType, hobjectType⟩
  have hparentType :
      objectType ∈ schema.getPossibleTypes parentType :=
    hobjectType parentType (List.mem_cons_of_mem typeCondition hparent)
  have heq : objectType = parentType :=
    object_typeIncludesObjectBool_eq_self schema hobject
      (List.contains_iff_mem.mpr hparentType)
  subst objectType
  exact typesOverlapBool_eq_true_of_typesOverlap schema
    ⟨parentType, object_typeIncludesObject_self schema hobject,
      hobjectType typeCondition (by simp)⟩

theorem fieldSelectionsWithResponseNameInScope_matching_argumentsEquivalent
    (schema : Schema) (parentType responseName fieldName : Name)
    (arguments : List Argument) (subselections rest : List Selection)
    : schema.objectType parentType
      -> selectionSetLookupValid schema parentType
          (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> FieldMerge.fieldsInSetCanMerge schema parentType
          (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> ∀ matchedFieldName matchedArguments matchedDirectives matchedSubselections,
          Selection.field responseName matchedFieldName matchedArguments
              matchedDirectives matchedSubselections
            ∈ fieldSelectionsWithResponseNameInScope schema parentType responseName rest
          -> Argument.argumentsEquivalent arguments matchedArguments := by
  intro hobject hlookupValid hmerge matchedFieldName matchedArguments
    matchedDirectives matchedSubselections hmatched
  have hheadLookup :
      selectionLookupValid schema parentType
        (Selection.field responseName fieldName arguments [] subselections) := by
    unfold selectionSetLookupValid at hlookupValid
    exact hlookupValid _ (by simp)
  simp [selectionLookupValid] at hheadLookup
  rcases hheadLookup with ⟨fieldDefinition, hlookup⟩
  let headScoped : FieldMerge.ScopedField :=
    {
      parentType := parentType,
      responseName := responseName,
      fieldName := fieldName,
      arguments := arguments,
      outputType := fieldDefinition.outputType,
      selectionSet := subselections
    }
  have hheadMem :
      headScoped ∈ FieldMerge.collectFields schema parentType
        (Selection.field responseName fieldName arguments [] subselections
          :: rest) := by
    simp [headScoped, FieldMerge.collectFields, hlookup]
  have htailLookup :
      selectionSetLookupValid schema parentType rest :=
    selectionSetLookupValid_tail hlookupValid
  rcases
    fieldSelectionsWithResponseNameInScope_field_mem_collectFields_scoped_lookupValid
      schema parentType parentType responseName rest matchedFieldName
      matchedArguments matchedDirectives matchedSubselections
      (fun hobject => object_typesOverlapBool_self schema hobject)
      htailLookup hmatched with
    ⟨matchedScoped, hmatchedMemRest, hmatchedResponse,
      _hmatchedField, hmatchedArguments, _hmatchedSelectionSet,
      hmatchedOverlap⟩
  have hmatchedMem :
      matchedScoped ∈ FieldMerge.collectFields schema parentType
        (Selection.field responseName fieldName arguments [] subselections
          :: rest) := by
    simpa [FieldMerge.collectFields, hlookup] using Or.inr hmatchedMemRest
  have hfieldMerge :
      FieldMerge.fieldsForNameCanMerge schema headScoped matchedScoped :=
    FieldMerge.fieldsInSetCanMerge_pair hmerge hheadMem hmatchedMem
      (by simpa [headScoped] using hmatchedResponse.symm)
  have hparents :
      headScoped.parentType = matchedScoped.parentType
        ∨ ¬ schema.objectType headScoped.parentType
        ∨ ¬ schema.objectType matchedScoped.parentType := by
    by_cases hmatchedObject : schema.objectType matchedScoped.parentType
    · have hoverlap := hmatchedOverlap hmatchedObject
      have hmatchedParent :
          matchedScoped.parentType = parentType :=
        object_typesOverlapBool_eq schema hobject hmatchedObject hoverlap
      exact Or.inl (by simp [headScoped, hmatchedParent])
    · exact Or.inr (Or.inr hmatchedObject)
  have hidentity :=
    FieldMerge.fieldsForNameCanMerge_identity hfieldMerge hparents
  simpa [headScoped, hmatchedArguments] using hidentity.2

theorem selectionSetVariables_partition_for_response
    (schema : Schema) (variableName : Name)
    (parentType responseName : Name) (headArguments : List Argument)
    : ∀ typeConditions selectionSet,
        schema.objectType parentType
        -> parentType ∈ typeConditions
        -> selectionSetDirectiveFree selectionSet
        -> selectionSetTypeConditionFeasible schema parentType typeConditions selectionSet
        -> (∀ fieldName arguments directives subselections,
              Selection.field responseName fieldName arguments directives subselections
                ∈ fieldSelectionsWithResponseNameInScope schema parentType
                    responseName selectionSet
              -> Argument.argumentsEquivalent headArguments arguments)
        -> variableName ∈ Validation.selectionSetVariables selectionSet
        -> variableName ∈ Validation.argumentsVariables headArguments
            ∨ variableName
              ∈ Validation.selectionSetVariables
                  (mergeSelectionSets
                    (fieldSelectionsWithResponseNameInScope schema parentType
                      responseName selectionSet))
            ∨ variableName
              ∈ Validation.selectionSetVariables
                  (withoutFieldSelectionsWithResponseName schema responseName
                    selectionSet)
  | _typeConditions, [], _hobject, _hparent, _hfree, _hfeasible,
    _harguments, hvariable => by
      simp [Validation.selectionSetVariables] at hvariable
  | typeConditions,
    Selection.field fieldResponseName fieldName arguments directives
        subselections :: rest,
    hobject, hparent, hfree, hfeasible, harguments, hvariable => by
      have hselectionFree := hfree.1
      have hdirectives : directives = [] := hselectionFree.1
      subst directives
      have htailFree := hfree.2
      have htailFeasible := hfeasible.2
      have hvariable' :
          variableName ∈ Validation.argumentsVariables arguments
          ∨ variableName ∈ Validation.selectionSetVariables subselections
          ∨ variableName ∈ Validation.selectionSetVariables rest := by
        simpa [Validation.selectionSetVariables,
          Validation.selectionVariables, Validation.directivesVariables,
          List.append_assoc] using hvariable
      by_cases hresponse : (fieldResponseName == responseName) = true
      · have hresponseEq : fieldResponseName = responseName :=
          beq_iff_eq.mp hresponse
        subst fieldResponseName
        rcases hvariable' with
          hargumentsVariable | hsubselectionsVariable | htailVariable
        · exact Or.inl
            ((Validation.argumentsVariables_mem_iff_of_equivalent
              variableName
              (harguments fieldName arguments [] subselections
                (by simp [fieldSelectionsWithResponseNameInScope]))).2
              hargumentsVariable)
        · exact Or.inr (Or.inl (by
            rw [fieldSelectionsWithResponseNameInScope]
            simp only [hresponse, if_true]
            change variableName ∈
              Validation.selectionSetVariables
                (subselections
                  ++ mergeSelectionSets
                      (fieldSelectionsWithResponseNameInScope schema parentType
                        responseName rest))
            rw [selectionSetVariables_append]
            exact List.mem_append_left _ hsubselectionsVariable))
        · have htailArguments :
              ∀ matchedFieldName matchedArguments matchedDirectives
                  matchedSubselections,
                Selection.field responseName matchedFieldName matchedArguments
                    matchedDirectives matchedSubselections
                  ∈ fieldSelectionsWithResponseNameInScope schema parentType
                      responseName rest
                -> Argument.argumentsEquivalent headArguments matchedArguments := by
            intro matchedFieldName matchedArguments matchedDirectives
              matchedSubselections hmatched
            exact harguments matchedFieldName matchedArguments matchedDirectives
              matchedSubselections
              (by
                simp [fieldSelectionsWithResponseNameInScope, hmatched])
          rcases selectionSetVariables_partition_for_response schema variableName
              parentType responseName headArguments typeConditions rest hobject
              hparent htailFree htailFeasible htailArguments htailVariable with
            hhead | hmatching | hfiltered
          · exact Or.inl hhead
          · exact Or.inr (Or.inl (by
              rw [fieldSelectionsWithResponseNameInScope]
              simp only [hresponse, if_true]
              change variableName ∈
                Validation.selectionSetVariables
                  (subselections
                    ++ mergeSelectionSets
                        (fieldSelectionsWithResponseNameInScope schema
                          parentType responseName rest))
              rw [selectionSetVariables_append]
              exact List.mem_append_right _ hmatching))
          · exact Or.inr (Or.inr (by
              simpa [withoutFieldSelectionsWithResponseName, hresponse]
                using hfiltered))
      · have hresponseFalse :
            (fieldResponseName == responseName) = false := by
          cases hmatch : fieldResponseName == responseName
          · rfl
          · contradiction
        rcases hvariable' with
          hargumentsVariable | hsubselectionsVariable | htailVariable
        · exact Or.inr (Or.inr (by
            simp [withoutFieldSelectionsWithResponseName, hresponseFalse,
              Validation.selectionSetVariables, Validation.selectionVariables,
              Validation.directivesVariables]
            exact Or.inl hargumentsVariable))
        · exact Or.inr (Or.inr (by
            simp [withoutFieldSelectionsWithResponseName, hresponseFalse,
              Validation.selectionSetVariables, Validation.selectionVariables,
              Validation.directivesVariables]
            exact Or.inr (Or.inl hsubselectionsVariable)))
        · have htailArguments :
              ∀ matchedFieldName matchedArguments matchedDirectives
                  matchedSubselections,
                Selection.field responseName matchedFieldName matchedArguments
                    matchedDirectives matchedSubselections
                  ∈ fieldSelectionsWithResponseNameInScope schema parentType
                      responseName rest
                -> Argument.argumentsEquivalent headArguments matchedArguments := by
            intro matchedFieldName matchedArguments matchedDirectives
              matchedSubselections hmatched
            exact harguments matchedFieldName matchedArguments matchedDirectives
              matchedSubselections
              (by
                simp [fieldSelectionsWithResponseNameInScope, hresponseFalse,
                  hmatched])
          rcases selectionSetVariables_partition_for_response schema variableName
              parentType responseName headArguments typeConditions rest hobject
              hparent htailFree htailFeasible htailArguments htailVariable with
            hhead | hmatching | hfiltered
          · exact Or.inl hhead
          · exact Or.inr (Or.inl (by
              simpa [fieldSelectionsWithResponseNameInScope, hresponseFalse]
                using hmatching))
          · exact Or.inr (Or.inr (by
              simp [withoutFieldSelectionsWithResponseName, hresponseFalse,
                Validation.selectionSetVariables,
                Validation.selectionVariables,
                Validation.directivesVariables]
              exact Or.inr (Or.inr hfiltered)))
  | typeConditions,
    Selection.inlineFragment typeCondition directives subselections :: rest,
    hobject, hparent, hfree, hfeasible, harguments, hvariable => by
      have hselectionFree := hfree.1
      have hdirectives : directives = [] := hselectionFree.1
      subst directives
      have hbodyFree := hselectionFree.2
      have htailFree := hfree.2
      have htailFeasible := hfeasible.2
      simp only [Validation.selectionSetVariables,
        Validation.selectionVariables, Validation.directivesVariables,
        List.nil_append, List.mem_append] at hvariable
      cases typeCondition with
      | none =>
          rcases hvariable with hbodyVariable | htailVariable
          · have hbodyArguments :
                ∀ matchedFieldName matchedArguments matchedDirectives
                    matchedSubselections,
                  Selection.field responseName matchedFieldName matchedArguments
                      matchedDirectives matchedSubselections
                    ∈ fieldSelectionsWithResponseNameInScope schema parentType
                        responseName subselections
                  -> Argument.argumentsEquivalent headArguments
                      matchedArguments := by
              intro matchedFieldName matchedArguments matchedDirectives
                matchedSubselections hmatched
              exact harguments matchedFieldName matchedArguments
                matchedDirectives matchedSubselections
                (by
                  simp [fieldSelectionsWithResponseNameInScope, hmatched])
            rcases selectionSetVariables_partition_for_response schema variableName
                parentType responseName headArguments typeConditions
                subselections hobject hparent hbodyFree hfeasible.1
                hbodyArguments hbodyVariable with hhead | hmatching | hfiltered
            · exact Or.inl hhead
            · exact Or.inr (Or.inl (by
                rw [fieldSelectionsWithResponseNameInScope,
                  mergeSelectionSets_append_for_variables,
                  selectionSetVariables_append]
                exact List.mem_append_left _ hmatching))
            · exact Or.inr (Or.inr (by
                simp [withoutFieldSelectionsWithResponseName,
                  Validation.selectionSetVariables,
                  Validation.selectionVariables,
                  Validation.directivesVariables, hfiltered]))
          · have htailArguments :
                ∀ matchedFieldName matchedArguments matchedDirectives
                    matchedSubselections,
                  Selection.field responseName matchedFieldName matchedArguments
                      matchedDirectives matchedSubselections
                    ∈ fieldSelectionsWithResponseNameInScope schema parentType
                        responseName rest
                  -> Argument.argumentsEquivalent headArguments
                      matchedArguments := by
              intro matchedFieldName matchedArguments matchedDirectives
                matchedSubselections hmatched
              exact harguments matchedFieldName matchedArguments
                matchedDirectives matchedSubselections
                (by
                  simp [fieldSelectionsWithResponseNameInScope, hmatched])
            rcases selectionSetVariables_partition_for_response schema variableName
                parentType responseName headArguments typeConditions rest hobject
                hparent htailFree htailFeasible htailArguments htailVariable with
              hhead | hmatching | hfiltered
            · exact Or.inl hhead
            · exact Or.inr (Or.inl (by
                rw [fieldSelectionsWithResponseNameInScope,
                  mergeSelectionSets_append_for_variables,
                  selectionSetVariables_append]
                exact List.mem_append_right _ hmatching))
            · exact Or.inr (Or.inr (by
                simp [withoutFieldSelectionsWithResponseName,
                  Validation.selectionSetVariables,
                  Validation.selectionVariables,
                  Validation.directivesVariables]
                exact Or.inr hfiltered))
      | some nestedType =>
          cases hoverlap : schema.typesOverlapBool parentType nestedType with
          | false =>
              have hbodyVariableFalse :
                  variableName
                    ∉ Validation.selectionSetVariables subselections := by
                intro hbodyVariable
                have hcontains :=
                  selectionSetContainsTypeConditionFeasibleField_of_variable
                    schema variableName parentType
                    (nestedType :: typeConditions) subselections hbodyFree
                    hfeasible.1 hbodyVariable
                have hstackFeasible :=
                  typeConditionStackFeasible_of_selectionSetContains_forValidity
                    schema (nestedType :: typeConditions) subselections hcontains
                have htrue :=
                  typesOverlapBool_true_of_feasible_cons_stack_containing_object
                    schema hobject hparent hstackFeasible
                rw [hoverlap] at htrue
                contradiction
              have htailVariable : variableName
                  ∈ Validation.selectionSetVariables rest :=
                hvariable.resolve_left hbodyVariableFalse
              have htailArguments :
                  ∀ matchedFieldName matchedArguments matchedDirectives
                      matchedSubselections,
                    Selection.field responseName matchedFieldName matchedArguments
                        matchedDirectives matchedSubselections
                      ∈ fieldSelectionsWithResponseNameInScope schema parentType
                          responseName rest
                    -> Argument.argumentsEquivalent headArguments
                        matchedArguments := by
                intro matchedFieldName matchedArguments matchedDirectives
                  matchedSubselections hmatched
                exact harguments matchedFieldName matchedArguments
                  matchedDirectives matchedSubselections
                  (by
                    simp [fieldSelectionsWithResponseNameInScope, hoverlap,
                      hmatched])
              rcases selectionSetVariables_partition_for_response schema
                  variableName parentType responseName headArguments
                  typeConditions rest hobject hparent htailFree htailFeasible
                  htailArguments htailVariable with
                hhead | hmatching | hfiltered
              · exact Or.inl hhead
              · exact Or.inr (Or.inl (by
                  simpa [fieldSelectionsWithResponseNameInScope, hoverlap]
                    using hmatching))
              · exact Or.inr (Or.inr (by
                  simp [withoutFieldSelectionsWithResponseName,
                    Validation.selectionSetVariables,
                    Validation.selectionVariables,
                    Validation.directivesVariables]
                  exact Or.inr hfiltered))
          | true =>
              rcases hvariable with hbodyVariable | htailVariable
              · have hbodyArguments :
                    ∀ matchedFieldName matchedArguments matchedDirectives
                        matchedSubselections,
                      Selection.field responseName matchedFieldName
                          matchedArguments matchedDirectives matchedSubselections
                        ∈ fieldSelectionsWithResponseNameInScope schema parentType
                            responseName subselections
                      -> Argument.argumentsEquivalent headArguments
                          matchedArguments := by
                  intro matchedFieldName matchedArguments matchedDirectives
                    matchedSubselections hmatched
                  exact harguments matchedFieldName matchedArguments
                    matchedDirectives matchedSubselections
                    (by
                      simp [fieldSelectionsWithResponseNameInScope, hoverlap,
                        hmatched])
                rcases selectionSetVariables_partition_for_response schema
                    variableName parentType responseName headArguments
                    (nestedType :: typeConditions) subselections hobject
                    (List.mem_cons_of_mem nestedType hparent) hbodyFree
                    hfeasible.1 hbodyArguments hbodyVariable with
                  hhead | hmatching | hfiltered
                · exact Or.inl hhead
                · exact Or.inr (Or.inl (by
                    simp only [fieldSelectionsWithResponseNameInScope,
                      hoverlap, if_true]
                    rw [
                      mergeSelectionSets_append_for_variables,
                      selectionSetVariables_append]
                    exact List.mem_append_left _ hmatching))
                · exact Or.inr (Or.inr (by
                    simp [withoutFieldSelectionsWithResponseName,
                      Validation.selectionSetVariables,
                      Validation.selectionVariables,
                      Validation.directivesVariables, hfiltered]))
              · have htailArguments :
                    ∀ matchedFieldName matchedArguments matchedDirectives
                        matchedSubselections,
                      Selection.field responseName matchedFieldName
                          matchedArguments matchedDirectives matchedSubselections
                        ∈ fieldSelectionsWithResponseNameInScope schema parentType
                            responseName rest
                      -> Argument.argumentsEquivalent headArguments
                          matchedArguments := by
                  intro matchedFieldName matchedArguments matchedDirectives
                    matchedSubselections hmatched
                  exact harguments matchedFieldName matchedArguments
                    matchedDirectives matchedSubselections
                    (by
                      simp [fieldSelectionsWithResponseNameInScope, hoverlap,
                        hmatched])
                rcases selectionSetVariables_partition_for_response schema
                    variableName parentType responseName headArguments
                    typeConditions rest hobject hparent htailFree htailFeasible
                    htailArguments htailVariable with
                  hhead | hmatching | hfiltered
                · exact Or.inl hhead
                · exact Or.inr (Or.inl (by
                    simp only [fieldSelectionsWithResponseNameInScope,
                      hoverlap, if_true]
                    rw [
                      mergeSelectionSets_append_for_variables,
                      selectionSetVariables_append]
                    exact List.mem_append_right _ hmatching))
                · exact Or.inr (Or.inr (by
                    simp [withoutFieldSelectionsWithResponseName,
                      Validation.selectionSetVariables,
                      Validation.selectionVariables,
                      Validation.directivesVariables]
                    exact Or.inr hfiltered))

theorem selectionSetVariables_possibleTypeNormalizations_of_mem
    (schema : Schema) (variableName objectType : Name)
    : ∀ possibleTypes selectionSet,
        objectType ∈ possibleTypes
        -> variableName
            ∈ Validation.selectionSetVariables
                (normalizeSelectionSet schema objectType selectionSet)
        -> variableName
            ∈ Validation.selectionSetVariables
                (possibleTypeNormalizations schema possibleTypes selectionSet)
  | [], _selectionSet, hobjectType, _hvariable => by
      cases hobjectType
  | candidate :: rest, selectionSet, hobjectType, hvariable => by
      rcases List.mem_cons.mp hobjectType with heq | hrest
      · subst candidate
        cases hnormalized :
            normalizeSelectionSet schema objectType selectionSet with
        | nil =>
            simp [hnormalized, Validation.selectionSetVariables] at hvariable
        | cons head tail =>
            simp [possibleTypeNormalizations, hnormalized,
              Validation.selectionSetVariables,
              Validation.selectionVariables,
              Validation.directivesVariables]
            have hbranch :
                variableName ∈ Validation.selectionVariables head
                  ∨ variableName
                      ∈ Validation.selectionSetVariables tail := by
              simpa [hnormalized, Validation.selectionSetVariables] using
                hvariable
            rcases hbranch with hhead | htail
            · exact Or.inl hhead
            · exact Or.inr (Or.inl htail)
      · cases hnormalized :
            normalizeSelectionSet schema candidate selectionSet with
        | nil =>
            simpa [possibleTypeNormalizations, hnormalized] using
              selectionSetVariables_possibleTypeNormalizations_of_mem
                schema variableName objectType rest selectionSet hrest hvariable
        | cons head tail =>
            simp [possibleTypeNormalizations, hnormalized,
              Validation.selectionSetVariables,
              Validation.selectionVariables,
              Validation.directivesVariables]
            exact Or.inr (Or.inr
              (selectionSetVariables_possibleTypeNormalizations_of_mem
                schema variableName objectType rest selectionSet hrest hvariable))

theorem normalizeSelectionSet_variables_mem
    (schema : Schema) (variableName : Name)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    : ∀ parentType selectionSet,
      ∀ typeConditions,
        schema.objectType parentType
        -> parentType ∈ typeConditions
        -> objectSatisfiesTypeConditionStack schema parentType typeConditions
        -> selectionSetSemanticsReady schema parentType selectionSet
        -> FieldMerge.fieldsInSetCanMerge schema parentType selectionSet
        -> selectionSetDirectiveFree selectionSet
        -> selectionSetTypeConditionFeasible schema parentType typeConditions selectionSet
        -> variableName ∈ Validation.selectionSetVariables selectionSet
        -> variableName
            ∈ Validation.selectionSetVariables
                (normalizeSelectionSet schema parentType selectionSet) := by
  intro parentType selectionSet
  induction parentType, selectionSet using normalizeSelectionSet.induct schema with
  | case1 parentType =>
      intro _typeConditions _hobject _hparent _hstack _hready
        _hmerge _hfree _hfeasible hvariable
      simp [Validation.selectionSetVariables] at hvariable
  | case2 parentType rest responseName fieldName arguments directives
      subselections hlookup _hrest =>
      intro _typeConditions _hobject _hparent _hstack hready
        _hmerge _hfree _hfeasible _hvariable
      have hlookupValid :
          selectionSetLookupValid schema parentType
            (Selection.field responseName fieldName arguments directives
              subselections :: rest) :=
        selectionSetLookupValid_of_selectionSetSemanticsReady
          (Selection.field responseName fieldName arguments directives
            subselections :: rest)
          hready
      have hheadLookup :
          selectionLookupValid schema parentType
            (Selection.field responseName fieldName arguments directives
              subselections) := by
        unfold selectionSetLookupValid at hlookupValid
        exact hlookupValid _ (by simp)
      simp [selectionLookupValid, hlookup] at hheadLookup
  | case3 parentType rest responseName fieldName arguments directives
      subselections fieldDefinition hlookup matching mergedSubselections
      returnType hrest hmerged hpossible =>
      intro typeConditions hobject hparent hstack hready hmerge
        hfree hfeasible hvariable
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
      have hrestFree : selectionSetDirectiveFree rest :=
        selectionSetDirectiveFree_tail hfree
      have htailReady :
          selectionSetSemanticsReady schema parentType rest :=
        selectionSetSemanticsReady_tail hready
      have htailMerge :
          FieldMerge.fieldsInSetCanMerge schema parentType rest :=
        fieldsInSetCanMerge_tail schema parentType
          (Selection.field responseName fieldName arguments [] subselections)
          rest hmerge
      have hfilteredReady :
          selectionSetSemanticsReady schema parentType
            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        selectionSetSemanticsReady_withoutFieldSelectionsWithResponseName schema
          responseName parentType rest htailReady
      have hfilteredMerge :
          FieldMerge.fieldsInSetCanMerge schema parentType
            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        fieldsInSetCanMerge_withoutFieldSelectionsWithResponseName schema
          responseName parentType rest htailMerge
      have hfilteredFree :
          selectionSetDirectiveFree
            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        withoutFieldSelectionsWithResponseName_directiveFree schema responseName
          rest hrestFree
      have htailFeasible :
          selectionSetTypeConditionFeasible schema parentType typeConditions
             rest :=
        selectionSetTypeConditionFeasible_tail hfeasible
      have hfilteredFeasible :
          selectionSetTypeConditionFeasible schema parentType typeConditions
            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        selectionSetTypeConditionFeasible_withoutFieldSelectionsWithResponseName
          schema responseName parentType typeConditions rest htailFeasible
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
        exact fieldSelectionsWithResponseNameInScope_directiveFree schema
          parentType responseName rest hrestFree
      have hmergedFree :
          selectionSetDirectiveFree mergedSubselections := by
        subst mergedSubselections
        exact selectionSetDirectiveFree_append hsubselectionsFree
          (selectionSetDirectiveFree_mergeSelectionSets hmatchingFree)
      have hheadFeasible :
          selectionTypeConditionFeasible schema parentType typeConditions
            (Selection.field responseName fieldName arguments []
              subselections) := by
        simpa [selectionSetTypeConditionFeasible] using hfeasible.1
      have hmergedFeasible :
          ∀ objectType,
            objectType ∈ schema.getPossibleTypes returnType ->
              selectionSetTypeConditionFeasible schema objectType [objectType]
                mergedSubselections := by
        intro objectType hobjectType
        have hheadChildFeasible :
            selectionSetTypeConditionFeasible schema objectType [objectType]
              subselections :=
          selectionTypeConditionFeasible_field_child_branch_forObject
            schema hheadFeasible hstack hlookup
            (by simpa [returnType] using hobjectType)
        have hmatchingChildFeasible :
            selectionSetTypeConditionFeasible schema objectType [objectType]
              (mergeSelectionSets matching) := by
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
              schema parentType responseName hobject hstack rest htailFeasible
              fieldName matchedArguments matchedDirectives matchedSubselections
              fieldDefinition objectType hmatched hlookup
              (by simpa [returnType] using hobjectType)
        subst mergedSubselections
        exact selectionSetTypeConditionFeasible_append hheadChildFeasible
          hmatchingChildFeasible
      have hmatchingArguments :
          ∀ matchedFieldName matchedArguments matchedDirectives
              matchedSubselections,
            Selection.field responseName matchedFieldName matchedArguments
                matchedDirectives matchedSubselections
              ∈ fieldSelectionsWithResponseNameInScope schema parentType
                  responseName rest
            -> Argument.argumentsEquivalent arguments matchedArguments :=
        fieldSelectionsWithResponseNameInScope_matching_argumentsEquivalent
          schema parentType responseName fieldName arguments subselections rest
          hobject hlookupValid hmerge
      have hsourceVariable :
          variableName ∈ Validation.argumentsVariables arguments
            ∨ variableName
                ∈ Validation.selectionSetVariables mergedSubselections
            ∨ variableName
                ∈ Validation.selectionSetVariables
                    (withoutFieldSelectionsWithResponseName schema responseName
                      rest) := by
        have hsourceParts :
            variableName ∈ Validation.argumentsVariables arguments
              ∨ variableName
                  ∈ Validation.selectionSetVariables subselections
              ∨ variableName
                  ∈ Validation.selectionSetVariables rest := by
          simpa [Validation.selectionSetVariables,
            Validation.selectionVariables, Validation.directivesVariables,
            List.append_assoc] using hvariable
        rcases hsourceParts with harguments | hsubselections | hrestVariable
        · exact Or.inl harguments
        · exact Or.inr (Or.inl (by
            subst mergedSubselections
            rw [selectionSetVariables_append]
            exact List.mem_append_left _ hsubselections))
        · rcases
            selectionSetVariables_partition_for_response schema variableName
              parentType responseName arguments typeConditions rest hobject
              hparent hrestFree htailFeasible hmatchingArguments hrestVariable
            with harguments | hmatching | hfiltered
          · exact Or.inl harguments
          · exact Or.inr (Or.inl (by
              subst mergedSubselections
              rw [selectionSetVariables_append]
              exact List.mem_append_right _ hmatching))
          · exact Or.inr (Or.inr hfiltered)
      have hchildVariable :
          ∀ objectType,
            objectType ∈ schema.getPossibleTypes returnType
            -> schema.objectType objectType
            -> variableName
                ∈ Validation.selectionSetVariables mergedSubselections
            -> variableName
                ∈ Validation.selectionSetVariables
                    (normalizeSelectionSet schema objectType
                      mergedSubselections) := by
        intro objectType hobjectType hobjectBranch hmergedVariable
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
        have hchildMerge :
            FieldMerge.fieldsInSetCanMerge schema objectType
              mergedSubselections :=
          fieldsInSetCanMerge_fieldHead_merged_of_canMerge_object_lookupValid
            schema parentType responseName fieldName objectType arguments
            subselections rest fieldDefinition hobject hlookupValid hmerge
            hlookup
        exact hpossible objectType [objectType] hobjectBranch (by simp)
          (objectSatisfiesTypeConditionStack_singleton_of_object_forValidity
            schema hobjectBranch)
          hchildReady hchildMerge hmergedFree
          (hmergedFeasible objectType hobjectType) hmergedVariable
      have hnormalizedChildVariable :
          variableName ∈ Validation.selectionSetVariables mergedSubselections
          -> variableName
              ∈ Validation.selectionSetVariables normalizedSubselections := by
        intro hmergedVariable
        subst normalizedSubselections
        by_cases hreturnObject : objectTypeNameBool schema returnType = true
        · have hreturnObjectType :
              schema.objectType returnType :=
            objectType_of_objectTypeNameBool_eq_true schema hreturnObject
          have hreturnType :
              returnType ∈ schema.getPossibleTypes returnType :=
            List.contains_iff_mem.mp
              (object_typeIncludesObjectBool_self schema hreturnObjectType)
          simpa [hreturnObject] using
            hchildVariable returnType hreturnType hreturnObjectType
              hmergedVariable
        · have hreturnObjectFalse :
              objectTypeNameBool schema returnType = false := by
            cases hmatch : objectTypeNameBool schema returnType
            · rfl
            · contradiction
          have hpossibleTypesNonempty :
              schema.getPossibleTypes returnType ≠ [] := by
            cases subselections with
            | cons child children =>
                have hchildFeasible := hheadFeasible.2
                rw [hlookup] at hchildFeasible
                simpa [returnType] using hchildFeasible.1
            | nil =>
                have hmatchingVariable :
                    variableName
                      ∈ Validation.selectionSetVariables
                          (mergeSelectionSets matching) := by
                  subst mergedSubselections
                  simpa [selectionSetVariables_append,
                    Validation.selectionSetVariables] using hmergedVariable
                rcases
                    selectionSetVariables_mergeSelectionSets_exists_of_mem
                      matching hmatchingVariable with
                  ⟨matchedSelection, hmatched, hmatchedVariable⟩
                subst matching
                rcases
                    fieldSelectionsWithResponseNameInScope_mem_field schema
                      parentType responseName rest matchedSelection hmatched with
                  ⟨matchedFieldName, matchedArguments, matchedDirectives,
                    matchedSubselections, hmatchedShape⟩
                subst matchedSelection
                have hsame :
                    matchedFieldName = fieldName :=
                  fieldSelectionsWithResponseNameInScope_matching_same_field_of_canMerge_object_lookupValid
                    schema parentType responseName fieldName arguments [] rest
                    hobject hlookupValid hmerge matchedFieldName
                    matchedArguments matchedDirectives matchedSubselections
                    hmatched
                subst matchedFieldName
                have hmatchedSubselectionsNonempty :
                    matchedSubselections ≠ [] := by
                  intro hnil
                  subst matchedSubselections
                  exact List.not_mem_nil hmatchedVariable
                simpa [returnType] using
                  fieldSelectionsWithResponseNameInScope_field_child_possibleTypes_nonempty
                    schema parentType responseName rest htailFeasible fieldName
                    matchedArguments matchedDirectives matchedSubselections
                    fieldDefinition hmatched hlookup
                    hmatchedSubselectionsNonempty
          rcases List.exists_mem_of_ne_nil _ hpossibleTypesNonempty with
            ⟨objectType, hobjectType⟩
          have hobjectBranch :
              schema.objectType objectType :=
            SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
              hschema returnType objectType hobjectType
          simpa [hreturnObjectFalse] using
            selectionSetVariables_possibleTypeNormalizations_of_mem
              schema variableName objectType
              (schema.getPossibleTypes returnType) mergedSubselections
              hobjectType
              (hchildVariable objectType hobjectType hobjectBranch
                hmergedVariable)
      rw [normalizeSelectionSet.eq_2, hlookup]
      change variableName
        ∈ Validation.selectionSetVariables
            (Selection.field responseName fieldName arguments []
                normalizedSubselections
              :: normalizeSelectionSet schema parentType
                (withoutFieldSelectionsWithResponseName schema responseName
                  rest))
      simp [Validation.selectionSetVariables,
        Validation.selectionVariables, Validation.directivesVariables,
        List.mem_append]
      rcases hsourceVariable with harguments | hmergedVariable | hfiltered
      · exact Or.inl harguments
      · exact Or.inr (Or.inl
          (hnormalizedChildVariable hmergedVariable))
      · exact Or.inr (Or.inr
          (hrest typeConditions hobject hparent hstack hfilteredReady
            hfilteredMerge hfilteredFree hfilteredFeasible hfiltered))
  | case4 parentType rest directives subselections happend =>
      intro typeConditions hobject hparent hstack hready hmerge
        hfree hfeasible hvariable
      have hselectionFree := selectionSetDirectiveFree_head hfree
      have hdirectives : directives = [] := hselectionFree.1
      subst directives
      have hrestFree := selectionSetDirectiveFree_tail hfree
      have hbodyReady :
          selectionSetSemanticsReady schema parentType subselections := by
        have hhead :
            selectionSemanticsReady schema parentType
              (Selection.inlineFragment none [] subselections) := by
          unfold selectionSetSemanticsReady at hready
          exact hready _ (by simp)
        simpa [selectionSemanticsReady] using hhead
      have htailReady := selectionSetSemanticsReady_tail hready
      have hbodyTailReady :
          selectionSetSemanticsReady schema parentType
            (subselections ++ rest) :=
        selectionSetSemanticsReady_append hbodyReady htailReady
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
             subselections := by
        simpa [selectionSetTypeConditionFeasible,
          selectionTypeConditionFeasible] using hfeasible.1
      have htailFeasible :
          selectionSetTypeConditionFeasible schema parentType typeConditions
             rest :=
        selectionSetTypeConditionFeasible_tail hfeasible
      have hbodyTailFeasible :
          selectionSetTypeConditionFeasible schema parentType typeConditions
            (subselections ++ rest) :=
        selectionSetTypeConditionFeasible_append hbodyFeasible htailFeasible
      have hbodyTailVariable :
          variableName
            ∈ Validation.selectionSetVariables (subselections ++ rest) := by
        rw [selectionSetVariables_append]
        simpa [Validation.selectionSetVariables,
          Validation.selectionVariables, Validation.directivesVariables] using
          hvariable
      simpa [normalizeSelectionSet] using
        happend typeConditions hobject hparent hstack hbodyTailReady
          hbodyTailMerge hbodyTailFree hbodyTailFeasible hbodyTailVariable
  | case5 parentType rest typeCondition directives subselections hoverlap
      _hrest happend =>
      intro typeConditions hobject hparent hstack hready hmerge
        hfree hfeasible hvariable
      have hselectionFree := selectionSetDirectiveFree_head hfree
      have hdirectives : directives = [] := hselectionFree.1
      subst directives
      have hrestFree := selectionSetDirectiveFree_tail hfree
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
      have htailReady := selectionSetSemanticsReady_tail hready
      have hbodyTailReady :
          selectionSetSemanticsReady schema parentType
            (subselections ++ rest) :=
        selectionSetSemanticsReady_append hbodyReady htailReady
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
            (typeCondition :: typeConditions) subselections := by
        simpa [selectionSetTypeConditionFeasible,
          selectionTypeConditionFeasible] using hfeasible.1
      have htailFeasible :
          selectionSetTypeConditionFeasible schema parentType typeConditions
             rest :=
        selectionSetTypeConditionFeasible_tail hfeasible
      have hbodyFeasibleInOuterStack :
          selectionSetTypeConditionFeasible schema parentType typeConditions
             subselections :=
        selectionSetTypeConditionFeasible_of_stack_subset schema
          (fun candidate hcandidate =>
            List.mem_cons_of_mem typeCondition hcandidate)
          subselections hbodyFeasible
      have hbodyTailFeasible :
          selectionSetTypeConditionFeasible schema parentType typeConditions
            (subselections ++ rest) :=
        selectionSetTypeConditionFeasible_append hbodyFeasibleInOuterStack
          htailFeasible
      have hbodyTailVariable :
          variableName
            ∈ Validation.selectionSetVariables (subselections ++ rest) := by
        rw [selectionSetVariables_append]
        simpa [Validation.selectionSetVariables,
          Validation.selectionVariables, Validation.directivesVariables] using
          hvariable
      simpa [normalizeSelectionSet, hoverlap] using
        happend typeConditions hobject hparent hstack hbodyTailReady
          hbodyTailMerge hbodyTailFree hbodyTailFeasible hbodyTailVariable
  | case6 parentType rest typeCondition directives subselections hoverlap
      hrest =>
      intro typeConditions hobject hparent hstack hready hmerge
        hfree hfeasible hvariable
      have hselectionFree := selectionSetDirectiveFree_head hfree
      have hdirectives : directives = [] := hselectionFree.1
      subst directives
      have htailReady := selectionSetSemanticsReady_tail hready
      have htailMerge :
          FieldMerge.fieldsInSetCanMerge schema parentType rest :=
        fieldsInSetCanMerge_tail schema parentType
          (Selection.inlineFragment (some typeCondition) [] subselections)
          rest hmerge
      have htailFree := selectionSetDirectiveFree_tail hfree
      have htailFeasible :
          selectionSetTypeConditionFeasible schema parentType typeConditions
             rest :=
        selectionSetTypeConditionFeasible_tail hfeasible
      have hbodyFree := hselectionFree.2
      have hbodyFeasible :
          selectionSetTypeConditionFeasible schema parentType
            (typeCondition :: typeConditions) subselections := by
        simpa [selectionSetTypeConditionFeasible,
          selectionTypeConditionFeasible] using hfeasible.1
      have hparts :
          variableName ∈ Validation.selectionSetVariables subselections
            ∨ variableName ∈ Validation.selectionSetVariables rest := by
        simpa [Validation.selectionSetVariables,
          Validation.selectionVariables, Validation.directivesVariables] using
          hvariable
      have hfalse :
          schema.typesOverlapBool parentType typeCondition = false := by
        cases hmatch : schema.typesOverlapBool parentType typeCondition
        · rfl
        · contradiction
      have hbodyVariableFalse :
          variableName ∉ Validation.selectionSetVariables subselections := by
        intro hbodyVariable
        have hcontains :=
          selectionSetContainsTypeConditionFeasibleField_of_variable
            schema variableName parentType (typeCondition :: typeConditions)
            subselections hbodyFree hbodyFeasible hbodyVariable
        have hstackFeasible :=
          typeConditionStackFeasible_of_selectionSetContains_forValidity
            schema (typeCondition :: typeConditions) subselections hcontains
        have htrue :=
          typesOverlapBool_true_of_feasible_cons_stack_containing_object
            schema hobject hparent hstackFeasible
        rw [hfalse] at htrue
        contradiction
      have htailVariable : variableName
          ∈ Validation.selectionSetVariables rest :=
        hparts.resolve_left hbodyVariableFalse
      simpa [normalizeSelectionSet, hfalse] using
        hrest typeConditions hobject hparent hstack htailReady
          htailMerge htailFree htailFeasible htailVariable

end GroundTypeNormalization

end NormalForm

end GraphQL
