import Proofs.GraphQL.Theories.ExecutionReadiness
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.ArgumentNodup
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Validity

/-!
Argument-coercion readiness is reflected by ground-type normalization.

The reverse direction is the one needed by uniqueness: a normalized field group keeps
one validated representative, so readiness of that representative must be transferred
back to every syntactically equivalent source occurrence in the group.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

private theorem selectionSet_size_tail_lt_cons_for_readiness
    (selection : Selection) (rest : List Selection)
    : SelectionSet.size rest < SelectionSet.size (selection :: rest) := by
  cases selection <;> simp [SelectionSet.size, Selection.size]
  all_goals omega

private theorem selectionSet_size_child_lt_cons_inline_for_readiness
    (typeCondition : Option Name) (directives : List DirectiveApplication)
    (children rest : List Selection)
    : SelectionSet.size children
      < SelectionSet.size
          (Selection.inlineFragment typeCondition directives children :: rest) := by
  simp [SelectionSet.size, Selection.size]
  omega

private theorem selectionDirectiveFree_of_mem_for_readiness
    {selection : Selection} {selectionSet : List Selection}
    (hfree : selectionSetDirectiveFree selectionSet)
    (hmem : selection ∈ selectionSet)
    : selectionDirectiveFree selection := by
  induction selectionSet with
  | nil => simp at hmem
  | cons head rest ih =>
      rcases List.mem_cons.mp hmem with rfl | htail
      · exact hfree.1
      · exact ih hfree.2 htail

mutual
  def allFieldsWithResponseName (responseName : Name) : List Selection -> List Selection
    | [] => []
    | selection :: rest =>
        match selection with
        | field@(.field candidate _fieldName _arguments _directives _children) =>
            if candidate == responseName then
              field :: allFieldsWithResponseName responseName rest
            else
              allFieldsWithResponseName responseName rest
        | .inlineFragment _typeCondition _directives children =>
            allFieldsWithResponseName responseName children
            ++ allFieldsWithResponseName responseName rest
end

mutual
  def selectionRemovedResponseReady
      (schema : Schema) (variableValues : Execution.VariableValues)
      (parentType responseName : Name)
      : Selection -> Prop
    | selection@(.field candidate _fieldName _arguments _directives _children) =>
        if candidate == responseName then
          selectionArgumentsCoercible schema variableValues parentType selection
        else
          True
    | .inlineFragment _typeCondition _directives children =>
        selectionSetRemovedResponseReady schema variableValues parentType responseName
          children

  def selectionSetRemovedResponseReady
      (schema : Schema) (variableValues : Execution.VariableValues)
      (parentType responseName : Name)
      : List Selection -> Prop
    | [] => True
    | selection :: rest =>
        selectionRemovedResponseReady schema variableValues parentType responseName
          selection
        ∧ selectionSetRemovedResponseReady schema variableValues parentType
            responseName rest
end

theorem selectionSetRemovedResponseReady_of_all_fields
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType responseName : Name)
    : ∀ selectionSet,
        (∀ field,
          field ∈ allFieldsWithResponseName responseName selectionSet
          -> selectionArgumentsCoercible schema variableValues parentType field)
        -> selectionSetRemovedResponseReady schema variableValues parentType responseName
            selectionSet
  | [], _hfields => by
      simp [selectionSetRemovedResponseReady]
  | selection :: rest, hfields => by
      constructor
      · cases selection with
        | field candidate fieldName arguments directives children =>
            by_cases hname : (candidate == responseName) = true
            · simpa [selectionRemovedResponseReady, hname] using
                hfields (.field candidate fieldName arguments directives children)
                  (by simp [allFieldsWithResponseName, hname])
            · have hnameFalse : (candidate == responseName) = false := by
                cases hmatch : candidate == responseName
                · rfl
                · contradiction
              simp [selectionRemovedResponseReady, hnameFalse]
        | inlineFragment typeCondition directives children =>
            apply selectionSetRemovedResponseReady_of_all_fields schema variableValues
              parentType responseName children
            intro field hfield
            exact hfields field (by
              simp [allFieldsWithResponseName]
              exact Or.inl hfield)
      · apply selectionSetRemovedResponseReady_of_all_fields schema variableValues
          parentType responseName rest
        intro field hfield
        cases selection with
        | field candidate fieldName arguments directives children =>
            by_cases hname : (candidate == responseName) = true
            · exact hfields field (by
                simp [allFieldsWithResponseName, hname, hfield])
            · have hnameFalse : (candidate == responseName) = false := by
                cases hmatch : candidate == responseName
                · rfl
                · contradiction
              exact hfields field (by
                simpa [allFieldsWithResponseName, hnameFalse] using hfield)
        | inlineFragment typeCondition directives children =>
            exact hfields field (by
              simp [allFieldsWithResponseName]
              exact Or.inr hfield)

theorem allFieldsWithResponseName_mem_stack_feasible
    (schema : Schema) (responseName : Name)
    : ∀ parentType typeConditions selectionSet field,
        selectionSetTypeConditionFeasible schema parentType typeConditions selectionSet
        -> field ∈ allFieldsWithResponseName responseName selectionSet
        -> typeConditionStackFeasible schema typeConditions := by
  intro parentType typeConditions selectionSet
  cases selectionSet with
  | nil =>
      intro field _hfeasible hmem
      simp [allFieldsWithResponseName] at hmem
  | cons selection rest =>
      intro field hfeasible hmem
      rcases hfeasible with ⟨hheadFeasible, hrestFeasible⟩
      cases selection with
      | field candidate fieldName arguments directives children =>
          by_cases hname : (candidate == responseName) = true
          · simp [allFieldsWithResponseName, hname] at hmem
            rcases hmem with rfl | htail
            · simpa [selectionTypeConditionFeasible] using hheadFeasible.1
            · exact allFieldsWithResponseName_mem_stack_feasible schema
                responseName parentType typeConditions rest field hrestFeasible htail
          · have hnameFalse : (candidate == responseName) = false := by
              cases hmatch : candidate == responseName
              · rfl
              · contradiction
            simp [allFieldsWithResponseName, hnameFalse] at hmem
            exact allFieldsWithResponseName_mem_stack_feasible schema responseName
              parentType typeConditions rest field hrestFeasible hmem
      | inlineFragment typeCondition directives children =>
          simp [allFieldsWithResponseName] at hmem
          rcases hmem with hchild | htail
          · cases typeCondition with
            | none =>
                exact allFieldsWithResponseName_mem_stack_feasible schema responseName
                  parentType typeConditions children field hheadFeasible hchild
            | some typeCondition =>
                exact typeConditionStackFeasible_of_subset_forValidity
                  (allFieldsWithResponseName_mem_stack_feasible schema responseName
                    parentType (typeCondition :: typeConditions) children field
                    hheadFeasible hchild)
                  (fun candidate hcandidate =>
                    List.mem_cons_of_mem typeCondition hcandidate)
          · exact allFieldsWithResponseName_mem_stack_feasible schema responseName
              parentType typeConditions rest field hrestFeasible htail
termination_by _parentType _typeConditions selectionSet =>
  SelectionSet.size selectionSet
decreasing_by
  all_goals
    simp [SelectionSet.size, Selection.size]
    omega

theorem allFieldsWithResponseName_mem_scoped (schema : Schema) (responseName : Name)
    : ∀ parentType typeConditions selectionSet field,
        schema.objectType parentType
        -> parentType ∈ typeConditions
        -> selectionSetTypeConditionFeasible schema parentType typeConditions selectionSet
        -> field ∈ allFieldsWithResponseName responseName selectionSet
        -> field
            ∈ fieldSelectionsWithResponseNameInScope schema parentType responseName
                selectionSet := by
  intro parentType typeConditions selectionSet
  cases selectionSet with
  | nil =>
      intro field _hobject _hparent _hfeasible hmem
      simp [allFieldsWithResponseName] at hmem
  | cons selection rest =>
      intro field hobject hparent hfeasible hmem
      rcases hfeasible with ⟨hheadFeasible, hrestFeasible⟩
      cases selection with
      | field candidate fieldName arguments directives children =>
          by_cases hname : (candidate == responseName) = true
          · simp [allFieldsWithResponseName, hname] at hmem
            rcases hmem with rfl | htail
            · simp [fieldSelectionsWithResponseNameInScope, hname]
            · simp [fieldSelectionsWithResponseNameInScope, hname]
              exact Or.inr
                (allFieldsWithResponseName_mem_scoped schema responseName parentType
                  typeConditions rest field hobject hparent hrestFeasible htail)
          · have hnameFalse : (candidate == responseName) = false := by
              cases hmatch : candidate == responseName
              · rfl
              · contradiction
            simp [allFieldsWithResponseName, hnameFalse] at hmem
            simpa [fieldSelectionsWithResponseNameInScope, hnameFalse] using
              allFieldsWithResponseName_mem_scoped schema responseName parentType
                typeConditions rest field hobject hparent hrestFeasible hmem
      | inlineFragment typeCondition directives children =>
          simp [allFieldsWithResponseName] at hmem
          rcases hmem with hchild | htail
          · cases typeCondition with
            | none =>
                simp [fieldSelectionsWithResponseNameInScope]
                exact Or.inl
                  (allFieldsWithResponseName_mem_scoped schema responseName
                    parentType typeConditions children field hobject hparent
                    hheadFeasible hchild)
            | some typeCondition =>
                have hstack :
                    typeConditionStackFeasible schema
                      (typeCondition :: typeConditions) :=
                  allFieldsWithResponseName_mem_stack_feasible schema responseName
                    parentType (typeCondition :: typeConditions) children field
                    hheadFeasible hchild
                have hoverlap :
                    schema.typesOverlapBool parentType typeCondition = true :=
                  typesOverlapBool_true_of_feasible_cons_stack_containing_object
                    schema hobject hparent hstack
                have hparentCondition :
                    parentType ∈ schema.getPossibleTypes typeCondition :=
                  List.contains_iff_mem.mp
                    (typeIncludesObjectBool_of_object_typesOverlapBool schema hobject
                      hoverlap)
                simp [fieldSelectionsWithResponseNameInScope, hoverlap]
                exact Or.inl
                  (allFieldsWithResponseName_mem_scoped schema responseName
                    parentType (typeCondition :: typeConditions) children field
                    hobject (by simp [hparent]) hheadFeasible hchild)
          · cases typeCondition with
            | none =>
                simp [fieldSelectionsWithResponseNameInScope]
                exact Or.inr
                  (allFieldsWithResponseName_mem_scoped schema responseName parentType
                    typeConditions rest field hobject hparent hrestFeasible htail)
            | some typeCondition =>
                by_cases hoverlap :
                    schema.typesOverlapBool parentType typeCondition = true
                · simp [fieldSelectionsWithResponseNameInScope, hoverlap]
                  exact Or.inr
                    (allFieldsWithResponseName_mem_scoped schema responseName parentType
                      typeConditions rest field hobject hparent hrestFeasible htail)
                · have hoverlapFalse :
                      schema.typesOverlapBool parentType typeCondition = false := by
                    cases hmatch : schema.typesOverlapBool parentType typeCondition
                    · rfl
                    · contradiction
                  simpa [fieldSelectionsWithResponseNameInScope, hoverlapFalse] using
                    allFieldsWithResponseName_mem_scoped schema responseName parentType
                      typeConditions rest field hobject hparent hrestFeasible htail
termination_by _parentType _typeConditions selectionSet =>
  SelectionSet.size selectionSet
decreasing_by
  all_goals
    simp [SelectionSet.size, Selection.size]
    omega

theorem allFieldsWithResponseName_mem_field (responseName : Name)
    : ∀ selectionSet field,
        field ∈ allFieldsWithResponseName responseName selectionSet
        -> ∃ fieldName arguments directives children,
            field
            = Selection.field responseName fieldName arguments directives children := by
  intro selectionSet
  cases selectionSet with
  | nil =>
      intro field hmem
      simp [allFieldsWithResponseName] at hmem
  | cons selection rest =>
      intro field hmem
      cases selection with
      | field candidate fieldName arguments directives children =>
          by_cases hname : (candidate == responseName) = true
          · have heq : candidate = responseName := beq_iff_eq.mp hname
            subst candidate
            simp [allFieldsWithResponseName] at hmem
            rcases hmem with rfl | htail
            · exact ⟨fieldName, arguments, directives, children, rfl⟩
            · exact allFieldsWithResponseName_mem_field responseName rest field htail
          · have hnameFalse : (candidate == responseName) = false := by
              cases hmatch : candidate == responseName
              · rfl
              · contradiction
            simp [allFieldsWithResponseName, hnameFalse] at hmem
            exact allFieldsWithResponseName_mem_field responseName rest field hmem
      | inlineFragment typeCondition directives children =>
          simp [allFieldsWithResponseName] at hmem
          rcases hmem with hchild | htail
          · exact allFieldsWithResponseName_mem_field responseName children field
              hchild
          · exact allFieldsWithResponseName_mem_field responseName rest field htail
termination_by selectionSet => SelectionSet.size selectionSet
decreasing_by
  all_goals
    simp [SelectionSet.size, Selection.size]
    omega

private theorem subselections_mem_mergeSelectionSets_of_mem
    {field : Selection} {fieldSelections : List Selection}
    (hfield : field ∈ fieldSelections)
    : ∀ selection,
        selection ∈ field.subselections
        -> selection ∈ mergeSelectionSets fieldSelections := by
  induction fieldSelections with
  | nil => simp at hfield
  | cons head rest ih =>
      rcases List.mem_cons.mp hfield with rfl | htail
      · intro selection hselection
        simp [mergeSelectionSets, hselection]
      · intro selection hselection
        simp [mergeSelectionSets]
        exact Or.inr (ih htail selection hselection)

theorem selectionSetArgumentsCoercible_mergeSelectionSets_of_mem
    {schema : Schema} {variableValues : Execution.VariableValues}
    {parentType : Name} {selectionSet fieldSelections : List Selection}
    {field : Selection}
    (hready
      : selectionSetArgumentsCoercible schema variableValues parentType
          (mergeSelectionSets fieldSelections))
    (hfield : field ∈ fieldSelections)
    (hselectionSet : field.subselections = selectionSet)
    : selectionSetArgumentsCoercible schema variableValues parentType selectionSet := by
  apply selectionSetArgumentsCoercible_of_subset hready
  intro selection hselection
  exact subselections_mem_mergeSelectionSets_of_mem hfield selection
    (by simpa [hselectionSet] using hselection)

theorem selectionSetArgumentsCoercible_possibleTypeNormalizations_branch
    (schema : Schema) (variableValues : Execution.VariableValues)
    (runtimeType : Name)
    : ∀ possibleTypes selectionSet,
        schema.objectType runtimeType
        -> runtimeType ∈ possibleTypes
        -> normalizeSelectionSet schema runtimeType selectionSet ≠ []
        -> selectionSetArgumentsCoercible schema variableValues runtimeType
            (possibleTypeNormalizations schema possibleTypes selectionSet)
        -> selectionSetArgumentsCoercible schema variableValues runtimeType
            (normalizeSelectionSet schema runtimeType selectionSet)
  | [], _selectionSet, _hobject, hmem, _hnonempty, _hready => by
      cases hmem
  | candidate :: rest, selectionSet, hobject, hmem, hnonempty, hready => by
      rcases List.mem_cons.mp hmem with rfl | htail
      · cases hnormalized : normalizeSelectionSet schema runtimeType selectionSet with
        | nil => exact False.elim (hnonempty hnormalized)
        | cons head tail =>
            have hparts :
                selectionArgumentsCoercible schema variableValues runtimeType
                    (.inlineFragment (some runtimeType) [] (head :: tail))
                  ∧ selectionSetArgumentsCoercible schema variableValues runtimeType
                      (possibleTypeNormalizations schema rest selectionSet) := by
              simpa [possibleTypeNormalizations, hnormalized,
                selectionSetArgumentsCoercible] using hready
            have hheadReady := hparts.1
            exact hheadReady (by simp [Execution.selectionDirectivesAllowBool])
              (object_typeIncludesObjectBool_self schema hobject)
      · cases hnormalized : normalizeSelectionSet schema candidate selectionSet with
        | nil =>
            have htailReady :
                selectionSetArgumentsCoercible schema variableValues runtimeType
                  (possibleTypeNormalizations schema rest selectionSet) := by
              simpa [possibleTypeNormalizations, hnormalized] using hready
            exact selectionSetArgumentsCoercible_possibleTypeNormalizations_branch
              schema variableValues runtimeType rest selectionSet hobject htail
              hnonempty htailReady
        | cons head tail =>
            have hparts :
                selectionArgumentsCoercible schema variableValues runtimeType
                    (.inlineFragment (some candidate) [] (head :: tail))
                  ∧ selectionSetArgumentsCoercible schema variableValues runtimeType
                      (possibleTypeNormalizations schema rest selectionSet) := by
              simpa [possibleTypeNormalizations, hnormalized,
                selectionSetArgumentsCoercible] using hready
            exact selectionSetArgumentsCoercible_possibleTypeNormalizations_branch
              schema variableValues runtimeType rest selectionSet hobject htail
              hnonempty hparts.2

theorem selectionSetArgumentsCoercible_of_no_feasible_field
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name)
    : ∀ typeConditions selectionSet,
        selectionSetTypeConditionFeasible schema parentType typeConditions selectionSet
        -> ¬ selectionSetContainsTypeConditionFeasibleField schema typeConditions
              selectionSet
        -> selectionSetArgumentsCoercible schema variableValues parentType selectionSet
  | _typeConditions, [], _hfeasible, _hcontains => by
      simp [selectionSetArgumentsCoercible]
  | typeConditions, selection :: rest, hfeasible, hcontains => by
      rcases hfeasible with ⟨hheadFeasible, hrestFeasible⟩
      have hheadNot :
          ¬ selectionContainsTypeConditionFeasibleField schema typeConditions
            selection := fun hhead => hcontains (Or.inl hhead)
      have hrestNot :
          ¬ selectionSetContainsTypeConditionFeasibleField schema typeConditions rest :=
        fun hrest => hcontains (Or.inr hrest)
      constructor
      · cases selection with
        | field responseName fieldName arguments directives children =>
            exact False.elim (hheadNot (by
              simpa [selectionContainsTypeConditionFeasibleField,
                selectionTypeConditionFeasible] using hheadFeasible.1))
        | inlineFragment typeCondition directives children =>
            cases typeCondition with
            | none =>
                intro _hdirectives _htypeCondition
                exact selectionSetArgumentsCoercible_of_no_feasible_field schema
                  variableValues parentType typeConditions children hheadFeasible
                  hheadNot
            | some typeCondition =>
                intro _hdirectives _htypeCondition
                exact selectionSetArgumentsCoercible_of_no_feasible_field schema
                  variableValues parentType (typeCondition :: typeConditions)
                  children hheadFeasible hheadNot
      · exact selectionSetArgumentsCoercible_of_no_feasible_field schema
          variableValues parentType typeConditions rest hrestFeasible hrestNot

private theorem selectionSetRemovedResponseReady_of_merged_group
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
    (himplementation
      : Validation.selectionSetValidInPossibleTypes schema variableDefinitions parentType
          (Selection.field responseName fieldName arguments [] subselections :: rest))
    (hmerge
      : FieldMerge.fieldsInSetCanMerge schema parentType
          (Selection.field responseName fieldName arguments [] subselections :: rest))
    (hfeasible
      : selectionSetTypeConditionFeasible schema parentType typeConditions
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
                    (fieldSelectionsWithResponseNameInScope schema parentType responseName
                      rest)))
    : selectionSetRemovedResponseReady schema variableValues parentType responseName
        rest := by
  apply selectionSetRemovedResponseReady_of_all_fields schema variableValues
    parentType responseName rest
  intro field hfield
  rcases allFieldsWithResponseName_mem_field responseName rest field hfield with
    ⟨matchedFieldName, matchedArguments, matchedDirectives, matchedSubselections,
      rfl⟩
  have hscoped :
      Selection.field responseName matchedFieldName matchedArguments
          matchedDirectives matchedSubselections
        ∈ fieldSelectionsWithResponseNameInScope schema parentType responseName rest :=
    allFieldsWithResponseName_mem_scoped schema responseName parentType
      typeConditions rest _ hobject hparent hfeasible.2 hfield
  have hsameField : matchedFieldName = fieldName :=
    fieldSelectionsWithResponseNameInScope_matching_same_field_of_canMerge_object_lookupValid
      schema parentType responseName fieldName arguments subselections rest hobject
      hlookupValid hmerge matchedFieldName matchedArguments matchedDirectives
      matchedSubselections hscoped
  have hargumentsEquivalent :
      Argument.argumentsEquivalent arguments matchedArguments :=
    fieldSelectionsWithResponseNameInScope_matching_argumentsEquivalent schema
      parentType responseName fieldName arguments subselections rest hobject
      hlookupValid hmerge matchedFieldName matchedArguments matchedDirectives
      matchedSubselections hscoped
  have hheadImplementation :=
    selectionSetValidInPossibleTypes_head himplementation
  have hheadNodup : (arguments.map Argument.name).Nodup := by
    have hnodup :=
      Execution.selectionArgumentsNodup_of_selectionValid hheadImplementation.1
    simpa [Execution.selectionArgumentsNodup] using hnodup.1
  have hmatchedImplementation :=
    fieldSelectionsWithResponseNameInScope_field_validInPossibleTypes schema
      variableDefinitions parentType responseName hobject rest
      (selectionSetValidInPossibleTypes_tail himplementation) matchedFieldName
      matchedArguments matchedDirectives matchedSubselections hscoped
  have hmatchedNodup : (matchedArguments.map Argument.name).Nodup := by
    have hnodup :=
      Execution.selectionArgumentsNodup_of_selectionValid
        hmatchedImplementation.1
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
            (fieldSelectionsWithResponseNameInScope schema parentType responseName
              rest)) :=
      (selectionSetArgumentsCoercible_append schema variableValues runtimeType
        subselections
        (mergeSelectionSets
          (fieldSelectionsWithResponseNameInScope schema parentType responseName
            rest))).1 hmerged |>.2
    exact selectionSetArgumentsCoercible_mergeSelectionSets_of_mem hmatchingReady
      hscoped rfl

theorem selectionSetArgumentsCoercible_of_filtered_and_removed
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType responseName : Name)
    : ∀ selectionSet,
        selectionSetArgumentsCoercible schema variableValues parentType
          (withoutFieldSelectionsWithResponseName schema responseName selectionSet)
        -> selectionSetRemovedResponseReady schema variableValues parentType responseName
            selectionSet
        -> selectionSetArgumentsCoercible schema variableValues parentType selectionSet
  | [], _hfiltered, _hremoved => by
      simp [selectionSetArgumentsCoercible]
  | selection :: rest, hfiltered, hremoved => by
      rcases hremoved with ⟨hheadRemoved, hrestRemoved⟩
      cases selection with
      | field candidate fieldName arguments directives children =>
          by_cases hname : (candidate == responseName) = true
          · have htailFiltered :
                selectionSetArgumentsCoercible schema variableValues parentType
                  (withoutFieldSelectionsWithResponseName schema responseName rest) := by
              simpa [withoutFieldSelectionsWithResponseName, hname] using hfiltered
            exact ⟨by
                simpa [selectionRemovedResponseReady, hname] using hheadRemoved,
              selectionSetArgumentsCoercible_of_filtered_and_removed schema
                variableValues parentType responseName rest htailFiltered
                hrestRemoved⟩
          · have hnameFalse : (candidate == responseName) = false := by
              cases hmatch : candidate == responseName
              · rfl
              · contradiction
            have hparts :
                selectionArgumentsCoercible schema variableValues parentType
                    (.field candidate fieldName arguments directives children)
                  ∧ selectionSetArgumentsCoercible schema variableValues parentType
                      (withoutFieldSelectionsWithResponseName schema responseName rest) := by
              simpa [withoutFieldSelectionsWithResponseName, hnameFalse,
                selectionSetArgumentsCoercible] using hfiltered
            exact ⟨hparts.1,
              selectionSetArgumentsCoercible_of_filtered_and_removed schema
                variableValues parentType responseName rest hparts.2 hrestRemoved⟩
      | inlineFragment typeCondition directives children =>
          have hparts :
              selectionArgumentsCoercible schema variableValues parentType
                  (.inlineFragment typeCondition directives
                    (withoutFieldSelectionsWithResponseName schema responseName
                      children))
                ∧ selectionSetArgumentsCoercible schema variableValues parentType
                    (withoutFieldSelectionsWithResponseName schema responseName rest) := by
            simpa [withoutFieldSelectionsWithResponseName,
              selectionSetArgumentsCoercible] using hfiltered
          exact ⟨by
              intro hdirectives htypeCondition
              exact selectionSetArgumentsCoercible_of_filtered_and_removed schema
                variableValues parentType responseName children
                (hparts.1 hdirectives htypeCondition) hheadRemoved,
            selectionSetArgumentsCoercible_of_filtered_and_removed schema
              variableValues parentType responseName rest hparts.2 hrestRemoved⟩

private theorem selectionSetArgumentsCoercible_withoutFieldSelections
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType responseName : Name)
    : ∀ selectionSet,
        selectionSetArgumentsCoercible schema variableValues parentType selectionSet
        -> selectionSetArgumentsCoercible schema variableValues parentType
            (withoutFieldSelectionsWithResponseName schema responseName selectionSet)
  | [], hready => by
      rw [withoutFieldSelectionsWithResponseName]
      exact hready
  | selection :: rest, hready => by
      rcases hready with ⟨hhead, htail⟩
      cases selection with
      | field candidate fieldName arguments directives children =>
          by_cases hname : (candidate == responseName) = true
          · simpa [withoutFieldSelectionsWithResponseName, hname] using
              selectionSetArgumentsCoercible_withoutFieldSelections schema
                variableValues parentType responseName rest htail
          · have hnameFalse : (candidate == responseName) = false := by
              cases hmatch : candidate == responseName
              · rfl
              · contradiction
            simpa [withoutFieldSelectionsWithResponseName, hnameFalse,
              selectionSetArgumentsCoercible] using
              And.intro hhead
                (selectionSetArgumentsCoercible_withoutFieldSelections schema
                  variableValues parentType responseName rest htail)
      | inlineFragment typeCondition directives children =>
          simpa [withoutFieldSelectionsWithResponseName,
            selectionSetArgumentsCoercible, selectionArgumentsCoercible] using And.intro
              (fun hdirectives htypeCondition =>
                selectionSetArgumentsCoercible_withoutFieldSelections schema
                  variableValues parentType responseName children
                  (hhead hdirectives htypeCondition))
              (selectionSetArgumentsCoercible_withoutFieldSelections schema
                variableValues parentType responseName rest htail)

private theorem selectionArgumentsCoercible_of_scoped_field_mem
    (schema : Schema) (variableValues : Execution.VariableValues)
    (executionParentType normalParentType responseName : Name)
    : ∀ selectionSet field,
        executionParentType = normalParentType
        -> schema.objectType normalParentType
        -> selectionSetDirectiveFree selectionSet
        -> selectionSetArgumentsCoercible schema variableValues executionParentType
            selectionSet
        -> field
            ∈ fieldSelectionsWithResponseNameInScope schema normalParentType responseName
                selectionSet
        -> selectionArgumentsCoercible schema variableValues executionParentType
            field := by
  intro selectionSet
  cases selectionSet with
  | nil =>
      intro field _hparent _hobject _hfree _hready hmem
      simp [fieldSelectionsWithResponseNameInScope] at hmem
  | cons selection rest =>
      intro field hparent hobject hfree hready hmem
      subst executionParentType
      rcases hready with ⟨hhead, htail⟩
      have hheadFree := selectionSetDirectiveFree_head hfree
      have htailFree := selectionSetDirectiveFree_tail hfree
      cases selection with
      | field candidate fieldName arguments directives children =>
          by_cases hname : (candidate == responseName) = true
          · simp [fieldSelectionsWithResponseNameInScope, hname] at hmem
            rcases hmem with rfl | hrest
            · exact hhead
            · exact selectionArgumentsCoercible_of_scoped_field_mem schema
                variableValues normalParentType normalParentType responseName rest
                field rfl hobject htailFree htail hrest
          · have hnameFalse : (candidate == responseName) = false := by
              cases hmatch : candidate == responseName
              · rfl
              · contradiction
            simp [fieldSelectionsWithResponseNameInScope, hnameFalse] at hmem
            exact selectionArgumentsCoercible_of_scoped_field_mem schema
              variableValues normalParentType normalParentType responseName rest
              field rfl hobject htailFree htail hmem
      | inlineFragment typeCondition directives children =>
          have hdirectives : directives = [] := hheadFree.1
          subst directives
          have hchildrenFree := hheadFree.2
          cases typeCondition with
          | none =>
              simp [fieldSelectionsWithResponseNameInScope] at hmem
              rcases hmem with hchild | hrest
              · exact selectionArgumentsCoercible_of_scoped_field_mem schema
                  variableValues normalParentType normalParentType responseName
                  children field rfl hobject hchildrenFree
                  (hhead (by simp [Execution.selectionDirectivesAllowBool]) trivial)
                  hchild
              · exact selectionArgumentsCoercible_of_scoped_field_mem schema
                  variableValues normalParentType normalParentType responseName rest
                  field rfl hobject htailFree htail hrest
          | some typeCondition =>
              by_cases hoverlap :
                  schema.typesOverlapBool normalParentType typeCondition = true
              · simp [fieldSelectionsWithResponseNameInScope, hoverlap] at hmem
                rcases hmem with hchild | hrest
                · exact selectionArgumentsCoercible_of_scoped_field_mem schema
                    variableValues normalParentType normalParentType responseName
                    children field rfl hobject hchildrenFree
                    (hhead (by simp [Execution.selectionDirectivesAllowBool])
                      (typeIncludesObjectBool_of_object_typesOverlapBool schema
                        hobject hoverlap))
                    hchild
                · exact selectionArgumentsCoercible_of_scoped_field_mem schema
                    variableValues normalParentType normalParentType responseName
                    rest field rfl hobject htailFree htail hrest
              · have hoverlapFalse :
                    schema.typesOverlapBool normalParentType typeCondition = false := by
                  cases hmatch : schema.typesOverlapBool normalParentType typeCondition
                  · rfl
                  · contradiction
                simp [fieldSelectionsWithResponseNameInScope, hoverlapFalse] at hmem
                exact selectionArgumentsCoercible_of_scoped_field_mem schema
                  variableValues normalParentType normalParentType responseName rest
                  field rfl hobject htailFree htail hmem
termination_by selectionSet => SelectionSet.size selectionSet
decreasing_by
  all_goals
    simp [SelectionSet.size, Selection.size]
    omega

private theorem mergeSelectionSets_argumentsCoercible_of_fields
    (schema : Schema) (variableValues : Execution.VariableValues)
    (childRuntimeType fieldName : Name)
    : ∀ fields,
        (∀ field,
          field ∈ fields
          -> ∃ responseName arguments directives children,
              field = .field responseName fieldName arguments directives children
              ∧ selectionSetArgumentsCoercible schema variableValues
                  childRuntimeType children)
        -> selectionSetArgumentsCoercible schema variableValues childRuntimeType
            (mergeSelectionSets fields)
  | [], _hfields => by
      simp [mergeSelectionSets, selectionSetArgumentsCoercible]
  | field :: rest, hfields => by
      cases field with
      | field responseName fieldName arguments directives children =>
          rcases hfields (.field responseName fieldName arguments directives children)
              (by simp) with
            ⟨matchedResponseName, matchedArguments, matchedDirectives,
              matchedChildren, heq, hchildren⟩
          cases heq
          have hrest :
              selectionSetArgumentsCoercible schema variableValues childRuntimeType
                (mergeSelectionSets rest) :=
            mergeSelectionSets_argumentsCoercible_of_fields schema variableValues
              childRuntimeType fieldName rest
              (by
                intro candidate hmem
                exact hfields candidate (by simp [hmem]))
          exact (selectionSetArgumentsCoercible_append schema variableValues
            childRuntimeType children (mergeSelectionSets rest)).2
              ⟨hchildren, hrest⟩
      | inlineFragment typeCondition directives children =>
          rcases hfields (.inlineFragment typeCondition directives children) (by simp) with
            ⟨responseName, arguments, matchedDirectives, matchedChildren, heq,
              _hready⟩
          cases heq

private theorem possibleTypeNormalizations_argumentsCoercible
    (schema : Schema) (variableValues : Execution.VariableValues)
    (executionParentType : Name)
    : ∀ possibleTypes selectionSet,
        (∀ objectType,
          objectType ∈ possibleTypes
          -> schema.typeIncludesObjectBool objectType executionParentType = true
          -> selectionSetArgumentsCoercible schema variableValues executionParentType
              (normalizeSelectionSet schema objectType selectionSet))
        -> selectionSetArgumentsCoercible schema variableValues executionParentType
            (possibleTypeNormalizations schema possibleTypes selectionSet)
  | [], _selectionSet, _hbranches => by
      simp [possibleTypeNormalizations, selectionSetArgumentsCoercible]
  | objectType :: rest, selectionSet, hbranches => by
      cases hnormalized : normalizeSelectionSet schema objectType selectionSet with
      | nil =>
          simpa [possibleTypeNormalizations, hnormalized] using
            possibleTypeNormalizations_argumentsCoercible schema variableValues
              executionParentType rest selectionSet
              (fun candidate hmem hinclude =>
                hbranches candidate (by simp [hmem]) hinclude)
      | cons head tail =>
          have hhead :
              selectionArgumentsCoercible schema variableValues executionParentType
                (.inlineFragment (some objectType) [] (head :: tail)) := by
            intro _hdirectives hinclude
            simpa [hnormalized] using hbranches objectType (by simp) hinclude
          simpa [possibleTypeNormalizations, hnormalized,
            selectionSetArgumentsCoercible] using And.intro hhead
              (possibleTypeNormalizations_argumentsCoercible schema variableValues
                executionParentType rest selectionSet
                (fun candidate hmem hinclude =>
                  hbranches candidate (by simp [hmem]) hinclude))

theorem selectionSetArgumentsCoercible_normalizeSelectionSetAt
    (schema : Schema) (variableValues : Execution.VariableValues)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    : ∀ parentType selectionSet,
        schema.objectType parentType
        -> selectionSetSemanticsReady schema parentType selectionSet
        -> FieldMerge.fieldsInSetCanMerge schema parentType selectionSet
        -> selectionSetDirectiveFree selectionSet
        -> selectionSetArgumentsCoercible schema variableValues parentType selectionSet
        -> selectionSetArgumentsCoercible schema variableValues parentType
            (normalizeSelectionSet schema parentType selectionSet) := by
  intro parentType selectionSet
  induction parentType, selectionSet using normalizeSelectionSet.induct schema with
  | case1 parentType =>
      intro _hobject _hready _hmerge _hfree _hcoercible
      simp [normalizeSelectionSet, selectionSetArgumentsCoercible]
  | case2 normalParentType rest responseName fieldName arguments directives
      subselections hlookup hrest =>
      intro hobject hready hmerge hfree hcoercible
      have htailReady := selectionSetSemanticsReady_tail hready
      have htailMerge :=
        fieldsInSetCanMerge_tail schema normalParentType
          (Selection.field responseName fieldName arguments directives subselections)
          rest hmerge
      have htailFree := selectionSetDirectiveFree_tail hfree
      have htailCoercible := hcoercible.2
      have hfilteredReady :=
        selectionSetSemanticsReady_withoutFieldSelectionsWithResponseName schema
          responseName normalParentType rest htailReady
      have hfilteredMerge :=
        fieldsInSetCanMerge_withoutFieldSelectionsWithResponseName schema responseName
          normalParentType rest htailMerge
      have hfilteredFree :=
        withoutFieldSelectionsWithResponseName_directiveFree schema responseName rest
          htailFree
      have hfilteredCoercible :=
        selectionSetArgumentsCoercible_withoutFieldSelections schema variableValues
          normalParentType responseName rest htailCoercible
      simpa [normalizeSelectionSet, hlookup] using
        hrest hobject hfilteredReady hfilteredMerge hfilteredFree hfilteredCoercible
  | case3 normalParentType rest responseName fieldName arguments directives
      subselections fieldDefinition hlookup matching mergedSubselections
      returnType hrest hmerged hpossible =>
      intro hobject hready hmerge hfree hcoercible
      let normalizedSubselections :=
        if objectTypeNameBool schema returnType then
          normalizeSelectionSet schema returnType mergedSubselections
        else
          possibleTypeNormalizations schema
            (schema.getPossibleTypes returnType) mergedSubselections
      have hselectionFree := selectionSetDirectiveFree_head hfree
      have hdirectives : directives = [] := hselectionFree.1
      subst directives
      have hsubselectionsFree := hselectionFree.2
      have hrestFree := selectionSetDirectiveFree_tail hfree
      have htailReady := selectionSetSemanticsReady_tail hready
      have htailMerge :=
        fieldsInSetCanMerge_tail schema normalParentType
          (Selection.field responseName fieldName arguments [] subselections) rest
          hmerge
      have htailCoercible := hcoercible.2
      have hfilteredReady :=
        selectionSetSemanticsReady_withoutFieldSelectionsWithResponseName schema
          responseName normalParentType rest htailReady
      have hfilteredMerge :=
        fieldsInSetCanMerge_withoutFieldSelectionsWithResponseName schema responseName
          normalParentType rest htailMerge
      have hfilteredFree :=
        withoutFieldSelectionsWithResponseName_directiveFree schema responseName rest
          hrestFree
      have hfilteredCoercible :=
        selectionSetArgumentsCoercible_withoutFieldSelections schema variableValues
          normalParentType responseName rest htailCoercible
      have hlookupValid :
          selectionSetLookupValid schema normalParentType
            (Selection.field responseName fieldName arguments [] subselections :: rest) :=
        selectionSetLookupValid_of_selectionSetSemanticsReady
          (Selection.field responseName fieldName arguments [] subselections :: rest)
          hready
      have hmatchingFree : selectionSetDirectiveFree matching := by
        subst matching
        exact fieldSelectionsWithResponseNameInScope_directiveFree schema
          normalParentType responseName rest hrestFree
      have hmergedFree : selectionSetDirectiveFree mergedSubselections := by
        subst mergedSubselections
        exact selectionSetDirectiveFree_append hsubselectionsFree
          (selectionSetDirectiveFree_mergeSelectionSets hmatchingFree)
      have hmergedSemanticReady :
          ∀ objectType,
            objectType ∈ schema.getPossibleTypes returnType
            -> selectionSetSemanticsReady schema objectType mergedSubselections := by
        intro objectType hobjectType
        exact selectionSetSemanticsReady_fieldHead_merged_of_child_object schema
          normalParentType responseName fieldName objectType arguments subselections rest
          fieldDefinition hobject hready hlookupValid hmerge hlookup
          (List.contains_iff_mem.mpr (by simpa [returnType] using hobjectType))
      have hmergedMerge :
          ∀ objectType,
            objectType ∈ schema.getPossibleTypes returnType
            -> FieldMerge.fieldsInSetCanMerge schema objectType mergedSubselections := by
        intro objectType _hobjectType
        exact fieldsInSetCanMerge_fieldHead_merged_of_canMerge_object_lookupValid
          schema normalParentType responseName fieldName objectType arguments
          subselections rest fieldDefinition hobject hlookupValid hmerge hlookup
      have hnormalizedRest :=
        hrest hobject hfilteredReady hfilteredMerge hfilteredFree
          hfilteredCoercible
      rw [normalizeSelectionSet.eq_2, hlookup]
      change selectionSetArgumentsCoercible schema variableValues normalParentType
        (Selection.field responseName fieldName arguments [] normalizedSubselections
          :: normalizeSelectionSet schema normalParentType
            (withoutFieldSelectionsWithResponseName schema responseName rest))
      constructor
      · intro _hdirectives executionDefinition hexecutionLookup
        have hdefinition : executionDefinition = fieldDefinition := by
          rw [hlookup] at hexecutionLookup
          exact Option.some.inj hexecutionLookup.symm
        subst executionDefinition
        have hsourceField :=
          hcoercible.1 (by simp [Execution.selectionDirectivesAllowBool])
            fieldDefinition hlookup
        constructor
        · exact hsourceField.1
        · intro childRuntimeType hchildInclude
          have hmatchingChildren :
              selectionSetArgumentsCoercible schema variableValues childRuntimeType
                (mergeSelectionSets matching) := by
            apply mergeSelectionSets_argumentsCoercible_of_fields schema variableValues
              childRuntimeType fieldName matching
            intro matched hmatched
            rcases fieldSelectionsWithResponseNameInScope_mem_field schema
                normalParentType responseName rest matched hmatched with
              ⟨matchedFieldName, matchedArguments, matchedDirectives,
                matchedSubselections, rfl⟩
            have hsame : matchedFieldName = fieldName :=
              fieldSelectionsWithResponseNameInScope_matching_same_field_of_canMerge_object_lookupValid
                schema normalParentType responseName fieldName arguments subselections
                rest hobject hlookupValid hmerge matchedFieldName matchedArguments
                matchedDirectives matchedSubselections hmatched
            subst matchedFieldName
            have hmatchedReady :=
              selectionArgumentsCoercible_of_scoped_field_mem schema variableValues
                normalParentType normalParentType responseName rest _ rfl hobject
                hrestFree htailCoercible hmatched
            have hmatchedFree :
                selectionDirectiveFree
                  (.field responseName fieldName matchedArguments matchedDirectives
                    matchedSubselections) :=
              selectionDirectiveFree_of_mem_for_readiness hmatchingFree hmatched
            have hmatchedDirectives : matchedDirectives = [] := hmatchedFree.1
            subst matchedDirectives
            exact ⟨responseName, matchedArguments, [],
              matchedSubselections, rfl,
              (hmatchedReady (by simp [Execution.selectionDirectivesAllowBool])
                fieldDefinition hlookup).2 childRuntimeType
                  (by simpa [returnType] using hchildInclude)⟩
          have hsourceMerged :
              selectionSetArgumentsCoercible schema variableValues childRuntimeType
                mergedSubselections := by
            subst mergedSubselections
            exact (selectionSetArgumentsCoercible_append schema variableValues
              childRuntimeType subselections (mergeSelectionSets matching)).2
                ⟨hsourceField.2 childRuntimeType hchildInclude,
                  hmatchingChildren⟩
          by_cases hreturnObject : objectTypeNameBool schema returnType = true
          · have hreturnObjectType :=
              objectType_of_objectTypeNameBool_eq_true schema hreturnObject
            have hchildEq : childRuntimeType = returnType :=
              object_typeIncludesObjectBool_eq_self schema hreturnObjectType
                (by simpa [returnType] using hchildInclude)
            subst childRuntimeType
            simpa [normalizedSubselections, hreturnObject] using
              hmerged hreturnObjectType
                (hmergedSemanticReady returnType
                  (List.contains_iff_mem.mp
                    (object_typeIncludesObjectBool_self schema hreturnObjectType)))
                (hmergedMerge returnType
                  (List.contains_iff_mem.mp
                    (object_typeIncludesObjectBool_self schema hreturnObjectType)))
                hmergedFree hsourceMerged
          · have hreturnObjectFalse :
                objectTypeNameBool schema returnType = false := by
              cases hmatch : objectTypeNameBool schema returnType
              · rfl
              · contradiction
            have hbranches :
                ∀ objectType,
                  objectType ∈ schema.getPossibleTypes returnType
                  -> schema.typeIncludesObjectBool objectType childRuntimeType = true
                  -> selectionSetArgumentsCoercible schema variableValues
                      childRuntimeType
                      (normalizeSelectionSet schema objectType mergedSubselections) := by
              intro objectType hobjectType hobjectIncludes
              have hobjectBranch :=
                SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects hschema
                  returnType objectType hobjectType
              have hchildEq : childRuntimeType = objectType :=
                object_typeIncludesObjectBool_eq_self schema hobjectBranch
                  hobjectIncludes
              subst childRuntimeType
              exact hpossible objectType hobjectBranch
                (hmergedSemanticReady objectType hobjectType)
                (hmergedMerge objectType hobjectType) hmergedFree hsourceMerged
            simpa [normalizedSubselections, hreturnObjectFalse] using
              possibleTypeNormalizations_argumentsCoercible schema variableValues
                childRuntimeType (schema.getPossibleTypes returnType)
                mergedSubselections hbranches
      · exact hnormalizedRest
  | case4 normalParentType rest directives subselections happend =>
      intro hobject hready hmerge hfree hcoercible
      have hselectionFree := selectionSetDirectiveFree_head hfree
      have hdirectives : directives = [] := hselectionFree.1
      subst directives
      have hheadReady :
          selectionSemanticsReady schema normalParentType
            (Selection.inlineFragment none [] subselections) := by
        unfold selectionSetSemanticsReady at hready
        exact hready _ (by simp)
      have hbodyReady :
          selectionSetSemanticsReady schema normalParentType subselections := by
        simpa [selectionSemanticsReady] using hheadReady
      have htailReady := selectionSetSemanticsReady_tail hready
      have hbodyTailReady := selectionSetSemanticsReady_append hbodyReady htailReady
      have hbodyTailMerge :=
        fieldsInSetCanMerge_inlineFragment_none_flatten schema normalParentType
          subselections rest hmerge
      have hbodyTailFree :=
        selectionSetDirectiveFree_append hselectionFree.2
          (selectionSetDirectiveFree_tail hfree)
      have hbodyTailCoercible :=
        (selectionSetArgumentsCoercible_append schema variableValues
          normalParentType subselections rest).2
            ⟨hcoercible.1 (by simp [Execution.selectionDirectivesAllowBool]) trivial,
              hcoercible.2⟩
      simpa [normalizeSelectionSet] using
        happend hobject hbodyTailReady hbodyTailMerge hbodyTailFree hbodyTailCoercible
  | case5 normalParentType rest typeCondition directives subselections hoverlap
      _hrest happend =>
      intro hobject hready hmerge hfree hcoercible
      have hselectionFree := selectionSetDirectiveFree_head hfree
      have hdirectives : directives = [] := hselectionFree.1
      subst directives
      have hheadReady :
          selectionSemanticsReady schema normalParentType
            (Selection.inlineFragment (some typeCondition) [] subselections) := by
        unfold selectionSetSemanticsReady at hready
        exact hready _ (by simp)
      have hbodyReady :
          selectionSetSemanticsReady schema normalParentType subselections := by
        have hpair :
            selectionSetLookupValid schema typeCondition subselections
              ∧ (schema.typesOverlapBool normalParentType typeCondition = true ->
                selectionSetSemanticsReady schema normalParentType subselections) := by
          simpa [selectionSemanticsReady] using hheadReady
        exact hpair.2 hoverlap
      have htailReady := selectionSetSemanticsReady_tail hready
      have hlookupBodyType : selectionSetLookupValid schema typeCondition subselections := by
        have hpair :
            selectionSetLookupValid schema typeCondition subselections
              ∧ (schema.typesOverlapBool normalParentType typeCondition = true ->
                selectionSetSemanticsReady schema normalParentType subselections) := by
          simpa [selectionSemanticsReady] using hheadReady
        exact hpair.1
      have hbodyTailReady := selectionSetSemanticsReady_append hbodyReady htailReady
      have hbodyTailMerge :=
        fieldsInSetCanMerge_inlineFragment_some_overlap_flatten_object schema
          normalParentType typeCondition subselections rest hschema hobject hoverlap
          (selectionSetLookupValid_of_selectionSetSemanticsReady subselections
            hbodyReady)
          hlookupBodyType
          (selectionSetLookupValid_of_selectionSetSemanticsReady rest htailReady) hmerge
      have hbodyTailFree :=
        selectionSetDirectiveFree_append hselectionFree.2
          (selectionSetDirectiveFree_tail hfree)
      have hbodyTailCoercible :=
        (selectionSetArgumentsCoercible_append schema variableValues
          normalParentType subselections rest).2
            ⟨hcoercible.1 (by simp [Execution.selectionDirectivesAllowBool])
                (typeIncludesObjectBool_of_object_typesOverlapBool schema hobject
                  hoverlap),
              hcoercible.2⟩
      simpa [normalizeSelectionSet, hoverlap] using
        happend hobject hbodyTailReady hbodyTailMerge hbodyTailFree hbodyTailCoercible
  | case6 normalParentType rest typeCondition directives subselections hoverlap hrest =>
      intro hobject hready hmerge hfree hcoercible
      have htailReady := selectionSetSemanticsReady_tail hready
      have htailMerge :=
        fieldsInSetCanMerge_tail schema normalParentType
          (Selection.inlineFragment (some typeCondition) directives subselections)
          rest hmerge
      have htailFree := selectionSetDirectiveFree_tail hfree
      have hfalse : schema.typesOverlapBool normalParentType typeCondition = false := by
        cases hmatch : schema.typesOverlapBool normalParentType typeCondition
        · rfl
        · contradiction
      simpa [normalizeSelectionSet, hfalse] using
        hrest hobject htailReady htailMerge htailFree hcoercible.2

theorem selectionSetArgumentsCoercible_of_normalizeSelectionSet
    (schema : Schema) (variableValues : Execution.VariableValues)
    (variableDefinitions : List VariableDefinition)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    : ∀ parentType selectionSet,
      ∀ typeConditions,
        schema.objectType parentType
        -> parentType ∈ typeConditions
        -> objectSatisfiesTypeConditionStack schema parentType typeConditions
        -> selectionSetSemanticsReady schema parentType selectionSet
        -> Validation.selectionSetValidInPossibleTypes schema
            variableDefinitions parentType selectionSet
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
      intro _typeConditions _hobject _hparent _hstack _hready _himplementation
        _hmerge _hfree _hfeasible _hnormalized
      simp [selectionSetArgumentsCoercible]
  | case2 parentType rest responseName fieldName arguments directives
      subselections hlookup _hrest =>
      intro _typeConditions _hobject _hparent _hstack hready _himplementation
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
      intro typeConditions hobject hparent hstack hready himplementation hmerge
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
      have htailImplementation := selectionSetValidInPossibleTypes_tail himplementation
      have htailMerge :=
        fieldsInSetCanMerge_tail schema parentType
          (Selection.field responseName fieldName arguments [] subselections) rest
          hmerge
      have htailFeasible := selectionSetTypeConditionFeasible_tail hfeasible
      have hfilteredReady :=
        selectionSetSemanticsReady_withoutFieldSelectionsWithResponseName schema
          responseName parentType rest htailReady
      have hfilteredImplementation :=
        selectionSetValidInPossibleTypes_withoutFieldSelectionsWithResponseName
          schema responseName variableDefinitions parentType rest htailImplementation
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
      have hmergedFeasible :
          ∀ objectType,
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
      have hmergedImplementation :
          ∀ objectType,
            objectType ∈ schema.getPossibleTypes returnType
            -> Validation.selectionSetValidInPossibleTypes schema
                variableDefinitions objectType mergedSubselections := by
        intro objectType hobjectType
        exact selectionSetValidInPossibleTypes_fieldHead_merged_of_child_object
          schema variableDefinitions parentType responseName fieldName objectType
          arguments subselections rest fieldDefinition hobject hlookupValid
          himplementation hmerge hlookup
          (List.contains_iff_mem.mpr (by simpa [returnType] using hobjectType))
      have hmergedSemanticReady :
          ∀ objectType,
            objectType ∈ schema.getPossibleTypes returnType
            -> selectionSetSemanticsReady schema objectType mergedSubselections := by
        intro objectType hobjectType
        exact selectionSetSemanticsReady_fieldHead_merged_of_child_object schema
          parentType responseName fieldName objectType arguments subselections rest
          fieldDefinition hobject hready hlookupValid hmerge hlookup
          (by
            exact List.contains_iff_mem.mpr
              (by simpa [returnType] using hobjectType))
      have hmergedMerge :
          ∀ objectType,
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
          hfilteredImplementation hfilteredMerge hfilteredFree hfilteredFeasible
          hnormalizedRest
      have hmergedCoercible :
          ∀ runtimeType,
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
            (hmergedImplementation returnType hruntimeMem)
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
              (hmergedImplementation runtimeType hruntimeMem)
              (hmergedMerge runtimeType hruntimeMem) hmergedFree
              (hmergedFeasible runtimeType hruntimeMem) hnormalizedChild
          · exact selectionSetArgumentsCoercible_of_no_feasible_field schema
              variableValues runtimeType [runtimeType] mergedSubselections
              (hmergedFeasible runtimeType hruntimeMem) hcontains
      have hremovedCoercible :=
        selectionSetRemovedResponseReady_of_merged_group schema variableValues
          variableDefinitions parentType responseName fieldName arguments
          subselections rest fieldDefinition typeConditions hobject hparent
          hlookupValid himplementation hmerge hfeasible hlookup
          hnormalizedField.1 (by simpa [returnType] using hmergedCoercible)
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
      intro typeConditions hobject hparent hstack hready himplementation hmerge
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
      have hbodyImplementation :
          Validation.selectionSetValidInPossibleTypes schema variableDefinitions
            parentType subselections := by
        have hhead := selectionSetValidInPossibleTypes_head himplementation
        exact hhead parentType
          (List.contains_iff_mem.mp (object_typeIncludesObjectBool_self schema hobject))
      have htailReady := selectionSetSemanticsReady_tail hready
      have htailImplementation := selectionSetValidInPossibleTypes_tail himplementation
      have hbodyTailReady := selectionSetSemanticsReady_append hbodyReady htailReady
      have hbodyTailImplementation :=
        selectionSetValidInPossibleTypes_append hbodyImplementation htailImplementation
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
        hbodyTailReady hbodyTailImplementation hbodyTailMerge hbodyTailFree
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
      intro typeConditions hobject hparent hstack hready himplementation hmerge
        hfree hfeasible hnormalized
      have hselectionFree := selectionSetDirectiveFree_head hfree
      have hdirectives : directives = [] := hselectionFree.1
      subst directives
      have hrestFree := selectionSetDirectiveFree_tail hfree
      have hheadReady :
          selectionSemanticsReady schema parentType
            (Selection.inlineFragment (some typeCondition) [] subselections) :=
        by
          unfold selectionSetSemanticsReady at hready
          exact hready _ (by simp)
      have hbodyReady : selectionSetSemanticsReady schema parentType subselections := by
        have hpair :
            selectionSetLookupValid schema typeCondition subselections
              ∧ (schema.typesOverlapBool parentType typeCondition = true ->
                selectionSetSemanticsReady schema parentType subselections) := by
          simpa [selectionSemanticsReady] using hheadReady
        exact hpair.2 hoverlap
      have hheadImplementation := selectionSetValidInPossibleTypes_head himplementation
      have hbodyImplementation :
          Validation.selectionSetValidInPossibleTypes schema variableDefinitions
            parentType subselections := by
        have hfragment :
            ∀ objectType,
              objectType ∈ schema.getPossibleTypes typeCondition
              -> Validation.selectionSetValidInPossibleTypes schema
                  variableDefinitions objectType subselections := by
          simpa [Validation.selectionValidInPossibleTypes] using
            hheadImplementation hoverlap
        exact hfragment parentType
          (List.contains_iff_mem.mp
            (typeIncludesObjectBool_of_object_typesOverlapBool schema hobject hoverlap))
      have htailReady := selectionSetSemanticsReady_tail hready
      have htailImplementation := selectionSetValidInPossibleTypes_tail himplementation
      have hbodyTailReady := selectionSetSemanticsReady_append hbodyReady htailReady
      have hbodyTailImplementation :=
        selectionSetValidInPossibleTypes_append hbodyImplementation htailImplementation
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
        hbodyTailReady hbodyTailImplementation hbodyTailMerge hbodyTailFree
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
      intro typeConditions hobject hparent hstack hready himplementation hmerge
        hfree hfeasible hnormalized
      have htailReady := selectionSetSemanticsReady_tail hready
      have htailImplementation := selectionSetValidInPossibleTypes_tail himplementation
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
        htailImplementation htailMerge htailFree htailFeasible
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

theorem operationArgumentsCoercible_of_normalizeOperation
    (schema : Schema) (operation : Operation)
    (suppliedValues : Execution.VariableValues)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hvalid : Validation.operationDefinitionValid schema operation)
    (hfree : operationDirectiveFree operation)
    (himplementation : operationFieldsValidInPossibleTypes schema operation)
    (hfeasible : operationTypeConditionFeasible schema operation)
    (hnormalized
      : operationArgumentsCoercible schema suppliedValues
          (normalizeOperation schema operation))
    : operationArgumentsCoercible schema suppliedValues operation := by
  have hrootObject : schema.objectType (operation.rootType schema) := by
    have hrootEq := Validation.operationDefinitionValid_rootType_eq hvalid
    rw [hrootEq]
    exact hschema.2.1
  have hselectionValid :
      Validation.selectionSetValid schema operation.variableDefinitions
        (operation.rootType schema) operation.selectionSet :=
    Validation.operationDefinitionValid_selectionSetValid hvalid
  have hready :
      selectionSetSemanticsReady schema (operation.rootType schema)
        operation.selectionSet :=
    selectionSetSemanticsReady_of_selectionSetValid_object schema
      operation.variableDefinitions (operation.rootType schema) hschema hrootObject
      operation.selectionSet hselectionValid
  have hmerge :
      FieldMerge.fieldsInSetCanMerge schema (operation.rootType schema)
        operation.selectionSet :=
    Validation.operationDefinitionValid_fieldsInSetCanMerge hvalid
  have hstack :
      objectSatisfiesTypeConditionStack schema (operation.rootType schema)
        [operation.rootType schema] :=
    objectSatisfiesTypeConditionStack_singleton_of_object_forValidity schema
      hrootObject
  have hvalues :
      Execution.coerceVariableValues (normalizeOperation schema operation)
          suppliedValues
        = Execution.coerceVariableValues operation suppliedValues := by
    rfl
  rw [operationArgumentsCoercible, hvalues] at hnormalized
  change selectionSetArgumentsCoercible schema
    (Execution.coerceVariableValues operation suppliedValues)
    (operation.rootType schema)
    (normalizeSelectionSet schema (operation.rootType schema) operation.selectionSet)
      at hnormalized
  unfold operationArgumentsCoercible
  apply selectionSetArgumentsCoercible_of_normalizeSelectionSet schema
    (Execution.coerceVariableValues operation suppliedValues)
    operation.variableDefinitions hschema (operation.rootType schema)
    operation.selectionSet [operation.rootType schema] hrootObject (by simp)
    hstack hready himplementation hmerge hfree hfeasible
  exact hnormalized

theorem operationArgumentsCoercible_normalizeOperation
    (schema : Schema) (operation : Operation)
    (suppliedValues : Execution.VariableValues)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hvalid : Validation.operationDefinitionValid schema operation)
    (hfree : operationDirectiveFree operation)
    (hcoercible : operationArgumentsCoercible schema suppliedValues operation)
    : operationArgumentsCoercible schema suppliedValues
        (normalizeOperation schema operation) := by
  have hrootObject : schema.objectType (operation.rootType schema) := by
    have hrootEq := Validation.operationDefinitionValid_rootType_eq hvalid
    rw [hrootEq]
    exact hschema.2.1
  have hselectionValid :
      Validation.selectionSetValid schema operation.variableDefinitions
        (operation.rootType schema) operation.selectionSet :=
    Validation.operationDefinitionValid_selectionSetValid hvalid
  have hready :
      selectionSetSemanticsReady schema (operation.rootType schema)
        operation.selectionSet :=
    selectionSetSemanticsReady_of_selectionSetValid_object schema
      operation.variableDefinitions (operation.rootType schema) hschema hrootObject
      operation.selectionSet hselectionValid
  have hmerge :
      FieldMerge.fieldsInSetCanMerge schema (operation.rootType schema)
        operation.selectionSet :=
    Validation.operationDefinitionValid_fieldsInSetCanMerge hvalid
  have hvalues :
      Execution.coerceVariableValues (normalizeOperation schema operation)
          suppliedValues
        = Execution.coerceVariableValues operation suppliedValues := by
    rfl
  unfold operationArgumentsCoercible at hcoercible ⊢
  rw [hvalues]
  change selectionSetArgumentsCoercible schema
    (Execution.coerceVariableValues operation suppliedValues)
    (operation.rootType schema)
    (normalizeSelectionSet schema (operation.rootType schema) operation.selectionSet)
  exact selectionSetArgumentsCoercible_normalizeSelectionSetAt schema
    (Execution.coerceVariableValues operation suppliedValues) hschema
    (operation.rootType schema) operation.selectionSet
    hrootObject hready hmerge hfree hcoercible

end GroundTypeNormalization

end NormalForm

end GraphQL
