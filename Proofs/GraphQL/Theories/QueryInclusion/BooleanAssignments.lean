import Proofs.GraphQL.Theories.QueryInclusion.Algebra

/-! Complete Boolean assignments and their effect on conditional field collection. -/

namespace GraphQL
namespace QueryInclusion

open Execution

def representativeBooleanValues : List Name -> VariableValues -> VariableValues
  | [], _variableValues => []
  | variableName :: rest, variableValues =>
      let value := (inputValueBoolean? variableValues (.variable variableName)).getD false
      (variableName, .boolean value) :: representativeBooleanValues rest variableValues

theorem representativeBooleanValues_mem
    (variables : List Name) (variableValues : VariableValues)
    : representativeBooleanValues variables variableValues
      ∈ booleanVariableAssignments variables := by
  induction variables with
  | nil => simp [representativeBooleanValues, booleanVariableAssignments]
  | cons variableName rest ih =>
      cases hvalue : inputValueBoolean? variableValues (.variable variableName) with
      | none =>
          simp [representativeBooleanValues, booleanVariableAssignments, hvalue, ih]
      | some value =>
          cases value <;>
            simp [representativeBooleanValues, booleanVariableAssignments, hvalue, ih]

theorem inputValueBoolean?_representativeBooleanValues
    (variables : List Name) (variableValues : VariableValues)
    (hcomplete : boolVarsComplete variables variableValues)
    (variableName : Name) (hvariable : variableName ∈ variables)
    : inputValueBoolean? (representativeBooleanValues variables variableValues)
        (.variable variableName)
      = inputValueBoolean? variableValues (.variable variableName) := by
  induction variables with
  | nil => simp at hvariable
  | cons head rest ih =>
      by_cases hname : head = variableName
      · subst head
        rcases hcomplete variableName (by simp) with ⟨value, hvalue⟩
        simp only [representativeBooleanValues]
        rw [hvalue]
        simp [inputValueBoolean?, lookupVariableValue?, InputValue.staticBoolean?,
          ConstInputValue.toInputValue]
      · have hrest : variableName ∈ rest := by
          rcases List.mem_cons.mp hvariable with heq | hrest
          · exact False.elim (hname heq.symm)
          · exact hrest
        have hrestComplete : boolVarsComplete rest variableValues := by
          intro candidate hcandidate
          exact hcomplete candidate (by simp [hcandidate])
        have hagree := ih hrestComplete hrest
        simpa only [representativeBooleanValues, inputValueBoolean?,
          lookupVariableValue?, if_neg hname] using hagree

theorem booleanVariableAssignments_lookup
    (variables : List Name) (variableValues : VariableValues)
    (hcase : variableValues ∈ booleanVariableAssignments variables)
    (variableName : Name) (hvariable : variableName ∈ variables)
    : ∃ value,
        lookupVariableValue? variableValues variableName = some (.boolean value) := by
  induction variables generalizing variableValues with
  | nil => simp at hvariable
  | cons head rest ih =>
      simp only [booleanVariableAssignments, List.mem_append, List.mem_map] at hcase
      rcases hcase with ⟨tail, htail, rfl⟩ | ⟨tail, htail, rfl⟩
      · rcases List.mem_cons.mp hvariable with rfl | hrest
        · exact ⟨false, by simp [lookupVariableValue?]⟩
        · by_cases heq : head = variableName
          · subst head
            exact ⟨false, by
              simp [lookupVariableValue?]⟩
          · rcases ih tail htail hrest with ⟨value, hlookup⟩
            exact ⟨value, by simp [lookupVariableValue?, heq, hlookup]⟩
      · rcases List.mem_cons.mp hvariable with rfl | hrest
        · exact ⟨true, by simp [lookupVariableValue?]⟩
        · by_cases heq : head = variableName
          · subst head
            exact ⟨true, by
              simp [lookupVariableValue?]⟩
          · rcases ih tail htail hrest with ⟨value, hlookup⟩
            exact ⟨value, by simp [lookupVariableValue?, heq, hlookup]⟩

theorem booleanVariableAssignments_lookup_nonNull
    (variables : List Name) (variableValues : VariableValues)
    (hcase : variableValues ∈ booleanVariableAssignments variables)
    {variableName : Name} {value : CoercedInputValue}
    (hlookup : lookupVariableValue? variableValues variableName = some value)
    : Validation.inputValueNonNull value.toInputValue := by
  induction variables generalizing variableValues with
  | nil =>
      simp [booleanVariableAssignments] at hcase
      subst variableValues
      simp [lookupVariableValue?] at hlookup
  | cons head rest ih =>
      simp only [booleanVariableAssignments, List.mem_append, List.mem_map] at hcase
      rcases hcase with ⟨tail, htail, rfl⟩ | ⟨tail, htail, rfl⟩
      · by_cases hname : head = variableName
        · subst head
          simp [lookupVariableValue?] at hlookup
          subst value
          simp [ConstInputValue.toInputValue, Validation.inputValueNonNull]
        · simp [lookupVariableValue?, hname] at hlookup
          exact ih tail htail hlookup
      · by_cases hname : head = variableName
        · subst head
          simp [lookupVariableValue?] at hlookup
          subst value
          simp [ConstInputValue.toInputValue, Validation.inputValueNonNull]
        · simp [lookupVariableValue?, hname] at hlookup
          exact ih tail htail hlookup

theorem selectionDirectivesAllowBool_eq_of_agree
    (left right : VariableValues) (directives : List DirectiveApplication)
    (hagrees
      : ∀ variableName,
          variableName
            ∈ directives.filterMap SelectionConditions.directiveBooleanVariable?
          -> inputValueBoolean? left (.variable variableName)
              = inputValueBoolean? right (.variable variableName))
    : selectionDirectivesAllowBool left directives
      = selectionDirectivesAllowBool right directives := by
  induction directives with
  | nil => rfl
  | cons directive rest ih =>
      have hrest := ih (by
        intro variableName hmember
        apply hagrees variableName
        simp only [List.filterMap_cons]
        cases SelectionConditions.directiveBooleanVariable? directive <;> simp [hmember])
      have hdirective : directiveAllowsSelectionBool left directive
          = directiveAllowsSelectionBool right directive := by
        cases directive <;> rename_i argument <;> cases argument <;> try rfl
        all_goals
          simp only [directiveAllowsSelectionBool]
          rw [hagrees _ (by simp [SelectionConditions.directiveBooleanVariable?])]
      change (directiveAllowsSelectionBool left directive
          && selectionDirectivesAllowBool left rest)
        = (directiveAllowsSelectionBool right directive
          && selectionDirectivesAllowBool right rest)
      rw [hdirective, hrest]

mutual
  theorem collectFields_eq_of_boolean_agreement
      (schema : Schema) (left right : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectRef)
      (selectionSet : List Selection)
      (hagrees
        : ∀ variableName,
            variableName ∈ SelectionConditions.selectionSetBooleanVariables selectionSet
            -> inputValueBoolean? left (.variable variableName)
                = inputValueBoolean? right (.variable variableName))
      : collectFields schema left parentType source selectionSet
        = collectFields schema right parentType source selectionSet := by
    cases selectionSet with
    | nil => rfl
    | cons selection rest =>
        rw [collectFields, collectFields]
        congr 1
        · exact collectSelection_eq_of_boolean_agreement schema left right parentType source
            selection (by
              intro variableName hmember
              exact hagrees variableName (by
                simp [SelectionConditions.selectionSetBooleanVariables, hmember]))
        · exact collectFields_eq_of_boolean_agreement schema left right parentType source rest
            (by
              intro variableName hmember
              exact hagrees variableName (by
                simp [SelectionConditions.selectionSetBooleanVariables, hmember]))

  theorem collectSelection_eq_of_boolean_agreement
      (schema : Schema) (left right : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectRef)
      (selection : Selection)
      (hagrees
        : ∀ variableName,
            variableName ∈ SelectionConditions.selectionBooleanVariables selection
            -> inputValueBoolean? left (.variable variableName)
                = inputValueBoolean? right (.variable variableName))
      : collectSelection schema left parentType source selection
        = collectSelection schema right parentType source selection := by
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        have hallows := selectionDirectivesAllowBool_eq_of_agree left right directives
          (by
            intro variableName hmember
            exact hagrees variableName (by
              simp [SelectionConditions.selectionBooleanVariables, hmember]))
        simp only [collectSelection]
        rw [hallows]
    | inlineFragment typeCondition directives selectionSet =>
        have hallows := selectionDirectivesAllowBool_eq_of_agree left right directives
          (by
            intro variableName hmember
            exact hagrees variableName (by
              simp [SelectionConditions.selectionBooleanVariables, hmember]))
        cases typeCondition with
        | none =>
            simp only [collectSelection]
            rw [hallows]
            split
            · exact collectFields_eq_of_boolean_agreement schema left right parentType source
                selectionSet (by
                  intro variableName hmember
                  exact hagrees variableName (by
                    simp [SelectionConditions.selectionBooleanVariables, hmember]))
            · rfl
        | some typeName =>
            simp only [collectSelection]
            rw [hallows]
            split
            · split
              · exact collectFields_eq_of_boolean_agreement schema left right parentType
                  source selectionSet (by
                    intro variableName hmember
                    exact hagrees variableName (by
                      simp [SelectionConditions.selectionBooleanVariables, hmember]))
              · rfl
            · rfl
end

theorem collectRuntimeFieldGroups_eq_of_boolean_agreement
    (schema : Schema) (left right : VariableValues)
    (parentType runtimeType : Name) (selectionSet : List Selection)
    (hagrees
      : ∀ variableName,
          variableName ∈ SelectionConditions.selectionSetBooleanVariables selectionSet
          -> inputValueBoolean? left (.variable variableName)
              = inputValueBoolean? right (.variable variableName))
    : collectRuntimeFieldGroups schema left parentType runtimeType selectionSet
      = collectRuntimeFieldGroups schema right parentType runtimeType selectionSet := by
  exact collectFields_eq_of_boolean_agreement schema left right parentType
    (.object runtimeType PUnit.unit) selectionSet hagrees

end QueryInclusion
end GraphQL
