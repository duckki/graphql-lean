import GraphQL.Theories.QueryInclusion
import Proofs.GraphQL.Theories.QueryInclusion.Support.Theories.SelectionConditions

/-! Supporting lemmas extracted from commit `7797374fd` for the talk exercises. -/

namespace GraphQL.QueryInclusion

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

theorem representativeBooleanValues_complete
    (variables : List Name) (variableValues : VariableValues)
    : boolVarsComplete variables
        (representativeBooleanValues variables variableValues) := by
  induction variables with
  | nil =>
      intro variableName hvariable
      simp at hvariable
  | cons head rest ih =>
      intro variableName hvariable
      by_cases hname : head = variableName
      · subst head
        refine ⟨
          (inputValueBoolean? variableValues (.variable variableName)).getD false,
          ?_
        ⟩
        simp [representativeBooleanValues, inputValueBoolean?, lookupVariableValue?,
          InputValue.staticBoolean?, ConstInputValue.toInputValue]
      · have hrest : variableName ∈ rest := by
          rcases List.mem_cons.mp hvariable with heq | hrest
          · exact False.elim (hname heq.symm)
          · exact hrest
        rcases ih variableName hrest with ⟨value, hvalue⟩
        refine ⟨value, ?_⟩
        simpa only [representativeBooleanValues, inputValueBoolean?,
          lookupVariableValue?, ite_eq_right hname] using hvalue

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

theorem directiveAllowsSelectionBool_skip_variable
    (variableValues : VariableValues) (variableName : Name)
    : directiveAllowsSelectionBool variableValues (.skip (.variable variableName))
      = !(inputValueBoolean? variableValues (.variable variableName) == some true) := by
  simp only [directiveAllowsSelectionBool]
  cases inputValueBoolean? variableValues (.variable variableName) with
  | none => rfl
  | some value => cases value <;> rfl

theorem directiveAllowsSelectionBool_include_variable
    (variableValues : VariableValues) (variableName : Name)
    : directiveAllowsSelectionBool variableValues (.include (.variable variableName))
      = (inputValueBoolean? variableValues (.variable variableName) == some true) := by
  simp only [directiveAllowsSelectionBool]
  cases inputValueBoolean? variableValues (.variable variableName) with
  | none => rfl
  | some value => cases value <;> rfl

theorem selectionDirectivesAllowBool_eq_of_agree
    (left right : VariableValues) (directives : List DirectiveApplication)
    (hagrees
      : ∀ variableName,
          variableName ∈ directives.filterMap QueryInclusion.directiveBooleanVariable?
          -> (inputValueBoolean? left (.variable variableName) == some true)
              = (inputValueBoolean? right (.variable variableName) == some true))
    : selectionDirectivesAllowBool left directives
      = selectionDirectivesAllowBool right directives := by
  induction directives with
  | nil => rfl
  | cons directive rest ih =>
      have hrest := ih (by
        intro variableName hmember
        apply hagrees variableName
        simp only [List.filterMap_cons]
        cases QueryInclusion.directiveBooleanVariable? directive <;> simp [hmember])
      have hdirective
          : directiveAllowsSelectionBool left directive
            = directiveAllowsSelectionBool right directive := by
        cases directive <;> rename_i argument <;> cases argument <;> try rfl
        case skip.variable variableName =>
          rw [directiveAllowsSelectionBool_skip_variable,
            directiveAllowsSelectionBool_skip_variable,
            hagrees variableName
              (by simp [QueryInclusion.directiveBooleanVariable?])]
        case include.variable variableName =>
          rw [directiveAllowsSelectionBool_include_variable,
            directiveAllowsSelectionBool_include_variable,
            hagrees variableName
              (by simp [QueryInclusion.directiveBooleanVariable?])]
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
            variableName ∈ QueryInclusion.selectionSetBooleanVariables selectionSet
            -> (inputValueBoolean? left (.variable variableName) == some true)
                = (inputValueBoolean? right (.variable variableName) == some true))
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
                simp [QueryInclusion.selectionSetBooleanVariables, hmember]))
        · exact collectFields_eq_of_boolean_agreement schema left right parentType source rest
            (by
              intro variableName hmember
              exact hagrees variableName (by
                simp [QueryInclusion.selectionSetBooleanVariables, hmember]))

  theorem collectSelection_eq_of_boolean_agreement
      (schema : Schema) (left right : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectRef)
      (selection : Selection)
      (hagrees
        : ∀ variableName,
            variableName ∈ QueryInclusion.selectionBooleanVariables selection
            -> (inputValueBoolean? left (.variable variableName) == some true)
                = (inputValueBoolean? right (.variable variableName) == some true))
      : collectSelection schema left parentType source selection
        = collectSelection schema right parentType source selection := by
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        have hallows := selectionDirectivesAllowBool_eq_of_agree left right directives
          (by
            intro variableName hmember
            exact hagrees variableName (by
              simp [QueryInclusion.selectionBooleanVariables, hmember]))
        simp only [collectSelection]
        rw [hallows]
    | inlineFragment typeCondition directives selectionSet =>
        have hallows := selectionDirectivesAllowBool_eq_of_agree left right directives
          (by
            intro variableName hmember
            exact hagrees variableName (by
              simp [QueryInclusion.selectionBooleanVariables, hmember]))
        cases typeCondition with
        | none =>
            simp only [collectSelection]
            rw [hallows]
            split
            · exact collectFields_eq_of_boolean_agreement schema left right parentType source
                selectionSet (by
                  intro variableName hmember
                  exact hagrees variableName (by
                    simp [QueryInclusion.selectionBooleanVariables, hmember]))
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
                      simp [QueryInclusion.selectionBooleanVariables, hmember]))
              · rfl
            · rfl
end

theorem inputValueBoolean?_representativeBooleanValues_effectiveEq
    (variables : List Name) (variableValues : VariableValues)
    (variableName : Name) (hvariable : variableName ∈ variables)
    : (inputValueBoolean? (representativeBooleanValues variables variableValues)
          (.variable variableName)
        == some true)
      = (inputValueBoolean? variableValues (.variable variableName) == some true) := by
  induction variables with
  | nil => simp at hvariable
  | cons head rest ih =>
      by_cases hname : head = variableName
      · subst head
        have hlookup
            : inputValueBoolean?
                (representativeBooleanValues (variableName :: rest) variableValues)
                (.variable variableName)
              = some
                  ((inputValueBoolean? variableValues
                      (.variable variableName)).getD
                    false) := by
          simp [representativeBooleanValues, inputValueBoolean?, lookupVariableValue?,
            InputValue.staticBoolean?, ConstInputValue.toInputValue]
        rw [hlookup]
        cases hvalue : inputValueBoolean? variableValues (.variable variableName) with
        | none => rfl
        | some value => cases value <;> rfl
      · have hrest : variableName ∈ rest := by
          rcases List.mem_cons.mp hvariable with heq | hrest
          · exact False.elim (hname heq.symm)
          · exact hrest
        have hskip
            : inputValueBoolean?
                (representativeBooleanValues (head :: rest) variableValues)
                (.variable variableName)
              = inputValueBoolean? (representativeBooleanValues rest variableValues)
                  (.variable variableName) := by
          simp [representativeBooleanValues, inputValueBoolean?, lookupVariableValue?,
            ite_eq_right hname]
        rw [hskip]
        exact ih hrest

end GraphQL.QueryInclusion
