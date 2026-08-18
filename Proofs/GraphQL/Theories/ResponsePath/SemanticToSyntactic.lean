import Proofs.GraphQL.Theories.ResponsePath.ReferenceChecker
import Proofs.GraphQL.Theories.QueryInclusion.Soundness

/-! The semantic-to-syntactic correspondence direction of path-based query inclusion. -/

namespace GraphQL
namespace ResponsePath

open Execution
open QueryInclusion

-- The explicit Boolean case induced by one complete Boolean environment over a fixed
-- variable list. Variables without a Boolean value in the environment are dropped.
def booleanAssignmentOf (conditionValues : VariableValues) (variables : List Name)
    : BoolCase :=
  variables.filterMap
    fun variableName =>
      (inputValueBoolean? conditionValues (.variable variableName)).map
        fun value => (variableName, value)

-- The induced Boolean case reproduces every Boolean value the source environment
-- assigns to a listed variable.
theorem booleanAssignmentOf_inputValueBoolean? (conditionValues : VariableValues)
    : ∀ (variables : List Name) (variableName : Name) (value : Bool),
        variableName ∈ variables
        -> inputValueBoolean? conditionValues (.variable variableName) = some value
        -> inputValueBoolean?
              (boolCaseVariableValues (booleanAssignmentOf conditionValues variables))
              (.variable variableName)
            = some value
  | [], _variableName, _value, hmem, _hvalue => by cases hmem
  | candidate :: rest, variableName, value, hmem, hvalue => by
      cases hcandidate : inputValueBoolean? conditionValues (.variable candidate) with
      | none =>
          have hne : variableName ≠ candidate := by
            intro heq
            rw [heq, hcandidate] at hvalue
            cases hvalue
          have hrest : variableName ∈ rest := by
            rcases List.mem_cons.mp hmem with heq | hrest
            · exact absurd heq hne
            · exact hrest
          have hexpand : booleanAssignmentOf conditionValues (candidate :: rest)
              = booleanAssignmentOf conditionValues rest := by
            simp [booleanAssignmentOf, List.filterMap_cons, hcandidate]
          rw [hexpand]
          exact booleanAssignmentOf_inputValueBoolean? conditionValues rest variableName
            value hrest hvalue
      | some candidateValue =>
          have hexpand : booleanAssignmentOf conditionValues (candidate :: rest)
              = (candidate, candidateValue) :: booleanAssignmentOf conditionValues rest
              := by
            simp [booleanAssignmentOf, List.filterMap_cons, hcandidate]
          rw [hexpand]
          by_cases heq : candidate = variableName
          · subst heq
            rw [hcandidate] at hvalue
            injection hvalue with hvalueEq
            subst hvalueEq
            simp [boolCaseVariableValues, inputValueBoolean?, lookupVariableValue?,
              ConstInputValue.toInputValue, InputValue.staticBoolean?]
          · have hrest : variableName ∈ rest := by
              rcases List.mem_cons.mp hmem with heqName | hrest
              · exact absurd heqName.symm heq
              · exact hrest
            have hstep := booleanAssignmentOf_inputValueBoolean? conditionValues rest
              variableName value hrest hvalue
            simpa [boolCaseVariableValues, inputValueBoolean?, lookupVariableValue?,
              heq] using hstep

-- The induced Boolean case stays complete for the listed variables.
theorem booleanAssignmentOf_boolVarsComplete
    (conditionValues : VariableValues) (variables : List Name)
    (hcomplete : boolVarsComplete variables conditionValues)
    : boolVarsComplete variables
        (boolCaseVariableValues (booleanAssignmentOf conditionValues variables)) := by
  intro variableName hmem
  rcases hcomplete variableName hmem with ⟨value, hvalue⟩
  exact ⟨value, booleanAssignmentOf_inputValueBoolean? conditionValues variables
    variableName value hmem hvalue⟩

-- On the listed variables, the induced Boolean case agrees with the source environment.
theorem booleanAssignmentOf_agrees
    (conditionValues : VariableValues) (variables : List Name)
    (hcomplete : boolVarsComplete variables conditionValues)
    (variableName : Name) (hmem : variableName ∈ variables)
    : inputValueBoolean?
        (boolCaseVariableValues (booleanAssignmentOf conditionValues variables))
        (.variable variableName)
      = inputValueBoolean? conditionValues (.variable variableName) := by
  rcases hcomplete variableName hmem with ⟨value, hvalue⟩
  rw [hvalue]
  exact booleanAssignmentOf_inputValueBoolean? conditionValues variables variableName
    value hmem hvalue

-- Query-only operations share the schema query root.
theorem rootType_eq (schema : Schema) (left right : Operation)
    : left.rootType schema = right.rootType schema := by
  cases hleft : left.operationType
  cases hright : right.operationType
  simp [Operation.rootType, hleft, hright, OperationType.rootType]

-- For valid operations under a well-formed schema, path-based syntactic inclusion
-- implies semantic query inclusion. Witnesses `ResponsePath.IncludesSemanticToSyntactic`.
theorem includesSemanticToSyntactic {schema : Schema} {left right : Operation}
    : IncludesSemanticToSyntactic schema left right := by
  intro hschema hleftValid hrightValid hpath
  have hroot : left.rootType schema = right.rootType schema :=
    rootType_eq schema left right
  refine QueryInclusion.includes_of_selectionSetChecks hschema hleftValid hrightValid
    hroot hpath.1 ?_
  intro conditionValues hcomplete
  let conditionVariables :=
    comparisonConditionVariables left.selectionSet right.selectionSet
  let assignment := booleanAssignmentOf conditionValues conditionVariables
  have hassignComplete : boolVarsComplete conditionVariables
      (boolCaseVariableValues assignment) :=
    booleanAssignmentOf_boolVarsComplete conditionValues conditionVariables hcomplete
  have hrightObject : schema.objectType (right.rootType schema) :=
    NormalForm.CompleteNormalization.operation_root_object_of_valid hschema hrightValid
  have hrootSingleton := getPossibleTypes_eq_singleton_of_object schema hrightObject
  have hpaths : ∀ step rest,
      step.parentObject = right.rootType schema
      -> collectedFieldsSelectPath schema (boolCaseVariableValues assignment)
          (collectFields schema (boolCaseVariableValues assignment)
            (right.rootType schema) (.object (right.rootType schema) PUnit.unit)
            right.selectionSet)
          (step :: rest)
      -> collectedFieldsSelectPath schema (boolCaseVariableValues assignment)
          (collectFields schema (boolCaseVariableValues assignment)
            (right.rootType schema) (.object (right.rootType schema) PUnit.unit)
            left.selectionSet)
          (step :: rest) := by
    intro step rest hscope hrightSel
    have hrootIncl : schema.typeIncludesObject (right.rootType schema)
        step.parentObject := by
      rw [hscope]
      show right.rootType schema ∈ schema.getPossibleTypes (right.rootType schema)
      rw [hrootSingleton]
      simp
    have hrightOp : operationSelectsPath schema right assignment (step :: rest) := by
      refine ⟨hrootIncl, ?_⟩
      rw [hscope]
      exact hrightSel
    have hleftOp := hpath.2 assignment hassignComplete (step :: rest) hrightOp
    have hleftSel := hleftOp.2
    rw [hroot, hscope] at hleftSel
    exact hleftSel
  have haccept := selectionSetIncludesBoolWithFuel_of_pathInclusion schema hschema
    (boolCaseVariableValues assignment) (right.size + 1) (right.rootType schema)
    left.selectionSet right.selectionSet hrightObject
    (by
      rw [← hroot]
      exact
        NormalForm.CompleteNormalization.operation_selectionSetSemanticsReady_of_valid
          hschema hleftValid)
    (by
      rw [← hroot]
      exact Validation.operationDefinitionValid_fieldsInSetCanMerge hleftValid)
    (NormalForm.CompleteNormalization.operation_selectionSetSemanticsReady_of_valid
      hschema hrightValid)
    (Validation.operationDefinitionValid_fieldsInSetCanMerge hrightValid)
    (Nat.le_succ_of_le (Execution.selectionSetResponseDepth_le_size right.selectionSet))
    hpaths
  have hagreeLeft : ∀ variableName,
      variableName ∈ SelectionConditions.selectionSetBooleanVariables left.selectionSet
      -> inputValueBoolean? (boolCaseVariableValues assignment) (.variable variableName)
          = inputValueBoolean? conditionValues (.variable variableName) := by
    intro variableName hvariable
    apply booleanAssignmentOf_agrees conditionValues conditionVariables hcomplete
    simp [conditionVariables, comparisonConditionVariables, List.mem_eraseDups,
      hvariable]
  have hagreeRight : ∀ variableName,
      variableName ∈ SelectionConditions.selectionSetBooleanVariables right.selectionSet
      -> inputValueBoolean? (boolCaseVariableValues assignment) (.variable variableName)
          = inputValueBoolean? conditionValues (.variable variableName) := by
    intro variableName hvariable
    apply booleanAssignmentOf_agrees conditionValues conditionVariables hcomplete
    simp [conditionVariables, comparisonConditionVariables, List.mem_eraseDups,
      hvariable]
  have heq := selectionSetIncludesBoolWithFuel_eq_of_boolean_agreement schema
    (right.size + 1) (right.rootType schema) (boolCaseVariableValues assignment)
    conditionValues left.selectionSet right.selectionSet
    (fun variableName hvariable => by rw [hagreeLeft variableName hvariable])
    (fun variableName hvariable => by rw [hagreeRight variableName hvariable])
  rw [← heq]
  exact haccept

end ResponsePath
end GraphQL
