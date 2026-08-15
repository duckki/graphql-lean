import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Variables

/-!
Directive evaluation facts for complete normalization boolCases.
-/

namespace GraphQL

namespace NormalForm

namespace CompleteNormalization

theorem inputValueBoolIn?_literal (boolCase : BoolCase) (value : Bool)
    : inputValueBoolIn? boolCase (.boolean value) = some value := by
  rfl

theorem inputValueBoolIn?_variable (boolCase : BoolCase) (varName : BoolVar)
    : inputValueBoolIn? boolCase (.variable varName)
      = BoolCase.lookup? boolCase varName := by
  rfl

theorem directiveAllowsIn_skip_variable_true (boolCase : BoolCase) (varName : BoolVar)
    : BoolCase.lookup? boolCase varName = some true
      -> directiveAllowsIn boolCase (.skip (.variable varName)) = false := by
  intro hvalue
  simp [directiveAllowsIn,
    inputValueBoolIn?, hvalue]

theorem directiveAllowsIn_skip_variable_false (boolCase : BoolCase) (varName : BoolVar)
    : BoolCase.lookup? boolCase varName = some false
      -> directiveAllowsIn boolCase (.skip (.variable varName)) = true := by
  intro hvalue
  simp [directiveAllowsIn,
    inputValueBoolIn?, hvalue]

theorem directiveAllowsIn_include_variable_true (boolCase : BoolCase) (varName : BoolVar)
    : BoolCase.lookup? boolCase varName = some true
      -> directiveAllowsIn boolCase (.include (.variable varName)) = true := by
  intro hvalue
  simp [directiveAllowsIn,
    inputValueBoolIn?, hvalue]

theorem directiveAllowsIn_include_variable_false (boolCase : BoolCase) (varName : BoolVar)
    : BoolCase.lookup? boolCase varName = some false
      -> directiveAllowsIn boolCase (.include (.variable varName)) = false := by
  intro hvalue
  simp [directiveAllowsIn,
    inputValueBoolIn?, hvalue]

def variableValuesAgreeWithCase
    (variableValues : Execution.VariableValues)
    (boolCase : BoolCase)
    (variables : List BoolVar)
    : Prop :=
  ∀ varName,
    varName ∈ variables
    -> Execution.inputValueBoolean? variableValues (.variable varName)
        = BoolCase.lookup? boolCase varName

theorem inputValueBoolInCase_eq_execution
    (variableValues : Execution.VariableValues)
    (boolCase : BoolCase)
    (variables : List BoolVar)
    (hagrees : variableValuesAgreeWithCase variableValues boolCase variables)
    : ∀ value,
        (∀ varName, varName ∈ inputValueBooleanVariables value -> varName ∈ variables)
        -> inputValueBoolIn? boolCase value
            = Execution.inputValueBoolean? variableValues value
  | .variable varName, hvars => by
      exact (hagrees varName
        (hvars varName (by simp [inputValueBooleanVariables]))).symm
  | .list values, _hvars => by
      rfl
  | .object fields, _hvars => by
      rfl
  | .null, _hvars => by
      rfl
  | .int value, _hvars => by
      rfl
  | .float value, _hvars => by
      rfl
  | .string value, _hvars => by
      rfl
  | .boolean value, _hvars => by
      rfl
  | .enum value, _hvars => by
      rfl

theorem directiveAllowsInCase_eq_execution
    (variableValues : Execution.VariableValues)
    (boolCase : BoolCase)
    (variables : List BoolVar)
    (hagrees : variableValuesAgreeWithCase variableValues boolCase variables)
    : ∀ directive,
        (∀ varName, varName ∈ directiveBooleanVariables directive -> varName ∈ variables)
        -> directiveAllowsIn boolCase directive
            = Execution.directiveAllowsSelectionBool variableValues directive
  | .skip ifArgument, hvars => by
      rw [directiveAllowsIn,
        Execution.directiveAllowsSelectionBool]
      rw [inputValueBoolInCase_eq_execution variableValues
        boolCase variables hagrees ifArgument hvars]
      rfl
  | .include ifArgument, hvars => by
      rw [directiveAllowsIn,
        Execution.directiveAllowsSelectionBool]
      rw [inputValueBoolInCase_eq_execution variableValues
        boolCase variables hagrees ifArgument hvars]
      rfl

theorem directivesAllowInCase_eq_execution
    (variableValues : Execution.VariableValues)
    (boolCase : BoolCase)
    (variables : List BoolVar)
    (directiveApplications : List DirectiveApplication)
    (hagrees : variableValuesAgreeWithCase variableValues boolCase variables)
    (hvars
      : ∀ varName,
          varName ∈ directivesBooleanVariables directiveApplications
          -> varName ∈ variables)
    : directivesAllowIn boolCase directiveApplications
      = Execution.selectionDirectivesAllowBool variableValues directiveApplications := by
  induction directiveApplications with
  | nil =>
      simp [directivesAllowIn,
        Execution.selectionDirectivesAllowBool]
  | cons directive rest ih =>
      have hdirective :
          directiveAllowsIn boolCase directive =
            Execution.directiveAllowsSelectionBool variableValues directive := by
        exact directiveAllowsInCase_eq_execution variableValues
          boolCase variables hagrees directive
          (by
            intro varName hmem
            exact hvars varName
              (by simp [directivesBooleanVariables, hmem]))
      have hrest :
          directivesAllowIn boolCase rest =
            Execution.selectionDirectivesAllowBool variableValues rest := by
        exact ih
          (by
            intro varName hmem
            exact hvars varName
              (by simp [directivesBooleanVariables, hmem]))
      change (directiveAllowsIn boolCase directive && directivesAllowIn boolCase rest)
              = (Execution.directiveAllowsSelectionBool variableValues directive
                  && Execution.selectionDirectivesAllowBool variableValues rest)
      rw [hdirective, hrest]

theorem allBoolCases_complete_for_variableValues
    (variableValues : Execution.VariableValues)
    (variables : List BoolVar)
    : (∀ varName,
        varName ∈ variables
        -> ∃ value,
            Execution.inputValueBoolean? variableValues (.variable varName) = some value)
      -> ∃ boolCase,
          boolCase ∈ allBoolCases variables
          ∧ variableValuesAgreeWithCase variableValues boolCase variables := by
  intro hcomplete
  rcases
      allBoolCases_complete
        (variables := variables)
        (f := fun varName =>
          Execution.inputValueBoolean? variableValues (.variable varName))
        hcomplete with
    ⟨boolCase, hcase, hagrees⟩
  exact ⟨boolCase, hcase, by
    intro varName hmem
    exact (hagrees varName hmem).symm⟩

theorem allBoolCases_variableValuesAgree_unique
    (variableValues : Execution.VariableValues)
    : ∀ {variables left right},
        variables.Nodup
        -> left ∈ allBoolCases variables
        -> right ∈ allBoolCases variables
        -> variableValuesAgreeWithCase variableValues left variables
        -> variableValuesAgreeWithCase variableValues right variables
        -> left = right
  | [], left, right, _hnodup, hleft, hright, _hleftAgree,
      _hrightAgree => by
      simp [allBoolCases] at hleft hright
      subst left
      subst right
      rfl
  | headVar :: restVars, left, right, hnodup, hleft, hright,
      hleftAgree, hrightAgree => by
      have hnodupParts := List.nodup_cons.mp hnodup
      have hheadNotMem : headVar ∉ restVars := hnodupParts.1
      have hrestNodup : restVars.Nodup := hnodupParts.2
      simp [allBoolCases] at hleft hright
      rcases hleft with hleft | hleft
      · rcases hleft with ⟨leftRest, hleftRestMem, hleftEq⟩
        subst left
        rcases hright with hright | hright
        · rcases hright with ⟨rightRest, hrightRestMem, hrightEq⟩
          subst right
          have hleftRestAgree :
              variableValuesAgreeWithCase variableValues leftRest
                restVars := by
            intro varName hmem
            have hneq : headVar ≠ varName := by
              intro heq
              subst varName
              exact hheadNotMem hmem
            have hagree :=
              hleftAgree varName (by simp [hmem])
            simpa [BoolCase.lookup?, hneq] using hagree
          have hrightRestAgree :
              variableValuesAgreeWithCase variableValues rightRest
                restVars := by
            intro varName hmem
            have hneq : headVar ≠ varName := by
              intro heq
              subst varName
              exact hheadNotMem hmem
            have hagree :=
              hrightAgree varName (by simp [hmem])
            simpa [BoolCase.lookup?, hneq] using hagree
          have hrestEq :=
            allBoolCases_variableValuesAgree_unique variableValues
              hrestNodup hleftRestMem hrightRestMem hleftRestAgree
              hrightRestAgree
          simp [hrestEq]
        · rcases hright with ⟨rightRest, _hrightRestMem, hrightEq⟩
          subst right
          have hleftHead := hleftAgree headVar (by simp)
          have hrightHead := hrightAgree headVar (by simp)
          simp [BoolCase.lookup?] at hleftHead hrightHead
          have hcontra : some false = some true :=
            hleftHead.symm.trans hrightHead
          cases hcontra
      · rcases hleft with ⟨leftRest, hleftRestMem, hleftEq⟩
        subst left
        rcases hright with hright | hright
        · rcases hright with ⟨rightRest, _hrightRestMem, hrightEq⟩
          subst right
          have hleftHead := hleftAgree headVar (by simp)
          have hrightHead := hrightAgree headVar (by simp)
          simp [BoolCase.lookup?] at hleftHead hrightHead
          have hcontra : some true = some false :=
            hleftHead.symm.trans hrightHead
          cases hcontra
        · rcases hright with ⟨rightRest, hrightRestMem, hrightEq⟩
          subst right
          have hleftRestAgree :
              variableValuesAgreeWithCase variableValues leftRest
                restVars := by
            intro varName hmem
            have hneq : headVar ≠ varName := by
              intro heq
              subst varName
              exact hheadNotMem hmem
            have hagree :=
              hleftAgree varName (by simp [hmem])
            simpa [BoolCase.lookup?, hneq] using hagree
          have hrightRestAgree :
              variableValuesAgreeWithCase variableValues rightRest
                restVars := by
            intro varName hmem
            have hneq : headVar ≠ varName := by
              intro heq
              subst varName
              exact hheadNotMem hmem
            have hagree :=
              hrightAgree varName (by simp [hmem])
            simpa [BoolCase.lookup?, hneq] using hagree
          have hrestEq :=
            allBoolCases_variableValuesAgree_unique variableValues
              hrestNodup hleftRestMem hrightRestMem hleftRestAgree
              hrightRestAgree
          simp [hrestEq]

theorem allBoolCases_mismatch_of_ne_agree (variableValues : Execution.VariableValues)
    : ∀ {variables left right},
        variables.Nodup
        -> left ∈ allBoolCases variables
        -> right ∈ allBoolCases variables
        -> variableValuesAgreeWithCase variableValues left variables
        -> right ≠ left
        -> ∃ varName value,
            (varName, value) ∈ right
            ∧ Execution.inputValueBoolean? variableValues (.variable varName)
              = some (!value)
  | [], left, right, _hnodup, hleft, hright, _hagrees, hne => by
      simp [allBoolCases] at hleft hright
      subst left
      subst right
      exact False.elim (hne rfl)
  | headVar :: restVars, left, right, hnodup, hleft, hright, hagrees,
      hne => by
      have hnodupParts := List.nodup_cons.mp hnodup
      have hheadNotMem : headVar ∉ restVars := hnodupParts.1
      have hrestNodup : restVars.Nodup := hnodupParts.2
      simp [allBoolCases] at hleft hright
      rcases hleft with hleft | hleft
      · rcases hleft with ⟨leftRest, hleftRestMem, hleftEq⟩
        subst left
        have hleftHead :
            Execution.inputValueBoolean? variableValues (.variable headVar)
              =
            some false := by
          simpa [BoolCase.lookup?] using hagrees headVar (by simp)
        have hleftRestAgree :
            variableValuesAgreeWithCase variableValues leftRest
              restVars := by
          intro varName hmem
          have hneq : headVar ≠ varName := by
            intro heq
            subst varName
            exact hheadNotMem hmem
          have hagree := hagrees varName (by simp [hmem])
          simpa [BoolCase.lookup?, hneq] using hagree
        rcases hright with hright | hright
        · rcases hright with ⟨rightRest, hrightRestMem, hrightEq⟩
          subst right
          have htailNe : rightRest ≠ leftRest := by
            intro htailEq
            apply hne
            simp [htailEq]
          rcases
              allBoolCases_mismatch_of_ne_agree variableValues
                hrestNodup hleftRestMem hrightRestMem hleftRestAgree
                htailNe with
            ⟨varName, value, hpair, hmismatch⟩
          exact ⟨varName, value, by simp [hpair], hmismatch⟩
        · rcases hright with ⟨rightRest, _hrightRestMem, hrightEq⟩
          subst right
          exact ⟨headVar, true, by simp, by simpa using hleftHead⟩
      · rcases hleft with ⟨leftRest, hleftRestMem, hleftEq⟩
        subst left
        have hleftHead :
            Execution.inputValueBoolean? variableValues (.variable headVar)
              =
            some true := by
          simpa [BoolCase.lookup?] using hagrees headVar (by simp)
        have hleftRestAgree :
            variableValuesAgreeWithCase variableValues leftRest
              restVars := by
          intro varName hmem
          have hneq : headVar ≠ varName := by
            intro heq
            subst varName
            exact hheadNotMem hmem
          have hagree := hagrees varName (by simp [hmem])
          simpa [BoolCase.lookup?, hneq] using hagree
        rcases hright with hright | hright
        · rcases hright with ⟨rightRest, _hrightRestMem, hrightEq⟩
          subst right
          exact ⟨headVar, false, by simp, by simpa using hleftHead⟩
        · rcases hright with ⟨rightRest, hrightRestMem, hrightEq⟩
          subst right
          have htailNe : rightRest ≠ leftRest := by
            intro htailEq
            apply hne
            simp [htailEq]
          rcases
              allBoolCases_mismatch_of_ne_agree variableValues
                hrestNodup hleftRestMem hrightRestMem hleftRestAgree
                htailNe with
            ⟨varName, value, hpair, hmismatch⟩
          exact ⟨varName, value, by simp [hpair], hmismatch⟩

end CompleteNormalization

end NormalForm

end GraphQL
