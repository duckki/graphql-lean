import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.DirectiveSemantics

/-!
BoolCase-wrapper facts for complete normalization.
-/

namespace GraphQL

namespace NormalForm

namespace CompleteNormalization

variable {ObjectRef : Type}

theorem wrapWithBoolCase_nil (selectionSet : List Selection)
    : wrapWithBoolCase [] selectionSet = selectionSet := by
  rfl

theorem wrapWithBoolCase_cons
    (varName : BoolVar) (value : Bool)
    (rest : BoolCase) (selectionSet : List Selection)
    : wrapWithBoolCase ((varName, value) :: rest) selectionSet
      = [.inlineFragment none [directiveForBit varName value]
          (wrapWithBoolCase rest selectionSet)] := by
  rfl

theorem wrapWithBoolCase_true_head
    (varName : BoolVar) (rest : BoolCase)
    (selectionSet : List Selection)
    : wrapWithBoolCase ((varName, true) :: rest) selectionSet
      = [.inlineFragment none [.include (.variable varName)]
          (wrapWithBoolCase rest selectionSet)] := by
  simp [wrapWithBoolCase, directiveForBit]

theorem wrapWithBoolCase_false_head
    (varName : BoolVar) (rest : BoolCase)
    (selectionSet : List Selection)
    : wrapWithBoolCase ((varName, false) :: rest) selectionSet
      = [.inlineFragment none [.skip (.variable varName)]
          (wrapWithBoolCase rest selectionSet)] := by
  simp [wrapWithBoolCase, directiveForBit]

theorem collectFields_wrapWithBoolCase_nil
    (schema : Schema)
    (variableValues : Execution.VariableValues)
    (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    (selectionSet : List Selection)
    : Execution.collectFields schema variableValues parentType source
        (wrapWithBoolCase [] selectionSet)
      = Execution.collectFields schema variableValues parentType source selectionSet := by
  rfl

theorem collectFields_wrapWithBoolCase_cons_allowed
    (schema : Schema)
    (variableValues : Execution.VariableValues)
    (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    (varName : BoolVar) (value : Bool) (rest : BoolCase)
    (selectionSet : List Selection)
    : Execution.selectionDirectivesAllowBool variableValues
          [directiveForBit varName value]
        = true
      -> Execution.collectFields schema variableValues parentType source
            (wrapWithBoolCase ((varName, value) :: rest) selectionSet)
          = Execution.collectFields schema variableValues parentType source
              (wrapWithBoolCase rest selectionSet) := by
  intro hallow
  simp [wrapWithBoolCase, Execution.collectFields,
    Execution.collectSelection, hallow, Execution.mergeExecutableGroups]

theorem collectFields_wrapWithBoolCase_cons_skipped
    (schema : Schema)
    (variableValues : Execution.VariableValues)
    (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    (varName : BoolVar) (value : Bool) (rest : BoolCase)
    (selectionSet : List Selection)
    : Execution.selectionDirectivesAllowBool variableValues
          [directiveForBit varName value]
        = false
      -> Execution.collectFields schema variableValues parentType source
            (wrapWithBoolCase ((varName, value) :: rest) selectionSet)
          = [] := by
  intro hallow
  simp [wrapWithBoolCase, Execution.collectFields,
    Execution.collectSelection, hallow, Execution.mergeExecutableGroups]

theorem selectionDirectivesAllowBool_boolCaseBit_of_agrees
    (variableValues : Execution.VariableValues)
    (varName : BoolVar) (value : Bool)
    : Execution.inputValueBoolean? variableValues (.variable varName) = some value
      -> Execution.selectionDirectivesAllowBool variableValues
            [directiveForBit varName value]
          = true := by
  intro hvalue
  cases value <;>
    simp [directiveForBit,
      Execution.selectionDirectivesAllowBool,
      Execution.directiveAllowsSelectionBool, hvalue]

theorem selectionDirectivesAllowBool_boolCaseBit_of_mismatch
    (variableValues : Execution.VariableValues)
    (varName : BoolVar) (value : Bool)
    : Execution.inputValueBoolean? variableValues (.variable varName) = some (!value)
      -> Execution.selectionDirectivesAllowBool variableValues
            [directiveForBit varName value]
          = false := by
  intro hvalue
  cases value <;>
    simp [directiveForBit,
      Execution.selectionDirectivesAllowBool,
      Execution.directiveAllowsSelectionBool, hvalue]

theorem collectFields_wrapWithBoolCase_cons_mismatch
    (schema : Schema)
    (variableValues : Execution.VariableValues)
    (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    (varName : BoolVar) (value : Bool) (rest : BoolCase)
    (selectionSet : List Selection)
    : Execution.inputValueBoolean? variableValues (.variable varName) = some (!value)
      -> Execution.collectFields schema variableValues parentType source
            (wrapWithBoolCase ((varName, value) :: rest) selectionSet)
          = [] := by
  intro hmismatch
  exact collectFields_wrapWithBoolCase_cons_skipped schema
    variableValues parentType source varName value rest selectionSet
    (selectionDirectivesAllowBool_boolCaseBit_of_mismatch variableValues
      varName value hmismatch)

theorem collectFields_wrapWithBoolCase_of_mismatch_pair
    (schema : Schema)
    (variableValues : Execution.VariableValues)
    (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    (selectionSet : List Selection)
    : ∀ boolCase : BoolCase,
        (varName : BoolVar)
        -> (value : Bool)
        -> (varName, value) ∈ boolCase
            -> Execution.inputValueBoolean? variableValues (.variable varName)
                = some (!value)
            -> Execution.collectFields schema variableValues parentType source
                  (wrapWithBoolCase boolCase selectionSet)
                = []
  | [], varName, value, hpair, _hmismatch => by
      cases hpair
  | (headVar, headValue) :: rest, varName, value, hpair, hmismatch => by
      simp at hpair
      rcases hpair with hhead | htail
      · have hvar : varName = headVar := hhead.1
        have hvalue : value = headValue := hhead.2
        subst varName
        subst value
        exact collectFields_wrapWithBoolCase_cons_mismatch
          schema variableValues parentType source headVar headValue rest
          selectionSet hmismatch
      · cases hallow :
          Execution.selectionDirectivesAllowBool variableValues
            [directiveForBit headVar headValue]
        · exact collectFields_wrapWithBoolCase_cons_skipped
            schema variableValues parentType source headVar headValue rest
            selectionSet hallow
        · have htailCollect :=
            collectFields_wrapWithBoolCase_of_mismatch_pair
              schema variableValues parentType source selectionSet rest
              varName value htail hmismatch
          exact
            (collectFields_wrapWithBoolCase_cons_allowed
              schema variableValues parentType source headVar headValue rest
              selectionSet hallow).trans htailCollect

theorem collectFields_wrapWithBoolCase_of_agrees
    (schema : Schema)
    (variableValues : Execution.VariableValues)
    (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    (selectionSet : List Selection)
    : ∀ boolCase : BoolCase,
        (∀ varName value,
          (varName, value) ∈ boolCase
          -> Execution.inputValueBoolean? variableValues (.variable varName) = some value)
        -> Execution.collectFields schema variableValues parentType source
              (wrapWithBoolCase boolCase selectionSet)
            = Execution.collectFields schema variableValues parentType source selectionSet
  | [], _hagrees => by
      rfl
  | (varName, value) :: rest, hagrees => by
      have hhead :
          Execution.selectionDirectivesAllowBool variableValues
              [directiveForBit varName value] = true :=
        selectionDirectivesAllowBool_boolCaseBit_of_agrees variableValues
          varName value (hagrees varName value (by simp))
      have hrest :
          Execution.collectFields schema variableValues parentType source
              (wrapWithBoolCase rest selectionSet)
            =
          Execution.collectFields schema variableValues parentType source
              selectionSet :=
        collectFields_wrapWithBoolCase_of_agrees schema
          variableValues parentType source selectionSet rest
          (by
            intro restVar restValue hmem
            exact hagrees restVar restValue (by simp [hmem]))
      exact
        (collectFields_wrapWithBoolCase_cons_allowed
          schema variableValues parentType source varName value rest
          selectionSet hhead).trans hrest

theorem collectFields_wrapWithBoolCase_of_variableValuesAgree
    (schema : Schema)
    (variableValues : Execution.VariableValues)
    (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    (variables : List BoolVar) (boolCase : BoolCase)
    (selectionSet : List Selection)
    : (∀ varName value,
        (varName, value) ∈ boolCase
        -> varName ∈ variables ∧ BoolCase.lookup? boolCase varName = some value)
      -> variableValuesAgreeWithCase variableValues boolCase variables
      -> Execution.collectFields schema variableValues parentType source
            (wrapWithBoolCase boolCase selectionSet)
          = Execution.collectFields schema variableValues parentType source
              selectionSet := by
  intro hcase hagrees
  exact
    collectFields_wrapWithBoolCase_of_agrees schema variableValues
      parentType source selectionSet boolCase
      (by
        intro varName value hmem
        rcases hcase varName value hmem with ⟨hvar, hvalue⟩
        exact (hagrees varName hvar).trans hvalue)

theorem collectFields_wrapWithBoolCase_of_mem_allBoolCases
    (schema : Schema)
    (variableValues : Execution.VariableValues)
    (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    (variables : List BoolVar) (boolCase : BoolCase)
    (selectionSet : List Selection)
    : variables.Nodup
      -> boolCase ∈ allBoolCases variables
      -> variableValuesAgreeWithCase variableValues boolCase variables
      -> Execution.collectFields schema variableValues parentType source
            (wrapWithBoolCase boolCase selectionSet)
          = Execution.collectFields schema variableValues parentType source
              selectionSet := by
  intro hnodup hmem hagrees
  exact
    collectFields_wrapWithBoolCase_of_variableValuesAgree schema
      variableValues parentType source variables boolCase selectionSet
      (by
        intro varName value hpair
        exact ⟨
          boolCase_pair_variable_mem_of_allBoolCases hmem hpair,
          BoolCase.lookup?_eq_of_pair_mem_allBoolCases_nodup
            hnodup hmem hpair⟩)
      hagrees

end CompleteNormalization

end NormalForm

end GraphQL
