import Proofs.GraphQL.Execution.ArgumentCoercion
import Proofs.GraphQL.Theories.ExecutionReadiness
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Uniqueness.GroundBridge
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Uniqueness.RestrictedSemantics

/-!
Validity and semantic equivalence of ground-normal bodies selected from complete-normal
Boolean branches.
-/

namespace GraphQL

namespace NormalForm

namespace CompleteNormalization

theorem completeNormalBooleanStem_body_valid_nonempty
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType : Name}
    : ∀ {boolCase : BoolCase} {selection : Selection} {body : List Selection},
        completeNormalBooleanStem boolCase selection body
        -> Validation.selectionValid schema variableDefinitions parentType selection
        -> Validation.selectionSetValid schema variableDefinitions parentType body
            ∧ body ≠ []
  | [], _selection, _body, hstem, _hvalid => by
      simp [completeNormalBooleanStem] at hstem
  | [(varName, value)],
      .inlineFragment none [directive] selectionSet, body, hstem, hvalid => by
      rcases hstem with ⟨hdirective, hbody⟩
      subst directive
      subst selectionSet
      simp [Validation.selectionValid] at hvalid
      exact ⟨hvalid.2.2, hvalid.2.1⟩
  | (varName, value) :: (nextVar, nextValue) :: rest,
      .inlineFragment none [directive] [child], body, hstem, hvalid => by
      rcases hstem with ⟨hdirective, hchildStem⟩
      subst directive
      have hchildValid :
          Validation.selectionValid schema variableDefinitions parentType
            child := by
        have hchildrenValid :=
          Validation.selectionValid_inlineFragment_none_selectionSetValid
            hvalid
        unfold Validation.selectionSetValid at hchildrenValid
        exact hchildrenValid child (by simp)
      exact completeNormalBooleanStem_body_valid_nonempty hchildStem
        hchildValid
  | _ :: _ :: _, .field _ _ _ _ _, _body, hstem, _hvalid => by
      simp [completeNormalBooleanStem] at hstem
  | _ :: _ :: _, .inlineFragment none [] _, _body, hstem, _hvalid => by
      simp [completeNormalBooleanStem] at hstem
  | _ :: _ :: _, .inlineFragment none (_ :: _ :: _) _, _body, hstem,
      _hvalid => by
      simp [completeNormalBooleanStem] at hstem
  | _ :: _ :: _, .inlineFragment (some _) _ _, _body, hstem, _hvalid => by
      simp [completeNormalBooleanStem] at hstem
  | [_], .field _ _ _ _ _, _body, hstem, _hvalid => by
      simp [completeNormalBooleanStem] at hstem
  | [_], .inlineFragment none [] _, _body, hstem, _hvalid => by
      simp [completeNormalBooleanStem] at hstem
  | [_], .inlineFragment none (_ :: _ :: _) _, _body, hstem, _hvalid => by
      simp [completeNormalBooleanStem] at hstem
  | [_], .inlineFragment (some _) _ _, _body, hstem, _hvalid => by
      simp [completeNormalBooleanStem] at hstem

private theorem completeNormalBooleanStem_body_valid_nonempty_of_mem
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType : Name} {selectionSet : List Selection}
    {boolCase : BoolCase} {selection : Selection} {body : List Selection}
    (hvalid
      : Validation.selectionSetValid schema variableDefinitions parentType selectionSet)
    (hmem : selection ∈ selectionSet)
    (hstem : completeNormalBooleanStem boolCase selection body)
    : Validation.selectionSetValid schema variableDefinitions parentType body
      ∧ body ≠ [] := by
  unfold Validation.selectionSetValid at hvalid
  exact completeNormalBooleanStem_body_valid_nonempty hstem
    (hvalid selection hmem)

private theorem completeNormalBooleanStem_body_argumentsCoercible
    {schema : Schema} {variableValues : Execution.VariableValues}
    {parentType : Name}
    : ∀ {boolCase : BoolCase} {selection : Selection} {body : List Selection},
        completeNormalBooleanStem boolCase selection body
        -> (∀ varName value,
              (varName, value) ∈ boolCase
              -> Execution.inputValueBoolean? variableValues (.variable varName)
                  = some value)
        -> selectionArgumentsCoercible schema variableValues parentType selection
        -> selectionSetArgumentsCoercible schema variableValues parentType body
  | [], _selection, _body, hstem, _hagrees, _hready => by
      simp [completeNormalBooleanStem] at hstem
  | [(varName, value)],
      .inlineFragment none [directive] selectionSet, body, hstem, hagrees, hready => by
      rcases hstem with ⟨hdirective, rfl⟩
      subst directive
      exact hready
        (selectionDirectivesAllowBool_boolCaseBit_of_agrees variableValues
          varName value (hagrees varName value (by simp))) trivial
  | (varName, value) :: (nextVar, nextValue) :: rest,
      .inlineFragment none [directive] [child], body, hstem, hagrees, hready => by
      rcases hstem with ⟨hdirective, hchildStem⟩
      subst directive
      have hchildReady :
          selectionArgumentsCoercible schema variableValues parentType child := by
        have hchildrenReady :
            selectionSetArgumentsCoercible schema variableValues parentType [child] := by
          exact hready
            (selectionDirectivesAllowBool_boolCaseBit_of_agrees variableValues
              varName value (hagrees varName value (by simp))) trivial
        exact hchildrenReady.1
      exact completeNormalBooleanStem_body_argumentsCoercible hchildStem
        (by
          intro candidate candidateValue hmem
          exact hagrees candidate candidateValue (by simp [hmem]))
        hchildReady
  | _ :: _ :: _, .field _ _ _ _ _, _body, hstem, _hagrees, _hready => by
      simp [completeNormalBooleanStem] at hstem
  | _ :: _ :: _, .inlineFragment none [] _, _body, hstem, _hagrees, _hready => by
      simp [completeNormalBooleanStem] at hstem
  | _ :: _ :: _, .inlineFragment none (_ :: _ :: _) _, _body, hstem,
      _hagrees, _hready => by
      simp [completeNormalBooleanStem] at hstem
  | _ :: _ :: _, .inlineFragment (some _) _ _, _body, hstem, _hagrees,
      _hready => by
      simp [completeNormalBooleanStem] at hstem
  | [_], .field _ _ _ _ _, _body, hstem, _hagrees, _hready => by
      simp [completeNormalBooleanStem] at hstem
  | [_], .inlineFragment none [] _, _body, hstem, _hagrees, _hready => by
      simp [completeNormalBooleanStem] at hstem
  | [_], .inlineFragment none (_ :: _ :: _) _, _body, hstem, _hagrees,
      _hready => by
      simp [completeNormalBooleanStem] at hstem
  | [_], .inlineFragment (some _) _ _, _body, hstem, _hagrees, _hready => by
      simp [completeNormalBooleanStem] at hstem

private theorem completeNormalBooleanStem_body_argumentsCoercible_of_mem
    {schema : Schema} {variableValues : Execution.VariableValues}
    {parentType : Name} {selectionSet : List Selection}
    {boolCase : BoolCase} {selection : Selection} {body : List Selection}
    (hready
      : selectionSetArgumentsCoercible schema variableValues parentType selectionSet)
    (hmem : selection ∈ selectionSet)
    {variables : List BoolVar}
    (hcomplete : completeNormalBoolCase variables boolCase)
    (hagrees : variableValuesAgreeWithCase variableValues boolCase variables)
    (hstem : completeNormalBooleanStem boolCase selection body)
    : selectionSetArgumentsCoercible schema variableValues parentType body := by
  exact completeNormalBooleanStem_body_argumentsCoercible hstem
    (by
      intro varName value hpair
      exact inputValueBoolean?_eq_of_agrees_completeNormalBoolCase
        hcomplete hagrees hpair)
    (selectionArgumentsCoercible_of_mem hready hmem)

private theorem variableValuesAgreeWithCase_coerceVariableValues
    (operation : Operation) {variables : List BoolVar} {boolCase : BoolCase}
    {variableValues : Execution.VariableValues}
    (hcomplete : completeNormalBoolCase variables boolCase)
    (hagrees : variableValuesAgreeWithCase variableValues boolCase variables)
    : variableValuesAgreeWithCase
        (Execution.coerceVariableValues operation variableValues) boolCase variables := by
  intro varName hmem
  have hcaseVar : varName ∈ boolCase.map Prod.fst :=
    (hcomplete.2.2 varName).2 hmem
  rcases List.mem_map.mp hcaseVar with
    ⟨⟨candidateVar, value⟩, hpair, hvarEq⟩
  change candidateVar = varName at hvarEq
  subst candidateVar
  have hlookup := BoolCase.lookup?_eq_of_pair_mem_nodup hcomplete.2.1 hpair
  have hvalue :
      Execution.inputValueBoolean? variableValues (.variable varName) = some value := by
    simpa [hlookup] using hagrees varName hmem
  exact (inputValueBoolean?_coerceVariableValues_eq_some operation variableValues
    hvalue).trans hlookup.symm

private theorem selectedCompleteNormalBodies_semanticallyEquivalent
    {schema : Schema} {leftOperation rightOperation : Operation}
    {parentType : Name}
    {leftVarName rightVarName : BoolVar}
    {leftVariables rightVariables : List BoolVar}
    {leftSelectionSet rightSelectionSet : List Selection}
    {leftPrepare rightPrepare : Execution.VariableValues -> Execution.VariableValues}
    {leftCase rightCase : BoolCase}
    {leftSelection rightSelection : Selection}
    {leftBody rightBody : List Selection}
    (hleftNormal
      : completeNormalSelectionSet schema
          (leftVarName :: leftVariables) parentType leftSelectionSet)
    (hrightNormal
      : completeNormalSelectionSet schema
          (rightVarName :: rightVariables) parentType rightSelectionSet)
    (hleftMem : leftSelection ∈ leftSelectionSet)
    (hrightMem : rightSelection ∈ rightSelectionSet)
    (hleftCase : completeNormalBoolCase (leftVarName :: leftVariables) leftCase)
    (hrightCase : completeNormalBoolCase (rightVarName :: rightVariables) rightCase)
    (_hequivalent : completeNormalBoolCasesEquivalent leftCase rightCase)
    (hleftStem : completeNormalBooleanStem leftCase leftSelection leftBody)
    (hrightStem : completeNormalBooleanStem rightCase rightSelection rightBody)
    (hleftFree : selectionSetDirectiveFree leftBody)
    (hrightFree : selectionSetDirectiveFree rightBody)
    (hsem
      : selectionSetsSemanticallyEquivalentForCompleteBoolVars schema
          (leftVarName :: leftVariables) leftOperation rightOperation
          leftPrepare rightPrepare parentType leftSelectionSet rightSelectionSet)
    : ∀ variableValues,
        boolVarsComplete (leftVarName :: leftVariables) variableValues
        -> operationArgumentsCoercible schema variableValues leftOperation
        -> operationArgumentsCoercible schema variableValues rightOperation
        -> variableValuesAgreeWithCase (leftPrepare variableValues)
            leftCase (leftVarName :: leftVariables)
        -> variableValuesAgreeWithCase (rightPrepare variableValues)
            rightCase (rightVarName :: rightVariables)
        ->  let leftValues := leftPrepare variableValues
            let rightValues := rightPrepare variableValues
            Execution.variableValuesCoercionEquivalent leftValues rightValues
            ∧ selectionSetsSemanticallyEquivalentAtVariableValues schema
                leftValues rightValues parentType leftBody rightBody := by
  intro variableValues hcomplete hleftReady hrightReady hagreesLeft hagreesRight
  let leftValues := leftPrepare variableValues
  let rightValues := rightPrepare variableValues
  have heffectiveValues :
      Execution.variableValuesCoercionEquivalent leftValues rightValues :=
    hsem.2.2.1 variableValues variableValues
      (Execution.variableValuesCoercionEquivalent_refl variableValues)
  refine ⟨heffectiveValues, ?_⟩
  intro ObjectRef resolvers fuel source hsource
  have hleftCollect :=
    collectFields_completeNormalSelectionSet_eq_body_of_equivalent_of_agrees
      schema leftValues parentType source hleftNormal hleftMem
      hleftCase hleftCase hagreesLeft
      (completeNormalBoolCasesEquivalent_refl leftCase) hleftStem hleftFree
  have hrightCollect :=
    collectFields_completeNormalSelectionSet_eq_body_of_equivalent_of_agrees
      schema rightValues parentType source hrightNormal hrightMem
      hrightCase hrightCase hagreesRight
      (completeNormalBoolCasesEquivalent_refl rightCase) hrightStem hrightFree
  have hleftExecute :=
    executeSelectionSet_eq_of_collectFields_eq schema resolvers leftValues fuel
      parentType source leftSelectionSet leftBody hleftCollect
  have hrightExecute :=
    executeSelectionSet_eq_of_collectFields_eq schema resolvers rightValues fuel
      parentType source rightSelectionSet rightBody hrightCollect
  have hleftResponse :
      Execution.executeSelectionSetAsResponse schema resolvers
          leftValues fuel parentType source leftBody
        =
      Execution.executeSelectionSetAsResponse schema resolvers
          leftValues fuel parentType source leftSelectionSet := by
    unfold Execution.executeSelectionSetAsResponse
    rw [← hleftExecute]
  have hrightResponse :
      Execution.executeSelectionSetAsResponse schema resolvers
          rightValues fuel parentType source rightBody
        =
      Execution.executeSelectionSetAsResponse schema resolvers
          rightValues fuel parentType source rightSelectionSet := by
    unfold Execution.executeSelectionSetAsResponse
    rw [← hrightExecute]
  rw [hleftResponse, hrightResponse]
  exact hsem.2.2.2 resolvers variableValues fuel source hcomplete
    hleftReady hrightReady hsource

private theorem selectedCompleteNormalBody_nil_semanticallyEquivalent
    {schema : Schema} {leftOperation rightOperation : Operation}
    {parentType : Name}
    {leftVarName rightVarName : BoolVar}
    {leftVariables rightVariables : List BoolVar}
    {leftSelectionSet rightSelectionSet : List Selection}
    {leftPrepare rightPrepare : Execution.VariableValues -> Execution.VariableValues}
    {runtimeCase : BoolCase} {leftSelection : Selection}
    {leftBody : List Selection}
    (hleftNormal
      : completeNormalSelectionSet schema
          (leftVarName :: leftVariables) parentType leftSelectionSet)
    (hrightNormal
      : completeNormalSelectionSet schema
          (rightVarName :: rightVariables) parentType rightSelectionSet)
    (hleftMem : leftSelection ∈ leftSelectionSet)
    (hruntimeLeft : completeNormalBoolCase (leftVarName :: leftVariables) runtimeCase)
    (hruntimeRight : completeNormalBoolCase (rightVarName :: rightVariables) runtimeCase)
    (hleftStem : completeNormalBooleanStem runtimeCase leftSelection leftBody)
    (hleftFree : selectionSetDirectiveFree leftBody)
    (hnone
      : ¬ ∃ selection candidate body,
            selection ∈ rightSelectionSet
            ∧ completeNormalBoolCase (rightVarName :: rightVariables) candidate
            ∧ completeNormalBooleanStem candidate selection body
            ∧ completeNormalBoolCasesEquivalent runtimeCase candidate)
    (hsem
      : selectionSetsSemanticallyEquivalentForCompleteBoolVars schema
          (leftVarName :: leftVariables) leftOperation rightOperation
          leftPrepare rightPrepare parentType leftSelectionSet rightSelectionSet)
    : ∀ baseValues,
        operationArgumentsCoercible schema
          (boolCaseVariableValues runtimeCase baseValues) leftOperation
        -> operationArgumentsCoercible schema
            (boolCaseVariableValues runtimeCase baseValues) rightOperation
        ->  let leftValues := leftPrepare (boolCaseVariableValues runtimeCase baseValues)
            let rightValues :=
              rightPrepare (boolCaseVariableValues runtimeCase baseValues)
            Execution.variableValuesCoercionEquivalent leftValues rightValues
            ∧ selectionSetsSemanticallyEquivalentAtVariableValues schema
                leftValues rightValues parentType leftBody [] := by
  intro baseValues hleftReady hrightReady
  let caseValues := boolCaseVariableValues runtimeCase baseValues
  let leftCaseValues := leftPrepare caseValues
  let rightCaseValues := rightPrepare caseValues
  have heffectiveValues :
      Execution.variableValuesCoercionEquivalent leftCaseValues
        rightCaseValues :=
    hsem.2.2.1 caseValues caseValues
      (Execution.variableValuesCoercionEquivalent_refl caseValues)
  refine ⟨heffectiveValues, ?_⟩
  intro ObjectRef resolvers fuel source hsource
  have hagreesLeft :
      variableValuesAgreeWithCase leftCaseValues runtimeCase
        (leftVarName :: leftVariables) := by
    intro name hmem
    rcases boolVarsComplete_boolCaseVariableValues baseValues hruntimeLeft
        name hmem with ⟨value, hvalue⟩
    have hprepared := hsem.1 caseValues name value hvalue
    exact hprepared.trans <| hvalue.symm.trans
      (variableValuesAgreeWithCase_boolCaseVariableValues baseValues
        hruntimeLeft name hmem)
  have hagreesRight :
      variableValuesAgreeWithCase rightCaseValues runtimeCase
        (rightVarName :: rightVariables) := by
    intro name hmem
    rcases boolVarsComplete_boolCaseVariableValues baseValues hruntimeRight
        name hmem with ⟨value, hvalue⟩
    have hprepared := hsem.2.1 caseValues name value hvalue
    exact hprepared.trans <| hvalue.symm.trans
      (variableValuesAgreeWithCase_boolCaseVariableValues baseValues
        hruntimeRight name hmem)
  have hleftCollect :=
    collectFields_completeNormalSelectionSet_eq_body_of_equivalent_of_agrees
      schema leftCaseValues parentType source hleftNormal hleftMem
      hruntimeLeft hruntimeLeft hagreesLeft
      (completeNormalBoolCasesEquivalent_refl runtimeCase) hleftStem hleftFree
  have hrightCollect :=
    collectFields_completeNormalSelectionSet_eq_nil_of_no_equivalent_of_agrees
      schema rightCaseValues parentType source hrightNormal hruntimeRight
      hagreesRight hnone
  have hleftExecute :=
    executeSelectionSet_eq_of_collectFields_eq schema resolvers leftCaseValues fuel
      parentType source leftSelectionSet leftBody hleftCollect
  have hrightExecute :=
    executeSelectionSet_eq_of_collectFields_eq schema resolvers rightCaseValues fuel
      parentType source rightSelectionSet [] hrightCollect
  have hleftResponse :
      Execution.executeSelectionSetAsResponse schema resolvers
          leftCaseValues fuel parentType source leftBody
        =
      Execution.executeSelectionSetAsResponse schema resolvers
          leftCaseValues fuel parentType source leftSelectionSet := by
    unfold Execution.executeSelectionSetAsResponse
    rw [← hleftExecute]
  have hrightResponse :
      Execution.executeSelectionSetAsResponse schema resolvers
          rightCaseValues fuel parentType source []
        =
      Execution.executeSelectionSetAsResponse schema resolvers
          rightCaseValues fuel parentType source rightSelectionSet := by
    unfold Execution.executeSelectionSetAsResponse
    rw [← hrightExecute]
  rw [hleftResponse, hrightResponse]
  exact hsem.2.2.2 resolvers caseValues fuel source
    (boolVarsComplete_boolCaseVariableValues baseValues hruntimeLeft)
    hleftReady hrightReady hsource

private theorem selectionSetEqualUpToReordering_eq_nil {selectionSet : List Selection}
    : SelectionSetEqualUpToReordering selectionSet [] -> selectionSet = [] := by
  intro hequal
  cases hequal with
  | paired pairs hleft hright _hpairs =>
      have hpairsNil : pairs = [] := by
        have hlength := hright.length_eq
        simp at hlength
        exact hlength
      subst pairs
      simp at hleft
      exact hleft

private theorem selectionSetEqualUpToReorderingWithCoercion_eq_nil
    {schema : Schema} {leftValues rightValues : Execution.VariableValues}
    {parentType : Name} {selectionSet : List Selection}
    : SelectionSetEqualUpToReorderingWithCoercion schema leftValues rightValues
        parentType selectionSet []
      -> selectionSet = [] := by
  intro hequal
  cases hequal with
  | paired pairs hleft hright _hpairs =>
      have hpairsNil : pairs = [] := by
        have hlength := hright.length_eq
        simp at hlength
        exact hlength
      subst pairs
      simp at hleft
      exact hleft

private theorem selectionSetNormal_nil (schema : Schema) (parentType : Name)
    : selectionSetNormal schema parentType [] := by
  simp [selectionSetNormal, selectionSetGroundTyped,
    selectionsAllFields, selectionsAllInlineFragments,
    selectionSetNonRedundant, responseNamesNodup,
    inlineFragmentTypeConditionsNodup]

private theorem completeNormalBoolCase_length_eq_variables
    {variables : List BoolVar} {boolCase : BoolCase}
    : completeNormalBoolCase variables boolCase
      -> boolCase.length = variables.length := by
  intro hcomplete
  have hperm : (boolCase.map Prod.fst).Perm variables :=
    GroundTypeNormalization.listPermOfNodupSubsetSubset
      hcomplete.2.1 hcomplete.1
      (fun varName hmem => (hcomplete.2.2 varName).1 hmem)
      (fun varName hmem => (hcomplete.2.2 varName).2 hmem)
  simpa using hperm.length_eq

private theorem wrapWithBoolCase_case_body_injective_of_length_eq
    : ∀ {leftCase rightCase : BoolCase} {leftBody rightBody : List Selection},
        leftCase.length = rightCase.length
        -> leftCase ≠ []
        -> wrapWithBoolCase leftCase leftBody = wrapWithBoolCase rightCase rightBody
        -> leftCase = rightCase ∧ leftBody = rightBody
  | [], _rightCase, _leftBody, _rightBody, _hlength, hleftNe, _hwrap => by
      exact False.elim (hleftNe rfl)
  | _leftCase, [], _leftBody, _rightBody, hlength, _hleftNe, _hwrap => by
      simp at hlength
      exact False.elim (_hleftNe hlength)
  | (leftVar, leftValue) :: leftRest,
      (rightVar, rightValue) :: rightRest,
      leftBody, rightBody, hlength, _hleftNe, hwrap => by
      simp [wrapWithBoolCase] at hwrap
      rcases hwrap with ⟨hdirective, hchildren⟩
      have hhead : (leftVar, leftValue) = (rightVar, rightValue) :=
        directiveForBit_injective hdirective
      cases hhead
      have hrestLength : leftRest.length = rightRest.length := by
        simpa using hlength
      cases leftRest with
      | nil =>
          cases rightRest with
          | nil =>
              simp [wrapWithBoolCase] at hchildren
              exact ⟨rfl, hchildren⟩
          | cons rightHead rightTail =>
              simp at hrestLength
      | cons leftHead leftTail =>
          cases rightRest with
          | nil =>
              simp at hrestLength
          | cons rightHead rightTail =>
              have hrecursive :=
                wrapWithBoolCase_case_body_injective_of_length_eq
                  hrestLength (by simp) hchildren
              exact ⟨by simp [hrecursive.1], hrecursive.2⟩

theorem completeNormalBooleanStem_case_body_eq
    {variables : List BoolVar} {leftCase rightCase : BoolCase}
    {selection : Selection} {leftBody rightBody : List Selection}
    (hleftCase : completeNormalBoolCase variables leftCase)
    (hrightCase : completeNormalBoolCase variables rightCase)
    (hvariablesNonempty : variables ≠ [])
    (hleftStem : completeNormalBooleanStem leftCase selection leftBody)
    (hrightStem : completeNormalBooleanStem rightCase selection rightBody)
    : leftCase = rightCase ∧ leftBody = rightBody := by
  have hleftLength := completeNormalBoolCase_length_eq_variables hleftCase
  have hrightLength := completeNormalBoolCase_length_eq_variables hrightCase
  have hcaseLength : leftCase.length = rightCase.length := by
    rw [hleftLength, hrightLength]
  have hleftNonempty : leftCase ≠ [] := by
    intro hnil
    have : leftCase.length = 0 := by simp [hnil]
    rw [hleftLength] at this
    have hvariablesNil : variables = [] := by
      simpa using this
    exact hvariablesNonempty hvariablesNil
  exact wrapWithBoolCase_case_body_injective_of_length_eq hcaseLength
    hleftNonempty (by
      rw [completeNormalBooleanStem_wrapWithBoolCase_eq hleftStem,
        completeNormalBooleanStem_wrapWithBoolCase_eq hrightStem])

def CompleteNormalSelectionMatch
    (schema : Schema) (leftOperation rightOperation : Operation)
    (leftVariables rightVariables : List BoolVar)
    (parentType : Name) (left right : Selection)
    : Prop :=
  ∃ leftCase rightCase leftBody rightBody,
    completeNormalBoolCase leftVariables leftCase
    ∧ completeNormalBoolCase rightVariables rightCase
    ∧ completeNormalBooleanStem leftCase left leftBody
    ∧ completeNormalBooleanStem rightCase right rightBody
    ∧ selectionSetNormal schema parentType leftBody
    ∧ selectionSetNormal schema parentType rightBody
    ∧ selectionSetDirectiveFree leftBody
    ∧ selectionSetDirectiveFree rightBody
    ∧ completeNormalBoolCasesEquivalent leftCase rightCase
    ∧ ∀ variableValues,
        operationArgumentsCoercible schema variableValues leftOperation
        -> operationArgumentsCoercible schema variableValues rightOperation
        -> boolVarsComplete leftVariables variableValues
        -> variableValuesAgreeWithCase
            (Execution.coerceVariableValues leftOperation variableValues)
            leftCase leftVariables
        -> variableValuesAgreeWithCase
            (Execution.coerceVariableValues rightOperation variableValues)
            rightCase rightVariables
        -> SelectionSetEqualUpToReorderingWithCoercion schema
            (Execution.coerceVariableValues leftOperation variableValues)
            (Execution.coerceVariableValues rightOperation variableValues)
            parentType leftBody rightBody

theorem completeNormalSelectionEqualUpToReordering_of_match
    {schema : Schema} {leftOperation rightOperation : Operation}
    {leftVariables rightVariables : List BoolVar}
    {parentType : Name} {left right : Selection}
    : CompleteNormalSelectionMatch schema leftOperation rightOperation
        leftVariables rightVariables parentType left right
      -> CompleteNormalSelectionEqualUpToReorderingWithCoercion schema
          leftOperation rightOperation parentType leftVariables rightVariables
          left right := by
  rintro ⟨leftCase, rightCase, leftBody, rightBody, hleftCase,
    hrightCase, hleftStem, hrightStem, _hleftNormal, _hrightNormal,
    _hleftFree, _hrightFree, hequivalent, hequal⟩
  exact ⟨leftCase, rightCase, leftBody, rightBody, hleftCase,
    hrightCase, hleftStem, hrightStem, hequivalent, hequal⟩

theorem completeNormalSelection_has_match
    {schema : Schema}
    {leftOperation rightOperation : Operation}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    {parentType : Name}
    {leftVarName rightVarName : BoolVar}
    {leftVariables rightVariables : List BoolVar}
    {leftSelectionSet rightSelectionSet : List Selection}
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hleftValid
      : Validation.selectionSetValid schema
          leftVariableDefinitions parentType leftSelectionSet)
    (hrightValid
      : Validation.selectionSetValid schema
          rightVariableDefinitions parentType rightSelectionSet)
    (hleftRoot : leftOperation.rootType schema = parentType)
    (hrightRoot : rightOperation.rootType schema = parentType)
    (hleftSelectionSet : leftOperation.selectionSet = leftSelectionSet)
    (hrightSelectionSet : rightOperation.selectionSet = rightSelectionSet)
    (hleftBoolVars : operationBoolVars leftOperation = leftVarName :: leftVariables)
    (hjoint : completeBoolCasesJointlyCoercible schema leftOperation rightOperation)
    (hleftNormal
      : completeNormalSelectionSet schema
          (leftVarName :: leftVariables) parentType leftSelectionSet)
    (hrightNormal
      : completeNormalSelectionSet schema
          (rightVarName :: rightVariables) parentType rightSelectionSet)
    (hcaseTransport
      : ∀ boolCase,
          completeNormalBoolCase (leftVarName :: leftVariables) boolCase
          -> completeNormalBoolCase (rightVarName :: rightVariables) boolCase)
    (hobject : objectTypeNameBool schema parentType = true)
    (hsem
      : selectionSetsSemanticallyEquivalentForCompleteBoolVars schema
          (leftVarName :: leftVariables) leftOperation rightOperation
          (Execution.coerceVariableValues leftOperation)
          (Execution.coerceVariableValues rightOperation) parentType
          leftSelectionSet rightSelectionSet)
    {leftSelection : Selection} (hleftMem : leftSelection ∈ leftSelectionSet)
    : ∃ rightSelection,
        rightSelection ∈ rightSelectionSet
        ∧ CompleteNormalSelectionMatch schema leftOperation rightOperation
            (leftVarName :: leftVariables) (rightVarName :: rightVariables)
            parentType leftSelection rightSelection := by
  have hleftShape := hleftNormal
  rcases hleftShape with ⟨_hleftVarsNodup, _hleftSetNodup,
    hleftBranches, _hleftUnique⟩
  have hrightShape := hrightNormal
  rcases hrightShape with ⟨_hrightVarsNodup, _hrightSetNodup,
    _hrightBranches, _hrightUnique⟩
  rcases hleftBranches leftSelection hleftMem with
    ⟨leftCase, leftBody, hleftCase, hleftStem, hleftBodyNormal,
      hleftBodyFree⟩
  have hleftReady :=
    completeNormalBooleanStem_body_valid_nonempty_of_mem hleftValid
      hleftMem hleftStem
  have hleftBodyValid := hleftReady.1
  have hleftBodyNonempty := hleftReady.2
  have hleftCaseRight := hcaseTransport leftCase hleftCase
  by_cases hmatch : ∃ rightSelection rightCase rightBody,
      rightSelection ∈ rightSelectionSet
        ∧ completeNormalBoolCase (rightVarName :: rightVariables) rightCase
        ∧ completeNormalBooleanStem rightCase rightSelection rightBody
        ∧ completeNormalBoolCasesEquivalent leftCase rightCase
        ∧ selectionSetNormal schema parentType rightBody
        ∧ selectionSetDirectiveFree rightBody
  · rcases hmatch with
      ⟨rightSelection, rightCase, rightBody, hrightMem, hrightCase,
        hrightStem, hequivalent, hrightBodyNormal, hrightBodyFree⟩
    have hrightReady :=
      completeNormalBooleanStem_body_valid_nonempty_of_mem hrightValid
        hrightMem hrightStem
    have hbodySem :=
      selectedCompleteNormalBodies_semanticallyEquivalent hleftNormal
        hrightNormal hleftMem hrightMem hleftCase hrightCase
        hequivalent hleftStem hrightStem hleftBodyFree hrightBodyFree hsem
    have hbodyEqual : ∀ variableValues,
        operationArgumentsCoercible schema variableValues leftOperation
        -> operationArgumentsCoercible schema variableValues rightOperation
        -> boolVarsComplete (leftVarName :: leftVariables) variableValues
        -> variableValuesAgreeWithCase
            (Execution.coerceVariableValues leftOperation variableValues)
            leftCase (leftVarName :: leftVariables)
        -> variableValuesAgreeWithCase
            (Execution.coerceVariableValues rightOperation variableValues)
            rightCase (rightVarName :: rightVariables)
        ->
        SelectionSetEqualUpToReorderingWithCoercion schema
          (Execution.coerceVariableValues leftOperation variableValues)
          (Execution.coerceVariableValues rightOperation variableValues)
          parentType leftBody rightBody := by
      intro variableValues hleftOperationReady hrightOperationReady hcomplete
        hagreesLeft hagreesRight
      have hselected := hbodySem variableValues hcomplete hleftOperationReady
        hrightOperationReady hagreesLeft hagreesRight
      have hleftSelectionSetReady :
          selectionSetArgumentsCoercible schema
            (Execution.coerceVariableValues leftOperation variableValues)
            parentType leftSelectionSet := by
        unfold operationArgumentsCoercible at hleftOperationReady
        simpa [hleftRoot, hleftSelectionSet] using hleftOperationReady
      have hrightSelectionSetReady :
          selectionSetArgumentsCoercible schema
            (Execution.coerceVariableValues rightOperation variableValues)
            parentType rightSelectionSet := by
        unfold operationArgumentsCoercible at hrightOperationReady
        simpa [hrightRoot, hrightSelectionSet] using hrightOperationReady
      have hleftCoercion :=
        completeNormalBooleanStem_body_argumentsCoercible_of_mem
          hleftSelectionSetReady hleftMem hleftCase hagreesLeft hleftStem
      have hrightCoercion :=
        completeNormalBooleanStem_body_argumentsCoercible_of_mem
          hrightSelectionSetReady hrightMem hrightCase hagreesRight hrightStem
      exact validNormalObjectSelectionSets_semanticallyEquivalent_equalUpToReordering
        hselected.1 hschema hleftBodyValid hrightReady.1 hleftCoercion
        hrightCoercion hleftBodyFree
        hrightBodyFree hleftBodyNormal hrightBodyNormal hobject hselected.2
    exact ⟨rightSelection, hrightMem, leftCase, rightCase, leftBody,
      rightBody, hleftCase, hrightCase, hleftStem, hrightStem,
      hleftBodyNormal, hrightBodyNormal, hleftBodyFree, hrightBodyFree,
      hequivalent, hbodyEqual⟩
  · have hnone : ¬ ∃ rightSelection rightCase rightBody,
        rightSelection ∈ rightSelectionSet
          ∧ completeNormalBoolCase (rightVarName :: rightVariables)
            rightCase
          ∧ completeNormalBooleanStem rightCase rightSelection rightBody
          ∧ completeNormalBoolCasesEquivalent leftCase rightCase := by
      intro hexists
      rcases hexists with
        ⟨rightSelection, rightCase, rightBody, hrightMem, hrightCase,
          hrightStem, hequivalent⟩
      have hrightShapeAgain := hrightNormal
      rcases hrightShapeAgain with
        ⟨_hrightVarsNodup, _hrightSetNodup, hrightBranches,
          _hrightUnique⟩
      rcases hrightBranches rightSelection hrightMem with
        ⟨normalCase, normalBody, hnormalCase, hnormalStem,
          hnormalBody, hnormalFree⟩
      have hcaseBodyEq := completeNormalBooleanStem_case_body_eq hrightCase
        hnormalCase (by simp) hrightStem hnormalStem
      cases hcaseBodyEq.1
      cases hcaseBodyEq.2
      exact hmatch ⟨rightSelection, rightCase, rightBody, hrightMem,
        hrightCase, hrightStem, hequivalent,
        hnormalBody, hnormalFree⟩
    have hbodyNilSem :=
      selectedCompleteNormalBody_nil_semanticallyEquivalent hleftNormal
        hrightNormal hleftMem hleftCase hleftCaseRight hleftStem
        hleftBodyFree hnone hsem
    have hleftCaseAtOperation :
        completeNormalBoolCase (operationBoolVars leftOperation) leftCase := by
      simpa [hleftBoolVars] using hleftCase
    rcases hjoint leftCase hleftCaseAtOperation with
      ⟨baseValues, hleftOperationReady, hrightOperationReady⟩
    have hselectedNil :=
      hbodyNilSem baseValues hleftOperationReady hrightOperationReady
    have hleftSelectionSetReady :
        selectionSetArgumentsCoercible schema
          (Execution.coerceVariableValues leftOperation
            (boolCaseVariableValues leftCase baseValues))
          parentType leftSelectionSet := by
      unfold operationArgumentsCoercible at hleftOperationReady
      simpa [hleftRoot, hleftSelectionSet] using hleftOperationReady
    have hleftCoercion :=
      completeNormalBooleanStem_body_argumentsCoercible_of_mem
        hleftSelectionSetReady hleftMem hleftCaseAtOperation
          (variableValuesAgreeWithCase_coerceVariableValues leftOperation
            hleftCaseAtOperation
            (variableValuesAgreeWithCase_boolCaseVariableValues baseValues
              hleftCaseAtOperation))
          hleftStem
    have hrightCoercion :
        selectionSetArgumentsCoercible schema
          (Execution.coerceVariableValues rightOperation
            (boolCaseVariableValues leftCase baseValues))
          parentType [] := by
      simp [selectionSetArgumentsCoercible]
    have hbodyNilEqual :=
      validNormalObjectSelectionSets_semanticallyEquivalent_equalUpToReordering
        (rightVariableDefinitions := rightVariableDefinitions)
        hselectedNil.1 hschema hleftBodyValid
        (by simp [Validation.selectionSetValid]) hleftCoercion hrightCoercion
        hleftBodyFree
        selectionSetDirectiveFree_nil hleftBodyNormal
        (selectionSetNormal_nil schema parentType) hobject hselectedNil.2
    exact False.elim
      (hleftBodyNonempty
        (selectionSetEqualUpToReorderingWithCoercion_eq_nil hbodyNilEqual))

theorem completeNormalSelectionMatch_left_unique
    {schema : Schema} {leftOperation rightOperation : Operation}
    {leftVariables rightVariables : List BoolVar}
    {parentType : Name} {leftSelectionSet : List Selection}
    (hleftNormal
      : completeNormalSelectionSet schema leftVariables parentType leftSelectionSet)
    (hleftVariablesNonempty : leftVariables ≠ [])
    (hrightVariablesNonempty : rightVariables ≠ [])
    {leftFirst leftSecond right : Selection}
    (hleftFirstMem : leftFirst ∈ leftSelectionSet)
    (hleftSecondMem : leftSecond ∈ leftSelectionSet)
    (hfirst
      : CompleteNormalSelectionMatch schema leftOperation rightOperation
          leftVariables rightVariables parentType leftFirst right)
    (hsecond
      : CompleteNormalSelectionMatch schema leftOperation rightOperation
          leftVariables rightVariables parentType leftSecond right)
    : leftFirst = leftSecond := by
  rcases hfirst with
    ⟨leftCaseFirst, rightCaseFirst, leftBodyFirst, rightBodyFirst,
      hleftCaseFirst, hrightCaseFirst, hleftStemFirst, hrightStemFirst,
      _hleftBodyFirstNormal, _hrightBodyFirstNormal, hleftBodyFirstFree,
      hrightBodyFirstFree, hequivalentFirst, _hbodyFirstEqual⟩
  rcases hsecond with
    ⟨leftCaseSecond, rightCaseSecond, leftBodySecond, rightBodySecond,
      hleftCaseSecond, hrightCaseSecond, hleftStemSecond, hrightStemSecond,
      _hleftBodySecondNormal, _hrightBodySecondNormal, hleftBodySecondFree,
      hrightBodySecondFree, hequivalentSecond, _hbodySecondEqual⟩
  have hrightCaseEq :=
    (completeNormalBooleanStem_case_body_eq hrightCaseFirst
      hrightCaseSecond hrightVariablesNonempty hrightStemFirst
      hrightStemSecond).1
  subst rightCaseSecond
  have hleftCasesEquivalent :
      completeNormalBoolCasesEquivalent leftCaseFirst leftCaseSecond :=
    completeNormalBoolCasesEquivalent_trans hequivalentFirst
      (completeNormalBoolCasesEquivalent_symm hequivalentSecond)
  unfold completeNormalSelectionSet at hleftNormal
  rcases hleftNormal with ⟨_hleftVariablesNodup, hleftShape⟩
  cases leftVariables with
  | nil => contradiction
  | cons leftHead leftTail =>
      rcases hleftShape with
        ⟨_hleftSetNodup, _hleftBranches, hleftUnique⟩
      exact hleftUnique leftFirst leftSecond leftCaseFirst leftCaseSecond
        leftBodyFirst leftBodySecond hleftFirstMem hleftSecondMem
        hleftCaseFirst hleftCaseSecond hleftStemFirst hleftStemSecond
        hleftBodyFirstFree hleftBodySecondFree hleftCasesEquivalent

theorem completeNormalSelectionMatch_reverse_right_unique
    {schema : Schema} {leftOperation rightOperation : Operation}
    {leftVariables rightVariables : List BoolVar}
    {parentType : Name} {rightSelectionSet : List Selection}
    (hrightNormal
      : completeNormalSelectionSet schema rightVariables parentType rightSelectionSet)
    (hleftVariablesNonempty : leftVariables ≠ [])
    (hrightVariablesNonempty : rightVariables ≠ [])
    {left rightForward rightReverse : Selection}
    (hrightForwardMem : rightForward ∈ rightSelectionSet)
    (hrightReverseMem : rightReverse ∈ rightSelectionSet)
    (hforward
      : CompleteNormalSelectionMatch schema leftOperation rightOperation
          leftVariables rightVariables parentType left rightForward)
    (hreverse
      : CompleteNormalSelectionMatch schema rightOperation leftOperation
          rightVariables leftVariables parentType rightReverse left)
    : rightForward = rightReverse := by
  rcases hforward with
    ⟨leftCaseForward, rightCaseForward, leftBodyForward,
      rightBodyForward, hleftCaseForward, hrightCaseForward,
      hleftStemForward, hrightStemForward, _hleftBodyForwardNormal,
      _hrightBodyForwardNormal, hleftBodyForwardFree,
      hrightBodyForwardFree, hequivalentForward,
      _hbodiesForwardEqual⟩
  rcases hreverse with
    ⟨rightCaseReverse, leftCaseReverse, rightBodyReverse,
      leftBodyReverse, hrightCaseReverse, hleftCaseReverse,
      hrightStemReverse, hleftStemReverse, _hrightBodyReverseNormal,
      _hleftBodyReverseNormal, hrightBodyReverseFree,
      hleftBodyReverseFree, hequivalentReverse,
      _hbodiesReverseEqual⟩
  have hleftCaseEq :=
    (completeNormalBooleanStem_case_body_eq hleftCaseForward
      hleftCaseReverse hleftVariablesNonempty hleftStemForward
      hleftStemReverse).1
  subst leftCaseReverse
  have hrightCasesEquivalent :
      completeNormalBoolCasesEquivalent rightCaseForward
        rightCaseReverse :=
    completeNormalBoolCasesEquivalent_trans
      (completeNormalBoolCasesEquivalent_symm hequivalentForward)
      (completeNormalBoolCasesEquivalent_symm hequivalentReverse)
  unfold completeNormalSelectionSet at hrightNormal
  rcases hrightNormal with ⟨_hrightVariablesNodup, hrightShape⟩
  cases rightVariables with
  | nil => contradiction
  | cons rightHead rightTail =>
      rcases hrightShape with
        ⟨_hrightSetNodup, _hrightBranches, hrightUnique⟩
      exact hrightUnique rightForward rightReverse rightCaseForward
        rightCaseReverse rightBodyForward rightBodyReverse hrightForwardMem
        hrightReverseMem hrightCaseForward hrightCaseReverse hrightStemForward
        hrightStemReverse hrightBodyForwardFree hrightBodyReverseFree
        hrightCasesEquivalent

end CompleteNormalization

end NormalForm

end GraphQL
