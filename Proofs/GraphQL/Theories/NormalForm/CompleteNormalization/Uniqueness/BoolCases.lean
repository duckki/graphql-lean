import Proofs.GraphQL.Execution.ArgumentCoercion
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.OperationNormality
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.SyntaxDiff

/-!
Boolean-case assignments used to isolate complete-normal root branches.
-/

namespace GraphQL

namespace NormalForm

namespace CompleteNormalization

theorem BoolCase.lookup?_eq_of_pair_mem_nodup
    {boolCase : BoolCase} {varName : BoolVar} {value : Bool}
    (hnodup : (boolCase.map Prod.fst).Nodup)
    (hmem : (varName, value) ∈ boolCase)
    : BoolCase.lookup? boolCase varName = some value := by
  induction boolCase with
  | nil => simp at hmem
  | cons head rest ih =>
      rcases head with ⟨headVar, headValue⟩
      have hparts := List.nodup_cons.mp hnodup
      simp only [List.mem_cons] at hmem
      rcases hmem with hhead | hrest
      · cases hhead
        simp [BoolCase.lookup?]
      · have hvarMem : varName ∈ rest.map Prod.fst :=
          List.mem_map.mpr ⟨(varName, value), hrest, rfl⟩
        have hne : headVar ≠ varName := by
          intro heq
          subst headVar
          exact hparts.1 hvarMem
        simp [BoolCase.lookup?, hne, ih hparts.2 hrest]

theorem inputValueBoolean?_eq_of_agrees_completeNormalBoolCase
    {variables : List BoolVar} {boolCase : BoolCase}
    {variableValues : Execution.VariableValues}
    (hcomplete : completeNormalBoolCase variables boolCase)
    (hagrees : variableValuesAgreeWithCase variableValues boolCase variables)
    {varName : BoolVar} {value : Bool}
    (hmem : (varName, value) ∈ boolCase)
    : Execution.inputValueBoolean? variableValues (.variable varName) = some value := by
  have hvarMem : varName ∈ variables :=
    (hcomplete.2.2 varName).1
      (List.mem_map.mpr ⟨(varName, value), hmem, rfl⟩)
  exact (hagrees varName hvarMem).trans
    (BoolCase.lookup?_eq_of_pair_mem_nodup hcomplete.2.1 hmem)

private theorem lookupVariableValue?_boolCaseVariableValues_of_mem
    {boolCase : BoolCase} {varName : BoolVar} {value : Bool}
    (base : Execution.VariableValues)
    : (boolCase.map Prod.fst).Nodup
      -> (varName, value) ∈ boolCase
      -> Execution.lookupVariableValue? (boolCaseVariableValues boolCase base) varName
          = some (.boolean value) := by
  intro hnodup hmem
  induction boolCase with
  | nil => simp at hmem
  | cons head rest ih =>
      rcases head with ⟨headVar, headValue⟩
      have hparts := List.nodup_cons.mp hnodup
      simp only [List.mem_cons] at hmem
      rcases hmem with hhead | hrest
      · cases hhead
        simp [boolCaseVariableValues, Execution.lookupVariableValue?]
      · have hvarMem : varName ∈ rest.map Prod.fst := by
          exact List.mem_map.mpr ⟨(varName, value), hrest, rfl⟩
        have hvarNe : headVar ≠ varName := by
          intro heq
          subst headVar
          exact hparts.1 hvarMem
        simpa [boolCaseVariableValues, Execution.lookupVariableValue?, hvarNe]
          using ih hparts.2 hrest

private theorem inputValueBoolean?_boolCaseVariableValues_of_mem
    {boolCase : BoolCase} {varName : BoolVar} {value : Bool}
    (base : Execution.VariableValues)
    (hnodup : (boolCase.map Prod.fst).Nodup)
    (hmem : (varName, value) ∈ boolCase)
    : Execution.inputValueBoolean?
        (boolCaseVariableValues boolCase base) (.variable varName)
      = some value := by
  simp [Execution.inputValueBoolean?,
    lookupVariableValue?_boolCaseVariableValues_of_mem base hnodup hmem,
    InputValue.staticBoolean?]

private theorem boolCase_value_eq_of_map_fst_nodup
    {boolCase : BoolCase} {varName : BoolVar} {leftValue rightValue : Bool}
    (hnodup : (boolCase.map Prod.fst).Nodup)
    (hleft : (varName, leftValue) ∈ boolCase)
    (hright : (varName, rightValue) ∈ boolCase)
    : leftValue = rightValue := by
  induction boolCase with
  | nil => simp at hleft
  | cons head rest ih =>
      rcases head with ⟨headVar, headValue⟩
      have hparts := List.nodup_cons.mp hnodup
      simp only [List.mem_cons] at hleft hright
      rcases hleft with hleft | hleft <;>
        rcases hright with hright | hright
      · cases hleft
        cases hright
        rfl
      · cases hleft
        have hmem : varName ∈ rest.map Prod.fst :=
          List.mem_map.mpr ⟨(varName, rightValue), hright, rfl⟩
        exact False.elim (hparts.1 hmem)
      · cases hright
        have hmem : varName ∈ rest.map Prod.fst :=
          List.mem_map.mpr ⟨(varName, leftValue), hleft, rfl⟩
        exact False.elim (hparts.1 hmem)
      · exact ih hparts.2 hleft hright

private theorem boolCaseVariableValues_agree
    {variables : List BoolVar} {boolCase : BoolCase}
    (base : Execution.VariableValues)
    (hcomplete : completeNormalBoolCase variables boolCase)
    : ∀ varName value,
        (varName, value) ∈ boolCase
        -> Execution.inputValueBoolean?
              (boolCaseVariableValues boolCase base) (.variable varName)
            = some value := by
  intro varName value hmem
  exact inputValueBoolean?_boolCaseVariableValues_of_mem base
    hcomplete.2.1 hmem

theorem variableValuesAgreeWithCase_boolCaseVariableValues
    {variables : List BoolVar} {boolCase : BoolCase}
    (base : Execution.VariableValues)
    (hcomplete : completeNormalBoolCase variables boolCase)
    : variableValuesAgreeWithCase (boolCaseVariableValues boolCase base)
        boolCase variables := by
  intro varName hvarMem
  have hcaseVar : varName ∈ boolCase.map Prod.fst :=
    (hcomplete.2.2 varName).2 hvarMem
  rcases List.mem_map.mp hcaseVar with
    ⟨⟨candidateVar, value⟩, hpair, hvarEq⟩
  change candidateVar = varName at hvarEq
  subst candidateVar
  exact (inputValueBoolean?_boolCaseVariableValues_of_mem base hcomplete.2.1 hpair).trans
          (BoolCase.lookup?_eq_of_pair_mem_nodup hcomplete.2.1 hpair).symm

theorem boolVarsComplete_boolCaseVariableValues
    {variables : List BoolVar} {boolCase : BoolCase}
    (base : Execution.VariableValues)
    (hcomplete : completeNormalBoolCase variables boolCase)
    : boolVarsComplete variables (boolCaseVariableValues boolCase base) := by
  intro varName hvarMem
  have hcaseVar : varName ∈ boolCase.map Prod.fst :=
    (hcomplete.2.2 varName).2 hvarMem
  rcases List.mem_map.mp hcaseVar with
    ⟨⟨candidateVar, value⟩, hpair, hvarEq⟩
  change candidateVar = varName at hvarEq
  subst candidateVar
  exact ⟨value, inputValueBoolean?_boolCaseVariableValues_of_mem base
    hcomplete.2.1 hpair⟩

theorem boolCaseVariableValues_agree_of_equivalent
    {variables : List BoolVar} {selected candidate : BoolCase}
    (base : Execution.VariableValues)
    (hselected : completeNormalBoolCase variables selected)
    (hequivalent : completeNormalBoolCasesEquivalent selected candidate)
    : ∀ varName value,
        (varName, value) ∈ candidate
        -> Execution.inputValueBoolean?
              (boolCaseVariableValues selected base) (.variable varName)
            = some value := by
  intro varName value hmem
  exact boolCaseVariableValues_agree base hselected varName value
    ((hequivalent varName value).2 hmem)

private theorem lookupVariableValue?_append_of_not_mem
    {leading base : Execution.VariableValues} {name : Name}
    (hnot : name ∉ leading.map Prod.fst)
    : Execution.lookupVariableValue? (leading ++ base) name
      = Execution.lookupVariableValue? base name := by
  induction leading with
  | nil => rfl
  | cons head rest ih =>
      rcases head with ⟨headName, headValue⟩
      simp only [List.map_cons, List.mem_cons] at hnot
      have hhead : headName ≠ name := by
        intro heq
        exact hnot (Or.inl heq.symm)
      have hrest : name ∉ rest.map Prod.fst := by
        intro hmem
        exact hnot (Or.inr hmem)
      simp [Execution.lookupVariableValue?, hhead, ih hrest]

private theorem BoolCase.nodup_of_names_nodup {boolCase : BoolCase}
    (hnodup : (boolCase.map Prod.fst).Nodup)
    : boolCase.Nodup := by
  induction boolCase with
  | nil => simp
  | cons pair rest ih =>
      simp only [List.map_cons, List.nodup_cons] at hnodup ⊢
      constructor
      · intro hpair
        exact hnodup.1 (List.mem_map.mpr ⟨pair, hpair, rfl⟩)
      · exact ih hnodup.2

private theorem variableValuesCoercionFuel_eq_of_perm
    {left right : Execution.VariableValues} (hperm : left.Perm right)
    : Execution.variableValuesCoercionFuel left
      = Execution.variableValuesCoercionFuel right := by
  induction hperm with
  | nil => rfl
  | cons entry hperm ih =>
      rcases entry with ⟨name, value⟩
      simp [Execution.variableValuesCoercionFuel, ih]
  | swap first second rest =>
      rcases first with ⟨firstName, firstValue⟩
      rcases second with ⟨secondName, secondValue⟩
      simp [Execution.variableValuesCoercionFuel, Nat.add_left_comm]
  | trans hleft hright ihLeft ihRight => exact ihLeft.trans ihRight

theorem boolCaseVariableValues_coercionEquivalent_of_equivalent
    {leftVariables rightVariables : List BoolVar}
    {leftCase rightCase : BoolCase} (base : Execution.VariableValues)
    (hleft : completeNormalBoolCase leftVariables leftCase)
    (hright : completeNormalBoolCase rightVariables rightCase)
    (hequivalent : completeNormalBoolCasesEquivalent leftCase rightCase)
    : Execution.variableValuesCoercionEquivalent
        (boolCaseVariableValues leftCase base)
        (boolCaseVariableValues rightCase base) := by
  have hleftNodup := BoolCase.nodup_of_names_nodup hleft.2.1
  have hrightNodup := BoolCase.nodup_of_names_nodup hright.2.1
  have hcasePerm : leftCase.Perm rightCase :=
    GroundTypeNormalization.listPermOfNodupSubsetSubset
      hleftNodup hrightNodup
      (fun pair hmem => (hequivalent pair.1 pair.2).1 hmem)
      (fun pair hmem => (hequivalent pair.1 pair.2).2 hmem)
  constructor
  · intro name
    by_cases hleftName : name ∈ leftCase.map Prod.fst
    · rcases List.mem_map.mp hleftName with
        ⟨⟨candidate, value⟩, hleftPair, hcandidate⟩
      change candidate = name at hcandidate
      subst candidate
      have hrightPair : (name, value) ∈ rightCase :=
        (hequivalent name value).1 hleftPair
      rw [lookupVariableValue?_boolCaseVariableValues_of_mem base
        hleft.2.1 hleftPair]
      rw [lookupVariableValue?_boolCaseVariableValues_of_mem base
        hright.2.1 hrightPair]
      simpa using
        GroundTypeNormalization.inputValue_equivalent_refl_forSyntaxDiff
          (.boolean value)
    · have hrightName : name ∉ rightCase.map Prod.fst := by
        intro hmem
        rcases List.mem_map.mp hmem with
          ⟨⟨candidate, value⟩, hrightPair, hcandidate⟩
        change candidate = name at hcandidate
        subst candidate
        exact hleftName (List.mem_map.mpr
          ⟨(name, value), (hequivalent name value).2 hrightPair, rfl⟩)
      have hlookupLeft := lookupVariableValue?_append_of_not_mem
        (leading := leftCase.map fun entry => (entry.1, .boolean entry.2))
        (base := base) (name := name) (by simpa using hleftName)
      have hlookupRight := lookupVariableValue?_append_of_not_mem
        (leading := rightCase.map fun entry => (entry.1, .boolean entry.2))
        (base := base) (name := name) (by simpa using hrightName)
      simp only [boolCaseVariableValues]
      rw [hlookupLeft, hlookupRight]
      cases Execution.lookupVariableValue? base name <;> simp
      exact
        GroundTypeNormalization.inputValue_equivalent_refl_forSyntaxDiff _
  · apply variableValuesCoercionFuel_eq_of_perm
    simp only [boolCaseVariableValues]
    exact List.Perm.append_right base
      (List.Perm.map
        (fun entry => (entry.1, InputValue.boolean entry.2)) hcasePerm)

private theorem completeNormalBoolCasesEquivalent_of_candidate_pairs
    {variables : List BoolVar} {selected candidate : BoolCase}
    (hselected : completeNormalBoolCase variables selected)
    (hcandidate : completeNormalBoolCase variables candidate)
    (hpairs
      : ∀ varName value, (varName, value) ∈ candidate -> (varName, value) ∈ selected)
    : completeNormalBoolCasesEquivalent selected candidate := by
  intro varName value
  constructor
  · intro hselectedPair
    have hvarCandidate : varName ∈ candidate.map Prod.fst :=
      (hcandidate.2.2 varName).2
        ((hselected.2.2 varName).1
          (List.mem_map.mpr ⟨(varName, value), hselectedPair, rfl⟩))
    rcases List.mem_map.mp hvarCandidate with
      ⟨⟨candidateVar, candidateValue⟩, hcandidatePair, hvarEq⟩
    change candidateVar = varName at hvarEq
    subst candidateVar
    have hselectedCandidate :=
      hpairs varName candidateValue hcandidatePair
    have hvalueEq : candidateValue = value :=
      boolCase_value_eq_of_map_fst_nodup hselected.2.1
        hselectedCandidate hselectedPair
    subst candidateValue
    exact hcandidatePair
  · intro hcandidatePair
    exact hpairs varName value hcandidatePair

theorem completeNormalBoolCases_mismatch_pair
    {variables : List BoolVar} {selected candidate : BoolCase}
    (hselected : completeNormalBoolCase variables selected)
    (hcandidate : completeNormalBoolCase variables candidate)
    (hnequivalent : ¬ completeNormalBoolCasesEquivalent selected candidate)
    : ∃ varName value, (varName, value) ∈ candidate ∧ (varName, !value) ∈ selected := by
  classical
  by_cases hexists : ∃ varName value,
      (varName, value) ∈ candidate
        ∧ (varName, !value) ∈ selected
  · exact hexists
  · have hpairs : ∀ varName value,
        (varName, value) ∈ candidate ->
          (varName, value) ∈ selected := by
      intro varName value hcandidatePair
      have hvarSelected : varName ∈ selected.map Prod.fst :=
        (hselected.2.2 varName).2
          ((hcandidate.2.2 varName).1
            (List.mem_map.mpr
              ⟨(varName, value), hcandidatePair, rfl⟩))
      rcases List.mem_map.mp hvarSelected with
        ⟨⟨selectedVar, selectedValue⟩, hselectedPair, hvarEq⟩
      change selectedVar = varName at hvarEq
      subst selectedVar
      cases value <;> cases selectedValue
      · exact hselectedPair
      · exact False.elim
          (hexists ⟨varName, false, hcandidatePair,
            by simpa using hselectedPair⟩)
      · exact False.elim
          (hexists ⟨varName, true, hcandidatePair,
            by simpa using hselectedPair⟩)
      · exact hselectedPair
    exact False.elim
      (hnequivalent
        (completeNormalBoolCasesEquivalent_of_candidate_pairs
          hselected hcandidate hpairs))

theorem boolCaseVariableValues_mismatch_of_not_equivalent
    {variables : List BoolVar} {selected candidate : BoolCase}
    (base : Execution.VariableValues)
    (hselected : completeNormalBoolCase variables selected)
    (hcandidate : completeNormalBoolCase variables candidate)
    (hnequivalent : ¬ completeNormalBoolCasesEquivalent selected candidate)
    : ∃ varName value,
        (varName, value) ∈ candidate
        ∧ Execution.inputValueBoolean?
            (boolCaseVariableValues selected base) (.variable varName)
          = some (!value) := by
  rcases completeNormalBoolCases_mismatch_pair hselected hcandidate
      hnequivalent with
    ⟨varName, value, hcandidatePair, hselectedPair⟩
  exact ⟨varName, value, hcandidatePair,
    inputValueBoolean?_boolCaseVariableValues_of_mem base
      hselected.2.1 hselectedPair⟩

end CompleteNormalization

end NormalForm

end GraphQL
