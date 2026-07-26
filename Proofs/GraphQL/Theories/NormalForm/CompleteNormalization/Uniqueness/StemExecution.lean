import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.ExecutionPrelude
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.BoolCaseWrappers
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Uniqueness.BoolCases

/-!
Execution of arbitrary complete-normal Boolean stems and root branch lists.
-/

namespace GraphQL

namespace NormalForm

namespace CompleteNormalization

variable {ObjectRef : Type}

private theorem list_split_of_mem_nodup {α : Type} {items : List α} {item : α}
    : items.Nodup
      -> item ∈ items
      -> ∃ before after,
          items = before ++ item :: after
          ∧ (∀ candidate, candidate ∈ before -> candidate ≠ item)
          ∧ (∀ candidate, candidate ∈ after -> candidate ≠ item) := by
  intro hnodup hmem
  induction items with
  | nil => simp at hmem
  | cons head rest ih =>
      have hparts := List.nodup_cons.mp hnodup
      simp only [List.mem_cons] at hmem
      rcases hmem with hhead | hrest
      · subst head
        refine ⟨[], rest, by simp, ?_, ?_⟩
        · intro candidate hcandidate
          simp at hcandidate
        · intro candidate hcandidate heq
          subst candidate
          exact hparts.1 hcandidate
      · rcases ih hparts.2 hrest with
          ⟨before, after, hsplit, hbefore, hafter⟩
        refine ⟨head :: before, after, ?_, ?_, hafter⟩
        · simp [hsplit]
        · intro candidate hcandidate
          simp only [List.mem_cons] at hcandidate
          rcases hcandidate with hcandidate | hcandidate
          · subst candidate
            intro heq
            subst head
            exact hparts.1 hrest
          · exact hbefore candidate hcandidate

private theorem collectFields_eq_nil_of_singletons_eq_nil
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    : ∀ selectionSet : List Selection,
        (∀ selection,
          selection ∈ selectionSet
          -> Execution.collectFields schema variableValues parentType source [selection]
              = [])
        -> Execution.collectFields schema variableValues parentType source selectionSet
            = []
  | [], _hsingletons => by
      simp [Execution.collectFields]
  | selection :: rest, hsingletons => by
      have hhead := hsingletons selection (by simp)
      have hrest :
          Execution.collectFields schema variableValues parentType source rest
            =
          [] :=
        collectFields_eq_nil_of_singletons_eq_nil schema variableValues
          parentType source rest (by
            intro candidate hcandidate
            exact hsingletons candidate (by simp [hcandidate]))
      simpa using
        collectFields_append_left_nil schema variableValues parentType source
          [selection] rest hhead |>.trans hrest

private theorem collectFields_completeNormalBooleanStem_of_equivalent_of_agrees
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    {variables : List BoolVar} {runtimeCase candidate : BoolCase}
    {selection : Selection} {body : List Selection}
    (hruntime : completeNormalBoolCase variables runtimeCase)
    (hagrees : variableValuesAgreeWithCase variableValues runtimeCase variables)
    (hequivalent : completeNormalBoolCasesEquivalent runtimeCase candidate)
    (hstem : completeNormalBooleanStem candidate selection body)
    : Execution.collectFields schema variableValues parentType source [selection]
      = Execution.collectFields schema variableValues parentType source body := by
  rw [← completeNormalBooleanStem_wrapWithBoolCase_eq hstem]
  exact collectFields_wrapWithBoolCase_of_agrees schema variableValues
    parentType source body candidate (by
      intro varName value hmem
      exact inputValueBoolean?_eq_of_agrees_completeNormalBoolCase
        hruntime hagrees ((hequivalent varName value).2 hmem))

private theorem collectFields_completeNormalBooleanStem_of_not_equivalent_of_agrees
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    {variables : List BoolVar} {runtimeCase candidate : BoolCase}
    {selection : Selection} {body : List Selection}
    (hruntime : completeNormalBoolCase variables runtimeCase)
    (hcandidate : completeNormalBoolCase variables candidate)
    (hagrees : variableValuesAgreeWithCase variableValues runtimeCase variables)
    (hnequivalent : ¬ completeNormalBoolCasesEquivalent runtimeCase candidate)
    (hstem : completeNormalBooleanStem candidate selection body)
    : Execution.collectFields schema variableValues parentType source [selection]
      = [] := by
  rcases completeNormalBoolCases_mismatch_pair hruntime hcandidate
      hnequivalent with ⟨varName, value, hpair, hmismatchPair⟩
  rw [← completeNormalBooleanStem_wrapWithBoolCase_eq hstem]
  exact collectFields_wrapWithBoolCase_of_mismatch_pair schema variableValues
    parentType source body candidate varName value hpair
    (inputValueBoolean?_eq_of_agrees_completeNormalBoolCase
      hruntime hagrees hmismatchPair)

private theorem collectFields_wrapWithBoolCase_of_missing_pair
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    (selectionSet : List Selection)
    : ∀ boolCase : BoolCase,
        (varName : BoolVar)
        -> (value : Bool)
        -> (varName, value) ∈ boolCase
            -> Execution.inputValueBoolean? variableValues (.variable varName) = none
            -> Execution.collectFields schema variableValues parentType source
                  (wrapWithBoolCase boolCase selectionSet)
                = []
  | [], varName, value, hpair, _hmissing => by
      cases hpair
  | (headVar, headValue) :: rest, varName, value, hpair, hmissing => by
      simp only [List.mem_cons] at hpair
      rcases hpair with hhead | htail
      · cases hhead
        apply collectFields_wrapWithBoolCase_cons_skipped schema variableValues
          parentType source headVar headValue rest selectionSet
        cases headValue <;>
          simp [directiveForBit, Execution.selectionDirectivesAllowBool,
            Execution.directiveAllowsSelectionBool, hmissing]
      · cases hallow :
          Execution.selectionDirectivesAllowBool variableValues
            [directiveForBit headVar headValue]
        · exact collectFields_wrapWithBoolCase_cons_skipped schema
            variableValues parentType source headVar headValue rest selectionSet
            hallow
        · exact
            (collectFields_wrapWithBoolCase_cons_allowed schema variableValues
              parentType source headVar headValue rest selectionSet hallow).trans
              (collectFields_wrapWithBoolCase_of_missing_pair schema
                variableValues parentType source selectionSet rest varName value
                htail hmissing)

theorem collectFields_completeNormalSelectionSet_eq_nil_of_missing_variable
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    {varName : BoolVar} {variables : List BoolVar}
    {selectionSet : List Selection}
    (hnormal
      : completeNormalSelectionSet schema (varName :: variables) parentType selectionSet)
    {missingVar : BoolVar} (hmissingMem : missingVar ∈ varName :: variables)
    (hmissing : Execution.inputValueBoolean? variableValues (.variable missingVar) = none)
    : Execution.collectFields schema variableValues parentType source selectionSet
      = [] := by
  rcases hnormal with ⟨_hvariablesNodup, _hselectionSetNodup,
    hbranches, _hunique⟩
  apply collectFields_eq_nil_of_singletons_eq_nil schema variableValues
    parentType source selectionSet
  intro selection hselection
  rcases hbranches selection hselection with
    ⟨candidate, body, hcandidate, hstem, _hbodyNormal, _hbodyFree⟩
  have hcaseVar : missingVar ∈ candidate.map Prod.fst :=
    (hcandidate.2.2 missingVar).2 hmissingMem
  rcases List.mem_map.mp hcaseVar with
    ⟨⟨candidateVar, value⟩, hpair, hvarEq⟩
  change candidateVar = missingVar at hvarEq
  subst candidateVar
  rw [← completeNormalBooleanStem_wrapWithBoolCase_eq hstem]
  exact collectFields_wrapWithBoolCase_of_missing_pair schema variableValues
    parentType source body candidate missingVar value hpair hmissing

theorem collectFields_completeNormalSelectionSet_eq_nil_of_no_equivalent_of_agrees
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    {varName : BoolVar} {variables : List BoolVar}
    {runtimeCase : BoolCase} {selectionSet : List Selection}
    (hnormal
      : completeNormalSelectionSet schema (varName :: variables) parentType selectionSet)
    (hruntime : completeNormalBoolCase (varName :: variables) runtimeCase)
    (hagrees
      : variableValuesAgreeWithCase variableValues runtimeCase (varName :: variables))
    (hnone
      : ¬ ∃ selection candidate body,
            selection ∈ selectionSet
            ∧ completeNormalBoolCase (varName :: variables) candidate
            ∧ completeNormalBooleanStem candidate selection body
            ∧ completeNormalBoolCasesEquivalent runtimeCase candidate)
    : Execution.collectFields schema variableValues parentType source selectionSet
      = [] := by
  rcases hnormal with ⟨_hvariablesNodup, _hselectionSetNodup,
    hbranches, _hunique⟩
  apply collectFields_eq_nil_of_singletons_eq_nil schema variableValues
    parentType source selectionSet
  intro selection hselection
  rcases hbranches selection hselection with
    ⟨candidate, body, hcandidate, hstem, _hbodyNormal, _hbodyFree⟩
  apply collectFields_completeNormalBooleanStem_of_not_equivalent_of_agrees
    schema variableValues parentType source hruntime hcandidate hagrees
  · intro hequivalent
    exact hnone ⟨selection, candidate, body, hselection, hcandidate, hstem,
      hequivalent⟩
  · exact hstem

theorem collectFields_completeNormalSelectionSet_eq_body_of_equivalent_of_agrees
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    {varName : BoolVar} {variables : List BoolVar}
    {runtimeCase selected : BoolCase} {selectedSelection : Selection}
    {selectedBody selectionSet : List Selection}
    (hnormal
      : completeNormalSelectionSet schema (varName :: variables) parentType selectionSet)
    (hselectedMem : selectedSelection ∈ selectionSet)
    (hruntime : completeNormalBoolCase (varName :: variables) runtimeCase)
    (hselected : completeNormalBoolCase (varName :: variables) selected)
    (hagrees
      : variableValuesAgreeWithCase variableValues runtimeCase (varName :: variables))
    (hequivalent : completeNormalBoolCasesEquivalent runtimeCase selected)
    (hselectedStem : completeNormalBooleanStem selected selectedSelection selectedBody)
    (hselectedBodyFree : selectionSetDirectiveFree selectedBody)
    : Execution.collectFields schema variableValues parentType source selectionSet
      = Execution.collectFields schema variableValues parentType source selectedBody := by
  rcases hnormal with ⟨_hvariablesNodup, hselectionSetNodup,
    hbranches, hunique⟩
  rcases list_split_of_mem_nodup hselectionSetNodup hselectedMem with
    ⟨before, after, hsplit, hbeforeNe, hafterNe⟩
  have hother : ∀ candidateSelection,
      candidateSelection ∈ selectionSet ->
      candidateSelection ≠ selectedSelection ->
        Execution.collectFields schema variableValues parentType source
            [candidateSelection]
          =
        [] := by
    intro candidateSelection hcandidateMem hcandidateNe
    rcases hbranches candidateSelection hcandidateMem with
      ⟨candidate, candidateBody, hcandidate, hcandidateStem,
        _hcandidateBodyNormal, hcandidateBodyFree⟩
    apply
      collectFields_completeNormalBooleanStem_of_not_equivalent_of_agrees
        schema variableValues parentType source hruntime hcandidate hagrees
    · intro hruntimeCandidate
      have hselectedCandidate :
          completeNormalBoolCasesEquivalent selected candidate :=
        completeNormalBoolCasesEquivalent_trans
          (completeNormalBoolCasesEquivalent_symm hequivalent)
          hruntimeCandidate
      have heq := hunique selectedSelection candidateSelection selected
        candidate selectedBody candidateBody hselectedMem hcandidateMem
        hselected hcandidate hselectedStem hcandidateStem hselectedBodyFree
        hcandidateBodyFree hselectedCandidate
      exact hcandidateNe heq.symm
    · exact hcandidateStem
  have hbeforeCollect :
      Execution.collectFields schema variableValues parentType source before =
        [] :=
    collectFields_eq_nil_of_singletons_eq_nil schema variableValues parentType
      source before (by
        intro candidate hcandidate
        exact hother candidate (by rw [hsplit]; simp [hcandidate])
          (hbeforeNe candidate hcandidate))
  have hafterCollect :
      Execution.collectFields schema variableValues parentType source after =
        [] :=
    collectFields_eq_nil_of_singletons_eq_nil schema variableValues parentType
      source after (by
        intro candidate hcandidate
        exact hother candidate (by rw [hsplit]; simp [hcandidate])
          (hafterNe candidate hcandidate))
  have hselectedCollect :=
    collectFields_completeNormalBooleanStem_of_equivalent_of_agrees schema
      variableValues parentType source hruntime hagrees hequivalent
      hselectedStem
  rw [hsplit]
  rw [collectFields_append_left_nil schema variableValues parentType source
    before (selectedSelection :: after) hbeforeCollect]
  change Execution.collectFields schema variableValues parentType source
      ([selectedSelection] ++ after) = _
  rw [collectFields_append_right_nil schema variableValues parentType source
    [selectedSelection] after hafterCollect]
  exact hselectedCollect

theorem collectFields_completeNormalSelectionSet_eq_nil_of_no_equivalent
    (schema : Schema) (base : Execution.VariableValues)
    (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    {varName : BoolVar} {variables : List BoolVar}
    {selected : BoolCase} {selectionSet : List Selection}
    (hnormal
      : completeNormalSelectionSet schema (varName :: variables) parentType selectionSet)
    (hselected : completeNormalBoolCase (varName :: variables) selected)
    (hnone
      : ¬ ∃ selection candidate body,
            selection ∈ selectionSet
            ∧ completeNormalBoolCase (varName :: variables) candidate
            ∧ completeNormalBooleanStem candidate selection body
            ∧ completeNormalBoolCasesEquivalent selected candidate)
    : Execution.collectFields schema
        (boolCaseVariableValues selected base) parentType source selectionSet
      = [] := by
  exact
    collectFields_completeNormalSelectionSet_eq_nil_of_no_equivalent_of_agrees
      schema (boolCaseVariableValues selected base) parentType source hnormal
      hselected (variableValuesAgreeWithCase_boolCaseVariableValues base
        hselected) hnone

theorem collectFields_completeNormalSelectionSet_eq_body_of_equivalent
    (schema : Schema) (base : Execution.VariableValues)
    (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    {varName : BoolVar} {variables : List BoolVar}
    {runtimeCase selected : BoolCase} {selectedSelection : Selection}
    {selectedBody selectionSet : List Selection}
    (hnormal
      : completeNormalSelectionSet schema (varName :: variables) parentType selectionSet)
    (hselectedMem : selectedSelection ∈ selectionSet)
    (hruntime : completeNormalBoolCase (varName :: variables) runtimeCase)
    (hselected : completeNormalBoolCase (varName :: variables) selected)
    (hequivalent : completeNormalBoolCasesEquivalent runtimeCase selected)
    (hselectedStem : completeNormalBooleanStem selected selectedSelection selectedBody)
    (hselectedBodyFree : selectionSetDirectiveFree selectedBody)
    : Execution.collectFields schema
        (boolCaseVariableValues runtimeCase base) parentType source selectionSet
      = Execution.collectFields schema
          (boolCaseVariableValues runtimeCase base) parentType source
          selectedBody := by
  exact
    collectFields_completeNormalSelectionSet_eq_body_of_equivalent_of_agrees
      schema (boolCaseVariableValues runtimeCase base) parentType source
      hnormal hselectedMem hruntime hselected
      (variableValuesAgreeWithCase_boolCaseVariableValues base hruntime)
      hequivalent hselectedStem hselectedBodyFree

theorem collectFields_completeNormalSelectionSet_eq_body
    (schema : Schema) (base : Execution.VariableValues)
    (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    {varName : BoolVar} {variables : List BoolVar}
    {selected : BoolCase} {selectedSelection : Selection}
    {selectedBody selectionSet : List Selection}
    (hnormal
      : completeNormalSelectionSet schema (varName :: variables) parentType selectionSet)
    (hselectedMem : selectedSelection ∈ selectionSet)
    (hselected : completeNormalBoolCase (varName :: variables) selected)
    (hselectedStem : completeNormalBooleanStem selected selectedSelection selectedBody)
    (hselectedBodyFree : selectionSetDirectiveFree selectedBody)
    : Execution.collectFields schema
        (boolCaseVariableValues selected base) parentType source selectionSet
      = Execution.collectFields schema
          (boolCaseVariableValues selected base) parentType source selectedBody := by
  exact collectFields_completeNormalSelectionSet_eq_body_of_equivalent schema
    base parentType source hnormal hselectedMem hselected hselected
    (completeNormalBoolCasesEquivalent_refl selected) hselectedStem
    hselectedBodyFree

end CompleteNormalization

end NormalForm

end GraphQL
