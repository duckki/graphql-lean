import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.DirectiveSemantics
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Normality

/-!
Normality proof for the current partial complete normalizer.
-/

namespace GraphQL

namespace NormalForm

namespace CompleteNormalization

mutual
  theorem selectionDirectiveFree_booleanVariables_nil
      : ∀ selection,
          selectionDirectiveFree selection -> selectionBooleanVariables selection = []
    | .field _responseName _fieldName _arguments _directives selectionSet,
        hfree => by
        rcases hfree with ⟨hdirectives, hselectionSet⟩
        subst _directives
        simp [selectionBooleanVariables, directivesBooleanVariables,
          selectionSetDirectiveFree_booleanVariables_nil selectionSet
            hselectionSet]
    | .inlineFragment _typeCondition _directives selectionSet, hfree => by
        rcases hfree with ⟨hdirectives, hselectionSet⟩
        subst _directives
        simp [selectionBooleanVariables, directivesBooleanVariables,
          selectionSetDirectiveFree_booleanVariables_nil selectionSet
            hselectionSet]

  theorem selectionSetDirectiveFree_booleanVariables_nil
      : ∀ selectionSet,
          selectionSetDirectiveFree selectionSet
          -> selectionSetBooleanVariables selectionSet = []
    | [], _hfree => by
        rfl
    | selection :: rest, hfree => by
        simp [selectionSetBooleanVariables,
          selectionDirectiveFree_booleanVariables_nil selection hfree.1,
          selectionSetDirectiveFree_booleanVariables_nil rest hfree.2]
end

theorem operationBoolVarsComplete_of_operationDirectiveFree
    (operation : Operation)
    (variableValues : Execution.VariableValues)
    : operationDirectiveFree operation
      -> operationBoolVarsComplete operation variableValues := by
  intro hfree varName hmem
  have hvariables :
      selectionSetBooleanVariables operation.selectionSet = [] :=
    selectionSetDirectiveFree_booleanVariables_nil operation.selectionSet
      hfree
  simp [operationBoolVars, hvariables, dedupBoolVars] at hmem

private theorem selection_size_pos (selection : Selection) : 0 < selection.size := by
  cases selection <;> simp [Selection.size] <;> omega

private theorem selectionSet_size_tail_lt_cons
    (selection : Selection) (rest : List Selection)
    : SelectionSet.size rest < SelectionSet.size (selection :: rest) := by
  simp [SelectionSet.size]
  exact Nat.lt_add_of_pos_left (selection_size_pos selection)

private theorem selectionSet_size_child_lt_cons_field
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : SelectionSet.size selectionSet
      < SelectionSet.size
          (Selection.field responseName fieldName arguments directives selectionSet
            :: rest) := by
  simp [SelectionSet.size, Selection.size]
  omega

private theorem selectionSet_size_child_lt_cons_inline
    (typeCondition : Option Name) (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : SelectionSet.size selectionSet
      < SelectionSet.size
          (Selection.inlineFragment typeCondition directives selectionSet :: rest) := by
  simp [SelectionSet.size, Selection.size]
  omega

theorem filterSelectionSetBoolCase_directiveFree (schema : Schema)
    : ∀ boolCase selectionSet,
        selectionSetDirectiveFree (filterSelectionSetBoolCase boolCase selectionSet)
  | boolCase, [] => by
      simpa [filterSelectionSetBoolCase] using selectionSetDirectiveFree_nil
  | boolCase, selection :: rest => by
      have hrest :
          selectionSetDirectiveFree
            (filterSelectionSetBoolCase boolCase rest) :=
        filterSelectionSetBoolCase_directiveFree schema boolCase rest
      cases selection with
      | field responseName fieldName arguments directives selectionSet =>
          by_cases hallow : directivesAllowIn boolCase directives = true
          · have hchild :
                selectionSetDirectiveFree
                  (filterSelectionSetBoolCase boolCase
                    selectionSet) :=
              filterSelectionSetBoolCase_directiveFree schema boolCase selectionSet
            cases selectionSet with
            | nil =>
                simpa [filterSelectionSetBoolCase, hallow] using
                  (show selectionSetDirectiveFree
                    (Selection.field responseName fieldName arguments [] []
                      :: filterSelectionSetBoolCase boolCase
                        rest) from
                    ⟨⟨rfl, selectionSetDirectiveFree_nil⟩, hrest⟩)
            | cons child children =>
                cases hfiltered :
                    filterSelectionSetBoolCase boolCase
                      (child :: children) with
                | nil =>
                    simpa [filterSelectionSetBoolCase, hallow, hfiltered]
                      using
                        (show selectionSetDirectiveFree
                          (Selection.field responseName fieldName arguments [] []
                            :: filterSelectionSetBoolCase boolCase rest) from
                          ⟨⟨rfl, selectionSetDirectiveFree_nil⟩, hrest⟩)
                | cons filteredChild filteredChildren =>
                    have hfilteredFree :
                        selectionSetDirectiveFree
                          (filteredChild :: filteredChildren) := by
                      simpa [hfiltered] using hchild
                    simpa [filterSelectionSetBoolCase, hallow, hfiltered]
                      using
                        (show selectionSetDirectiveFree
                          (Selection.field responseName fieldName arguments []
                            (filteredChild :: filteredChildren)
                            :: filterSelectionSetBoolCase boolCase rest) from
                          ⟨⟨rfl, hfilteredFree⟩, hrest⟩)
          · have hfalse :
                directivesAllowIn boolCase directives = false := by
              cases hmatch : directivesAllowIn boolCase directives
              · rfl
              · contradiction
            simpa [filterSelectionSetBoolCase, hfalse] using hrest
      | inlineFragment typeCondition directives selectionSet =>
          cases typeCondition with
          | none =>
              by_cases hallow : directivesAllowIn boolCase directives = true
              · have hchild :
                    selectionSetDirectiveFree
                      (filterSelectionSetBoolCase boolCase
                        selectionSet) :=
                  filterSelectionSetBoolCase_directiveFree schema boolCase selectionSet
                cases hfiltered :
                    filterSelectionSetBoolCase boolCase
                      selectionSet with
                | nil =>
                    simpa [filterSelectionSetBoolCase, hallow, hfiltered]
                      using hrest
                | cons filteredChild filteredChildren =>
                    have hfilteredFree :
                        selectionSetDirectiveFree
                          (filteredChild :: filteredChildren) := by
                      simpa [hfiltered] using hchild
                    simpa [filterSelectionSetBoolCase, hallow, hfiltered]
                      using
                        (show selectionSetDirectiveFree
                          (Selection.inlineFragment none []
                            (filteredChild :: filteredChildren)
                            :: filterSelectionSetBoolCase boolCase rest) from
                          ⟨⟨rfl, hfilteredFree⟩, hrest⟩)
              · have hfalse :
                    directivesAllowIn boolCase directives = false := by
                  cases hmatch : directivesAllowIn boolCase directives
                  · rfl
                  · contradiction
                simpa [filterSelectionSetBoolCase, hfalse] using hrest
          | some typeCondition =>
              by_cases hallow : directivesAllowIn boolCase directives = true
              · have hchild :
                    selectionSetDirectiveFree
                      (filterSelectionSetBoolCase boolCase
                        selectionSet) :=
                  filterSelectionSetBoolCase_directiveFree schema boolCase selectionSet
                cases hfiltered :
                    filterSelectionSetBoolCase boolCase
                      selectionSet with
                | nil =>
                    simpa [filterSelectionSetBoolCase, hallow, hfiltered]
                      using hrest
                | cons filteredChild filteredChildren =>
                    have hfilteredFree :
                        selectionSetDirectiveFree
                          (filteredChild :: filteredChildren) := by
                      simpa [hfiltered] using hchild
                    simpa [filterSelectionSetBoolCase, hallow, hfiltered]
                      using
                        (show selectionSetDirectiveFree
                          (Selection.inlineFragment (some typeCondition) []
                            (filteredChild :: filteredChildren)
                            :: filterSelectionSetBoolCase boolCase rest) from
                          ⟨⟨rfl, hfilteredFree⟩, hrest⟩)
              · have hfalse :
                    directivesAllowIn boolCase directives = false := by
                  cases hmatch : directivesAllowIn boolCase directives
                  · rfl
                  · contradiction
                simpa [filterSelectionSetBoolCase, hfalse] using hrest
termination_by _boolCase selectionSet =>
  SelectionSet.size selectionSet
decreasing_by
  all_goals
    first
    | exact selectionSet_size_tail_lt_cons selection rest
    | exact selectionSet_size_child_lt_cons_field responseName fieldName
        arguments directives selectionSet rest
    | exact selectionSet_size_child_lt_cons_inline none directives
        selectionSet rest
    | exact selectionSet_size_child_lt_cons_inline (some typeCondition)
        directives selectionSet rest

theorem wrapWithBoolCase_singleton_of_ne
    : ∀ boolCase selectionSet,
        boolCase ≠ [] -> ∃ selection, wrapWithBoolCase boolCase selectionSet = [selection]
  | [], _selectionSet, hne => by
      exact False.elim (hne rfl)
  | (varName, value) :: rest, selectionSet, _hne => by
      exact ⟨Selection.inlineFragment none [directiveForBit varName value]
        (wrapWithBoolCase rest selectionSet), rfl⟩

theorem completeNormalBooleanStem_wrapWithBoolCase
    : ∀ boolCase selectionSet selection,
        boolCase ≠ []
        -> wrapWithBoolCase boolCase selectionSet = [selection]
        -> completeNormalBooleanStem boolCase selection selectionSet
  | [], _selectionSet, _selection, hne, _hwrap => by
      exact False.elim (hne rfl)
  | [(varName, value)], selectionSet, selection, _hne, hwrap => by
      simp [wrapWithBoolCase] at hwrap
      subst selection
      simp [completeNormalBooleanStem]
  | (varName, value) :: (nextVar, nextValue) :: rest, selectionSet,
      selection, _hne, hwrap => by
      simp [wrapWithBoolCase] at hwrap
      subst selection
      simp [completeNormalBooleanStem]
      exact completeNormalBooleanStem_wrapWithBoolCase
        ((nextVar, nextValue) :: rest) selectionSet
        (Selection.inlineFragment none [directiveForBit nextVar nextValue]
          (wrapWithBoolCase rest selectionSet))
        (by simp) rfl

theorem completeNormalBooleanStem_of_mem_wrapWithBoolCase
    {boolCase : BoolCase} {selectionSet : List Selection}
    {selection : Selection}
    : boolCase ≠ []
      -> selection ∈ wrapWithBoolCase boolCase selectionSet
      -> completeNormalBooleanStem boolCase selection selectionSet := by
  intro hne hmem
  rcases wrapWithBoolCase_singleton_of_ne boolCase selectionSet hne with
    ⟨wrappedSelection, hwrap⟩
  rw [hwrap] at hmem
  simp at hmem
  subst selection
  exact completeNormalBooleanStem_wrapWithBoolCase boolCase selectionSet
    wrappedSelection hne hwrap

theorem completeNormalBooleanStem_wrapWithBoolCase_eq
    : ∀ {boolCase selection body},
        completeNormalBooleanStem boolCase selection body
        -> wrapWithBoolCase boolCase body = [selection]
  | [], _selection, _body, hstem => by
      simp [completeNormalBooleanStem] at hstem
  | [(varName, value)],
      .inlineFragment none [directive] selectionSet, body, hstem => by
      rcases hstem with ⟨hdirective, hbody⟩
      subst directive
      subst selectionSet
      simp [wrapWithBoolCase]
  | (varName, value) :: (nextVar, nextValue) :: rest,
      .inlineFragment none [directive] [child], body, hstem => by
      rcases hstem with ⟨hdirective, hchildStem⟩
      subst directive
      have hchildWrap :=
        completeNormalBooleanStem_wrapWithBoolCase_eq hchildStem
      simp [wrapWithBoolCase] at hchildWrap
      simp [wrapWithBoolCase, hchildWrap]
  | _ :: _ :: _, .field _ _ _ _ _, _body, hstem => by
      simp [completeNormalBooleanStem] at hstem
  | _ :: _ :: _, .inlineFragment none [] _, _body, hstem => by
      simp [completeNormalBooleanStem] at hstem
  | _ :: _ :: _, .inlineFragment none (_ :: _ :: _) _, _body, hstem => by
      simp [completeNormalBooleanStem] at hstem
  | _ :: _ :: _, .inlineFragment (some _) _ _, _body, hstem => by
      simp [completeNormalBooleanStem] at hstem
  | [_], .field _ _ _ _ _, _body, hstem => by
      simp [completeNormalBooleanStem] at hstem
  | [_], .inlineFragment none [] _, _body, hstem => by
      simp [completeNormalBooleanStem] at hstem
  | [_], .inlineFragment none (_ :: _ :: _) _, _body, hstem => by
      simp [completeNormalBooleanStem] at hstem
  | [_], .inlineFragment (some _) _ _, _body, hstem => by
      simp [completeNormalBooleanStem] at hstem

theorem boolCase_map_fst_of_mem_allBoolCases
    : ∀ {variables boolCase},
        boolCase ∈ allBoolCases variables -> boolCase.map Prod.fst = variables
  | [], boolCase, hmem => by
      simp [allBoolCases] at hmem
      subst boolCase
      rfl
  | varName :: restVariables, boolCase, hmem => by
      simp [allBoolCases] at hmem
      rcases hmem with hmem | hmem
      · rcases hmem with ⟨restCase, hrestMem, hcase⟩
        subst boolCase
        simp [boolCase_map_fst_of_mem_allBoolCases hrestMem]
      · rcases hmem with ⟨restCase, hrestMem, hcase⟩
        subst boolCase
        simp [boolCase_map_fst_of_mem_allBoolCases hrestMem]

theorem completeNormalBoolCase_of_mem_allBoolCases
    {variables : List BoolVar} {boolCase : BoolCase}
    : variables.Nodup
      -> boolCase ∈ allBoolCases variables
      -> completeNormalBoolCase variables boolCase := by
  intro hnodup hmem
  have hfst := boolCase_map_fst_of_mem_allBoolCases hmem
  refine ⟨hnodup, ?_, ?_⟩
  · simpa [hfst] using hnodup
  · intro varName
    simp [hfst]

theorem completeNormalBoolCase_ne_nil_of_variables_cons
    {varName : BoolVar} {variables : List BoolVar} {boolCase : BoolCase}
    : completeNormalBoolCase (varName :: variables) boolCase -> boolCase ≠ [] := by
  intro hcomplete hnil
  rcases hcomplete with ⟨_hvarsNodup, _hcaseNodup, hvars⟩
  subst boolCase
  have hmem := (hvars varName).2 (by simp)
  simp at hmem

theorem completeNormalBoolCasesEquivalent_refl (boolCase : BoolCase)
    : completeNormalBoolCasesEquivalent boolCase boolCase := by
  intro varName value
  rfl

theorem completeNormalBoolCasesEquivalent_symm {left right : BoolCase}
    : completeNormalBoolCasesEquivalent left right
      -> completeNormalBoolCasesEquivalent right left := by
  intro hequiv varName value
  exact (hequiv varName value).symm

theorem completeNormalBoolCasesEquivalent_trans {left middle right : BoolCase}
    : completeNormalBoolCasesEquivalent left middle
      -> completeNormalBoolCasesEquivalent middle right
      -> completeNormalBoolCasesEquivalent left right := by
  intro hleft hright varName value
  exact Iff.trans (hleft varName value) (hright varName value)

theorem boolCase_eq_of_mem_allBoolCases_equivalent
    : ∀ {variables left right},
        variables.Nodup
        -> left ∈ allBoolCases variables
        -> right ∈ allBoolCases variables
        -> completeNormalBoolCasesEquivalent left right
        -> left = right
  | [], left, right, _hnodup, hleft, hright, _hequiv => by
      simp [allBoolCases] at hleft hright
      subst left
      subst right
      rfl
  | varName :: restVariables, left, right, hnodup, hleft, hright,
      hequiv => by
      have hparts := List.nodup_cons.mp hnodup
      have hvarNotMem : varName ∉ restVariables := hparts.1
      have hrestNodup : restVariables.Nodup := hparts.2
      have noHeadPair :
          ∀ {restCase value},
            restCase ∈ allBoolCases restVariables ->
              (varName, value) ∉ restCase := by
        intro restCase value hcase hpair
        exact hvarNotMem
          (boolCase_pair_variable_mem_of_allBoolCases hcase hpair)
      simp [allBoolCases] at hleft hright
      rcases hleft with hleft | hleft
      · rcases hleft with ⟨leftRest, hleftRest, hleftEq⟩
        subst left
        rcases hright with hright | hright
        · rcases hright with ⟨rightRest, hrightRest, hrightEq⟩
          subst right
          have htailEquiv :
              completeNormalBoolCasesEquivalent leftRest rightRest := by
            intro pairVar pairValue
            constructor
            · intro hpair
              have hfull :
                  (pairVar, pairValue) ∈
                    (varName, false) :: rightRest :=
                (hequiv pairVar pairValue).1 (by simp [hpair])
              simp at hfull
              rcases hfull with hhead | htail
              · rcases hhead with ⟨hvar, hvalue⟩
                subst pairVar
                subst pairValue
                exact False.elim (noHeadPair hleftRest hpair)
              · exact htail
            · intro hpair
              have hfull :
                  (pairVar, pairValue) ∈
                    (varName, false) :: leftRest :=
                (hequiv pairVar pairValue).2 (by simp [hpair])
              simp at hfull
              rcases hfull with hhead | htail
              · rcases hhead with ⟨hvar, hvalue⟩
                subst pairVar
                subst pairValue
                exact False.elim (noHeadPair hrightRest hpair)
              · exact htail
          have htailEq :=
            boolCase_eq_of_mem_allBoolCases_equivalent
              hrestNodup hleftRest hrightRest htailEquiv
          subst rightRest
          rfl
        · rcases hright with ⟨rightRest, hrightRest, hrightEq⟩
          subst right
          have hrightHasFalse :
              (varName, false) ∈ (varName, true) :: rightRest :=
            (hequiv varName false).1 (by simp)
          rcases List.mem_cons.mp hrightHasFalse with hvalue | htail
          · cases hvalue
          · exact False.elim (noHeadPair hrightRest htail)
      · rcases hleft with ⟨leftRest, hleftRest, hleftEq⟩
        subst left
        rcases hright with hright | hright
        · rcases hright with ⟨rightRest, hrightRest, hrightEq⟩
          subst right
          have hrightHasTrue :
              (varName, true) ∈ (varName, false) :: rightRest :=
            (hequiv varName true).1 (by simp)
          rcases List.mem_cons.mp hrightHasTrue with hvalue | htail
          · cases hvalue
          · exact False.elim (noHeadPair hrightRest htail)
        · rcases hright with ⟨rightRest, hrightRest, hrightEq⟩
          subst right
          have htailEquiv :
              completeNormalBoolCasesEquivalent leftRest rightRest := by
            intro pairVar pairValue
            constructor
            · intro hpair
              have hfull :
                  (pairVar, pairValue) ∈
                    (varName, true) :: rightRest :=
                (hequiv pairVar pairValue).1 (by simp [hpair])
              simp at hfull
              rcases hfull with hhead | htail
              · rcases hhead with ⟨hvar, hvalue⟩
                subst pairVar
                subst pairValue
                exact False.elim (noHeadPair hleftRest hpair)
              · exact htail
            · intro hpair
              have hfull :
                  (pairVar, pairValue) ∈
                    (varName, true) :: leftRest :=
                (hequiv pairVar pairValue).2 (by simp [hpair])
              simp at hfull
              rcases hfull with hhead | htail
              · rcases hhead with ⟨hvar, hvalue⟩
                subst pairVar
                subst pairValue
                exact False.elim (noHeadPair hrightRest hpair)
              · exact htail
          have htailEq :=
            boolCase_eq_of_mem_allBoolCases_equivalent
              hrestNodup hleftRest hrightRest htailEquiv
          subst rightRest
          rfl

theorem boolCase_ne_nil_of_mem_allBoolCases_cons
    {varName : BoolVar} {variables : List BoolVar} {boolCase : BoolCase}
    : boolCase ∈ allBoolCases (varName :: variables) -> boolCase ≠ [] := by
  intro hmem hnil
  subst boolCase
  simp [allBoolCases] at hmem

theorem directiveForBit_booleanVariables (varName : BoolVar) (value : Bool)
    : directiveBooleanVariables (directiveForBit varName value) = [varName] := by
  cases value <;>
    simp [directiveForBit, directiveBooleanVariables,
      inputValueBooleanVariables]

theorem directiveForBit_injective
    {leftVar rightVar : BoolVar} {leftValue rightValue : Bool}
    : directiveForBit leftVar leftValue = directiveForBit rightVar rightValue
      -> (leftVar, leftValue) = (rightVar, rightValue) := by
  cases leftValue <;> cases rightValue <;> simp [directiveForBit]

theorem selectionSetBooleanVariables_wrapWithBoolCase
    : ∀ boolCase selectionSet,
        selectionSetBooleanVariables (wrapWithBoolCase boolCase selectionSet)
        = boolCase.map Prod.fst ++ selectionSetBooleanVariables selectionSet
  | [], selectionSet => by
      simp [wrapWithBoolCase]
  | (varName, value) :: rest, selectionSet => by
      simp [wrapWithBoolCase, selectionSetBooleanVariables,
        selectionBooleanVariables, directivesBooleanVariables,
        directiveForBit_booleanVariables,
        selectionSetBooleanVariables_wrapWithBoolCase rest selectionSet]

theorem selectionSetDirectiveFree_wrapWithBoolCase_cons_false
    (varName : BoolVar) (value : Bool) (rest : BoolCase)
    (selectionSet : List Selection)
    : ¬ selectionSetDirectiveFree
          (wrapWithBoolCase ((varName, value) :: rest) selectionSet) := by
      simp [wrapWithBoolCase, selectionSetDirectiveFree,
        selectionDirectiveFree]

theorem selectionBooleanVariables_of_completeNormalBooleanStem
    {boolCase : BoolCase} {selection : Selection}
    {body : List Selection}
    : completeNormalBooleanStem boolCase selection body
      -> selectionSetDirectiveFree body
      -> selectionBooleanVariables selection = boolCase.map Prod.fst := by
  intro hstem hbodyFree
  have hwrap :=
    completeNormalBooleanStem_wrapWithBoolCase_eq hstem
  have hvariables :=
    selectionSetBooleanVariables_wrapWithBoolCase boolCase body
  rw [hwrap] at hvariables
  simpa [selectionSetBooleanVariables,
    selectionSetDirectiveFree_booleanVariables_nil body hbodyFree]
    using hvariables

theorem completeNormalBoolCase_of_variable_mem_iff
    {leftVariables rightVariables : List BoolVar} {boolCase : BoolCase}
    : completeNormalBoolCase leftVariables boolCase
      -> rightVariables.Nodup
      -> (∀ varName, varName ∈ boolCase.map Prod.fst ↔ varName ∈ rightVariables)
      -> completeNormalBoolCase rightVariables boolCase := by
  intro hcomplete hrightNodup hrightMem
  rcases hcomplete with ⟨_hleftNodup, hcaseNodup, _hleftMem⟩
  exact ⟨hrightNodup, hcaseNodup, hrightMem⟩

theorem completeNormalSelectionSet_of_variable_mem_iff
    {schema : Schema} {leftVariables rightVariables : List BoolVar}
    {parentType : Name} {selectionSet : List Selection}
    : completeNormalSelectionSet schema leftVariables parentType selectionSet
      -> rightVariables.Nodup
      -> (∀ varName, varName ∈ rightVariables ↔ varName ∈ leftVariables)
      -> completeNormalSelectionSet schema rightVariables parentType selectionSet := by
  intro hnormal hrightNodup hmemIff
  unfold completeNormalSelectionSet at hnormal ⊢
  rcases hnormal with ⟨hleftNodup, hshape⟩
  refine ⟨hrightNodup, ?_⟩
  cases hleft : leftVariables with
  | nil =>
      cases hright : rightVariables with
      | nil =>
          simpa [hleft, hright] using hshape
      | cons head tail =>
          have hheadMemRight : head ∈ head :: tail := by simp
          have hheadMemLeft : head ∈ leftVariables :=
            (hmemIff head).1 (by simp [hright])
          simp [hleft] at hheadMemLeft
  | cons leftHead leftTail =>
      simp [hleft] at hshape
      cases hright : rightVariables with
      | nil =>
          have hleftHeadMemRight : leftHead ∈ rightVariables :=
            (hmemIff leftHead).2 (by simp [hleft])
          simp [hright] at hleftHeadMemRight
      | cons rightHead rightTail =>
          have hrightConsNodup : (rightHead :: rightTail).Nodup := by
            simpa [hright] using hrightNodup
          rcases hshape with ⟨hnodupSelections, hbranches, hunique⟩
          refine ⟨hnodupSelections, ?_, ?_⟩
          · intro selection hselection
            rcases hbranches selection hselection with
              ⟨boolCase, hcase, body, hstem, hbodyNormal,
                hbodyFree⟩
            refine ⟨boolCase, body, ?_, hstem, hbodyNormal,
              hbodyFree⟩
            exact completeNormalBoolCase_of_variable_mem_iff hcase
              hrightConsNodup (fun varName => by
                rw [hcase.2.2 varName]
                simpa [hleft, hright] using (hmemIff varName).symm)
          · intro left right leftCase rightCase leftBody rightBody
              hleftMem hrightMem hleftCaseComplete hrightCaseComplete
              hleftStem hrightStem hleftBodyFree hrightBodyFree hequiv
            have hleftConsNodup : (leftHead :: leftTail).Nodup := by
              simpa [hleft] using hleftNodup
            have hleftCaseCompleteForLeft :
                completeNormalBoolCase (leftHead :: leftTail) leftCase := by
              exact completeNormalBoolCase_of_variable_mem_iff
                hleftCaseComplete hleftConsNodup (fun varName => by
                  rw [hleftCaseComplete.2.2 varName]
                  simpa [hleft, hright] using hmemIff varName)
            have hrightCaseCompleteForLeft :
                completeNormalBoolCase (leftHead :: leftTail) rightCase := by
              exact completeNormalBoolCase_of_variable_mem_iff
                hrightCaseComplete hleftConsNodup (fun varName => by
                  rw [hrightCaseComplete.2.2 varName]
                  simpa [hleft, hright] using hmemIff varName)
            exact hunique left right leftCase rightCase leftBody rightBody
              hleftMem hrightMem hleftCaseCompleteForLeft
              hrightCaseCompleteForLeft hleftStem hrightStem
              hleftBodyFree hrightBodyFree hequiv

theorem selectionSetBooleanVariables_mem_of_completeNormalBranches
    {schema : Schema} {parentType : Name}
    {variables : List BoolVar} {varName : BoolVar}
    : ∀ {selectionSet : List Selection},
        (∀ selection,
          selection ∈ selectionSet
          -> ∃ boolCase body,
              completeNormalBoolCase variables boolCase
              ∧ completeNormalBooleanStem boolCase selection body
              ∧ selectionSetNormal schema parentType body
              ∧ selectionSetDirectiveFree body)
        -> varName ∈ selectionSetBooleanVariables selectionSet
        -> varName ∈ variables
  | [], _hbranches, hmem => by
      simp [selectionSetBooleanVariables] at hmem
  | selection :: rest, hbranches, hmem => by
      simp [selectionSetBooleanVariables] at hmem
      rcases hmem with hselection | hrest
      · rcases hbranches selection (by simp) with
          ⟨boolCase, body, hcase, hstem, _hbodyNormal,
            hbodyFree⟩
        have hselectionVars :=
          selectionBooleanVariables_of_completeNormalBooleanStem hstem
            hbodyFree
        have hcaseMem : varName ∈ boolCase.map Prod.fst := by
          simpa [hselectionVars] using hselection
        exact (hcase.2.2 varName).1 hcaseMem
      · exact
          selectionSetBooleanVariables_mem_of_completeNormalBranches
            (selectionSet := rest)
            (fun candidate hcandidate =>
              hbranches candidate
                (List.mem_cons_of_mem selection hcandidate))
            hrest

theorem selectionSetBooleanVariables_mem_of_variable_completeNormalBranches
    {schema : Schema} {parentType : Name}
    {variables : List BoolVar} {varName : BoolVar}
    {selection : Selection} {rest : List Selection}
    : (∀ candidate,
        candidate ∈ selection :: rest
        -> ∃ boolCase body,
            completeNormalBoolCase variables boolCase
            ∧ completeNormalBooleanStem boolCase candidate body
            ∧ selectionSetNormal schema parentType body
            ∧ selectionSetDirectiveFree body)
      -> varName ∈ variables
      -> varName ∈ selectionSetBooleanVariables (selection :: rest) := by
  intro hbranches hvar
  rcases hbranches selection (by simp) with
    ⟨boolCase, body, hcase, hstem, _hbodyNormal, hbodyFree⟩
  have hselectionVars :=
    selectionBooleanVariables_of_completeNormalBooleanStem hstem hbodyFree
  have hcaseMem : varName ∈ boolCase.map Prod.fst :=
    (hcase.2.2 varName).2 hvar
  simp [selectionSetBooleanVariables, hselectionVars, hcaseMem]

theorem operationBoolVars_mem_iff_of_completeNormalSelectionSet_cons
    {schema : Schema} {varName : BoolVar} {variables : List BoolVar}
    {parentType : Name} {selectionSet : List Selection}
    : completeNormalSelectionSet schema (varName :: variables) parentType selectionSet
      -> selectionSet ≠ []
      -> ∀ candidate,
          candidate ∈ dedupBoolVars (selectionSetBooleanVariables selectionSet)
          ↔ candidate ∈ varName :: variables := by
  intro hnormal hnonempty candidate
  unfold completeNormalSelectionSet at hnormal
  rcases hnormal with
    ⟨_hvariablesNodup, _hselectionSetNodup, hbranches,
      _hunique⟩
  rw [mem_dedupBoolVars_iff]
  constructor
  · intro hmem
    exact selectionSetBooleanVariables_mem_of_completeNormalBranches
      (schema := schema) (variables := varName :: variables)
      (varName := candidate) hbranches hmem
  · intro hmem
    cases selectionSet with
    | nil =>
        exact False.elim (hnonempty rfl)
    | cons selection rest =>
        exact
          selectionSetBooleanVariables_mem_of_variable_completeNormalBranches
            (schema := schema) (variables := varName :: variables)
            (varName := candidate) hbranches hmem

theorem wrapWithBoolCase_boolCase_injective_of_directiveFree
    : ∀ left right leftBody rightBody,
        selectionSetDirectiveFree leftBody
        -> selectionSetDirectiveFree rightBody
        -> left ≠ []
        -> right ≠ []
        -> wrapWithBoolCase left leftBody = wrapWithBoolCase right rightBody
        -> left = right
  | [], _right, _leftBody, _rightBody, _hleftFree, _hrightFree,
      hleftNe, _hrightNe, _hwrap => by
      exact False.elim (hleftNe rfl)
  | _left, [], _leftBody, _rightBody, _hleftFree, _hrightFree,
      _hleftNe, hrightNe, _hwrap => by
      exact False.elim (hrightNe rfl)
  | (leftVar, leftValue) :: leftRest,
      (rightVar, rightValue) :: rightRest,
      leftBody, rightBody, hleftFree, hrightFree, _hleftNe, _hrightNe,
      hwrap => by
      simp [wrapWithBoolCase] at hwrap
      rcases hwrap with ⟨hdirective, hchild⟩
      have hhead : (leftVar, leftValue) = (rightVar, rightValue) := by
        exact directiveForBit_injective hdirective
      cases hhead
      cases leftRest with
      | nil =>
          cases rightRest with
          | nil =>
              rfl
          | cons rightHead rightTail =>
              rcases rightHead with ⟨rightNextVar, rightNextValue⟩
              have hnot :=
                selectionSetDirectiveFree_wrapWithBoolCase_cons_false
                  rightNextVar rightNextValue rightTail rightBody
              rw [← hchild] at hnot
              exact False.elim (hnot hleftFree)
      | cons leftHead leftTail =>
          rcases leftHead with ⟨leftNextVar, leftNextValue⟩
          cases rightRest with
          | nil =>
              have hnot :=
                selectionSetDirectiveFree_wrapWithBoolCase_cons_false
                  leftNextVar leftNextValue leftTail leftBody
              rw [hchild] at hnot
              exact False.elim (hnot hrightFree)
          | cons rightHead rightTail =>
              have htail :=
                wrapWithBoolCase_boolCase_injective_of_directiveFree
                  ((leftNextVar, leftNextValue) :: leftTail)
                  (rightHead :: rightTail)
                  leftBody rightBody hleftFree hrightFree
                  (by simp) (by simp) hchild
              simp [htail]

theorem completeNormalizeRootSelectionSet_normal_nil
    (schema : Schema)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (parentType : Name) (selectionSet normalizedSelectionSet : List Selection)
    (hparentObject : objectTypeNameBool schema parentType = true)
    : completeNormalizeRootSelectionSet schema [] parentType selectionSet
        = normalizedSelectionSet
      -> completeNormalSelectionSet schema [] parentType normalizedSelectionSet := by
  intro hnormalized
  unfold completeNormalizeRootSelectionSet at hnormalized
  simp [allBoolCases, wrapWithBoolCase] at hnormalized
  cases hbody :
      normalizeSelectionSet schema parentType
        (filterSelectionSetBoolCase [] selectionSet) with
  | nil =>
      simp [hbody] at hnormalized
      subst normalizedSelectionSet
      simp [completeNormalSelectionSet, selectionSetNormal,
        selectionSetGroundTyped, selectionsAllFields, hparentObject,
        selectionSetNonRedundant, responseNamesNodup,
        inlineFragmentTypeConditionsNodup, selectionSetDirectiveFree]
  | cons selection rest =>
      simp [hbody] at hnormalized
      cases hnormalized
      refine ⟨by simp, ?_, ?_⟩
      · simpa [hbody] using
        GroundTypeNormalization.normalizeSelectionSet_normal schema hschema
          parentType
          (filterSelectionSetBoolCase [] selectionSet) hparentObject
      · simpa [hbody] using
          GroundTypeNormalization.normalizeSelectionSet_directiveFree schema
            parentType
            (filterSelectionSetBoolCase [] selectionSet)
            (filterSelectionSetBoolCase_directiveFree schema []
              selectionSet)

private def completeNormalizeRootBranch
    (schema : Schema) (parentType : Name) (selectionSet : List Selection)
    (boolCase : BoolCase)
    : List Selection :=
  match normalizeSelectionSet schema parentType
          (filterSelectionSetBoolCase boolCase selectionSet) with
  | [] => []
  | selection :: rest =>
      wrapWithBoolCase boolCase (selection :: rest)

theorem nodup_flatten_map_of_nil_or_singleton_injective
    {α β : Type} {items : List α} {f : α -> List β}
    : items.Nodup
      -> (∀ item, item ∈ items -> f item = [] ∨ ∃ value, f item = [value])
      -> (∀ left,
            left ∈ items
            -> ∀ right,
                right ∈ items
                -> ∀ value, value ∈ f left -> value ∈ f right -> left = right)
      -> (items.map f).flatten.Nodup := by
  intro hnodup hshape hinjective
  induction items with
  | nil =>
      simp
  | cons head rest ih =>
      have hparts := List.nodup_cons.mp hnodup
      have hheadNotMem : head ∉ rest := hparts.1
      have hrestNodup : rest.Nodup := hparts.2
      have hrestShape :
          ∀ item, item ∈ rest ->
            f item = [] ∨ ∃ value, f item = [value] := by
        intro item hitem
        exact hshape item (List.mem_cons_of_mem head hitem)
      have hrestInjective :
          ∀ left, left ∈ rest ->
          ∀ right, right ∈ rest ->
          ∀ value, value ∈ f left -> value ∈ f right -> left = right := by
        intro left hleft right hright value hleftValue hrightValue
        exact hinjective left (List.mem_cons_of_mem head hleft)
          right (List.mem_cons_of_mem head hright)
          value hleftValue hrightValue
      have hrestFlatten :=
        ih hrestNodup hrestShape hrestInjective
      rcases hshape head (by simp) with hheadNil | ⟨headValue, hheadSingle⟩
      · simpa [hheadNil] using hrestFlatten
      · simp [hheadSingle]
        refine ⟨?_, hrestFlatten⟩
        intro rightItem hrightItemMem hheadValueMem
        have hitemsEq :=
          hinjective head (by simp)
            rightItem (List.mem_cons_of_mem head hrightItemMem)
            headValue (by simp [hheadSingle]) hheadValueMem
        subst rightItem
        exact hheadNotMem hrightItemMem

theorem completeNormalizeRootBranch_nil_or_singleton
    (schema : Schema) (parentType : Name) (selectionSet : List Selection)
    {boolCase : BoolCase}
    : boolCase ≠ []
      -> completeNormalizeRootBranch schema parentType selectionSet boolCase = []
          ∨ ∃ selection,
              completeNormalizeRootBranch schema parentType selectionSet boolCase
              = [selection] := by
  intro hne
  unfold completeNormalizeRootBranch
  cases hbody :
      normalizeSelectionSet schema parentType
        (filterSelectionSetBoolCase boolCase selectionSet) with
  | nil =>
      simp
  | cons selection rest =>
      rcases wrapWithBoolCase_singleton_of_ne boolCase
        (selection :: rest) hne with ⟨wrappedSelection, hwrap⟩
      exact Or.inr ⟨wrappedSelection, by simp [hwrap]⟩

theorem normalize_filterSelectionSetBoolCase_directiveFree
    (schema : Schema) (parentType : Name) (boolCase : BoolCase)
    (selectionSet : List Selection)
    : selectionSetDirectiveFree
        (normalizeSelectionSet schema parentType
          (filterSelectionSetBoolCase boolCase selectionSet)) := by
  exact GroundTypeNormalization.normalizeSelectionSet_directiveFree schema
    parentType
    (filterSelectionSetBoolCase boolCase selectionSet)
    (filterSelectionSetBoolCase_directiveFree schema boolCase
      selectionSet)

theorem completeNormalizeRootBranch_mem_boolCase_injective
    (schema : Schema) (parentType : Name) (selectionSet : List Selection)
    {left right : BoolCase} {selection : Selection}
    : left ≠ []
      -> right ≠ []
      -> selection ∈ completeNormalizeRootBranch schema parentType selectionSet left
      -> selection ∈ completeNormalizeRootBranch schema parentType selectionSet right
      -> left = right := by
  intro hleftNe hrightNe hleftMem hrightMem
  unfold completeNormalizeRootBranch at hleftMem hrightMem
  cases hleftBody :
      normalizeSelectionSet schema parentType
        (filterSelectionSetBoolCase left selectionSet) with
  | nil =>
      simp [hleftBody] at hleftMem
  | cons leftHead leftTail =>
      cases hrightBody :
          normalizeSelectionSet schema parentType
            (filterSelectionSetBoolCase right selectionSet) with
      | nil =>
          simp [hrightBody] at hrightMem
      | cons rightHead rightTail =>
          simp [hleftBody] at hleftMem
          simp [hrightBody] at hrightMem
          have hleftBodyFree :
              selectionSetDirectiveFree (leftHead :: leftTail) := by
            simpa [hleftBody] using
              normalize_filterSelectionSetBoolCase_directiveFree schema parentType left selectionSet
          have hrightBodyFree :
              selectionSetDirectiveFree (rightHead :: rightTail) := by
            simpa [hrightBody] using
              normalize_filterSelectionSetBoolCase_directiveFree schema parentType right selectionSet
          rcases wrapWithBoolCase_singleton_of_ne left
            (leftHead :: leftTail) hleftNe with
            ⟨leftSelection, hleftWrap⟩
          rw [hleftWrap] at hleftMem
          simp at hleftMem
          subst selection
          rcases wrapWithBoolCase_singleton_of_ne right
            (rightHead :: rightTail) hrightNe with
            ⟨rightSelection, hrightWrap⟩
          rw [hrightWrap] at hrightMem
          simp at hrightMem
          subst rightSelection
          have hwrapEq :
              wrapWithBoolCase left (leftHead :: leftTail) =
                wrapWithBoolCase right (rightHead :: rightTail) := by
            rw [hleftWrap, hrightWrap]
          exact wrapWithBoolCase_boolCase_injective_of_directiveFree
            left right (leftHead :: leftTail) (rightHead :: rightTail)
            hleftBodyFree hrightBodyFree hleftNe hrightNe hwrapEq

theorem completeNormalBooleanStem_boolCase_eq_of_generated
    {varName : BoolVar} {variables : List BoolVar}
    {generatedCase stemCase : BoolCase}
    {generatedBody stemBody : List Selection} {selection : Selection}
    : generatedCase ∈ allBoolCases (varName :: variables)
      -> completeNormalBoolCase (varName :: variables) stemCase
      -> selectionSetDirectiveFree generatedBody
      -> selectionSetDirectiveFree stemBody
      -> selection ∈ wrapWithBoolCase generatedCase generatedBody
      -> completeNormalBooleanStem stemCase selection stemBody
      -> generatedCase = stemCase := by
  intro hgenerated hstemComplete hgeneratedFree hstemFree
    hselection hstem
  have hgeneratedNe :=
    boolCase_ne_nil_of_mem_allBoolCases_cons hgenerated
  have hstemNe :=
    completeNormalBoolCase_ne_nil_of_variables_cons hstemComplete
  rcases wrapWithBoolCase_singleton_of_ne generatedCase
    generatedBody hgeneratedNe with
    ⟨generatedSelection, hgeneratedWrap⟩
  rw [hgeneratedWrap] at hselection
  simp at hselection
  subst selection
  have hstemWrap :=
    completeNormalBooleanStem_wrapWithBoolCase_eq hstem
  have hwrapEq :
      wrapWithBoolCase generatedCase generatedBody =
        wrapWithBoolCase stemCase stemBody := by
    rw [hgeneratedWrap, hstemWrap]
  exact wrapWithBoolCase_boolCase_injective_of_directiveFree
    generatedCase stemCase generatedBody stemBody
    hgeneratedFree hstemFree hgeneratedNe hstemNe hwrapEq

theorem completeNormalizeRootSelectionSet_normal_cons
    (schema : Schema)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (varName : BoolVar) (variables : List BoolVar)
    (hvariablesNodup : (varName :: variables).Nodup)
    (parentType : Name) (selectionSet normalizedSelectionSet : List Selection)
    (hparentObject : objectTypeNameBool schema parentType = true)
    : completeNormalizeRootSelectionSet schema (varName :: variables)
          parentType selectionSet
        = normalizedSelectionSet
      -> completeNormalSelectionSet schema (varName :: variables)
          parentType normalizedSelectionSet := by
  intro hnormalized
  unfold completeNormalizeRootSelectionSet at hnormalized
  change
      List.flatten
          ((allBoolCases (varName :: variables)).map
            (completeNormalizeRootBranch schema parentType selectionSet)) =
        normalizedSelectionSet at hnormalized
  cases hflatten :
      List.flatten
        ((allBoolCases (varName :: variables)).map
          (completeNormalizeRootBranch schema parentType selectionSet)) with
  | nil =>
      simp [hflatten] at hnormalized
      subst normalizedSelectionSet
      unfold completeNormalSelectionSet
      simp [hvariablesNodup]
  | cons first rest =>
      simp [hflatten] at hnormalized
      cases hnormalized
      have hflattenNodup :
          (List.flatten
            ((allBoolCases (varName :: variables)).map
              (completeNormalizeRootBranch schema parentType selectionSet))).Nodup := by
        apply nodup_flatten_map_of_nil_or_singleton_injective
        · exact allBoolCases_nodup hvariablesNodup
        · intro boolCase hcase
          exact completeNormalizeRootBranch_nil_or_singleton schema
            parentType selectionSet
            (boolCase_ne_nil_of_mem_allBoolCases_cons hcase)
        · intro left hleft right hright selection hleftSelection
            hrightSelection
          exact completeNormalizeRootBranch_mem_boolCase_injective
            schema parentType selectionSet
            (boolCase_ne_nil_of_mem_allBoolCases_cons hleft)
            (boolCase_ne_nil_of_mem_allBoolCases_cons hright)
            hleftSelection hrightSelection
      simp only [completeNormalSelectionSet]
      refine ⟨hvariablesNodup, ?_, ?_, ?_⟩
      · simpa [hflatten] using hflattenNodup
      · intro selection hselection
        have hselectionFlatten :
            selection ∈
              List.flatten
                ((allBoolCases (varName :: variables)).map
                  (completeNormalizeRootBranch schema parentType
                    selectionSet)) := by
          simpa [hflatten] using hselection
        rw [List.mem_flatten] at hselectionFlatten
        rcases hselectionFlatten with
          ⟨branch, hbranchMem, hselectionBranch⟩
        rw [List.mem_map] at hbranchMem
        rcases hbranchMem with
          ⟨boolCase, hcase, hbranchEq⟩
        subst branch
        unfold completeNormalizeRootBranch at hselectionBranch
        cases hbody :
            normalizeSelectionSet schema parentType
              (filterSelectionSetBoolCase boolCase
                selectionSet) with
        | nil =>
            simp [hbody] at hselectionBranch
        | cons bodyHead bodyTail =>
            simp [hbody] at hselectionBranch
            refine ⟨boolCase, bodyHead :: bodyTail, ?_, ?_, ?_, ?_⟩
            · exact completeNormalBoolCase_of_mem_allBoolCases
                hvariablesNodup hcase
            · exact completeNormalBooleanStem_of_mem_wrapWithBoolCase
                (boolCase_ne_nil_of_mem_allBoolCases_cons hcase)
                hselectionBranch
            · simpa [hbody] using
                GroundTypeNormalization.normalizeSelectionSet_normal schema
                  hschema parentType
                  (filterSelectionSetBoolCase boolCase
                    selectionSet) hparentObject
            · simpa [hbody] using
                normalize_filterSelectionSetBoolCase_directiveFree schema parentType boolCase selectionSet
      · intro left right leftCase rightCase leftBody rightBody
          hleftMem hrightMem hleftComplete hrightComplete hleftStem
          hrightStem hleftBodyFree hrightBodyFree hequiv
        have hleftFlatten :
            left ∈
              List.flatten
                ((allBoolCases (varName :: variables)).map
                  (completeNormalizeRootBranch schema parentType
                    selectionSet)) := by
          simpa [hflatten] using hleftMem
        rw [List.mem_flatten] at hleftFlatten
        rcases hleftFlatten with
          ⟨leftBranch, hleftBranchMem, hleftInBranch⟩
        rw [List.mem_map] at hleftBranchMem
        rcases hleftBranchMem with
          ⟨leftGeneratedCase, hleftGeneratedMem, hleftBranchEq⟩
        subst leftBranch
        have hrightFlatten :
            right ∈
              List.flatten
                ((allBoolCases (varName :: variables)).map
                  (completeNormalizeRootBranch schema parentType
                    selectionSet)) := by
          simpa [hflatten] using hrightMem
        rw [List.mem_flatten] at hrightFlatten
        rcases hrightFlatten with
          ⟨rightBranch, hrightBranchMem, hrightInBranch⟩
        rw [List.mem_map] at hrightBranchMem
        rcases hrightBranchMem with
          ⟨rightGeneratedCase, hrightGeneratedMem, hrightBranchEq⟩
        subst rightBranch
        have hleftGeneratedEq :
            leftGeneratedCase = leftCase := by
          have hleftInBranchForParse := hleftInBranch
          unfold completeNormalizeRootBranch at hleftInBranchForParse
          cases hleftBody :
              normalizeSelectionSet schema parentType
                (filterSelectionSetBoolCase leftGeneratedCase selectionSet) with
          | nil =>
              simp [hleftBody] at hleftInBranchForParse
          | cons generatedHead generatedTail =>
              simp [hleftBody] at hleftInBranchForParse
              have hgeneratedFree :
                  selectionSetDirectiveFree
                    (generatedHead :: generatedTail) := by
                simpa [hleftBody] using
                  normalize_filterSelectionSetBoolCase_directiveFree schema parentType leftGeneratedCase selectionSet
              exact completeNormalBooleanStem_boolCase_eq_of_generated
                hleftGeneratedMem hleftComplete hgeneratedFree
                hleftBodyFree hleftInBranchForParse hleftStem
        have hrightGeneratedEq :
            rightGeneratedCase = rightCase := by
          have hrightInBranchForParse := hrightInBranch
          unfold completeNormalizeRootBranch at hrightInBranchForParse
          cases hrightBody :
              normalizeSelectionSet schema parentType
                (filterSelectionSetBoolCase rightGeneratedCase selectionSet) with
          | nil =>
              simp [hrightBody] at hrightInBranchForParse
          | cons generatedHead generatedTail =>
              simp [hrightBody] at hrightInBranchForParse
              have hgeneratedFree :
                  selectionSetDirectiveFree
                    (generatedHead :: generatedTail) := by
                simpa [hrightBody] using
                  normalize_filterSelectionSetBoolCase_directiveFree schema parentType rightGeneratedCase selectionSet
              exact completeNormalBooleanStem_boolCase_eq_of_generated
                hrightGeneratedMem hrightComplete hgeneratedFree
                hrightBodyFree hrightInBranchForParse hrightStem
        have hgeneratedEquiv :
            completeNormalBoolCasesEquivalent leftGeneratedCase
              rightGeneratedCase := by
          subst leftCase
          subst rightCase
          exact hequiv
        have hgeneratedEq :
            leftGeneratedCase = rightGeneratedCase :=
          boolCase_eq_of_mem_allBoolCases_equivalent hvariablesNodup
            hleftGeneratedMem hrightGeneratedMem hgeneratedEquiv
        rw [← hgeneratedEq] at hrightInBranch
        rcases completeNormalizeRootBranch_nil_or_singleton schema parentType
            selectionSet
            (boolCase_ne_nil_of_mem_allBoolCases_cons
              hleftGeneratedMem) with hbranchNil | ⟨onlySelection, hbranchSingle⟩
        · simp [hbranchNil] at hleftInBranch
        · rw [hbranchSingle] at hleftInBranch hrightInBranch
          simp at hleftInBranch hrightInBranch
          subst left
          subst right
          rfl

theorem completeNormalizeOperation_normal (schema : Schema) (operation : Operation)
    : completeNormalizeOperationNormal schema operation := by
  intro hschema hvalid
  have hrootEq :
      (operation.rootType schema) = schema.queryType :=
    Validation.operationDefinitionValid_rootType_eq hvalid
  have hrootObject :
      schema.objectType (operation.rootType schema) := by
    simpa [hrootEq] using hschema.2.1
  have hrootObjectBool :
      objectTypeNameBool schema (operation.rootType schema) = true :=
    GroundTypeNormalization.objectTypeNameBool_eq_true_of_objectType_forNormality
      schema hrootObject
  unfold completeNormalizeOperation
  cases hvariables : operationBoolVars operation with
  | nil =>
      simp
      let normalizedSelectionSet :=
        completeNormalizeRootSelectionSet schema [] (operation.rootType schema)
          operation.selectionSet
      have hrootNormal :
          completeNormalSelectionSet schema [] (operation.rootType schema)
            normalizedSelectionSet :=
        completeNormalizeRootSelectionSet_normal_nil schema hschema
          (operation.rootType schema) operation.selectionSet normalizedSelectionSet
          hrootObjectBool rfl
      have hnormalizedFree :
          selectionSetDirectiveFree normalizedSelectionSet := by
        unfold completeNormalSelectionSet at hrootNormal
        exact hrootNormal.2.2
      have hnormalizedVars :
          operationBoolVars
              { operation with selectionSet := normalizedSelectionSet } =
            [] := by
        unfold operationBoolVars
        simp [selectionSetDirectiveFree_booleanVariables_nil
          normalizedSelectionSet hnormalizedFree, dedupBoolVars]
      unfold completeNormalOperation
      change completeNormalSelectionSet schema
        (operationBoolVars { operation with selectionSet := normalizedSelectionSet })
        (({ operation with selectionSet := normalizedSelectionSet }).rootType schema)
        normalizedSelectionSet
      rw [hnormalizedVars]
      simpa [Operation.rootType, OperationType.rootType] using hrootNormal
  | cons varName variables =>
      simp
      have hsourceVarsNodup : (varName :: variables).Nodup := by
        have hopVarsNodup : (operationBoolVars operation).Nodup := by
          unfold operationBoolVars
          exact dedupBoolVars_nodup
            (selectionSetBooleanVariables operation.selectionSet)
        simpa [hvariables] using hopVarsNodup
      let normalizedSelectionSet :=
        completeNormalizeRootSelectionSet schema (varName :: variables)
          (operation.rootType schema) operation.selectionSet
      have hrootNormal :
          completeNormalSelectionSet schema (varName :: variables)
            (operation.rootType schema) normalizedSelectionSet :=
        completeNormalizeRootSelectionSet_normal_cons schema hschema
          varName variables hsourceVarsNodup (operation.rootType schema)
          operation.selectionSet normalizedSelectionSet hrootObjectBool rfl
      by_cases hnormalizedEmpty : normalizedSelectionSet = []
      · unfold completeNormalOperation operationBoolVars
        have hnormalizedEmptyRoot :
            completeNormalizeRootSelectionSet schema (varName :: variables)
                schema.queryType operation.selectionSet =
              [] := by
          simpa [normalizedSelectionSet, Operation.rootType,
            OperationType.rootType] using hnormalizedEmpty
        simp [completeNormalSelectionSet, selectionSetNormal,
          selectionSetGroundTyped, selectionsAllFields,
          selectionSetNonRedundant, responseNamesNodup,
          inlineFragmentTypeConditionsNodup, selectionSetBooleanVariables,
          selectionSetDirectiveFree, selectionsAllInlineFragments,
          dedupBoolVars, Operation.rootType, OperationType.rootType,
          hnormalizedEmptyRoot]
      · have hnormalizedVarsNodup :
            (operationBoolVars
              { operation with selectionSet := normalizedSelectionSet }).Nodup := by
          unfold operationBoolVars
          exact dedupBoolVars_nodup
            (selectionSetBooleanVariables normalizedSelectionSet)
        have hnormalizedVarsIff :
            ∀ candidate,
              candidate ∈ operationBoolVars
                  { operation with selectionSet := normalizedSelectionSet }
                ↔ candidate ∈ varName :: variables := by
          intro candidate
          simpa [operationBoolVars] using
            operationBoolVars_mem_iff_of_completeNormalSelectionSet_cons
              hrootNormal hnormalizedEmpty candidate
        have htransported :=
          completeNormalSelectionSet_of_variable_mem_iff hrootNormal
            hnormalizedVarsNodup hnormalizedVarsIff
        unfold completeNormalOperation
        exact htransported

end CompleteNormalization

end NormalForm

end GraphQL
