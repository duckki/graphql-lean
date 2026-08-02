import Proofs.GraphQL.Theories.ResponseShape.Denotation

/-!
Exclusivity facts for complete-minterm response-shape clauses.
-/

namespace GraphQL

namespace ResponseShape

namespace Clause

private theorem namesStrictlyIncreasing_pairwise :
    ∀ names : List Name,
      namesStrictlyIncreasing names = true ->
      List.Pairwise (fun left right : Name => left < right) names
  | [], _hincreasing => by simp
  | [_name], _hincreasing => by simp
  | left :: right :: rest, hincreasing => by
      simp only [namesStrictlyIncreasing, Bool.and_eq_true,
        decide_eq_true_eq] at hincreasing
      have htail :=
        namesStrictlyIncreasing_pairwise (right :: rest) hincreasing.2
      apply List.pairwise_cons.mpr
      constructor
      · intro candidate hcandidate
        rcases List.mem_cons.mp hcandidate with hcandidate | hcandidate
        · subst candidate
          exact hincreasing.1
        · exact String.lt_trans hincreasing.1
            ((List.pairwise_cons.mp htail).1 candidate hcandidate)
      · exact htail

private theorem literals_pairwise_of_valid
    {support : List NormalForm.BoolVar} {clause : Clause}
    (hvalid : clause.Valid support) :
    List.Pairwise (fun left right : BoolLiteral => left.1 < right.1)
      clause.literals := by
  unfold Valid validBool at hvalid
  simp only [Bool.and_eq_true] at hvalid
  have hnames := namesStrictlyIncreasing_pairwise
    (clause.literals.map Prod.fst) hvalid.1
  change List.Pairwise
    (fun left right : NormalForm.BoolVar × Bool => left.1 < right.1)
    clause.literals
  exact List.pairwise_map.mp hnames

private theorem literals_eq_of_pairwise_of_mem_iff :
    ∀ (left right : List BoolLiteral),
      List.Pairwise (fun left right : BoolLiteral => left.1 < right.1) left ->
      List.Pairwise (fun left right : BoolLiteral => left.1 < right.1) right ->
      (∀ literal, literal ∈ left ↔ literal ∈ right) ->
      left = right
  | [], [], _hleft, _hright, _hmem => rfl
  | [], right :: rights, _hleft, _hright, hmem => by
      have : right ∈ ([] : List BoolLiteral) :=
        (hmem right).mpr (by simp)
      simp at this
  | left :: lefts, [], _hleft, _hright, hmem => by
      have : left ∈ ([] : List BoolLiteral) :=
        (hmem left).mp (by simp)
      simp at this
  | left :: lefts, right :: rights, hleft, hright, hmem => by
      have hleftMem : left = right ∨ left ∈ rights :=
        List.mem_cons.mp ((hmem left).mp (by simp))
      have hrightMem : right = left ∨ right ∈ lefts :=
        List.mem_cons.mp ((hmem right).mpr (by simp))
      have hheads : left = right := by
        rcases hleftMem with hheads | hleftTail
        · exact hheads
        · rcases hrightMem with hheads | hrightTail
          · exact hheads.symm
          · exact False.elim
              (String.lt_asymm
                ((List.pairwise_cons.mp hleft).1 right hrightTail)
                ((List.pairwise_cons.mp hright).1 left hleftTail))
      subst right
      have hleftHeadNot : left ∉ lefts := by
        intro hleftTail
        exact String.lt_irrefl left.1
          ((List.pairwise_cons.mp hleft).1 left hleftTail)
      have hrightHeadNot : left ∉ rights := by
        intro hrightTail
        exact String.lt_irrefl left.1
          ((List.pairwise_cons.mp hright).1 left hrightTail)
      have htailMem : ∀ literal, literal ∈ lefts ↔ literal ∈ rights := by
        intro literal
        by_cases heq : literal = left
        · subst literal
          simp [hleftHeadNot, hrightHeadNot]
        · simpa [heq] using hmem literal
      rw [literals_eq_of_pairwise_of_mem_iff lefts rights
        (List.pairwise_cons.mp hleft).2
        (List.pairwise_cons.mp hright).2 htailMem]

/--
Two complete minterms over one support cannot both activate under an assignment
unless they are the same clause.
-/
theorem eq_of_completeMinterm_of_holdsInBool
    {support : List NormalForm.BoolVar} {assignment : NormalForm.BoolCase}
    {left right : Clause}
    (hleftComplete : left.CompleteMinterm support)
    (hrightComplete : right.CompleteMinterm support)
    (hleftHolds : left.holdsInBool assignment = true)
    (hrightHolds : right.holdsInBool assignment = true) :
    left = right := by
  unfold CompleteMinterm completeMintermBool at hleftComplete hrightComplete
  simp only [Bool.and_eq_true] at hleftComplete hrightComplete
  have hleftValid : left.Valid support := hleftComplete.1.2
  have hrightValid : right.Valid support := hrightComplete.1.2
  have hleftHolds' : left.HoldsIn assignment :=
    (holdsInBool_iff assignment left).mp hleftHolds
  have hrightHolds' : right.HoldsIn assignment :=
    (holdsInBool_iff assignment right).mp hrightHolds
  have hliterals : left.literals = right.literals := by
    apply literals_eq_of_pairwise_of_mem_iff left.literals right.literals
      (literals_pairwise_of_valid hleftValid)
      (literals_pairwise_of_valid hrightValid)
    intro literal
    constructor
    · intro hleftMem
      have hleftValid' := hleftValid
      unfold Valid validBool at hleftValid'
      simp only [Bool.and_eq_true] at hleftValid'
      have hsupportContains :=
        List.all_eq_true.mp hleftValid'.2 literal hleftMem
      have hsupportMem : literal.1 ∈ support :=
        List.contains_iff_mem.mp hsupportContains
      have hrightAny :=
        List.all_eq_true.mp hrightComplete.2 literal.1 hsupportMem
      rcases List.any_eq_true.mp hrightAny with
        ⟨⟨candidateName, candidateValue⟩, hrightMem, hnameEq⟩
      simp only [beq_iff_eq] at hnameEq
      have hleftValue := hleftHolds' literal hleftMem
      have hrightValue := hrightHolds'
        (candidateName, candidateValue) hrightMem
      rcases literal with ⟨literalName, literalValue⟩
      simp only at hnameEq
      subst candidateName
      have hvalueEq : literalValue = candidateValue :=
        Option.some.inj (hleftValue.symm.trans hrightValue)
      subst candidateValue
      exact hrightMem
    · intro hrightMem
      have hrightValid' := hrightValid
      unfold Valid validBool at hrightValid'
      simp only [Bool.and_eq_true] at hrightValid'
      have hsupportContains :=
        List.all_eq_true.mp hrightValid'.2 literal hrightMem
      have hsupportMem : literal.1 ∈ support :=
        List.contains_iff_mem.mp hsupportContains
      have hleftAny :=
        List.all_eq_true.mp hleftComplete.2 literal.1 hsupportMem
      rcases List.any_eq_true.mp hleftAny with
        ⟨⟨candidateName, candidateValue⟩, hleftMem, hnameEq⟩
      simp only [beq_iff_eq] at hnameEq
      have hrightValue := hrightHolds' literal hrightMem
      have hleftValue := hleftHolds'
        (candidateName, candidateValue) hleftMem
      rcases literal with ⟨literalName, literalValue⟩
      simp only at hnameEq
      subst candidateName
      have hvalueEq : literalValue = candidateValue :=
        Option.some.inj (hrightValue.symm.trans hleftValue)
      subst candidateValue
      exact hleftMem
  cases left
  cases right
  simpa only [GraphQL.ResponseShape.Clause.mk.injEq] using hliterals

/-- At most one clause in a duplicate-free complete-minterm list can activate. -/
theorem filter_holdsInBool_length_le_one
    {support : List NormalForm.BoolVar} (assignment : NormalForm.BoolCase) :
    ∀ (clauses : List Clause),
      clauses.Nodup ->
      (∀ clause ∈ clauses, clause.CompleteMinterm support) ->
      (clauses.filter
        (fun clause => clause.holdsInBool assignment)).length ≤ 1
  | [], _hnodup, _hcomplete => by simp
  | clause :: rest, hnodup, hcomplete => by
      have hnodupParts := List.nodup_cons.mp hnodup
      have hclauseComplete := hcomplete clause (by simp)
      have hrestComplete :
          ∀ candidate ∈ rest, candidate.CompleteMinterm support := by
        intro candidate hcandidate
        exact hcomplete candidate (List.mem_cons_of_mem clause hcandidate)
      by_cases hholds : clause.holdsInBool assignment = true
      · have hfilteredRest :
            rest.filter (fun candidate => candidate.holdsInBool assignment) = [] := by
          apply List.eq_nil_iff_forall_not_mem.mpr
          intro candidate hcandidateFiltered
          have hparts := List.mem_filter.mp hcandidateFiltered
          have heq := eq_of_completeMinterm_of_holdsInBool
            hclauseComplete (hrestComplete candidate hparts.1)
            hholds hparts.2
          exact hnodupParts.1 (heq.symm ▸ hparts.1)
        simp [hholds, hfilteredRest]
      · simp [hholds]
        exact filter_holdsInBool_length_le_one assignment rest
          hnodupParts.2 hrestComplete

end Clause

end ResponseShape

end GraphQL
