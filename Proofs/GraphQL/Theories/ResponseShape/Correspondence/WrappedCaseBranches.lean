import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.OperationNormality

/-!
Boolean-case wrapping and variable-support facts shared by response-shape
correspondence proofs.
-/

namespace GraphQL

namespace ResponseShape

/-- Wrap a nonempty selection set with a Boolean case, preserving an empty body. -/
def wrapNonemptyCase (boolCase : NormalForm.BoolCase) (body : List Selection)
    : List Selection :=
  match body with
  | [] => []
  | selection :: rest =>
      NormalForm.wrapWithBoolCase boolCase (selection :: rest)

/-- Wrapping a body with the empty Boolean case leaves it unchanged. -/
theorem wrapNonemptyCase_nil (body : List Selection)
    : wrapNonemptyCase [] body = body := by
  cases body <;> rfl

private theorem wrappedCaseBranches_variables_subset
    (support : List NormalForm.BoolVar)
    (bodies : NormalForm.BoolCase → List Selection)
    : ∀ cases : List NormalForm.BoolCase,
        (∀ boolCase, boolCase ∈ cases → boolCase ∈ NormalForm.allBoolCases support)
        → (∀ boolCase,
            boolCase ∈ cases
            → NormalForm.selectionSetBooleanVariables (bodies boolCase) = [])
        → ∀ varName,
            varName
              ∈ NormalForm.selectionSetBooleanVariables
                  (List.flatten
                    (cases.map
                      (fun boolCase => wrapNonemptyCase boolCase (bodies boolCase))))
            → varName ∈ support
  | [], _hgenerated, _hbodyVariables, varName, hmem => by
      simp [NormalForm.selectionSetBooleanVariables] at hmem
  | boolCase :: rest, hgenerated, hbodyVariables, varName, hmem => by
      have hcaseGenerated :
          boolCase ∈ NormalForm.allBoolCases support :=
        hgenerated boolCase (by simp)
      have hcaseNames : boolCase.map Prod.fst = support :=
        NormalForm.CompleteNormalization.boolCase_map_fst_of_mem_allBoolCases
          hcaseGenerated
      have hrestGenerated :
          ∀ candidate, candidate ∈ rest →
            candidate ∈ NormalForm.allBoolCases support := by
        intro candidate hcandidate
        exact hgenerated candidate (List.mem_cons_of_mem boolCase hcandidate)
      have hrestBodyVariables :
          ∀ candidate, candidate ∈ rest →
            NormalForm.selectionSetBooleanVariables (bodies candidate) = [] := by
        intro candidate hcandidate
        exact hbodyVariables candidate
          (List.mem_cons_of_mem boolCase hcandidate)
      cases hbody : bodies boolCase with
      | nil =>
          apply wrappedCaseBranches_variables_subset support bodies rest
            hrestGenerated hrestBodyVariables varName
          simpa [wrapNonemptyCase, hbody] using hmem
      | cons head tail =>
          have hbodyVars :
              NormalForm.selectionSetBooleanVariables (head :: tail) = [] := by
            simpa [hbody] using hbodyVariables boolCase (by simp)
          have hbranchVariables :
              NormalForm.selectionSetBooleanVariables
                  (wrapNonemptyCase boolCase (bodies boolCase)) = support := by
            rw [hbody, wrapNonemptyCase,
              NormalForm.CompleteNormalization.selectionSetBooleanVariables_wrapWithBoolCase,
              hbodyVars, List.append_nil, hcaseNames]
          rw [List.map_cons, List.flatten_cons,
            NormalForm.CompleteNormalization.selectionSetBooleanVariables_append,
            hbranchVariables] at hmem
          rcases List.mem_append.mp hmem with hcurrent | hrest
          · exact hcurrent
          · exact wrappedCaseBranches_variables_subset support bodies rest
              hrestGenerated hrestBodyVariables varName hrest

private theorem wrappedCaseBranches_variables_cover
    (support : List NormalForm.BoolVar)
    (bodies : NormalForm.BoolCase → List Selection)
    : ∀ cases : List NormalForm.BoolCase,
        (∀ boolCase, boolCase ∈ cases → boolCase ∈ NormalForm.allBoolCases support)
        → (∀ boolCase,
            boolCase ∈ cases
            → NormalForm.selectionSetBooleanVariables (bodies boolCase) = [])
        → List.flatten
            (cases.map (fun boolCase => wrapNonemptyCase boolCase (bodies boolCase)))
          ≠ []
        → ∀ varName,
            varName ∈ support
            → varName
              ∈ NormalForm.selectionSetBooleanVariables
                  (List.flatten
                    (cases.map
                      (fun boolCase => wrapNonemptyCase boolCase (bodies boolCase))))
  | [], _hgenerated, _hbodyVariables, hnonempty, _varName, _hvar => by
      exact (hnonempty rfl).elim
  | boolCase :: rest, hgenerated, hbodyVariables, hnonempty, varName, hvar => by
      have hcaseGenerated :
          boolCase ∈ NormalForm.allBoolCases support :=
        hgenerated boolCase (by simp)
      have hcaseNames : boolCase.map Prod.fst = support :=
        NormalForm.CompleteNormalization.boolCase_map_fst_of_mem_allBoolCases
          hcaseGenerated
      have hrestGenerated :
          ∀ candidate, candidate ∈ rest →
            candidate ∈ NormalForm.allBoolCases support := by
        intro candidate hcandidate
        exact hgenerated candidate (List.mem_cons_of_mem boolCase hcandidate)
      have hrestBodyVariables :
          ∀ candidate, candidate ∈ rest →
            NormalForm.selectionSetBooleanVariables (bodies candidate) = [] := by
        intro candidate hcandidate
        exact hbodyVariables candidate
          (List.mem_cons_of_mem boolCase hcandidate)
      cases hbody : bodies boolCase with
      | nil =>
          have hrestNonempty :
              List.flatten (rest.map
                (fun boolCase => wrapNonemptyCase boolCase (bodies boolCase))) ≠ [] := by
            simpa [wrapNonemptyCase, hbody] using hnonempty
          have hrestCover := wrappedCaseBranches_variables_cover support bodies rest
            hrestGenerated hrestBodyVariables hrestNonempty varName hvar
          simpa [wrapNonemptyCase, hbody] using hrestCover
      | cons head tail =>
          have hbodyVars :
              NormalForm.selectionSetBooleanVariables (head :: tail) = [] := by
            simpa [hbody] using hbodyVariables boolCase (by simp)
          have hbranchVariables :
              NormalForm.selectionSetBooleanVariables
                  (wrapNonemptyCase boolCase (bodies boolCase)) = support := by
            rw [hbody, wrapNonemptyCase,
              NormalForm.CompleteNormalization.selectionSetBooleanVariables_wrapWithBoolCase,
              hbodyVars, List.append_nil, hcaseNames]
          rw [List.map_cons, List.flatten_cons,
            NormalForm.CompleteNormalization.selectionSetBooleanVariables_append,
            hbranchVariables]
          exact List.mem_append_left _ hvar

/--
The deduplicated variables in nonempty wrapped case branches are exactly their
generated Boolean support when the branch bodies contain no Boolean variables.
-/
theorem wrappedCaseBranches_variables_mem_iff
    (support : List NormalForm.BoolVar)
    (bodies : NormalForm.BoolCase → List Selection)
    (cases : List NormalForm.BoolCase)
    (hgenerated
      : ∀ boolCase, boolCase ∈ cases → boolCase ∈ NormalForm.allBoolCases support)
    (hbodyVariables
      : ∀ boolCase,
          boolCase ∈ cases
          → NormalForm.selectionSetBooleanVariables (bodies boolCase) = [])
    (hnonempty
      : List.flatten
          (cases.map (fun boolCase => wrapNonemptyCase boolCase (bodies boolCase)))
        ≠ [])
    (varName : NormalForm.BoolVar)
    : varName
        ∈ NormalForm.dedupBoolVars
            (NormalForm.selectionSetBooleanVariables
              (List.flatten
                (cases.map
                  (fun boolCase => wrapNonemptyCase boolCase (bodies boolCase)))))
      ↔ varName ∈ support := by
  rw [NormalForm.CompleteNormalization.mem_dedupBoolVars_iff]
  exact ⟨wrappedCaseBranches_variables_subset support bodies cases hgenerated
      hbodyVariables varName,
    fun hvar => wrappedCaseBranches_variables_cover support bodies cases hgenerated
      hbodyVariables hnonempty varName hvar⟩

end ResponseShape

end GraphQL
