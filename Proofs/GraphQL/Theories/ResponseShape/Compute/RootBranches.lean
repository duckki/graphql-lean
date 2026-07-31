import GraphQL.Theories.ResponseShape.Compute

/-!
Shared root-branch construction and duplicate-check facts used by decoder proofs.
-/

namespace GraphQL

namespace ResponseShape

/-- Builds the normalized selections for one Boolean root case, omitting an
empty branch body. -/
def normalizedRootBranch
    (schema : Schema) (parentType : Name) (selectionSet : List Selection)
    (boolCase : NormalForm.BoolCase) : List Selection :=
  match NormalForm.normalizeSelectionSet schema parentType
      (NormalForm.filterSelectionSetBoolCase boolCase selectionSet) with
  | [] => []
  | selection :: rest =>
      NormalForm.wrapWithBoolCase boolCase (selection :: rest)

/-- A clause absent from the seen list cannot be found by the decoder's
executable equality check. -/
theorem clausesEqualBool_any_eq_false_of_not_mem
    (clause : Clause) : ∀ clauses : List Clause,
      clause ∉ clauses -> clauses.any (clausesEqualBool clause) = false
  | [], _hnotMem => rfl
  | candidate :: rest, hnotMem => by
      have hparts : clause ≠ candidate ∧ clause ∉ rest := by
        simpa only [List.mem_cons, not_or] using hnotMem
      simp [clausesEqualBool, hparts.1,
        clausesEqualBool_any_eq_false_of_not_mem clause rest hparts.2]

end ResponseShape

end GraphQL
