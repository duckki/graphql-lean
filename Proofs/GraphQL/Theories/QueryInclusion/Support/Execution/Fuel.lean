import GraphQL.Theories.QueryInclusion
import Proofs.GraphQL.Theories.QueryInclusion.Support.Theories.ResponseMeasure

/-! Supporting lemmas extracted from commit `7797374fd` for the talk exercises. -/

namespace GraphQL.Execution

theorem selectionSetResponseDepth_append (left right : List Selection)
    : selectionSetResponseDepth (left ++ right)
      = max (selectionSetResponseDepth left) (selectionSetResponseDepth right) := by
  induction left with
  | nil => simp [selectionSetResponseDepth]
  | cons selection rest ih =>
      simp [selectionSetResponseDepth, ih, Nat.max_assoc]

mutual
  theorem selectionResponseDepth_le_size (selection : Selection)
      : selectionResponseDepth selection ≤ selection.size := by
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        simp only [selectionResponseDepth, Selection.size]
        simpa [Nat.add_comm]
          using Nat.add_le_add_right (selectionSetResponseDepth_le_size selectionSet) 1
    | inlineFragment typeCondition directives selectionSet =>
        simp only [selectionResponseDepth, Selection.size]
        simpa [Nat.add_comm]
          using Nat.le_succ_of_le (selectionSetResponseDepth_le_size selectionSet)

  theorem selectionSetResponseDepth_le_size (selectionSet : List Selection)
      : selectionSetResponseDepth selectionSet ≤ SelectionSet.size selectionSet := by
    cases selectionSet with
    | nil => exact Nat.le_refl _
    | cons selection rest =>
        simp only [selectionSetResponseDepth, SelectionSet.size]
        exact Nat.max_le.mpr
          ⟨Nat.le_trans (selectionResponseDepth_le_size selection)
              (Nat.le_add_right _ _),
            Nat.le_trans (selectionSetResponseDepth_le_size rest)
              (Nat.le_add_left _ _)⟩
end

end GraphQL.Execution
