import GraphQL.Theories.TreeSummary.ExactCases

/-! Structural facts about exact-case Boolean decisions. -/

namespace GraphQL
namespace TreeSummary
namespace ExactCases
namespace Internal.BooleanDecision

@[simp]
theorem collapse_joinCases (algebra : Algebra)
    (left right : BooleanDecision algebra.Summary)
    : (joinCases algebra.join left right).collapse algebra
      = algebra.join (left.collapse algebra) (right.collapse algebra) := by
  cases left <;> cases right <;> rfl

@[simp]
theorem collapse_compact (algebra : Algebra) (decision : BooleanDecision algebra.Summary)
    : (decision.compact algebra.join).collapse algebra = decision.collapse algebra := by
  induction decision with
  | leaf => rfl
  | split test onFalse onTrue ihFalse ihTrue =>
      simp [compact, collapse, ihFalse, ihTrue]
  | join left right ihLeft ihRight =>
      simp [compact, collapse, ihLeft, ihRight]

theorem eraseDups_nodup (variables : BooleanVariableNames)
    : variables.eraseDups.Nodup := by
  cases variables with
  | nil => simp
  | cons variableName rest =>
      rw [List.eraseDups_cons, List.nodup_cons]
      constructor
      · simp
      · exact eraseDups_nodup (rest.filter fun candidate => !candidate == variableName)
termination_by variables.length
decreasing_by
  subst_vars
  have hlength :=
    List.length_filter_le (fun candidate => !candidate == variableName) rest
  simp only [List.length_cons]
  omega

end BooleanDecision
end Internal
end ExactCases
end TreeSummary
end GraphQL
