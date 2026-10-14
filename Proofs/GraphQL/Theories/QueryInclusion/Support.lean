import Proofs.GraphQL.Theories.QueryInclusion.Support.OperationSoundness
import Proofs.GraphQL.Theories.QueryInclusion.Support.Theories.QueryInclusion.ReferenceChecker
import Proofs.GraphQL.Theories.QueryInclusion.Support.Theories.ResponsePath.OperationToReferenceChecker

/-! Talk scaffold: Boolean enumeration and both selected-path bridges. -/

namespace GraphQL.QueryInclusion
open Execution

-- A convenient proposition-level interface to the enumerator's lookup lemma.
theorem booleanVariableAssignments_complete {variables : List Name}
    {values : VariableValues} (hcase : values ∈ booleanVariableAssignments variables)
    : boolVarsComplete variables values := by
  intro name hname
  obtain ⟨value, hlookup⟩ := booleanVariableAssignments_lookup variables values hcase name hname
  exact ⟨
    value,
    by simp [inputValueBoolean?, hlookup, ConstInputValue.toInputValue,
      InputValue.staticBoolean?]
  ⟩

end GraphQL.QueryInclusion
