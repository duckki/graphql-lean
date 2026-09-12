import GraphQL.Theories.ConditionTree.Execution
import Proofs.GraphQL.Execution.FieldGroups

/-! Exactness of condition-tree runtime field grouping. -/

namespace GraphQL
namespace ConditionTree

open Execution

theorem groupExecutableFields_exact (fields : List (Name × ExecutableField))
    : RuntimeFieldGroupsExact fields (groupExecutableFields fields) :=
  Execution.FieldGroups.groupExecutableFields_exact fields

theorem mem_groupExecutableFields_key_iff
    (fields : List (Name × ExecutableField)) (name : Name)
    : name ∈ (groupExecutableFields fields).map Prod.fst
      ↔ ∃ field, field ∈ fields ∧ name = field.1 :=
  Execution.FieldGroups.mem_groupExecutableFields_key_iff fields name

theorem groupExecutableFields_wellFormed (fields : List (Name × ExecutableField))
    : NormalForm.executableGroupsWellFormed (groupExecutableFields fields) :=
  Execution.FieldGroups.groupExecutableFields_wellFormed fields

theorem Tree.collectRuntimeFieldGroups_exact
    (variableValues : VariableValues) (runtimeType : Name)
    (tree : Tree)
    : RuntimeFieldGroupsExact
        (tree.collectRuntimeFields variableValues runtimeType)
        (tree.collectRuntimeFieldGroups variableValues runtimeType) := by
  exact groupExecutableFields_exact
    (tree.collectRuntimeFields variableValues runtimeType)

theorem Tree.collectRuntimeFieldGroups_wellFormed
    (variableValues : VariableValues) (runtimeType : Name)
    (tree : Tree)
    : NormalForm.executableGroupsWellFormed
        (tree.collectRuntimeFieldGroups variableValues runtimeType) := by
  exact groupExecutableFields_wellFormed _

end ConditionTree
end GraphQL
