import GraphQL.Theories.ConditionTree.Execution
import Proofs.GraphQL.Execution.FieldGroups

/-! Exactness of condition-tree runtime field grouping. -/

namespace GraphQL
namespace ConditionTree

open Execution

theorem flattenCollectedFields_eq_fieldGroups
    (groups : List (Name × List ExecutableField))
    : flattenCollectedFields groups
      = Execution.FieldGroups.flattenCollectedFields groups := by
  simpa [GraphQL.ConditionTree.flattenCollectedFields] using
    (Execution.FieldGroups.flattenCollectedFields_eq_flatMap_snd groups).symm

mutual
  theorem collectFlatFields_eq_fieldGroups
      {ObjectRef : Type}
      (schema : Schema) (variableValues : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectRef)
      (selectionSet : List Selection)
      : collectFlatFields schema variableValues parentType source selectionSet
        = Execution.FieldGroups.collectFlatFields schema variableValues parentType source
            selectionSet := by
    cases selectionSet with
    | nil => rfl
    | cons selection rest =>
        simp only [collectFlatFields, Execution.FieldGroups.collectFlatFields]
        rw [collectFlatSelection_eq_fieldGroups schema variableValues parentType source
          selection]
        rw [collectFlatFields_eq_fieldGroups schema variableValues parentType source rest]

  theorem collectFlatSelection_eq_fieldGroups
      {ObjectRef : Type}
      (schema : Schema) (variableValues : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectRef)
      (selection : Selection)
      : collectFlatSelection schema variableValues parentType source selection
        = Execution.FieldGroups.collectFlatSelection schema variableValues parentType
            source selection := by
    cases selection with
    | field => rfl
    | inlineFragment typeCondition directives selectionSet =>
        cases typeCondition with
        | none =>
            simp only [collectFlatSelection,
              Execution.FieldGroups.collectFlatSelection]
            split
            · exact collectFlatFields_eq_fieldGroups schema variableValues parentType source
                selectionSet
            · rfl
        | some typeName =>
            simp only [collectFlatSelection,
              Execution.FieldGroups.collectFlatSelection]
            split
            · exact collectFlatFields_eq_fieldGroups schema variableValues parentType source
                selectionSet
            · rfl
end

theorem groupExecutableFields_exact (fields : List ExecutableField)
    : RuntimeFieldGroupsExact fields (groupExecutableFields fields) := by
  have hexact := Execution.FieldGroups.groupExecutableFields_exact fields
  constructor
  · simpa [groupExecutableFields, Execution.FieldGroups.groupExecutableFields]
      using hexact.1
  · simpa [groupExecutableFields, Execution.FieldGroups.groupExecutableFields,
      flattenCollectedFields_eq_fieldGroups] using hexact.2

theorem mem_groupExecutableFields_key_iff (fields : List ExecutableField) (name : Name)
    : name ∈ (groupExecutableFields fields).map Prod.fst
      ↔ ∃ field, field ∈ fields ∧ name = field.responseName := by
  simpa [groupExecutableFields, Execution.FieldGroups.groupExecutableFields] using
    Execution.FieldGroups.mem_groupExecutableFields_key_iff fields name

theorem groupExecutableFields_wellFormed (fields : List ExecutableField)
    : NormalForm.executableGroupsWellFormed (groupExecutableFields fields) := by
  simpa [groupExecutableFields, Execution.FieldGroups.groupExecutableFields] using
    Execution.FieldGroups.groupExecutableFields_wellFormed fields

theorem Tree.collectRuntimeFieldGroups_exact
    (variableValues : VariableValues) (executionParentType runtimeType : Name)
    (tree : Tree)
    : RuntimeFieldGroupsExact
        (tree.collectRuntimeFields variableValues executionParentType runtimeType)
        (tree.collectRuntimeFieldGroups variableValues executionParentType
          runtimeType) := by
  exact groupExecutableFields_exact
    (tree.collectRuntimeFields variableValues executionParentType runtimeType)

theorem Tree.collectRuntimeFieldGroups_wellFormed
    (variableValues : VariableValues) (executionParentType runtimeType : Name)
    (tree : Tree)
    : NormalForm.executableGroupsWellFormed
        (tree.collectRuntimeFieldGroups variableValues executionParentType
          runtimeType) := by
  exact groupExecutableFields_wellFormed _

end ConditionTree
end GraphQL
