import GraphQL.Theories.ConditionTree.Execution
import Proofs.GraphQL.Theories.ConditionTree.Extraction

/-! Shared projections and preservation facts for condition-tree field entries. -/

namespace GraphQL
namespace ConditionTree

-- Raw syntax is useful for source-extraction proofs, but execution consumes only
-- `storedFieldEntries`. Keep this projection out of the public execution module.
mutual
  def Tree.fieldEntries (tree : Tree) : List (Condition × Selection) :=
    tree.fields.flatMap (fun group => group.selections.map (tree.condition, ·))
    ++ branchFieldEntries tree.branches
  termination_by sizeOf tree
  decreasing_by
    cases tree
    simp_all
    omega

  def branchFieldEntries : List (Branch Tree) -> List (Condition × Selection)
    | [] => []
    | branch :: rest =>
        branch.body.fieldEntries ++ branchFieldEntries rest
  termination_by branches => sizeOf branches
  decreasing_by
    all_goals
      cases branch
      simp_wf
      omega
end

def projectStoredFieldEntry (entry : Condition × NamedField) : Condition × Selection :=
  (entry.1, entry.2.toSelection)

private theorem localFieldEntries_eq_map_stored
    (condition : Condition) (groups : List FieldGroup)
    : groups.flatMap (fun group => group.selections.map (condition, ·))
      = List.map projectStoredFieldEntry
          (groups.flatMap
            fun group =>
              group.fields.map
                fun field =>
                  (
                    condition,
                    ({ responseName := group.responseName, field } : NamedField)
                  )) := by
  induction groups with
  | nil => rfl
  | cons group rest ih =>
      rw [List.flatMap_cons, List.flatMap_cons, List.map_append, ih]
      congr 1
      rw [FieldGroup.selections, List.map_map, List.map_map]
      apply List.map_congr_left
      intro field _hfield
      rfl

mutual
  theorem Tree.fieldEntries_eq_map_storedFieldEntries (tree : Tree)
      : tree.fieldEntries = tree.storedFieldEntries.map projectStoredFieldEntry := by
    rw [Tree.fieldEntries, Tree.storedFieldEntries, List.map_append,
      branchFieldEntries_eq_map_storedFieldEntries tree.branches]
    rw [localFieldEntries_eq_map_stored]
  termination_by sizeOf tree
  decreasing_by
    cases tree
    simp_all
    omega

  theorem branchFieldEntries_eq_map_storedFieldEntries (branches : List (Branch Tree))
      : branchFieldEntries branches
        = (branchStoredFieldEntries branches).map projectStoredFieldEntry := by
    cases branches with
    | nil => simp [branchFieldEntries, branchStoredFieldEntries]
    | cons branch rest =>
        rw [branchFieldEntries, branchStoredFieldEntries, List.map_append,
          branch.body.fieldEntries_eq_map_storedFieldEntries,
          branchFieldEntries_eq_map_storedFieldEntries rest]
  termination_by sizeOf branches
  decreasing_by
    all_goals
      cases branch
      simp_wf
      omega
end

end ConditionTree
end GraphQL
