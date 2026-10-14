import GraphQL.Theories.QueryInclusion
import Proofs.GraphQL.Theories.QueryInclusion.Support.Theories.ConditionTree.FieldCollection
import Proofs.GraphQL.Theories.QueryInclusion.Support.Theories.ResponseMeasure
import Proofs.GraphQL.Theories.QueryInclusion.Support.Theories.SelectionConditions
import Proofs.GraphQL.Theories.QueryInclusion.Support.Algorithms.ExecutionUngrouped.Equivalence.Core
import Proofs.GraphQL.Theories.QueryInclusion.Support.Execution.Fuel
import Proofs.GraphQL.Theories.QueryInclusion.Support.Theories.NormalForm.Shared.Execution

/-! Supporting lemmas extracted from commit `7797374fd` for the talk exercises. -/

namespace GraphQL.Execution.FieldGroups

open Execution
open GraphQL.ConditionTree
open Algorithms.ExecutionUngroupedUncached.Eager

theorem flattenExecutableFieldGroups_map_snd (groups : List (Name × List ExecutableField))
    : (flattenExecutableFieldGroups groups).map Prod.snd = groups.flatMap Prod.snd := by
  induction groups with
  | nil => rfl
  | cons group rest ih =>
      rcases group with ⟨responseName, fields⟩
      simp [flattenExecutableFieldGroups, ih, Function.comp_def]

theorem flattenExecutableFieldGroups_addExecutableGroup_perm
    (group : Name × List ExecutableField)
    (groups : List (Name × List ExecutableField))
    : (flattenExecutableFieldGroups (addExecutableGroup group groups)).Perm
        (flattenExecutableFieldGroups groups
          ++ group.2.map (fun field => (group.1, field))) := by
  rcases group with ⟨groupName, groupFields⟩
  induction groups with
  | nil => simp [addExecutableGroup, flattenExecutableFieldGroups]
  | cons current rest ih =>
      rcases current with ⟨currentName, currentFields⟩
      by_cases hname : (currentName == groupName) = true
      · have heq : currentName = groupName := beq_iff_eq.mp hname
        subst groupName
        simp only [addExecutableGroup, hname, ite_true,
          flattenExecutableFieldGroups, List.map_append]
        simpa [List.append_assoc]
          using (List.Perm.append_left
                  (currentFields.map fun field => (currentName, field))
                  (List.perm_append_comm
                    (l₁ := groupFields.map fun field => (currentName, field))
                    (l₂ := flattenExecutableFieldGroups rest)))
      · have hfalse : (currentName == groupName) = false := by
          cases hvalue : currentName == groupName
          · rfl
          · contradiction
        simp only [addExecutableGroup, hfalse, Bool.false_eq_true, ite_false,
          flattenExecutableFieldGroups]
        simpa [List.append_assoc]
          using ih.append_left (currentFields.map fun field => (currentName, field))

theorem mergedFieldSelectionSet_eq_flatMap (fields : List ExecutableField)
    : Execution.mergedFieldSelectionSet fields
      = fields.flatMap ExecutableField.selectionSet := by
  induction fields with
  | nil => rfl
  | cons field rest ih => simp [Execution.mergedFieldSelectionSet, ih]

theorem flattenExecutableFieldGroups_mergeExecutableGroups_perm
    (left right : List (Name × List ExecutableField))
    : (flattenExecutableFieldGroups (mergeExecutableGroups left right)).Perm
        (flattenExecutableFieldGroups left ++ flattenExecutableFieldGroups right) := by
  induction right generalizing left with
  | nil => simp [mergeExecutableGroups, flattenExecutableFieldGroups]
  | cons group rest ih =>
      rw [mergeExecutableGroups]
      have hrest := ih (addExecutableGroup group left)
      have hadded := flattenExecutableFieldGroups_addExecutableGroup_perm group left
      exact hrest.trans
        (by
          rw [flattenExecutableFieldGroups]
          simpa [List.append_assoc]
            using hadded.append_right (flattenExecutableFieldGroups rest))

theorem collectFlatFields_perm_flatten_collectFields
    {ObjectRef : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectRef)
    (selectionSet : List Selection)
    : (collectFlatFields schema variableValues parentType source selectionSet).Perm
        (flattenExecutableFieldGroups
          (collectFields schema variableValues parentType source selectionSet)) := by
  cases hselectionSet : selectionSet with
  | nil =>
      subst selectionSet
      simp [collectFlatFields, collectFields, flattenExecutableFieldGroups]
  | cons selection rest =>
      subst selectionSet
      have hrest :=
        collectFlatFields_perm_flatten_collectFields schema variableValues
          parentType source rest
      have hhead :
          (collectFlatSelection schema variableValues parentType source selection).Perm
            (flattenExecutableFieldGroups
              (collectSelection schema variableValues parentType source selection)) := by
        cases selection with
        | field responseName fieldName arguments directives childSelectionSet =>
            cases hdirectives :
                selectionDirectivesAllowBool variableValues directives <;>
              simp [collectFlatSelection, collectSelection,
                flattenExecutableFieldGroups, hdirectives]
        | inlineFragment typeCondition directives childSelectionSet =>
            have hchild :=
              collectFlatFields_perm_flatten_collectFields schema variableValues
                parentType source childSelectionSet
            cases typeCondition with
            | none =>
                cases hdirectives :
                    selectionDirectivesAllowBool variableValues directives <;>
                  simp [collectFlatSelection, collectSelection,
                    flattenExecutableFieldGroups, hdirectives, hchild]
            | some typeName =>
                cases hdirectives :
                    selectionDirectivesAllowBool variableValues directives <;>
                  cases htype :
                    doesFragmentTypeApplyBool schema parentType source typeName <;>
                  simp [collectFlatSelection, collectSelection,
                    flattenExecutableFieldGroups, hdirectives, htype, hchild]
      rw [collectFlatFields, collectFields]
      exact (hhead.append hrest).trans
        (flattenExecutableFieldGroups_mergeExecutableGroups_perm
          (collectSelection schema variableValues parentType source selection)
          (collectFields schema variableValues parentType source rest)).symm
termination_by SelectionSet.size selectionSet
decreasing_by
  all_goals
    try subst selectionSet
    try subst selection
    simp_wf
    simp_all [SelectionSet.size, Selection.size]
    first
    | cases selection <;> simp [Selection.size] <;> omega
    | omega

def ExecutableFieldsResponseDepthBound (fields : List ExecutableField) (depth : Nat)
    : Prop :=
  ∀ field, field ∈ fields -> selectionSetResponseDepth field.selectionSet + 1 ≤ depth

def RuntimeGroupsResponseDepthBound
    (groups : List (Name × List ExecutableField)) (depth : Nat)
    : Prop :=
  ExecutableFieldsResponseDepthBound (groups.flatMap Prod.snd) depth

mutual
  theorem collectFlatSelection_responseDepth_bound
      {ObjectRef : Type}
      (schema : Schema) (variableValues : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectRef)
      (selection : Selection)
      : ExecutableFieldsResponseDepthBound
          ((collectFlatSelection schema variableValues parentType source selection).map
            Prod.snd)
          (selectionResponseDepth selection) := by
    intro field hfield
    cases selection with
    | field responseName fieldName arguments directives childSelectionSet =>
        cases hallows : selectionDirectivesAllowBool variableValues directives <;>
          simp [collectFlatSelection, hallows] at hfield
        subst field
        exact Nat.le_refl _
    | inlineFragment typeCondition directives selectionSet =>
        cases typeCondition with
        | none =>
            cases hallows : selectionDirectivesAllowBool variableValues directives
            · simp [collectFlatSelection, hallows] at hfield
            · exact collectFlatFields_responseDepth_bound schema variableValues
                parentType source selectionSet field (by
                  simpa only [collectFlatSelection, hallows, ite_true] using hfield)
        | some typeName =>
            cases hallows : selectionDirectivesAllowBool variableValues directives
            · simp [collectFlatSelection, hallows] at hfield
            · cases happly : doesFragmentTypeApplyBool schema parentType source typeName
              · simp [collectFlatSelection, hallows, happly] at hfield
              · exact collectFlatFields_responseDepth_bound schema variableValues
                  parentType source selectionSet field (by
                    simpa only [collectFlatSelection, hallows, happly,
                      Bool.true_and, ite_true] using hfield)

  theorem collectFlatFields_responseDepth_bound
      {ObjectRef : Type}
      (schema : Schema) (variableValues : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectRef)
      (selectionSet : List Selection)
      : ExecutableFieldsResponseDepthBound
          ((collectFlatFields schema variableValues parentType source selectionSet).map
            Prod.snd)
          (selectionSetResponseDepth selectionSet) := by
    intro field hfield
    cases selectionSet with
    | nil => simp [collectFlatFields] at hfield
    | cons selection rest =>
        rw [collectFlatFields] at hfield
        rw [List.map_append] at hfield
        rcases List.mem_append.mp hfield with hhead | htail
        · exact Nat.le_trans
            (collectFlatSelection_responseDepth_bound schema variableValues
              parentType source selection field hhead)
            (Nat.le_max_left _ _)
        · exact Nat.le_trans
            (collectFlatFields_responseDepth_bound schema variableValues
              parentType source rest field htail)
            (Nat.le_max_right _ _)
end

theorem collectFields_responseDepth_bound
    {ObjectRef : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectRef)
    (selectionSet : List Selection)
    : RuntimeGroupsResponseDepthBound
        (collectFields schema variableValues parentType source selectionSet)
        (selectionSetResponseDepth selectionSet) := by
  intro field hfield
  have hfield' : field ∈
      (flattenExecutableFieldGroups
        (collectFields schema variableValues parentType source selectionSet)).map
          Prod.snd := by
    simpa only [flattenExecutableFieldGroups_map_snd] using hfield
  have hperm :=
    (collectFlatFields_perm_flatten_collectFields schema variableValues
      parentType source selectionSet).map Prod.snd
  exact collectFlatFields_responseDepth_bound schema variableValues parentType
    source selectionSet field
      (hperm.mem_iff.mpr hfield')

theorem selectionSetResponseDepth_flatMap_le
    (fields : List ExecutableField) (depth : Nat)
    (hdepth : ExecutableFieldsResponseDepthBound fields (depth + 1))
    : selectionSetResponseDepth (fields.flatMap ExecutableField.selectionSet)
      ≤ depth := by
  induction fields with
  | nil => simp [selectionSetResponseDepth]
  | cons field rest ih =>
      rw [List.flatMap_cons, selectionSetResponseDepth_append]
      apply Nat.max_le.mpr
      constructor
      · have hfield := hdepth field (by simp)
        omega
      · apply ih
        intro candidate hcandidate
        exact hdepth candidate (by simp [hcandidate])

theorem pair_eq_of_map_fst_nodup
    {α : Type} {groups : List (Name × α)}
    (hnodup : (groups.map Prod.fst).Nodup)
    {left right : Name × α}
    (hleft : left ∈ groups) (hright : right ∈ groups)
    (hname : left.1 = right.1)
    : left = right := by
  induction groups with
  | nil => simp at hleft
  | cons head rest ih =>
      have hheadNot : head.1 ∉ rest.map Prod.fst :=
        (List.nodup_cons.mp hnodup).1
      have hrestNodup : (rest.map Prod.fst).Nodup :=
        (List.nodup_cons.mp hnodup).2
      rcases List.mem_cons.mp hleft with rfl | hleftRest
      · rcases List.mem_cons.mp hright with rfl | hrightRest
        · rfl
        · exact False.elim
            (hheadNot (List.mem_map.mpr ⟨right, hrightRest, hname.symm⟩))
      · rcases List.mem_cons.mp hright with rfl | hrightRest
        · exact False.elim
            (hheadNot (List.mem_map.mpr ⟨left, hleftRest, hname⟩))
        · exact ih hrestNodup hleftRest hrightRest

theorem executableGroupNamesNodup_iff_map_fst_nodup
    (groups : List (Name × List ExecutableField))
    : NormalForm.executableGroupNamesNodup groups ↔ (groups.map Prod.fst).Nodup := by
  induction groups with
  | nil => simp [NormalForm.executableGroupNamesNodup]
  | cons group rest ih =>
      rcases group with ⟨responseName, fields⟩
      simp [NormalForm.executableGroupNamesNodup, ih]

end GraphQL.Execution.FieldGroups
