import GraphQL.Execution
import GraphQL.Theories.ConditionTree.FieldCollection
import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Equivalence.Collection
import Proofs.GraphQL.Execution.Fuel
import Proofs.GraphQL.List
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.FieldCollection

/-! Exact grouping of flat executable fields by response name. -/

namespace GraphQL
namespace Execution
namespace FieldGroups

open Execution
open GraphQL.ConditionTree
open Algorithms.ExecutionUngroupedUncached.Eager

@[simp]
theorem flattenExecutableFieldGroups_map_snd (groups : List (Name × List ExecutableField))
    : (flattenExecutableFieldGroups groups).map Prod.snd = groups.flatMap Prod.snd := by
  induction groups with
  | nil => rfl
  | cons group rest ih =>
      rcases group with ⟨responseName, fields⟩
      simp [flattenExecutableFieldGroups, ih, Function.comp_def]

theorem flattenExecutableFieldGroups_eq_flatMap
    (groups : List (Name × List ExecutableField))
    : flattenExecutableFieldGroups groups
      = groups.flatMap (fun group => group.2.map (fun field => (group.1, field))) := by
  induction groups with
  | nil => rfl
  | cons group rest ih =>
      rcases group with ⟨responseName, fields⟩
      simp [flattenExecutableFieldGroups, ih]

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

theorem flattenExecutableFieldGroups_mem_addExecutableGroup
    (group : Name × List ExecutableField)
    (groups : List (Name × List ExecutableField))
    (entry : Name × ExecutableField)
    : entry ∈ flattenExecutableFieldGroups (addExecutableGroup group groups)
      ↔ entry ∈ group.2.map (fun field => (group.1, field))
        ∨ entry ∈ flattenExecutableFieldGroups groups := by
  rw [(flattenExecutableFieldGroups_addExecutableGroup_perm group groups).mem_iff]
  simp [or_comm]

theorem flattenExecutableFieldGroups_mem_mergeExecutableGroups
    (left right : List (Name × List ExecutableField))
    (entry : Name × ExecutableField)
    : entry ∈ flattenExecutableFieldGroups (mergeExecutableGroups left right)
      ↔ entry ∈ flattenExecutableFieldGroups left
        ∨ entry ∈ flattenExecutableFieldGroups right := by
  induction right generalizing left with
  | nil => simp [mergeExecutableGroups, flattenExecutableFieldGroups]
  | cons group rest ih =>
      change entry ∈ flattenExecutableFieldGroups
          (mergeExecutableGroups (addExecutableGroup group left) rest)
        ↔ entry ∈ flattenExecutableFieldGroups left
          ∨ entry ∈ flattenExecutableFieldGroups (group :: rest)
      rw [ih, flattenExecutableFieldGroups_mem_addExecutableGroup]
      simp [flattenExecutableFieldGroups, or_assoc, or_left_comm]

theorem mem_addExecutableGroup_key_iff
    (group : Name × List ExecutableField)
    (groups : List (Name × List ExecutableField)) (name : Name)
    : name ∈ (addExecutableGroup group groups).map Prod.fst
      ↔ name = group.1 ∨ name ∈ groups.map Prod.fst := by
  induction groups with
  | nil => simp [addExecutableGroup]
  | cons current rest ih =>
      rcases current with ⟨currentName, currentFields⟩
      by_cases hname : (currentName == group.1) = true
      · have hequal : currentName = group.1 := beq_iff_eq.mp hname
        simp [addExecutableGroup, hequal]
      · have hfalse : (currentName == group.1) = false := by
          cases hvalue : currentName == group.1
          · rfl
          · contradiction
        have hne : currentName ≠ group.1 := by
          intro hequal
          subst currentName
          simp at hfalse
        simp [addExecutableGroup, hfalse, ih, or_left_comm]

theorem addExecutableGroup_keys_nodup
    (group : Name × List ExecutableField)
    (groups : List (Name × List ExecutableField))
    (hnodup : (groups.map Prod.fst).Nodup)
    : ((addExecutableGroup group groups).map Prod.fst).Nodup := by
  induction groups with
  | nil => simp [addExecutableGroup]
  | cons current rest ih =>
      rcases current with ⟨currentName, currentFields⟩
      simp only [List.map_cons, List.nodup_cons] at hnodup
      by_cases hname : (currentName == group.1) = true
      · simpa [addExecutableGroup, hname] using hnodup
      · have hfalse : (currentName == group.1) = false := by
          cases hvalue : currentName == group.1
          · rfl
          · contradiction
        have hne : currentName ≠ group.1 := by
          intro hequal
          subst currentName
          simp at hfalse
        rw [addExecutableGroup]
        simp only [hfalse, Bool.false_eq_true, ite_false, List.map_cons]
        apply List.nodup_cons.mpr
        constructor
        · intro hmember
          rcases (mem_addExecutableGroup_key_iff group rest currentName).mp
              hmember with hequal | hrest
          · exact hne hequal
          · exact hnodup.1 hrest
        · exact ih hnodup.2

theorem groupExecutableFields_exact (fields : List (Name × ExecutableField))
    : RuntimeFieldGroupsExact fields (groupExecutableFields fields) := by
  unfold RuntimeFieldGroupsExact groupExecutableFields
  have hgeneral :
      ∀ (rest : List (Name × ExecutableField))
        (groups : List (Name × List ExecutableField)),
        (groups.map Prod.fst).Nodup
        -> ((rest.foldl
              (fun result field =>
                addExecutableGroup (field.1, [field.2]) result)
              groups).map Prod.fst).Nodup
          ∧ (flattenExecutableFieldGroups
              (rest.foldl
                (fun result field =>
                  addExecutableGroup (field.1, [field.2]) result)
                groups)).Perm
              (flattenExecutableFieldGroups groups ++ rest) := by
    intro rest
    induction rest with
    | nil =>
        intro groups hnodup
        exact ⟨hnodup, by simp⟩
    | cons field rest ih =>
        intro groups hnodup
        let added := addExecutableGroup (field.1, [field.2]) groups
        have haddedNodup : (added.map Prod.fst).Nodup :=
          addExecutableGroup_keys_nodup _ _ hnodup
        rcases ih added haddedNodup with ⟨hfinalNodup, hfinalPerm⟩
        constructor
        · exact hfinalNodup
        · apply hfinalPerm.trans
          have haddPerm :
              (flattenExecutableFieldGroups added).Perm
                (flattenExecutableFieldGroups groups ++ [field]) := by
            simpa [added]
              using flattenExecutableFieldGroups_addExecutableGroup_perm
                (field.1, [field.2]) groups
          simpa [List.append_assoc] using haddPerm.append_right rest
  simpa [flattenExecutableFieldGroups] using hgeneral fields [] (by simp)

theorem mem_foldExecutableFields_key_iff
    (fields : List (Name × ExecutableField))
    (groups : List (Name × List ExecutableField)) (responseName : Name)
    : responseName
        ∈ (fields.foldl
            (fun result field =>
              addExecutableGroup (field.1, [field.2]) result)
            groups).map
            Prod.fst
      ↔ responseName ∈ groups.map Prod.fst
        ∨ ∃ field, field ∈ fields ∧ responseName = field.1 := by
  induction fields generalizing groups with
  | nil => simp
  | cons field rest ih =>
      rw [List.foldl_cons, ih,
        mem_addExecutableGroup_key_iff (field.1, [field.2]) groups]
      simp only [List.mem_cons]
      constructor
      · intro hmember
        rcases hmember with (hequal | hgroups) | hrest
        · exact Or.inr ⟨field, Or.inl rfl, hequal⟩
        · exact Or.inl hgroups
        · rcases hrest with ⟨candidate, hcandidate, hequal⟩
          exact Or.inr ⟨candidate, Or.inr hcandidate, hequal⟩
      · intro hmember
        rcases hmember with hgroups | ⟨candidate, hcandidate, hequal⟩
        · exact Or.inl (Or.inr hgroups)
        · rcases hcandidate with rfl | hrest
          · exact Or.inl (Or.inl hequal)
          · exact Or.inr ⟨candidate, hrest, hequal⟩

theorem mem_groupExecutableFields_key_iff
    (fields : List (Name × ExecutableField)) (responseName : Name)
    : responseName ∈ (groupExecutableFields fields).map Prod.fst
      ↔ ∃ field, field ∈ fields ∧ responseName = field.1 := by
  simpa [groupExecutableFields]
    using mem_foldExecutableFields_key_iff fields [] responseName

theorem groupExecutableFields_wellFormed (fields : List (Name × ExecutableField))
    : NormalForm.executableGroupsWellFormed (groupExecutableFields fields) := by
  unfold groupExecutableFields
  have hfold :
      ∀ (rest : List (Name × ExecutableField))
        (groups : List (Name × List ExecutableField)),
        NormalForm.executableGroupsWellFormed groups
        -> NormalForm.executableGroupsWellFormed
            (rest.foldl
              (fun result field =>
                addExecutableGroup (field.1, [field.2]) result)
              groups) := by
    intro rest
    induction rest with
    | nil => exact fun _groups hgroups => hgroups
    | cons field rest ih =>
        intro groups hgroups
        apply ih
        exact NormalForm.GroundTypeNormalization.addExecutableGroup_wellFormed
          (field.1, [field.2]) groups (by simp [NormalForm.executableGroupWellFormed])
          hgroups
  exact hfold fields []
    (by
      intro group hgroup
      simp at hgroup)

theorem mem_map_snd_flattenExecutableFieldGroups_iff
    (groups : List (Name × List ExecutableField)) (field : ExecutableField)
    : field ∈ (flattenExecutableFieldGroups groups).map Prod.snd
      ↔ ∃ responseName fields, (responseName, fields) ∈ groups ∧ field ∈ fields := by
  induction groups with
  | nil => simp [flattenExecutableFieldGroups]
  | cons group rest ih =>
      rcases group with ⟨responseName, fields⟩
      rw [flattenExecutableFieldGroups, List.map_append]
      have hmap :
          (fields.map (fun field => (responseName, field))).map Prod.snd = fields := by
        simp [Function.comp_def]
      rw [hmap]
      simp only [List.mem_append, ih, List.mem_cons]
      constructor
      · intro hmember
        rcases hmember with hfield | ⟨name, groupFields, hgroup, hfield⟩
        · exact ⟨responseName, fields, Or.inl rfl, hfield⟩
        · exact ⟨name, groupFields, Or.inr hgroup, hfield⟩
      · rintro ⟨name, groupFields, hgroup, hfield⟩
        rcases hgroup with heq | hrest
        · cases heq
          exact Or.inl hfield
        · exact Or.inr ⟨name, groupFields, hrest, hfield⟩

theorem mem_flattenExecutableFieldGroups_iff
    (groups : List (Name × List ExecutableField))
    (entry : Name × ExecutableField)
    : entry ∈ flattenExecutableFieldGroups groups
      ↔ ∃ fields, (entry.1, fields) ∈ groups ∧ entry.2 ∈ fields := by
  induction groups with
  | nil => simp [flattenExecutableFieldGroups]
  | cons group rest ih =>
      rcases group with ⟨responseName, fields⟩
      simp only [flattenExecutableFieldGroups, List.mem_append,
        List.mem_map, List.mem_cons, ih]
      constructor
      · rintro (⟨field, hfield, rfl⟩ | ⟨groupFields, hgroup, hfield⟩)
        · exact ⟨fields, Or.inl rfl, hfield⟩
        · exact ⟨groupFields, Or.inr hgroup, hfield⟩
      · rintro ⟨groupFields, hgroup, hfield⟩
        rcases hgroup with hhead | htail
        · cases hhead
          exact Or.inl ⟨entry.2, hfield, rfl⟩
        · exact Or.inr ⟨groupFields, htail, hfield⟩

theorem mergedFieldSelectionSet_perm
    {left right : List ExecutableField} (hfields : left.Perm right)
    : (Execution.mergedFieldSelectionSet left).Perm
        (Execution.mergedFieldSelectionSet right) := by
  have heq :
      ∀ fields : List ExecutableField,
        Execution.mergedFieldSelectionSet fields
          = fields.flatMap ExecutableField.selectionSet := by
    intro fields
    induction fields with
    | nil => rfl
    | cons field rest ih => simp [Execution.mergedFieldSelectionSet, ih]
  rw [heq, heq]
  induction hfields with
  | nil => exact List.Perm.refl []
  | cons head _tail ih =>
      simpa only [List.flatMap_cons] using ih.append_left head.selectionSet
  | swap first second rest =>
      simp only [List.flatMap_cons]
      simpa [List.append_assoc]
        using (List.perm_append_comm
                (l₁ := second.selectionSet) (l₂ := first.selectionSet)).append_right
          (rest.flatMap ExecutableField.selectionSet)
  | trans _ _ ihleft ihright => exact ihleft.trans ihright

theorem mergedFieldSelectionSet_eq_flatMap (fields : List ExecutableField)
    : Execution.mergedFieldSelectionSet fields
      = fields.flatMap ExecutableField.selectionSet := by
  induction fields with
  | nil => rfl
  | cons field rest ih => simp [Execution.mergedFieldSelectionSet, ih]

theorem collectFlatFields_mem_collectFields
    {ObjectRef : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectRef)
    (selectionSet : List Selection) (field : Name × ExecutableField)
    : field ∈ collectFlatFields schema variableValues parentType source selectionSet
      ↔ field
        ∈ flattenExecutableFieldGroups
            (Execution.collectFields schema variableValues parentType source
              selectionSet) := by
  cases hselectionSet : selectionSet with
  | nil =>
      subst selectionSet
      simp [collectFlatFields, Execution.collectFields, flattenExecutableFieldGroups]
  | cons selection rest =>
      subst selectionSet
      rw [collectFlatFields, Execution.collectFields,
        flattenExecutableFieldGroups_mem_mergeExecutableGroups]
      have ihRest :=
        collectFlatFields_mem_collectFields schema variableValues parentType source
          rest field
      cases selection with
      | field responseName fieldName arguments directives childSelectionSet =>
          cases hdirectives :
              selectionDirectivesAllowBool variableValues directives <;>
            simp [collectFlatSelection, Execution.collectSelection,
              flattenExecutableFieldGroups, hdirectives, ihRest]
      | inlineFragment typeCondition directives childSelectionSet =>
          have ihChild :=
            collectFlatFields_mem_collectFields schema variableValues parentType
              source childSelectionSet field
          cases typeCondition with
          | none =>
              cases hdirectives :
                  selectionDirectivesAllowBool variableValues directives <;>
                simp [collectFlatSelection, Execution.collectSelection,
                  flattenExecutableFieldGroups, hdirectives, ihChild, ihRest]
          | some typeName =>
              cases hdirectives :
                  selectionDirectivesAllowBool variableValues directives <;>
                cases htype :
                  doesFragmentTypeApplyBool schema parentType source typeName <;>
                simp [collectFlatSelection, Execution.collectSelection,
                  flattenExecutableFieldGroups, hdirectives, htype, ihChild, ihRest]
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

theorem collectFlatFields_eq_flatMap_collectFlatSelection
    {ObjectRef : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectRef)
    (selectionSet : List Selection)
    : collectFlatFields schema variableValues parentType source selectionSet
      = selectionSet.flatMap
          (collectFlatSelection schema variableValues parentType source) := by
  induction selectionSet with
  | nil => rfl
  | cons selection rest ih =>
      simp [collectFlatFields, ih]

theorem collectFlatFields_perm_of_selectionSet_perm
    {ObjectRef : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectRef)
    {left right : List Selection} (hselectionSet : left.Perm right)
    : (collectFlatFields schema variableValues parentType source left).Perm
        (collectFlatFields schema variableValues parentType source right) := by
  rw [collectFlatFields_eq_flatMap_collectFlatSelection,
    collectFlatFields_eq_flatMap_collectFlatSelection]
  exact List.Perm.flatMap hselectionSet
    (collectFlatSelection schema variableValues parentType source)

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

theorem flattenExecutableFieldGroups_map_snd_eq_collectedExecutableFields
    (groups : List (Name × List ExecutableField))
    : (flattenExecutableFieldGroups groups).map Prod.snd
      = collectedExecutableFields groups := by
  induction groups with
  | nil => rfl
  | cons group rest ih =>
      rcases group with ⟨responseName, fields⟩
      simp [flattenExecutableFieldGroups, collectedExecutableFields, ih,
        Function.comp_def]

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

structure RuntimeGroupsPermutationEquivalent
    (left right : List (Name × List ExecutableField))
    : Prop where
  leftWellFormed : NormalForm.executableGroupsWellFormed left
  rightWellFormed : NormalForm.executableGroupsWellFormed right
  leftKeysNodup : (left.map Prod.fst).Nodup
  rightKeysNodup : (right.map Prod.fst).Nodup
  fieldsPerm
    : (flattenExecutableFieldGroups left).Perm (flattenExecutableFieldGroups right)

theorem mem_group_key_iff_exists_field_of_wellFormed
    (groups : List (Name × List ExecutableField))
    (hgroups : NormalForm.executableGroupsWellFormed groups)
    (responseName : Name)
    : responseName ∈ groups.map Prod.fst
      ↔ ∃ field, (responseName, field) ∈ flattenExecutableFieldGroups groups := by
  constructor
  · intro hmember
    rcases List.mem_map.mp hmember with ⟨group, hgroup, hname⟩
    rcases group with ⟨groupName, fields⟩
    simp only at hname
    subst groupName
    have hwellFormed := hgroups (responseName, fields) hgroup
    cases fields with
    | nil => exact False.elim (hwellFormed rfl)
    | cons field rest =>
        refine ⟨field, ?_⟩
        exact (mem_flattenExecutableFieldGroups_iff groups (responseName, field)).2
          ⟨field :: rest, hgroup, by simp⟩
  · rintro ⟨field, hfield⟩
    rcases (mem_flattenExecutableFieldGroups_iff groups
      (responseName, field)).1 hfield with ⟨fields, hgroup, _hfield⟩
    exact List.mem_map.mpr ⟨(responseName, fields), hgroup, rfl⟩

theorem executableGroupNamesNodup_iff_map_fst_nodup
    (groups : List (Name × List ExecutableField))
    : NormalForm.executableGroupNamesNodup groups ↔ (groups.map Prod.fst).Nodup := by
  induction groups with
  | nil => simp [NormalForm.executableGroupNamesNodup]
  | cons group rest ih =>
      rcases group with ⟨responseName, fields⟩
      simp [NormalForm.executableGroupNamesNodup, ih]

theorem RuntimeGroupsPermutationEquivalent.keys
    {left right : List (Name × List ExecutableField)}
    (equivalent : RuntimeGroupsPermutationEquivalent left right)
    (responseName : Name)
    : responseName ∈ left.map Prod.fst ↔ responseName ∈ right.map Prod.fst := by
  rw [mem_group_key_iff_exists_field_of_wellFormed left
      equivalent.leftWellFormed responseName,
    mem_group_key_iff_exists_field_of_wellFormed right
      equivalent.rightWellFormed responseName]
  constructor
  · rintro ⟨field, hfield⟩
    exact ⟨field, equivalent.fieldsPerm.mem_iff.mp hfield⟩
  · rintro ⟨field, hfield⟩
    exact ⟨field, equivalent.fieldsPerm.mem_iff.mpr hfield⟩

private theorem count_eq_indicator_of_nodup {α : Type} [BEq α] [LawfulBEq α] (value : α)
    : ∀ {items : List α},
        items.Nodup -> items.count value = if value ∈ items then 1 else 0
  | [], _hnodup => by simp
  | head :: tail, hnodup => by
      have hparts : head ∉ tail ∧ tail.Nodup := by simpa using hnodup
      by_cases hequal : value = head
      · subst head
        rw [List.count_cons_self, List.count_eq_zero.mpr hparts.1]
        simp
      · rw [List.count_cons_of_ne (fun h => hequal h.symm),
          count_eq_indicator_of_nodup value hparts.2]
        simp [hequal]

theorem RuntimeGroupsPermutationEquivalent.keysPerm
    {left right : List (Name × List ExecutableField)}
    (equivalent : RuntimeGroupsPermutationEquivalent left right)
    : (left.map Prod.fst).Perm (right.map Prod.fst) := by
  rw [List.perm_iff_count]
  intro responseName
  rw [count_eq_indicator_of_nodup responseName equivalent.leftKeysNodup,
    count_eq_indicator_of_nodup responseName equivalent.rightKeysNodup]
  simp only [equivalent.keys responseName]

theorem filter_eq_nil_of_all_false {α : Type}
    (predicate : α -> Bool) (values : List α)
    (hfalse : ∀ value, value ∈ values -> predicate value = false)
    : values.filter predicate = [] := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
      rw [List.filter_cons, hfalse value (by simp)]
      simp only [Bool.false_eq_true, ite_false]
      exact ih
        fun candidate hcandidate =>
          hfalse candidate (by simp [hcandidate])

theorem filter_flattenExecutableFieldGroups_eq_nil_of_key_not_mem
    (responseName : Name) (groups : List (Name × List ExecutableField))
    (hnot : responseName ∉ groups.map Prod.fst)
    : (flattenExecutableFieldGroups groups).filter (fun entry => entry.1 == responseName)
      = [] := by
  induction groups with
  | nil => rfl
  | cons group rest ih =>
      rcases group with ⟨groupName, fields⟩
      have hne : groupName ≠ responseName := by
        intro heq
        exact hnot (by simp [heq])
      rw [flattenExecutableFieldGroups, List.filter_append]
      simp [hne, ih (by intro hmem; exact hnot (by simp [hmem]))]

theorem filter_flattenExecutableFieldGroups_head_eq
    (responseName : Name) (fields : List ExecutableField)
    (rest : List (Name × List ExecutableField))
    (hnodup : (((responseName, fields) :: rest).map Prod.fst).Nodup)
    : (flattenExecutableFieldGroups ((responseName, fields) :: rest)).filter
        (fun entry => entry.1 == responseName)
      = fields.map (fun field => (responseName, field)) := by
  have hrestNot : responseName ∉ rest.map Prod.fst :=
    (List.nodup_cons.mp hnodup).1
  rw [flattenExecutableFieldGroups, List.filter_append,
    filter_flattenExecutableFieldGroups_eq_nil_of_key_not_mem responseName rest hrestNot]
  simp

theorem filter_flattenExecutableFieldGroups_head_ne
    (responseName : Name) (fields : List ExecutableField)
    (rest : List (Name × List ExecutableField))
    (hnodup : (((responseName, fields) :: rest).map Prod.fst).Nodup)
    : (flattenExecutableFieldGroups ((responseName, fields) :: rest)).filter
        (fun entry => !(entry.1 == responseName))
      = flattenExecutableFieldGroups rest := by
  have hrestNot : responseName ∉ rest.map Prod.fst :=
    (List.nodup_cons.mp hnodup).1
  rw [flattenExecutableFieldGroups, List.filter_append]
  have hhead :
      (fields.map (fun field => (responseName, field))).filter
          (fun entry => !(entry.1 == responseName)) = [] := by
    apply filter_eq_nil_of_all_false
    intro entry hentry
    rcases List.mem_map.mp hentry with ⟨field, _hfield, rfl⟩
    simp
  rw [hhead]
  simp only [List.nil_append]
  apply List.filter_eq_self.mpr
  intro entry hentry
  have hne : entry.1 ≠ responseName := by
    intro heq
    rcases (mem_flattenExecutableFieldGroups_iff rest entry).1 hentry with
      ⟨groupFields, hgroup, _hfield⟩
    exact hrestNot (List.mem_map.mpr
      ⟨(entry.1, groupFields), hgroup, heq⟩)
  simp [hne]

theorem RuntimeGroupsPermutationEquivalent.permuteRight
    {left right reordered : List (Name × List ExecutableField)}
    (equivalent : RuntimeGroupsPermutationEquivalent left right)
    (hperm : right.Perm reordered)
    : RuntimeGroupsPermutationEquivalent left reordered := by
  constructor
  · exact equivalent.leftWellFormed
  · intro group hgroup
    exact equivalent.rightWellFormed group (hperm.mem_iff.mpr hgroup)
  · exact equivalent.leftKeysNodup
  · exact (hperm.map Prod.fst).nodup_iff.mp equivalent.rightKeysNodup
  · have hentries := List.Perm.flatMap hperm
        (fun group => group.2.map (fun field => (group.1, field)))
    exact equivalent.fieldsPerm.trans (by
      simpa only [← flattenExecutableFieldGroups_eq_flatMap] using hentries)

theorem RuntimeGroupsPermutationEquivalent.headFields
    {responseName : Name} {leftFields rightFields : List ExecutableField}
    {leftTail rightTail : List (Name × List ExecutableField)}
    (equivalent
      : RuntimeGroupsPermutationEquivalent
          ((responseName, leftFields) :: leftTail)
          ((responseName, rightFields) :: rightTail))
    : leftFields.Perm rightFields := by
  have hfiltered :=
    equivalent.fieldsPerm.filter (fun entry => entry.1 == responseName)
  have hpairs :
      (leftFields.map (fun field => (responseName, field))).Perm
        (rightFields.map (fun field => (responseName, field))) := by
    simpa only [
      filter_flattenExecutableFieldGroups_head_eq responseName leftFields leftTail
        equivalent.leftKeysNodup,
      filter_flattenExecutableFieldGroups_head_eq responseName rightFields rightTail
        equivalent.rightKeysNodup]
      using hfiltered
  have hfields := hpairs.map Prod.snd
  simpa [Function.comp_def] using hfields

theorem RuntimeGroupsPermutationEquivalent.tails
    {responseName : Name} {leftFields rightFields : List ExecutableField}
    {leftTail rightTail : List (Name × List ExecutableField)}
    (equivalent
      : RuntimeGroupsPermutationEquivalent
          ((responseName, leftFields) :: leftTail)
          ((responseName, rightFields) :: rightTail))
    : RuntimeGroupsPermutationEquivalent leftTail rightTail := by
  constructor
  · exact NormalForm.GroundTypeNormalization.executableGroupsWellFormed_tail
      equivalent.leftWellFormed
  · exact NormalForm.GroundTypeNormalization.executableGroupsWellFormed_tail
      equivalent.rightWellFormed
  · exact (List.nodup_cons.mp equivalent.leftKeysNodup).2
  · exact (List.nodup_cons.mp equivalent.rightKeysNodup).2
  · have hfiltered :=
      equivalent.fieldsPerm.filter
        (fun entry => !(entry.1 == responseName))
    simpa only [
      filter_flattenExecutableFieldGroups_head_ne responseName leftFields leftTail
        equivalent.leftKeysNodup,
      filter_flattenExecutableFieldGroups_head_ne responseName rightFields rightTail
        equivalent.rightKeysNodup] using hfiltered

theorem RuntimeGroupsPermutationEquivalent.leftDepthBound
    {left right : List (Name × List ExecutableField)}
    (equivalent : RuntimeGroupsPermutationEquivalent left right)
    {depth : Nat} (hright : RuntimeGroupsResponseDepthBound right depth)
    : RuntimeGroupsResponseDepthBound left depth := by
  intro field hfield
  apply hright field
  have hfield' :=
    (equivalent.fieldsPerm.map Prod.snd).mem_iff.mp
      (by simpa only [flattenExecutableFieldGroups_map_snd] using hfield)
  simpa only [flattenExecutableFieldGroups_map_snd] using hfield'

def RuntimeGroupsCrossCompatible (left right : List (Name × List ExecutableField))
    : Prop :=
  ∀ leftName leftField,
    (leftName, leftField) ∈ flattenExecutableFieldGroups left
    -> ∀ rightName rightField,
        (rightName, rightField) ∈ flattenExecutableFieldGroups right
        -> leftName = rightName
        -> leftField.fieldName = rightField.fieldName
            ∧ Argument.argumentsEquivalent leftField.arguments rightField.arguments

theorem flatMap_snd_perm_of_perm
    {left right : List (Name × List ExecutableField)}
    (hperm : left.Perm right)
    : (left.flatMap Prod.snd).Perm (right.flatMap Prod.snd) :=
  List.Perm.flatMap hperm Prod.snd

theorem RuntimeGroupsCrossCompatible.permuteRight
    {left right reordered : List (Name × List ExecutableField)}
    (compatible : RuntimeGroupsCrossCompatible left right)
    (hperm : right.Perm reordered)
    : RuntimeGroupsCrossCompatible left reordered := by
  intro leftName leftField hleft rightName rightField hright hresponse
  have hentries := List.Perm.flatMap hperm
    (fun group => group.2.map (fun field => (group.1, field)))
  have hentries' : (flattenExecutableFieldGroups right).Perm
      (flattenExecutableFieldGroups reordered) := by
    simpa only [← flattenExecutableFieldGroups_eq_flatMap] using hentries
  exact compatible leftName leftField hleft rightName rightField
    (hentries'.mem_iff.mpr hright) hresponse

theorem RuntimeGroupsCrossCompatible.tails
    {leftGroup rightGroup : Name × List ExecutableField}
    {leftTail rightTail : List (Name × List ExecutableField)}
    (compatible
      : RuntimeGroupsCrossCompatible (leftGroup :: leftTail) (rightGroup :: rightTail))
    : RuntimeGroupsCrossCompatible leftTail rightTail := by
  intro leftName leftField hleft rightName rightField hright hresponse
  apply compatible leftName leftField
  · rw [flattenExecutableFieldGroups]
    exact List.mem_append.mpr (Or.inr hleft)
  · rw [flattenExecutableFieldGroups]
    exact List.mem_append.mpr (Or.inr hright)
  · exact hresponse

theorem RuntimeGroupsPermutationEquivalent.crossCompatible
    {left right : List (Name × List ExecutableField)}
    (equivalent : RuntimeGroupsPermutationEquivalent left right)
    (hfieldCompatible : CollectedGroupsFieldValidationMergeCompatible right)
    : RuntimeGroupsCrossCompatible left right := by
  intro leftName leftField hleft rightName rightField hright hresponse
  have hleftRight : (leftName, leftField) ∈ flattenExecutableFieldGroups right :=
    equivalent.fieldsPerm.mem_iff.mp hleft
  rcases (mem_flattenExecutableFieldGroups_iff right
    (leftName, leftField)).mp hleftRight with
    ⟨leftFields, hleftGroup, hleftInGroup⟩
  rcases (mem_flattenExecutableFieldGroups_iff right
    (rightName, rightField)).mp hright with
    ⟨rightFields, hrightGroup, hrightInGroup⟩
  have hgroups : (leftName, leftFields) = (rightName, rightFields) :=
    pair_eq_of_map_fst_nodup equivalent.rightKeysNodup hleftGroup hrightGroup
      hresponse
  cases hgroups
  exact hfieldCompatible leftName leftFields hleftGroup leftField rightField
    hleftInGroup hrightInGroup

theorem RuntimeGroupsPermutationEquivalent.alignRightHead
    {responseName : Name} {leftFields : List ExecutableField}
    {leftTail right : List (Name × List ExecutableField)}
    (equivalent
      : RuntimeGroupsPermutationEquivalent ((responseName, leftFields) :: leftTail) right)
    : ∃ rightFields rightTail,
        right.Perm ((responseName, rightFields) :: rightTail)
        ∧ RuntimeGroupsPermutationEquivalent
            ((responseName, leftFields) :: leftTail)
            ((responseName, rightFields) :: rightTail) := by
  have hkeyLeft :
      responseName ∈ (((responseName, leftFields) :: leftTail).map Prod.fst) := by
    simp
  have hkeyRight : responseName ∈ right.map Prod.fst :=
    (equivalent.keys responseName).mp hkeyLeft
  rcases List.mem_map.mp hkeyRight with ⟨group, hgroup, hname⟩
  rcases group with ⟨groupName, rightFields⟩
  simp only at hname
  subst groupName
  rcases List.mem_iff_append.mp hgroup with ⟨before, after, hright⟩
  subst right
  let rightTail := before ++ after
  have hperm :
      (before ++ (responseName, rightFields) :: after).Perm
        ((responseName, rightFields) :: rightTail) := by
    simp [rightTail]
  exact ⟨rightFields, rightTail, hperm, equivalent.permuteRight hperm⟩

end FieldGroups
end Execution
end GraphQL
