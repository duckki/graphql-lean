import GraphQL.Execution
import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Equivalence.Collection
import Proofs.GraphQL.Execution.Fuel
import Proofs.GraphQL.List
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.FieldCollection

/-! Exact grouping of flat executable fields by response name. -/

namespace GraphQL
namespace Execution
namespace FieldGroups

open Execution
open Algorithms.ExecutionUngroupedUncached.Eager

-- Ungrouped runtime field collection for one syntax boundary. This is proof-facing:
-- the specification executor returns response-name groups directly.
mutual
  def collectFlatFields (schema : Schema) (variableValues : VariableValues)
      (executionParentType : Name) (source : ResolverValue ObjectRef)
      : List Selection -> List ExecutableField
    | [] => []
    | selection :: rest =>
        collectFlatSelection schema variableValues executionParentType source selection
        ++ collectFlatFields schema variableValues executionParentType source rest

  def collectFlatSelection (schema : Schema) (variableValues : VariableValues)
      (executionParentType : Name) (source : ResolverValue ObjectRef)
      : Selection -> List ExecutableField
    | .field responseName fieldName arguments directives selectionSet =>
        if selectionDirectivesAllowBool variableValues directives then
          [{
            parentType := executionParentType
            responseName
            fieldName
            arguments
            selectionSet
          }]
        else
          []
    | .inlineFragment none directives selectionSet =>
        if selectionDirectivesAllowBool variableValues directives then
          collectFlatFields schema variableValues executionParentType source selectionSet
        else
          []
    | .inlineFragment (some typeCondition) directives selectionSet =>
        if selectionDirectivesAllowBool variableValues directives
            && doesFragmentTypeApplyBool schema executionParentType source
                typeCondition then
          collectFlatFields schema variableValues executionParentType source selectionSet
        else
          []
end

def flattenCollectedFields : List (Name × List ExecutableField) -> List ExecutableField
  | [] => []
  | (_responseName, fields) :: rest => fields ++ flattenCollectedFields rest

theorem flattenCollectedFields_eq_flatMap_snd
    (groups : List (Name × List ExecutableField))
    : flattenCollectedFields groups = groups.flatMap Prod.snd := by
  induction groups with
  | nil => rfl
  | cons group rest ih =>
      rcases group with ⟨responseName, fields⟩
      simp [flattenCollectedFields, ih]

def groupExecutableFields (fields : List ExecutableField)
    : List (Name × List ExecutableField) :=
  fields.foldl
    (fun groups field => addExecutableGroup (field.responseName, [field]) groups) []

def RuntimeFieldGroupsExact (fields : List ExecutableField)
    (groups : List (Name × List ExecutableField))
    : Prop :=
  (groups.map Prod.fst).Nodup ∧ (flattenCollectedFields groups).Perm fields

theorem flattenCollectedFields_addExecutableGroup_perm
    (group : Name × List ExecutableField)
    (groups : List (Name × List ExecutableField))
    : (flattenCollectedFields (addExecutableGroup group groups)).Perm
        (flattenCollectedFields groups ++ group.2) := by
  rcases group with ⟨groupName, groupFields⟩
  induction groups with
  | nil => simp [addExecutableGroup, flattenCollectedFields]
  | cons current rest ih =>
      rcases current with ⟨currentName, currentFields⟩
      by_cases hname : (currentName == groupName) = true
      · simp only [addExecutableGroup, hname]
        change (currentFields ++ groupFields ++ flattenCollectedFields rest).Perm
                ((currentFields ++ flattenCollectedFields rest) ++ groupFields)
        simpa [List.append_assoc] using
          (List.Perm.append_left currentFields
            (List.perm_append_comm (l₁ := groupFields)
              (l₂ := flattenCollectedFields rest)))
      · have hfalse : (currentName == groupName) = false := by
          cases hvalue : currentName == groupName
          · rfl
          · contradiction
        simp only [addExecutableGroup, hfalse]
        change (currentFields
                ++ flattenCollectedFields
                    (addExecutableGroup (groupName, groupFields) rest)).Perm
                ((currentFields ++ flattenCollectedFields rest) ++ groupFields)
        simpa [List.append_assoc] using ih.append_left currentFields

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
        simp only [hfalse, Bool.false_eq_true, if_false, List.map_cons]
        apply List.nodup_cons.mpr
        constructor
        · intro hmember
          rcases (mem_addExecutableGroup_key_iff group rest currentName).mp
              hmember with hequal | hrest
          · exact hne hequal
          · exact hnodup.1 hrest
        · exact ih hnodup.2

theorem groupExecutableFields_exact (fields : List ExecutableField)
    : RuntimeFieldGroupsExact fields (groupExecutableFields fields) := by
  unfold RuntimeFieldGroupsExact groupExecutableFields
  have hgeneral :
      ∀ (rest : List ExecutableField)
        (groups : List (Name × List ExecutableField)),
        (groups.map Prod.fst).Nodup
        -> ((rest.foldl
              (fun result field =>
                addExecutableGroup (field.responseName, [field]) result)
              groups).map Prod.fst).Nodup
          ∧ (flattenCollectedFields
              (rest.foldl
                (fun result field =>
                  addExecutableGroup (field.responseName, [field]) result)
                groups)).Perm
              (flattenCollectedFields groups ++ rest) := by
    intro rest
    induction rest with
    | nil =>
        intro groups hnodup
        exact ⟨hnodup, by simp⟩
    | cons field rest ih =>
        intro groups hnodup
        let added := addExecutableGroup (field.responseName, [field]) groups
        have haddedNodup : (added.map Prod.fst).Nodup :=
          addExecutableGroup_keys_nodup _ _ hnodup
        rcases ih added haddedNodup with ⟨hfinalNodup, hfinalPerm⟩
        constructor
        · exact hfinalNodup
        · apply hfinalPerm.trans
          have haddPerm :
              (flattenCollectedFields added).Perm
                (flattenCollectedFields groups ++ [field]) := by
            simpa [added] using
              flattenCollectedFields_addExecutableGroup_perm
                (field.responseName, [field]) groups
          simpa [List.append_assoc] using haddPerm.append_right rest
  simpa [flattenCollectedFields] using hgeneral fields [] (by simp)

theorem mem_foldExecutableFields_key_iff
    (fields : List ExecutableField)
    (groups : List (Name × List ExecutableField)) (responseName : Name)
    : responseName
        ∈ (fields.foldl
            (fun result field =>
              addExecutableGroup (field.responseName, [field]) result)
            groups).map
            Prod.fst
      ↔ responseName ∈ groups.map Prod.fst
        ∨ ∃ field, field ∈ fields ∧ responseName = field.responseName := by
  induction fields generalizing groups with
  | nil => simp
  | cons field rest ih =>
      rw [List.foldl_cons, ih,
        mem_addExecutableGroup_key_iff (field.responseName, [field]) groups]
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
    (fields : List ExecutableField) (responseName : Name)
    : responseName ∈ (groupExecutableFields fields).map Prod.fst
      ↔ ∃ field, field ∈ fields ∧ responseName = field.responseName := by
  simpa [groupExecutableFields] using
    mem_foldExecutableFields_key_iff fields [] responseName

theorem groupExecutableFields_wellFormed (fields : List ExecutableField)
    : NormalForm.executableGroupsWellFormed (groupExecutableFields fields) := by
  unfold groupExecutableFields
  have hfold :
      ∀ (rest : List ExecutableField)
        (groups : List (Name × List ExecutableField)),
        NormalForm.executableGroupsWellFormed groups
        -> NormalForm.executableGroupsWellFormed
            (rest.foldl
              (fun result field =>
                addExecutableGroup (field.responseName, [field]) result)
              groups) := by
    intro rest
    induction rest with
    | nil => exact fun _groups hgroups => hgroups
    | cons field rest ih =>
        intro groups hgroups
        apply ih
        exact
          NormalForm.GroundTypeNormalization.addExecutableGroup_wellFormed
            (field.responseName, [field]) groups
            (by
              constructor
              · simp
              · intro candidate hcandidate
                simp at hcandidate
                subst candidate
                rfl)
            hgroups
  exact hfold fields [] (by
    intro group hgroup
    simp at hgroup)

theorem mem_flattenCollectedFields_iff
    (groups : List (Name × List ExecutableField)) (field : ExecutableField)
    : field ∈ flattenCollectedFields groups
      ↔ ∃ responseName fields, (responseName, fields) ∈ groups ∧ field ∈ fields := by
  induction groups with
  | nil => simp [flattenCollectedFields]
  | cons group rest ih =>
      rcases group with ⟨responseName, fields⟩
      simp only [flattenCollectedFields, List.mem_append, ih, List.mem_cons]
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
      simpa only [List.flatMap_cons] using
        ih.append_left head.selectionSet
  | swap first second rest =>
      simp only [List.flatMap_cons]
      simpa [List.append_assoc] using
        (List.perm_append_comm
          (l₁ := second.selectionSet) (l₂ := first.selectionSet)).append_right
            (rest.flatMap ExecutableField.selectionSet)
  | trans _ _ ihleft ihright => exact ihleft.trans ihright

theorem mergedFieldSelectionSet_eq_flatMap (fields : List ExecutableField)
    : Execution.mergedFieldSelectionSet fields
      = fields.flatMap ExecutableField.selectionSet := by
  induction fields with
  | nil => rfl
  | cons field rest ih => simp [Execution.mergedFieldSelectionSet, ih]

theorem flattenCollectedFields_mem_addExecutableGroup
    (group : Name × List ExecutableField)
    (groups : List (Name × List ExecutableField))
    (field : ExecutableField)
    : field ∈ flattenCollectedFields (Execution.addExecutableGroup group groups)
      ↔ field ∈ group.snd ∨ field ∈ flattenCollectedFields groups := by
  rcases group with ⟨groupName, groupFields⟩
  induction groups with
  | nil =>
      simp [flattenCollectedFields, Execution.addExecutableGroup]
  | cons current rest ih =>
      rcases current with ⟨currentName, currentFields⟩
      by_cases hname : (currentName == groupName) = true
      · simp [flattenCollectedFields, Execution.addExecutableGroup, hname,
          List.mem_append]
        constructor
        · intro hmem
          rcases hmem with hcurrent | hgroupOrRest
          · exact Or.inr (Or.inl hcurrent)
          · rcases hgroupOrRest with hgroup | hrest
            · exact Or.inl hgroup
            · exact Or.inr (Or.inr hrest)
        · intro hmem
          rcases hmem with hgroup | hcurrentOrRest
          · exact Or.inr (Or.inl hgroup)
          · rcases hcurrentOrRest with hcurrent | hrest
            · exact Or.inl hcurrent
            · exact Or.inr (Or.inr hrest)
      · have hfalse : (currentName == groupName) = false := by
          cases hmatch : currentName == groupName
          · rfl
          · contradiction
        simp [flattenCollectedFields, Execution.addExecutableGroup, hfalse,
          List.mem_append]
        constructor
        · intro hmem
          rcases hmem with hcurrent | hadded
          · exact Or.inr (Or.inl hcurrent)
          · rcases ih.mp hadded with hgroup | hrest
            · exact Or.inl hgroup
            · exact Or.inr (Or.inr hrest)
        · intro hmem
          rcases hmem with hgroup | hcurrentOrRest
          · exact Or.inr (ih.mpr (Or.inl hgroup))
          · rcases hcurrentOrRest with hcurrent | hrest
            · exact Or.inl hcurrent
            · exact Or.inr (ih.mpr (Or.inr hrest))

theorem flattenCollectedFields_mem_mergeExecutableGroups
    (left right : List (Name × List ExecutableField))
    (field : ExecutableField)
    : field ∈ flattenCollectedFields (Execution.mergeExecutableGroups left right)
      ↔ field ∈ flattenCollectedFields left ∨ field ∈ flattenCollectedFields right := by
  induction right generalizing left with
  | nil =>
      simp [flattenCollectedFields, Execution.mergeExecutableGroups]
  | cons group rest ih =>
      rcases group with ⟨responseName, fields⟩
      change
        field
              ∈ flattenCollectedFields
                (Execution.mergeExecutableGroups
                  (Execution.addExecutableGroup (responseName, fields) left)
                  rest)
          ↔ field ∈ flattenCollectedFields left
            ∨ field
              ∈ flattenCollectedFields ((responseName, fields) :: rest)
      constructor
      · intro hmem
        rcases
            (ih
              (Execution.addExecutableGroup (responseName, fields) left)).mp
              hmem with
          hadded | hrest
        · rcases
              (flattenCollectedFields_mem_addExecutableGroup
                (responseName, fields) left field).mp hadded with
            hfield | hleft
          · exact Or.inr (by simp [flattenCollectedFields, hfield])
          · exact Or.inl hleft
        · exact Or.inr (by simp [flattenCollectedFields, hrest])
      · intro hmem
        rcases hmem with hleft | hright
        · exact (ih (Execution.addExecutableGroup (responseName, fields) left)).mpr
                  (Or.inl
                    ((flattenCollectedFields_mem_addExecutableGroup
                        (responseName, fields) left field).mpr
                      (Or.inr hleft)))
        · have hfieldsOrRest :
              field ∈ fields ∨ field ∈ flattenCollectedFields rest := by
            simpa [flattenCollectedFields, List.mem_append] using hright
          rcases hfieldsOrRest with hfield | hrest
          · exact (ih (Execution.addExecutableGroup (responseName, fields) left)).mpr
                    (Or.inl
                      ((flattenCollectedFields_mem_addExecutableGroup
                          (responseName, fields) left field).mpr
                        (Or.inl hfield)))
          · exact (ih (Execution.addExecutableGroup (responseName, fields) left)).mpr
                    (Or.inr hrest)

theorem collectFlatFields_mem_collectFields
    {ObjectRef : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectRef)
    (selectionSet : List Selection) (field : ExecutableField)
    : field ∈ collectFlatFields schema variableValues parentType source selectionSet
      ↔ field
        ∈ flattenCollectedFields
            (Execution.collectFields schema variableValues parentType source
              selectionSet) := by
  cases hselectionSet : selectionSet with
  | nil =>
      subst selectionSet
      simp [collectFlatFields, Execution.collectFields, flattenCollectedFields]
  | cons selection rest =>
      subst selectionSet
      rw [collectFlatFields, Execution.collectFields,
        flattenCollectedFields_mem_mergeExecutableGroups]
      have ihRest :=
        collectFlatFields_mem_collectFields schema variableValues parentType source
          rest field
      cases selection with
      | field responseName fieldName arguments directives childSelectionSet =>
          cases hdirectives :
              selectionDirectivesAllowBool variableValues directives <;>
            simp [collectFlatSelection, Execution.collectSelection,
              flattenCollectedFields, hdirectives, ihRest]
      | inlineFragment typeCondition directives childSelectionSet =>
          have ihChild :=
            collectFlatFields_mem_collectFields schema variableValues parentType
              source childSelectionSet field
          cases typeCondition with
          | none =>
              cases hdirectives :
                  selectionDirectivesAllowBool variableValues directives <;>
                simp [collectFlatSelection, Execution.collectSelection,
                  flattenCollectedFields, hdirectives, ihChild, ihRest]
          | some typeName =>
              cases hdirectives :
                  selectionDirectivesAllowBool variableValues directives <;>
                cases htype :
                  doesFragmentTypeApplyBool schema parentType source typeName <;>
                simp [collectFlatSelection, Execution.collectSelection,
                  flattenCollectedFields, hdirectives, htype, ihChild, ihRest]
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

theorem flattenCollectedFields_mergeExecutableGroups_perm
    (left right : List (Name × List ExecutableField))
    : (flattenCollectedFields (mergeExecutableGroups left right)).Perm
        (flattenCollectedFields left ++ flattenCollectedFields right) := by
  induction right generalizing left with
  | nil => simp [mergeExecutableGroups, flattenCollectedFields]
  | cons group rest ih =>
      rcases group with ⟨responseName, fields⟩
      rw [mergeExecutableGroups]
      have hrest := ih (addExecutableGroup (responseName, fields) left)
      have hadded :=
        flattenCollectedFields_addExecutableGroup_perm
          (responseName, fields) left
      exact hrest.trans (by
        rw [flattenCollectedFields]
        simpa [List.append_assoc] using
          hadded.append_right (flattenCollectedFields rest))

theorem collectFlatFields_perm_flatten_collectFields
    {ObjectRef : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectRef)
    (selectionSet : List Selection)
    : (collectFlatFields schema variableValues parentType source selectionSet).Perm
        (flattenCollectedFields
          (collectFields schema variableValues parentType source selectionSet)) := by
  cases hselectionSet : selectionSet with
  | nil =>
      subst selectionSet
      simp [collectFlatFields, collectFields, flattenCollectedFields]
  | cons selection rest =>
      subst selectionSet
      have hrest :=
        collectFlatFields_perm_flatten_collectFields schema variableValues
          parentType source rest
      have hhead :
          (collectFlatSelection schema variableValues parentType source selection).Perm
            (flattenCollectedFields
              (collectSelection schema variableValues parentType source selection)) := by
        cases selection with
        | field responseName fieldName arguments directives childSelectionSet =>
            cases hdirectives :
                selectionDirectivesAllowBool variableValues directives <;>
              simp [collectFlatSelection, collectSelection,
                flattenCollectedFields, hdirectives]
        | inlineFragment typeCondition directives childSelectionSet =>
            have hchild :=
              collectFlatFields_perm_flatten_collectFields schema variableValues
                parentType source childSelectionSet
            cases typeCondition with
            | none =>
                cases hdirectives :
                    selectionDirectivesAllowBool variableValues directives <;>
                  simp [collectFlatSelection, collectSelection,
                    flattenCollectedFields, hdirectives, hchild]
            | some typeName =>
                cases hdirectives :
                    selectionDirectivesAllowBool variableValues directives <;>
                  cases htype :
                    doesFragmentTypeApplyBool schema parentType source typeName <;>
                  simp [collectFlatSelection, collectSelection,
                    flattenCollectedFields, hdirectives, htype, hchild]
      rw [collectFlatFields, collectFields]
      exact (hhead.append hrest).trans
        (flattenCollectedFields_mergeExecutableGroups_perm
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
          (collectFlatSelection schema variableValues parentType source selection)
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
            cases hallows : selectionDirectivesAllowBool variableValues directives <;>
              simp [collectFlatSelection, hallows] at hfield
            exact collectFlatFields_responseDepth_bound schema variableValues
              parentType source selectionSet field hfield
        | some typeName =>
            cases hallows : selectionDirectivesAllowBool variableValues directives <;>
              cases happly :
                doesFragmentTypeApplyBool schema parentType source typeName <;>
              simp [collectFlatSelection, hallows, happly] at hfield
            exact collectFlatFields_responseDepth_bound schema variableValues
              parentType source selectionSet field hfield

  theorem collectFlatFields_responseDepth_bound
      {ObjectRef : Type}
      (schema : Schema) (variableValues : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectRef)
      (selectionSet : List Selection)
      : ExecutableFieldsResponseDepthBound
          (collectFlatFields schema variableValues parentType source selectionSet)
          (selectionSetResponseDepth selectionSet) := by
    intro field hfield
    cases selectionSet with
    | nil => simp [collectFlatFields] at hfield
    | cons selection rest =>
        rw [collectFlatFields] at hfield
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
  have hfield' : field ∈ flattenCollectedFields
      (collectFields schema variableValues parentType source selectionSet) := by
    simpa [flattenCollectedFields_eq_flatMap_snd] using hfield
  exact collectFlatFields_responseDepth_bound schema variableValues parentType
    source selectionSet field
      ((collectFlatFields_perm_flatten_collectFields schema variableValues
        parentType source selectionSet).mem_iff.mpr hfield')

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

theorem flattenCollectedFields_eq_collectedExecutableFields
    (groups : List (Name × List ExecutableField))
    : flattenCollectedFields groups = collectedExecutableFields groups := by
  induction groups with
  | nil => rfl
  | cons group rest ih =>
      rcases group with ⟨responseName, fields⟩
      simp [flattenCollectedFields, collectedExecutableFields, ih]

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
  fieldsPerm : (left.flatMap Prod.snd).Perm (right.flatMap Prod.snd)

theorem RuntimeGroupsPermutationEquivalent.flattenedFieldsPerm
    {left right : List (Name × List ExecutableField)}
    (equivalent : RuntimeGroupsPermutationEquivalent left right)
    : (flattenCollectedFields left).Perm (flattenCollectedFields right) := by
  rw [flattenCollectedFields_eq_flatMap_snd,
    flattenCollectedFields_eq_flatMap_snd]
  exact equivalent.fieldsPerm

theorem mem_group_key_iff_exists_field_of_wellFormed
    (groups : List (Name × List ExecutableField))
    (hgroups : NormalForm.executableGroupsWellFormed groups)
    (responseName : Name)
    : responseName ∈ groups.map Prod.fst
      ↔ ∃ field,
          field ∈ flattenCollectedFields groups ∧ responseName = field.responseName := by
  constructor
  · intro hmember
    rcases List.mem_map.mp hmember with ⟨group, hgroup, hname⟩
    rcases group with ⟨groupName, fields⟩
    simp only at hname
    subst groupName
    have hwellFormed := hgroups (responseName, fields) hgroup
    cases hfields : fields with
    | nil => exact False.elim (hwellFormed.1 hfields)
    | cons field rest =>
        have hfield : field ∈ fields := by simp [hfields]
        exact ⟨
          field,
          (mem_flattenCollectedFields_iff groups field).mpr
            ⟨responseName, fields, hgroup, hfield⟩,
          (hwellFormed.2 field hfield).symm
        ⟩
  · rintro ⟨field, hfield, hname⟩
    rcases (mem_flattenCollectedFields_iff groups field).mp hfield with
      ⟨groupName, fields, hgroup, hfieldGroup⟩
    have hwellFormed := hgroups (groupName, fields) hgroup
    have hfieldName := hwellFormed.2 field hfieldGroup
    apply List.mem_map.mpr
    exact ⟨(groupName, fields), hgroup, hfieldName.symm.trans hname.symm⟩

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
  · rintro ⟨field, hfield, hname⟩
    exact ⟨field, equivalent.flattenedFieldsPerm.mem_iff.mp hfield, hname⟩
  · rintro ⟨field, hfield, hname⟩
    exact ⟨field, equivalent.flattenedFieldsPerm.mem_iff.mpr hfield, hname⟩

theorem filter_eq_nil_of_all_false {α : Type}
    (predicate : α -> Bool) (values : List α)
    (hfalse : ∀ value, value ∈ values -> predicate value = false)
    : values.filter predicate = [] := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
      rw [List.filter_cons, hfalse value (by simp)]
      simp only [Bool.false_eq_true, if_false]
      exact ih fun candidate hcandidate =>
        hfalse candidate (by simp [hcandidate])

theorem filter_fields_eq_responseName
    (responseName : Name) (fields : List ExecutableField)
    (hresponses : ∀ field, field ∈ fields -> field.responseName = responseName)
    : fields.filter (fun field => field.responseName == responseName) = fields := by
  exact List.filter_eq_self.mpr fun field hfield => by
    simp [hresponses field hfield]

theorem filter_fields_ne_responseName
    (responseName : Name) (fields : List ExecutableField)
    (hresponses : ∀ field, field ∈ fields -> field.responseName ≠ responseName)
    : fields.filter (fun field => field.responseName == responseName) = [] := by
  apply filter_eq_nil_of_all_false
  intro field hfield
  exact beq_eq_false_iff_ne.mpr (hresponses field hfield)

theorem filter_flattenCollectedFields_eq_nil_of_key_not_mem
    (responseName : Name) (groups : List (Name × List ExecutableField))
    (hwellFormed : NormalForm.executableGroupsWellFormed groups)
    (hnot : responseName ∉ groups.map Prod.fst)
    : (flattenCollectedFields groups).filter
        (fun field => field.responseName == responseName)
      = [] := by
  induction groups with
  | nil => rfl
  | cons group rest ih =>
      rcases group with ⟨groupName, fields⟩
      have hgroupWellFormed := hwellFormed (groupName, fields) (by simp)
      have hgroupNe : groupName ≠ responseName := by
        intro hequal
        apply hnot
        simp [hequal]
      have hfields :
          fields.filter (fun field => field.responseName == responseName) = [] :=
        filter_fields_ne_responseName responseName fields fun field hfield => by
          rw [hgroupWellFormed.2 field hfield]
          exact hgroupNe
      rw [flattenCollectedFields, List.filter_append, hfields,
        ih (NormalForm.GroundTypeNormalization.executableGroupsWellFormed_tail
          hwellFormed) (by
            intro hmember
            exact hnot (by simp [hmember]))]
      rfl

theorem filter_flattenCollectedFields_head_eq
    (responseName : Name) (fields : List ExecutableField)
    (rest : List (Name × List ExecutableField))
    (hwellFormed : NormalForm.executableGroupsWellFormed ((responseName, fields) :: rest))
    (hnodup : (((responseName, fields) :: rest).map Prod.fst).Nodup)
    : (flattenCollectedFields ((responseName, fields) :: rest)).filter
        (fun field => field.responseName == responseName)
      = fields := by
  have hgroup := hwellFormed (responseName, fields) (by simp)
  have hrestNot : responseName ∉ rest.map Prod.fst :=
    (List.nodup_cons.mp hnodup).1
  rw [flattenCollectedFields, List.filter_append,
    filter_fields_eq_responseName responseName fields hgroup.2,
    filter_flattenCollectedFields_eq_nil_of_key_not_mem responseName rest
      (NormalForm.GroundTypeNormalization.executableGroupsWellFormed_tail
        hwellFormed) hrestNot,
    List.append_nil]

theorem filter_flattenCollectedFields_head_ne
    (responseName : Name) (fields : List ExecutableField)
    (rest : List (Name × List ExecutableField))
    (hwellFormed : NormalForm.executableGroupsWellFormed ((responseName, fields) :: rest))
    (hnodup : (((responseName, fields) :: rest).map Prod.fst).Nodup)
    : (flattenCollectedFields ((responseName, fields) :: rest)).filter
        (fun field => !(field.responseName == responseName))
      = flattenCollectedFields rest := by
  have hgroup := hwellFormed (responseName, fields) (by simp)
  rw [flattenCollectedFields, List.filter_append]
  have hhead :
      fields.filter (fun field => !(field.responseName == responseName)) = [] := by
    apply filter_eq_nil_of_all_false
    intro field hfield
    simp [hgroup.2 field hfield]
  rw [hhead, List.nil_append]
  apply List.filter_eq_self.mpr
  intro field hfield
  rcases (mem_flattenCollectedFields_iff rest field).mp hfield with
    ⟨groupName, groupFields, hgroupMem, hfieldMem⟩
  have hrestWellFormed :=
    NormalForm.GroundTypeNormalization.executableGroupsWellFormed_tail hwellFormed
  have hfieldName :=
    (hrestWellFormed (groupName, groupFields) hgroupMem).2 field hfieldMem
  have hgroupNe : groupName ≠ responseName := by
    intro hequal
    subst groupName
    have hkey : responseName ∈ rest.map Prod.fst := by
      exact List.mem_map.mpr ⟨(responseName, groupFields), hgroupMem, rfl⟩
    exact (List.nodup_cons.mp hnodup).1 hkey
  simp [hfieldName, hgroupNe]

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
  · exact equivalent.fieldsPerm.trans (List.Perm.flatMap hperm Prod.snd)

theorem RuntimeGroupsPermutationEquivalent.headFields
    {responseName : Name} {leftFields rightFields : List ExecutableField}
    {leftTail rightTail : List (Name × List ExecutableField)}
    (equivalent
      : RuntimeGroupsPermutationEquivalent
          ((responseName, leftFields) :: leftTail)
          ((responseName, rightFields) :: rightTail))
    : leftFields.Perm rightFields := by
  have hfiltered :=
    equivalent.flattenedFieldsPerm.filter
      (fun field => field.responseName == responseName)
  simpa [filter_flattenCollectedFields_head_eq responseName leftFields leftTail
      equivalent.leftWellFormed equivalent.leftKeysNodup,
    filter_flattenCollectedFields_head_eq responseName rightFields rightTail
      equivalent.rightWellFormed equivalent.rightKeysNodup] using hfiltered

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
      equivalent.flattenedFieldsPerm.filter
        (fun field => !(field.responseName == responseName))
    have htails :
        (flattenCollectedFields leftTail).Perm
          (flattenCollectedFields rightTail) := by
      simpa [filter_flattenCollectedFields_head_ne responseName leftFields leftTail
          equivalent.leftWellFormed equivalent.leftKeysNodup,
        filter_flattenCollectedFields_head_ne responseName rightFields rightTail
          equivalent.rightWellFormed equivalent.rightKeysNodup] using hfiltered
    simpa [flattenCollectedFields_eq_flatMap_snd] using htails

theorem RuntimeGroupsPermutationEquivalent.leftDepthBound
    {left right : List (Name × List ExecutableField)}
    (equivalent : RuntimeGroupsPermutationEquivalent left right)
    {depth : Nat} (hright : RuntimeGroupsResponseDepthBound right depth)
    : RuntimeGroupsResponseDepthBound left depth := by
  intro field hfield
  exact hright field (equivalent.fieldsPerm.mem_iff.mp hfield)

def RuntimeGroupsCrossCompatible (left right : List (Name × List ExecutableField))
    : Prop :=
  ∀ leftField,
    leftField ∈ left.flatMap Prod.snd
    -> ∀ rightField,
        rightField ∈ right.flatMap Prod.snd
        -> leftField.responseName = rightField.responseName
        -> leftField.parentType = rightField.parentType
            ∧ leftField.fieldName = rightField.fieldName
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
  intro leftField hleft rightField hright hresponse
  exact compatible leftField hleft rightField
    ((flatMap_snd_perm_of_perm hperm).mem_iff.mpr hright) hresponse

theorem RuntimeGroupsCrossCompatible.tails
    {leftGroup rightGroup : Name × List ExecutableField}
    {leftTail rightTail : List (Name × List ExecutableField)}
    (compatible
      : RuntimeGroupsCrossCompatible (leftGroup :: leftTail) (rightGroup :: rightTail))
    : RuntimeGroupsCrossCompatible leftTail rightTail := by
  intro leftField hleft rightField hright hresponse
  apply compatible leftField
  · simp [hleft]
  · simp [hright]
  · exact hresponse

theorem RuntimeGroupsPermutationEquivalent.crossCompatible
    {left right : List (Name × List ExecutableField)}
    (equivalent : RuntimeGroupsPermutationEquivalent left right)
    (hfieldCompatible : CollectedGroupsFieldValidationMergeCompatible right)
    (hsameParent : CollectedGroupsSameResponseParent right)
    : RuntimeGroupsCrossCompatible left right := by
  intro leftField hleft rightField hright hresponse
  have hleftRight : leftField ∈ right.flatMap Prod.snd :=
    equivalent.fieldsPerm.mem_iff.mp hleft
  have hleftRight' : leftField ∈ flattenCollectedFields right := by
    simpa [flattenCollectedFields_eq_flatMap_snd] using hleftRight
  have hright' : rightField ∈ flattenCollectedFields right := by
    simpa [flattenCollectedFields_eq_flatMap_snd] using hright
  rcases (mem_flattenCollectedFields_iff right leftField).mp hleftRight' with
    ⟨leftName, leftFields, hleftGroup, hleftInGroup⟩
  rcases (mem_flattenCollectedFields_iff right rightField).mp hright' with
    ⟨rightName, rightFields, hrightGroup, hrightInGroup⟩
  have hleftName :=
    (equivalent.rightWellFormed (leftName, leftFields) hleftGroup).2
      leftField hleftInGroup
  have hrightName :=
    (equivalent.rightWellFormed (rightName, rightFields) hrightGroup).2
      rightField hrightInGroup
  have hgroupName : leftName = rightName := by
    exact hleftName.symm.trans (hresponse.trans hrightName)
  have hgroups : (leftName, leftFields) = (rightName, rightFields) :=
    pair_eq_of_map_fst_nodup equivalent.rightKeysNodup hleftGroup hrightGroup
      hgroupName
  cases hgroups
  have hfield :=
    hfieldCompatible leftName leftFields hleftGroup leftField rightField
      hleftInGroup hrightInGroup hresponse
  have hparent :=
    hsameParent leftName leftFields hleftGroup leftField rightField
      hleftInGroup hrightInGroup hresponse
  exact ⟨hparent, hfield⟩

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
