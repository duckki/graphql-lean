import Proofs.GraphQL.Theories.QueryInclusion.RegionSearch
import Proofs.GraphQL.Theories.SelectionConditions.BooleanVariables

/-! Runtime grouping facts for guarded response-field groups. -/

namespace GraphQL
namespace QueryInclusion

open Execution
open Execution.FieldGroups
open SelectionConditions

-- Filtering specification used to relate the one-pass executable grouping function to
-- the field-group semantics.
def conditionedFieldsForResponseName (responseName : Name)
    (entries : List SelectionConditions.ConditionedField)
    : List SelectionConditions.ConditionedField :=
  entries.filter fun entry => entry.field.responseName == responseName

def guardedFieldRuntimeGroups (variableValues : VariableValues)
    (executionParentType runtimeType : Name)
    (groups : List GuardedFieldGroup)
    : List (Name × List ExecutableField) :=
  groups.flatMap
    fun group =>
      executableFieldsAsGroup group.responseName
        (guardedFieldExecutableFields variableValues executionParentType runtimeType
          group.responseName group.entries)

theorem guardedFieldExecutableFields_entriesForName
    (variableValues : VariableValues) (executionParentType runtimeType : Name)
    (responseName : Name)
    (entries : List SelectionConditions.ConditionedField)
    : guardedFieldExecutableFields variableValues executionParentType runtimeType
        responseName (conditionedFieldsForResponseName responseName entries)
      = (SelectionConditions.runtimeFields variableValues executionParentType
          runtimeType entries).filter
          fun field => field.responseName == responseName := by
  induction entries with
  | nil => simp [conditionedFieldsForResponseName, guardedFieldExecutableFields,
      SelectionConditions.runtimeFields]
  | cons entry rest ih =>
      rcases entry with ⟨condition, field⟩
      rw [conditionedFieldsForResponseName, SelectionConditions.runtimeFields]
      simp only [List.flatMap_cons, List.filter_append]
      by_cases hname : field.responseName = responseName <;>
        cases hallow : condition.allows variableValues runtimeType <;>
        simp [hname, hallow, guardedFieldExecutableFields] <;>
        simpa only [conditionedFieldsForResponseName,
          guardedFieldExecutableFields,
          SelectionConditions.runtimeFields] using ih

theorem eraseDups_nodup [BEq α] [LawfulBEq α] (values : List α)
    : values.eraseDups.Nodup := by
  cases values with
  | nil => simp
  | cons value rest =>
      rw [List.eraseDups_cons, List.nodup_cons]
      constructor
      · intro hmember
        have hfiltered := List.mem_eraseDups.mp hmember
        have hparts := List.mem_filter.mp hfiltered
        simp at hparts
      · exact eraseDups_nodup
          (rest.filter fun candidate => !candidate == value)
termination_by values.length
decreasing_by
  simp_wf
  exact Nat.lt_of_le_of_lt (List.length_filter_le _ rest) (Nat.lt_succ_self _)

def guardedFieldGroupsForNames (names : List Name)
    (entries : List SelectionConditions.ConditionedField)
    : List GuardedFieldGroup :=
  names.map
    fun responseName =>
      { responseName, entries := conditionedFieldsForResponseName responseName entries }

def guardedFieldGroupsByFiltering (entries : List SelectionConditions.ConditionedField)
    : List GuardedFieldGroup :=
  guardedFieldGroupsForNames
    (entries.map (fun entry => entry.field.responseName)).eraseDups entries

private theorem conditionedFieldsForResponseName_append_eq_self
    (responseName : Name) (entries : List SelectionConditions.ConditionedField)
    (entry : SelectionConditions.ConditionedField)
    (hname : entry.field.responseName ≠ responseName)
    : conditionedFieldsForResponseName responseName (entries ++ [entry])
      = conditionedFieldsForResponseName responseName entries := by
  simp [conditionedFieldsForResponseName, hname]

private theorem conditionedFieldsForResponseName_append_eq_append
    (entries : List SelectionConditions.ConditionedField)
    (entry : SelectionConditions.ConditionedField)
    : conditionedFieldsForResponseName entry.field.responseName (entries ++ [entry])
      = conditionedFieldsForResponseName entry.field.responseName entries ++ [entry] := by
  simp [conditionedFieldsForResponseName]

private theorem conditionedFieldsForResponseName_eq_nil_of_not_mem
    (responseName : Name) (entries : List SelectionConditions.ConditionedField)
    (hname : responseName ∉ entries.map fun entry => entry.field.responseName)
    : conditionedFieldsForResponseName responseName entries = [] := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      have hparts : responseName ≠ entry.field.responseName
          ∧ responseName ∉ rest.map fun item => item.field.responseName := by
        simpa only [List.map_cons, List.mem_cons, not_or] using hname
      have hhead : (entry.field.responseName == responseName) = false := by
        simp [hparts.1.symm]
      rw [conditionedFieldsForResponseName, List.filter_cons, hhead]
      simp only [Bool.false_eq_true, if_false]
      simpa only [conditionedFieldsForResponseName] using ih hparts.2

private theorem guardedFieldGroupsForNames_append_eq_self
    (names : List Name) (entries : List SelectionConditions.ConditionedField)
    (entry : SelectionConditions.ConditionedField)
    (hname : entry.field.responseName ∉ names)
    : guardedFieldGroupsForNames names (entries ++ [entry])
      = guardedFieldGroupsForNames names entries := by
  induction names with
  | nil => rfl
  | cons responseName rest ih =>
      have hparts : entry.field.responseName ≠ responseName
          ∧ entry.field.responseName ∉ rest := by
        simpa only [List.mem_cons, not_or] using hname
      simp only [guardedFieldGroupsForNames, List.map_cons, List.cons.injEq]
      exact ⟨by
        rw [conditionedFieldsForResponseName_append_eq_self _ _ _ hparts.1],
        ih hparts.2⟩

private theorem addGuardedFieldEntry_not_mem
    (entry : SelectionConditions.ConditionedField) (groups : List GuardedFieldGroup)
    (hname : entry.field.responseName ∉ groups.map GuardedFieldGroup.responseName)
    : addGuardedFieldEntry entry groups
      = groups ++ [{ responseName := entry.field.responseName, entries := [entry] }] := by
  induction groups with
  | nil => rfl
  | cons group rest ih =>
      have hparts : entry.field.responseName ≠ group.responseName
          ∧ entry.field.responseName
            ∉ rest.map GuardedFieldGroup.responseName := by
        simpa only [List.map_cons, List.mem_cons, not_or] using hname
      simp only [addGuardedFieldEntry, beq_iff_eq, hparts.1, if_false,
        List.cons_append, List.cons.injEq, true_and]
      exact ih hparts.2

private theorem addGuardedFieldEntry_existing
    (entry : SelectionConditions.ConditionedField) (names : List Name)
    (entries : List SelectionConditions.ConditionedField)
    (hnodup : names.Nodup) (hname : entry.field.responseName ∈ names)
    : addGuardedFieldEntry entry (guardedFieldGroupsForNames names entries)
      = guardedFieldGroupsForNames names (entries ++ [entry]) := by
  induction names with
  | nil => simp at hname
  | cons responseName rest ih =>
      have hparts := List.nodup_cons.mp hnodup
      rcases List.mem_cons.mp hname with hhead | hrest
      · subst responseName
        simp only [guardedFieldGroupsForNames, List.map_cons,
          addGuardedFieldEntry, beq_self_eq_true, if_true]
        rw [conditionedFieldsForResponseName_append_eq_append]
        have htail := guardedFieldGroupsForNames_append_eq_self rest entries entry hparts.1
        congr 1
        simpa only [guardedFieldGroupsForNames] using htail.symm
      · have hne : entry.field.responseName ≠ responseName := by
          intro heq
          subst responseName
          exact hparts.1 hrest
        simp only [guardedFieldGroupsForNames, List.map_cons,
          addGuardedFieldEntry, beq_iff_eq, hne, if_false, List.cons.injEq]
        constructor
        · rw [conditionedFieldsForResponseName_append_eq_self _ _ _ hne]
        · exact ih hparts.2 hrest

private theorem addGuardedFieldEntry_byFiltering
    (entries : List SelectionConditions.ConditionedField)
    (entry : SelectionConditions.ConditionedField)
    : addGuardedFieldEntry entry (guardedFieldGroupsByFiltering entries)
      = guardedFieldGroupsByFiltering (entries ++ [entry]) := by
  let names := (entries.map fun item => item.field.responseName).eraseDups
  by_cases hname : entry.field.responseName ∈ names
  · have hnodup : names.Nodup := eraseDups_nodup _
    rw [guardedFieldGroupsByFiltering, guardedFieldGroupsByFiltering,
      List.map_append, List.eraseDups_append]
    change addGuardedFieldEntry entry (guardedFieldGroupsForNames names entries)
      = guardedFieldGroupsForNames
          (names ++ ([entry.field.responseName].removeAll
            (entries.map fun item => item.field.responseName)).eraseDups)
          (entries ++ [entry])
    have hsource : entry.field.responseName
        ∈ entries.map fun item => item.field.responseName :=
      List.mem_eraseDups.mp hname
    have hremoved : [entry.field.responseName].removeAll
        (entries.map fun item => item.field.responseName) = [] := by
      have hcontains : (entries.map fun item => item.field.responseName).contains
          entry.field.responseName = true := List.contains_iff_mem.mpr hsource
      rw [List.cons_removeAll, hcontains]
      rfl
    rw [hremoved]
    simpa using addGuardedFieldEntry_existing entry names entries hnodup hname
  · rw [guardedFieldGroupsByFiltering, guardedFieldGroupsByFiltering,
      List.map_append, List.eraseDups_append]
    change addGuardedFieldEntry entry (guardedFieldGroupsForNames names entries)
      = guardedFieldGroupsForNames
          (names ++ ([entry.field.responseName].removeAll
            (entries.map fun item => item.field.responseName)).eraseDups)
          (entries ++ [entry])
    have hsource : entry.field.responseName
        ∉ entries.map fun item => item.field.responseName := by
      simpa only [names, List.mem_eraseDups] using hname
    have hremoved : [entry.field.responseName].removeAll
        (entries.map fun item => item.field.responseName) = [entry.field.responseName] := by
      have hcontains : (entries.map fun item => item.field.responseName).contains
          entry.field.responseName = false := by
        cases hresult
              : (entries.map fun item => item.field.responseName).contains
                  entry.field.responseName with
        | false => rfl
        | true => exact False.elim (hsource (List.contains_iff_mem.mp hresult))
      rw [List.cons_removeAll, hcontains]
      rfl
    rw [hremoved]
    have hadd := addGuardedFieldEntry_not_mem entry
      (guardedFieldGroupsForNames names entries) (by
        simpa [guardedFieldGroupsForNames] using hname)
    rw [hadd]
    simp only [List.eraseDups_cons, List.filter_nil, List.eraseDups_nil]
    have hsame := guardedFieldGroupsForNames_append_eq_self names entries entry hname
    have hempty := conditionedFieldsForResponseName_eq_nil_of_not_mem
      entry.field.responseName entries hsource
    unfold guardedFieldGroupsForNames at hsame ⊢
    rw [List.map_append, List.map_singleton, hsame,
      conditionedFieldsForResponseName_append_eq_append, hempty, List.nil_append]

private theorem foldl_addGuardedFieldEntry_byFiltering
    (processed remaining : List SelectionConditions.ConditionedField)
    : remaining.foldl (fun groups entry => addGuardedFieldEntry entry groups)
        (guardedFieldGroupsByFiltering processed)
      = guardedFieldGroupsByFiltering (processed ++ remaining) := by
  induction remaining generalizing processed with
  | nil => simp
  | cons entry rest ih =>
      simp only [List.foldl_cons]
      rw [addGuardedFieldEntry_byFiltering]
      simpa only [List.append_assoc, List.singleton_append] using
        ih (processed ++ [entry])

theorem guardedFieldGroups_eq_byFiltering
    (entries : List SelectionConditions.ConditionedField)
    : guardedFieldGroups entries = guardedFieldGroupsByFiltering entries := by
  unfold guardedFieldGroups
  simpa [guardedFieldGroupsByFiltering, guardedFieldGroupsForNames] using
    foldl_addGuardedFieldEntry_byFiltering [] entries

def executableGroupsForResponseNames (names : List Name) (fields : List ExecutableField)
    : List (Name × List ExecutableField) :=
  names.flatMap
    fun responseName =>
      executableFieldsAsGroup responseName
        (fields.filter fun field => field.responseName == responseName)

theorem executableGroupsForResponseNames_wellFormed (names : List Name)
    (fields : List ExecutableField)
    : NormalForm.executableGroupsWellFormed
        (executableGroupsForResponseNames names fields) := by
  intro group hgroup
  rcases List.mem_flatMap.mp hgroup with ⟨responseName, _hname, hgroup⟩
  cases hfields : fields.filter (fun field => field.responseName == responseName) with
  | nil => simp [executableFieldsAsGroup, hfields] at hgroup
  | cons field rest =>
      simp [executableFieldsAsGroup, hfields] at hgroup
      subst group
      constructor
      · simp
      · intro candidate hcandidate
        have hfiltered : candidate ∈
            fields.filter (fun item => item.responseName == responseName) := by
          simpa [hfields] using hcandidate
        exact beq_iff_eq.mp (List.mem_filter.mp hfiltered).2

theorem executableGroupsForResponseNames_keysNodup
    {names : List Name} (hnodup : names.Nodup) (fields : List ExecutableField)
    : ((executableGroupsForResponseNames names fields).map Prod.fst).Nodup := by
  induction names with
  | nil => simp [executableGroupsForResponseNames]
  | cons responseName rest ih =>
      have hparts := List.nodup_cons.mp hnodup
      rw [executableGroupsForResponseNames, List.flatMap_cons, List.map_append]
      cases hfields : fields.filter (fun field => field.responseName == responseName) with
      | nil =>
          change ((executableGroupsForResponseNames rest fields).map Prod.fst).Nodup
          exact ih hparts.2
      | cons field tail =>
          change (responseName ::
            (executableGroupsForResponseNames rest fields).map Prod.fst).Nodup
          rw [List.nodup_cons]
          constructor
          · intro hmember
            rcases List.mem_map.mp hmember with ⟨group, hgroup, hname⟩
            rcases List.mem_flatMap.mp hgroup with ⟨candidate, hcandidate, hgroup⟩
            cases hcandidateFields
                  : fields.filter (fun item => item.responseName == candidate) with
            | nil => simp [executableFieldsAsGroup, hcandidateFields] at hgroup
            | cons candidateField candidateRest =>
                simp [executableFieldsAsGroup, hcandidateFields] at hgroup
                subst group
                simp at hname
                exact hparts.1 (hname ▸ hcandidate)
          · exact ih hparts.2

theorem flattenCollectedFields_executableGroupsForResponseNames
    (names : List Name) (fields : List ExecutableField)
    : flattenCollectedFields (executableGroupsForResponseNames names fields)
      = names.flatMap
          fun responseName =>
            fields.filter fun field => field.responseName == responseName := by
  induction names with
  | nil => rfl
  | cons responseName rest ih =>
      rw [executableGroupsForResponseNames, List.flatMap_cons]
      cases hfields : fields.filter (fun field => field.responseName == responseName) with
      | nil =>
          simp only [hfields, executableFieldsAsGroup, List.flatMap_cons,
            List.nil_append]
          exact ih
      | cons field tail =>
          simp only [hfields, executableFieldsAsGroup, List.flatMap_cons]
          change flattenCollectedFields
              ([(responseName, field :: tail)]
                ++ executableGroupsForResponseNames rest fields)
            = (field :: tail) ++ rest.flatMap
                (fun responseName =>
                  fields.filter fun field => field.responseName == responseName)
          simp [flattenCollectedFields, ih]

theorem filtersByResponseNames_perm
    (names : List Name) (fields : List ExecutableField)
    (hnodup : names.Nodup)
    (hcovered : ∀ field, field ∈ fields -> field.responseName ∈ names)
    : (names.flatMap
        fun responseName => fields.filter fun field => field.responseName == responseName)
      |>.Perm fields := by
  induction names generalizing fields with
  | nil =>
      have hempty : fields = [] := by
        cases fields with
        | nil => rfl
        | cons field rest => exact False.elim (by simpa using hcovered field (by simp))
      subst fields
      simp
  | cons responseName rest ih =>
      have hparts := List.nodup_cons.mp hnodup
      let matchingFields := fields.filter fun field => field.responseName == responseName
      let others := fields.filter fun field => !(field.responseName == responseName)
      have hrestCovered : ∀ field, field ∈ others -> field.responseName ∈ rest := by
        intro field hfield
        have hmember := List.mem_filter.mp hfield
        rcases List.mem_cons.mp (hcovered field hmember.1) with hhead | hrest
        · subst responseName
          simp at hmember
        · exact hrest
      have hrestPerm := ih others hparts.2 hrestCovered
      have hfilters : rest.flatMap
            (fun candidate => fields.filter fun field => field.responseName == candidate)
          = rest.flatMap
            (fun candidate => others.filter fun field => field.responseName == candidate) := by
        apply congrArg List.flatten
        apply List.map_congr_left
        intro candidate hcandidate
        rw [List.filter_filter]
        apply List.filter_congr
        intro field _hfield
        have hne : candidate ≠ responseName := by
          intro heq
          subst candidate
          exact hparts.1 hcandidate
        by_cases hcandidateField : field.responseName = candidate
        · subst candidate
          simp [hne]
        · simp [hcandidateField]
      rw [List.flatMap_cons, hfilters]
      exact (List.Perm.append_left matchingFields hrestPerm).trans
        (List.filter_append_perm (fun field => field.responseName == responseName)
          fields)

theorem executableGroupsForResponseNames_runtimeFieldGroupsExact (names : List Name)
    (fields : List ExecutableField) (hnodup : names.Nodup)
    (hcovered : ∀ field, field ∈ fields -> field.responseName ∈ names)
    : RuntimeFieldGroupsExact fields (executableGroupsForResponseNames names fields) := by
  constructor
  · exact executableGroupsForResponseNames_keysNodup hnodup fields
  · rw [flattenCollectedFields_executableGroupsForResponseNames]
    exact filtersByResponseNames_perm names fields hnodup hcovered

theorem runtimeFields_responseName_mem
    (variableValues : VariableValues) (executionParentType runtimeType : Name)
    (entries : List SelectionConditions.ConditionedField)
    {field : ExecutableField}
    (hfield
      : field
        ∈ SelectionConditions.runtimeFields variableValues
            executionParentType runtimeType entries)
    : field.responseName ∈ entries.map fun entry => entry.field.responseName := by
  induction entries with
  | nil => simp [SelectionConditions.runtimeFields] at hfield
  | cons entry rest ih =>
      rw [SelectionConditions.runtimeFields, List.flatMap_cons] at hfield
      rcases List.mem_append.mp hfield with hhead | hrest
      · split at hhead
        · simp at hhead
          subst field
          simp
        · simp at hhead
      · simp [ih hrest]

theorem guardedFieldRuntimeGroups_guardedFieldGroups
    (variableValues : VariableValues) (executionParentType runtimeType : Name)
    (entries : List SelectionConditions.ConditionedField)
    : guardedFieldRuntimeGroups variableValues executionParentType runtimeType
        (guardedFieldGroups entries)
      = executableGroupsForResponseNames
          ((entries.map fun entry => entry.field.responseName).eraseDups)
          (SelectionConditions.runtimeFields variableValues executionParentType
            runtimeType entries) := by
  let fields := SelectionConditions.runtimeFields variableValues executionParentType
    runtimeType entries
  let names := (entries.map fun entry => entry.field.responseName).eraseDups
  rw [guardedFieldGroups_eq_byFiltering]
  change guardedFieldRuntimeGroups variableValues executionParentType runtimeType
      (names.map fun responseName =>
        { responseName,
          entries := conditionedFieldsForResponseName responseName entries })
    = executableGroupsForResponseNames names fields
  induction names with
  | nil => rfl
  | cons responseName rest ih =>
      rw [List.map_cons, guardedFieldRuntimeGroups, List.flatMap_cons,
        executableGroupsForResponseNames, List.flatMap_cons,
        guardedFieldExecutableFields_entriesForName]
      exact congrArg
        (fun tail => executableFieldsAsGroup responseName
          (fields.filter fun field => field.responseName == responseName) ++ tail) ih

theorem guardedFieldRuntimeGroups_runtimeFieldGroupsExact
    (variableValues : VariableValues) (executionParentType runtimeType : Name)
    (entries : List SelectionConditions.ConditionedField)
    : RuntimeFieldGroupsExact
        (SelectionConditions.runtimeFields variableValues executionParentType
          runtimeType entries)
        (guardedFieldRuntimeGroups variableValues executionParentType runtimeType
          (guardedFieldGroups entries)) := by
  rw [guardedFieldRuntimeGroups_guardedFieldGroups]
  apply executableGroupsForResponseNames_runtimeFieldGroupsExact
  · exact eraseDups_nodup _
  · intro field hfield
    exact List.mem_eraseDups.mpr
      (runtimeFields_responseName_mem variableValues executionParentType
        runtimeType entries hfield)

theorem guardedFieldRuntimeGroups_permutationEquivalent
    (variableValues : VariableValues) (executionParentType runtimeType : Name)
    (entries : List SelectionConditions.ConditionedField)
    : RuntimeGroupsPermutationEquivalent
        (guardedFieldRuntimeGroups variableValues executionParentType runtimeType
          (guardedFieldGroups entries))
        (groupExecutableFields
          (SelectionConditions.runtimeFields variableValues executionParentType
            runtimeType entries)) := by
  let guardedGroups := guardedFieldRuntimeGroups variableValues executionParentType
    runtimeType (guardedFieldGroups entries)
  let groupedFields := groupExecutableFields
    (SelectionConditions.runtimeFields variableValues executionParentType runtimeType
      entries)
  have hguarded := guardedFieldRuntimeGroups_runtimeFieldGroupsExact variableValues
    executionParentType runtimeType entries
  have hgrouped := groupExecutableFields_exact
    (SelectionConditions.runtimeFields variableValues executionParentType runtimeType
      entries)
  exact {
    leftWellFormed := by
      rw [guardedFieldRuntimeGroups_guardedFieldGroups]
      exact executableGroupsForResponseNames_wellFormed _ _
    rightWellFormed := groupExecutableFields_wellFormed _
    leftKeysNodup := hguarded.1
    rightKeysNodup := hgrouped.1
    fieldsPerm := by
      simpa only [← Execution.FieldGroups.flattenCollectedFields_eq_flatMap_snd]
        using hguarded.2.trans hgrouped.2.symm
  }

theorem runtimeGroupsPermutationEquivalent_trans
    {left middle right : List (Name × List ExecutableField)}
    (hleft : RuntimeGroupsPermutationEquivalent left middle)
    (hright : RuntimeGroupsPermutationEquivalent middle right)
    : RuntimeGroupsPermutationEquivalent left right :=
  {
    leftWellFormed := hleft.leftWellFormed
    rightWellFormed := hright.rightWellFormed
    leftKeysNodup := hleft.leftKeysNodup
    rightKeysNodup := hright.rightKeysNodup
    fieldsPerm := hleft.fieldsPerm.trans hright.fieldsPerm
  }

theorem runtimeGroupsPermutationEquivalent_singleton_of_mem
    {left right : List (Name × List ExecutableField)}
    (equivalent : RuntimeGroupsPermutationEquivalent left right)
    {responseName : Name} {leftFields : List ExecutableField}
    (hleft : (responseName, leftFields) ∈ left)
    : ∃ rightFields,
        (responseName, rightFields) ∈ right
        ∧ RuntimeGroupsPermutationEquivalent
            [(responseName, leftFields)] [(responseName, rightFields)] := by
  rcases runtimeGroupsPermutationEquivalent_matchingGroup equivalent hleft with
    ⟨rightFields, hright, hfields⟩
  refine ⟨rightFields, hright, ?_⟩
  constructor
  · intro group hgroup
    have heq : group = (responseName, leftFields) := by simpa using hgroup
    subst group
    exact equivalent.leftWellFormed (responseName, leftFields) hleft
  · intro group hgroup
    have heq : group = (responseName, rightFields) := by simpa using hgroup
    subst group
    exact equivalent.rightWellFormed (responseName, rightFields) hright
  · simp
  · simp
  · simpa [flattenCollectedFields] using hfields

theorem completionFieldsWitness_of_perm
    {schema : Schema} {fieldType : TypeRef}
    {source target : List ExecutableField}
    (hperm : source.Perm target)
    (hwitness : completionFieldsWitness schema fieldType source)
    : completionFieldsWitness schema fieldType target := by
  rcases hwitness with ⟨field, definition, hfield, hlookup, htype⟩
  exact ⟨field, definition, hperm.mem_iff.mp hfield, hlookup, htype⟩

end QueryInclusion
end GraphQL
