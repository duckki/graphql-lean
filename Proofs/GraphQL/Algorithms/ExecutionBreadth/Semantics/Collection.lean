import GraphQL.Algorithms.ExecutionBreadth
import Proofs.GraphQL.SchemaWellFormedness.PossibleTypes
import Proofs.GraphQL.Theories.NormalForm.Shared.Execution

/-!
Collection facts for breadth execution.
-/

namespace GraphQL

namespace Algorithms
namespace ExecutionBreadth

open GraphQL.Execution

variable {ObjectRef : Type}

def collectedGroupsResponseName (groups : List (Name × List ExecutableField)) : Prop :=
  ∀ (responseName : Name) (fields : List ExecutableField) (field : ExecutableField),
    (responseName, fields) ∈ groups -> field ∈ fields -> field.responseName = responseName

def executableFieldsResponseName (responseName : Name) (fields : List ExecutableField)
    : Prop :=
  ∀ (field : ExecutableField), field ∈ fields -> field.responseName = responseName

def collectedGroupsNonempty (groups : List (Name × List ExecutableField)) : Prop :=
  ∀ (responseName : Name) (fields : List ExecutableField),
    (responseName, fields) ∈ groups -> fields ≠ []

def pairKeysNodup {α : Type} (pairs : List (Name × α)) : Prop :=
  (pairs.map Prod.fst).Nodup

def executableFieldsSize : List ExecutableField -> Nat
  | [] => 0
  | field :: fields =>
      1 + SelectionSet.size field.selectionSet + executableFieldsSize fields

def executableGroupsSize : List (Name × List ExecutableField) -> Nat
  | [] => 0
  | (_responseName, fields) :: groups =>
      executableFieldsSize fields + executableGroupsSize groups

def executableFieldBreadthWeight (schema : Schema) (field : ExecutableField) : Nat :=
  1
  + (schema.objectTypes.length + 1) * selectionSetBreadthWeight schema field.selectionSet

def executableFieldsBreadthWeight (schema : Schema) : List ExecutableField -> Nat
  | [] => 0
  | field :: fields =>
      executableFieldBreadthWeight schema field
      + executableFieldsBreadthWeight schema fields

def executableGroupsBreadthWeight (schema : Schema)
    : List (Name × List ExecutableField) -> Nat
  | [] => 0
  | (_responseName, fields) :: groups =>
      executableFieldsBreadthWeight schema fields
      + executableGroupsBreadthWeight schema groups

theorem executableFieldsSize_append (left right : List ExecutableField)
    : executableFieldsSize (left ++ right)
      = executableFieldsSize left + executableFieldsSize right := by
  induction left with
  | nil =>
      simp [executableFieldsSize]
  | cons field left ih =>
      simp [executableFieldsSize, ih, Nat.add_assoc]

theorem selectionSet_size_append (left right : List Selection)
    : SelectionSet.size (left ++ right)
      = SelectionSet.size left + SelectionSet.size right := by
  induction left with
  | nil =>
      simp [SelectionSet.size]
  | cons selection left ih =>
      simp [SelectionSet.size, ih, Nat.add_assoc]

theorem selectionSetBreadthWeight_append (schema : Schema) (left right : List Selection)
    : selectionSetBreadthWeight schema (left ++ right)
      = selectionSetBreadthWeight schema left
        + selectionSetBreadthWeight schema right := by
  induction left with
  | nil =>
      simp [selectionSetBreadthWeight]
  | cons selection left ih =>
      simp [selectionSetBreadthWeight, ih, Nat.add_assoc]

theorem executableFieldsBreadthWeight_append
    (schema : Schema) (left right : List ExecutableField)
    : executableFieldsBreadthWeight schema (left ++ right)
      = executableFieldsBreadthWeight schema left
        + executableFieldsBreadthWeight schema right := by
  induction left with
  | nil =>
      simp [executableFieldsBreadthWeight]
  | cons field left ih =>
      simp [executableFieldsBreadthWeight, ih, Nat.add_assoc]

theorem childSelectionSetForFields_size (fields : List ExecutableField)
    : SelectionSet.size (childSelectionSetForFields fields)
      = fields.foldr
          (fun field size => SelectionSet.size field.selectionSet + size) 0 := by
  induction fields with
  | nil =>
      simp [childSelectionSetForFields, SelectionSet.size]
  | cons field fields ih =>
      change
        SelectionSet.size
            (field.selectionSet ++ (fields.map (fun field => field.selectionSet)).flatten) =
          SelectionSet.size field.selectionSet +
            fields.foldr
              (fun field size => SelectionSet.size field.selectionSet + size) 0
      rw [selectionSet_size_append]
      simpa [childSelectionSetForFields] using
        congrArg (fun size => SelectionSet.size field.selectionSet + size) ih

theorem childSelectionSetForFields_size_le_executableFieldsSize
    (fields : List ExecutableField)
    : SelectionSet.size (childSelectionSetForFields fields)
      <= executableFieldsSize fields := by
  induction fields with
  | nil =>
      simp [childSelectionSetForFields, SelectionSet.size, executableFieldsSize]
  | cons field fields ih =>
      rw [childSelectionSetForFields_size]
      simp [executableFieldsSize]
      have hfoldLe :
          fields.foldr
              (fun field size => SelectionSet.size field.selectionSet + size) 0 <=
            executableFieldsSize fields := by
        simpa [childSelectionSetForFields_size] using ih
      omega

theorem childSelectionSetForFields_size_succ_le_executableFieldsSize
    (fields : List ExecutableField)
    : fields ≠ []
      -> SelectionSet.size (childSelectionSetForFields fields) + 1
          <= executableFieldsSize fields := by
  intro hfields
  cases fields with
  | nil =>
      exact False.elim (hfields rfl)
  | cons field fields =>
      rw [childSelectionSetForFields_size]
      simp [executableFieldsSize]
      have hfoldLe :
          fields.foldr
              (fun field size => SelectionSet.size field.selectionSet + size) 0 <=
            executableFieldsSize fields := by
        simpa [childSelectionSetForFields_size] using
          childSelectionSetForFields_size_le_executableFieldsSize fields
      omega

theorem childSelectionSetForFields_breadthWeight
    (schema : Schema) (fields : List ExecutableField)
    : selectionSetBreadthWeight schema (childSelectionSetForFields fields)
      = fields.foldr
          (fun field weight =>
            selectionSetBreadthWeight schema field.selectionSet + weight) 0 := by
  induction fields with
  | nil =>
      simp [childSelectionSetForFields, selectionSetBreadthWeight]
  | cons field fields ih =>
      change
        selectionSetBreadthWeight schema
            (field.selectionSet ++
              (fields.map (fun field => field.selectionSet)).flatten) =
          selectionSetBreadthWeight schema field.selectionSet +
            fields.foldr
              (fun field weight =>
                selectionSetBreadthWeight schema field.selectionSet + weight) 0
      rw [selectionSetBreadthWeight_append]
      simpa [childSelectionSetForFields] using
        congrArg
          (fun weight =>
            selectionSetBreadthWeight schema field.selectionSet + weight)
          ih

theorem childSelectionSetForFields_runtimeStepWeight_le_executableFieldsBreadthWeight
    (schema : Schema) (fields : List ExecutableField)
    : fields ≠ []
      -> 1
            + (schema.objectTypes.length + 1)
              * selectionSetBreadthWeight schema (childSelectionSetForFields fields)
          <= executableFieldsBreadthWeight schema fields := by
  intro hfields
  induction fields with
  | nil =>
      exact False.elim (hfields rfl)
  | cons field fields ih =>
      have htail :
          (schema.objectTypes.length + 1)
              * selectionSetBreadthWeight schema
                (childSelectionSetForFields fields) <=
            executableFieldsBreadthWeight schema fields := by
        cases fields with
        | nil =>
            simp [childSelectionSetForFields, selectionSetBreadthWeight,
              executableFieldsBreadthWeight]
        | cons tail tails =>
            have htailStep :=
              ih (by simp)
            omega
      rw [childSelectionSetForFields_breadthWeight]
      rw [childSelectionSetForFields_breadthWeight] at htail
      simp [executableFieldsBreadthWeight, executableFieldBreadthWeight]
      rw [Nat.mul_add]
      omega

theorem executableFieldsSize_le_executableGroupsSize_of_mem
    (responseName : Name) (fields : List ExecutableField)
    (groups : List (Name × List ExecutableField))
    : (responseName, fields) ∈ groups
      -> executableFieldsSize fields <= executableGroupsSize groups := by
  intro hmem
  induction groups with
  | nil =>
      simp at hmem
  | cons group groups ih =>
      rcases group with ⟨headName, headFields⟩
      simp at hmem
      rcases hmem with hhead | htail
      · rcases hhead with ⟨_hname, hfields⟩
        subst fields
        simp [executableGroupsSize]
      · have htailLe := ih htail
        simp [executableGroupsSize]
        omega

theorem executableFieldsResponseName_append
    (responseName : Name) (left right : List ExecutableField)
    : executableFieldsResponseName responseName left
      -> executableFieldsResponseName responseName right
      -> executableFieldsResponseName responseName (left ++ right) := by
  intro hleft hright field hmem
  simp at hmem
  rcases hmem with hmem | hmem
  · exact hleft field hmem
  · exact hright field hmem

theorem collectedGroupsResponseName_tail
    (responseName : Name) (fields : List ExecutableField)
    (groups : List (Name × List ExecutableField))
    : collectedGroupsResponseName ((responseName, fields) :: groups)
      -> collectedGroupsResponseName groups := by
  intro hgroups groupResponseName groupFields field groupMem fieldMem
  exact hgroups groupResponseName groupFields field (by simp [groupMem])
    fieldMem

theorem collectedGroupsResponseName_addExecutableGroup
    (group : Name × List ExecutableField)
    (groups : List (Name × List ExecutableField))
    : executableFieldsResponseName group.fst group.snd
      -> collectedGroupsResponseName groups
      -> collectedGroupsResponseName (addExecutableGroup group groups) := by
  rcases group with ⟨groupResponseName, groupFields⟩
  intro hgroup hgroups
  induction groups with
  | nil =>
      intro responseName fields field hmem hfield
      simp [addExecutableGroup] at hmem
      rcases hmem with ⟨hresponse, hfields⟩
      subst responseName
      subst fields
      exact hgroup field hfield
  | cons current rest ih =>
      rcases current with ⟨currentResponseName, currentFields⟩
      by_cases hsame : currentResponseName == groupResponseName
      · have hresponse : currentResponseName = groupResponseName := by
          simpa using hsame
        intro responseName fields field hmem hfield
        simp [addExecutableGroup, hsame] at hmem
        rcases hmem with hhead | htail
        · rcases hhead with ⟨hresponseName, hfields⟩
          subst responseName
          subst fields
          have happ :
              executableFieldsResponseName currentResponseName
                (currentFields ++ groupFields) :=
            executableFieldsResponseName_append currentResponseName
              currentFields groupFields
              (by
                intro field hmem
                exact hgroups _ _ _ (by simp) hmem)
              (by
                intro field hmem
                simpa [hresponse] using hgroup field hmem)
          exact happ field hfield
        · exact hgroups _ _ _ (by simp [htail]) hfield
      · have hrest : collectedGroupsResponseName rest :=
          collectedGroupsResponseName_tail currentResponseName currentFields rest
            hgroups
        have haddRest :
            collectedGroupsResponseName
              (addExecutableGroup (groupResponseName, groupFields) rest) :=
          ih hrest
        intro responseName fields field hmem hfield
        simp [addExecutableGroup, hsame] at hmem
        rcases hmem with hhead | htail
        · rcases hhead with ⟨hresponseName, hfields⟩
          subst responseName
          subst fields
          exact hgroups _ _ _ (by simp) hfield
        · exact haddRest _ _ _ htail hfield

theorem collectedGroupsResponseName_mergeExecutableGroups
    (left right : List (Name × List ExecutableField))
    : collectedGroupsResponseName left
      -> collectedGroupsResponseName right
      -> collectedGroupsResponseName (mergeExecutableGroups left right) := by
  intro hleft hright
  induction right generalizing left with
  | nil =>
      simpa [mergeExecutableGroups]
  | cons group rest ih =>
      have hgroupFields : executableFieldsResponseName group.fst group.snd := by
        intro field hfield
        exact hright _ _ _ (by simp) hfield
      have hrest : collectedGroupsResponseName rest := by
        cases group with
        | mk responseName fields =>
            exact collectedGroupsResponseName_tail responseName fields rest hright
      simpa [mergeExecutableGroups, List.foldl]
        using ih (addExecutableGroup group left)
          (collectedGroupsResponseName_addExecutableGroup group left
            hgroupFields hleft)
          hrest

theorem collectedGroupsNonempty_tail
    (responseName : Name) (fields : List ExecutableField)
    (groups : List (Name × List ExecutableField))
    : collectedGroupsNonempty ((responseName, fields) :: groups)
      -> collectedGroupsNonempty groups := by
  intro hgroups groupResponseName groupFields groupMem
  exact hgroups groupResponseName groupFields (by simp [groupMem])

theorem collectedGroupsNonempty_addExecutableGroup
    (group : Name × List ExecutableField)
    (groups : List (Name × List ExecutableField))
    : group.snd ≠ []
      -> collectedGroupsNonempty groups
      -> collectedGroupsNonempty (addExecutableGroup group groups) := by
  rcases group with ⟨groupResponseName, groupFields⟩
  intro hgroup hgroups
  induction groups with
  | nil =>
      intro responseName fields hmem
      simp [addExecutableGroup] at hmem
      rcases hmem with ⟨hresponse, hfields⟩
      subst responseName
      subst fields
      exact hgroup
  | cons current rest ih =>
      rcases current with ⟨currentResponseName, currentFields⟩
      by_cases hsame : currentResponseName == groupResponseName
      · intro responseName fields hmem
        simp [addExecutableGroup, hsame] at hmem
        rcases hmem with hhead | htail
        · rcases hhead with ⟨hresponseName, hfields⟩
          subst responseName
          subst fields
          intro happEmpty
          have hcurrent :
              currentFields ≠ [] :=
            hgroups currentResponseName currentFields (by simp)
          cases currentFields with
          | nil =>
              exact hcurrent rfl
          | cons _ _ =>
              simp at happEmpty
        · exact hgroups responseName fields (by simp [htail])
      · have hrest : collectedGroupsNonempty rest :=
          collectedGroupsNonempty_tail currentResponseName currentFields rest
            hgroups
        have haddRest :
            collectedGroupsNonempty
              (addExecutableGroup (groupResponseName, groupFields) rest) :=
          ih hrest
        intro responseName fields hmem
        simp [addExecutableGroup, hsame] at hmem
        rcases hmem with hhead | htail
        · rcases hhead with ⟨hresponseName, hfields⟩
          subst responseName
          subst fields
          exact hgroups currentResponseName currentFields (by simp)
        · exact haddRest responseName fields htail

theorem collectedGroupsNonempty_mergeExecutableGroups
    (left right : List (Name × List ExecutableField))
    : collectedGroupsNonempty left
      -> collectedGroupsNonempty right
      -> collectedGroupsNonempty (mergeExecutableGroups left right) := by
  intro hleft hright
  induction right generalizing left with
  | nil =>
      simpa [mergeExecutableGroups] using hleft
  | cons group rest ih =>
      have hgroupFields : group.snd ≠ [] := by
        cases group with
        | mk responseName fields =>
            exact hright responseName fields (by simp)
      have hrest : collectedGroupsNonempty rest := by
        cases group with
        | mk responseName fields =>
            exact collectedGroupsNonempty_tail responseName fields rest hright
      simpa [mergeExecutableGroups, List.foldl]
        using ih (addExecutableGroup group left)
          (collectedGroupsNonempty_addExecutableGroup group left
            hgroupFields hleft)
          hrest

theorem executableGroupsSize_addExecutableGroup
    (group : Name × List ExecutableField)
    (groups : List (Name × List ExecutableField))
    : executableGroupsSize (addExecutableGroup group groups)
      = executableFieldsSize group.snd + executableGroupsSize groups := by
  rcases group with ⟨groupName, groupFields⟩
  induction groups with
  | nil =>
      simp [addExecutableGroup, executableGroupsSize]
  | cons current rest ih =>
      rcases current with ⟨currentName, currentFields⟩
      by_cases hsame : currentName == groupName
      · simp [addExecutableGroup, executableGroupsSize, hsame,
          executableFieldsSize_append]
        omega
      · simp [addExecutableGroup, executableGroupsSize, hsame, ih]
        omega

theorem executableGroupsBreadthWeight_addExecutableGroup
    (schema : Schema)
    (group : Name × List ExecutableField)
    (groups : List (Name × List ExecutableField))
    : executableGroupsBreadthWeight schema (addExecutableGroup group groups)
      = executableFieldsBreadthWeight schema group.snd
        + executableGroupsBreadthWeight schema groups := by
  rcases group with ⟨groupName, groupFields⟩
  induction groups with
  | nil =>
      simp [addExecutableGroup, executableGroupsBreadthWeight]
  | cons current rest ih =>
      rcases current with ⟨currentName, currentFields⟩
      by_cases hsame : currentName == groupName
      · simp [addExecutableGroup, executableGroupsBreadthWeight, hsame,
          executableFieldsBreadthWeight_append]
        omega
      · simp [addExecutableGroup, executableGroupsBreadthWeight, hsame, ih]
        omega

theorem executableGroupsSize_mergeExecutableGroups
    (left right : List (Name × List ExecutableField))
    : executableGroupsSize (mergeExecutableGroups left right)
      = executableGroupsSize left + executableGroupsSize right := by
  induction right generalizing left with
  | nil =>
      simp [mergeExecutableGroups, executableGroupsSize]
  | cons group rest ih =>
      change
        executableGroupsSize
            (mergeExecutableGroups (addExecutableGroup group left) rest) =
          executableGroupsSize left +
            (executableFieldsSize group.snd + executableGroupsSize rest)
      rw [ih (addExecutableGroup group left)]
      rw [executableGroupsSize_addExecutableGroup]
      omega

theorem executableGroupsBreadthWeight_mergeExecutableGroups
    (schema : Schema)
    (left right : List (Name × List ExecutableField))
    : executableGroupsBreadthWeight schema (mergeExecutableGroups left right)
      = executableGroupsBreadthWeight schema left
        + executableGroupsBreadthWeight schema right := by
  induction right generalizing left with
  | nil =>
      simp [mergeExecutableGroups, executableGroupsBreadthWeight]
  | cons group rest ih =>
      change
        executableGroupsBreadthWeight schema
            (mergeExecutableGroups (addExecutableGroup group left) rest) =
          executableGroupsBreadthWeight schema left +
            (executableFieldsBreadthWeight schema group.snd +
              executableGroupsBreadthWeight schema rest)
      rw [ih (addExecutableGroup group left)]
      rw [executableGroupsBreadthWeight_addExecutableGroup]
      omega

mutual
  theorem collectSelectionByKey_executableGroupsSize_le
      (schema : Schema) (variableValues : VariableValues)
      (parentType : Name) (selection : Selection)
      : executableGroupsSize
          (collectSelectionByKey schema variableValues parentType selection)
        <= selection.size := by
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        by_cases hdirectives :
            selectionDirectivesAllowBool variableValues directives = true
        · simp [collectSelectionByKey, hdirectives, buildExecutionField,
            executableGroupsSize, executableFieldsSize, Selection.size]
        · simp [collectSelectionByKey, hdirectives, Selection.size,
            executableGroupsSize]
    | inlineFragment typeCondition directives selectionSet =>
        cases typeCondition with
        | none =>
            by_cases hdirectives :
                selectionDirectivesAllowBool variableValues directives = true
            · have hchild :=
                collectFieldsByKey_executableGroupsSize_le schema variableValues
                  parentType selectionSet
              simp [collectSelectionByKey, hdirectives, Selection.size]
              omega
            · simp [collectSelectionByKey, hdirectives, Selection.size,
                executableGroupsSize]
        | some typeCondition =>
            by_cases hdirectives :
                selectionDirectivesAllowBool variableValues directives = true
            · by_cases hpossible :
                  parentTypeIsPossible schema parentType typeCondition = true
              · have hchild :=
                  collectFieldsByKey_executableGroupsSize_le schema variableValues
                    parentType selectionSet
                simp [collectSelectionByKey, hdirectives, hpossible,
                  Selection.size]
                omega
              · simp [collectSelectionByKey, hdirectives, hpossible,
                  Selection.size, executableGroupsSize]
            · simp [collectSelectionByKey, hdirectives, Selection.size,
                executableGroupsSize]

  theorem collectFieldsByKey_executableGroupsSize_le
      (schema : Schema) (variableValues : VariableValues)
      (parentType : Name) (selectionSet : List Selection)
      : executableGroupsSize
          (collectFieldsByKey schema variableValues parentType selectionSet)
        <= SelectionSet.size selectionSet := by
    cases selectionSet with
    | nil =>
        simp [collectFieldsByKey, executableGroupsSize, SelectionSet.size]
    | cons selection rest =>
        have hhead :=
          collectSelectionByKey_executableGroupsSize_le schema variableValues
            parentType selection
        have htail :=
          collectFieldsByKey_executableGroupsSize_le schema variableValues
            parentType rest
        simp [collectFieldsByKey, executableGroupsSize_mergeExecutableGroups,
          SelectionSet.size]
        omega
end

mutual
  theorem collectSelectionByKey_executableGroupsBreadthWeight_le
      (schema : Schema) (variableValues : VariableValues)
      (parentType : Name) (selection : Selection)
      : executableGroupsBreadthWeight schema
          (collectSelectionByKey schema variableValues parentType selection)
        <= selectionBreadthWeight schema selection := by
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        by_cases hdirectives :
            selectionDirectivesAllowBool variableValues directives = true
        · simp [collectSelectionByKey, hdirectives, buildExecutionField,
            executableGroupsBreadthWeight, executableFieldsBreadthWeight,
            executableFieldBreadthWeight, selectionBreadthWeight]
        · simp [collectSelectionByKey, hdirectives, selectionBreadthWeight,
            executableGroupsBreadthWeight]
    | inlineFragment typeCondition directives selectionSet =>
        cases typeCondition with
        | none =>
            by_cases hdirectives :
                selectionDirectivesAllowBool variableValues directives = true
            · have hchild :=
                collectFieldsByKey_executableGroupsBreadthWeight_le
                  schema variableValues parentType selectionSet
              simpa [collectSelectionByKey, hdirectives,
                selectionBreadthWeight] using hchild
            · simp [collectSelectionByKey, hdirectives, selectionBreadthWeight,
                executableGroupsBreadthWeight]
        | some typeCondition =>
            by_cases hdirectives :
                selectionDirectivesAllowBool variableValues directives = true
            · by_cases hpossible :
                  parentTypeIsPossible schema parentType typeCondition = true
              · have hchild :=
                  collectFieldsByKey_executableGroupsBreadthWeight_le
                    schema variableValues parentType selectionSet
                simpa [collectSelectionByKey, hdirectives, hpossible,
                  selectionBreadthWeight] using hchild
              · simp [collectSelectionByKey, hdirectives, hpossible,
                  selectionBreadthWeight, executableGroupsBreadthWeight]
            · simp [collectSelectionByKey, hdirectives, selectionBreadthWeight,
                executableGroupsBreadthWeight]

  theorem collectFieldsByKey_executableGroupsBreadthWeight_le
      (schema : Schema) (variableValues : VariableValues)
      (parentType : Name) (selectionSet : List Selection)
      : executableGroupsBreadthWeight schema
          (collectFieldsByKey schema variableValues parentType selectionSet)
        <= selectionSetBreadthWeight schema selectionSet := by
    cases selectionSet with
    | nil =>
        simp [collectFieldsByKey, executableGroupsBreadthWeight,
          selectionSetBreadthWeight]
    | cons selection rest =>
        have hhead :=
          collectSelectionByKey_executableGroupsBreadthWeight_le
            schema variableValues parentType selection
        have htail :=
          collectFieldsByKey_executableGroupsBreadthWeight_le
            schema variableValues parentType rest
        simp [collectFieldsByKey,
          executableGroupsBreadthWeight_mergeExecutableGroups,
          selectionSetBreadthWeight]
        omega
end

theorem childSelectionSetForFields_size_succ_le_selectionSet_of_collectFieldsByKey_mem
    (schema : Schema) (variableValues : VariableValues)
    (parentType responseName : Name)
    (selectionSet : List Selection) (fields : List ExecutableField)
    : (responseName, fields)
        ∈ collectFieldsByKey schema variableValues parentType selectionSet
      -> fields ≠ []
      -> SelectionSet.size (childSelectionSetForFields fields) + 1
          <= SelectionSet.size selectionSet := by
  intro hmem hfields
  have hchild :=
    childSelectionSetForFields_size_succ_le_executableFieldsSize
      fields hfields
  have hfieldGroup :=
    executableFieldsSize_le_executableGroupsSize_of_mem responseName fields
      (collectFieldsByKey schema variableValues parentType selectionSet) hmem
  have hgroups :=
    collectFieldsByKey_executableGroupsSize_le schema variableValues parentType
      selectionSet
  omega

theorem pairKeysNodup_tail {α : Type} (key : Name) (value : α) (rest : List (Name × α))
    : pairKeysNodup ((key, value) :: rest) -> pairKeysNodup rest := by
  intro hnodup
  unfold pairKeysNodup at hnodup ⊢
  exact (List.nodup_cons.mp hnodup).2

theorem pairKeysNodup_head_not_mem_tail
    {α : Type} (key : Name) (value : α) (rest : List (Name × α))
    : pairKeysNodup ((key, value) :: rest) -> key ∉ rest.map Prod.fst := by
  intro hnodup
  unfold pairKeysNodup at hnodup
  exact (List.nodup_cons.mp hnodup).1

theorem mem_map_fst_addExecutableGroup
    (name : Name) (group : Name × List ExecutableField)
    (groups : List (Name × List ExecutableField))
    : name ∈ (addExecutableGroup group groups).map Prod.fst
      -> name = group.fst ∨ name ∈ groups.map Prod.fst := by
  rcases group with ⟨groupName, groupFields⟩
  induction groups with
  | nil =>
      intro hmem
      simp [addExecutableGroup] at hmem
      exact Or.inl hmem
  | cons current rest ih =>
      rcases current with ⟨currentName, currentFields⟩
      by_cases hsame : currentName == groupName
      · have hcurrent : currentName = groupName := by
          simpa using hsame
        intro hmem
        simp [addExecutableGroup, hsame] at hmem
        rcases hmem with hhead | htail
        · exact Or.inl (by simpa [hcurrent] using hhead)
        · exact Or.inr (by simp [htail])
      · intro hmem
        simp [addExecutableGroup, hsame] at hmem
        rcases hmem with hhead | htail
        · exact Or.inr (by simp [hhead])
        · rcases ih (by simpa using htail) with hgroup | hrest
          · exact Or.inl hgroup
          · exact Or.inr (by simp [hrest])

theorem pairKeysNodup_addExecutableGroup
    (group : Name × List ExecutableField)
    (groups : List (Name × List ExecutableField))
    : pairKeysNodup groups -> pairKeysNodup (addExecutableGroup group groups) := by
  rcases group with ⟨groupName, groupFields⟩
  intro hnodup
  induction groups with
  | nil =>
      simp [pairKeysNodup, addExecutableGroup]
  | cons current rest ih =>
      rcases current with ⟨currentName, currentFields⟩
      by_cases hsame : currentName == groupName
      · simpa [pairKeysNodup, addExecutableGroup, hsame] using hnodup
      · have hcurrentNe : currentName ≠ groupName := by
          intro heq
          have hbeq : (currentName == groupName) = true := by
            simp [heq]
          exact hsame hbeq
        have hrestNodup :
            pairKeysNodup rest :=
          pairKeysNodup_tail currentName currentFields rest hnodup
        have hcurrentNotRest :
            currentName ∉ rest.map Prod.fst :=
          pairKeysNodup_head_not_mem_tail currentName currentFields rest hnodup
        have htailNodup :
            pairKeysNodup
              (addExecutableGroup (groupName, groupFields) rest) :=
          ih hrestNodup
        have hcurrentNotTail :
            currentName ∉
              (addExecutableGroup (groupName, groupFields) rest).map Prod.fst := by
          intro hmem
          rcases mem_map_fst_addExecutableGroup currentName
              (groupName, groupFields) rest hmem with hgroup | hrest
          · exact hcurrentNe hgroup
          · exact hcurrentNotRest hrest
        unfold pairKeysNodup at htailNodup ⊢
        simp [addExecutableGroup, hsame, hcurrentNotTail, htailNodup]

theorem pairKeysNodup_mergeExecutableGroups
    (left right : List (Name × List ExecutableField))
    : pairKeysNodup left
      -> pairKeysNodup right
      -> pairKeysNodup (mergeExecutableGroups left right) := by
  intro hleft hright
  induction right generalizing left with
  | nil =>
      simpa [mergeExecutableGroups] using hleft
  | cons group rest ih =>
      have hrest : pairKeysNodup rest := by
        cases group with
        | mk responseName fields =>
            exact pairKeysNodup_tail responseName fields rest hright
      simpa [mergeExecutableGroups, List.foldl] using
        ih (addExecutableGroup group left)
          (pairKeysNodup_addExecutableGroup group left hleft) hrest

mutual
  theorem collectSelectionByKey_pairKeysNodup
      (schema : Schema) (variableValues : VariableValues)
      (parentType : Name) (selection : Selection)
      : pairKeysNodup
          (collectSelectionByKey schema variableValues parentType selection) := by
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        by_cases hdirectives :
            selectionDirectivesAllowBool variableValues directives = true
        · simp [collectSelectionByKey, hdirectives, pairKeysNodup,
            buildExecutionField]
        · simp [collectSelectionByKey, hdirectives, pairKeysNodup]
    | inlineFragment typeCondition directives selectionSet =>
        cases typeCondition with
        | none =>
            by_cases hdirectives :
                selectionDirectivesAllowBool variableValues directives = true
            · simpa [collectSelectionByKey, hdirectives] using
                collectFieldsByKey_pairKeysNodup schema variableValues
                  parentType selectionSet
            · simp [collectSelectionByKey, hdirectives, pairKeysNodup]
        | some typeCondition =>
            by_cases hdirectives :
                selectionDirectivesAllowBool variableValues directives = true
            · by_cases hpossible :
                  parentTypeIsPossible schema parentType typeCondition = true
              · simpa [collectSelectionByKey, hdirectives, hpossible] using
                  collectFieldsByKey_pairKeysNodup schema variableValues
                    parentType selectionSet
              · simp [collectSelectionByKey, hdirectives, hpossible,
                  pairKeysNodup]
            · simp [collectSelectionByKey, hdirectives, pairKeysNodup]

  theorem collectFieldsByKey_pairKeysNodup
      (schema : Schema) (variableValues : VariableValues)
      (parentType : Name) (selectionSet : List Selection)
      : pairKeysNodup
          (collectFieldsByKey schema variableValues parentType selectionSet) := by
    cases selectionSet with
    | nil =>
        simp [collectFieldsByKey, pairKeysNodup]
    | cons selection rest =>
        exact
          pairKeysNodup_mergeExecutableGroups
            (collectSelectionByKey schema variableValues parentType selection)
            (collectFieldsByKey schema variableValues parentType rest)
            (collectSelectionByKey_pairKeysNodup schema variableValues
              parentType selection)
            (collectFieldsByKey_pairKeysNodup schema variableValues
              parentType rest)
end

theorem parentTypeIsPossible_eq_doesFragmentTypeApplyBool_self_object
    (schema : Schema) (parentType typeCondition : Name) (ref : ObjectRef)
    : parentTypeIsPossible schema parentType typeCondition
      = doesFragmentTypeApplyBool schema parentType
          (ResolverValue.object parentType ref) typeCondition := by
  rfl

mutual
  theorem collectSelectionByKey_eq_collectSelection_self_object
      (schema : Schema) (variableValues : VariableValues)
      (parentType : Name) (ref : ObjectRef) (selection : Selection)
      : collectSelectionByKey schema variableValues parentType selection
        = GraphQL.Execution.collectSelection schema variableValues parentType
            (ResolverValue.object parentType ref) selection := by
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        simp [collectSelectionByKey, GraphQL.Execution.collectSelection,
          buildExecutionField]
    | inlineFragment typeCondition directives selectionSet =>
        cases typeCondition with
        | none =>
            by_cases hdirectives :
                selectionDirectivesAllowBool variableValues directives = true
            · have hfields :=
                collectFieldsByKey_eq_collectFields_self_object schema
                  variableValues parentType ref selectionSet
              simp [collectSelectionByKey, GraphQL.Execution.collectSelection,
                hdirectives, hfields]
            · simp [collectSelectionByKey, GraphQL.Execution.collectSelection,
                hdirectives]
        | some typeCondition =>
            by_cases hdirectives :
                selectionDirectivesAllowBool variableValues directives = true
            · by_cases hpossible :
                  schema.typeIncludesObjectBool typeCondition parentType = true
              · have hfields :=
                  collectFieldsByKey_eq_collectFields_self_object schema
                    variableValues parentType ref selectionSet
                simp [collectSelectionByKey, GraphQL.Execution.collectSelection,
                  parentTypeIsPossible, doesFragmentTypeApplyBool,
                  runtimeObjectType?, hdirectives, hpossible, hfields]
              · simp [collectSelectionByKey, GraphQL.Execution.collectSelection,
                  parentTypeIsPossible, doesFragmentTypeApplyBool,
                  runtimeObjectType?, hdirectives, hpossible]
            · simp [collectSelectionByKey, GraphQL.Execution.collectSelection,
                hdirectives]

  theorem collectFieldsByKey_eq_collectFields_self_object
      (schema : Schema) (variableValues : VariableValues)
      (parentType : Name) (ref : ObjectRef) (selectionSet : List Selection)
      : collectFieldsByKey schema variableValues parentType selectionSet
        = GraphQL.Execution.collectFields schema variableValues parentType
            (ResolverValue.object parentType ref) selectionSet := by
    cases selectionSet with
    | nil =>
        rfl
    | cons selection rest =>
        have hhead :=
          collectSelectionByKey_eq_collectSelection_self_object schema
            variableValues parentType ref selection
        have htail :=
          collectFieldsByKey_eq_collectFields_self_object schema
            variableValues parentType ref rest
        simp [collectFieldsByKey, GraphQL.Execution.collectFields, hhead,
          htail]
end

theorem collectFieldsByKey_eq_collectFields_root_source
    (schema : Schema) (operation : Operation)
    (variableValues : VariableValues)
    (source : ResolverValue ObjectRef)
    : SchemaWellFormedness.schemaWellFormed schema
      -> rootSourceAppliesBool schema operation source = true
      -> collectFieldsByKey schema variableValues (operation.rootType schema)
            operation.selectionSet
          = GraphQL.Execution.collectFields schema variableValues
              (operation.rootType schema) source operation.selectionSet := by
  intro hschema hroot
  have hrootType : (operation.rootType schema) = schema.queryType := by
    simp [Operation.rootType, OperationType.rootType]
  have hrootObject : schema.objectType (operation.rootType schema) := by
    rw [hrootType]
    exact hschema.2.1
  cases source with
  | null =>
      simp [rootSourceAppliesBool, runtimeObjectType?] at hroot
  | scalar value =>
      simp [rootSourceAppliesBool, runtimeObjectType?] at hroot
  | object runtimeType ref =>
      have hinclude :
          schema.typeIncludesObjectBool (operation.rootType schema) runtimeType = true := by
        simpa [rootSourceAppliesBool, runtimeObjectType?] using hroot
      have hruntime : runtimeType = (operation.rootType schema) :=
        object_typeIncludesObjectBool_eq_self schema hrootObject hinclude
      subst runtimeType
      exact
        collectFieldsByKey_eq_collectFields_self_object schema variableValues
          (operation.rootType schema) ref operation.selectionSet
  | list values =>
      simp [rootSourceAppliesBool, runtimeObjectType?] at hroot

mutual
  theorem collectSelectionByKey_collectedGroupsResponseName
      (schema : Schema) (variableValues : VariableValues)
      (parentType : Name) (selection : Selection)
      : collectedGroupsResponseName
          (collectSelectionByKey schema variableValues parentType selection) := by
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        by_cases hdirectives :
            selectionDirectivesAllowBool variableValues directives = true
        · intro groupResponse fields field hmem hfield
          simp [collectSelectionByKey, hdirectives, buildExecutionField] at hmem
          rcases hmem with ⟨hgroupResponse, hfields⟩
          subst groupResponse
          subst fields
          simp at hfield
          subst field
          rfl
        · simp [collectSelectionByKey, hdirectives, collectedGroupsResponseName]
    | inlineFragment typeCondition directives selectionSet =>
        cases typeCondition with
        | none =>
            by_cases hdirectives :
                selectionDirectivesAllowBool variableValues directives = true
            · simpa [collectSelectionByKey, hdirectives] using
                collectFieldsByKey_collectedGroupsResponseName schema
                  variableValues parentType selectionSet
            · simp [collectSelectionByKey, hdirectives, collectedGroupsResponseName]
        | some typeCondition =>
            by_cases hdirectives :
                selectionDirectivesAllowBool variableValues directives = true
            · by_cases hpossible :
                  parentTypeIsPossible schema parentType typeCondition = true
              · simpa [collectSelectionByKey, hdirectives, hpossible] using
                  collectFieldsByKey_collectedGroupsResponseName schema
                    variableValues parentType selectionSet
              · simp [collectSelectionByKey, hdirectives, hpossible,
                  collectedGroupsResponseName]
            · simp [collectSelectionByKey, hdirectives, collectedGroupsResponseName]

  theorem collectFieldsByKey_collectedGroupsResponseName
      (schema : Schema) (variableValues : VariableValues)
      (parentType : Name) (selectionSet : List Selection)
      : collectedGroupsResponseName
          (collectFieldsByKey schema variableValues parentType selectionSet) := by
    cases selectionSet with
    | nil =>
        simp [collectFieldsByKey, collectedGroupsResponseName]
    | cons selection rest =>
        exact
          collectedGroupsResponseName_mergeExecutableGroups
            (collectSelectionByKey schema variableValues parentType selection)
            (collectFieldsByKey schema variableValues parentType rest)
            (collectSelectionByKey_collectedGroupsResponseName schema
              variableValues parentType selection)
            (collectFieldsByKey_collectedGroupsResponseName schema
              variableValues parentType rest)
end

mutual
  theorem collectSelectionByKey_collectedGroupsNonempty
      (schema : Schema) (variableValues : VariableValues)
      (parentType : Name) (selection : Selection)
      : collectedGroupsNonempty
          (collectSelectionByKey schema variableValues parentType selection) := by
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        by_cases hdirectives :
            selectionDirectivesAllowBool variableValues directives = true
        · intro groupResponse fields hmem
          simp [collectSelectionByKey, hdirectives, buildExecutionField] at hmem
          rcases hmem with ⟨hgroupResponse, hfields⟩
          subst groupResponse
          subst fields
          simp
        · simp [collectSelectionByKey, hdirectives, collectedGroupsNonempty]
    | inlineFragment typeCondition directives selectionSet =>
        cases typeCondition with
        | none =>
            by_cases hdirectives :
                selectionDirectivesAllowBool variableValues directives = true
            · simpa [collectSelectionByKey, hdirectives] using
                collectFieldsByKey_collectedGroupsNonempty schema
                  variableValues parentType selectionSet
            · simp [collectSelectionByKey, hdirectives, collectedGroupsNonempty]
        | some typeCondition =>
            by_cases hdirectives :
                selectionDirectivesAllowBool variableValues directives = true
            · by_cases hpossible :
                  parentTypeIsPossible schema parentType typeCondition = true
              · simpa [collectSelectionByKey, hdirectives, hpossible] using
                  collectFieldsByKey_collectedGroupsNonempty schema
                    variableValues parentType selectionSet
              · simp [collectSelectionByKey, hdirectives, hpossible,
                  collectedGroupsNonempty]
            · simp [collectSelectionByKey, hdirectives, collectedGroupsNonempty]

  theorem collectFieldsByKey_collectedGroupsNonempty
      (schema : Schema) (variableValues : VariableValues)
      (parentType : Name) (selectionSet : List Selection)
      : collectedGroupsNonempty
          (collectFieldsByKey schema variableValues parentType selectionSet) := by
    cases selectionSet with
    | nil =>
        simp [collectFieldsByKey, collectedGroupsNonempty]
    | cons selection rest =>
        exact
          collectedGroupsNonempty_mergeExecutableGroups
            (collectSelectionByKey schema variableValues parentType selection)
            (collectFieldsByKey schema variableValues parentType rest)
            (collectSelectionByKey_collectedGroupsNonempty schema
              variableValues parentType selection)
            (collectFieldsByKey_collectedGroupsNonempty schema
              variableValues parentType rest)
end

theorem collectFieldsByKey_singleton_field_responseName
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (selectionSet : List Selection)
    (responseName : Name) (field : ExecutableField)
    : collectFieldsByKey schema variableValues parentType selectionSet
        = [(responseName, [field])]
      -> field.responseName = responseName := by
  intro hcollect
  have hgroups :=
    collectFieldsByKey_collectedGroupsResponseName schema variableValues
      parentType selectionSet
  exact hgroups responseName [field] field (by simp [hcollect]) (by simp)

theorem childSelectionSetForFields_nil
    : childSelectionSetForFields ([] : List ExecutableField) = [] := by
  rfl

theorem childSelectionSetForFields_eq_mergedFieldSelectionSet
    (fields : List ExecutableField)
    : childSelectionSetForFields fields
      = GraphQL.Execution.mergedFieldSelectionSet fields := by
  induction fields with
  | nil =>
      rfl
  | cons field rest ih =>
      simp [childSelectionSetForFields, GraphQL.Execution.mergedFieldSelectionSet,
        ← ih]

theorem childSelectionSetForFields_append (left right : List ExecutableField)
    : childSelectionSetForFields (left ++ right)
      = childSelectionSetForFields left ++ childSelectionSetForFields right := by
  induction left generalizing right with
  | nil =>
      simp [childSelectionSetForFields]
  | cons field rest ih =>
      simp [childSelectionSetForFields, List.append_assoc]

theorem collectFieldsByKey_childSelectionSetForFields_eq_collectSubfields_self_object
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (ref : ObjectRef) (fields : List ExecutableField)
    : collectFieldsByKey schema variableValues parentType
        (childSelectionSetForFields fields)
      = GraphQL.Execution.collectSubfields schema variableValues parentType
          (ResolverValue.object parentType ref) fields := by
  rw [childSelectionSetForFields_eq_mergedFieldSelectionSet,
    GraphQL.NormalForm.collectSubfields_eq_collectFields_mergedFieldSelectionSet]
  exact collectFieldsByKey_eq_collectFields_self_object schema variableValues
    parentType ref (GraphQL.Execution.mergedFieldSelectionSet fields)

theorem collectSubfields_singleton_executableField_childSelectionSetForFields_eq
    (schema : Schema) (variableValues : VariableValues)
    (runtimeType : Name) (ref : ObjectRef)
    (key : ScheduleKey) (fields : List ExecutableField)
    : GraphQL.Execution.collectSubfields schema variableValues runtimeType
        (ResolverValue.object runtimeType ref)
        [key.executableField (childSelectionSetForFields fields)]
      = GraphQL.Execution.collectSubfields schema variableValues runtimeType
          (ResolverValue.object runtimeType ref) fields := by
  have hself :=
    collectFieldsByKey_eq_collectFields_self_object schema variableValues
      runtimeType ref (childSelectionSetForFields fields)
  have hfields :=
    collectFieldsByKey_childSelectionSetForFields_eq_collectSubfields_self_object
      schema variableValues runtimeType ref fields
  calc
    GraphQL.Execution.collectSubfields schema variableValues runtimeType
          (ResolverValue.object runtimeType ref)
          [key.executableField (childSelectionSetForFields fields)]
        = GraphQL.Execution.collectFields schema variableValues runtimeType
            (ResolverValue.object runtimeType ref)
            (childSelectionSetForFields fields) := by
      simp [GraphQL.Execution.collectSubfields,
        GraphQL.Execution.mergeExecutableGroups, ScheduleKey.executableField]
    _ = collectFieldsByKey schema variableValues runtimeType
          (childSelectionSetForFields fields) := by
      rw [hself]
    _ = GraphQL.Execution.collectSubfields schema variableValues runtimeType
          (ResolverValue.object runtimeType ref) fields :=
      hfields

theorem completeValue_singleton_executableField_childSelectionSetForFields_eq
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (fuel : Nat) (fieldType : TypeRef)
    (key : ScheduleKey) (fields : List ExecutableField)
    (value : ResolverValue ObjectRef)
    : GraphQL.Execution.completeValue schema resolvers variableValues fuel fieldType
        [key.executableField (childSelectionSetForFields fields)] value
      = GraphQL.Execution.completeValue schema resolvers variableValues fuel fieldType
          fields value := by
  induction fieldType generalizing fuel value with
  | named typeName =>
      cases fuel with
      | zero =>
          simp [GraphQL.Execution.completeValue]
      | succ fuel =>
          cases value with
          | null =>
              simp [GraphQL.Execution.completeValue]
          | scalar scalarValue =>
              simp [GraphQL.Execution.completeValue]
          | object runtimeType ref =>
              by_cases hincludes : schema.typeIncludesObjectBool typeName runtimeType
              · simp [GraphQL.Execution.completeValue, hincludes,
                  childSelectionSetForFields_eq_mergedFieldSelectionSet,
                  ScheduleKey.executableField]
              · simp [GraphQL.Execution.completeValue, hincludes]
          | list values =>
              simp [GraphQL.Execution.completeValue]
  | list inner ih =>
      cases fuel with
      | zero =>
          simp [GraphQL.Execution.completeValue]
      | succ fuel =>
          cases value with
          | null =>
              simp [GraphQL.Execution.completeValue]
          | scalar scalarValue =>
              simp [GraphQL.Execution.completeValue]
          | object runtimeType ref =>
              simp [GraphQL.Execution.completeValue]
          | list values =>
              have hlist :
                  GraphQL.Execution.completeValueList schema resolvers variableValues fuel
                      inner [key.executableField (childSelectionSetForFields fields)] values =
                    GraphQL.Execution.completeValueList schema resolvers variableValues fuel
                      inner fields values := by
                induction values with
                | nil =>
                    simp [GraphQL.Execution.completeValueList]
                | cons value values ihValues =>
                    simp [GraphQL.Execution.completeValueList, ih, ihValues]
              simp [GraphQL.Execution.completeValue, hlist]
  | nonNull inner ih =>
      cases fuel with
      | zero =>
          simp [GraphQL.Execution.completeValue]
      | succ fuel =>
          simp [GraphQL.Execution.completeValue, ih]

theorem executeField_singleton_scheduleKeyForFields_childSelectionSetForFields_eq
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (fuel : Nat) (source : ResolverValue ObjectRef)
    (responseName : Name)
    (field : ExecutableField) (fields : List ExecutableField)
    : GraphQL.Execution.executeField schema resolvers variableValues fuel source
        responseName
        [(scheduleKeyForFields field.parentType responseName
            (field :: fields)).executableField
          (childSelectionSetForFields (field :: fields))]
      = GraphQL.Execution.executeField schema resolvers variableValues fuel source
          responseName (field :: fields) := by
  cases fuel with
  | zero =>
      simp [GraphQL.Execution.executeField]
  | succ fuel =>
      cases hlookup : schema.lookupField field.parentType field.fieldName with
      | none =>
          simp [GraphQL.Execution.executeField, hlookup, scheduleKeyForFields,
            ScheduleKey.executableField]
      | some fieldDefinition =>
          cases hresolve
                : resolvers.resolve field.parentType field.fieldName
                    (coerceArgumentValues schema variableValues
                      fieldDefinition.arguments field.arguments) source with
          | none =>
              simp [GraphQL.Execution.executeField, GraphQL.Execution.resolveFieldValue,
                hlookup, hresolve,
                scheduleKeyForFields, ScheduleKey.executableField]
          | some resolved =>
              simp [GraphQL.Execution.executeField, GraphQL.Execution.resolveFieldValue,
                hlookup, hresolve,
                scheduleKeyForFields, ScheduleKey.executableField]
              exact congrArg (GraphQL.Execution.singleFieldResult responseName)
                (completeValue_singleton_executableField_childSelectionSetForFields_eq
                  (ObjectRef := ObjectRef) schema resolvers variableValues fuel
                  fieldDefinition.outputType
                  (scheduleKeyForFields field.parentType responseName (field :: fields))
                  (field :: fields) resolved)

theorem collectFields_empty_of_childSelectionSetForFields_empty
    (schema : Schema) (variableValues : VariableValues)
    (runtimeType : Name) (ref : ObjectRef)
    (field : ExecutableField) (fields : List ExecutableField)
    : childSelectionSetForFields (field :: fields) = []
      -> GraphQL.Execution.collectFields schema variableValues runtimeType
            (ResolverValue.object runtimeType ref)
            (field.selectionSet ++ GraphQL.Execution.mergedFieldSelectionSet fields)
          = [] := by
  intro hselectionSet
  have hmerged :
      GraphQL.Execution.mergedFieldSelectionSet (field :: fields) = [] := by
    rw [← childSelectionSetForFields_eq_mergedFieldSelectionSet]
    exact hselectionSet
  have hsubfields :
      GraphQL.Execution.collectSubfields schema variableValues runtimeType
          (ResolverValue.object runtimeType ref) (field :: fields) = [] := by
    rw [GraphQL.NormalForm.collectSubfields_eq_collectFields_mergedFieldSelectionSet,
      hmerged]
    rfl
  have hcollectMerged :
      GraphQL.Execution.collectFields schema variableValues runtimeType
          (ResolverValue.object runtimeType ref)
          (GraphQL.Execution.mergedFieldSelectionSet (field :: fields)) =
        [] := by
    rw [← GraphQL.NormalForm.collectSubfields_eq_collectFields_mergedFieldSelectionSet]
    exact hsubfields
  simpa [GraphQL.Execution.mergedFieldSelectionSet] using hcollectMerged

theorem collectFields_cons_merged_eq_of_childSelectionSetForFields_groups
    (schema : Schema) (variableValues : VariableValues)
    (runtimeType : Name) (ref : ObjectRef)
    (field : ExecutableField) (fields : List ExecutableField)
    (groups : List (Name × List ExecutableField))
    : collectFieldsByKey schema variableValues runtimeType
          (childSelectionSetForFields (field :: fields))
        = groups
      -> GraphQL.Execution.collectFields schema variableValues runtimeType
            (ResolverValue.object runtimeType ref)
            (field.selectionSet ++ GraphQL.Execution.mergedFieldSelectionSet fields)
          = groups := by
  intro hgroups
  have hsubfields :
      GraphQL.Execution.collectSubfields schema variableValues runtimeType
          (ResolverValue.object runtimeType ref) (field :: fields) = groups := by
    rw [← collectFieldsByKey_childSelectionSetForFields_eq_collectSubfields_self_object
      schema variableValues runtimeType ref (field :: fields)]
    exact hgroups
  have h := hsubfields
  rw [GraphQL.NormalForm.collectSubfields_eq_collectFields_mergedFieldSelectionSet] at h
  simpa [GraphQL.Execution.mergedFieldSelectionSet] using h

end ExecutionBreadth

end Algorithms

end GraphQL
