import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Equivalence.Core
import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Equivalence.Validation
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Validity.Support.FieldHeads
import Proofs.GraphQL.Theories.NormalForm.Shared.LookupValidity
import Proofs.GraphQL.Theories.NormalForm.Shared.SemanticReadiness
import Proofs.GraphQL.Execution.Data

namespace GraphQL

namespace Algorithms
namespace ExecutionUngrouped

open GraphQL.Execution

def collectedExecutableFields : List (Name × List ExecutableField) -> List ExecutableField
  | [] => []
  | (_responseName, fields) :: rest =>
      fields ++ collectedExecutableFields rest

theorem collectedExecutableFields_append (left right : List (Name × List ExecutableField))
    : collectedExecutableFields (left ++ right)
      = collectedExecutableFields left ++ collectedExecutableFields right := by
  induction left with
  | nil =>
      simp [collectedExecutableFields]
  | cons group rest ih =>
      rcases group with ⟨responseName, fields⟩
      simp [collectedExecutableFields, ih, List.append_assoc]

theorem collectedExecutableFields_addExecutableGroup_length
    (group : Name × List ExecutableField)
    (groups : List (Name × List ExecutableField))
    : (collectedExecutableFields
        (GraphQL.Execution.addExecutableGroup group groups)).length
      = group.snd.length + (collectedExecutableFields groups).length := by
  rcases group with ⟨groupName, groupFields⟩
  induction groups with
  | nil =>
      simp [collectedExecutableFields, GraphQL.Execution.addExecutableGroup]
  | cons current rest ih =>
      rcases current with ⟨currentName, currentFields⟩
      by_cases hname : (currentName == groupName) = true
      · simp [collectedExecutableFields, GraphQL.Execution.addExecutableGroup,
          hname, List.length_append]
        omega
      · have hfalse : (currentName == groupName) = false := by
          cases hmatch : currentName == groupName
          · rfl
          · contradiction
        simp [collectedExecutableFields, GraphQL.Execution.addExecutableGroup,
          hfalse, ih, List.length_append]
        omega

theorem collectedExecutableFields_mergeExecutableGroups_length
    (left right : List (Name × List ExecutableField))
    : (collectedExecutableFields
        (GraphQL.Execution.mergeExecutableGroups left right)).length
      = (collectedExecutableFields left).length
        + (collectedExecutableFields right).length := by
  induction right generalizing left with
  | nil =>
      simp [collectedExecutableFields, GraphQL.Execution.mergeExecutableGroups]
  | cons group rest ih =>
      rcases group with ⟨responseName, fields⟩
      change
        (collectedExecutableFields
          (GraphQL.Execution.mergeExecutableGroups
            (GraphQL.Execution.addExecutableGroup (responseName, fields) left)
            rest)).length =
          (collectedExecutableFields left).length +
            (fields ++ collectedExecutableFields rest).length
      rw [ih]
      rw [collectedExecutableFields_addExecutableGroup_length]
      simp [List.length_append]
      omega

theorem addExecutableGroup_key_mem
    (group : Name × List ExecutableField)
    (groups : List (Name × List ExecutableField)) (responseName : Name)
    : responseName ∈ (GraphQL.Execution.addExecutableGroup group groups).map Prod.fst
      ↔ responseName = group.fst ∨ responseName ∈ groups.map Prod.fst := by
  rcases group with ⟨groupName, groupFields⟩
  induction groups with
  | nil =>
      simp [GraphQL.Execution.addExecutableGroup]
  | cons current rest ih =>
      rcases current with ⟨currentName, currentFields⟩
      by_cases hname : (currentName == groupName) = true
      · have hcurrent : currentName = groupName := beq_iff_eq.mp hname
        simp [GraphQL.Execution.addExecutableGroup, hcurrent]
      · have hfalse : (currentName == groupName) = false := by
          cases h : currentName == groupName
          · rfl
          · contradiction
        simp [GraphQL.Execution.addExecutableGroup, hfalse, ih]
        constructor
        · intro hmem
          rcases hmem with hcurrent | hgroupOrRest
          · exact Or.inr (by simp [hcurrent])
          · rcases hgroupOrRest with hgroup | hrest
            · exact Or.inl hgroup
            · exact Or.inr (by simp [hrest])
        · intro hmem
          rcases hmem with hgroup | hcurrentOrRest
          · exact Or.inr (Or.inl hgroup)
          · rcases hcurrentOrRest with hcurrent | hrest
            · exact Or.inl hcurrent
            · exact Or.inr (Or.inr hrest)

theorem mergeExecutableGroups_key_mem
    (left right : List (Name × List ExecutableField)) (responseName : Name)
    : responseName ∈ (GraphQL.Execution.mergeExecutableGroups left right).map Prod.fst
      ↔ responseName ∈ left.map Prod.fst ∨ responseName ∈ right.map Prod.fst := by
  induction right generalizing left with
  | nil =>
      simp [GraphQL.Execution.mergeExecutableGroups]
  | cons group rest ih =>
      change
        responseName ∈
            (GraphQL.Execution.mergeExecutableGroups
              (GraphQL.Execution.addExecutableGroup group left) rest).map
              Prod.fst ↔
          responseName ∈ left.map Prod.fst ∨
            responseName ∈ (group :: rest).map Prod.fst
      rw [ih]
      rw [addExecutableGroup_key_mem group left responseName]
      simp only [List.map_cons, List.mem_cons]
      constructor
      · intro hmem
        rcases hmem with hgroupOrLeft | hrest
        · rcases hgroupOrLeft with hgroup | hleft
          · exact Or.inr (Or.inl hgroup)
          · exact Or.inl hleft
        · exact Or.inr (Or.inr hrest)
      · intro hmem
        rcases hmem with hleft | hgroupOrRest
        · exact Or.inl (Or.inr hleft)
        · rcases hgroupOrRest with hgroup | hrest
          · exact Or.inl (Or.inl hgroup)
          · exact Or.inr hrest

theorem collectedExecutableFields_mergeExecutableGroups_eq_append_of_namesDisjoint
    (left right : List (Name × List ExecutableField))
    : GraphQL.NormalForm.executableGroupNamesDisjoint left right
      -> GraphQL.NormalForm.executableGroupNamesNodup right
      -> collectedExecutableFields (GraphQL.Execution.mergeExecutableGroups left right)
          = collectedExecutableFields left ++ collectedExecutableFields right := by
  intro hdisjoint hnodup
  rw [GraphQL.NormalForm.mergeExecutableGroups_eq_append_of_namesDisjoint
    left right hdisjoint hnodup]
  exact collectedExecutableFields_append left right

theorem collectedExecutableFields_merge_single_duplicate_around_disjoint
    (responseName : Name) (first later : ExecutableField)
    (middleGroups : List (Name × List ExecutableField))
    : responseName ∉ middleGroups.map Prod.fst
      -> GraphQL.NormalForm.executableGroupNamesNodup middleGroups
      -> collectedExecutableFields
            (GraphQL.Execution.mergeExecutableGroups
              [(responseName, [first])]
              (middleGroups ++ [(responseName, [later])]))
          = [first, later] ++ collectedExecutableFields middleGroups := by
  intro hnotMiddle hmiddleNodup
  have hdisjoint :
      GraphQL.NormalForm.executableGroupNamesDisjoint
        [(responseName, [first])] middleGroups := by
    intro candidate hleft hright
    simp at hleft
    exact hnotMiddle (by simpa [hleft] using hright)
  unfold GraphQL.Execution.mergeExecutableGroups
  rw [List.foldl_append]
  change
    collectedExecutableFields
        (GraphQL.Execution.addExecutableGroup (responseName, [later])
          (GraphQL.Execution.mergeExecutableGroups [(responseName, [first])]
            middleGroups)) =
      [first, later] ++ collectedExecutableFields middleGroups
  rw [GraphQL.NormalForm.mergeExecutableGroups_eq_append_of_namesDisjoint
    [(responseName, [first])] middleGroups hdisjoint hmiddleNodup]
  simp [GraphQL.Execution.addExecutableGroup, collectedExecutableFields]

theorem collectedExecutableFields_merge_group_duplicate_around_disjoint
    (responseName : Name) (prefixFields : List ExecutableField)
    (later : ExecutableField)
    (middleGroups : List (Name × List ExecutableField))
    : responseName ∉ middleGroups.map Prod.fst
      -> GraphQL.NormalForm.executableGroupNamesNodup middleGroups
      -> collectedExecutableFields
            (GraphQL.Execution.mergeExecutableGroups
              [(responseName, prefixFields)]
              (middleGroups ++ [(responseName, [later])]))
          = (prefixFields ++ [later]) ++ collectedExecutableFields middleGroups := by
  intro hnotMiddle hmiddleNodup
  have hdisjoint :
      GraphQL.NormalForm.executableGroupNamesDisjoint
        [(responseName, prefixFields)] middleGroups := by
    intro candidate hleft hright
    simp at hleft
    exact hnotMiddle (by simpa [hleft] using hright)
  unfold GraphQL.Execution.mergeExecutableGroups
  rw [List.foldl_append]
  change
    collectedExecutableFields
        (GraphQL.Execution.addExecutableGroup (responseName, [later])
          (GraphQL.Execution.mergeExecutableGroups [(responseName, prefixFields)]
            middleGroups)) =
      (prefixFields ++ [later]) ++ collectedExecutableFields middleGroups
  rw [GraphQL.NormalForm.mergeExecutableGroups_eq_append_of_namesDisjoint
    [(responseName, prefixFields)] middleGroups hdisjoint hmiddleNodup]
  simp [GraphQL.Execution.addExecutableGroup, collectedExecutableFields,
    List.append_assoc]

theorem
    executableFieldSelections_collectedExecutableFields_collectFields_duplicate_around_disjoint
    {ObjectIdentity : Type} (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (first later : ExecutableField) (middle : List Selection)
    : later.responseName = first.responseName
      -> first.responseName
          ∉ (GraphQL.Execution.collectFields schema variableValues parentType source
              middle).map
              Prod.fst
      -> executableFieldSelections
            (collectedExecutableFields
              (GraphQL.Execution.collectFields schema variableValues parentType
                source
                (executableFieldSelections [first]
                  ++ middle
                  ++ executableFieldSelections [later])))
          = executableFieldSelections [first, later]
            ++ executableFieldSelections
                (collectedExecutableFields
                  (GraphQL.Execution.collectFields schema variableValues parentType
                    source middle)) := by
  intro hsame hnotMiddle
  let firstCollected : ExecutableField :=
    executableField parentType first.responseName first.fieldName
      first.arguments first.selectionSet
  let laterCollected : ExecutableField :=
    executableField parentType later.responseName later.fieldName
      later.arguments later.selectionSet
  let middleGroups :=
    GraphQL.Execution.collectFields schema variableValues parentType source
      middle
  have hfirstCollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
        (executableFieldSelections [first]) =
      [(first.responseName, [firstCollected])] := by
    simp [executableFieldSelections, executableFieldSelection, firstCollected,
      executableField, GraphQL.Execution.collectFields,
      GraphQL.Execution.collectSelection, GraphQL.Execution.mergeExecutableGroups,
      selectionDirectivesAllowBool_empty]
  have hlaterCollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
        (executableFieldSelections [later]) =
      [(later.responseName, [laterCollected])] := by
    simp [executableFieldSelections, executableFieldSelection, laterCollected,
      executableField, GraphQL.Execution.collectFields,
      GraphQL.Execution.collectSelection, GraphQL.Execution.mergeExecutableGroups,
      selectionDirectivesAllowBool_empty]
  have hmiddleLater :
      GraphQL.Execution.collectFields schema variableValues parentType source
          (middle ++ executableFieldSelections [later]) =
        middleGroups ++ [(later.responseName, [laterCollected])] := by
    rw [GraphQL.NormalForm.collectFields_append]
    rw [hlaterCollect]
    have hdisjoint :
        GraphQL.NormalForm.executableGroupNamesDisjoint middleGroups
          [(later.responseName, [laterCollected])] := by
      intro responseName hmiddle hsingle
      simp at hsingle
      exact hnotMiddle (by simpa [middleGroups, hsingle, hsame] using hmiddle)
    rw [GraphQL.NormalForm.mergeExecutableGroups_eq_append_of_namesDisjoint
      middleGroups [(later.responseName, [laterCollected])] hdisjoint
      (by simp [GraphQL.NormalForm.executableGroupNamesNodup])]
  rw [show
      executableFieldSelections [first] ++ middle ++
          executableFieldSelections [later] =
        executableFieldSelections [first] ++
          (middle ++ executableFieldSelections [later]) by
    simp [List.append_assoc]]
  rw [GraphQL.NormalForm.collectFields_append]
  rw [hfirstCollect, hmiddleLater]
  have hmiddleNodup :
      GraphQL.NormalForm.executableGroupNamesNodup middleGroups := by
    exact GraphQL.NormalForm.collectFields_namesNodup schema variableValues
      parentType source middle
  have hnotMiddle' :
      first.responseName ∉ middleGroups.map Prod.fst := by
    simpa [middleGroups] using hnotMiddle
  rw [hsame]
  rw [collectedExecutableFields_merge_single_duplicate_around_disjoint
    first.responseName firstCollected laterCollected middleGroups hnotMiddle'
    hmiddleNodup]
  simp [executableFieldSelections, executableFieldSelection, firstCollected,
    laterCollected, executableField, middleGroups, hsame]

theorem
    executableFieldSelections_collectedExecutableFields_collectFields_group_duplicate_around_disjoint
    {ObjectIdentity : Type} (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity) (responseName : Name)
    (prefixFields : List ExecutableField) (later : ExecutableField)
    (middle : List Selection)
    : prefixFields ≠ []
      -> (∀ field, field ∈ prefixFields -> field.responseName = responseName)
      -> later.responseName = responseName
      -> responseName
          ∉ (GraphQL.Execution.collectFields schema variableValues parentType source
              middle).map
              Prod.fst
      -> executableFieldSelections
            (collectedExecutableFields
              (GraphQL.Execution.collectFields schema variableValues parentType
                source
                (executableFieldSelections prefixFields
                  ++ middle
                  ++ executableFieldSelections [later])))
          = executableFieldSelections (prefixFields ++ [later])
            ++ executableFieldSelections
                (collectedExecutableFields
                  (GraphQL.Execution.collectFields schema variableValues parentType
                    source middle)) := by
  intro hprefixNonempty hprefixResponse hlaterResponse hnotMiddle
  cases prefixFields with
  | nil =>
      exact False.elim (hprefixNonempty rfl)
  | cons firstPrefix restPrefix =>
      let collectedField : ExecutableField -> ExecutableField :=
        fun field =>
          executableField parentType field.responseName field.fieldName
            field.arguments field.selectionSet
      let collectedPrefix : List ExecutableField :=
        (firstPrefix :: restPrefix).map collectedField
      let laterCollected : ExecutableField :=
        executableField parentType later.responseName later.fieldName
          later.arguments later.selectionSet
      let middleGroups :=
        GraphQL.Execution.collectFields schema variableValues parentType source
          middle
      have hprefixSelections :
          executableFieldSelections collectedPrefix =
            executableFieldSelections (firstPrefix :: restPrefix) := by
        simp [collectedPrefix, collectedField, executableFieldSelections,
          executableFieldSelection, executableField, List.map_map]
      have hcollectedPrefixResponse :
          ∀ field, field ∈ collectedPrefix ->
            field.responseName = responseName := by
        intro field hfield
        rcases List.mem_map.mp hfield with ⟨sourceField, hsource, hfieldEq⟩
        subst field
        exact hprefixResponse sourceField hsource
      have hcollectedPrefixParent :
          ∀ field, field ∈ collectedPrefix -> field.parentType = parentType := by
        intro field hfield
        rcases List.mem_map.mp hfield with ⟨sourceField, _hsource, hfieldEq⟩
        subst field
        rfl
      have hprefixCollect :
          GraphQL.Execution.collectFields schema variableValues parentType source
              (executableFieldSelections (firstPrefix :: restPrefix)) =
            [(responseName, collectedPrefix)] := by
        rw [← hprefixSelections]
        simpa [collectedPrefix] using
          collectFields_executableFieldSelections_same_group schema
            variableValues parentType source responseName collectedPrefix
            hcollectedPrefixResponse hcollectedPrefixParent
      have hlaterCollect :
          GraphQL.Execution.collectFields schema variableValues parentType source
            (executableFieldSelections [later]) =
          [(later.responseName, [laterCollected])] := by
        simp [executableFieldSelections, executableFieldSelection,
          laterCollected, executableField, GraphQL.Execution.collectFields,
          GraphQL.Execution.collectSelection,
          GraphQL.Execution.mergeExecutableGroups,
          selectionDirectivesAllowBool_empty]
      have hmiddleLater :
          GraphQL.Execution.collectFields schema variableValues parentType source
              (middle ++ executableFieldSelections [later]) =
            middleGroups ++ [(later.responseName, [laterCollected])] := by
        rw [GraphQL.NormalForm.collectFields_append]
        rw [hlaterCollect]
        have hdisjoint :
            GraphQL.NormalForm.executableGroupNamesDisjoint middleGroups
              [(later.responseName, [laterCollected])] := by
          intro candidate hmiddle hsingle
          simp at hsingle
          exact hnotMiddle (by
            simpa [middleGroups, hsingle, hlaterResponse] using hmiddle)
        rw [GraphQL.NormalForm.mergeExecutableGroups_eq_append_of_namesDisjoint
          middleGroups [(later.responseName, [laterCollected])] hdisjoint
          (by simp [GraphQL.NormalForm.executableGroupNamesNodup])]
      rw [show
          executableFieldSelections (firstPrefix :: restPrefix) ++ middle ++
              executableFieldSelections [later] =
            executableFieldSelections (firstPrefix :: restPrefix) ++
              (middle ++ executableFieldSelections [later]) by
        simp [List.append_assoc]]
      rw [GraphQL.NormalForm.collectFields_append]
      rw [hprefixCollect, hmiddleLater]
      have hmiddleNodup :
          GraphQL.NormalForm.executableGroupNamesNodup middleGroups := by
        exact GraphQL.NormalForm.collectFields_namesNodup schema variableValues
          parentType source middle
      have hnotMiddle' :
          responseName ∉ middleGroups.map Prod.fst := by
        simpa [middleGroups] using hnotMiddle
      rw [hlaterResponse]
      rw [collectedExecutableFields_merge_group_duplicate_around_disjoint
        responseName collectedPrefix laterCollected middleGroups hnotMiddle'
        hmiddleNodup]
      simp [executableFieldSelections, executableFieldSelection,
        collectedPrefix, collectedField, laterCollected, executableField,
        middleGroups, hlaterResponse, List.map_map, List.append_assoc]

theorem collectFields_executableFieldSelections_collectedExecutableFields
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    : PairKeysNodup groups
      -> CollectedGroupsFieldsNonempty groups
      -> CollectedGroupsResponseName groups
      -> CollectedGroupsParent parentType groups
      -> GraphQL.Execution.collectFields schema variableValues parentType source
            (executableFieldSelections (collectedExecutableFields groups))
          = groups := by
  induction groups with
  | nil =>
      intro _hnodup _hnonempty _hresponse _hparent
      simp [collectedExecutableFields, executableFieldSelections,
        GraphQL.Execution.collectFields]
  | cons group rest ih =>
      rcases group with ⟨responseName, fields⟩
      intro hnodup hnonempty hresponse hparent
      have hrestNodup : PairKeysNodup rest :=
        PairKeysNodup.tail hnodup
      have hfieldsNonempty : fields ≠ [] :=
        hnonempty responseName fields (by simp)
      have hfieldsResponse :
          ExecutableFieldsResponseName responseName fields :=
        hresponse responseName fields (by simp)
      have hfieldsParent :
          ExecutableFieldsParent parentType fields :=
        hparent responseName fields (by simp)
      have hrestResponse : CollectedGroupsResponseName rest :=
        CollectedGroupsResponseName_tail hresponse
      have hrestParent : CollectedGroupsParent parentType rest :=
        CollectedGroupsParent_tail hparent
      have hrestNonempty : CollectedGroupsFieldsNonempty rest := by
        intro restResponseName restFields hmem
        exact hnonempty restResponseName restFields (by simp [hmem])
      cases fields with
      | nil =>
          exact False.elim (hfieldsNonempty rfl)
      | cons field fieldsTail =>
          rw [show
              executableFieldSelections
                  (collectedExecutableFields
                    ((responseName, field :: fieldsTail) :: rest)) =
                executableFieldSelections (field :: fieldsTail) ++
                  executableFieldSelections (collectedExecutableFields rest) by
            simp [collectedExecutableFields, executableFieldSelections]]
          rw [GraphQL.NormalForm.collectFields_append]
          rw [collectFields_executableFieldSelections_same_group schema
            variableValues parentType source responseName (field :: fieldsTail)
            hfieldsResponse hfieldsParent]
          rw [ih hrestNodup hrestNonempty hrestResponse hrestParent]
          have hdisjoint :
              GraphQL.NormalForm.executableGroupNamesDisjoint
                [(responseName, field :: fieldsTail)] rest := by
            exact executableGroupNamesDisjoint_singleton_tail_of_pairKeysNodup
              hnodup
          have hrestNamesNodup :
              GraphQL.NormalForm.executableGroupNamesNodup rest :=
            executableGroupNamesNodup_of_pairKeysNodup rest hrestNodup
          rw [GraphQL.NormalForm.mergeExecutableGroups_eq_append_of_namesDisjoint
            [(responseName, field :: fieldsTail)] rest hdisjoint
            hrestNamesNodup]
          simp

theorem collectFields_executableFieldSelections_collectedExecutableFields_collectFields
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    : GraphQL.Execution.collectFields schema variableValues parentType source
        (executableFieldSelections
          (collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source selectionSet)))
      = GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet := by
  apply collectFields_executableFieldSelections_collectedExecutableFields
  · exact PairKeysNodup_of_executableGroupNamesNodup
      (GraphQL.Execution.collectFields schema variableValues parentType source
        selectionSet)
      (GraphQL.NormalForm.collectFields_namesNodup schema variableValues
        parentType source selectionSet)
  · exact collectFields_fieldsNonempty schema variableValues parentType source
      selectionSet
  · exact collectFields_responseName schema variableValues parentType source
      selectionSet
  · exact collectFields_parent schema variableValues parentType source
      selectionSet

theorem collectedExecutableFields_collectFields_executableFieldSelections_length
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (fields : List ExecutableField)
    : (collectedExecutableFields
        (GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections fields))).length
      = fields.length := by
  induction fields with
  | nil =>
      simp [executableFieldSelections, GraphQL.Execution.collectFields,
        collectedExecutableFields]
  | cons field rest ih =>
      have hhead :
          GraphQL.Execution.collectSelection schema variableValues parentType
              source (executableFieldSelection field) =
            [(field.responseName,
              [executableField parentType field.responseName field.fieldName
                field.arguments field.selectionSet])] := by
        simp [executableFieldSelection, executableField,
          GraphQL.Execution.collectSelection, selectionDirectivesAllowBool_empty]
      simp only [executableFieldSelections, List.map_cons,
        GraphQL.Execution.collectFields]
      rw [hhead]
      rw [collectedExecutableFields_mergeExecutableGroups_length]
      simp [collectedExecutableFields]
      rw [show
          List.map executableFieldSelection rest =
            executableFieldSelections rest by
        rfl]
      rw [ih]
      omega

theorem specExecuteRootSelectionSet_executableFieldSelections_collectedExecutableFields
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    : PairKeysNodup groups
      -> CollectedGroupsFieldsNonempty groups
      -> CollectedGroupsResponseName groups
      -> CollectedGroupsParent parentType groups
      -> GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
            depth parentType source
            (executableFieldSelections (collectedExecutableFields groups))
          = GraphQL.Execution.executeCollectedFields schema resolvers variableValues
              depth source groups := by
  intro hnodup hnonempty hresponse hparent
  simp [GraphQL.Execution.executeRootSelectionSet,
    collectFields_executableFieldSelections_collectedExecutableFields schema
      variableValues parentType source groups hnodup hnonempty hresponse
      hparent]

theorem
    specExecuteRootSelectionSet_executableFieldSelections_collectedExecutableFields_collectFields
    {ObjectIdentity : Type} (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat) (parentType : Name)
    (source : ResolverValue ObjectIdentity) (selectionSet : List Selection)
    : GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        depth parentType source
        (executableFieldSelections
          (collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source selectionSet)))
      = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          depth parentType source selectionSet := by
  simp [GraphQL.Execution.executeRootSelectionSet,
    collectFields_executableFieldSelections_collectedExecutableFields_collectFields
      schema variableValues parentType source selectionSet]

theorem executeRootSelectionSet_eq_spec_of_flattened_collectFields_eq
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    (hflat
      : executeRootSelectionSet schema resolvers variableValues depth parentType
          source selectionSet
        = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
            depth parentType source
            (executableFieldSelections
              (collectedExecutableFields
                (GraphQL.Execution.collectFields schema variableValues parentType
                  source selectionSet))))
    : executeRootSelectionSet schema resolvers variableValues depth parentType
        source selectionSet
      = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          depth parentType source selectionSet :=
  hflat.trans
    (specExecuteRootSelectionSet_executableFieldSelections_collectedExecutableFields_collectFields
      schema resolvers variableValues depth parentType source selectionSet)

theorem collectedExecutableFields_mem_of_group_mem
    {groups : List (Name × List ExecutableField)}
    {responseName : Name} {fields : List ExecutableField}
    {field : ExecutableField}
    : (responseName, fields) ∈ groups
      -> field ∈ fields
      -> field ∈ collectedExecutableFields groups := by
  intro hgroup hfield
  induction groups with
  | nil =>
      simp at hgroup
  | cons group rest ih =>
      rcases group with ⟨groupResponseName, groupFields⟩
      simp [collectedExecutableFields] at hgroup ⊢
      rcases hgroup with hhead | htail
      · rcases hhead with ⟨_hresponseName, hfields⟩
        cases hfields
        exact Or.inl hfield
      · exact Or.inr (ih htail)

theorem CollectedGroupsFieldValidationMergeCompatible.of_collectedExecutableFields
    (groups : List (Name × List ExecutableField))
    : ExecutableFieldsFieldValidationMergeCompatible (collectedExecutableFields groups)
      -> CollectedGroupsFieldValidationMergeCompatible groups := by
  intro hflat responseName fields hgroup first later hfirst hlater hresponse
  exact hflat first later
    (collectedExecutableFields_mem_of_group_mem hgroup hfirst)
    (collectedExecutableFields_mem_of_group_mem hgroup hlater)
    hresponse

theorem CollectedGroupsValidationMergeCompatible.of_collectedExecutableFields
    (groups : List (Name × List ExecutableField))
    : ExecutableFieldsSameParentValidationMergeCompatible
        (collectedExecutableFields groups)
      -> CollectedGroupsValidationMergeCompatible groups := by
  intro hflat responseName fields hgroup first later hfirst hlater hresponse
    hparent
  exact hflat first later
    (collectedExecutableFields_mem_of_group_mem hgroup hfirst)
    (collectedExecutableFields_mem_of_group_mem hgroup hlater)
    hresponse hparent

theorem ExecutableFieldsFieldValidationMergeCompatible.mono
    (source target : List ExecutableField)
    : (∀ field, field ∈ target -> field ∈ source)
      -> ExecutableFieldsFieldValidationMergeCompatible source
      -> ExecutableFieldsFieldValidationMergeCompatible target := by
  intro hsubset hcompatible first later hfirst hlater hresponse
  exact hcompatible first later (hsubset first hfirst)
    (hsubset later hlater) hresponse

theorem ExecutableFieldsSameParentValidationMergeCompatible.mono
    (source target : List ExecutableField)
    : (∀ field, field ∈ target -> field ∈ source)
      -> ExecutableFieldsSameParentValidationMergeCompatible source
      -> ExecutableFieldsSameParentValidationMergeCompatible target := by
  intro hsubset hcompatible first later hfirst hlater hresponse hparent
  exact hcompatible first later (hsubset first hfirst)
    (hsubset later hlater) hresponse hparent

theorem collectedExecutableFields_mem_addExecutableGroup
    (group : Name × List ExecutableField)
    (groups : List (Name × List ExecutableField))
    (field : ExecutableField)
    : field
        ∈ collectedExecutableFields (GraphQL.Execution.addExecutableGroup group groups)
      ↔ field ∈ group.snd ∨ field ∈ collectedExecutableFields groups := by
  rcases group with ⟨groupName, groupFields⟩
  induction groups with
  | nil =>
      simp [collectedExecutableFields, GraphQL.Execution.addExecutableGroup]
  | cons current rest ih =>
      rcases current with ⟨currentName, currentFields⟩
      by_cases hname : (currentName == groupName) = true
      · simp [collectedExecutableFields, GraphQL.Execution.addExecutableGroup,
          hname, List.mem_append]
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
        simp [collectedExecutableFields, GraphQL.Execution.addExecutableGroup,
          hfalse, List.mem_append]
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

theorem collectedExecutableFields_mem_mergeExecutableGroups
    (left right : List (Name × List ExecutableField))
    (field : ExecutableField)
    : field
        ∈ collectedExecutableFields (GraphQL.Execution.mergeExecutableGroups left right)
      ↔ field ∈ collectedExecutableFields left
        ∨ field ∈ collectedExecutableFields right := by
  induction right generalizing left with
  | nil =>
      simp [collectedExecutableFields, GraphQL.Execution.mergeExecutableGroups]
  | cons group rest ih =>
      rcases group with ⟨responseName, fields⟩
      change
        field ∈
            collectedExecutableFields
              (GraphQL.Execution.mergeExecutableGroups
                (GraphQL.Execution.addExecutableGroup (responseName, fields)
                  left) rest)
          ↔
        field ∈ collectedExecutableFields left
          ∨ field ∈ collectedExecutableFields ((responseName, fields) :: rest)
      constructor
      · intro hmem
        rcases
            (ih
              (GraphQL.Execution.addExecutableGroup (responseName, fields)
                left)).mp hmem with hadded | hrest
        · rcases
            (collectedExecutableFields_mem_addExecutableGroup
              (responseName, fields) left field).mp hadded with
            hfield | hleft
          · exact Or.inr (by simp [collectedExecutableFields, hfield])
          · exact Or.inl hleft
        · exact Or.inr (by simp [collectedExecutableFields, hrest])
      · intro hmem
        rcases hmem with hleft | hright
        · exact
            (ih
              (GraphQL.Execution.addExecutableGroup (responseName, fields)
                left)).mpr
              (Or.inl
                ((collectedExecutableFields_mem_addExecutableGroup
                  (responseName, fields) left field).mpr (Or.inr hleft)))
        · have hfieldsOrRest :
              field ∈ fields ∨ field ∈ collectedExecutableFields rest := by
            simpa [collectedExecutableFields, List.mem_append] using hright
          rcases hfieldsOrRest with hfield | hrest
          · exact
              (ih
                (GraphQL.Execution.addExecutableGroup (responseName, fields)
                  left)).mpr
                (Or.inl
                  ((collectedExecutableFields_mem_addExecutableGroup
                    (responseName, fields) left field).mpr (Or.inl hfield)))
          · exact
              (ih
                (GraphQL.Execution.addExecutableGroup (responseName, fields)
                  left)).mpr (Or.inr hrest)

theorem collectedExecutableFields_addExecutableGroup_subset_append
    (group : Name × List ExecutableField)
    (groups : List (Name × List ExecutableField))
    : ∀ field,
        field
          ∈ collectedExecutableFields (GraphQL.Execution.addExecutableGroup group groups)
        -> field ∈ group.snd ++ collectedExecutableFields groups := by
  intro field hmem
  rcases
      (collectedExecutableFields_mem_addExecutableGroup group groups field).mp
        hmem with hgroup | hgroups
  · exact List.mem_append.mpr (Or.inl hgroup)
  · exact List.mem_append.mpr (Or.inr hgroups)

theorem collectedExecutableFields_mergeExecutableGroups_subset_append
    (left right : List (Name × List ExecutableField))
    : ∀ field,
        field
          ∈ collectedExecutableFields (GraphQL.Execution.mergeExecutableGroups left right)
        -> field ∈ collectedExecutableFields left ++ collectedExecutableFields right := by
  intro field hmem
  rcases
      (collectedExecutableFields_mem_mergeExecutableGroups left right field).mp
        hmem with hleft | hright
  · exact List.mem_append.mpr (Or.inl hleft)
  · exact List.mem_append.mpr (Or.inr hright)

theorem collectedExecutableFields_addExecutableGroup_fieldCompatible_of_append
    (group : Name × List ExecutableField)
    (groups : List (Name × List ExecutableField))
    : ExecutableFieldsFieldValidationMergeCompatible
        (group.snd ++ collectedExecutableFields groups)
      -> ExecutableFieldsFieldValidationMergeCompatible
          (collectedExecutableFields
            (GraphQL.Execution.addExecutableGroup group groups)) := by
  intro hcompatible
  exact ExecutableFieldsFieldValidationMergeCompatible.mono
    (group.snd ++ collectedExecutableFields groups)
    (collectedExecutableFields
      (GraphQL.Execution.addExecutableGroup group groups))
    (collectedExecutableFields_addExecutableGroup_subset_append group groups)
    hcompatible

theorem collectedExecutableFields_mergeExecutableGroups_fieldCompatible_of_append
    (left right : List (Name × List ExecutableField))
    : ExecutableFieldsFieldValidationMergeCompatible
        (collectedExecutableFields left ++ collectedExecutableFields right)
      -> ExecutableFieldsFieldValidationMergeCompatible
          (collectedExecutableFields
            (GraphQL.Execution.mergeExecutableGroups left right)) := by
  intro hcompatible
  exact ExecutableFieldsFieldValidationMergeCompatible.mono
    (collectedExecutableFields left ++ collectedExecutableFields right)
    (collectedExecutableFields
      (GraphQL.Execution.mergeExecutableGroups left right))
    (collectedExecutableFields_mergeExecutableGroups_subset_append left right)
    hcompatible

theorem executableFieldSelections_selectionSetValid_field
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType : Name)
    : ∀ fields : List ExecutableField,
        Validation.selectionSetValid schema variableDefinitions parentType
          (executableFieldSelections fields)
        -> ExecutableFieldsParent parentType fields
        -> ∀ field,
            field ∈ fields
            -> Validation.selectionSetValid schema variableDefinitions
                ((schema.fieldReturnType? field.parentType field.fieldName).getD
                  field.fieldName)
                field.selectionSet
  | [], _hvalid, _hparents, field, hfield => by
      simp at hfield
  | head :: rest, hvalid, hparents, field, hfield => by
      have hvalidCons :
          Validation.selectionSetValid schema variableDefinitions parentType
            (executableFieldSelection head ::
              executableFieldSelections rest) := by
        simpa [executableFieldSelections] using hvalid
      rcases List.mem_cons.mp hfield with hhead | hrest
      · subst field
        rcases Validation.selectionSetValid_field_head_lookup hvalidCons with
          ⟨fieldDefinition, hlookup, _harguments, hselectionSet⟩
        have hparent : head.parentType = parentType :=
          hparents head (by simp)
        have hreturn :
            ((schema.fieldReturnType? head.parentType head.fieldName).getD
              head.fieldName) =
            fieldDefinition.outputType.namedType := by
          subst hparent
          simp [Schema.fieldReturnType?, hlookup]
        simpa [hreturn] using
          Validation.fieldSelectionSetValid_selectionSetValid schema
            variableDefinitions fieldDefinition head.selectionSet hselectionSet
      · have htailValid :
            Validation.selectionSetValid schema variableDefinitions parentType
              (executableFieldSelections rest) :=
          Validation.selectionSetValid_tail hvalidCons
        have htailParents : ExecutableFieldsParent parentType rest := by
          intro candidate hcandidate
          exact hparents candidate (by simp [hcandidate])
        exact
          executableFieldSelections_selectionSetValid_field schema
            variableDefinitions parentType rest htailValid htailParents field
            hrest

theorem executableFieldsScopedBy_selectionSetValid_field
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType : Name) (selectionSet : List Selection)
    (fields : List ExecutableField)
    : Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> ExecutableFieldsScopedBy
          (FieldMerge.collectFields schema parentType selectionSet) fields
      -> ∀ field,
          field ∈ fields
          -> Validation.selectionSetValid schema variableDefinitions
              ((schema.fieldReturnType? field.parentType field.fieldName).getD
                field.fieldName)
              field.selectionSet := by
  intro hvalid hscoped field hfield
  rcases hscoped field hfield with
    ⟨scopedField, hscopedMem, hmatch⟩
  rcases hmatch with
    ⟨hparent, _hresponse, hfieldName, _harguments, hselectionSet⟩
  rcases
      GraphQL.NormalForm.collectFields_scoped_mem_fieldSelectionSetValid schema
        variableDefinitions parentType selectionSet scopedField hvalid
        hscopedMem with
    ⟨fieldDefinition, hlookup, houtput, hfieldSelectionSet⟩
  have hlookupField :
      schema.lookupField field.parentType field.fieldName =
        some fieldDefinition := by
    simpa [hparent, hfieldName] using hlookup
  have hreturn :
      ((schema.fieldReturnType? field.parentType field.fieldName).getD
        field.fieldName) =
        fieldDefinition.outputType.namedType := by
    simp [Schema.fieldReturnType?, hlookupField]
  have hselectionSetValid :
      Validation.selectionSetValid schema variableDefinitions
        fieldDefinition.outputType.namedType scopedField.selectionSet :=
    Validation.fieldSelectionSetValid_selectionSetValid schema
      variableDefinitions fieldDefinition scopedField.selectionSet
      hfieldSelectionSet
  simpa [hreturn, hselectionSet] using hselectionSetValid

theorem executableFieldsScopedBy_lookupField
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType : Name) (selectionSet : List Selection)
    (fields : List ExecutableField)
    : Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> ExecutableFieldsScopedBy
          (FieldMerge.collectFields schema parentType selectionSet) fields
      -> ∀ field,
          field ∈ fields
          -> ∃ fieldDefinition,
              schema.lookupField field.parentType field.fieldName
              = some fieldDefinition := by
  intro hvalid hscoped field hfield
  rcases hscoped field hfield with
    ⟨scopedField, hscopedMem, hmatch⟩
  rcases hmatch with
    ⟨hparent, _hresponse, hfieldName, _harguments, _hselectionSet⟩
  rcases
      GraphQL.NormalForm.collectFields_scoped_mem_fieldSelectionSetValid schema
        variableDefinitions parentType selectionSet scopedField hvalid
        hscopedMem with
    ⟨fieldDefinition, hlookup, _houtput, _hfieldSelectionSet⟩
  refine ⟨fieldDefinition, ?_⟩
  simpa [hparent, hfieldName] using hlookup

theorem executableFieldsRuntimeScopedBy_scopedSelectionSetValid_field
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (validParent runtimeType : Name) (selectionSet : List Selection)
    (fields : List ExecutableField)
    : Validation.selectionSetValid schema variableDefinitions validParent selectionSet
      -> ExecutableFieldsRuntimeScopedBy schema runtimeType
          (FieldMerge.collectFields schema validParent selectionSet) fields
      -> ∀ field,
          field ∈ fields
          -> ∃ scopedField,
              scopedField ∈ FieldMerge.collectFields schema validParent selectionSet
              ∧ ScopedFieldMatchesExecutableIdentity scopedField field
              ∧ ScopedFieldRuntimeApplies schema runtimeType scopedField
              ∧ Validation.selectionSetValid schema variableDefinitions
                  scopedField.outputType.namedType field.selectionSet := by
  intro hvalid hscoped field hfield
  rcases hscoped field hfield with
    ⟨scopedField, hscopedMem, hmatch, hruntime⟩
  rcases hmatch with
    ⟨hresponse, hfieldName, harguments, hselectionSet⟩
  rcases
      GraphQL.NormalForm.collectFields_scoped_mem_fieldSelectionSetValid schema
        variableDefinitions validParent selectionSet scopedField hvalid
        hscopedMem with
    ⟨fieldDefinition, _hlookup, houtput, hfieldSelectionSet⟩
  have hselectionSetValid :
      Validation.selectionSetValid schema variableDefinitions
        scopedField.outputType.namedType scopedField.selectionSet := by
    simpa [← houtput] using
      Validation.fieldSelectionSetValid_selectionSetValid schema
        variableDefinitions fieldDefinition scopedField.selectionSet
        hfieldSelectionSet
  refine
    ⟨scopedField, hscopedMem, ?_, hruntime, ?_⟩
  · exact ⟨hresponse, hfieldName, harguments, hselectionSet⟩
  · simpa [hselectionSet] using hselectionSetValid

theorem selectionSetSemanticsReady_mergedFieldSelectionSet
    (schema : Schema) (parentType : Name)
    : ∀ fields : List ExecutableField,
        (∀ field,
          field ∈ fields
          -> NormalForm.selectionSetSemanticsReady schema parentType field.selectionSet)
        -> NormalForm.selectionSetSemanticsReady schema parentType
            (GraphQL.Execution.mergedFieldSelectionSet fields)
  | [], _hready => by
      simpa [GraphQL.Execution.mergedFieldSelectionSet] using
        NormalForm.selectionSetSemanticsReady_nil schema parentType
  | field :: rest, hready => by
      have hfield :
          NormalForm.selectionSetSemanticsReady schema parentType
            field.selectionSet :=
        hready field (by simp)
      have hrest :
          NormalForm.selectionSetSemanticsReady schema parentType
            (GraphQL.Execution.mergedFieldSelectionSet rest) :=
        selectionSetSemanticsReady_mergedFieldSelectionSet schema parentType
          rest
          (by
            intro candidate hcandidate
            exact hready candidate (by simp [hcandidate]))
      simpa [GraphQL.Execution.mergedFieldSelectionSet] using
        NormalForm.selectionSetSemanticsReady_append hfield hrest

theorem selectionSetLookupValid_mergedFieldSelectionSet_of_semanticsReady
    (schema : Schema) (parentType : Name)
    (fields : List ExecutableField)
    : (∀ field,
        field ∈ fields
        -> NormalForm.selectionSetSemanticsReady schema parentType field.selectionSet)
      -> NormalForm.selectionSetLookupValid schema parentType
          (GraphQL.Execution.mergedFieldSelectionSet fields) := by
  intro hready
  exact
    NormalForm.selectionSetLookupValid_of_selectionSetSemanticsReady
      (GraphQL.Execution.mergedFieldSelectionSet fields)
      (selectionSetSemanticsReady_mergedFieldSelectionSet schema parentType
        fields hready)

theorem selectionSetLookupValid_mergedFieldSelectionSet
    (schema : Schema) (parentType : Name)
    : ∀ fields : List ExecutableField,
        (∀ field,
          field ∈ fields
          -> NormalForm.selectionSetLookupValid schema parentType field.selectionSet)
        -> NormalForm.selectionSetLookupValid schema parentType
            (GraphQL.Execution.mergedFieldSelectionSet fields)
  | [], _hlookup => by
      simpa [GraphQL.Execution.mergedFieldSelectionSet] using
        NormalForm.selectionSetLookupValid_nil schema parentType
  | field :: rest, hlookup => by
      have hfield :
          NormalForm.selectionSetLookupValid schema parentType
            field.selectionSet :=
        hlookup field (by simp)
      have hrest :
          NormalForm.selectionSetLookupValid schema parentType
            (GraphQL.Execution.mergedFieldSelectionSet rest) :=
        selectionSetLookupValid_mergedFieldSelectionSet schema parentType rest
          (by
            intro candidate hcandidate
            exact hlookup candidate (by simp [hcandidate]))
      simpa [GraphQL.Execution.mergedFieldSelectionSet] using
        NormalForm.selectionSetLookupValid_append hfield hrest

theorem selectionSetValidInPossibleTypes_mergedFieldSelectionSet
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType : Name)
    : ∀ fields : List ExecutableField,
        (∀ field,
          field ∈ fields
          -> Validation.selectionSetValidInPossibleTypes schema
              variableDefinitions parentType field.selectionSet)
        -> Validation.selectionSetValidInPossibleTypes schema
            variableDefinitions parentType
            (GraphQL.Execution.mergedFieldSelectionSet fields)
  | [], _hvalid => by
      simp [GraphQL.Execution.mergedFieldSelectionSet,
        Validation.selectionSetValidInPossibleTypes]
  | field :: rest, hvalid => by
      have hfield :
          Validation.selectionSetValidInPossibleTypes schema
            variableDefinitions parentType field.selectionSet :=
        hvalid field (by simp)
      have hrest :
          Validation.selectionSetValidInPossibleTypes schema
            variableDefinitions parentType
            (GraphQL.Execution.mergedFieldSelectionSet rest) :=
        selectionSetValidInPossibleTypes_mergedFieldSelectionSet schema
          variableDefinitions parentType rest
          (by
            intro candidate hcandidate
            exact hvalid candidate (by simp [hcandidate]))
      have happend :
          Validation.selectionSetValidInPossibleTypes schema
            variableDefinitions parentType
            (field.selectionSet ++
              GraphQL.Execution.mergedFieldSelectionSet rest) := by
        revert hfield
        induction field.selectionSet with
        | nil =>
            intro _hfield
            simpa using hrest
        | cons selection tail ih =>
            intro hfield
            change
              Validation.selectionValidInPossibleTypes schema variableDefinitions
                  parentType selection
                ∧ Validation.selectionSetValidInPossibleTypes schema
                  variableDefinitions parentType tail at hfield
            change
              Validation.selectionValidInPossibleTypes schema variableDefinitions
                  parentType selection
                ∧ Validation.selectionSetValidInPossibleTypes schema
                  variableDefinitions parentType
                  (tail ++ GraphQL.Execution.mergedFieldSelectionSet rest)
            exact ⟨hfield.1, ih hfield.2⟩
      change
        Validation.selectionSetValidInPossibleTypes schema
          variableDefinitions parentType
          (field.selectionSet ++
            GraphQL.Execution.mergedFieldSelectionSet rest)
      exact happend

mutual
  theorem collectSelection_identityScopedBy_of_selectionValid
      {ObjectIdentity : Type}
      (schema : Schema)
      (variableDefinitions : List VariableDefinition)
      (variableValues : VariableValues)
      (collectParent validParent : Name)
      (source : ResolverValue ObjectIdentity)
      (selection : Selection)
      : Validation.selectionValid schema variableDefinitions validParent selection
        -> ExecutableFieldsIdentityScopedBy
            (FieldMerge.collectFields schema validParent [selection])
            (collectedExecutableFields
              (GraphQL.Execution.collectSelection schema variableValues
                collectParent source selection)) := by
    intro hvalid field hfield
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        rcases Validation.selectionValid_field_lookup hvalid with
          ⟨fieldDefinition, hlookup, _harguments, _hselectionSet⟩
        by_cases hallows :
            selectionDirectivesAllowBool variableValues directives = true
        · simp [GraphQL.Execution.collectSelection, collectedExecutableFields,
            hallows] at hfield
          have hfieldEq :
              field =
                {
                  parentType := collectParent,
                  responseName := responseName,
                  fieldName := fieldName,
                  arguments := arguments,
                  selectionSet := selectionSet
                } := by
            simpa using hfield
          subst field
          refine
            ⟨{
              parentType := validParent,
              responseName := responseName,
              fieldName := fieldName,
              arguments := arguments,
              outputType := fieldDefinition.outputType,
              selectionSet := selectionSet
            }, ?_, ?_⟩
          · simp [FieldMerge.collectFields, hlookup]
          · exact ⟨rfl, rfl, rfl, rfl⟩
        · have hfalse :
              selectionDirectivesAllowBool variableValues directives = false := by
            cases hmatch : selectionDirectivesAllowBool variableValues directives
            · rfl
            · contradiction
          simp [GraphQL.Execution.collectSelection, collectedExecutableFields,
            hfalse] at hfield
    | inlineFragment typeCondition directives selectionSet =>
        cases typeCondition with
        | none =>
            have hselectionSet :
                Validation.selectionSetValid schema variableDefinitions
                  validParent selectionSet :=
              Validation.selectionValid_inlineFragment_none_selectionSetValid
                hvalid
            by_cases hallows :
                selectionDirectivesAllowBool variableValues directives = true
            · have hrecursive :=
                collectFields_identityScopedBy_of_selectionSetValid schema
                  variableDefinitions variableValues collectParent validParent
                  source selectionSet hselectionSet
              simp [GraphQL.Execution.collectSelection, hallows] at hfield
              rcases hrecursive field hfield with
                ⟨scopedField, hscoped, hmatch⟩
              exact ⟨scopedField, by simpa [FieldMerge.collectFields] using hscoped,
                hmatch⟩
            · have hfalse :
                  selectionDirectivesAllowBool variableValues directives =
                    false := by
                cases hmatch :
                    selectionDirectivesAllowBool variableValues directives
                · rfl
                · contradiction
              simp [GraphQL.Execution.collectSelection,
                collectedExecutableFields, hfalse] at hfield
        | some typeCondition =>
            have hselectionSet :
                Validation.selectionSetValid schema variableDefinitions
                  typeCondition selectionSet :=
              Validation.selectionValid_inlineFragment_some_selectionSetValid
                hvalid
            by_cases hallows :
                selectionDirectivesAllowBool variableValues directives = true
            · by_cases happly :
                  doesFragmentTypeApplyBool schema collectParent source
                    typeCondition = true
              · have hrecursive :=
                  collectFields_identityScopedBy_of_selectionSetValid schema
                    variableDefinitions variableValues collectParent typeCondition
                    source selectionSet hselectionSet
                simp [GraphQL.Execution.collectSelection, hallows, happly] at hfield
                rcases hrecursive field hfield with
                  ⟨scopedField, hscoped, hmatch⟩
                exact
                  ⟨scopedField, by simpa [FieldMerge.collectFields] using hscoped,
                    hmatch⟩
              · have hfalse :
                    doesFragmentTypeApplyBool schema collectParent source
                      typeCondition = false := by
                  cases hmatch :
                      doesFragmentTypeApplyBool schema collectParent source
                        typeCondition
                  · rfl
                  · contradiction
                simp [GraphQL.Execution.collectSelection,
                  collectedExecutableFields, hallows, hfalse] at hfield
            · have hfalse :
                  selectionDirectivesAllowBool variableValues directives =
                    false := by
                cases hmatch :
                    selectionDirectivesAllowBool variableValues directives
                · rfl
                · contradiction
              simp [GraphQL.Execution.collectSelection,
                collectedExecutableFields, hfalse] at hfield

  theorem collectFields_identityScopedBy_of_selectionSetValid
      {ObjectIdentity : Type}
      (schema : Schema)
      (variableDefinitions : List VariableDefinition)
      (variableValues : VariableValues)
      (collectParent validParent : Name)
      (source : ResolverValue ObjectIdentity)
      (selectionSet : List Selection)
      : Validation.selectionSetValid schema variableDefinitions validParent selectionSet
        -> ExecutableFieldsIdentityScopedBy
            (FieldMerge.collectFields schema validParent selectionSet)
            (collectedExecutableFields
              (GraphQL.Execution.collectFields schema variableValues collectParent
                source selectionSet)) := by
    intro hvalid field hfield
    cases selectionSet with
    | nil =>
        simp [GraphQL.Execution.collectFields, collectedExecutableFields] at hfield
    | cons selection rest =>
        have hhead :
            Validation.selectionValid schema variableDefinitions validParent
              selection := by
          simp [Validation.selectionSetValid] at hvalid
          exact hvalid.1
        have htail :
            Validation.selectionSetValid schema variableDefinitions validParent
              rest :=
          Validation.selectionSetValid_tail hvalid
        have hleft :=
          collectSelection_identityScopedBy_of_selectionValid schema
            variableDefinitions variableValues collectParent validParent source
            selection hhead
        have hright :=
          collectFields_identityScopedBy_of_selectionSetValid schema
            variableDefinitions variableValues collectParent validParent source
            rest htail
        simp [GraphQL.Execution.collectFields] at hfield
        rcases
            (collectedExecutableFields_mem_mergeExecutableGroups
              (GraphQL.Execution.collectSelection schema variableValues
                collectParent source selection)
              (GraphQL.Execution.collectFields schema variableValues collectParent
                source rest)
              field).mp hfield with hselection | hrest
        · rcases hleft field hselection with
            ⟨scopedField, hscoped, hmatch⟩
          refine ⟨scopedField, ?_, hmatch⟩
          rw [show selection :: rest = [selection] ++ rest by rfl]
          rw [FieldMerge.collectFields_append]
          exact List.mem_append.mpr (Or.inl hscoped)
        · rcases hright field hrest with
            ⟨scopedField, hscoped, hmatch⟩
          refine ⟨scopedField, ?_, hmatch⟩
          rw [show selection :: rest = [selection] ++ rest by rfl]
          rw [FieldMerge.collectFields_append]
          exact List.mem_append.mpr (Or.inr hscoped)
end

mutual
  theorem collectSelection_runtimeScopedBy_of_selectionValid
      {ObjectIdentity : Type}
      (schema : Schema)
      (variableDefinitions : List VariableDefinition)
      (variableValues : VariableValues)
      (collectParent validParent runtimeType : Name)
      (identity : ObjectIdentity)
      (selection : Selection)
      : ScopedParentRuntimeApplies schema runtimeType validParent
        -> Validation.selectionValid schema variableDefinitions validParent selection
        -> ExecutableFieldsRuntimeScopedBy schema runtimeType
            (FieldMerge.collectFields schema validParent [selection])
            (collectedExecutableFields
              (GraphQL.Execution.collectSelection schema variableValues
                collectParent (.object runtimeType identity) selection)) := by
    intro hparentRuntime hvalid field hfield
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        rcases Validation.selectionValid_field_lookup hvalid with
          ⟨fieldDefinition, hlookup, _harguments, _hselectionSet⟩
        by_cases hallows :
            selectionDirectivesAllowBool variableValues directives = true
        · simp [GraphQL.Execution.collectSelection, collectedExecutableFields,
            hallows] at hfield
          have hfieldEq :
              field =
                {
                  parentType := collectParent,
                  responseName := responseName,
                  fieldName := fieldName,
                  arguments := arguments,
                  selectionSet := selectionSet
                } := by
            simpa using hfield
          subst field
          refine
            ⟨{
              parentType := validParent,
              responseName := responseName,
              fieldName := fieldName,
              arguments := arguments,
              outputType := fieldDefinition.outputType,
              selectionSet := selectionSet
            }, ?_, ?_, ?_⟩
          · simp [FieldMerge.collectFields, hlookup]
          · exact ⟨rfl, rfl, rfl, rfl⟩
          · simpa [ScopedFieldRuntimeApplies, ScopedParentRuntimeApplies]
              using hparentRuntime
        · have hfalse :
              selectionDirectivesAllowBool variableValues directives = false := by
            cases hmatch : selectionDirectivesAllowBool variableValues directives
            · rfl
            · contradiction
          simp [GraphQL.Execution.collectSelection, collectedExecutableFields,
            hfalse] at hfield
    | inlineFragment typeCondition directives selectionSet =>
        cases typeCondition with
        | none =>
            have hselectionSet :
                Validation.selectionSetValid schema variableDefinitions
                  validParent selectionSet :=
              Validation.selectionValid_inlineFragment_none_selectionSetValid
                hvalid
            by_cases hallows :
                selectionDirectivesAllowBool variableValues directives = true
            · have hrecursive :=
                collectFields_runtimeScopedBy_of_selectionSetValid schema
                  variableDefinitions variableValues collectParent validParent
                  runtimeType identity selectionSet hparentRuntime hselectionSet
              simp [GraphQL.Execution.collectSelection, hallows] at hfield
              rcases hrecursive field hfield with
                ⟨scopedField, hscoped, hmatch, hruntime⟩
              exact ⟨scopedField, by simpa [FieldMerge.collectFields] using hscoped,
                hmatch, hruntime⟩
            · have hfalse :
                  selectionDirectivesAllowBool variableValues directives =
                    false := by
                cases hmatch :
                    selectionDirectivesAllowBool variableValues directives
                · rfl
                · contradiction
              simp [GraphQL.Execution.collectSelection,
                collectedExecutableFields, hfalse] at hfield
        | some typeCondition =>
            have hselectionSet :
                Validation.selectionSetValid schema variableDefinitions
                  typeCondition selectionSet :=
              Validation.selectionValid_inlineFragment_some_selectionSetValid
                hvalid
            by_cases hallows :
                selectionDirectivesAllowBool variableValues directives = true
            · by_cases happly :
                  doesFragmentTypeApplyBool schema collectParent
                    (.object runtimeType identity) typeCondition = true
              · have htypeRuntime :
                    ScopedParentRuntimeApplies schema runtimeType typeCondition := by
                  simpa [ScopedParentRuntimeApplies, doesFragmentTypeApplyBool,
                    runtimeObjectType?] using happly
                have hrecursive :=
                  collectFields_runtimeScopedBy_of_selectionSetValid schema
                    variableDefinitions variableValues collectParent typeCondition
                    runtimeType identity selectionSet htypeRuntime hselectionSet
                simp [GraphQL.Execution.collectSelection, hallows, happly] at hfield
                rcases hrecursive field hfield with
                  ⟨scopedField, hscoped, hmatch, hruntime⟩
                exact
                  ⟨scopedField, by simpa [FieldMerge.collectFields] using hscoped,
                    hmatch, hruntime⟩
              · have hfalse :
                    doesFragmentTypeApplyBool schema collectParent
                      (.object runtimeType identity) typeCondition = false := by
                  cases hmatch :
                      doesFragmentTypeApplyBool schema collectParent
                        (.object runtimeType identity) typeCondition
                  · rfl
                  · contradiction
                simp [GraphQL.Execution.collectSelection,
                  collectedExecutableFields, hallows, hfalse] at hfield
            · have hfalse :
                  selectionDirectivesAllowBool variableValues directives =
                    false := by
                cases hmatch :
                    selectionDirectivesAllowBool variableValues directives
                · rfl
                · contradiction
              simp [GraphQL.Execution.collectSelection,
                collectedExecutableFields, hfalse] at hfield

  theorem collectFields_runtimeScopedBy_of_selectionSetValid
      {ObjectIdentity : Type}
      (schema : Schema)
      (variableDefinitions : List VariableDefinition)
      (variableValues : VariableValues)
      (collectParent validParent runtimeType : Name)
      (identity : ObjectIdentity)
      (selectionSet : List Selection)
      : ScopedParentRuntimeApplies schema runtimeType validParent
        -> Validation.selectionSetValid schema variableDefinitions validParent
            selectionSet
        -> ExecutableFieldsRuntimeScopedBy schema runtimeType
            (FieldMerge.collectFields schema validParent selectionSet)
            (collectedExecutableFields
              (GraphQL.Execution.collectFields schema variableValues collectParent
                (.object runtimeType identity) selectionSet)) := by
    intro hparentRuntime hvalid field hfield
    cases selectionSet with
    | nil =>
        simp [GraphQL.Execution.collectFields, collectedExecutableFields] at hfield
    | cons selection rest =>
        have hhead :
            Validation.selectionValid schema variableDefinitions validParent
              selection := by
          simp [Validation.selectionSetValid] at hvalid
          exact hvalid.1
        have htail :
            Validation.selectionSetValid schema variableDefinitions validParent
              rest :=
          Validation.selectionSetValid_tail hvalid
        have hleft :=
          collectSelection_runtimeScopedBy_of_selectionValid schema
            variableDefinitions variableValues collectParent validParent
            runtimeType identity selection hparentRuntime hhead
        have hright :=
          collectFields_runtimeScopedBy_of_selectionSetValid schema
            variableDefinitions variableValues collectParent validParent
            runtimeType identity rest hparentRuntime htail
        simp [GraphQL.Execution.collectFields] at hfield
        rcases
            (collectedExecutableFields_mem_mergeExecutableGroups
              (GraphQL.Execution.collectSelection schema variableValues
                collectParent (.object runtimeType identity) selection)
              (GraphQL.Execution.collectFields schema variableValues collectParent
                (.object runtimeType identity) rest)
              field).mp hfield with hselection | hrest
        · rcases hleft field hselection with
            ⟨scopedField, hscoped, hmatch, hruntime⟩
          refine ⟨scopedField, ?_, hmatch, hruntime⟩
          rw [show selection :: rest = [selection] ++ rest by rfl]
          rw [FieldMerge.collectFields_append]
          exact List.mem_append.mpr (Or.inl hscoped)
        · rcases hright field hrest with
            ⟨scopedField, hscoped, hmatch, hruntime⟩
          refine ⟨scopedField, ?_, hmatch, hruntime⟩
          rw [show selection :: rest = [selection] ++ rest by rfl]
          rw [FieldMerge.collectFields_append]
          exact List.mem_append.mpr (Or.inr hscoped)
end

mutual
  theorem collectSelection_runtimeScopedBy_of_selectionValid_object
      {ObjectIdentity : Type}
      (schema : Schema)
      (variableDefinitions : List VariableDefinition)
      (variableValues : VariableValues)
      (collectParent validParent runtimeType : Name)
      (identity : ObjectIdentity)
      (selection : Selection)
      : ScopedParentRuntimeApplies schema runtimeType validParent
        -> Validation.selectionValid schema variableDefinitions validParent selection
        -> ExecutableFieldsRuntimeScopedBy schema runtimeType
            (FieldMerge.collectFields schema validParent [selection])
            (collectedExecutableFields
              (GraphQL.Execution.collectSelection schema variableValues
                collectParent (.object runtimeType identity) selection)) := by
    intro hparentRuntime hvalid field hfield
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        rcases Validation.selectionValid_field_lookup hvalid with
          ⟨fieldDefinition, hlookup, _harguments, _hselectionSet⟩
        by_cases hallows :
            selectionDirectivesAllowBool variableValues directives = true
        · simp [GraphQL.Execution.collectSelection, collectedExecutableFields,
            hallows] at hfield
          have hfieldEq :
              field =
                {
                  parentType := collectParent,
                  responseName := responseName,
                  fieldName := fieldName,
                  arguments := arguments,
                  selectionSet := selectionSet
                } := by
            simpa using hfield
          subst field
          refine
            ⟨{
              parentType := validParent,
              responseName := responseName,
              fieldName := fieldName,
              arguments := arguments,
              outputType := fieldDefinition.outputType,
              selectionSet := selectionSet
            }, ?_, ?_, ?_⟩
          · simp [FieldMerge.collectFields, hlookup]
          · exact ⟨rfl, rfl, rfl, rfl⟩
          · simpa [ScopedFieldRuntimeApplies, ScopedParentRuntimeApplies]
              using hparentRuntime
        · have hfalse :
              selectionDirectivesAllowBool variableValues directives = false := by
            cases hmatch : selectionDirectivesAllowBool variableValues directives
            · rfl
            · contradiction
          simp [GraphQL.Execution.collectSelection, collectedExecutableFields,
            hfalse] at hfield
    | inlineFragment typeCondition directives selectionSet =>
        cases typeCondition with
        | none =>
            have hselectionSet :
                Validation.selectionSetValid schema variableDefinitions
                  validParent selectionSet :=
              Validation.selectionValid_inlineFragment_none_selectionSetValid
                hvalid
            by_cases hallows :
                selectionDirectivesAllowBool variableValues directives = true
            · have hrecursive :=
                collectFields_runtimeScopedBy_of_selectionSetValid_object schema
                  variableDefinitions variableValues collectParent validParent
                  runtimeType identity selectionSet hparentRuntime hselectionSet
              simp [GraphQL.Execution.collectSelection, hallows] at hfield
              rcases hrecursive field hfield with
                ⟨scopedField, hscoped, hmatch, hruntime⟩
              exact ⟨scopedField, by simpa [FieldMerge.collectFields] using hscoped,
                hmatch, hruntime⟩
            · have hfalse :
                  selectionDirectivesAllowBool variableValues directives =
                    false := by
                cases hmatch :
                    selectionDirectivesAllowBool variableValues directives
                · rfl
                · contradiction
              simp [GraphQL.Execution.collectSelection,
                collectedExecutableFields, hfalse] at hfield
        | some typeCondition =>
            have hselectionSet :
                Validation.selectionSetValid schema variableDefinitions
                  typeCondition selectionSet :=
              Validation.selectionValid_inlineFragment_some_selectionSetValid
                hvalid
            by_cases hallows :
                selectionDirectivesAllowBool variableValues directives = true
            · by_cases happly :
                  doesFragmentTypeApplyBool schema collectParent
                    (.object runtimeType identity) typeCondition = true
              · have htypeRuntime :
                    ScopedParentRuntimeApplies schema runtimeType typeCondition := by
                  simpa [ScopedParentRuntimeApplies, doesFragmentTypeApplyBool,
                    runtimeObjectType?] using happly
                have hrecursive :=
                  collectFields_runtimeScopedBy_of_selectionSetValid_object schema
                    variableDefinitions variableValues collectParent typeCondition
                    runtimeType identity selectionSet htypeRuntime hselectionSet
                simp [GraphQL.Execution.collectSelection, hallows, happly] at hfield
                rcases hrecursive field hfield with
                  ⟨scopedField, hscoped, hmatch, hruntime⟩
                exact
                  ⟨scopedField, by simpa [FieldMerge.collectFields] using hscoped,
                    hmatch, hruntime⟩
              · have hfalse :
                    doesFragmentTypeApplyBool schema collectParent
                      (.object runtimeType identity) typeCondition = false := by
                  cases hmatch :
                      doesFragmentTypeApplyBool schema collectParent
                        (.object runtimeType identity) typeCondition
                  · rfl
                  · contradiction
                simp [GraphQL.Execution.collectSelection,
                  collectedExecutableFields, hallows, hfalse] at hfield
            · have hfalse :
                  selectionDirectivesAllowBool variableValues directives =
                    false := by
                cases hmatch :
                    selectionDirectivesAllowBool variableValues directives
                · rfl
                · contradiction
              simp [GraphQL.Execution.collectSelection,
                collectedExecutableFields, hfalse] at hfield

  theorem collectFields_runtimeScopedBy_of_selectionSetValid_object
      {ObjectIdentity : Type}
      (schema : Schema)
      (variableDefinitions : List VariableDefinition)
      (variableValues : VariableValues)
      (collectParent validParent runtimeType : Name)
      (identity : ObjectIdentity)
      (selectionSet : List Selection)
      : ScopedParentRuntimeApplies schema runtimeType validParent
        -> Validation.selectionSetValid schema variableDefinitions validParent
            selectionSet
        -> ExecutableFieldsRuntimeScopedBy schema runtimeType
            (FieldMerge.collectFields schema validParent selectionSet)
            (collectedExecutableFields
              (GraphQL.Execution.collectFields schema variableValues collectParent
                (.object runtimeType identity) selectionSet)) := by
    intro hparentRuntime hvalid field hfield
    cases selectionSet with
    | nil =>
        simp [GraphQL.Execution.collectFields, collectedExecutableFields] at hfield
    | cons selection rest =>
        have hhead :
            Validation.selectionValid schema variableDefinitions validParent
              selection := by
          simp [Validation.selectionSetValid] at hvalid
          exact hvalid.1
        have htail :
            Validation.selectionSetValid schema variableDefinitions validParent
              rest :=
          Validation.selectionSetValid_tail hvalid
        have hleft :=
          collectSelection_runtimeScopedBy_of_selectionValid_object schema
            variableDefinitions variableValues collectParent validParent
            runtimeType identity selection hparentRuntime hhead
        have hright :=
          collectFields_runtimeScopedBy_of_selectionSetValid_object schema
            variableDefinitions variableValues collectParent validParent
            runtimeType identity rest hparentRuntime htail
        simp [GraphQL.Execution.collectFields] at hfield
        rcases
            (collectedExecutableFields_mem_mergeExecutableGroups
              (GraphQL.Execution.collectSelection schema variableValues
                collectParent (.object runtimeType identity) selection)
              (GraphQL.Execution.collectFields schema variableValues collectParent
                (.object runtimeType identity) rest)
              field).mp hfield with hselection | hrest
        · rcases hleft field hselection with
            ⟨scopedField, hscoped, hmatch, hruntime⟩
          refine ⟨scopedField, ?_, hmatch, hruntime⟩
          rw [show selection :: rest = [selection] ++ rest by rfl]
          rw [FieldMerge.collectFields_append]
          exact List.mem_append.mpr (Or.inl hscoped)
        · rcases hright field hrest with
            ⟨scopedField, hscoped, hmatch, hruntime⟩
          refine ⟨scopedField, ?_, hmatch, hruntime⟩
          rw [show selection :: rest = [selection] ++ rest by rfl]
          rw [FieldMerge.collectFields_append]
          exact List.mem_append.mpr (Or.inr hscoped)
end

mutual
  theorem collectSelection_runtimeScopedBy_of_selectionLookupValid
      {ObjectIdentity : Type}
      (schema : Schema)
      (variableValues : VariableValues)
      (collectParent scopedParent runtimeType : Name)
      (identity : ObjectIdentity)
      (selection : Selection)
      : ScopedParentRuntimeApplies schema runtimeType scopedParent
        -> NormalForm.selectionLookupValid schema scopedParent selection
        -> ExecutableFieldsRuntimeScopedBy schema runtimeType
            (FieldMerge.collectFields schema scopedParent [selection])
            (collectedExecutableFields
              (GraphQL.Execution.collectSelection schema variableValues
                collectParent (.object runtimeType identity) selection)) := by
    intro hparentRuntime hlookupValid field hfield
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        have hfieldLookup :
            ∃ fieldDefinition,
              schema.lookupField scopedParent fieldName =
                some fieldDefinition := by
          simpa [NormalForm.selectionLookupValid] using hlookupValid
        rcases hfieldLookup with ⟨fieldDefinition, hlookup⟩
        by_cases hallows :
            selectionDirectivesAllowBool variableValues directives = true
        · simp [GraphQL.Execution.collectSelection, collectedExecutableFields,
            hallows] at hfield
          have hfieldEq :
              field =
                {
                  parentType := collectParent,
                  responseName := responseName,
                  fieldName := fieldName,
                  arguments := arguments,
                  selectionSet := selectionSet
                } := by
            simpa using hfield
          subst field
          refine
            ⟨{
              parentType := scopedParent,
              responseName := responseName,
              fieldName := fieldName,
              arguments := arguments,
              outputType := fieldDefinition.outputType,
              selectionSet := selectionSet
            }, ?_, ?_, ?_⟩
          · simp [FieldMerge.collectFields, hlookup]
          · exact ⟨rfl, rfl, rfl, rfl⟩
          · simpa [ScopedFieldRuntimeApplies, ScopedParentRuntimeApplies]
              using hparentRuntime
        · have hfalse :
              selectionDirectivesAllowBool variableValues directives = false := by
            cases hmatch : selectionDirectivesAllowBool variableValues directives
            · rfl
            · contradiction
          simp [GraphQL.Execution.collectSelection, collectedExecutableFields,
            hfalse] at hfield
    | inlineFragment typeCondition directives selectionSet =>
        cases typeCondition with
        | none =>
            by_cases hallows :
                selectionDirectivesAllowBool variableValues directives = true
            · have hrecursive :=
                collectFields_runtimeScopedBy_of_selectionSetLookupValid schema
                  variableValues collectParent scopedParent runtimeType identity
                  selectionSet hparentRuntime
                  (by simpa [NormalForm.selectionLookupValid] using hlookupValid)
              simp [GraphQL.Execution.collectSelection, hallows] at hfield
              rcases hrecursive field hfield with
                ⟨scopedField, hscoped, hmatch, hruntime⟩
              exact ⟨scopedField, by simpa [FieldMerge.collectFields] using hscoped,
                hmatch, hruntime⟩
            · have hfalse :
                  selectionDirectivesAllowBool variableValues directives =
                    false := by
                cases hmatch :
                    selectionDirectivesAllowBool variableValues directives
                · rfl
                · contradiction
              simp [GraphQL.Execution.collectSelection,
                collectedExecutableFields, hfalse] at hfield
        | some typeCondition =>
            have hselectionSet :
                NormalForm.selectionSetLookupValid schema typeCondition
                  selectionSet := by
              simpa [NormalForm.selectionLookupValid] using hlookupValid
            by_cases hallows :
                selectionDirectivesAllowBool variableValues directives = true
            · by_cases happly :
                  doesFragmentTypeApplyBool schema collectParent
                    (.object runtimeType identity) typeCondition = true
              · have htypeRuntime :
                    ScopedParentRuntimeApplies schema runtimeType typeCondition := by
                  simpa [ScopedParentRuntimeApplies, doesFragmentTypeApplyBool,
                    runtimeObjectType?] using happly
                have hrecursive :=
                  collectFields_runtimeScopedBy_of_selectionSetLookupValid schema
                    variableValues collectParent typeCondition runtimeType
                    identity selectionSet htypeRuntime hselectionSet
                simp [GraphQL.Execution.collectSelection, hallows, happly] at hfield
                rcases hrecursive field hfield with
                  ⟨scopedField, hscoped, hmatch, hruntime⟩
                exact
                  ⟨scopedField, by simpa [FieldMerge.collectFields] using hscoped,
                    hmatch, hruntime⟩
              · have hfalse :
                    doesFragmentTypeApplyBool schema collectParent
                      (.object runtimeType identity) typeCondition = false := by
                  cases hmatch :
                      doesFragmentTypeApplyBool schema collectParent
                        (.object runtimeType identity) typeCondition
                  · rfl
                  · contradiction
                simp [GraphQL.Execution.collectSelection,
                  collectedExecutableFields, hallows, hfalse] at hfield
            · have hfalse :
                  selectionDirectivesAllowBool variableValues directives =
                    false := by
                cases hmatch :
                    selectionDirectivesAllowBool variableValues directives
                · rfl
                · contradiction
              simp [GraphQL.Execution.collectSelection,
                collectedExecutableFields, hfalse] at hfield

  theorem collectFields_runtimeScopedBy_of_selectionSetLookupValid
      {ObjectIdentity : Type}
      (schema : Schema)
      (variableValues : VariableValues)
      (collectParent scopedParent runtimeType : Name)
      (identity : ObjectIdentity)
      (selectionSet : List Selection)
      : ScopedParentRuntimeApplies schema runtimeType scopedParent
        -> NormalForm.selectionSetLookupValid schema scopedParent selectionSet
        -> ExecutableFieldsRuntimeScopedBy schema runtimeType
            (FieldMerge.collectFields schema scopedParent selectionSet)
            (collectedExecutableFields
              (GraphQL.Execution.collectFields schema variableValues collectParent
                (.object runtimeType identity) selectionSet)) := by
    intro hparentRuntime hlookupValid field hfield
    cases selectionSet with
    | nil =>
        simp [GraphQL.Execution.collectFields, collectedExecutableFields] at hfield
    | cons selection rest =>
        have hlookupValid' :
            ∀ candidate, candidate ∈ selection :: rest ->
              NormalForm.selectionLookupValid schema scopedParent candidate := by
          simpa [NormalForm.selectionSetLookupValid] using hlookupValid
        have hhead :
            NormalForm.selectionLookupValid schema scopedParent selection := by
          exact hlookupValid' selection (by simp)
        have htail :
            NormalForm.selectionSetLookupValid schema scopedParent rest := by
          have htailFunction :
              ∀ candidate, candidate ∈ rest ->
                NormalForm.selectionLookupValid schema scopedParent candidate := by
            intro candidate hcandidate
            exact hlookupValid' candidate
              (List.mem_cons_of_mem selection hcandidate)
          simpa [NormalForm.selectionSetLookupValid] using htailFunction
        have hleft :=
          collectSelection_runtimeScopedBy_of_selectionLookupValid schema
            variableValues collectParent scopedParent runtimeType identity
            selection hparentRuntime hhead
        have hright :=
          collectFields_runtimeScopedBy_of_selectionSetLookupValid schema
            variableValues collectParent scopedParent runtimeType identity rest
            hparentRuntime htail
        simp [GraphQL.Execution.collectFields] at hfield
        rcases
            (collectedExecutableFields_mem_mergeExecutableGroups
              (GraphQL.Execution.collectSelection schema variableValues
                collectParent (.object runtimeType identity) selection)
              (GraphQL.Execution.collectFields schema variableValues collectParent
                (.object runtimeType identity) rest)
              field).mp hfield with hselection | hrest
        · rcases hleft field hselection with
            ⟨scopedField, hscoped, hmatch, hruntime⟩
          refine ⟨scopedField, ?_, hmatch, hruntime⟩
          rw [show selection :: rest = [selection] ++ rest by rfl]
          rw [FieldMerge.collectFields_append]
          exact List.mem_append.mpr (Or.inl hscoped)
        · rcases hright field hrest with
            ⟨scopedField, hscoped, hmatch, hruntime⟩
          refine ⟨scopedField, ?_, hmatch, hruntime⟩
          rw [show selection :: rest = [selection] ++ rest by rfl]
          rw [FieldMerge.collectFields_append]
          exact List.mem_append.mpr (Or.inr hscoped)
end

mutual
  theorem collectSelection_runtimeScopedBy_of_selectionLookupValid_object
      {ObjectIdentity : Type}
      (schema : Schema)
      (variableValues : VariableValues)
      (collectParent scopedParent runtimeType : Name)
      (identity : ObjectIdentity)
      (selection : Selection)
      : ScopedParentRuntimeApplies schema runtimeType scopedParent
        -> NormalForm.selectionLookupValid schema scopedParent selection
        -> ExecutableFieldsRuntimeScopedBy schema runtimeType
            (FieldMerge.collectFields schema scopedParent [selection])
            (collectedExecutableFields
              (GraphQL.Execution.collectSelection schema variableValues
                collectParent (.object runtimeType identity) selection)) := by
    intro hparentRuntime hlookupValid field hfield
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        have hfieldLookup :
            ∃ fieldDefinition,
              schema.lookupField scopedParent fieldName =
                some fieldDefinition := by
          simpa [NormalForm.selectionLookupValid] using hlookupValid
        rcases hfieldLookup with ⟨fieldDefinition, hlookup⟩
        by_cases hallows :
            selectionDirectivesAllowBool variableValues directives = true
        · simp [GraphQL.Execution.collectSelection, collectedExecutableFields,
            hallows] at hfield
          have hfieldEq :
              field =
                {
                  parentType := collectParent,
                  responseName := responseName,
                  fieldName := fieldName,
                  arguments := arguments,
                  selectionSet := selectionSet
                } := by
            simpa using hfield
          subst field
          refine
            ⟨{
              parentType := scopedParent,
              responseName := responseName,
              fieldName := fieldName,
              arguments := arguments,
              outputType := fieldDefinition.outputType,
              selectionSet := selectionSet
            }, ?_, ?_, ?_⟩
          · simp [FieldMerge.collectFields, hlookup]
          · exact ⟨rfl, rfl, rfl, rfl⟩
          · simpa [ScopedFieldRuntimeApplies, ScopedParentRuntimeApplies]
              using hparentRuntime
        · have hfalse :
              selectionDirectivesAllowBool variableValues directives = false := by
            cases hmatch : selectionDirectivesAllowBool variableValues directives
            · rfl
            · contradiction
          simp [GraphQL.Execution.collectSelection, collectedExecutableFields,
            hfalse] at hfield
    | inlineFragment typeCondition directives selectionSet =>
        cases typeCondition with
        | none =>
            by_cases hallows :
                selectionDirectivesAllowBool variableValues directives = true
            · have hrecursive :=
                collectFields_runtimeScopedBy_of_selectionSetLookupValid_object
                  schema variableValues collectParent scopedParent runtimeType
                  identity selectionSet hparentRuntime
                  (by simpa [NormalForm.selectionLookupValid] using
                    hlookupValid)
              simp [GraphQL.Execution.collectSelection, hallows] at hfield
              rcases hrecursive field hfield with
                ⟨scopedField, hscoped, hmatch, hruntime⟩
              exact ⟨scopedField,
                by simpa [FieldMerge.collectFields] using hscoped,
                hmatch, hruntime⟩
            · have hfalse :
                  selectionDirectivesAllowBool variableValues directives =
                    false := by
                cases hmatch :
                    selectionDirectivesAllowBool variableValues directives
                · rfl
                · contradiction
              simp [GraphQL.Execution.collectSelection,
                collectedExecutableFields, hfalse] at hfield
        | some typeCondition =>
            have hselectionSet :
                NormalForm.selectionSetLookupValid schema typeCondition
                  selectionSet := by
              simpa [NormalForm.selectionLookupValid] using hlookupValid
            by_cases hallows :
                selectionDirectivesAllowBool variableValues directives = true
            · by_cases happly :
                  doesFragmentTypeApplyBool schema collectParent
                    (.object runtimeType identity) typeCondition = true
              · have htypeRuntime :
                    ScopedParentRuntimeApplies schema runtimeType typeCondition := by
                  simpa [ScopedParentRuntimeApplies, doesFragmentTypeApplyBool,
                    runtimeObjectType?] using happly
                have hrecursive :=
                  collectFields_runtimeScopedBy_of_selectionSetLookupValid_object
                    schema variableValues collectParent typeCondition runtimeType
                    identity selectionSet htypeRuntime hselectionSet
                simp [GraphQL.Execution.collectSelection, hallows, happly] at hfield
                rcases hrecursive field hfield with
                  ⟨scopedField, hscoped, hmatch, hruntime⟩
                exact
                  ⟨scopedField,
                    by simpa [FieldMerge.collectFields] using hscoped,
                    hmatch, hruntime⟩
              · have hfalse :
                    doesFragmentTypeApplyBool schema collectParent
                      (.object runtimeType identity) typeCondition = false := by
                  cases hmatch :
                      doesFragmentTypeApplyBool schema collectParent
                        (.object runtimeType identity) typeCondition
                  · rfl
                  · contradiction
                simp [GraphQL.Execution.collectSelection,
                  collectedExecutableFields, hallows, hfalse] at hfield
            · have hfalse :
                  selectionDirectivesAllowBool variableValues directives =
                    false := by
                cases hmatch :
                    selectionDirectivesAllowBool variableValues directives
                · rfl
                · contradiction
              simp [GraphQL.Execution.collectSelection,
                collectedExecutableFields, hfalse] at hfield

  theorem collectFields_runtimeScopedBy_of_selectionSetLookupValid_object
      {ObjectIdentity : Type}
      (schema : Schema)
      (variableValues : VariableValues)
      (collectParent scopedParent runtimeType : Name)
      (identity : ObjectIdentity)
      (selectionSet : List Selection)
      : ScopedParentRuntimeApplies schema runtimeType scopedParent
        -> NormalForm.selectionSetLookupValid schema scopedParent selectionSet
        -> ExecutableFieldsRuntimeScopedBy schema runtimeType
            (FieldMerge.collectFields schema scopedParent selectionSet)
            (collectedExecutableFields
              (GraphQL.Execution.collectFields schema variableValues collectParent
                (.object runtimeType identity) selectionSet)) := by
    intro hparentRuntime hlookupValid field hfield
    cases selectionSet with
    | nil =>
        simp [GraphQL.Execution.collectFields, collectedExecutableFields] at hfield
    | cons selection rest =>
        have hlookupValid' :
            ∀ candidate, candidate ∈ selection :: rest ->
              NormalForm.selectionLookupValid schema scopedParent candidate := by
          simpa [NormalForm.selectionSetLookupValid] using hlookupValid
        have hhead :
            NormalForm.selectionLookupValid schema scopedParent selection := by
          exact hlookupValid' selection (by simp)
        have htail :
            NormalForm.selectionSetLookupValid schema scopedParent rest := by
          have htailFunction :
              ∀ candidate, candidate ∈ rest ->
                NormalForm.selectionLookupValid schema scopedParent candidate := by
            intro candidate hcandidate
            exact hlookupValid' candidate
              (List.mem_cons_of_mem selection hcandidate)
          simpa [NormalForm.selectionSetLookupValid] using htailFunction
        have hleft :=
          collectSelection_runtimeScopedBy_of_selectionLookupValid_object schema
            variableValues collectParent scopedParent runtimeType identity
            selection hparentRuntime hhead
        have hright :=
          collectFields_runtimeScopedBy_of_selectionSetLookupValid_object schema
            variableValues collectParent scopedParent runtimeType identity rest
            hparentRuntime htail
        simp [GraphQL.Execution.collectFields] at hfield
        rcases
            (collectedExecutableFields_mem_mergeExecutableGroups
              (GraphQL.Execution.collectSelection schema variableValues
                collectParent (.object runtimeType identity) selection)
              (GraphQL.Execution.collectFields schema variableValues collectParent
                (.object runtimeType identity) rest)
              field).mp hfield with hselection | hrest
        · rcases hleft field hselection with
            ⟨scopedField, hscoped, hmatch, hruntime⟩
          refine ⟨scopedField, ?_, hmatch, hruntime⟩
          rw [show selection :: rest = [selection] ++ rest by rfl]
          rw [FieldMerge.collectFields_append]
          exact List.mem_append.mpr (Or.inl hscoped)
        · rcases hright field hrest with
            ⟨scopedField, hscoped, hmatch, hruntime⟩
          refine ⟨scopedField, ?_, hmatch, hruntime⟩
          rw [show selection :: rest = [selection] ++ rest by rfl]
          rw [FieldMerge.collectFields_append]
          exact List.mem_append.mpr (Or.inr hscoped)
end

mutual
  theorem collectSelection_lookupValid_of_selectionSemanticsReady_object
      {ObjectIdentity : Type}
      (schema : Schema)
      (variableValues : VariableValues)
      (parentType runtimeType : Name)
      (identity : ObjectIdentity)
      (selection : Selection)
      : schema.objectType parentType
        -> ScopedParentRuntimeApplies schema runtimeType parentType
        -> NormalForm.selectionSemanticsReady schema parentType selection
        -> ∀ field,
            field
              ∈ collectedExecutableFields
                  (GraphQL.Execution.collectSelection schema variableValues
                    parentType (.object runtimeType identity) selection)
            -> ∃ fieldDefinition,
                schema.lookupField parentType field.fieldName = some fieldDefinition := by
    intro hobject hparentRuntime hready field hfield
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        have hfieldReady :
            ∃ fieldDefinition,
              schema.lookupField parentType fieldName = some fieldDefinition
                ∧ ∀ runtimeType,
                  schema.typeIncludesObjectBool
                      fieldDefinition.outputType.namedType runtimeType =
                    true ->
                  NormalForm.selectionSetSemanticsReady schema runtimeType
                    selectionSet := by
          simpa [NormalForm.selectionSemanticsReady] using hready
        rcases hfieldReady with ⟨fieldDefinition, hlookup, _hchildReady⟩
        by_cases hallows :
            selectionDirectivesAllowBool variableValues directives = true
        · simp [GraphQL.Execution.collectSelection, collectedExecutableFields,
            hallows] at hfield
          subst field
          exact ⟨fieldDefinition, hlookup⟩
        · have hfalse :
              selectionDirectivesAllowBool variableValues directives = false := by
            cases hmatch : selectionDirectivesAllowBool variableValues directives
            · rfl
            · contradiction
          simp [GraphQL.Execution.collectSelection, collectedExecutableFields,
            hfalse] at hfield
    | inlineFragment typeCondition directives selectionSet =>
        cases typeCondition with
        | none =>
            by_cases hallows :
                selectionDirectivesAllowBool variableValues directives = true
            · have hbodyReady :
                  NormalForm.selectionSetSemanticsReady schema parentType
                    selectionSet := by
                simpa [NormalForm.selectionSemanticsReady] using hready
              have hrecursive :=
                collectFields_lookupValid_of_selectionSetSemanticsReady_object
                  schema variableValues parentType runtimeType identity
                  selectionSet hobject hparentRuntime hbodyReady
              simp [GraphQL.Execution.collectSelection, hallows] at hfield
              exact hrecursive field hfield
            · have hfalse :
                  selectionDirectivesAllowBool variableValues directives =
                    false := by
                cases hmatch :
                    selectionDirectivesAllowBool variableValues directives
                · rfl
                · contradiction
              simp [GraphQL.Execution.collectSelection, collectedExecutableFields,
                hfalse] at hfield
        | some typeCondition =>
            by_cases hallows :
                selectionDirectivesAllowBool variableValues directives = true
            · by_cases happly :
                  doesFragmentTypeApplyBool schema parentType
                    (.object runtimeType identity) typeCondition = true
              · have hbodyReady :
                    NormalForm.selectionSetSemanticsReady schema parentType
                      selectionSet := by
                  have hreadyPair :
                      NormalForm.selectionSetLookupValid schema typeCondition
                          selectionSet
                        ∧
                        (schema.typesOverlapBool parentType typeCondition =
                          true ->
                          NormalForm.selectionSetSemanticsReady schema
                            parentType selectionSet) := by
                    simpa [NormalForm.selectionSemanticsReady] using hready
                  have hruntimeEq : runtimeType = parentType :=
                    object_typeIncludesObjectBool_eq_self schema hobject
                      hparentRuntime
                  have htypeIncludes :
                      schema.typeIncludesObjectBool typeCondition parentType =
                        true := by
                    simpa [doesFragmentTypeApplyBool, runtimeObjectType?,
                      hruntimeEq] using happly
                  have hparentIncludes :
                      schema.typeIncludesObjectBool parentType parentType =
                        true :=
                    NormalForm.object_typeIncludesObjectBool_self schema hobject
                  have hoverlap :
                      schema.typesOverlapBool parentType typeCondition =
                        true := by
                    unfold Schema.typesOverlapBool
                    exact List.any_eq_true.mpr
                      ⟨parentType, List.contains_iff_mem.mp hparentIncludes,
                        htypeIncludes⟩
                  exact hreadyPair.2 hoverlap
                have hrecursive :=
                  collectFields_lookupValid_of_selectionSetSemanticsReady_object
                    schema variableValues parentType runtimeType identity
                    selectionSet hobject hparentRuntime hbodyReady
                simp [GraphQL.Execution.collectSelection, hallows, happly] at hfield
                exact hrecursive field hfield
              · have hfalse :
                    doesFragmentTypeApplyBool schema parentType
                      (.object runtimeType identity) typeCondition = false := by
                  cases hmatch :
                      doesFragmentTypeApplyBool schema parentType
                        (.object runtimeType identity) typeCondition
                  · rfl
                  · contradiction
                simp [GraphQL.Execution.collectSelection, collectedExecutableFields,
                  hallows, hfalse] at hfield
            · have hfalse :
                  selectionDirectivesAllowBool variableValues directives =
                    false := by
                cases hmatch :
                    selectionDirectivesAllowBool variableValues directives
                · rfl
                · contradiction
              simp [GraphQL.Execution.collectSelection, collectedExecutableFields,
                hfalse] at hfield

  theorem collectFields_lookupValid_of_selectionSetSemanticsReady_object
      {ObjectIdentity : Type}
      (schema : Schema)
      (variableValues : VariableValues)
      (parentType runtimeType : Name)
      (identity : ObjectIdentity)
      (selectionSet : List Selection)
      : schema.objectType parentType
        -> ScopedParentRuntimeApplies schema runtimeType parentType
        -> NormalForm.selectionSetSemanticsReady schema parentType selectionSet
        -> ∀ field,
            field
              ∈ collectedExecutableFields
                  (GraphQL.Execution.collectFields schema variableValues
                    parentType (.object runtimeType identity) selectionSet)
            -> ∃ fieldDefinition,
                schema.lookupField parentType field.fieldName = some fieldDefinition := by
    intro hobject hparentRuntime hready field hfield
    cases selectionSet with
    | nil =>
        simp [GraphQL.Execution.collectFields, collectedExecutableFields] at hfield
    | cons selection rest =>
        have hheadReady :
            NormalForm.selectionSemanticsReady schema parentType selection := by
          unfold NormalForm.selectionSetSemanticsReady at hready
          exact hready selection (by simp)
        have htailReady :
            NormalForm.selectionSetSemanticsReady schema parentType rest :=
          NormalForm.selectionSetSemanticsReady_tail hready
        have hleft :=
          collectSelection_lookupValid_of_selectionSemanticsReady_object
            schema variableValues parentType runtimeType identity selection
            hobject hparentRuntime hheadReady
        have hright :=
          collectFields_lookupValid_of_selectionSetSemanticsReady_object
            schema variableValues parentType runtimeType identity rest hobject
            hparentRuntime htailReady
        simp [GraphQL.Execution.collectFields] at hfield
        rcases
            (collectedExecutableFields_mem_mergeExecutableGroups
              (GraphQL.Execution.collectSelection schema variableValues
                parentType (.object runtimeType identity) selection)
              (GraphQL.Execution.collectFields schema variableValues parentType
                (.object runtimeType identity) rest)
              field).mp hfield with hselection | hrest
        · exact hleft field hselection
        · exact hright field hrest
end

mutual
  theorem collectSelection_childSemanticsReady_of_selectionSemanticsReady_object
      {ObjectIdentity : Type}
      (schema : Schema)
      (variableValues : VariableValues)
      (parentType runtimeType : Name)
      (identity : ObjectIdentity)
      (selection : Selection)
      : schema.objectType parentType
        -> ScopedParentRuntimeApplies schema runtimeType parentType
        -> NormalForm.selectionSemanticsReady schema parentType selection
        -> ∀ field,
            field
              ∈ collectedExecutableFields
                  (GraphQL.Execution.collectSelection schema variableValues
                    parentType (.object runtimeType identity) selection)
            -> ∀ fieldDefinition,
                schema.lookupField field.parentType field.fieldName = some fieldDefinition
                -> ∀ childRuntime,
                    schema.typeIncludesObjectBool
                        fieldDefinition.outputType.namedType childRuntime
                      = true
                    -> NormalForm.selectionSetSemanticsReady schema childRuntime
                        field.selectionSet := by
    intro hobject hparentRuntime hready field hfield fieldDefinition hlookup
      childRuntime hinclude
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        by_cases hallows :
            selectionDirectivesAllowBool variableValues directives = true
        · simp [GraphQL.Execution.collectSelection, collectedExecutableFields,
            hallows] at hfield
          subst field
          have hfieldReady :
              ∃ readyDefinition,
                schema.lookupField parentType fieldName = some readyDefinition
                  ∧ ∀ runtimeType,
                    schema.typeIncludesObjectBool
                        readyDefinition.outputType.namedType runtimeType =
                      true ->
                    NormalForm.selectionSetSemanticsReady schema runtimeType
                      selectionSet := by
            simpa [NormalForm.selectionSemanticsReady] using hready
          rcases hfieldReady with
            ⟨readyDefinition, hreadyLookup, hchildReady⟩
          rw [hlookup] at hreadyLookup
          cases hreadyLookup
          exact hchildReady childRuntime hinclude
        · have hfalse :
              selectionDirectivesAllowBool variableValues directives = false := by
            cases hmatch : selectionDirectivesAllowBool variableValues directives
            · rfl
            · contradiction
          simp [GraphQL.Execution.collectSelection, collectedExecutableFields,
            hfalse] at hfield
    | inlineFragment typeCondition directives selectionSet =>
        cases typeCondition with
        | none =>
            by_cases hallows :
                selectionDirectivesAllowBool variableValues directives = true
            · have hbodyReady :
                  NormalForm.selectionSetSemanticsReady schema parentType
                    selectionSet := by
                simpa [NormalForm.selectionSemanticsReady] using hready
              have hrecursive :=
                collectFields_childSemanticsReady_of_selectionSetSemanticsReady_object
                  schema variableValues parentType runtimeType identity
                  selectionSet hobject hparentRuntime hbodyReady
              simp [GraphQL.Execution.collectSelection, hallows] at hfield
              exact hrecursive field hfield fieldDefinition hlookup
                childRuntime hinclude
            · have hfalse :
                  selectionDirectivesAllowBool variableValues directives =
                    false := by
                cases hmatch :
                    selectionDirectivesAllowBool variableValues directives
                · rfl
                · contradiction
              simp [GraphQL.Execution.collectSelection,
                collectedExecutableFields, hfalse] at hfield
        | some typeCondition =>
            by_cases hallows :
                selectionDirectivesAllowBool variableValues directives = true
            · by_cases happly :
                  doesFragmentTypeApplyBool schema parentType
                    (.object runtimeType identity) typeCondition = true
              · have hbodyReady :
                    NormalForm.selectionSetSemanticsReady schema parentType
                      selectionSet := by
                  have hreadyPair :
                      NormalForm.selectionSetLookupValid schema typeCondition
                          selectionSet
                        ∧
                        (schema.typesOverlapBool parentType typeCondition =
                          true ->
                          NormalForm.selectionSetSemanticsReady schema
                            parentType selectionSet) := by
                    simpa [NormalForm.selectionSemanticsReady] using hready
                  have hruntimeEq : runtimeType = parentType :=
                    object_typeIncludesObjectBool_eq_self schema hobject
                      hparentRuntime
                  have htypeIncludes :
                      schema.typeIncludesObjectBool typeCondition parentType =
                        true := by
                    simpa [doesFragmentTypeApplyBool, runtimeObjectType?,
                      hruntimeEq] using happly
                  have hparentIncludes :
                      schema.typeIncludesObjectBool parentType parentType =
                        true :=
                    NormalForm.object_typeIncludesObjectBool_self schema hobject
                  have hoverlap :
                      schema.typesOverlapBool parentType typeCondition =
                        true := by
                    unfold Schema.typesOverlapBool
                    exact List.any_eq_true.mpr
                      ⟨parentType, List.contains_iff_mem.mp hparentIncludes,
                        htypeIncludes⟩
                  exact hreadyPair.2 hoverlap
                have hrecursive :=
                  collectFields_childSemanticsReady_of_selectionSetSemanticsReady_object
                    schema variableValues parentType runtimeType identity
                    selectionSet hobject hparentRuntime hbodyReady
                simp [GraphQL.Execution.collectSelection, hallows, happly] at hfield
                exact hrecursive field hfield fieldDefinition hlookup
                  childRuntime hinclude
              · have hfalse :
                    doesFragmentTypeApplyBool schema parentType
                      (.object runtimeType identity) typeCondition = false := by
                  cases hmatch :
                      doesFragmentTypeApplyBool schema parentType
                        (.object runtimeType identity) typeCondition
                  · rfl
                  · contradiction
                simp [GraphQL.Execution.collectSelection,
                  collectedExecutableFields, hallows, hfalse] at hfield
            · have hfalse :
                  selectionDirectivesAllowBool variableValues directives =
                    false := by
                cases hmatch :
                    selectionDirectivesAllowBool variableValues directives
                · rfl
                · contradiction
              simp [GraphQL.Execution.collectSelection,
                collectedExecutableFields, hfalse] at hfield

  theorem collectFields_childSemanticsReady_of_selectionSetSemanticsReady_object
      {ObjectIdentity : Type}
      (schema : Schema)
      (variableValues : VariableValues)
      (parentType runtimeType : Name)
      (identity : ObjectIdentity)
      (selectionSet : List Selection)
      : schema.objectType parentType
        -> ScopedParentRuntimeApplies schema runtimeType parentType
        -> NormalForm.selectionSetSemanticsReady schema parentType selectionSet
        -> ∀ field,
            field
              ∈ collectedExecutableFields
                  (GraphQL.Execution.collectFields schema variableValues
                    parentType (.object runtimeType identity) selectionSet)
            -> ∀ fieldDefinition,
                schema.lookupField field.parentType field.fieldName = some fieldDefinition
                -> ∀ childRuntime,
                    schema.typeIncludesObjectBool
                        fieldDefinition.outputType.namedType childRuntime
                      = true
                    -> NormalForm.selectionSetSemanticsReady schema childRuntime
                        field.selectionSet := by
    intro hobject hparentRuntime hready field hfield fieldDefinition hlookup
      childRuntime hinclude
    cases selectionSet with
    | nil =>
        simp [GraphQL.Execution.collectFields, collectedExecutableFields] at hfield
    | cons selection rest =>
        have hheadReady :
            NormalForm.selectionSemanticsReady schema parentType selection := by
          unfold NormalForm.selectionSetSemanticsReady at hready
          exact hready selection (by simp)
        have htailReady :
            NormalForm.selectionSetSemanticsReady schema parentType rest :=
          NormalForm.selectionSetSemanticsReady_tail hready
        have hleft :=
          collectSelection_childSemanticsReady_of_selectionSemanticsReady_object
            schema variableValues parentType runtimeType identity selection
            hobject hparentRuntime hheadReady
        have hright :=
          collectFields_childSemanticsReady_of_selectionSetSemanticsReady_object
            schema variableValues parentType runtimeType identity rest hobject
            hparentRuntime htailReady
        simp [GraphQL.Execution.collectFields] at hfield
        rcases
            (collectedExecutableFields_mem_mergeExecutableGroups
              (GraphQL.Execution.collectSelection schema variableValues
                parentType (.object runtimeType identity) selection)
              (GraphQL.Execution.collectFields schema variableValues parentType
                (.object runtimeType identity) rest)
              field).mp hfield with hselection | hrest
        · exact hleft field hselection fieldDefinition hlookup childRuntime
            hinclude
        · exact hright field hrest fieldDefinition hlookup childRuntime
            hinclude
end

end ExecutionUngrouped
end Algorithms

end GraphQL
