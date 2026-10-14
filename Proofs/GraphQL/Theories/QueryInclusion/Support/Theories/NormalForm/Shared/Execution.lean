import GraphQL.Theories.QueryInclusion
import Proofs.GraphQL.Theories.QueryInclusion.Support.Theories.SelectionConditions

/-! Supporting lemmas extracted from commit `7797374fd` for the talk exercises. -/

namespace GraphQL.Execution

def mergedFieldSelectionSet : List ExecutableField -> List Selection
  | [] => []
  | field :: rest => field.selectionSet ++ mergedFieldSelectionSet rest

theorem mergedFieldSelectionSet_cons
    (field : ExecutableField) (rest : List ExecutableField)
    : mergedFieldSelectionSet (field :: rest)
      = field.selectionSet ++ mergedFieldSelectionSet rest := by
  rfl

end GraphQL.Execution

namespace GraphQL.NormalForm

def executableGroupNamesNodup : List (Name × List Execution.ExecutableField) -> Prop
  | [] => True
  | (responseName, _fields) :: rest =>
      responseName ∉ rest.map Prod.fst ∧ executableGroupNamesNodup rest

def executableGroupNamesDisjoint
    (left right : List (Name × List Execution.ExecutableField))
    : Prop :=
  ∀ responseName,
    responseName ∈ left.map Prod.fst -> responseName ∈ right.map Prod.fst -> False

theorem addExecutableGroup_mem_responseName
    (group : Name × List Execution.ExecutableField)
    (groups : List (Name × List Execution.ExecutableField))
    (responseName : Name)
    : responseName ∈ (Execution.addExecutableGroup group groups).map Prod.fst
      ↔ responseName = group.fst ∨ responseName ∈ groups.map Prod.fst := by
  induction groups with
  | nil =>
      simp [Execution.addExecutableGroup]
  | cons current rest ih =>
      rcases current with ⟨currentName, fields⟩
      by_cases hname : (currentName == group.fst) = true
      · have hcurrent : currentName = group.fst := beq_iff_eq.mp hname
        subst currentName
        simp [Execution.addExecutableGroup]
      · have hfalse : (currentName == group.fst) = false := by
          cases hmatch : currentName == group.fst
          · rfl
          · contradiction
        have hne : currentName ≠ group.fst := by
          intro heq
          subst currentName
          simp at hfalse
        simp [Execution.addExecutableGroup, hfalse, ih, or_left_comm]

theorem addExecutableGroup_namesNodup
    (group : Name × List Execution.ExecutableField)
    (groups : List (Name × List Execution.ExecutableField))
    : executableGroupNamesNodup groups
      -> executableGroupNamesNodup (Execution.addExecutableGroup group groups) := by
  induction groups with
  | nil =>
      intro _hnodup
      simp [executableGroupNamesNodup, Execution.addExecutableGroup]
  | cons current rest ih =>
      rcases current with ⟨currentName, fields⟩
      intro hnodup
      by_cases hname : (currentName == group.fst) = true
      · have hcurrent : currentName = group.fst := beq_iff_eq.mp hname
        subst currentName
        simpa [Execution.addExecutableGroup, executableGroupNamesNodup] using hnodup
      · have hfalse : (currentName == group.fst) = false := by
          cases hmatch : currentName == group.fst
          · rfl
          · contradiction
        have hne : currentName ≠ group.fst := by
          intro heq
          subst currentName
          simp at hfalse
        have hrest :
            executableGroupNamesNodup rest := by
          exact hnodup.2
        have hadded := ih hrest
        simp [Execution.addExecutableGroup, hfalse]
        constructor
        · intro hmem
          exact hnodup.1
            ((addExecutableGroup_mem_responseName group rest currentName).mp
              hmem
              |>.elim (fun heq => False.elim (hne heq))
                (fun hin => hin))
        · exact hadded

theorem addExecutableGroup_of_responseName_not_mem
    (group : Name × List Execution.ExecutableField)
    (groups : List (Name × List Execution.ExecutableField))
    : group.fst ∉ groups.map Prod.fst
      -> Execution.addExecutableGroup group groups = groups ++ [group] := by
  induction groups with
  | nil =>
      intro _hnotin
      simp [Execution.addExecutableGroup]
  | cons current rest ih =>
      rcases current with ⟨currentName, fields⟩
      intro hnotin
      have hcurrentNe : currentName ≠ group.fst := by
        intro heq
        exact hnotin (by simp [heq])
      have hfalse : (currentName == group.fst) = false := by
        cases hmatch : currentName == group.fst
        · rfl
        · exact False.elim (hcurrentNe (beq_iff_eq.mp hmatch))
      have hrestNotin : group.fst ∉ rest.map Prod.fst := by
        intro hmem
        exact hnotin (by simp [hmem])
      simp [Execution.addExecutableGroup, hfalse, ih hrestNotin]

theorem addExecutableGroup_same_response_append
    (responseName : Name) (currentFields : List Execution.ExecutableField)
    (group : Name × List Execution.ExecutableField)
    (groups : List (Name × List Execution.ExecutableField))
    : group.fst = responseName
      -> Execution.addExecutableGroup group
            (Execution.addExecutableGroup (responseName, currentFields) groups)
          = Execution.addExecutableGroup
              (responseName, currentFields ++ group.snd) groups := by
  intro hname
  induction groups with
  | nil =>
      subst responseName
      simp [Execution.addExecutableGroup]
  | cons current rest ih =>
      rcases current with ⟨currentName, fields⟩
      subst responseName
      by_cases hcurrent : (currentName == group.fst) = true
      · simp [Execution.addExecutableGroup, hcurrent, List.append_assoc]
      · have hfalse : (currentName == group.fst) = false := by
          cases hmatch : currentName == group.fst
          · rfl
          · contradiction
        simpa [Execution.addExecutableGroup, hfalse] using ih

theorem addExecutableGroup_comm_of_responseName_ne_of_mem
    (leftGroup rightGroup : Name × List Execution.ExecutableField)
    (groups : List (Name × List Execution.ExecutableField))
    : leftGroup.fst ≠ rightGroup.fst
      -> leftGroup.fst ∈ groups.map Prod.fst
      -> Execution.addExecutableGroup leftGroup
            (Execution.addExecutableGroup rightGroup groups)
          = Execution.addExecutableGroup rightGroup
              (Execution.addExecutableGroup leftGroup groups) := by
  intro hne hmem
  induction groups with
  | nil =>
      cases hmem
  | cons current rest ih =>
      rcases current with ⟨currentName, currentFields⟩
      rcases leftGroup with ⟨leftName, leftFields⟩
      rcases rightGroup with ⟨rightName, rightFields⟩
      by_cases hcurrentLeft : (currentName == leftName) = true
      · have hcurrentRight : (currentName == rightName) = false := by
          cases hmatch : currentName == rightName
          · rfl
          · have hcl : currentName = leftName := beq_iff_eq.mp hcurrentLeft
            have hcr : currentName = rightName := beq_iff_eq.mp hmatch
            exact False.elim (hne (by rw [← hcl, hcr]))
        simp [Execution.addExecutableGroup, hcurrentLeft, hcurrentRight]
      · have hcurrentLeftFalse : (currentName == leftName) = false := by
          cases hmatch : currentName == leftName
          · rfl
          · contradiction
        by_cases hcurrentRight : (currentName == rightName) = true
        · have hcurrentLeft' : (currentName == leftName) = false :=
            hcurrentLeftFalse
          simp [Execution.addExecutableGroup, hcurrentRight, hcurrentLeft']
        · have hcurrentRightFalse : (currentName == rightName) = false := by
            cases hmatch : currentName == rightName
            · rfl
            · contradiction
          have hrestMem : leftName ∈ rest.map Prod.fst := by
            have hcases :
                leftName = currentName ∨ leftName ∈ rest.map Prod.fst := by
              simpa using hmem
            cases hcases with
            | inl heq =>
                have hneCurrentLeft : currentName ≠ leftName := by
                  intro h
                  subst currentName
                  simp at hcurrentLeftFalse
                exact False.elim (hneCurrentLeft heq.symm)
            | inr hrest => exact hrest
          simp [Execution.addExecutableGroup, hcurrentLeftFalse,
            hcurrentRightFalse, ih hrestMem]

theorem addExecutableGroup_mergeExecutableGroups_of_responseName_not_mem
    (group : Name × List Execution.ExecutableField)
    (left middle : List (Name × List Execution.ExecutableField))
    : group.fst ∉ middle.map Prod.fst
      -> group.fst ∈ left.map Prod.fst
      -> Execution.addExecutableGroup group (Execution.mergeExecutableGroups left middle)
          = Execution.mergeExecutableGroups
              (Execution.addExecutableGroup group left) middle := by
  intro hnotin hleftMem
  induction middle generalizing left with
  | nil =>
      simp [Execution.mergeExecutableGroups]
  | cons current rest ih =>
      rcases current with ⟨currentName, currentFields⟩
      have hcurrentNe : currentName ≠ group.fst := by
        intro heq
        exact hnotin (by simp [heq])
      have hrestNotin : group.fst ∉ rest.map Prod.fst := by
        intro hmem
        exact hnotin (by simp [hmem])
      simp [Execution.mergeExecutableGroups]
      change Execution.addExecutableGroup group
          (Execution.mergeExecutableGroups
            (Execution.addExecutableGroup (currentName, currentFields) left)
            rest)
        =
        Execution.mergeExecutableGroups
          (Execution.addExecutableGroup (currentName, currentFields)
            (Execution.addExecutableGroup group left)) rest
      have hleftMem' :
          group.fst ∈
            (Execution.addExecutableGroup (currentName, currentFields)
              left).map Prod.fst := by
        exact (addExecutableGroup_mem_responseName
          (currentName, currentFields) left group.fst).mpr
          (Or.inr hleftMem)
      rw [ih (Execution.addExecutableGroup (currentName, currentFields) left)
        hrestNotin hleftMem']
      rw [addExecutableGroup_comm_of_responseName_ne_of_mem
        group (currentName, currentFields) left (by
          intro heq
          exact hcurrentNe heq.symm) hleftMem]

theorem addExecutableGroup_mergeExecutableGroups_of_namesNodup
    (group : Name × List Execution.ExecutableField)
    (left middle : List (Name × List Execution.ExecutableField))
    : executableGroupNamesNodup middle
      -> Execution.addExecutableGroup group (Execution.mergeExecutableGroups left middle)
          = Execution.mergeExecutableGroups left
              (Execution.addExecutableGroup group middle) := by
  intro hmiddle
  induction middle generalizing left with
  | nil =>
      simp [Execution.mergeExecutableGroups, Execution.addExecutableGroup]
  | cons current rest ih =>
      rcases current with ⟨currentName, currentFields⟩
      by_cases hname : (currentName == group.fst) = true
      · simp [Execution.mergeExecutableGroups, Execution.addExecutableGroup,
          hname]
        have hkey : group.fst = currentName := (beq_iff_eq.mp hname).symm
        have hnotin : group.fst ∉ rest.map Prod.fst := by
          intro hmem
          exact hmiddle.1 (by simpa [hkey] using hmem)
        change Execution.addExecutableGroup group
            (Execution.mergeExecutableGroups
              (Execution.addExecutableGroup (currentName, currentFields)
                left) rest)
          =
          Execution.mergeExecutableGroups
            (Execution.addExecutableGroup
              (currentName, currentFields ++ group.snd) left) rest
        rw [addExecutableGroup_mergeExecutableGroups_of_responseName_not_mem
          group
          (Execution.addExecutableGroup (currentName, currentFields) left)
          rest hnotin
          ((addExecutableGroup_mem_responseName
            (currentName, currentFields) left group.fst).mpr
            (Or.inl hkey))]
        rw [addExecutableGroup_same_response_append currentName currentFields
          group left hkey]
      · have hfalse : (currentName == group.fst) = false := by
          cases hmatch : currentName == group.fst
          · rfl
          · contradiction
        simp [Execution.mergeExecutableGroups, Execution.addExecutableGroup,
          hfalse]
        exact ih (Execution.addExecutableGroup (currentName, currentFields)
          left) hmiddle.2

theorem mergeExecutableGroups_assoc_of_namesNodup
    (left middle right : List (Name × List Execution.ExecutableField))
    : executableGroupNamesNodup middle
      -> executableGroupNamesNodup right
      -> Execution.mergeExecutableGroups
            (Execution.mergeExecutableGroups left middle) right
          = Execution.mergeExecutableGroups left
              (Execution.mergeExecutableGroups middle right) := by
  intro hmiddle hright
  induction right generalizing left middle with
  | nil =>
      simp [Execution.mergeExecutableGroups]
  | cons group rest ih =>
      change Execution.mergeExecutableGroups
          (Execution.addExecutableGroup group
            (Execution.mergeExecutableGroups left middle)) rest
        =
        Execution.mergeExecutableGroups left
          (Execution.mergeExecutableGroups
            (Execution.addExecutableGroup group middle) rest)
      rw [addExecutableGroup_mergeExecutableGroups_of_namesNodup group left
        middle hmiddle]
      exact ih left (Execution.addExecutableGroup group middle)
        (addExecutableGroup_namesNodup group middle hmiddle)
        hright.2

theorem mergeExecutableGroups_eq_append_of_namesDisjoint
    (left right : List (Name × List Execution.ExecutableField))
    : executableGroupNamesDisjoint left right
      -> executableGroupNamesNodup right
      -> Execution.mergeExecutableGroups left right = left ++ right := by
  induction right generalizing left with
  | nil =>
      intro _hdisjoint _hnodup
      simp [Execution.mergeExecutableGroups]
  | cons group rest ih =>
      rcases group with ⟨responseName, fields⟩
      intro hdisjoint hnodup
      have hnotinLeft : responseName ∉ left.map Prod.fst := by
        intro hmem
        exact hdisjoint responseName hmem (by simp)
      have hrestNodup : executableGroupNamesNodup rest := hnodup.2
      have hrestDisjoint :
          executableGroupNamesDisjoint (left ++ [(responseName, fields)])
            rest := by
        intro name hleft hright
        have hleftCases :
            name ∈ left.map Prod.fst ∨ name = responseName := by
          simpa using hleft
        cases hleftCases with
        | inl hleftMem =>
            exact hdisjoint name hleftMem (by simp [hright])
        | inr hname =>
            subst name
            exact hnodup.1 hright
      simp [Execution.mergeExecutableGroups,
        addExecutableGroup_of_responseName_not_mem (responseName, fields)
          left hnotinLeft]
      change Execution.mergeExecutableGroups
          (left ++ [(responseName, fields)]) rest
        = left ++ (responseName, fields) :: rest
      rw [ih (left ++ [(responseName, fields)]) hrestDisjoint hrestNodup]
      simp [List.append_assoc]

theorem mergeExecutableGroups_nil_left_of_namesNodup
    (groups : List (Name × List Execution.ExecutableField))
    : executableGroupNamesNodup groups
      -> Execution.mergeExecutableGroups [] groups = groups := by
  intro hnodup
  simpa using
    mergeExecutableGroups_eq_append_of_namesDisjoint [] groups
      (by
        intro responseName hleft _hright
        cases hleft)
      hnodup

theorem mergeExecutableGroups_namesNodup
    (left right : List (Name × List Execution.ExecutableField))
    : executableGroupNamesNodup left
      -> executableGroupNamesNodup (Execution.mergeExecutableGroups left right) := by
  induction right generalizing left with
  | nil =>
      intro hleft
      exact hleft
  | cons group rest ih =>
      intro hleft
      simp [Execution.mergeExecutableGroups]
      exact ih (Execution.addExecutableGroup group left)
        (addExecutableGroup_namesNodup group left hleft)

mutual
  theorem collectSelection_namesNodup
      (schema : Schema) (variableValues : Execution.VariableValues)
      (parentType : Name)
      (source : Execution.ResolverValue ObjectRef)
      (selection : Selection)
      : executableGroupNamesNodup
          (Execution.collectSelection schema variableValues parentType source
            selection) := by
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        by_cases hallows :
            Execution.selectionDirectivesAllowBool variableValues directives = true
        · simp [Execution.collectSelection, hallows,
            executableGroupNamesNodup]
        · have hfalse :
              Execution.selectionDirectivesAllowBool variableValues directives =
                false := by
            cases hmatch :
                Execution.selectionDirectivesAllowBool variableValues directives
            · rfl
            · contradiction
          simp [Execution.collectSelection, hfalse,
            executableGroupNamesNodup]
    | inlineFragment typeCondition directives selectionSet =>
        cases typeCondition with
        | none =>
            by_cases hallows :
                Execution.selectionDirectivesAllowBool variableValues directives =
                  true
            · simp [Execution.collectSelection, hallows]
              exact collectFields_namesNodup schema variableValues parentType
                source selectionSet
            · have hfalse :
                  Execution.selectionDirectivesAllowBool variableValues
                    directives = false := by
                cases hmatch :
                    Execution.selectionDirectivesAllowBool variableValues
                      directives
                · rfl
                · contradiction
              simp [Execution.collectSelection, hfalse,
                executableGroupNamesNodup]
        | some typeCondition =>
            by_cases hallows :
                Execution.selectionDirectivesAllowBool variableValues directives =
                  true
            · by_cases happly :
                Execution.doesFragmentTypeApplyBool schema parentType source
                  typeCondition = true
              · simp [Execution.collectSelection, hallows, happly]
                exact collectFields_namesNodup schema variableValues parentType
                  source selectionSet
              · have hfalse :
                    Execution.doesFragmentTypeApplyBool schema parentType source
                      typeCondition = false := by
                  cases hmatch :
                      Execution.doesFragmentTypeApplyBool schema parentType
                        source typeCondition
                  · rfl
                  · contradiction
                simp [Execution.collectSelection, hallows, hfalse,
                  executableGroupNamesNodup]
            · have hfalse :
                  Execution.selectionDirectivesAllowBool variableValues
                    directives = false := by
                cases hmatch :
                    Execution.selectionDirectivesAllowBool variableValues
                      directives
                · rfl
                · contradiction
              simp [Execution.collectSelection, hfalse,
                executableGroupNamesNodup]

  theorem collectFields_namesNodup
      (schema : Schema) (variableValues : Execution.VariableValues)
      (parentType : Name)
      (source : Execution.ResolverValue ObjectRef)
      (selectionSet : List Selection)
      : executableGroupNamesNodup
          (Execution.collectFields schema variableValues parentType source
            selectionSet) := by
    cases selectionSet with
    | nil =>
        simp [Execution.collectFields, executableGroupNamesNodup]
    | cons selection rest =>
        simp [Execution.collectFields]
        exact mergeExecutableGroups_namesNodup
          (Execution.collectSelection schema variableValues parentType source
            selection)
          (Execution.collectFields schema variableValues parentType source rest)
          (collectSelection_namesNodup schema variableValues parentType source
            selection)
end

theorem collectFields_append
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (left right : List Selection)
    : Execution.collectFields schema variableValues parentType source (left ++ right)
      = Execution.mergeExecutableGroups
          (Execution.collectFields schema variableValues parentType source left)
          (Execution.collectFields schema variableValues parentType source right) := by
  induction left with
  | nil =>
      simp [Execution.collectFields]
      rw [mergeExecutableGroups_nil_left_of_namesNodup
        (Execution.collectFields schema variableValues parentType source right)
        (collectFields_namesNodup schema variableValues parentType source
          right)]
  | cons selection rest ih =>
      simp [Execution.collectFields, ih]
      rw [mergeExecutableGroups_assoc_of_namesNodup]
      · exact collectFields_namesNodup schema variableValues parentType source
          rest
      · exact collectFields_namesNodup schema variableValues parentType source
          right

theorem collectSubfields_eq_collectFields_mergedFieldSelectionSet
    (schema : Schema) (variableValues : Execution.VariableValues)
    (objectType : Name)
    (objectValue : Execution.ResolverValue ObjectRef)
    (fields : List Execution.ExecutableField)
    : Execution.collectSubfields schema variableValues objectType objectValue fields
      = Execution.collectFields schema variableValues objectType objectValue
          (Execution.mergedFieldSelectionSet fields) := by
  induction fields with
  | nil =>
      simp [Execution.collectSubfields, Execution.mergedFieldSelectionSet,
        Execution.collectFields]
  | cons field rest ih =>
      simp [Execution.collectSubfields, Execution.mergedFieldSelectionSet, ih]
      rw [collectFields_append]

end GraphQL.NormalForm
