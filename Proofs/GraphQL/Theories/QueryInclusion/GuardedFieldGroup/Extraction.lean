import Proofs.GraphQL.Theories.QueryInclusion.GuardedFieldGroup.Runtime

/-! Extraction provenance for guarded response-field groups. -/

namespace GraphQL
namespace QueryInclusion

open Execution
open Execution.FieldGroups
open SelectionConditions

theorem booleanAssignmentsAgree_refl (variableValues : VariableValues)
    : BooleanAssignmentsAgree variableValues variableValues := by
  intro variableName value hvalue
  exact hvalue

theorem booleanAssignmentsAgree_trans
    {first second third : VariableValues}
    (hfirst : BooleanAssignmentsAgree first second)
    (hsecond : BooleanAssignmentsAgree second third)
    : BooleanAssignmentsAgree first third := by
  intro variableName value hvalue
  exact hsecond variableName value (hfirst variableName value hvalue)

theorem guardedFieldGroups_responseNames_nodup
    (entries : List SelectionConditions.ConditionedField)
    : ((guardedFieldGroups entries).map GuardedFieldGroup.responseName).Nodup := by
  rw [guardedFieldGroups_eq_byFiltering]
  unfold guardedFieldGroupsByFiltering guardedFieldGroupsForNames
  rw [List.map_map]
  change ((entries.map fun entry => entry.field.responseName).eraseDups
    |>.map fun responseName => responseName).Nodup
  simpa using eraseDups_nodup
    (entries.map fun entry => entry.field.responseName)

theorem findGuardedFieldGroup?_some_mem
    {responseName : Name} {groups : List GuardedFieldGroup}
    {group : GuardedFieldGroup}
    (hfind : findGuardedFieldGroup? responseName groups = some group)
    : group ∈ groups ∧ group.responseName = responseName := by
  induction groups with
  | nil => simp [findGuardedFieldGroup?] at hfind
  | cons candidate rest ih =>
      rw [findGuardedFieldGroup?] at hfind
      split at hfind
      · rename_i hname
        injection hfind with heq
        subst group
        exact ⟨by simp, (beq_iff_eq.mp hname).symm⟩
      · rcases ih hfind with ⟨hmember, hname⟩
        exact ⟨by simp [hmember], hname⟩

theorem findGuardedFieldGroup?_eq_some_of_mem_of_nodup
    {groups : List GuardedFieldGroup} {group : GuardedFieldGroup}
    (hnodup : (groups.map GuardedFieldGroup.responseName).Nodup)
    (hmember : group ∈ groups)
    : findGuardedFieldGroup? group.responseName groups = some group := by
  induction groups with
  | nil => simp at hmember
  | cons candidate rest ih =>
      have hparts := List.nodup_cons.mp hnodup
      rcases List.mem_cons.mp hmember with heq | hrest
      · subst candidate
        simp [findGuardedFieldGroup?]
      · have hne : group.responseName ≠ candidate.responseName := by
          intro heq
          apply hparts.1
          exact List.mem_map.mpr ⟨group, hrest, heq⟩
        rw [findGuardedFieldGroup?]
        simp only [beq_iff_eq, hne, if_false]
        exact ih hparts.2 hrest

theorem insertBooleanLiteral_member_source (literal : SelectionConditions.BooleanLiteral)
    (condition inserted : List SelectionConditions.BooleanLiteral)
    (hinsert : SelectionConditions.insertBooleanLiteral literal condition = some inserted)
    {candidate : SelectionConditions.BooleanLiteral} (hmember : candidate ∈ inserted)
    : candidate = literal ∨ candidate ∈ condition := by
  induction condition generalizing inserted with
  | nil =>
      simp [SelectionConditions.insertBooleanLiteral] at hinsert
      subst inserted
      simpa using hmember
  | cons head rest ih =>
      rw [SelectionConditions.insertBooleanLiteral] at hinsert
      split at hinsert
      · injection hinsert with heq
        subst inserted
        exact Or.inr hmember
      · split at hinsert
        · simp at hinsert
        · split at hinsert
          · injection hinsert with heq
            subst inserted
            rcases List.mem_cons.mp hmember with heq | hrest
            · exact Or.inl heq
            · exact Or.inr (by simp [hrest])
          · cases hrecursive : SelectionConditions.insertBooleanLiteral literal rest with
            | none => simp [hrecursive] at hinsert
            | some recursive =>
                simp [hrecursive] at hinsert
                subst inserted
                rcases List.mem_cons.mp hmember with heq | hrecursiveMember
                · exact Or.inr (by simp [heq])
                · rcases ih recursive hrecursive hrecursiveMember with heq | hrest
                  · exact Or.inl heq
                  · exact Or.inr (by simp [hrest])

theorem canonicalBooleanCondition_member_source
    (source canonical : List SelectionConditions.BooleanLiteral)
    (hcanonical : SelectionConditions.canonicalBooleanCondition source = some canonical)
    {literal : SelectionConditions.BooleanLiteral} (hliteral : literal ∈ canonical)
    : literal ∈ source := by
  induction source generalizing canonical with
  | nil =>
      simp [SelectionConditions.canonicalBooleanCondition] at hcanonical
      subst canonical
      simp at hliteral
  | cons head rest ih =>
      rw [SelectionConditions.canonicalBooleanCondition] at hcanonical
      cases hrest : SelectionConditions.canonicalBooleanCondition rest with
      | none => simp [hrest] at hcanonical
      | some restCanonical =>
          cases hinsert : SelectionConditions.insertBooleanLiteral head restCanonical with
          | none => simp [hrest, hinsert] at hcanonical
          | some inserted =>
              simp [hrest, hinsert] at hcanonical
              subst canonical
              rcases insertBooleanLiteral_member_source head restCanonical inserted
                  hinsert hliteral with heq | hrestMember
              · simp [heq]
              · exact List.mem_cons.mpr
                  (Or.inr (ih restCanonical hrest hrestMember))

theorem conditionForBranch?_booleanVariablesWithin
    (schema : Schema) (inherited : List SelectionConditions.BooleanLiteral)
    (variables : List Name) (start target : SelectionConditions.Condition)
    (branch : SelectionConditions.BranchCondition)
    (hstart
      : ∀ literal, literal ∈ start.booleanCondition -> literal.variableName ∈ variables)
    (hbranch : SelectionConditions.BranchCondition.BooleanVariableWithin variables branch)
    (hresult
      : SelectionConditions.conditionForBranch? schema inherited start branch
        = some target)
    : ∀ literal,
        literal ∈ target.booleanCondition -> literal.variableName ∈ variables := by
  intro literal hliteral
  cases branch with
  | typeCondition typeName =>
      simp only [SelectionConditions.conditionForBranch?] at hresult
      split at hresult
      · simp at hresult
      · simp only [Option.some.injEq] at hresult
        subst target
        exact hstart literal hliteral
  | booleanLiteral branchLiteral =>
      simp only [SelectionConditions.conditionForBranch?] at hresult
      cases hcandidate
            : SelectionConditions.canonicalBooleanCondition
                (start.booleanCondition ++ [branchLiteral]) with
      | none => simp [hcandidate] at hresult
      | some candidate =>
          let filtered := candidate.filter fun item => !inherited.contains item
          rw [hcandidate] at hresult
          change (SelectionConditions.canonicalBooleanCondition
              (inherited ++ filtered)).bind
                (fun _globalBooleanCondition =>
                  some { start with booleanCondition := filtered })
            = some target at hresult
          cases hglobal
                : SelectionConditions.canonicalBooleanCondition
                    (inherited ++ filtered) with
          | none => simp [hglobal] at hresult
          | some global =>
              rw [hglobal] at hresult
              simp only [Option.bind_some, Option.some.injEq] at hresult
              subst target
              have hcandidateMember : literal ∈ candidate :=
                (List.mem_filter.mp hliteral).1
              have hsource := canonicalBooleanCondition_member_source
                (start.booleanCondition ++ [branchLiteral]) candidate hcandidate
                  hcandidateMember
              rcases List.mem_append.mp hsource with hstartMember | hbranchMember
              · exact hstart literal hstartMember
              · have heq : literal = branchLiteral := by simpa using hbranchMember
                subst literal
                exact hbranch

theorem conditionForBranches?_booleanVariablesWithin
    (schema : Schema) (inherited : List SelectionConditions.BooleanLiteral)
    (variables : List Name) (start target : SelectionConditions.Condition)
    (branches : List SelectionConditions.BranchCondition)
    (hstart
      : ∀ literal, literal ∈ start.booleanCondition -> literal.variableName ∈ variables)
    (hbranches
      : ∀ branch,
          branch ∈ branches
          -> SelectionConditions.BranchCondition.BooleanVariableWithin variables branch)
    (hresult
      : SelectionConditions.conditionForBranches? schema inherited start branches
        = some target)
    : ∀ literal,
        literal ∈ target.booleanCondition -> literal.variableName ∈ variables := by
  induction branches generalizing start with
  | nil =>
      simp [SelectionConditions.conditionForBranches?] at hresult
      subst target
      exact hstart
  | cons branch rest ih =>
      rw [SelectionConditions.conditionForBranches?] at hresult
      cases hnext
            : SelectionConditions.conditionForBranch? schema inherited start branch with
      | none => simp [hnext] at hresult
      | some next =>
          rw [hnext] at hresult
          exact ih next (conditionForBranch?_booleanVariablesWithin schema inherited
            variables start next branch hstart (hbranches branch (by simp)) hnext)
            (by
              intro candidate hcandidate
              exact hbranches candidate (by simp [hcandidate])) hresult

theorem conditionForBranch?_possibleTypes_subset
    (schema : Schema) (inherited : List SelectionConditions.BooleanLiteral)
    (start target : SelectionConditions.Condition)
    (branch : SelectionConditions.BranchCondition)
    (hresult
      : SelectionConditions.conditionForBranch? schema inherited start branch
        = some target)
    : ∀ runtimeType,
        runtimeType ∈ target.possibleTypes -> runtimeType ∈ start.possibleTypes := by
  intro runtimeType hruntime
  cases branch with
  | typeCondition typeName =>
      simp only [SelectionConditions.conditionForBranch?] at hresult
      split at hresult
      · simp at hresult
      · simp only [Option.some.injEq] at hresult
        subst target
        exact (List.mem_filter.mp hruntime).1
  | booleanLiteral literal =>
      simp only [SelectionConditions.conditionForBranch?] at hresult
      cases hcandidate
            : SelectionConditions.canonicalBooleanCondition
                (start.booleanCondition ++ [literal]) with
      | none => simp [hcandidate] at hresult
      | some candidate =>
          let filtered := candidate.filter fun item => !inherited.contains item
          rw [hcandidate] at hresult
          change (SelectionConditions.canonicalBooleanCondition
              (inherited ++ filtered)).bind
                (fun _globalBooleanCondition =>
                  some { start with booleanCondition := filtered })
            = some target at hresult
          cases hglobal
                : SelectionConditions.canonicalBooleanCondition
                    (inherited ++ filtered) with
          | none => simp [hglobal] at hresult
          | some global =>
              rw [hglobal] at hresult
              simp only [Option.bind_some, Option.some.injEq] at hresult
              subst target
              exact hruntime

theorem conditionForBranches?_possibleTypes_subset
    (schema : Schema) (inherited : List SelectionConditions.BooleanLiteral)
    (start target : SelectionConditions.Condition)
    (branches : List SelectionConditions.BranchCondition)
    (hresult
      : SelectionConditions.conditionForBranches? schema inherited start branches
        = some target)
    : ∀ runtimeType,
        runtimeType ∈ target.possibleTypes -> runtimeType ∈ start.possibleTypes := by
  induction branches generalizing start with
  | nil =>
      simp [SelectionConditions.conditionForBranches?] at hresult
      subst target
      exact fun _ h => h
  | cons branch rest ih =>
      rw [SelectionConditions.conditionForBranches?] at hresult
      cases hnext
            : SelectionConditions.conditionForBranch? schema inherited start branch with
      | none => simp [hnext] at hresult
      | some next =>
          rw [hnext] at hresult
          intro runtimeType hruntime
          exact conditionForBranch?_possibleTypes_subset schema inherited start next
            branch hnext runtimeType (ih next hresult runtimeType hruntime)

theorem extractFields_conditionPossibleTypes_subset
    (schema : Schema)
    (inherited : List SelectionConditions.BooleanLiteral)
    (currentCondition : SelectionConditions.Condition)
    (selectionSet : List Selection) (region : List Name)
    (hcurrent
      : ∀ runtimeType,
          runtimeType ∈ currentCondition.possibleTypes -> runtimeType ∈ region)
    {entry : SelectionConditions.ConditionedField}
    (hentry
      : entry
        ∈ SelectionConditions.extractFields schema inherited currentCondition
            selectionSet)
    {runtimeType : Name} (hruntime : runtimeType ∈ entry.condition.possibleTypes)
    : runtimeType ∈ region := by
  cases selectionSet with
  | nil => simp [SelectionConditions.extractFields] at hentry
  | cons selection rest =>
      cases selection with
      | field responseName fieldName arguments directives childSelectionSet =>
          rw [SelectionConditions.extractFields] at hentry
          cases hbranches
                : SelectionConditions.branchConditionsForDirectives? directives with
          | none =>
              simp [hbranches] at hentry
              exact extractFields_conditionPossibleTypes_subset schema inherited
                currentCondition rest region hcurrent hentry hruntime
          | some branches =>
              cases hnext
                    : SelectionConditions.conditionForBranches? schema inherited
                        currentCondition branches with
              | none =>
                  simp [hbranches, hnext] at hentry
                  exact extractFields_conditionPossibleTypes_subset schema inherited
                    currentCondition rest region hcurrent hentry hruntime
              | some nextCondition =>
                  simp only [hbranches, hnext, List.mem_append,
                    List.mem_singleton] at hentry
                  rcases hentry with hhead | hrest
                  · subst entry
                    exact hcurrent runtimeType
                      (conditionForBranches?_possibleTypes_subset schema inherited
                        currentCondition nextCondition branches hnext runtimeType hruntime)
                  · exact extractFields_conditionPossibleTypes_subset schema inherited
                      currentCondition rest region hcurrent hrest hruntime
      | inlineFragment typeCondition directives childSelectionSet =>
          rw [SelectionConditions.extractFields] at hentry
          cases hbranches
                : SelectionConditions.branchConditionsForInlineFragment?
                    typeCondition directives with
          | none =>
              simp [hbranches] at hentry
              exact extractFields_conditionPossibleTypes_subset schema inherited
                currentCondition rest region hcurrent hentry hruntime
          | some branches =>
              cases hnext
                    : SelectionConditions.conditionForBranches? schema inherited
                        currentCondition branches with
              | none =>
                  simp [hbranches, hnext] at hentry
                  exact extractFields_conditionPossibleTypes_subset schema inherited
                    currentCondition rest region hcurrent hentry hruntime
              | some nextCondition =>
                  simp only [hbranches, hnext, List.mem_append] at hentry
                  rcases hentry with hchild | hrest
                  · exact extractFields_conditionPossibleTypes_subset schema inherited
                      nextCondition childSelectionSet region
                      (fun candidateType hcandidate =>
                        hcurrent candidateType
                          (conditionForBranches?_possibleTypes_subset schema inherited
                            currentCondition nextCondition branches hnext candidateType
                            hcandidate))
                      hchild hruntime
                  · exact extractFields_conditionPossibleTypes_subset schema inherited
                      currentCondition rest region hcurrent hrest hruntime
termination_by SelectionSet.size selectionSet
decreasing_by
  all_goals
    simp_wf
    simp_all [SelectionSet.size, Selection.size]
    omega

theorem extractFields_conditionBooleanVariablesWithin
    (schema : Schema)
    (inherited : List SelectionConditions.BooleanLiteral)
    (currentCondition : SelectionConditions.Condition)
    (selectionSet : List Selection) (variables : List Name)
    (hcurrent
      : ∀ literal,
          literal ∈ currentCondition.booleanCondition -> literal.variableName ∈ variables)
    (hsource
      : ∀ variableName,
          variableName ∈ SelectionConditions.selectionSetBooleanVariables selectionSet
          -> variableName ∈ variables)
    {entry : SelectionConditions.ConditionedField}
    (hentry
      : entry
        ∈ SelectionConditions.extractFields schema inherited currentCondition
            selectionSet)
    {literal : SelectionConditions.BooleanLiteral}
    (hliteral : literal ∈ entry.condition.booleanCondition)
    : literal.variableName ∈ variables := by
  cases selectionSet with
  | nil => simp [SelectionConditions.extractFields] at hentry
  | cons selection rest =>
      cases selection with
      | field responseName fieldName arguments directives childSelectionSet =>
          have hrestVariables :
              ∀ variableName,
                variableName ∈ SelectionConditions.selectionSetBooleanVariables rest
                -> variableName ∈ variables := by
            intro variableName hvariable
            apply hsource variableName
            simp [SelectionConditions.selectionSetBooleanVariables,
              SelectionConditions.selectionBooleanVariables, hvariable]
          rw [SelectionConditions.extractFields] at hentry
          cases hbranches
                : SelectionConditions.branchConditionsForDirectives? directives with
          | none =>
              simp [hbranches] at hentry
              exact extractFields_conditionBooleanVariablesWithin schema inherited
                currentCondition rest variables hcurrent hrestVariables hentry hliteral
          | some branches =>
              cases hnext
                    : SelectionConditions.conditionForBranches? schema inherited
                        currentCondition branches with
              | none =>
                  simp [hbranches, hnext] at hentry
                  exact extractFields_conditionBooleanVariablesWithin schema inherited
                    currentCondition rest variables hcurrent hrestVariables hentry hliteral
              | some nextCondition =>
                  simp only [hbranches, hnext, List.mem_append,
                    List.mem_singleton] at hentry
                  rcases hentry with hhead | hrest
                  · subst entry
                    have hbranchWithin :=
                      SelectionConditions.branchConditionsForDirectives?_within directives
                        branches variables hbranches (by
                          intro variableName hvariable
                          apply hsource variableName
                          simp [SelectionConditions.selectionSetBooleanVariables,
                            SelectionConditions.selectionBooleanVariables, hvariable])
                    exact conditionForBranches?_booleanVariablesWithin schema inherited
                      variables currentCondition nextCondition branches hcurrent
                      (by
                        intro branch hbranch
                        exact hbranchWithin branch hbranch) hnext literal hliteral
                  · exact extractFields_conditionBooleanVariablesWithin schema inherited
                      currentCondition rest variables hcurrent hrestVariables hrest hliteral
      | inlineFragment typeCondition directives childSelectionSet =>
          have hrestVariables :
              ∀ variableName,
                variableName ∈ SelectionConditions.selectionSetBooleanVariables rest
                -> variableName ∈ variables := by
            intro variableName hvariable
            apply hsource variableName
            simp [SelectionConditions.selectionSetBooleanVariables,
              SelectionConditions.selectionBooleanVariables, hvariable]
          rw [SelectionConditions.extractFields] at hentry
          cases hbranches
                : SelectionConditions.branchConditionsForInlineFragment?
                    typeCondition directives with
          | none =>
              simp [hbranches] at hentry
              exact extractFields_conditionBooleanVariablesWithin schema inherited
                currentCondition rest variables hcurrent hrestVariables hentry hliteral
          | some branches =>
              cases hnext
                    : SelectionConditions.conditionForBranches? schema inherited
                        currentCondition branches with
              | none =>
                  simp [hbranches, hnext] at hentry
                  exact extractFields_conditionBooleanVariablesWithin schema inherited
                    currentCondition rest variables hcurrent hrestVariables hentry hliteral
              | some nextCondition =>
                  simp only [hbranches, hnext, List.mem_append] at hentry
                  rcases hentry with hchild | hrest
                  · have hbranchWithin :=
                      SelectionConditions.branchConditionsForInlineFragment?_within
                        typeCondition directives branches variables hbranches (by
                          intro variableName hvariable
                          apply hsource variableName
                          simp [SelectionConditions.selectionSetBooleanVariables,
                            SelectionConditions.selectionBooleanVariables, hvariable])
                    have hnextWithin :=
                      conditionForBranches?_booleanVariablesWithin schema inherited
                        variables currentCondition nextCondition branches hcurrent
                        (by
                          intro branch hbranch
                          exact hbranchWithin branch hbranch) hnext
                    exact extractFields_conditionBooleanVariablesWithin schema inherited
                      nextCondition childSelectionSet variables hnextWithin
                      (by
                        intro variableName hvariable
                        apply hsource variableName
                        simp [SelectionConditions.selectionSetBooleanVariables,
                          SelectionConditions.selectionBooleanVariables, hvariable])
                      hchild hliteral
                  · exact extractFields_conditionBooleanVariablesWithin schema inherited
                      currentCondition rest variables hcurrent hrestVariables hrest hliteral
termination_by SelectionSet.size selectionSet
decreasing_by
  all_goals
    simp_wf
    simp_all [SelectionSet.size, Selection.size]
    omega

theorem conditionedFieldsForResponseName_origin
    (responseName : Name) (entries : List SelectionConditions.ConditionedField)
    {entry : SelectionConditions.ConditionedField}
    (hentry : entry ∈ conditionedFieldsForResponseName responseName entries)
    : entry ∈ entries ∧ entry.field.responseName = responseName := by
  exact ⟨(List.mem_filter.mp hentry).1,
    beq_iff_eq.mp (List.mem_filter.mp hentry).2⟩

theorem guardedFieldGroup_entry_origin
    (entries : List SelectionConditions.ConditionedField)
    {group : GuardedFieldGroup} (hgroup : group ∈ guardedFieldGroups entries)
    {entry : SelectionConditions.ConditionedField} (hentry : entry ∈ group.entries)
    : entry ∈ entries ∧ entry.field.responseName = group.responseName := by
  rw [guardedFieldGroups_eq_byFiltering] at hgroup
  unfold guardedFieldGroupsByFiltering guardedFieldGroupsForNames at hgroup
  rcases List.mem_map.mp hgroup with ⟨responseName, _hname, hgroup⟩
  subst group
  exact conditionedFieldsForResponseName_origin responseName entries hentry

theorem guardedFieldGroupPossibleTypesWithin
    (schema : Schema) (region : List Name) (selectionSet : List Selection)
    (group : GuardedFieldGroup)
    (hgroup
      : group
        ∈ guardedFieldGroups
            (SelectionConditions.ofTypeRegion schema region selectionSet))
    (entry : SelectionConditions.ConditionedField) (hentry : entry ∈ group.entries)
    {runtimeType : Name} (hruntime : runtimeType ∈ entry.condition.possibleTypes)
    : runtimeType ∈ region := by
  have hsource := (guardedFieldGroup_entry_origin
    (SelectionConditions.ofTypeRegion schema region selectionSet) hgroup hentry).1
  let condition : SelectionConditions.Condition :=
    { possibleTypes := region, booleanCondition := [] }
  have hsource' : entry ∈
      SelectionConditions.extractFields schema [] condition selectionSet := by
    simpa [SelectionConditions.ofTypeRegion, condition] using hsource
  apply extractFields_conditionPossibleTypes_subset schema [] condition selectionSet
    region (fun _ h => h) hsource'
  exact hruntime

theorem guardedFieldGroupBooleanVariablesWithinSelectionSets
    (schema : Schema) (region : List Name)
    (leftSelectionSet rightSelectionSet : List Selection)
    (leftGroup : GuardedFieldGroup)
    (hleftGroup
      : leftGroup
        ∈ guardedFieldGroups
            (SelectionConditions.ofTypeRegion schema region leftSelectionSet))
    (rightGroup : GuardedFieldGroup)
    (hrightGroup
      : rightGroup
        ∈ guardedFieldGroups
            (SelectionConditions.ofTypeRegion schema region rightSelectionSet))
    {variableName : Name}
    (hvariable : variableName ∈ guardedFieldGroupBooleanVariables leftGroup rightGroup)
    : variableName ∈ SelectionConditions.selectionSetBooleanVariables leftSelectionSet
      ∨ variableName
        ∈ SelectionConditions.selectionSetBooleanVariables rightSelectionSet := by
  unfold guardedFieldGroupBooleanVariables at hvariable
  have hflat := List.mem_eraseDups.mp hvariable
  rcases List.mem_flatMap.mp hflat with ⟨entry, hentry, hliteral⟩
  rcases List.mem_map.mp hliteral with ⟨literal, hliteralCondition, heq⟩
  subst variableName
  rcases List.mem_append.mp hentry with hleft | hright
  · have hsource := (guardedFieldGroup_entry_origin
      (SelectionConditions.ofTypeRegion schema region leftSelectionSet)
      hleftGroup hleft).1
    apply Or.inl
    let condition : SelectionConditions.Condition :=
      { possibleTypes := region, booleanCondition := [] }
    have hsource' : entry ∈
        SelectionConditions.extractFields schema [] condition leftSelectionSet := by
      simpa [SelectionConditions.ofTypeRegion, condition] using hsource
    apply extractFields_conditionBooleanVariablesWithin schema [] condition
      leftSelectionSet
      (SelectionConditions.selectionSetBooleanVariables leftSelectionSet)
      (by simp [condition]) (fun _ h => h) hsource'
    exact hliteralCondition
  · have hsource := (guardedFieldGroup_entry_origin
      (SelectionConditions.ofTypeRegion schema region rightSelectionSet)
      hrightGroup hright).1
    apply Or.inr
    let condition : SelectionConditions.Condition :=
      { possibleTypes := region, booleanCondition := [] }
    have hsource' : entry ∈
        SelectionConditions.extractFields schema [] condition rightSelectionSet := by
      simpa [SelectionConditions.ofTypeRegion, condition] using hsource
    apply extractFields_conditionBooleanVariablesWithin schema [] condition
      rightSelectionSet
      (SelectionConditions.selectionSetBooleanVariables rightSelectionSet)
      (by simp [condition]) (fun _ h => h) hsource'
    exact hliteralCondition

theorem guardedFieldGroupBooleanVariablesWithinSelectionSet
    (schema : Schema) (region : List Name) (selectionSet : List Selection)
    (group : GuardedFieldGroup)
    (hgroup
      : group
        ∈ guardedFieldGroups
            (SelectionConditions.ofTypeRegion schema region selectionSet))
    {variableName : Name}
    (hvariable
      : variableName
        ∈ group.entries.flatMap
            fun entry =>
              entry.condition.booleanCondition.map
                SelectionConditions.BooleanLiteral.variableName)
    : variableName ∈ SelectionConditions.selectionSetBooleanVariables selectionSet := by
  have hcombined : variableName ∈ guardedFieldGroupBooleanVariables group group := by
    unfold guardedFieldGroupBooleanVariables
    apply List.mem_eraseDups.mpr
    apply List.mem_flatMap.mpr
    rcases List.mem_flatMap.mp hvariable with ⟨entry, hentry, hliteral⟩
    exact ⟨entry, List.mem_append.mpr (Or.inl hentry), hliteral⟩
  exact (guardedFieldGroupBooleanVariablesWithinSelectionSets schema region
    selectionSet selectionSet
    group hgroup group hgroup hcombined).elim id id

end QueryInclusion
end GraphQL
