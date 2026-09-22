import Proofs.GraphQL.Theories.QueryInclusion.GuardedFieldGroup.GroupCheck
import Proofs.GraphQL.Theories.QueryInclusion.SyntacticShortcut

/-! Semantic correctness of guarded field-group query inclusion. -/

namespace GraphQL
namespace QueryInclusion

open Execution
open Execution.FieldGroups
open SelectionConditions
open ConditionTree

theorem booleanAssignmentsAgree_cons_both
    {sourceValues targetValues : VariableValues} {variableName : Name} {value : Bool}
    (hagrees : BooleanAssignmentsAgree sourceValues targetValues)
    : BooleanAssignmentsAgree
        ((variableName, .boolean value) :: sourceValues)
        ((variableName, .boolean value) :: targetValues) := by
  intro candidate candidateValue hcandidate
  by_cases heq : variableName = candidate
  · subst candidate
    simpa [inputValueBoolean?, lookupVariableValue?] using hcandidate
  · simp [inputValueBoolean?, lookupVariableValue?, heq] at hcandidate ⊢
    exact hagrees candidate candidateValue hcandidate

mutual
  theorem guardedFieldGroupIncludesWithFuel_specialize
      (schema : Schema) (responseFuel : Nat)
      (fixedExecutionParentType : Option Name)
      (sourceValues targetValues : VariableValues)
      (remainingBooleanVariables : List Name)
      (parentRegion : List Name) (left right : GuardedFieldGroup)
      (hcheck
        : guardedFieldGroupIncludesWithFuel schema responseFuel
            fixedExecutionParentType sourceValues remainingBooleanVariables left right
            (guardedFieldGroupTypeRegions parentRegion left right)
          = true)
      (hagrees : BooleanAssignmentsAgree sourceValues targetValues)
      (hcovered
        : BooleanVariablesCovered sourceValues remainingBooleanVariables
            (guardedFieldGroupBooleanVariables left right))
      (hremainingWithin
        : ∀ variableName,
            variableName ∈ remainingBooleanVariables
            -> variableName ∈ guardedFieldGroupBooleanVariables left right)
      : guardedFieldGroupIncludesWithFuel schema responseFuel
          fixedExecutionParentType targetValues remainingBooleanVariables left right
          (guardedFieldGroupTypeRegions parentRegion left right)
        = true := by
    cases hremaining : remainingBooleanVariables with
    | cons variableName rest =>
        have hrestSmaller : rest.length < remainingBooleanVariables.length := by
          rw [hremaining]
          simp
        simp only [hremaining] at hcovered hremainingWithin
        rw [guardedFieldGroupIncludesWithFuel.eq_def] at hcheck ⊢
        simp only [hremaining] at hcheck ⊢
        cases hsource : inputValueBoolean? sourceValues (.variable variableName) with
        | some value =>
            have htarget := hagrees variableName value hsource
            simp only [hsource] at hcheck
            simp only [htarget]
            exact guardedFieldGroupIncludesWithFuel_specialize schema responseFuel
              fixedExecutionParentType sourceValues targetValues rest parentRegion left
              right hcheck hagrees
              (booleanVariablesCovered_tail_of_known hcovered ⟨value, hsource⟩)
              (by
                intro candidate hcandidate
                exact hremainingWithin candidate (by simp [hcandidate]))
        | none =>
            have hbranches :
                guardedFieldGroupIncludesWithFuel schema responseFuel
                    fixedExecutionParentType
                    ((variableName, .boolean false) :: sourceValues) rest left right
                    (guardedFieldGroupTypeRegions parentRegion left right) = true
                  ∧ guardedFieldGroupIncludesWithFuel schema responseFuel
                    fixedExecutionParentType
                    ((variableName, .boolean true) :: sourceValues) rest left right
                    (guardedFieldGroupTypeRegions parentRegion left right) = true := by
              simpa [hsource, Bool.and_eq_true] using hcheck
            cases htarget : inputValueBoolean? targetValues (.variable variableName) with
            | none =>
                simp only [Bool.and_eq_true]
                constructor
                · exact guardedFieldGroupIncludesWithFuel_specialize schema
                    responseFuel fixedExecutionParentType
                    ((variableName, .boolean false) :: sourceValues)
                    ((variableName, .boolean false) :: targetValues) rest parentRegion
                    left right hbranches.1
                    (booleanAssignmentsAgree_cons_both hagrees)
                    (booleanVariablesCovered_tail_of_cons hcovered)
                    (by
                      intro candidate hcandidate
                      exact hremainingWithin candidate (by simp [hcandidate]))
                · exact guardedFieldGroupIncludesWithFuel_specialize schema
                    responseFuel fixedExecutionParentType
                    ((variableName, .boolean true) :: sourceValues)
                    ((variableName, .boolean true) :: targetValues) rest parentRegion
                    left right hbranches.2
                    (booleanAssignmentsAgree_cons_both hagrees)
                    (booleanVariablesCovered_tail_of_cons hcovered)
                    (by
                      intro candidate hcandidate
                      exact hremainingWithin candidate (by simp [hcandidate]))
            | some value =>
                simp only
                cases value with
                | false =>
                    exact guardedFieldGroupIncludesWithFuel_specialize schema
                      responseFuel fixedExecutionParentType
                      ((variableName, .boolean false) :: sourceValues) targetValues rest
                      parentRegion left right hbranches.1
                      (booleanAssignmentsAgree_cons hagrees htarget)
                      (booleanVariablesCovered_tail_of_cons hcovered)
                      (by
                        intro candidate hcandidate
                        exact hremainingWithin candidate (by simp [hcandidate]))
                | true =>
                    exact guardedFieldGroupIncludesWithFuel_specialize schema
                      responseFuel fixedExecutionParentType
                      ((variableName, .boolean true) :: sourceValues) targetValues rest
                      parentRegion left right hbranches.2
                      (booleanAssignmentsAgree_cons hagrees htarget)
                      (booleanVariablesCovered_tail_of_cons hcovered)
                      (by
                        intro candidate hcandidate
                        exact hremainingWithin candidate (by simp [hcandidate]))
    | nil =>
        simp only [hremaining] at hcovered hremainingWithin
        rw [guardedFieldGroupIncludesWithFuel.eq_def] at hcheck ⊢
        simp only [hremaining] at hcheck ⊢
        rw [guardedFieldGroupIncludesForRegionsWithFuel] at hcheck ⊢
        apply List.all_eq_true.mpr
        intro region hregion
        have hregionCheck := List.all_eq_true.mp hcheck region hregion
        cases region with
        | nil => simp
        | cons runtimeType rest =>
            let sourceLeftFields := guardedFieldExecutableFields sourceValues
              runtimeType left.entries
            let sourceRightFields := guardedFieldExecutableFields sourceValues
              runtimeType right.entries
            let targetLeftFields := guardedFieldExecutableFields targetValues
              runtimeType left.entries
            let targetRightFields := guardedFieldExecutableFields targetValues
              runtimeType right.entries
            have hvariableAgreement : ∀ variableName,
                variableName ∈ guardedFieldGroupBooleanVariables left right
                -> inputValueBoolean? sourceValues (.variable variableName)
                    = inputValueBoolean? targetValues (.variable variableName) := by
              intro variableName hvariable
              rcases hcovered variableName hvariable with hremaining | hknown
              · simp at hremaining
              · rcases hknown with ⟨value, hvalue⟩
                exact hvalue.trans (hagrees variableName value hvalue).symm
            have hleftFields : sourceLeftFields = targetLeftFields := by
              unfold sourceLeftFields targetLeftFields
              exact guardedFieldExecutableFields_eq_of_region_and_variables
                parentRegion left right left (Or.inl rfl)
                (region := runtimeType :: rest) hregion
                (leftRuntimeType := runtimeType) (rightRuntimeType := runtimeType)
                (by simp) (by simp) hvariableAgreement
            have hrightFields : sourceRightFields = targetRightFields := by
              unfold sourceRightFields targetRightFields
              exact guardedFieldExecutableFields_eq_of_region_and_variables
                parentRegion left right right (Or.inr rfl)
                (region := runtimeType :: rest) hregion
                (leftRuntimeType := runtimeType) (rightRuntimeType := runtimeType)
                (by simp) (by simp) hvariableAgreement
            cases responseFuel with
            | zero =>
                change sourceRightFields.isEmpty = true at hregionCheck
                change targetRightFields.isEmpty = true
                rw [← hrightFields]
                exact hregionCheck
            | succ responseFuel =>
                let parentTypes :=
                  match fixedExecutionParentType with
                  | some parentType => [parentType]
                  | none => runtimeType :: rest
                let sourceLeftGroups := executableFieldsAsGroup left.responseName
                  sourceLeftFields
                let sourceRightGroups := executableFieldsAsGroup right.responseName
                  sourceRightFields
                let targetLeftGroups := executableFieldsAsGroup left.responseName
                  targetLeftFields
                let targetRightGroups := executableFieldsAsGroup right.responseName
                  targetRightFields
                change
                  (match inclusionChildTasksForParentTypes? schema sourceLeftGroups
                      sourceRightGroups parentTypes with
                    | none => false
                    | some tasks => tasks.all fun task =>
                        guardedFieldChildIncludesBool schema responseFuel sourceValues
                          task.possibleTypes task.leftSelectionSet
                          task.rightSelectionSet) = true at hregionCheck
                change (match inclusionChildTasksForParentTypes? schema targetLeftGroups
                                targetRightGroups parentTypes with
                        | none => false
                        | some tasks =>
                            tasks.all
                              fun task =>
                                guardedFieldChildIncludesBool schema responseFuel
                                  targetValues task.possibleTypes task.leftSelectionSet
                                  task.rightSelectionSet)
                        = true
                have hleftGroups : sourceLeftGroups = targetLeftGroups := by
                  unfold sourceLeftGroups targetLeftGroups
                  rw [hleftFields]
                have hrightGroups : sourceRightGroups = targetRightGroups := by
                  unfold sourceRightGroups targetRightGroups
                  rw [hrightFields]
                rw [← hleftGroups, ← hrightGroups]
                cases htasks
                      : inclusionChildTasksForParentTypes? schema sourceLeftGroups
                          sourceRightGroups parentTypes with
                | none => simp [htasks] at hregionCheck
                | some tasks =>
                    simp only [htasks] at hregionCheck ⊢
                    apply List.all_eq_true.mpr
                    intro task htask
                    have hchildCheck := List.all_eq_true.mp hregionCheck task htask
                    unfold guardedFieldChildIncludesBool at hchildCheck ⊢
                    cases hshortcut
                          : selectionSetSyntacticInclusionShortcutBool responseFuel
                              task.leftSelectionSet task.rightSelectionSet with
                    | false =>
                        simp only [hshortcut, Bool.false_or] at hchildCheck ⊢
                        exact guardedFieldGroupsIncludeWithFuel_specialize schema
                          responseFuel none sourceValues targetValues
                          (guardedFieldGroups (SelectionConditions.ofTypeRegion schema
                            task.possibleTypes task.leftSelectionSet))
                          (guardedFieldGroups (SelectionConditions.ofTypeRegion schema
                            task.possibleTypes task.rightSelectionSet))
                          hchildCheck hagrees
                    | true => simp
  termination_by (responseFuel, 0, remainingBooleanVariables.length)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | apply Prod.Lex.left; omega
      | apply Prod.Lex.right; apply Prod.Lex.left; omega
      | apply Prod.Lex.right; apply Prod.Lex.right; exact hrestSmaller

  theorem guardedFieldGroupSymbolicallyIncludesWithFuel_specialize
      (schema : Schema) (responseFuel : Nat)
      (fixedExecutionParentType : Option Name)
      (sourceValues targetValues : VariableValues)
      (left right : GuardedFieldGroup) (regions : List (List Name))
      (hcheck
        : guardedFieldGroupSymbolicallyIncludesWithFuel schema responseFuel
            fixedExecutionParentType sourceValues left right regions
          = true)
      (hagrees : BooleanAssignmentsAgree sourceValues targetValues)
      : guardedFieldGroupSymbolicallyIncludesWithFuel schema responseFuel
          fixedExecutionParentType targetValues left right regions
        = true := by
    cases responseFuel with
    | zero =>
        simp [guardedFieldGroupSymbolicallyIncludesWithFuel] at hcheck
    | succ childFuel =>
        rw [guardedFieldGroupSymbolicallyIncludesWithFuel] at hcheck ⊢
        apply List.all_eq_true.mpr
        intro region hregion
        have hregionCheck := List.all_eq_true.mp hcheck region hregion
        apply List.all_eq_true.mpr
        intro runtimeType hruntime
        have hruntimeCheck := List.all_eq_true.mp hregionCheck runtimeType hruntime
        let rightEntries := guardedFieldEntriesAtRuntimeType runtimeType right.entries
        cases hrightEntries : rightEntries with
        | nil =>
            simpa [guardedFieldGroupSymbolicallyIncludesAtRuntimeTypeBool,
              rightEntries, hrightEntries] using hruntimeCheck
        | cons rightHead rightRest =>
            simp only [guardedFieldGroupSymbolicallyIncludesAtRuntimeTypeBool,
              rightEntries, hrightEntries, Bool.and_eq_true] at hruntimeCheck ⊢
            constructor
            · exact hruntimeCheck.1
            · constructor
              · exact hruntimeCheck.2.1
              · apply List.all_eq_true.mpr
                intro executionParentType hparent
                have hparentCheck := List.all_eq_true.mp hruntimeCheck.2.2
                  executionParentType hparent
                cases hdefinition
                      : schema.lookupField executionParentType
                          rightHead.field.fieldName with
                | none => simp [hdefinition] at hparentCheck
                | some definition =>
                    simp only [hdefinition, Bool.and_eq_true] at hparentCheck ⊢
                    refine ⟨hparentCheck.1, ?_⟩
                    exact guardedFieldGroupsIncludeWithFuel_specialize schema
                      childFuel none sourceValues targetValues
                      (guardedFieldGroups
                        (SelectionConditions.ofTypeRegionUnder schema
                          (schema.getPossibleTypes definition.outputType.namedType)
                          (guardedFieldChildContributions
                            (guardedFieldEntriesAtRuntimeType runtimeType
                              left.entries))))
                      (guardedFieldGroups
                        (SelectionConditions.ofTypeRegionUnder schema
                          (schema.getPossibleTypes definition.outputType.namedType)
                          (guardedFieldChildContributions
                            (rightHead :: rightRest))))
                      hparentCheck.2 hagrees
  termination_by (responseFuel, 1, 0)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | apply Prod.Lex.left <;> omega
      | apply Prod.Lex.right; apply Prod.Lex.left <;> omega
      | apply Prod.Lex.right; apply Prod.Lex.right <;> omega

  theorem guardedFieldGroupsIncludeWithFuel_specialize
      (schema : Schema) (responseFuel : Nat)
      (fixedExecutionParentType : Option Name)
      (sourceValues targetValues : VariableValues)
      (leftGroups rightGroups : List GuardedFieldGroup)
      (hcheck
        : guardedFieldGroupsIncludeWithFuel schema responseFuel
            fixedExecutionParentType sourceValues leftGroups rightGroups
          = true)
      (hagrees : BooleanAssignmentsAgree sourceValues targetValues)
      : guardedFieldGroupsIncludeWithFuel schema responseFuel
          fixedExecutionParentType targetValues leftGroups rightGroups
        = true := by
    cases hgroups : rightGroups with
    | nil => simp [guardedFieldGroupsIncludeWithFuel]
    | cons right rest =>
        have hrestSmaller : rest.length < rightGroups.length := by
          rw [hgroups]
          simp
        rw [guardedFieldGroupsIncludeWithFuel.eq_def] at hcheck ⊢
        simp only [hgroups] at hcheck ⊢
        simp only [Bool.and_eq_true] at hcheck ⊢
        simp only [Bool.or_eq_true] at hcheck ⊢
        constructor
        · rcases hcheck.1 with hfast | hgeneral
          · rcases hfast with hshortcut | hsymbolic
            · exact Or.inl (Or.inl hshortcut)
            · apply Or.inl
              apply Or.inr
              simp only [Bool.and_eq_true] at hsymbolic ⊢
              refine ⟨hsymbolic.1, ?_⟩
              let left := guardedFieldGroupFor leftGroups right
              apply guardedFieldGroupSymbolicallyIncludesWithFuel_specialize schema
                responseFuel fixedExecutionParentType sourceValues targetValues left
                right
              · simpa [left, guardedFieldGroupFor, guardedFieldParentRegion]
                  using hsymbolic.2
              · exact hagrees
          · apply Or.inr
            let left := guardedFieldGroupFor leftGroups right
            apply guardedFieldGroupIncludesWithFuel_specialize schema responseFuel
              fixedExecutionParentType sourceValues targetValues
              (guardedFieldGroupBooleanVariables left right)
              (guardedFieldParentRegion schema fixedExecutionParentType left right)
              left right
            · unfold left guardedFieldGroupFor guardedFieldParentRegion
              exact hgeneral
            · exact hagrees
            · intro variableName hvariable
              exact Or.inl hvariable
            · intro variableName hvariable
              exact hvariable
        · exact guardedFieldGroupsIncludeWithFuel_specialize schema responseFuel
            fixedExecutionParentType sourceValues targetValues leftGroups rest
            hcheck.2 hagrees
  termination_by (responseFuel, 2, rightGroups.length)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | apply Prod.Lex.left; omega
      | apply Prod.Lex.right; apply Prod.Lex.left; omega
      | apply Prod.Lex.right; apply Prod.Lex.right; exact hrestSmaller
end

def activeContributionSelectionSet (variableValues : VariableValues)
    (contributions : List (List BooleanLiteral × List Selection))
    : List Selection :=
  contributions.flatMap
    fun (condition, selectionSet) =>
      if booleanConditionAllows variableValues condition then selectionSet else []

theorem collectFlatFields_append_local {ObjectRef : Type} (schema : Schema)
    (variableValues : VariableValues) (parentType : Name) (source : ResolverValue ObjectRef)
    (left right : List Selection)
    : collectFlatFields schema variableValues parentType source (left ++ right)
      = collectFlatFields schema variableValues parentType source left
        ++ collectFlatFields schema variableValues parentType source right := by
  induction left with
  | nil => rfl
  | cons selection rest ih =>
      simp [collectFlatFields, ih, List.append_assoc]

theorem runtimeFields_ofTypeRegionUnder
    {ObjectRef : Type} (schema : Schema) (variableValues : VariableValues)
    (executionParentType runtimeType : Name) (ref : ObjectRef) (region : List Name)
    (contributions : List (List BooleanLiteral × List Selection))
    (hruntime : runtimeType ∈ region)
    : runtimeFields variableValues runtimeType
        (SelectionConditions.ofTypeRegionUnder schema region contributions)
      = collectFlatFields schema variableValues executionParentType
          (.object runtimeType ref)
          (activeContributionSelectionSet variableValues contributions) := by
  induction contributions with
  | nil => simp [SelectionConditions.ofTypeRegionUnder,
      activeContributionSelectionSet, runtimeFields, collectFlatFields]
  | cons contribution rest ih =>
      rcases contribution with ⟨condition, selectionSet⟩
      change runtimeFields variableValues runtimeType
          (extractFields schema []
              { possibleTypes := region, booleanCondition := condition } selectionSet
            ++ SelectionConditions.ofTypeRegionUnder schema region rest)
        = _
      rw [runtimeFields_append]
      have hsource := SelectionConditions.extractFields_runtimeFields schema
        variableValues executionParentType runtimeType ref []
        ({ possibleTypes := region, booleanCondition := condition } : Condition)
        selectionSet (by simp [booleanConditionAllows])
      have hpossible : region.contains runtimeType = true :=
        List.contains_iff_mem.mpr hruntime
      simp only [Condition.allows, hpossible, Bool.true_and] at hsource
      rw [hsource, ih]
      change (if booleanConditionAllows variableValues condition then
          collectFlatFields schema variableValues executionParentType
            (.object runtimeType ref) selectionSet
        else [])
        ++ collectFlatFields schema variableValues executionParentType
            (.object runtimeType ref)
            (activeContributionSelectionSet variableValues rest)
        = collectFlatFields schema variableValues executionParentType
            (.object runtimeType ref)
            ((if booleanConditionAllows variableValues condition then
                selectionSet else [])
              ++ activeContributionSelectionSet variableValues rest)
      cases hallows : booleanConditionAllows variableValues condition <;>
        simp [collectFlatFields_append_local]

theorem activeContributionSelectionSet_guardedFieldChildContributions
    (variableValues : VariableValues) (runtimeType : Name)
    (entries : List SelectionConditions.ConditionedField)
    (hpossible : ∀ entry, entry ∈ entries -> runtimeType ∈ entry.condition.possibleTypes)
    : activeContributionSelectionSet variableValues
        (guardedFieldChildContributions entries)
      = executableFieldsMergedSelectionSet
          (guardedFieldExecutableFields variableValues runtimeType entries) := by
  induction entries with
  | nil => simp [activeContributionSelectionSet, guardedFieldChildContributions,
      executableFieldsMergedSelectionSet, guardedFieldExecutableFields]
  | cons entry rest ih =>
      have hhead := hpossible entry (by simp)
      have htail : ∀ candidate, candidate ∈ rest ->
          runtimeType ∈ candidate.condition.possibleTypes := by
        intro candidate hcandidate
        exact hpossible candidate (by simp [hcandidate])
      have ih := ih htail
      have hcontains : entry.condition.possibleTypes.contains runtimeType = true :=
        List.contains_iff_mem.mpr hhead
      change (if booleanConditionAllows variableValues
            entry.condition.booleanCondition then entry.field.selectionSet else [])
          ++ activeContributionSelectionSet variableValues
            (guardedFieldChildContributions rest)
        = executableFieldsMergedSelectionSet
            ((if entry.condition.allows variableValues runtimeType then
                [{
                  fieldName := entry.field.fieldName
                  arguments := entry.field.arguments
                  selectionSet := entry.field.selectionSet
                }]
              else [])
              ++ guardedFieldExecutableFields variableValues runtimeType rest)
      cases hallows
            : booleanConditionAllows variableValues entry.condition.booleanCondition <;>
        simp [Condition.allows, hhead, hallows, ih,
          executableFieldsMergedSelectionSet]

theorem ofTypeRegionUnder_runtimeGroups_permutationEquivalent
    (schema : Schema) (variableValues : VariableValues)
    (executionParentType runtimeType : Name) (region : List Name)
    (contributions : List (List BooleanLiteral × List Selection))
    (targetSelectionSet : List Selection) (hruntime : runtimeType ∈ region)
    (htarget
      : (activeContributionSelectionSet variableValues contributions).Perm
          targetSelectionSet)
    : RuntimeGroupsPermutationEquivalent
        (guardedFieldRuntimeGroups variableValues runtimeType
          (guardedFieldGroups
            (SelectionConditions.ofTypeRegionUnder schema region contributions)))
        (collectRuntimeFieldGroups schema variableValues executionParentType runtimeType
          targetSelectionSet) := by
  apply runtimeGroupsPermutationEquivalent_trans
    (guardedFieldRuntimeGroups_permutationEquivalent variableValues runtimeType
      (SelectionConditions.ofTypeRegionUnder schema region contributions))
  let fields := runtimeFields variableValues runtimeType
    (SelectionConditions.ofTypeRegionUnder schema region contributions)
  have hgrouped := groupExecutableFields_exact fields
  constructor
  · exact groupExecutableFields_wellFormed fields
  · exact NormalForm.GroundTypeNormalization.collectFields_wellFormed schema
      variableValues executionParentType (.object runtimeType PUnit.unit)
      targetSelectionSet
  · exact hgrouped.1
  · exact (executableGroupNamesNodup_iff_map_fst_nodup _).mp
      (NormalForm.collectFields_namesNodup schema variableValues executionParentType
        (.object runtimeType PUnit.unit) targetSelectionSet)
  · apply hgrouped.2.trans
    unfold fields
    rw [runtimeFields_ofTypeRegionUnder schema variableValues executionParentType
      runtimeType PUnit.unit region contributions hruntime]
    apply (collectFlatFields_perm_of_selectionSet_perm schema variableValues
      executionParentType (.object runtimeType PUnit.unit) htarget).trans
    exact collectFlatFields_perm_flatten_collectFields schema variableValues
      executionParentType (.object runtimeType PUnit.unit) targetSelectionSet

def knownBooleanVariableNames (variableValues : VariableValues) : List Name :=
  (variableValues.map Prod.fst).filter fun variableName =>
    (inputValueBoolean? variableValues (.variable variableName)).isSome

theorem lookupVariableValue?_some_name_mem
    (variableValues : VariableValues) (variableName : Name)
    {value : CoercedInputValue}
    (hlookup : lookupVariableValue? variableValues variableName = some value)
    : variableName ∈ variableValues.map Prod.fst := by
  induction variableValues with
  | nil => simp [lookupVariableValue?] at hlookup
  | cons binding rest ih =>
      rcases binding with ⟨name, bindingValue⟩
      by_cases heq : name = variableName
      · simp [heq]
      · simp only [lookupVariableValue?, heq, ite_false] at hlookup
        simp [ih hlookup]

theorem knownBooleanVariableNames_mem_of_input
    (variableValues : VariableValues) (variableName : Name) (value : Bool)
    (hvalue
      : inputValueBoolean? variableValues (.variable variableName) = some value)
    : variableName ∈ knownBooleanVariableNames variableValues := by
  cases hlookup : lookupVariableValue? variableValues variableName with
  | none => simp [inputValueBoolean?, hlookup] at hvalue
  | some inputValue =>
      have hstatic : inputValue.toInputValue.staticBoolean? = some value := by
        simpa [inputValueBoolean?, hlookup] using hvalue
      unfold knownBooleanVariableNames
      apply List.mem_filter.mpr
      refine ⟨lookupVariableValue?_some_name_mem variableValues variableName hlookup, ?_⟩
      simp [inputValueBoolean?, hlookup, hstatic]

theorem knownBooleanVariableNames_known (variableValues : VariableValues)
    : KnownBooleanVariablesWithin variableValues
        (knownBooleanVariableNames variableValues) := by
  intro variableName value hvalue
  exact knownBooleanVariableNames_mem_of_input variableValues variableName value hvalue

theorem boolVarsComplete_subset_knownBooleanVariableNames
    {variables : List Name} {variableValues : VariableValues}
    (hcomplete : boolVarsComplete variables variableValues)
    : ∀ variableName,
        variableName ∈ variables
        -> variableName ∈ knownBooleanVariableNames variableValues := by
  intro variableName hvariable
  rcases hcomplete variableName hvariable with ⟨value, hvalue⟩
  exact knownBooleanVariableNames_mem_of_input variableValues variableName value hvalue

theorem inputValueBoolean?_eq_of_agree_of_complete
    {first second : VariableValues} {variableName : Name}
    (hagrees : BooleanAssignmentsAgree first second)
    (hcomplete : ∃ value,
      inputValueBoolean? first (.variable variableName) = some value)
    : inputValueBoolean? first (.variable variableName)
      = inputValueBoolean? second (.variable variableName) := by
  rcases hcomplete with ⟨value, hvalue⟩
  rw [hvalue, hagrees variableName value hvalue]

theorem activeContributionSelectionSet_eq_of_boolean_agreement
    (first second : VariableValues)
    (contributions : List (List BooleanLiteral × List Selection))
    (hagrees : ∀ condition selectionSet,
      (condition, selectionSet) ∈ contributions
      -> ∀ literal,
          literal ∈ condition
          -> inputValueBoolean? first (.variable literal.variableName)
            = inputValueBoolean? second (.variable literal.variableName))
    : activeContributionSelectionSet first contributions
      = activeContributionSelectionSet second contributions := by
  induction contributions with
  | nil => rfl
  | cons contribution rest ih =>
      rcases contribution with ⟨condition, selectionSet⟩
      have hcondition : booleanConditionAllows first condition
          = booleanConditionAllows second condition := by
        apply booleanConditionAllows_eq_of_variables_agree
          (variables := condition.map BooleanLiteral.variableName)
        · intro literal hliteral
          exact List.mem_map.mpr ⟨literal, hliteral, rfl⟩
        · intro variableName hvariable
          rcases List.mem_map.mp hvariable with ⟨literal, hliteral, rfl⟩
          exact hagrees condition selectionSet (by simp) literal hliteral
      change (if booleanConditionAllows first condition then selectionSet else [])
          ++ activeContributionSelectionSet first rest
        = (if booleanConditionAllows second condition then selectionSet else [])
          ++ activeContributionSelectionSet second rest
      rw [hcondition, ih (by
        intro restCondition restSelectionSet hrest literal hliteral
        exact hagrees restCondition restSelectionSet (by simp [hrest]) literal hliteral)]

theorem ofTypeRegionUnder_conditionBooleanVariablesWithin
    (schema : Schema) (region : List Name)
    (contributions : List (List BooleanLiteral × List Selection))
    (variables : List Name)
    (hseed : ∀ condition selectionSet,
      (condition, selectionSet) ∈ contributions
      -> ∀ literal, literal ∈ condition -> literal.variableName ∈ variables)
    (hsource : ∀ condition selectionSet,
      (condition, selectionSet) ∈ contributions
      -> ∀ variableName,
          variableName ∈ SelectionConditions.selectionSetBooleanVariables selectionSet
          -> variableName ∈ variables)
    {entry : ConditionedField}
    (hentry : entry ∈ SelectionConditions.ofTypeRegionUnder schema region contributions)
    {literal : BooleanLiteral}
    (hliteral : literal ∈ entry.condition.booleanCondition)
    : literal.variableName ∈ variables := by
  unfold SelectionConditions.ofTypeRegionUnder at hentry
  rcases List.mem_flatMap.mp hentry with ⟨contribution, hcontribution, hentry⟩
  rcases contribution with ⟨condition, selectionSet⟩
  apply extractFields_conditionBooleanVariablesWithin schema []
    ({ possibleTypes := region, booleanCondition := condition } : Condition)
    selectionSet variables
  · exact hseed condition selectionSet hcontribution
  · exact hsource condition selectionSet hcontribution
  · exact hentry
  · exact hliteral

theorem ofTypeRegionUnder_childBooleanVariablesWithin
    (schema : Schema) (region : List Name)
    (contributions : List (List BooleanLiteral × List Selection))
    {entry : ConditionedField}
    (hentry : entry ∈ SelectionConditions.ofTypeRegionUnder schema region contributions)
    {variableName : Name}
    (hvariable
      : variableName
        ∈ SelectionConditions.selectionSetBooleanVariables entry.field.selectionSet)
    : ∃ condition selectionSet,
        (condition, selectionSet) ∈ contributions
        ∧ variableName
          ∈ SelectionConditions.selectionSetBooleanVariables selectionSet := by
  unfold SelectionConditions.ofTypeRegionUnder at hentry
  rcases List.mem_flatMap.mp hentry with ⟨contribution, hcontribution, hentry⟩
  rcases contribution with ⟨condition, selectionSet⟩
  exact ⟨condition, selectionSet, hcontribution,
    extractFields_childBooleanVariablesWithin schema []
      ({ possibleTypes := region, booleanCondition := condition } : Condition)
      selectionSet hentry hvariable⟩

theorem guardedFieldGroupFor_ofTypeRegionUnder_booleanVariablesWithin
    (schema : Schema) (region : List Name)
    (leftContributions rightContributions
      : List (List BooleanLiteral × List Selection))
    (variables : List Name)
    (hleftSeed : ∀ condition selectionSet,
      (condition, selectionSet) ∈ leftContributions
      -> ∀ literal, literal ∈ condition -> literal.variableName ∈ variables)
    (hleftSource : ∀ condition selectionSet,
      (condition, selectionSet) ∈ leftContributions
      -> ∀ variableName,
          variableName ∈ SelectionConditions.selectionSetBooleanVariables selectionSet
          -> variableName ∈ variables)
    (hrightSeed : ∀ condition selectionSet,
      (condition, selectionSet) ∈ rightContributions
      -> ∀ literal, literal ∈ condition -> literal.variableName ∈ variables)
    (hrightSource : ∀ condition selectionSet,
      (condition, selectionSet) ∈ rightContributions
      -> ∀ variableName,
          variableName ∈ SelectionConditions.selectionSetBooleanVariables selectionSet
          -> variableName ∈ variables)
    (right : GuardedFieldGroup)
    (hright : right ∈ guardedFieldGroups
      (SelectionConditions.ofTypeRegionUnder schema region rightContributions))
    {variableName : Name}
    (hvariable : variableName ∈ guardedFieldGroupBooleanVariables
      (guardedFieldGroupFor
        (guardedFieldGroups
          (SelectionConditions.ofTypeRegionUnder schema region leftContributions))
        right)
      right)
    : variableName ∈ variables := by
  unfold guardedFieldGroupBooleanVariables at hvariable
  have hflat := List.mem_eraseDups.mp hvariable
  rcases List.mem_flatMap.mp hflat with ⟨entry, hentry, hliteralName⟩
  rcases List.mem_map.mp hliteralName with ⟨literal, hliteral, rfl⟩
  rcases List.mem_append.mp hentry with hleft | hrightEntry
  · cases hfind : findGuardedFieldGroup? right.responseName
        (guardedFieldGroups
          (SelectionConditions.ofTypeRegionUnder schema region leftContributions)) with
    | none =>
        unfold guardedFieldGroupFor at hleft
        simp [hfind] at hleft
    | some left =>
        have hleftGroup := (findGuardedFieldGroup?_some_mem hfind).1
        have hleftOrigin := (guardedFieldGroup_entry_origin
          (SelectionConditions.ofTypeRegionUnder schema region leftContributions)
          hleftGroup (by
            unfold guardedFieldGroupFor at hleft
            simpa [hfind] using hleft)).1
        exact ofTypeRegionUnder_conditionBooleanVariablesWithin schema region
          leftContributions variables hleftSeed hleftSource hleftOrigin hliteral
  · have hrightOrigin := (guardedFieldGroup_entry_origin
        (SelectionConditions.ofTypeRegionUnder schema region rightContributions)
        hright hrightEntry).1
    exact ofTypeRegionUnder_conditionBooleanVariablesWithin schema region
      rightContributions variables hrightSeed hrightSource hrightOrigin hliteral

theorem guardedFieldGroupFor_childBooleanVariablesWithinSelectionSet
    (schema : Schema) (region : List Name) (selectionSet : List Selection)
    (leftGroups : List GuardedFieldGroup)
    (hleftGroups
      : leftGroups
        = guardedFieldGroups
            (SelectionConditions.ofTypeRegion schema region selectionSet))
    (right : GuardedFieldGroup)
    {entry : ConditionedField}
    (hentry : entry ∈ (guardedFieldGroupFor leftGroups right).entries)
    {variableName : Name}
    (hvariable
      : variableName
        ∈ SelectionConditions.selectionSetBooleanVariables entry.field.selectionSet)
    : variableName ∈ SelectionConditions.selectionSetBooleanVariables selectionSet := by
  cases hfind : findGuardedFieldGroup? right.responseName leftGroups with
  | none =>
      unfold guardedFieldGroupFor at hentry
      simp [hfind] at hentry
  | some left =>
      have hmember := (findGuardedFieldGroup?_some_mem hfind).1
      rw [hleftGroups] at hmember
      apply guardedFieldGroup_childBooleanVariablesWithinSelectionSet schema region
        selectionSet left hmember
      · unfold guardedFieldGroupFor at hentry
        simpa [hfind] using hentry
      · exact hvariable

theorem guardedFieldGroupFor_entry_origin
    (entries : List ConditionedField) (right : GuardedFieldGroup)
    {entry : ConditionedField}
    (hentry
      : entry ∈ (guardedFieldGroupFor (guardedFieldGroups entries) right).entries)
    : entry ∈ entries := by
  cases hfind : findGuardedFieldGroup? right.responseName
      (guardedFieldGroups entries) with
  | none =>
      unfold guardedFieldGroupFor at hentry
      simp [hfind] at hentry
  | some left =>
      have hleft := (findGuardedFieldGroup?_some_mem hfind).1
      apply (guardedFieldGroup_entry_origin entries hleft ?_).1
      unfold guardedFieldGroupFor at hentry
      simpa [hfind] using hentry

def SelectionSetInclusionCaseReady (schema : Schema) (responseFuel : Nat)
    (fixedExecutionParentType : Option Name) (targetValues : VariableValues)
    (leftSelectionSet rightSelectionSet : List Selection)
    (runtimeType : Name)
    : Prop :=
  schema.objectType runtimeType
  ∧ fixedExecutionParentType.getD runtimeType = runtimeType
  ∧ NormalForm.selectionSetSemanticsReady schema runtimeType leftSelectionSet
  ∧ FieldMerge.fieldsInSetCanMerge schema runtimeType leftSelectionSet
  ∧ NormalForm.selectionSetSemanticsReady schema runtimeType rightSelectionSet
  ∧ FieldMerge.fieldsInSetCanMerge schema runtimeType rightSelectionSet
  ∧ selectionSetIncludesAtRuntimeBoolWithFuel schema responseFuel runtimeType runtimeType
      targetValues leftSelectionSet rightSelectionSet
    = true

set_option maxRecDepth 10000 in
mutual
theorem guardedFieldGroupsIncludeWithFuel_entries_semantic_sound
    (schema : Schema) (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (responseFuel : Nat) (fixedExecutionParentType : Option Name)
    (checkValues targetValues : VariableValues) (parentRegion : List Name)
    (leftEntries rightEntries : List SelectionConditions.ConditionedField)
    (leftTargetSelectionSet rightTargetSelectionSet : List Selection)
    (runtimeType : Name)
    (hcheck
      : guardedFieldGroupsIncludeWithFuel schema responseFuel
          fixedExecutionParentType checkValues
          (guardedFieldGroups leftEntries) (guardedFieldGroups rightEntries)
        = true)
    (hagrees : BooleanAssignmentsAgree checkValues targetValues)
    (hleftComplete
      : boolVarsComplete
          (SelectionConditions.selectionSetBooleanVariables leftTargetSelectionSet)
          targetValues)
    (hrightComplete
      : boolVarsComplete
          (SelectionConditions.selectionSetBooleanVariables rightTargetSelectionSet)
          targetValues)
    (hleftChildrenComplete : ∀ entry,
      entry ∈ leftEntries
      -> boolVarsComplete
          (SelectionConditions.selectionSetBooleanVariables entry.field.selectionSet)
          targetValues)
    (hrightChildrenComplete : ∀ entry,
      entry ∈ rightEntries
      -> boolVarsComplete
          (SelectionConditions.selectionSetBooleanVariables entry.field.selectionSet)
          targetValues)
    (hgroupComplete : ∀ right,
      right ∈ guardedFieldGroups rightEntries
      -> boolVarsComplete
          (guardedFieldGroupBooleanVariables
            (guardedFieldGroupFor (guardedFieldGroups leftEntries) right) right)
          targetValues)
    (hleftEquivalent : RuntimeGroupsPermutationEquivalent
      (guardedFieldRuntimeGroups targetValues runtimeType
        (guardedFieldGroups leftEntries))
      (collectRuntimeFieldGroups schema targetValues runtimeType runtimeType
        leftTargetSelectionSet))
    (hrightEquivalent : RuntimeGroupsPermutationEquivalent
      (guardedFieldRuntimeGroups targetValues runtimeType
        (guardedFieldGroups rightEntries))
      (collectRuntimeFieldGroups schema targetValues runtimeType runtimeType
        rightTargetSelectionSet))
    (hruntimeParent : runtimeType ∈ parentRegion)
    (hfixedParentRegion
      : ∀ parentType,
          fixedExecutionParentType = some parentType
          -> parentRegion = schema.getPossibleTypes parentType)
    (hobject : schema.objectType runtimeType)
    (hexecutionParent : fixedExecutionParentType.getD runtimeType = runtimeType)
    (hleftReady
      : NormalForm.selectionSetSemanticsReady schema runtimeType leftTargetSelectionSet)
    (hleftMerge
      : FieldMerge.fieldsInSetCanMerge schema runtimeType leftTargetSelectionSet)
    (hrightReady
      : NormalForm.selectionSetSemanticsReady schema runtimeType rightTargetSelectionSet)
    (hrightMerge
      : FieldMerge.fieldsInSetCanMerge schema runtimeType rightTargetSelectionSet)
    : selectionSetIncludesAtRuntimeBoolWithFuel schema responseFuel runtimeType
        runtimeType targetValues leftTargetSelectionSet rightTargetSelectionSet
      = true := by
  let leftGroups := guardedFieldGroups leftEntries
  let rightGroups := guardedFieldGroups rightEntries
  let runtimeLeftGroups := collectRuntimeFieldGroups schema targetValues runtimeType
    runtimeType leftTargetSelectionSet
  let runtimeRightGroups := collectRuntimeFieldGroups schema targetValues runtimeType
    runtimeType rightTargetSelectionSet
  have hleftEquivalent' : RuntimeGroupsPermutationEquivalent
      (guardedFieldRuntimeGroups targetValues runtimeType leftGroups)
      runtimeLeftGroups := by simpa [leftGroups, runtimeLeftGroups] using hleftEquivalent
  have hrightEquivalent' : RuntimeGroupsPermutationEquivalent
      (guardedFieldRuntimeGroups targetValues runtimeType rightGroups)
      runtimeRightGroups := by simpa [rightGroups, runtimeRightGroups] using hrightEquivalent
  have hgroupComplete' : ∀ right,
      right ∈ rightGroups
      -> boolVarsComplete
          (guardedFieldGroupBooleanVariables
            (guardedFieldGroupFor leftGroups right) right) targetValues := by
    simpa [leftGroups, rightGroups] using hgroupComplete
  cases responseFuel with
  | zero =>
      have hcases : ∀ right,
          right ∈ rightGroups
          -> guardedFieldGroupCaseIncludesBool schema 0 fixedExecutionParentType
              targetValues runtimeType (guardedFieldGroupFor leftGroups right)
              right (fun _possibleTypes _leftSelectionSet _rightSelectionSet => true)
            = true := by
        intro right hright
        apply guardedFieldGroupsIncludeWithFuel_sound_at_runtime schema 0
          fixedExecutionParentType checkValues targetValues leftGroups rightGroups
          (fun _possibleTypes _leftSelectionSet _rightSelectionSet => true)
          (by simpa [leftGroups, rightGroups] using hcheck) hagrees hgroupComplete'
          (by intro childFuel heq; omega) right hright runtimeType
        · intro parentType hfixed
          rw [← hfixedParentRegion parentType hfixed]
          exact hruntimeParent
        · intro childFuel heq
          omega
      have hguarded := guardedFieldGroupCases_sound_runtime schema 0
        fixedExecutionParentType targetValues runtimeType leftGroups rightGroups
        (fun _possibleTypes _leftSelectionSet _rightSelectionSet => true) hcases
      unfold guardedFieldRuntimeGroupsIncludeBool at hguarded
      have hruntimeEmpty : runtimeRightGroups.isEmpty = true := by
        rw [← runtimeGroupsPermutationEquivalent_isEmpty_iff hrightEquivalent']
        simpa [hexecutionParent] using hguarded
      simpa [selectionSetIncludesAtRuntimeBoolWithFuel, runtimeRightGroups]
        using hruntimeEmpty
  | succ childFuel =>
      have hruntimeLeftReady := executableGroupsSemanticsReady_collectFields schema
        targetValues runtimeType PUnit.unit leftTargetSelectionSet hobject hleftReady
        hleftMerge
      have hruntimeRightReady := executableGroupsSemanticsReady_collectFields schema
        targetValues runtimeType PUnit.unit rightTargetSelectionSet hobject hrightReady
        hrightMerge
      let childCheck := fun possibleTypes leftSelectionSet rightSelectionSet =>
        guardedFieldChildIncludesBool schema childFuel targetValues possibleTypes
          leftSelectionSet rightSelectionSet
      have hchildSpecialize
          : ∀ candidateFuel,
              childFuel + 1 = candidateFuel + 1
              -> ∀ knownValues,
                BooleanAssignmentsAgree knownValues targetValues
                -> ∀ possibleTypes leftSelectionSet rightSelectionSet,
                  guardedFieldChildIncludesBool schema candidateFuel knownValues
                      possibleTypes leftSelectionSet rightSelectionSet = true
                  -> childCheck possibleTypes leftSelectionSet rightSelectionSet = true := by
            intro candidateFuel heq knownValues hknownAgrees possibleTypes
              leftSelectionSet rightSelectionSet hchildCheck
            have heqFuel : candidateFuel = childFuel := by omega
            subst candidateFuel
            unfold childCheck
            unfold guardedFieldChildIncludesBool at hchildCheck ⊢
            cases hshortcut
                  : selectionSetSyntacticInclusionShortcutBool childFuel leftSelectionSet
                      rightSelectionSet with
            | false =>
                simp only [hshortcut, Bool.false_or] at hchildCheck ⊢
                exact guardedFieldGroupsIncludeWithFuel_specialize schema childFuel none
                  knownValues targetValues
                  (guardedFieldGroups
                    (SelectionConditions.ofTypeRegion schema possibleTypes leftSelectionSet))
                  (guardedFieldGroups
                    (SelectionConditions.ofTypeRegion schema possibleTypes rightSelectionSet))
                  hchildCheck hknownAgrees
            | true => simp
      have hcases : ∀ right,
          right ∈ rightGroups
          -> guardedFieldGroupCaseIncludesBool schema (childFuel + 1)
              fixedExecutionParentType targetValues runtimeType
              (guardedFieldGroupFor leftGroups right) right childCheck
            = true := by
        intro right hright
        apply guardedFieldGroupsIncludeWithFuel_sound_at_runtime schema
          (childFuel + 1) fixedExecutionParentType checkValues targetValues
          leftGroups rightGroups childCheck
          (by simpa [leftGroups, rightGroups] using hcheck) hagrees hgroupComplete'
          hchildSpecialize right hright runtimeType
        · intro parentType hfixed
          rw [← hfixedParentRegion parentType hfixed]
          exact hruntimeParent
        · intro candidateFuel heq fieldType hleftNonempty hrightNonempty
            hleftWitness hrightWitness hseededCheck
          have heqFuel : candidateFuel = childFuel := by omega
          subst candidateFuel
          let left := guardedFieldGroupFor leftGroups right
          let guardedLeftFields := guardedFieldExecutableFields targetValues runtimeType
            left.entries
          let guardedRightFields := guardedFieldExecutableFields targetValues runtimeType
            right.entries
          have hleftLocal : (left.responseName, guardedLeftFields) ∈
              executableFieldsAsGroup left.responseName guardedLeftFields := by
            cases hfields : guardedLeftFields with
            | nil =>
                exact False.elim (hleftNonempty (by
                  simpa [left, guardedLeftFields] using hfields))
            | cons field rest => simp [executableFieldsAsGroup]
          have hrightLocal : (right.responseName, guardedRightFields) ∈
              executableFieldsAsGroup right.responseName guardedRightFields := by
            cases hfields : guardedRightFields with
            | nil =>
                exact False.elim (hrightNonempty (by
                  simpa [guardedRightFields] using hfields))
            | cons field rest => simp [executableFieldsAsGroup]
          have hleftFull : (left.responseName, guardedLeftFields) ∈
              guardedFieldRuntimeGroups targetValues runtimeType leftGroups := by
            apply guardedFieldGroupFor_runtimeGroups_subset targetValues runtimeType
              leftGroups right
            simpa [left, guardedLeftFields] using hleftLocal
          have hrightFull : (right.responseName, guardedRightFields) ∈
              guardedFieldRuntimeGroups targetValues runtimeType rightGroups := by
            apply guardedFieldRuntimeGroup_component_mem targetValues runtimeType
              rightGroups right hright
            simpa [guardedRightFields] using hrightLocal
          rcases runtimeGroupsPermutationEquivalent_matchingGroup hleftEquivalent'
              hleftFull with
            ⟨runtimeLeftFields, hruntimeLeftGroup, hleftFieldsPerm⟩
          rcases runtimeGroupsPermutationEquivalent_matchingGroup hrightEquivalent'
              hrightFull with
            ⟨runtimeRightFields, hruntimeRightGroup, hrightFieldsPerm⟩
          have hleftWitness' : completionFieldsWitness schema runtimeType fieldType
              guardedLeftFields := by
            simpa [left, guardedLeftFields, hexecutionParent] using hleftWitness
          have hrightWitness' : completionFieldsWitness schema runtimeType fieldType
              guardedRightFields := by
            simpa [guardedRightFields, hexecutionParent] using hrightWitness
          have hleftCompletionReady : completionFieldsSemanticsReady schema runtimeType
              fieldType runtimeLeftFields :=
            ⟨hruntimeLeftReady left.responseName runtimeLeftFields hruntimeLeftGroup,
              completionFieldsWitness_of_perm hleftFieldsPerm hleftWitness'⟩
          have hrightCompletionReady : completionFieldsSemanticsReady schema runtimeType
              fieldType runtimeRightFields :=
            ⟨hruntimeRightReady right.responseName runtimeRightFields hruntimeRightGroup,
              completionFieldsWitness_of_perm hrightFieldsPerm hrightWitness'⟩
          have hleftChildSelectionSet :
              (executableFieldsMergedSelectionSet guardedLeftFields).Perm
                (executableFieldsMergedSelectionSet runtimeLeftFields) := by
            simpa [executableFieldsMergedSelectionSet_eq_mergedFieldSelectionSet]
              using Execution.FieldGroups.mergedFieldSelectionSet_perm hleftFieldsPerm
          have hrightChildSelectionSet :
              (executableFieldsMergedSelectionSet guardedRightFields).Perm
                (executableFieldsMergedSelectionSet runtimeRightFields) := by
            simpa [executableFieldsMergedSelectionSet_eq_mergedFieldSelectionSet]
              using Execution.FieldGroups.mergedFieldSelectionSet_perm hrightFieldsPerm
          have hleftChildComplete : boolVarsComplete
              (SelectionConditions.selectionSetBooleanVariables
                (executableFieldsMergedSelectionSet guardedLeftFields)) targetValues := by
            intro variableName hvariable
            have hruntimeVariable :=
              (selectionSetBooleanVariables_perm hleftChildSelectionSet).mem_iff.mp
                hvariable
            have htargetVariable := mergedSelectionSet_variables_within_of_group_mem
              schema targetValues runtimeType runtimeType leftTargetSelectionSet
              (left.responseName, runtimeLeftFields) hruntimeLeftGroup variableName
              hruntimeVariable
            exact hleftComplete variableName htargetVariable
          have hrightChildComplete : boolVarsComplete
              (SelectionConditions.selectionSetBooleanVariables
                (executableFieldsMergedSelectionSet guardedRightFields)) targetValues := by
            intro variableName hvariable
            have hruntimeVariable :=
              (selectionSetBooleanVariables_perm hrightChildSelectionSet).mem_iff.mp
                hvariable
            have htargetVariable := mergedSelectionSet_variables_within_of_group_mem
              schema targetValues runtimeType runtimeType rightTargetSelectionSet
              (right.responseName, runtimeRightFields) hruntimeRightGroup variableName
              hruntimeVariable
            exact hrightComplete variableName htargetVariable
          let possibleTypes := schema.getPossibleTypes fieldType.namedType
          let leftRuntimeEntries := guardedFieldEntriesAtRuntimeType runtimeType left.entries
          let rightRuntimeEntries := guardedFieldEntriesAtRuntimeType runtimeType right.entries
          let leftContributions := guardedFieldChildContributions leftRuntimeEntries
          let rightContributions := guardedFieldChildContributions rightRuntimeEntries
          let leftSeededEntries := SelectionConditions.ofTypeRegionUnder schema
            possibleTypes leftContributions
          let rightSeededEntries := SelectionConditions.ofTypeRegionUnder schema
            possibleTypes rightContributions
          have hseededTarget : guardedFieldGroupsIncludeWithFuel schema childFuel none
              targetValues (guardedFieldGroups leftSeededEntries)
                (guardedFieldGroups rightSeededEntries) = true := by
            apply guardedFieldGroupsIncludeWithFuel_specialize schema childFuel none
              checkValues targetValues (guardedFieldGroups leftSeededEntries)
              (guardedFieldGroups rightSeededEntries)
            · simpa [left, possibleTypes, leftRuntimeEntries, rightRuntimeEntries,
                leftContributions, rightContributions, leftSeededEntries,
                rightSeededEntries] using hseededCheck
            · exact hagrees
          unfold childCheck guardedFieldChildIncludesBool
          simp only [Bool.or_eq_true]
          right
          apply guardedFieldGroupsIncludeWithFuel_semantic_complete schema hschema
            childFuel none targetValues possibleTypes
            (executableFieldsMergedSelectionSet guardedLeftFields)
            (executableFieldsMergedSelectionSet guardedRightFields)
            (knownBooleanVariableNames targetValues)
          · exact knownBooleanVariableNames_known targetValues
          · exact boolVarsComplete_subset_knownBooleanVariableNames hleftChildComplete
          · exact boolVarsComplete_subset_knownBooleanVariableNames hrightChildComplete
          · simp
          · intro childValues hchildComplete hchildAgrees childRuntimeType hchildRuntime
            have hchildObject : schema.objectType childRuntimeType :=
              SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects hschema
                fieldType.namedType childRuntimeType hchildRuntime
            have hchildIncludesBool : schema.typeIncludesObjectBool fieldType.namedType
                childRuntimeType = true := List.contains_iff_mem.mpr hchildRuntime
            have hleftChildReady := completionFieldsSemanticsReady_merged_semantics
              hleftCompletionReady hchildIncludesBool
            have hrightChildReady := completionFieldsSemanticsReady_merged_semantics
              hrightCompletionReady hchildIncludesBool
            have hleftChildMerge := completionFieldsSemanticsReady_merged_canMerge
              hleftCompletionReady childRuntimeType
            have hrightChildMerge := completionFieldsSemanticsReady_merged_canMerge
              hrightCompletionReady childRuntimeType
            have hseededChild : guardedFieldGroupsIncludeWithFuel schema childFuel none
                childValues (guardedFieldGroups leftSeededEntries)
                  (guardedFieldGroups rightSeededEntries) = true :=
              guardedFieldGroupsIncludeWithFuel_specialize schema childFuel none
                targetValues childValues (guardedFieldGroups leftSeededEntries)
                (guardedFieldGroups rightSeededEntries) hseededTarget hchildAgrees
            have hactiveLeftEq : activeContributionSelectionSet targetValues
                leftContributions = activeContributionSelectionSet childValues
                  leftContributions := by
              apply activeContributionSelectionSet_eq_of_boolean_agreement
              intro condition selectionSet hcontribution literal hliteral
              rcases List.mem_map.mp hcontribution with ⟨entry, hentry, heq⟩
              injection heq with hcondition _hselectionSet
              subst condition
              apply inputValueBoolean?_eq_of_agree_of_complete hchildAgrees
              apply hgroupComplete' right hright literal.variableName
              apply guardedFieldGroupBooleanVariables_mem_left left right
              · exact (List.mem_filter.mp hentry).1
              · exact hliteral
            have hactiveRightEq : activeContributionSelectionSet targetValues
                rightContributions = activeContributionSelectionSet childValues
                  rightContributions := by
              apply activeContributionSelectionSet_eq_of_boolean_agreement
              intro condition selectionSet hcontribution literal hliteral
              rcases List.mem_map.mp hcontribution with ⟨entry, hentry, heq⟩
              injection heq with hcondition _hselectionSet
              subst condition
              apply inputValueBoolean?_eq_of_agree_of_complete hchildAgrees
              apply hgroupComplete' right hright literal.variableName
              apply guardedFieldGroupBooleanVariables_mem_right left right
              · exact (List.mem_filter.mp hentry).1
              · exact hliteral
            have hactiveLeftTarget : activeContributionSelectionSet targetValues
                leftContributions
                = executableFieldsMergedSelectionSet guardedLeftFields := by
              calc
                activeContributionSelectionSet targetValues leftContributions
                    = executableFieldsMergedSelectionSet
                        (guardedFieldExecutableFields targetValues runtimeType
                          leftRuntimeEntries) :=
                  activeContributionSelectionSet_guardedFieldChildContributions
                    targetValues runtimeType leftRuntimeEntries (by
                      intro entry hentry
                      exact List.contains_iff_mem.mp (List.mem_filter.mp hentry).2)
                _ = executableFieldsMergedSelectionSet guardedLeftFields := by
                  rw [← guardedFieldExecutableFields_runtime_entries targetValues
                    runtimeType left.entries]
            have hactiveRightTarget : activeContributionSelectionSet targetValues
                rightContributions
                = executableFieldsMergedSelectionSet guardedRightFields := by
              calc
                activeContributionSelectionSet targetValues rightContributions
                    = executableFieldsMergedSelectionSet
                        (guardedFieldExecutableFields targetValues runtimeType
                          rightRuntimeEntries) :=
                  activeContributionSelectionSet_guardedFieldChildContributions
                    targetValues runtimeType rightRuntimeEntries (by
                      intro entry hentry
                      exact List.contains_iff_mem.mp (List.mem_filter.mp hentry).2)
                _ = executableFieldsMergedSelectionSet guardedRightFields := by
                  rw [← guardedFieldExecutableFields_runtime_entries targetValues
                    runtimeType right.entries]
            have hleftSeededEquivalent : RuntimeGroupsPermutationEquivalent
                (guardedFieldRuntimeGroups childValues childRuntimeType
                  (guardedFieldGroups leftSeededEntries))
                (collectRuntimeFieldGroups schema childValues childRuntimeType
                  childRuntimeType
                  (executableFieldsMergedSelectionSet runtimeLeftFields)) := by
              apply ofTypeRegionUnder_runtimeGroups_permutationEquivalent schema
                childValues childRuntimeType childRuntimeType possibleTypes
                leftContributions
                  (executableFieldsMergedSelectionSet runtimeLeftFields) hchildRuntime
              exact (List.Perm.of_eq
                (hactiveLeftEq.symm.trans hactiveLeftTarget)).trans
                  hleftChildSelectionSet
            have hrightSeededEquivalent : RuntimeGroupsPermutationEquivalent
                (guardedFieldRuntimeGroups childValues childRuntimeType
                  (guardedFieldGroups rightSeededEntries))
                (collectRuntimeFieldGroups schema childValues childRuntimeType
                  childRuntimeType
                  (executableFieldsMergedSelectionSet runtimeRightFields)) := by
              apply ofTypeRegionUnder_runtimeGroups_permutationEquivalent schema
                childValues childRuntimeType childRuntimeType possibleTypes
                rightContributions
                  (executableFieldsMergedSelectionSet runtimeRightFields) hchildRuntime
              exact (List.Perm.of_eq
                (hactiveRightEq.symm.trans hactiveRightTarget)).trans
                  hrightChildSelectionSet
            have hleftSeededChildrenComplete : ∀ entry,
                entry ∈ leftSeededEntries
                -> boolVarsComplete
                    (SelectionConditions.selectionSetBooleanVariables
                      entry.field.selectionSet) childValues := by
              intro entry hentry variableName hvariable
              rcases ofTypeRegionUnder_childBooleanVariablesWithin schema possibleTypes
                  leftContributions hentry hvariable with
                ⟨condition, selectionSet, hcontribution, hsourceVariable⟩
              rcases List.mem_map.mp hcontribution with ⟨sourceEntry, hsourceEntry, heq⟩
              injection heq with _hcondition hselectionSet
              subst selectionSet
              apply hchildComplete variableName
              apply boolVarsComplete_subset_knownBooleanVariableNames
                (hleftChildrenComplete sourceEntry
                  (guardedFieldGroupFor_entry_origin leftEntries right
                    (List.mem_filter.mp hsourceEntry).1))
              exact hsourceVariable
            have hrightSeededChildrenComplete : ∀ entry,
                entry ∈ rightSeededEntries
                -> boolVarsComplete
                    (SelectionConditions.selectionSetBooleanVariables
                      entry.field.selectionSet) childValues := by
              intro entry hentry variableName hvariable
              rcases ofTypeRegionUnder_childBooleanVariablesWithin schema possibleTypes
                  rightContributions hentry hvariable with
                ⟨condition, selectionSet, hcontribution, hsourceVariable⟩
              rcases List.mem_map.mp hcontribution with ⟨sourceEntry, hsourceEntry, heq⟩
              injection heq with _hcondition hselectionSet
              subst selectionSet
              apply hchildComplete variableName
              apply boolVarsComplete_subset_knownBooleanVariableNames
                (hrightChildrenComplete sourceEntry
                  (guardedFieldGroup_entry_origin rightEntries hright
                    (List.mem_filter.mp hsourceEntry).1).1)
              exact hsourceVariable
            have hseededGroupComplete : ∀ childRight,
                childRight ∈ guardedFieldGroups rightSeededEntries
                -> boolVarsComplete
                    (guardedFieldGroupBooleanVariables
                      (guardedFieldGroupFor
                        (guardedFieldGroups leftSeededEntries) childRight)
                      childRight)
                    childValues := by
              intro childRight hchildRight variableName hvariable
              apply hchildComplete variableName
              apply guardedFieldGroupFor_ofTypeRegionUnder_booleanVariablesWithin
                schema possibleTypes leftContributions rightContributions
                (knownBooleanVariableNames targetValues)
              · intro condition selectionSet hcontribution literal hliteral
                rcases List.mem_map.mp hcontribution with ⟨entry, hentry, heq⟩
                injection heq with hcondition _hselectionSet
                subst condition
                apply boolVarsComplete_subset_knownBooleanVariableNames
                  (hgroupComplete' right hright)
                exact guardedFieldGroupBooleanVariables_mem_left left right
                  (List.mem_filter.mp hentry).1 hliteral
              · intro condition selectionSet hcontribution candidate hcandidate
                rcases List.mem_map.mp hcontribution with ⟨entry, hentry, heq⟩
                injection heq with _hcondition hselectionSet
                subst selectionSet
                apply boolVarsComplete_subset_knownBooleanVariableNames
                  (hleftChildrenComplete entry
                    (guardedFieldGroupFor_entry_origin leftEntries right
                      (List.mem_filter.mp hentry).1))
                exact hcandidate
              · intro condition selectionSet hcontribution literal hliteral
                rcases List.mem_map.mp hcontribution with ⟨entry, hentry, heq⟩
                injection heq with hcondition _hselectionSet
                subst condition
                apply boolVarsComplete_subset_knownBooleanVariableNames
                  (hgroupComplete' right hright)
                exact guardedFieldGroupBooleanVariables_mem_right left right
                  (List.mem_filter.mp hentry).1 hliteral
              · intro condition selectionSet hcontribution candidate hcandidate
                rcases List.mem_map.mp hcontribution with ⟨entry, hentry, heq⟩
                injection heq with _hcondition hselectionSet
                subst selectionSet
                apply boolVarsComplete_subset_knownBooleanVariableNames
                  (hrightChildrenComplete entry
                    (guardedFieldGroup_entry_origin rightEntries hright
                      (List.mem_filter.mp hentry).1).1)
                exact hcandidate
              · exact hchildRight
              · exact hvariable
            have hchildResult :=
              guardedFieldGroupsIncludeWithFuel_entries_semantic_sound schema hschema
                childFuel none childValues childValues possibleTypes
                leftSeededEntries rightSeededEntries
                (executableFieldsMergedSelectionSet runtimeLeftFields)
                (executableFieldsMergedSelectionSet runtimeRightFields)
                childRuntimeType hseededChild
                (booleanAssignmentsAgree_refl childValues)
                (boolVarsComplete_mono hchildComplete (by
                  intro variableName hvariable
                  have hguardedVariable :=
                    (selectionSetBooleanVariables_perm
                      hleftChildSelectionSet).mem_iff.mpr hvariable
                  exact boolVarsComplete_subset_knownBooleanVariableNames
                    hleftChildComplete variableName hguardedVariable))
                (boolVarsComplete_mono hchildComplete (by
                  intro variableName hvariable
                  have hguardedVariable :=
                    (selectionSetBooleanVariables_perm
                      hrightChildSelectionSet).mem_iff.mpr hvariable
                  exact boolVarsComplete_subset_knownBooleanVariableNames
                    hrightChildComplete variableName hguardedVariable))
                hleftSeededChildrenComplete hrightSeededChildrenComplete
                hseededGroupComplete hleftSeededEquivalent hrightSeededEquivalent
                hchildRuntime (by simp) hchildObject rfl
                (by simpa using hleftChildReady) (by simpa using hleftChildMerge)
                (by simpa using hrightChildReady) (by simpa using hrightChildMerge)
            refine ⟨executableFieldsMergedSelectionSet runtimeLeftFields,
              executableFieldsMergedSelectionSet runtimeRightFields,
              hleftChildSelectionSet, hrightChildSelectionSet, ?_⟩
            exact ⟨hchildObject, rfl, (by simpa using hleftChildReady),
              (by simpa using hleftChildMerge), (by simpa using hrightChildReady),
              (by simpa using hrightChildMerge), hchildResult⟩
      have hguarded := guardedFieldGroupCases_sound_runtime schema
        (childFuel + 1) fixedExecutionParentType targetValues runtimeType leftGroups
        rightGroups childCheck hcases
      unfold guardedFieldRuntimeGroupsIncludeBool at hguarded
      simp only [hexecutionParent] at hguarded
      have hruntimeInclude : executableGroupsIncludeBool schema runtimeType
          (fun outputType leftSelectionSet rightSelectionSet =>
            (schema.getPossibleTypes outputType.namedType).all
              fun childRuntimeType =>
                selectionSetIncludesBoolWithFuel schema childFuel childRuntimeType
                  targetValues leftSelectionSet rightSelectionSet)
          runtimeLeftGroups runtimeRightGroups = true := by
        refine executableGroupsIncludeBool_transport schema runtimeType
          (fun outputType leftSelectionSet rightSelectionSet =>
            childCheck (schema.getPossibleTypes outputType.namedType)
              leftSelectionSet rightSelectionSet)
          (fun outputType leftSelectionSet rightSelectionSet =>
            (schema.getPossibleTypes outputType.namedType).all
              fun childRuntimeType =>
                selectionSetIncludesBoolWithFuel schema childFuel childRuntimeType
                  targetValues leftSelectionSet rightSelectionSet)
          (guardedFieldRuntimeGroups targetValues runtimeType leftGroups)
          (guardedFieldRuntimeGroups targetValues runtimeType rightGroups)
          runtimeLeftGroups runtimeRightGroups hleftEquivalent' hrightEquivalent'
          (executableGroupsResolverReady_of_semanticsReady hruntimeLeftReady)
          (executableGroupsResolverReady_of_semanticsReady hruntimeRightReady) ?_ hguarded
        intro fieldType leftName rightName guardedLeftFields runtimeLeftFields
          guardedRightFields runtimeRightFields hguardedLeftGroup hruntimeLeftGroup
          hguardedRightGroup hruntimeRightGroup _hresponseName hleftFieldsPerm
          hrightFieldsPerm _hnodeLeftWitness hruntimeLeftWitness _hnodeRightWitness
          hruntimeRightWitness hchildCheck
        apply List.all_eq_true.mpr
        intro childRuntimeType hchildRuntime
        have hchildObject : schema.objectType childRuntimeType :=
          SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects hschema
            fieldType.namedType childRuntimeType hchildRuntime
        have hleftCompletionReady : completionFieldsSemanticsReady schema runtimeType fieldType
            runtimeLeftFields :=
          ⟨hruntimeLeftReady leftName runtimeLeftFields hruntimeLeftGroup, hruntimeLeftWitness⟩
        have hrightCompletionReady : completionFieldsSemanticsReady schema runtimeType fieldType
            runtimeRightFields :=
          ⟨hruntimeRightReady rightName runtimeRightFields hruntimeRightGroup, hruntimeRightWitness⟩
        have hchildIncludesBool : schema.typeIncludesObjectBool fieldType.namedType
            childRuntimeType = true := List.contains_iff_mem.mpr hchildRuntime
        have hleftChildReady := completionFieldsSemanticsReady_merged_semantics
          hleftCompletionReady hchildIncludesBool
        have hrightChildReady := completionFieldsSemanticsReady_merged_semantics
          hrightCompletionReady hchildIncludesBool
        have hleftChildMerge := completionFieldsSemanticsReady_merged_canMerge
          hleftCompletionReady childRuntimeType
        have hrightChildMerge := completionFieldsSemanticsReady_merged_canMerge
          hrightCompletionReady childRuntimeType
        have hleftChildSelectionSet :
            (executableFieldsMergedSelectionSet guardedLeftFields).Perm
              (executableFieldsMergedSelectionSet runtimeLeftFields) := by
          simpa [executableFieldsMergedSelectionSet_eq_mergedFieldSelectionSet]
            using Execution.FieldGroups.mergedFieldSelectionSet_perm hleftFieldsPerm
        have hrightChildSelectionSet :
            (executableFieldsMergedSelectionSet guardedRightFields).Perm
              (executableFieldsMergedSelectionSet runtimeRightFields) := by
          simpa [executableFieldsMergedSelectionSet_eq_mergedFieldSelectionSet]
            using Execution.FieldGroups.mergedFieldSelectionSet_perm hrightFieldsPerm
        have hleftChildComplete : boolVarsComplete
            (SelectionConditions.selectionSetBooleanVariables
              (executableFieldsMergedSelectionSet guardedLeftFields)) targetValues := by
          intro variableName hvariable
          have hruntimeVariable :=
            (selectionSetBooleanVariables_perm hleftChildSelectionSet).mem_iff.mp
              hvariable
          have htargetVariable := mergedSelectionSet_variables_within_of_group_mem
            schema targetValues runtimeType runtimeType leftTargetSelectionSet
            (leftName, runtimeLeftFields) hruntimeLeftGroup variableName hruntimeVariable
          exact hleftComplete variableName htargetVariable
        have hrightChildComplete : boolVarsComplete
            (SelectionConditions.selectionSetBooleanVariables
              (executableFieldsMergedSelectionSet guardedRightFields)) targetValues := by
          intro variableName hvariable
          have hruntimeVariable :=
            (selectionSetBooleanVariables_perm hrightChildSelectionSet).mem_iff.mp
              hvariable
          have htargetVariable := mergedSelectionSet_variables_within_of_group_mem
            schema targetValues runtimeType runtimeType rightTargetSelectionSet
            (rightName, runtimeRightFields) hruntimeRightGroup variableName hruntimeVariable
          exact hrightComplete variableName htargetVariable
        let possibleTypes := schema.getPossibleTypes fieldType.namedType
        unfold childCheck guardedFieldChildIncludesBool at hchildCheck
        simp only [Bool.or_eq_true] at hchildCheck
        rcases hchildCheck with hshortcut | hgeneral
        · have hruntimeShortcut :=
            selectionSetSyntacticInclusionShortcutBool_of_perm
              hleftChildSelectionSet hrightChildSelectionSet hshortcut
          exact selectionSetSyntacticInclusionShortcutBool_sound schema hschema
            childFuel childRuntimeType targetValues
            (executableFieldsMergedSelectionSet runtimeLeftFields)
            (executableFieldsMergedSelectionSet runtimeRightFields) hchildObject
            (by simpa using hleftChildReady) (by simpa using hleftChildMerge)
            (by simpa using hrightChildReady) (by simpa using hrightChildMerge)
            hruntimeShortcut
        · have hchildResult :=
            guardedFieldGroupsIncludeWithFuel_semantic_sound schema hschema
              childFuel none targetValues targetValues possibleTypes
              (executableFieldsMergedSelectionSet guardedLeftFields)
              (executableFieldsMergedSelectionSet guardedRightFields)
              (executableFieldsMergedSelectionSet runtimeLeftFields)
              (executableFieldsMergedSelectionSet runtimeRightFields) childRuntimeType
              (by simpa [possibleTypes] using hgeneral)
              (booleanAssignmentsAgree_refl targetValues) hleftChildComplete
              hrightChildComplete hleftChildSelectionSet hrightChildSelectionSet
              hchildRuntime (by simp) hchildObject rfl
              (by simpa using hleftChildReady) (by simpa using hleftChildMerge)
              (by simpa using hrightChildReady) (by simpa using hrightChildMerge)
          rw [selectionSetIncludesBoolWithFuel,
            getPossibleTypes_eq_singleton_of_object schema hchildObject]
          simpa using hchildResult
      simpa [selectionSetIncludesAtRuntimeBoolWithFuel, runtimeLeftGroups,
        runtimeRightGroups]
        using hruntimeInclude
termination_by (responseFuel, 0)
decreasing_by
  all_goals simp_wf
  all_goals
    apply Prod.Lex.left
    omega

theorem guardedFieldGroupsIncludeWithFuel_semantic_sound
    (schema : Schema) (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (responseFuel : Nat) (fixedExecutionParentType : Option Name)
    (checkValues targetValues : VariableValues) (parentRegion : List Name)
    (leftExtractedSelectionSet rightExtractedSelectionSet : List Selection)
    (leftTargetSelectionSet rightTargetSelectionSet : List Selection)
    (runtimeType : Name)
    (hcheck
      : guardedFieldGroupsIncludeWithFuel schema responseFuel
          fixedExecutionParentType checkValues
          (guardedFieldGroups
            (SelectionConditions.ofTypeRegion schema parentRegion
              leftExtractedSelectionSet))
          (guardedFieldGroups
            (SelectionConditions.ofTypeRegion schema parentRegion
              rightExtractedSelectionSet))
        = true)
    (hagrees : BooleanAssignmentsAgree checkValues targetValues)
    (hleftComplete
      : boolVarsComplete
          (SelectionConditions.selectionSetBooleanVariables leftExtractedSelectionSet)
          targetValues)
    (hrightComplete
      : boolVarsComplete
          (SelectionConditions.selectionSetBooleanVariables rightExtractedSelectionSet)
          targetValues)
    (hleftSelectionSet : leftExtractedSelectionSet.Perm leftTargetSelectionSet)
    (hrightSelectionSet : rightExtractedSelectionSet.Perm rightTargetSelectionSet)
    (hruntimeParent : runtimeType ∈ parentRegion)
    (hfixedParentRegion
      : ∀ parentType,
          fixedExecutionParentType = some parentType
          -> parentRegion = schema.getPossibleTypes parentType)
    (hobject : schema.objectType runtimeType)
    (hexecutionParent : fixedExecutionParentType.getD runtimeType = runtimeType)
    (hleftReady
      : NormalForm.selectionSetSemanticsReady schema runtimeType leftTargetSelectionSet)
    (hleftMerge
      : FieldMerge.fieldsInSetCanMerge schema runtimeType leftTargetSelectionSet)
    (hrightReady
      : NormalForm.selectionSetSemanticsReady schema runtimeType rightTargetSelectionSet)
    (hrightMerge
      : FieldMerge.fieldsInSetCanMerge schema runtimeType rightTargetSelectionSet)
    : selectionSetIncludesAtRuntimeBoolWithFuel schema responseFuel runtimeType
        runtimeType targetValues leftTargetSelectionSet rightTargetSelectionSet
      = true := by
  let leftEntries := SelectionConditions.ofTypeRegion schema parentRegion
    leftExtractedSelectionSet
  let rightEntries := SelectionConditions.ofTypeRegion schema parentRegion
    rightExtractedSelectionSet
  have hleftEquivalent : RuntimeGroupsPermutationEquivalent
      (guardedFieldRuntimeGroups targetValues runtimeType
        (guardedFieldGroups leftEntries))
      (collectRuntimeFieldGroups schema targetValues runtimeType runtimeType
        leftTargetSelectionSet) := by
    apply runtimeGroupsPermutationEquivalent_trans
      (guardedFieldRuntimeGroups_permutationEquivalent targetValues runtimeType
        leftEntries)
    exact selectionConditionsForRegion_runtimeGroups_permutationEquivalent schema
      parentRegion hleftSelectionSet targetValues runtimeType runtimeType PUnit.unit
      hruntimeParent
  have hrightEquivalent : RuntimeGroupsPermutationEquivalent
      (guardedFieldRuntimeGroups targetValues runtimeType
        (guardedFieldGroups rightEntries))
      (collectRuntimeFieldGroups schema targetValues runtimeType runtimeType
        rightTargetSelectionSet) := by
    apply runtimeGroupsPermutationEquivalent_trans
      (guardedFieldRuntimeGroups_permutationEquivalent targetValues runtimeType
        rightEntries)
    exact selectionConditionsForRegion_runtimeGroups_permutationEquivalent schema
      parentRegion hrightSelectionSet targetValues runtimeType runtimeType PUnit.unit
      hruntimeParent
  have hgroupComplete : ∀ right,
      right ∈ guardedFieldGroups rightEntries
      -> boolVarsComplete
          (guardedFieldGroupBooleanVariables
            (guardedFieldGroupFor (guardedFieldGroups leftEntries) right) right)
          targetValues := by
    intro right hright variableName hvariable
    have hwithin := guardedFieldGroupFor_booleanVariablesWithin schema parentRegion
      leftExtractedSelectionSet rightExtractedSelectionSet
      (guardedFieldGroups leftEntries) (by simp [leftEntries]) right
      (by simpa [rightEntries] using hright) hvariable
    exact hwithin.elim (hleftComplete variableName) (hrightComplete variableName)
  have hleftTargetComplete : boolVarsComplete
      (SelectionConditions.selectionSetBooleanVariables leftTargetSelectionSet)
      targetValues := by
    intro variableName hvariable
    exact hleftComplete variableName
      ((selectionSetBooleanVariables_perm hleftSelectionSet).mem_iff.mpr hvariable)
  have hrightTargetComplete : boolVarsComplete
      (SelectionConditions.selectionSetBooleanVariables rightTargetSelectionSet)
      targetValues := by
    intro variableName hvariable
    exact hrightComplete variableName
      ((selectionSetBooleanVariables_perm hrightSelectionSet).mem_iff.mpr hvariable)
  exact guardedFieldGroupsIncludeWithFuel_entries_semantic_sound schema hschema
    responseFuel fixedExecutionParentType checkValues targetValues parentRegion
    leftEntries rightEntries leftTargetSelectionSet rightTargetSelectionSet runtimeType
    (by simpa [leftEntries, rightEntries] using hcheck) hagrees
    hleftTargetComplete hrightTargetComplete
    (by
      intro entry hentry variableName hvariable
      apply hleftComplete variableName
      apply extractFields_childBooleanVariablesWithin schema []
        ({ possibleTypes := parentRegion, booleanCondition := [] } : Condition)
        leftExtractedSelectionSet
      · simpa [leftEntries, SelectionConditions.ofTypeRegion] using hentry
      · exact hvariable)
    (by
      intro entry hentry variableName hvariable
      apply hrightComplete variableName
      apply extractFields_childBooleanVariablesWithin schema []
        ({ possibleTypes := parentRegion, booleanCondition := [] } : Condition)
        rightExtractedSelectionSet
      · simpa [rightEntries, SelectionConditions.ofTypeRegion] using hentry
      · exact hvariable)
    hgroupComplete hleftEquivalent
    hrightEquivalent hruntimeParent hfixedParentRegion hobject hexecutionParent
    hleftReady hleftMerge hrightReady hrightMerge
termination_by (responseFuel, 1)
decreasing_by
  all_goals simp_wf
  apply Prod.Lex.right
  omega

theorem guardedFieldGroupsIncludeWithFuel_semantic_complete
    (schema : Schema) (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (responseFuel : Nat) (fixedExecutionParentType : Option Name)
    (checkValues : VariableValues) (parentRegion : List Name)
    (leftExtractedSelectionSet rightExtractedSelectionSet : List Selection)
    (availableBooleanVariables : List Name)
    (hknown : KnownBooleanVariablesWithin checkValues availableBooleanVariables)
    (hleftWithin
      : ∀ variableName,
          variableName
            ∈ SelectionConditions.selectionSetBooleanVariables leftExtractedSelectionSet
          -> variableName ∈ availableBooleanVariables)
    (hrightWithin
      : ∀ variableName,
          variableName
            ∈ SelectionConditions.selectionSetBooleanVariables rightExtractedSelectionSet
          -> variableName ∈ availableBooleanVariables)
    (hfixedParentRegion
      : ∀ parentType,
          fixedExecutionParentType = some parentType
          -> parentRegion = schema.getPossibleTypes parentType)
    (hcases
      : ∀ targetValues,
          boolVarsComplete availableBooleanVariables targetValues
          -> BooleanAssignmentsAgree checkValues targetValues
          -> ∀ runtimeType,
              runtimeType ∈ parentRegion
              -> ∃ leftTargetSelectionSet rightTargetSelectionSet,
                  leftExtractedSelectionSet.Perm leftTargetSelectionSet
                  ∧ rightExtractedSelectionSet.Perm rightTargetSelectionSet
                  ∧ SelectionSetInclusionCaseReady schema responseFuel
                      fixedExecutionParentType targetValues leftTargetSelectionSet
                      rightTargetSelectionSet runtimeType)
    : guardedFieldGroupsIncludeWithFuel schema responseFuel
        fixedExecutionParentType checkValues
        (guardedFieldGroups
          (SelectionConditions.ofTypeRegion schema parentRegion
            leftExtractedSelectionSet))
        (guardedFieldGroups
          (SelectionConditions.ofTypeRegion schema parentRegion
            rightExtractedSelectionSet))
      = true := by
  let leftEntries := SelectionConditions.ofTypeRegion schema parentRegion leftExtractedSelectionSet
  let rightEntries := SelectionConditions.ofTypeRegion schema parentRegion rightExtractedSelectionSet
  let leftGroups := guardedFieldGroups leftEntries
  let rightGroups := guardedFieldGroups rightEntries
  let childIncludes := fun knownValues possibleTypes leftSelectionSet
      rightSelectionSet =>
    match responseFuel with
    | 0 => true
    | childFuel + 1 =>
        guardedFieldChildIncludesBool schema childFuel knownValues possibleTypes
          leftSelectionSet rightSelectionSet
  apply guardedFieldGroupsIncludeWithFuel_complete_cases schema responseFuel
    fixedExecutionParentType checkValues checkValues leftGroups rightGroups
    availableBooleanVariables childIncludes (booleanAssignmentsAgree_refl checkValues)
    hknown
  · intro right hright variableName hvariable
    have hwithin :=
      guardedFieldGroupFor_booleanVariablesWithin schema parentRegion
        leftExtractedSelectionSet rightExtractedSelectionSet leftGroups
        (by
          simp [leftGroups, leftEntries])
        right (by simpa [rightGroups, rightEntries] using hright) hvariable
    exact hwithin.elim (hleftWithin variableName) (hrightWithin variableName)
  · intro childFuel hfuel knownValues _hknownValues _hbaseAgrees possibleTypes
      leftSelectionSet rightSelectionSet hchild
    cases responseFuel with
    | zero => omega
    | succ responseFuel =>
        have heq : childFuel = responseFuel := by omega
        subst childFuel
        exact hchild
  · intro knownValues hknownValues hbaseAgrees right hright hgroupKnown
      targetValues htargetComplete htargetAgrees region hregion runtimeType hruntime
    have hruntimeLocalParent : runtimeType ∈
        guardedFieldParentRegion schema fixedExecutionParentType
          (guardedFieldGroupFor leftGroups right) right :=
      guardedFieldGroupTypeRegions_subset
        (guardedFieldParentRegion schema fixedExecutionParentType
          (guardedFieldGroupFor leftGroups right) right)
        (guardedFieldGroupFor leftGroups right) right hregion hruntime
    have hruntimeParent : runtimeType ∈ parentRegion := by
      cases hfixed : fixedExecutionParentType with
      | some parentType =>
          rw [hfixedParentRegion parentType hfixed]
          simpa [guardedFieldParentRegion, hfixed] using hruntimeLocalParent
      | none =>
          apply guardedFieldGroupFor_parentRegion_subset schema parentRegion
            leftExtractedSelectionSet rightExtractedSelectionSet leftGroups
            (by
              simp [leftGroups, leftEntries])
            right
          · simpa [rightGroups, rightEntries] using hright
          · simpa [hfixed] using hruntimeLocalParent
    have hcheckAgrees : BooleanAssignmentsAgree checkValues targetValues :=
      booleanAssignmentsAgree_trans hbaseAgrees htargetAgrees
    rcases hcases targetValues htargetComplete hcheckAgrees runtimeType
        hruntimeParent with
      ⟨leftTargetSelectionSet, rightTargetSelectionSet, hleftSelectionSet,
        hrightSelectionSet, hparentCase⟩
    let executionParentType := fixedExecutionParentType.getD runtimeType
    let runtimeLeftGroups := collectRuntimeFieldGroups schema targetValues runtimeType
      runtimeType leftTargetSelectionSet
    let runtimeRightGroups := collectRuntimeFieldGroups schema targetValues runtimeType
      runtimeType rightTargetSelectionSet
    have hleftEquivalent : RuntimeGroupsPermutationEquivalent
        (guardedFieldRuntimeGroups targetValues runtimeType leftGroups)
        runtimeLeftGroups := by
      apply runtimeGroupsPermutationEquivalent_trans
        (guardedFieldRuntimeGroups_permutationEquivalent targetValues runtimeType leftEntries)
      exact selectionConditionsForRegion_runtimeGroups_permutationEquivalent schema
        parentRegion hleftSelectionSet targetValues runtimeType runtimeType PUnit.unit
        hruntimeParent
    have hrightEquivalent : RuntimeGroupsPermutationEquivalent
        (guardedFieldRuntimeGroups targetValues runtimeType rightGroups)
        runtimeRightGroups := by
      apply runtimeGroupsPermutationEquivalent_trans
        (guardedFieldRuntimeGroups_permutationEquivalent targetValues runtimeType rightEntries)
      exact selectionConditionsForRegion_runtimeGroups_permutationEquivalent schema
        parentRegion hrightSelectionSet targetValues runtimeType runtimeType PUnit.unit
        hruntimeParent
    have hruntimeLeftReady := executableGroupsSemanticsReady_collectFields schema targetValues
      runtimeType PUnit.unit leftTargetSelectionSet hparentCase.1
      hparentCase.2.2.1 hparentCase.2.2.2.1
    have hruntimeRightReady := executableGroupsSemanticsReady_collectFields schema targetValues
      runtimeType PUnit.unit rightTargetSelectionSet hparentCase.1
      hparentCase.2.2.2.2.1 hparentCase.2.2.2.2.2.1
    cases responseFuel with
    | zero =>
        have hruntimeEmpty : runtimeRightGroups.isEmpty = true := by
          simpa [selectionSetIncludesAtRuntimeBoolWithFuel, runtimeRightGroups]
            using hparentCase.2.2.2.2.2.2
        have hguardedEmpty :
            (guardedFieldRuntimeGroups targetValues runtimeType rightGroups).isEmpty
              = true := by
          rw [runtimeGroupsPermutationEquivalent_isEmpty_iff hrightEquivalent]
          exact hruntimeEmpty
        have hfullInclude : guardedFieldRuntimeGroupsIncludeBool schema 0
            fixedExecutionParentType targetValues runtimeType leftGroups rightGroups
            (childIncludes knownValues) = true := by
          unfold guardedFieldRuntimeGroupsIncludeBool
          simpa [executionParentType, hparentCase.2.1] using hguardedEmpty
        exact guardedFieldGroupCases_complete_runtime schema 0
          fixedExecutionParentType targetValues runtimeType leftGroups rightGroups
          (childIncludes knownValues)
          (by simpa [leftGroups] using guardedFieldGroups_responseNames_nodup leftEntries)
          hfullInclude right hright
    | succ childFuel =>
        let guardedLeftFields := guardedFieldExecutableFields targetValues runtimeType
          (guardedFieldGroupFor leftGroups right).entries
        let guardedRightFields := guardedFieldExecutableFields targetValues runtimeType
          right.entries
        let guardedLeftLocalGroups := executableFieldsAsGroup
          (guardedFieldGroupFor leftGroups right).responseName guardedLeftFields
        let guardedRightLocalGroups := executableFieldsAsGroup right.responseName
          guardedRightFields
        unfold guardedFieldGroupCaseIncludesBool
        simp only [childIncludes]
        rw [hparentCase.2.1]
        change executableGroupsIncludeBool schema runtimeType
            (fun outputType leftSelectionSet rightSelectionSet =>
              guardedFieldChildIncludesBool schema childFuel knownValues
                (schema.getPossibleTypes outputType.namedType) leftSelectionSet
                rightSelectionSet)
            guardedLeftLocalGroups guardedRightLocalGroups = true
        cases hrightFields : guardedRightFields with
        | nil =>
            simp [guardedRightLocalGroups, executableFieldsAsGroup, hrightFields,
              executableGroupsIncludeBool]
        | cons rightHead rightRest =>
            have hguardedRightLocal :
                (right.responseName, rightHead :: rightRest) ∈ guardedRightLocalGroups := by
              simp [guardedRightLocalGroups, executableFieldsAsGroup, hrightFields]
            have hguardedRightFull :
                (right.responseName, rightHead :: rightRest) ∈
                  guardedFieldRuntimeGroups targetValues runtimeType rightGroups := by
              apply guardedFieldRuntimeGroup_component_mem targetValues runtimeType
                rightGroups right hright
              simpa [guardedRightFields] using hguardedRightLocal
            rcases runtimeGroupsPermutationEquivalent_singleton_of_mem
                hrightEquivalent hguardedRightFull with
              ⟨runtimeRightFields, hruntimeRightGroup, hrightSingleton⟩
            have hruntimeInclude : executableGroupsIncludeBool schema runtimeType
                (fun outputType leftSelectionSet rightSelectionSet =>
                  (schema.getPossibleTypes outputType.namedType).all
                    fun candidateRuntimeType =>
                      selectionSetIncludesBoolWithFuel schema childFuel
                        candidateRuntimeType targetValues leftSelectionSet
                        rightSelectionSet)
                runtimeLeftGroups runtimeRightGroups = true := by
              simpa [selectionSetIncludesAtRuntimeBoolWithFuel, runtimeLeftGroups,
                runtimeRightGroups]
                using hparentCase.2.2.2.2.2.2
            have hruntimeRightIncluded := List.all_eq_true.mp hruntimeInclude
              (right.responseName, runtimeRightFields) hruntimeRightGroup
            unfold executableGroupIncludedBool at hruntimeRightIncluded
            rcases List.any_eq_true.mp hruntimeRightIncluded with
              ⟨runtimeLeftGroup, hruntimeLeftGroup, hruntimeMatch⟩
            rcases runtimeLeftGroup with ⟨leftName, runtimeLeftFields⟩
            simp only [Bool.and_eq_true] at hruntimeMatch
            have hname : leftName = right.responseName := beq_iff_eq.mp hruntimeMatch.1
            rcases runtimeGroupsPermutationEquivalent_singleton_of_mem
                (runtimeGroupsPermutationEquivalent_symm hleftEquivalent)
                hruntimeLeftGroup with
              ⟨guardedLeftFields', hguardedLeftFull, hleftSingletonRuntime⟩
            have hguardedLeftLocal : (leftName, guardedLeftFields') ∈ guardedLeftLocalGroups := by
              apply guardedFieldGroupFor_runtimeGroup_mem targetValues runtimeType
                leftGroups right
                (by simpa [leftGroups] using
                  guardedFieldGroups_responseNames_nodup leftEntries)
                (leftName, guardedLeftFields') hguardedLeftFull hname
            have hleftSingleton : RuntimeGroupsPermutationEquivalent
                [(leftName, guardedLeftFields')] [(leftName, runtimeLeftFields)] := by
              exact runtimeGroupsPermutationEquivalent_symm hleftSingletonRuntime
            have hruntimeSingletonInclude : executableGroupsIncludeBool schema runtimeType
                (fun outputType leftSelectionSet rightSelectionSet =>
                  (schema.getPossibleTypes outputType.namedType).all
                    fun candidateRuntimeType =>
                      selectionSetIncludesBoolWithFuel schema childFuel
                        candidateRuntimeType targetValues leftSelectionSet
                        rightSelectionSet)
                [(leftName, runtimeLeftFields)]
                [(right.responseName, runtimeRightFields)] = true := by
              simpa [executableGroupsIncludeBool, executableGroupIncludedBool]
                using hruntimeMatch
            have hruntimeLeftSingletonReady : executableGroupsSemanticsReady schema runtimeType
                [(leftName, runtimeLeftFields)] := by
              intro responseName fields hgroup
              have heq : (responseName, fields) = (leftName, runtimeLeftFields) := by
                simpa using hgroup
              injection heq with hnameEq hfieldsEq
              subst responseName
              subst fields
              exact hruntimeLeftReady leftName runtimeLeftFields hruntimeLeftGroup
            have hruntimeRightSingletonReady : executableGroupsSemanticsReady schema runtimeType
                [(right.responseName, runtimeRightFields)] := by
              intro responseName fields hgroup
              have heq : (responseName, fields) =
                  (right.responseName, runtimeRightFields) := by simpa using hgroup
              injection heq with hnameEq hfieldsEq
              subst responseName
              subst fields
              exact hruntimeRightReady right.responseName runtimeRightFields hruntimeRightGroup
            have hguardedSingletonInclude : executableGroupsIncludeBool schema runtimeType
                (fun outputType leftSelectionSet rightSelectionSet =>
                  guardedFieldChildIncludesBool schema childFuel knownValues
                    (schema.getPossibleTypes outputType.namedType) leftSelectionSet
                    rightSelectionSet)
                [(leftName, guardedLeftFields')]
                [(right.responseName, rightHead :: rightRest)] = true := by
              apply executableGroupsIncludeBool_transport_of_ready schema runtimeType
                (fun outputType leftSelectionSet rightSelectionSet =>
                  guardedFieldChildIncludesBool schema childFuel knownValues
                    (schema.getPossibleTypes outputType.namedType) leftSelectionSet
                    rightSelectionSet)
                (fun outputType leftSelectionSet rightSelectionSet =>
                  (schema.getPossibleTypes outputType.namedType).all
                    fun candidateRuntimeType =>
                      selectionSetIncludesBoolWithFuel schema childFuel
                        candidateRuntimeType targetValues leftSelectionSet
                        rightSelectionSet)
                [(leftName, guardedLeftFields')]
                [(right.responseName, rightHead :: rightRest)]
                [(leftName, runtimeLeftFields)]
                [(right.responseName, runtimeRightFields)] hleftSingleton
                hrightSingleton hruntimeLeftSingletonReady hruntimeRightSingletonReady
              · intro fieldType candidateLeftName candidateRightName
                  candidateRuntimeLeftFields candidateGuardedLeftFields
                  candidateRuntimeRightFields candidateGuardedRightFields
                  hcandidateRuntimeLeft hcandidateGuardedLeft hcandidateRuntimeRight
                  hcandidateGuardedRight hresponseName hleftFieldsPerm
                  hrightFieldsPerm hruntimeLeftWitness hguardedLeftWitness
                  hruntimeRightWitness hguardedRightWitness _hrawChild
                have hruntimeLeftEq :
                    (candidateLeftName, candidateRuntimeLeftFields) =
                      (leftName, runtimeLeftFields) := by simpa using hcandidateRuntimeLeft
                have hguardedLeftEq :
                    (candidateLeftName, candidateGuardedLeftFields) =
                      (leftName, guardedLeftFields') := by simpa using hcandidateGuardedLeft
                have hruntimeRightEq :
                    (candidateRightName, candidateRuntimeRightFields) =
                      (right.responseName, runtimeRightFields) := by
                  simpa using hcandidateRuntimeRight
                have hguardedRightEq :
                    (candidateRightName, candidateGuardedRightFields) =
                      (right.responseName, rightHead :: rightRest) := by
                  simpa using hcandidateGuardedRight
                injection hruntimeLeftEq with hruntimeLeftNameEq hruntimeLeftFieldsEq
                injection hguardedLeftEq with _ hguardedLeftFieldsEq
                injection hruntimeRightEq with hruntimeRightNameEq hruntimeRightFieldsEq
                injection hguardedRightEq with _ hguardedRightFieldsEq
                subst candidateLeftName
                subst candidateRightName
                subst candidateRuntimeLeftFields
                subst candidateGuardedLeftFields
                subst candidateRuntimeRightFields
                subst candidateGuardedRightFields
                let possibleTypes := schema.getPossibleTypes fieldType.namedType
                have hleftChildSelectionSet :
                    (executableFieldsMergedSelectionSet guardedLeftFields').Perm
                      (executableFieldsMergedSelectionSet runtimeLeftFields) := by
                  simpa [executableFieldsMergedSelectionSet_eq_mergedFieldSelectionSet]
                    using Execution.FieldGroups.mergedFieldSelectionSet_perm
                      hleftFieldsPerm.symm
                have hrightChildSelectionSet :
                    (executableFieldsMergedSelectionSet (rightHead :: rightRest)).Perm
                      (executableFieldsMergedSelectionSet runtimeRightFields) := by
                  simpa [executableFieldsMergedSelectionSet_eq_mergedFieldSelectionSet]
                    using Execution.FieldGroups.mergedFieldSelectionSet_perm
                      hrightFieldsPerm.symm
                unfold guardedFieldChildIncludesBool
                simp only [Bool.or_eq_true]
                right
                apply guardedFieldGroupsIncludeWithFuel_semantic_complete schema
                  hschema childFuel none knownValues possibleTypes
                  (executableFieldsMergedSelectionSet guardedLeftFields')
                  (executableFieldsMergedSelectionSet (rightHead :: rightRest))
                  availableBooleanVariables hknownValues
                · intro variableName hvariable
                  have hruntimeVariable :=
                    (selectionSetBooleanVariables_perm
                      hleftChildSelectionSet).mem_iff.mp hvariable
                  have htargetVariable := mergedSelectionSet_variables_within_of_group_mem
                    schema targetValues runtimeType runtimeType leftTargetSelectionSet
                    (leftName, runtimeLeftFields)
                    (by simpa using hruntimeLeftGroup) variableName hruntimeVariable
                  exact hleftWithin variableName
                    ((selectionSetBooleanVariables_perm hleftSelectionSet).mem_iff.mpr
                      htargetVariable)
                · intro variableName hvariable
                  have hruntimeVariable :=
                    (selectionSetBooleanVariables_perm
                      hrightChildSelectionSet).mem_iff.mp hvariable
                  have htargetVariable := mergedSelectionSet_variables_within_of_group_mem
                    schema targetValues runtimeType runtimeType rightTargetSelectionSet
                    (right.responseName, runtimeRightFields)
                    (by simpa using hruntimeRightGroup) variableName hruntimeVariable
                  exact hrightWithin variableName
                    ((selectionSetBooleanVariables_perm hrightSelectionSet).mem_iff.mpr
                      htargetVariable)
                · simp
                · intro childValues hchildComplete hchildAgrees childRuntimeType
                    hchildRuntime
                  have houterAgrees : BooleanAssignmentsAgree checkValues childValues :=
                    booleanAssignmentsAgree_trans hbaseAgrees hchildAgrees
                  rcases hcases childValues hchildComplete houterAgrees runtimeType
                      hruntimeParent with
                    ⟨childOuterLeftSelectionSet, childOuterRightSelectionSet,
                      hchildOuterLeftSelectionSet, hchildOuterRightSelectionSet,
                      houterCase⟩
                  let childRuntimeLeftGroups := collectRuntimeFieldGroups schema childValues
                    runtimeType runtimeType childOuterLeftSelectionSet
                  let childRuntimeRightGroups := collectRuntimeFieldGroups schema childValues
                    runtimeType runtimeType childOuterRightSelectionSet
                  have hleftVariableAgreement : ∀ variableName,
                      variableName ∈ guardedFieldGroupBooleanVariables
                          (guardedFieldGroupFor leftGroups right) right
                      -> inputValueBoolean? targetValues (.variable variableName)
                          = inputValueBoolean? childValues (.variable variableName) := by
                    intro variableName hvariable
                    rcases hgroupKnown variableName hvariable with ⟨value, hvalue⟩
                    exact (htargetAgrees variableName value hvalue).trans
                      (hchildAgrees variableName value hvalue).symm
                  have hleftFieldsEqual :=
                    guardedFieldExecutableFields_eq_of_region_and_variables
                      (guardedFieldParentRegion schema fixedExecutionParentType
                        (guardedFieldGroupFor leftGroups right) right)
                      (guardedFieldGroupFor leftGroups right) right
                      (guardedFieldGroupFor leftGroups right) (Or.inl rfl)
                      hregion hruntime hruntime hleftVariableAgreement
                  have hrightFieldsEqual :=
                    guardedFieldExecutableFields_eq_of_region_and_variables
                      (guardedFieldParentRegion schema fixedExecutionParentType
                        (guardedFieldGroupFor leftGroups right) right)
                      (guardedFieldGroupFor leftGroups right) right right
                      (Or.inr rfl) hregion hruntime hruntime hleftVariableAgreement
                  have hchildLeftEquivalent : RuntimeGroupsPermutationEquivalent
                      (guardedFieldRuntimeGroups childValues runtimeType leftGroups)
                      childRuntimeLeftGroups := by
                    apply runtimeGroupsPermutationEquivalent_trans
                      (guardedFieldRuntimeGroups_permutationEquivalent childValues
                        runtimeType leftEntries)
                    exact selectionConditionsForRegion_runtimeGroups_permutationEquivalent
                      schema parentRegion hchildOuterLeftSelectionSet childValues runtimeType
                      runtimeType PUnit.unit hruntimeParent
                  have hchildRightEquivalent : RuntimeGroupsPermutationEquivalent
                      (guardedFieldRuntimeGroups childValues runtimeType rightGroups)
                      childRuntimeRightGroups := by
                    apply runtimeGroupsPermutationEquivalent_trans
                      (guardedFieldRuntimeGroups_permutationEquivalent childValues
                        runtimeType rightEntries)
                    exact selectionConditionsForRegion_runtimeGroups_permutationEquivalent
                      schema parentRegion hchildOuterRightSelectionSet childValues runtimeType
                      runtimeType PUnit.unit hruntimeParent
                  have hchildGuardedLeft : (leftName, guardedLeftFields') ∈
                      guardedFieldRuntimeGroups childValues runtimeType leftGroups := by
                    have htargetLocal :
                        (leftName, guardedLeftFields') ∈
                          guardedLeftLocalGroups := hguardedLeftLocal
                    have hchildLocal :
                        (leftName, guardedLeftFields') ∈
                          executableFieldsAsGroup
                            (guardedFieldGroupFor leftGroups right).responseName
                            (guardedFieldExecutableFields childValues runtimeType
                              (guardedFieldGroupFor leftGroups right).entries) := by
                      rw [← hleftFieldsEqual]
                      simpa [guardedLeftLocalGroups, guardedLeftFields] using htargetLocal
                    exact guardedFieldGroupFor_runtimeGroups_subset childValues
                      runtimeType leftGroups right _ hchildLocal
                  have hchildGuardedRight :
                      (right.responseName, rightHead :: rightRest) ∈
                        guardedFieldRuntimeGroups childValues runtimeType rightGroups := by
                    apply guardedFieldRuntimeGroup_component_mem childValues
                      runtimeType rightGroups right hright
                    rw [← hrightFieldsEqual]
                    simpa [guardedRightLocalGroups, guardedRightFields] using hguardedRightLocal
                  rcases runtimeGroupsPermutationEquivalent_matchingGroup
                      hchildLeftEquivalent hchildGuardedLeft with
                    ⟨childRuntimeLeftFields, hchildRuntimeLeftGroup,
                      hchildLeftFieldsPerm⟩
                  rcases runtimeGroupsPermutationEquivalent_matchingGroup
                      hchildRightEquivalent hchildGuardedRight with
                    ⟨childRuntimeRightFields, hchildRuntimeRightGroup,
                      hchildRightFieldsPerm⟩
                  have hchildRuntimeLeftReady := executableGroupsSemanticsReady_collectFields schema
                    childValues runtimeType PUnit.unit childOuterLeftSelectionSet
                    houterCase.1 houterCase.2.2.1 houterCase.2.2.2.1
                  have hchildRuntimeRightReady := executableGroupsSemanticsReady_collectFields schema
                    childValues runtimeType PUnit.unit childOuterRightSelectionSet
                    houterCase.1 houterCase.2.2.2.2.1
                    houterCase.2.2.2.2.2.1
                  have hchildRuntimeInclude : executableGroupsIncludeBool schema runtimeType
                      (fun outputType leftSelectionSet rightSelectionSet =>
                        (schema.getPossibleTypes outputType.namedType).all
                          fun candidateRuntimeType =>
                            selectionSetIncludesBoolWithFuel schema childFuel
                              candidateRuntimeType childValues leftSelectionSet
                              rightSelectionSet)
                      childRuntimeLeftGroups childRuntimeRightGroups = true := by
                    simpa [selectionSetIncludesAtRuntimeBoolWithFuel,
                      childRuntimeLeftGroups, childRuntimeRightGroups]
                      using houterCase.2.2.2.2.2.2
                  have hleftWitness := completionFieldsWitness_of_perm
                    hchildLeftFieldsPerm
                    (by simpa using hguardedLeftWitness)
                  have hrightWitness := completionFieldsWitness_of_perm
                    hchildRightFieldsPerm
                    (by simpa using hguardedRightWitness)
                  have hchildSemantic := executableGroupsIncludeBool_child_at_runtime
                    schema hschema childFuel runtimeType childValues childRuntimeLeftGroups
                    childRuntimeRightGroups leftName right.responseName
                    childRuntimeLeftFields childRuntimeRightFields fieldType childRuntimeType
                    hchildLeftEquivalent.rightKeysNodup
                    hchildRuntimeLeftReady hchildRuntimeRightReady
                    hchildRuntimeLeftGroup hchildRuntimeRightGroup
                    hname hleftWitness hrightWitness hchildRuntime
                    hchildRuntimeInclude
                  have hchildObject :=
                    SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
                      hschema fieldType.namedType childRuntimeType hchildRuntime
                  have hleftCompletionReady : completionFieldsSemanticsReady schema runtimeType fieldType
                      childRuntimeLeftFields :=
                    ⟨hchildRuntimeLeftReady leftName childRuntimeLeftFields
                      hchildRuntimeLeftGroup, hleftWitness⟩
                  have hrightCompletionReady : completionFieldsSemanticsReady schema runtimeType fieldType
                      childRuntimeRightFields :=
                    ⟨hchildRuntimeRightReady right.responseName childRuntimeRightFields
                      hchildRuntimeRightGroup, hrightWitness⟩
                  have hincludes : schema.typeIncludesObjectBool fieldType.namedType
                      childRuntimeType = true := List.contains_iff_mem.mpr hchildRuntime
                  refine ⟨executableFieldsMergedSelectionSet childRuntimeLeftFields,
                    executableFieldsMergedSelectionSet childRuntimeRightFields,
                    ?_, ?_, hchildObject, rfl, ?_, ?_, ?_, ?_, ?_⟩
                  · simpa [executableFieldsMergedSelectionSet_eq_mergedFieldSelectionSet]
                      using Execution.FieldGroups.mergedFieldSelectionSet_perm
                        hchildLeftFieldsPerm
                  · simpa [executableFieldsMergedSelectionSet_eq_mergedFieldSelectionSet]
                      using Execution.FieldGroups.mergedFieldSelectionSet_perm
                        hchildRightFieldsPerm
                  · simpa using completionFieldsSemanticsReady_merged_semantics
                      hleftCompletionReady hincludes
                  · simpa using completionFieldsSemanticsReady_merged_canMerge
                      hleftCompletionReady childRuntimeType
                  · simpa using completionFieldsSemanticsReady_merged_semantics
                      hrightCompletionReady hincludes
                  · simpa using completionFieldsSemanticsReady_merged_canMerge
                      hrightCompletionReady childRuntimeType
                  · exact hchildSemantic
              · exact hruntimeSingletonInclude
            have hguardedRightIncluded := List.all_eq_true.mp hguardedSingletonInclude
              (right.responseName, rightHead :: rightRest) (by simp)
            have hlocalIncluded := executableGroupIncludedBool_mono_left schema runtimeType
              (fun outputType leftSelectionSet rightSelectionSet =>
                guardedFieldChildIncludesBool schema childFuel knownValues
                  (schema.getPossibleTypes outputType.namedType) leftSelectionSet
                  rightSelectionSet)
              [(leftName, guardedLeftFields')] guardedLeftLocalGroups
              (right.responseName, rightHead :: rightRest)
              (by
                intro group hgroup
                have heq : group = (leftName, guardedLeftFields') := by simpa using hgroup
                subst group
                exact hguardedLeftLocal)
              hguardedRightIncluded
            simpa [guardedRightLocalGroups, executableFieldsAsGroup, hrightFields,
              executableGroupsIncludeBool]
              using hlocalIncluded
termination_by (responseFuel, 2)
decreasing_by
  all_goals simp_wf
  apply Prod.Lex.left
  omega
end

theorem selectionSetIncludesBool_sound
    (schema : Schema) (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (responseFuel : Nat) (parentType : Name)
    (leftSelectionSet rightSelectionSet : List Selection)
    (targetValues : VariableValues)
    (hparentObject : schema.objectType parentType)
    (hleftReady
      : NormalForm.selectionSetSemanticsReady schema parentType leftSelectionSet)
    (hleftMerge : FieldMerge.fieldsInSetCanMerge schema parentType leftSelectionSet)
    (hrightReady
      : NormalForm.selectionSetSemanticsReady schema parentType rightSelectionSet)
    (hrightMerge : FieldMerge.fieldsInSetCanMerge schema parentType rightSelectionSet)
    (hleftComplete
      : boolVarsComplete
          (SelectionConditions.selectionSetBooleanVariables leftSelectionSet)
          targetValues)
    (hrightComplete
      : boolVarsComplete
          (SelectionConditions.selectionSetBooleanVariables rightSelectionSet)
          targetValues)
    (hcheck
      : selectionSetIncludesBool schema responseFuel parentType
          leftSelectionSet rightSelectionSet
        = true)
    : selectionSetIncludesBoolWithFuel schema responseFuel parentType targetValues
        leftSelectionSet rightSelectionSet
      = true := by
  have hparentSelf : parentType ∈ schema.getPossibleTypes parentType := by
    simp [getPossibleTypes_eq_singleton_of_object schema hparentObject]
  have hrootCheck : guardedFieldGroupsIncludeWithFuel schema responseFuel
      (some parentType) []
      (guardedFieldGroups
        (SelectionConditions.ofTypeRegion schema (schema.getPossibleTypes parentType)
          leftSelectionSet))
      (guardedFieldGroups
        (SelectionConditions.ofTypeRegion schema (schema.getPossibleTypes parentType)
          rightSelectionSet)) = true := by
    simpa [selectionSetIncludesBool, selectionSetIncludesBoolWithPartialAssignment,
      SelectionConditions.ofSelectionSet, SelectionConditions.ofSelectionSetInScope,
      SelectionConditions.rootCondition, SelectionConditions.ofTypeRegion]
      using hcheck
  have hresult := guardedFieldGroupsIncludeWithFuel_semantic_sound schema hschema
    responseFuel (some parentType) [] targetValues
    (schema.getPossibleTypes parentType) leftSelectionSet rightSelectionSet
    leftSelectionSet rightSelectionSet parentType hrootCheck
    (booleanAssignmentsAgree_nil targetValues) hleftComplete hrightComplete
    (List.Perm.refl _) (List.Perm.refl _) hparentSelf (by simp) hparentObject rfl
    hleftReady hleftMerge hrightReady hrightMerge
  rw [selectionSetIncludesBoolWithFuel,
    getPossibleTypes_eq_singleton_of_object schema hparentObject]
  simpa using hresult

theorem selectionSetIncludesBool_complete
    (schema : Schema) (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (responseFuel : Nat) (parentType : Name)
    (leftSelectionSet rightSelectionSet : List Selection)
    (hparentObject : schema.objectType parentType)
    (hleftReady
      : NormalForm.selectionSetSemanticsReady schema parentType leftSelectionSet)
    (hleftMerge : FieldMerge.fieldsInSetCanMerge schema parentType leftSelectionSet)
    (hrightReady
      : NormalForm.selectionSetSemanticsReady schema parentType rightSelectionSet)
    (hrightMerge : FieldMerge.fieldsInSetCanMerge schema parentType rightSelectionSet)
    (hcases
      : ∀ variableValues,
          boolVarsComplete
            (comparisonConditionVariables leftSelectionSet rightSelectionSet)
            variableValues
          -> selectionSetIncludesBoolWithFuel schema responseFuel parentType
                variableValues leftSelectionSet rightSelectionSet
              = true)
    : selectionSetIncludesBool schema responseFuel parentType leftSelectionSet
        rightSelectionSet
      = true := by
  have hrootCheck := guardedFieldGroupsIncludeWithFuel_semantic_complete schema
    hschema responseFuel (some parentType) [] (schema.getPossibleTypes parentType)
    leftSelectionSet rightSelectionSet
    (comparisonConditionVariables leftSelectionSet rightSelectionSet)
    (knownBooleanVariablesWithin_nil _)
    (by
      intro variableName hvariable
      simp [comparisonConditionVariables, hvariable])
    (by
      intro variableName hvariable
      simp [comparisonConditionVariables, hvariable])
    (by simp) (by
      intro variableValues hcomplete _hagrees runtimeType hruntime
      have hruntimeEq : runtimeType = parentType := by
        rw [getPossibleTypes_eq_singleton_of_object schema hparentObject]
          at hruntime
        simpa using hruntime
      subst runtimeType
      have hselectionCheck := hcases variableValues hcomplete
      rw [selectionSetIncludesBoolWithFuel.eq_def, List.all_eq_true] at hselectionCheck
      have hparentSelf : parentType ∈ schema.getPossibleTypes parentType := by
        simp [getPossibleTypes_eq_singleton_of_object schema hparentObject]
      exact ⟨leftSelectionSet, rightSelectionSet, List.Perm.refl _,
        List.Perm.refl _, hparentObject, rfl, hleftReady,
        hleftMerge, hrightReady, hrightMerge,
        hselectionCheck parentType hparentSelf⟩)
  simpa [selectionSetIncludesBool, selectionSetIncludesBoolWithPartialAssignment,
    SelectionConditions.ofSelectionSet, SelectionConditions.ofSelectionSetInScope,
    SelectionConditions.rootCondition, SelectionConditions.ofTypeRegion]
    using hrootCheck

theorem includesBool_to_selectionSetChecks
    {schema : Schema} {left right : Operation}
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hleftValid : Validation.operationDefinitionValid schema left)
    (hrightValid : Validation.operationDefinitionValid schema right)
    (hcheck : includesBool schema left right = true)
    : left.rootType schema = right.rootType schema
      ∧ sharedVariableDefinitionsSyntacticallyCompatibleBool
          left.variableDefinitions right.variableDefinitions
        = true
      ∧ ∀ variableValues,
          boolVarsComplete
            (comparisonConditionVariables left.selectionSet right.selectionSet)
            variableValues
          -> selectionSetIncludesBoolWithFuel schema (right.size + 1)
                (right.rootType schema) variableValues
                left.selectionSet right.selectionSet
              = true := by
  unfold includesBool at hcheck
  split at hcheck
  · rename_i hguard
    have hparts :
        (left.rootType schema == right.rootType schema) = true
          ∧ sharedVariableDefinitionsSyntacticallyCompatibleBool
            left.variableDefinitions right.variableDefinitions = true := by
      simpa only [Bool.and_eq_true] using hguard
    rcases hparts with ⟨hroot, hdefinitions⟩
    refine ⟨beq_iff_eq.mp hroot, hdefinitions, ?_⟩
    intro variableValues hcomplete
    have hleftComplete : boolVarsComplete
        (SelectionConditions.selectionSetBooleanVariables left.selectionSet)
        variableValues := boolVarsComplete_mono hcomplete (by
      intro variableName hvariable
      simp [comparisonConditionVariables, hvariable])
    have hrightComplete : boolVarsComplete
        (SelectionConditions.selectionSetBooleanVariables right.selectionSet)
        variableValues := boolVarsComplete_mono hcomplete (by
      intro variableName hvariable
      simp [comparisonConditionVariables, hvariable])
    have hrightObject : schema.objectType (right.rootType schema) :=
      NormalForm.CompleteNormalization.operation_root_object_of_valid hschema
        hrightValid
    have hleftReady : NormalForm.selectionSetSemanticsReady schema
        (right.rootType schema) left.selectionSet := by
      rw [← beq_iff_eq.mp hroot]
      exact
        NormalForm.CompleteNormalization.operation_selectionSetSemanticsReady_of_valid
          hschema hleftValid
    have hleftMerge : FieldMerge.fieldsInSetCanMerge schema
        (right.rootType schema) left.selectionSet := by
      rw [← beq_iff_eq.mp hroot]
      exact Validation.operationDefinitionValid_fieldsInSetCanMerge hleftValid
    exact selectionSetIncludesBool_sound schema hschema (right.size + 1)
      (right.rootType schema) left.selectionSet right.selectionSet variableValues
      hrightObject hleftReady hleftMerge
      (NormalForm.CompleteNormalization.operation_selectionSetSemanticsReady_of_valid
        hschema hrightValid)
      (Validation.operationDefinitionValid_fieldsInSetCanMerge hrightValid)
      hleftComplete hrightComplete hcheck
  · simp at hcheck

theorem includesBool_complete_of_reference
    {schema : Schema} {left right : Operation}
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hleftValid : Validation.operationDefinitionValid schema left)
    (hrightValid : Validation.operationDefinitionValid schema right)
    (hcheck : includesBoolReference schema left right = true)
    : includesBool schema left right = true := by
  rcases includesBoolReference_to_selectionSetChecks hcheck with
    ⟨hroot, hdefinitions, hcases⟩
  have hguard : (left.rootType schema == right.rootType schema
      && sharedVariableDefinitionsSyntacticallyCompatibleBool
        left.variableDefinitions right.variableDefinitions) = true := by
    simp [hroot, hdefinitions]
  unfold includesBool
  rw [ite_eq_left hguard]
  have hrightObject : schema.objectType (right.rootType schema) :=
    NormalForm.CompleteNormalization.operation_root_object_of_valid hschema
      hrightValid
  have hleftReady : NormalForm.selectionSetSemanticsReady schema
      (right.rootType schema) left.selectionSet := by
    rw [← hroot]
    exact
      NormalForm.CompleteNormalization.operation_selectionSetSemanticsReady_of_valid
        hschema hleftValid
  have hleftMerge : FieldMerge.fieldsInSetCanMerge schema
      (right.rootType schema) left.selectionSet := by
    rw [← hroot]
    exact Validation.operationDefinitionValid_fieldsInSetCanMerge hleftValid
  exact selectionSetIncludesBool_complete schema hschema (right.size + 1)
    (right.rootType schema) left.selectionSet right.selectionSet hrightObject
    hleftReady hleftMerge
    (NormalForm.CompleteNormalization.operation_selectionSetSemanticsReady_of_valid
      hschema hrightValid)
    (Validation.operationDefinitionValid_fieldsInSetCanMerge hrightValid)
    (fun conditionValues _hcomplete => hcases conditionValues)

end QueryInclusion
end GraphQL
