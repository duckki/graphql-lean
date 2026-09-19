import GraphQL.Theories.TreeSummary.ExactCases
import Proofs.GraphQL.Theories.ConditionTree.Reduce.RuntimeBundles
import Proofs.GraphQL.Theories.ConditionTree.RuntimeExtraction
import Proofs.GraphQL.Theories.TreeSummary.Algebra
import Proofs.GraphQL.Theories.TreeSummary.PossibleTypeRegions
import Proofs.GraphQL.Theories.TreeSummary.ExactCases.VariableValues
import Proofs.GraphQL.Theories.TreeSummary.ExactCases.CaseTrace

/-! The deterministic runtime path through the incremental exact-case cursor. -/

namespace GraphQL
namespace TreeSummary
namespace ExactCases

open GraphQL.ConditionTree
open GraphQL.Execution
open Internal
open _root_.GraphQL.TreeSummary.ExactCases.Measure

namespace RuntimeCase

def chooseTypeRegion (runtimeType : Name) (fallback : PossibleTypeRegion)
    : List PossibleTypeRegion -> PossibleTypeRegion
  | [] => fallback
  | region :: rest =>
      if region.contains runtimeType then
        region
      else
        chooseTypeRegion runtimeType fallback rest

theorem chooseTypeRegion_mem_of_exists
    (runtimeType : Name) (fallback : PossibleTypeRegion)
    (regions : List PossibleTypeRegion)
    (hexists : ∃ region, region ∈ regions ∧ runtimeType ∈ region)
    : let chosen := chooseTypeRegion runtimeType fallback regions
      chosen ∈ regions ∧ runtimeType ∈ chosen := by
  induction regions with
  | nil => simp at hexists
  | cons region rest ih =>
      simp only [chooseTypeRegion]
      cases hcontains : region.contains runtimeType with
      | true => simp [List.contains_iff_mem.mp hcontains]
      | false =>
          have hnotmem : runtimeType ∉ region := by
            intro hmem
            exact Bool.noConfusion
              (hcontains.symm.trans (List.contains_iff_mem.mpr hmem))
          have hrest : ∃ candidate, candidate ∈ rest ∧ runtimeType ∈ candidate := by
            rcases hexists with ⟨candidate, hcandidate, hruntime⟩
            rcases List.mem_cons.mp hcandidate with rfl | hcandidate
            · exact False.elim (hnotmem hruntime)
            · exact ⟨candidate, hcandidate, hruntime⟩
          have hchosen := ih hrest
          exact ⟨List.mem_cons_of_mem region hchosen.1, hchosen.2⟩

theorem chooseTypeRegion_mem
    (scope : PossibleTypeRegion) (conditions : List PossibleTypes)
    (runtimeType : Name) (hruntime : runtimeType ∈ scope)
    : let regions := possibleTypeRegions scope conditions
      let chosen := chooseTypeRegion runtimeType scope regions
      chosen ∈ regions ∧ runtimeType ∈ chosen := by
  have hexact := possibleTypeRegions_exact scope conditions
  rcases hexact.2.1 runtimeType hruntime with ⟨region, hregion, _hunique⟩
  exact chooseTypeRegion_mem_of_exists runtimeType scope
    (possibleTypeRegions scope conditions) ⟨region, hregion.1, hregion.2⟩

theorem chooseTypeRegion_eq_of_mem
    (scope : PossibleTypeRegion) (conditions : List PossibleTypes)
    (runtimeType : Name) (hruntime : runtimeType ∈ scope)
    (region : PossibleTypeRegion)
    (hregion : region ∈ possibleTypeRegions scope conditions)
    (hregionRuntime : runtimeType ∈ region)
    : chooseTypeRegion runtimeType scope (possibleTypeRegions scope conditions)
      = region := by
  have hchosen := chooseTypeRegion_mem scope conditions runtimeType hruntime
  have hchosenClass := possibleTypeRegions_membershipClass scope conditions
    _ hchosen.1 runtimeType hchosen.2
  have hregionClass := possibleTypeRegions_membershipClass scope conditions
    region hregion runtimeType hregionRuntime
  exact hchosenClass.trans hregionClass.symm

private theorem unresolvedBranchesCount_append (left right : List (Branch Tree))
    : unresolvedBranchesCount (left ++ right)
      = unresolvedBranchesCount left + unresolvedBranchesCount right := by
  induction left with
  | nil => simp [unresolvedBranchesCount]
  | cons branch rest ih => simp [unresolvedBranchesCount, ih, Nat.add_assoc]

private theorem skipBranch_unresolved_lt (cursor : CaseCursor)
    (branch : Branch Tree) (rest : List (Branch Tree))
    (hbranches : cursor.pendingBranches = branch :: rest)
    : caseCursorUnresolvedCount (cursor.skipBranch rest)
      < caseCursorUnresolvedCount cursor := by
  simp [caseCursorUnresolvedCount, CaseCursor.skipBranch, hbranches,
    unresolvedBranchesCount]
  omega

private theorem selectBranch_unresolved_lt (cursor : CaseCursor)
    (branch : Branch Tree) (rest : List (Branch Tree))
    (hbranches : cursor.pendingBranches = branch :: rest)
    : caseCursorUnresolvedCount (cursor.selectBranch branch.body rest)
      < caseCursorUnresolvedCount cursor := by
  simp [caseCursorUnresolvedCount, CaseCursor.selectBranch, hbranches,
    unresolvedBranchesCount_append, unresolvedBranchesCount,
    unresolvedBranchCount]

private theorem resolveBooleanBranch_unresolved_lt (cursor : CaseCursor)
    (branch : Branch Tree) (rest : List (Branch Tree))
    (hbranches : cursor.pendingBranches = branch :: rest)
    (literal : BooleanLiteral) (value : Bool)
    : caseCursorUnresolvedCount
        (cursor.resolveBooleanBranch branch.body rest literal value)
      < caseCursorUnresolvedCount cursor := by
  unfold CaseCursor.resolveBooleanBranch
  split
  · exact selectBranch_unresolved_lt cursor branch rest hbranches
  · exact skipBranch_unresolved_lt cursor branch rest hbranches

private theorem nextTypeBranch_unresolved_lt (cursor : CaseCursor)
    (branch : Branch Tree) (rest : List (Branch Tree))
    (hbranches : cursor.pendingBranches = branch :: rest)
    (selected : Bool)
    : caseCursorUnresolvedCount
        (if selected then
            cursor.selectBranch branch.body rest
          else
            cursor.skipBranch rest)
      < caseCursorUnresolvedCount cursor := by
  cases selected
  · exact skipBranch_unresolved_lt cursor branch rest hbranches
  · exact selectBranch_unresolved_lt cursor branch rest hbranches

structure Resolved where
  cursor : CaseCursor
  possibleTypes : PossibleTypeRegion
  inheritedBooleanCondition : List BooleanLiteral

def resolve (inheritedBooleanCondition : List BooleanLiteral)
    (caseCondition : List BooleanLiteral) (cursor : CaseCursor)
    (possibleTypes : PossibleTypeRegion) (runtimeType : Name)
    (variableValues : VariableValues)
    : Resolved :=
  match _hbranches : cursor.pendingBranches with
  | [] =>
      {
        cursor
        possibleTypes
        inheritedBooleanCondition :=
          extendBooleanCondition inheritedBooleanCondition caseCondition
      }
  | branch :: rest =>
      match branch.condition with
      | .typeCondition _typeName =>
          let regions :=
            possibleTypeRegions possibleTypes [branch.body.condition.possibleTypes]
          let region := chooseTypeRegion runtimeType possibleTypes regions
          let nextCursor :=
            if possibleTypesSubset region branch.body.condition.possibleTypes then
              cursor.selectBranch branch.body rest
            else
              cursor.skipBranch rest
          resolve inheritedBooleanCondition caseCondition nextCursor region
            runtimeType variableValues
      | .booleanLiteral literal =>
          let value :=
            (inputValueBoolean? variableValues (.variable literal.variableName)).getD
              false
          let selectedLiteral :=
            if value then
              BooleanLiteral.positive literal.variableName
            else
              BooleanLiteral.negative literal.variableName
          resolve inheritedBooleanCondition (selectedLiteral :: caseCondition)
            (cursor.resolveBooleanBranch branch.body rest literal value)
            possibleTypes runtimeType variableValues
termination_by caseCursorUnresolvedCount cursor
decreasing_by
  · exact nextTypeBranch_unresolved_lt cursor branch rest _hbranches _
  · exact resolveBooleanBranch_unresolved_lt cursor branch rest _hbranches literal _

theorem resolve_nil
    (inheritedBooleanCondition caseCondition : List BooleanLiteral)
    (cursor : CaseCursor) (possibleTypes : PossibleTypeRegion)
    (runtimeType : Name) (variableValues : VariableValues)
    (hbranches : cursor.pendingBranches = [])
    : resolve inheritedBooleanCondition caseCondition cursor possibleTypes runtimeType
        variableValues
      = {
        cursor
        possibleTypes
        inheritedBooleanCondition :=
          Internal.extendBooleanCondition inheritedBooleanCondition caseCondition
      } := by
  rw [resolve.eq_1]
  split <;> rename_i hpending
  · rfl
  · simp [hbranches] at hpending

theorem resolve_typeCondition
    (inheritedBooleanCondition caseCondition : List BooleanLiteral)
    (cursor : CaseCursor) (possibleTypes : PossibleTypeRegion)
    (runtimeType : Name) (variableValues : VariableValues)
    (branch : Branch Tree) (rest : List (Branch Tree)) (typeName : Name)
    (hbranches : cursor.pendingBranches = branch :: rest)
    (hcondition : branch.condition = .typeCondition typeName)
    : let region :=
        chooseTypeRegion runtimeType possibleTypes
          (possibleTypeRegions possibleTypes [branch.body.condition.possibleTypes])
      resolve inheritedBooleanCondition caseCondition cursor possibleTypes runtimeType
        variableValues
      = resolve inheritedBooleanCondition caseCondition
          (if possibleTypesSubset region branch.body.condition.possibleTypes then
              cursor.selectBranch branch.body rest
            else
              cursor.skipBranch rest)
          region runtimeType variableValues := by
  rw [resolve.eq_1]
  split <;> rename_i hpending
  · simp [hbranches] at hpending
  · rcases List.cons.inj (hpending.symm.trans hbranches) with ⟨rfl, rfl⟩
    simp [hcondition]

theorem resolve_booleanLiteral
    (inheritedBooleanCondition caseCondition : List BooleanLiteral)
    (cursor : CaseCursor) (possibleTypes : PossibleTypeRegion)
    (runtimeType : Name) (variableValues : VariableValues)
    (branch : Branch Tree) (rest : List (Branch Tree)) (literal : BooleanLiteral)
    (hbranches : cursor.pendingBranches = branch :: rest)
    (hcondition : branch.condition = .booleanLiteral literal)
    : let value :=
        (inputValueBoolean? variableValues (.variable literal.variableName)).getD false
      resolve inheritedBooleanCondition caseCondition cursor possibleTypes runtimeType
        variableValues
      = resolve inheritedBooleanCondition
          ((if value then
              .positive literal.variableName
            else
              .negative literal.variableName)
            :: caseCondition)
          (cursor.resolveBooleanBranch branch.body rest literal value) possibleTypes
          runtimeType variableValues := by
  rw [resolve.eq_1]
  split <;> rename_i hpending
  · simp [hbranches] at hpending
  · rcases List.cons.inj (hpending.symm.trans hbranches) with ⟨rfl, rfl⟩
    simp [hcondition]

def fieldGroups (inheritedBooleanCondition : List BooleanLiteral)
    (cursor : CaseCursor) (possibleTypes : PossibleTypeRegion)
    (runtimeType : Name) (variableValues : VariableValues)
    : List CollectedFieldGroup :=
  let resolved :=
    resolve inheritedBooleanCondition [] cursor possibleTypes runtimeType variableValues
  resolved.cursor.fieldGroups resolved.inheritedBooleanCondition resolved.possibleTypes

def fieldGroupsFrom (inheritedBooleanCondition caseCondition : List BooleanLiteral)
    (cursor : CaseCursor) (possibleTypes : PossibleTypeRegion)
    (runtimeType : Name) (variableValues : VariableValues)
    : List CollectedFieldGroup :=
  let resolved :=
    resolve inheritedBooleanCondition caseCondition cursor possibleTypes
      runtimeType variableValues
  resolved.cursor.fieldGroups resolved.inheritedBooleanCondition resolved.possibleTypes

private def summarizeFrom (algebra : Algebra) (schema : Schema)
    (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
    (caseCondition : List BooleanLiteral) (cursor : CaseCursor)
    (possibleTypes : PossibleTypeRegion) (runtimeType : Name)
    (variableValues fixedVariableValues : VariableValues)
    : algebra.Summary :=
  match _hbranches : cursor.pendingBranches with
  | [] =>
      CaseCursor.summarizeFieldGroups algebra schema
        (cursor.fieldGroups
          (extendBooleanCondition inheritedBooleanCondition caseCondition)
          possibleTypes)
        variableValues fixedVariableValues
  | branch :: rest =>
      match branch.condition with
      | .typeCondition _typeName =>
          let regions :=
            possibleTypeRegions possibleTypes [branch.body.condition.possibleTypes]
          let region := chooseTypeRegion runtimeType possibleTypes regions
          let nextCursor :=
            if possibleTypesSubset region branch.body.condition.possibleTypes then
              cursor.selectBranch branch.body rest
            else
              cursor.skipBranch rest
          summarizeFrom algebra schema parentType inheritedBooleanCondition
            caseCondition
            nextCursor region runtimeType variableValues fixedVariableValues
      | .booleanLiteral literal =>
          let value :=
            (inputValueBoolean? variableValues (.variable literal.variableName)).getD
              false
          let selectedLiteral :=
            if value then
              BooleanLiteral.positive literal.variableName
            else
              BooleanLiteral.negative literal.variableName
          summarizeFrom algebra schema parentType inheritedBooleanCondition
            (selectedLiteral :: caseCondition)
            (cursor.resolveBooleanBranch branch.body rest literal value)
            possibleTypes runtimeType variableValues fixedVariableValues
termination_by caseCursorUnresolvedCount cursor
decreasing_by
  · exact nextTypeBranch_unresolved_lt cursor branch rest _hbranches _
  · exact resolveBooleanBranch_unresolved_lt cursor branch rest _hbranches literal _

def summarize (algebra : Algebra) (schema : Schema)
    (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
    (cursor : CaseCursor) (possibleTypes : PossibleTypeRegion)
    (runtimeType : Name) (variableValues : VariableValues)
    (fixedVariableValues : VariableValues := variableValues)
    : algebra.Summary :=
  summarizeFrom algebra schema parentType inheritedBooleanCondition [] cursor
    possibleTypes runtimeType variableValues fixedVariableValues

private theorem summarizeFrom_eq_resolved
    (algebra : Algebra) (schema : Schema)
    (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
    (caseCondition : List BooleanLiteral) (cursor : CaseCursor)
    (possibleTypes : PossibleTypeRegion) (runtimeType : Name)
    (variableValues fixedVariableValues : VariableValues)
    : summarizeFrom algebra schema parentType inheritedBooleanCondition
        caseCondition
        cursor possibleTypes runtimeType variableValues fixedVariableValues
      = let resolved :=
          resolve inheritedBooleanCondition caseCondition cursor possibleTypes
            runtimeType variableValues
        CaseCursor.summarizeFieldGroups algebra schema
          (resolved.cursor.fieldGroups resolved.inheritedBooleanCondition
            resolved.possibleTypes)
          variableValues fixedVariableValues := by
  rw [summarizeFrom, resolve.eq_1]
  split <;> rename_i hbranches
  · rfl
  · rename_i branch rest
    cases hcondition : branch.condition with
    | typeCondition typeName =>
        exact summarizeFrom_eq_resolved algebra schema parentType
          inheritedBooleanCondition caseCondition _ _ runtimeType variableValues
          fixedVariableValues
    | booleanLiteral literal =>
        simp only
        exact summarizeFrom_eq_resolved algebra schema parentType
          inheritedBooleanCondition
          ((if (inputValueBoolean? variableValues (.variable literal.variableName)).getD false
              then BooleanLiteral.positive literal.variableName
              else BooleanLiteral.negative literal.variableName) :: caseCondition) _
          possibleTypes runtimeType variableValues fixedVariableValues
termination_by caseCursorUnresolvedCount cursor
decreasing_by
  all_goals first
    | apply nextTypeBranch_unresolved_lt <;> assumption
    | apply resolveBooleanBranch_unresolved_lt <;> assumption

theorem summarize_eq_resolved
    (algebra : Algebra) (schema : Schema)
    (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
    (cursor : CaseCursor) (possibleTypes : PossibleTypeRegion)
    (runtimeType : Name) (variableValues fixedVariableValues : VariableValues)
    : summarize algebra schema parentType inheritedBooleanCondition cursor possibleTypes
        runtimeType variableValues fixedVariableValues
      = CaseCursor.summarizeFieldGroups algebra schema
          (fieldGroups inheritedBooleanCondition cursor possibleTypes
            runtimeType variableValues)
          variableValues fixedVariableValues := by
  unfold summarize fieldGroups
  exact summarizeFrom_eq_resolved algebra schema parentType inheritedBooleanCondition []
    cursor possibleTypes runtimeType variableValues fixedVariableValues

private theorem summarizeFrom_le
    (algebra : Algebra) {lawful : algebra.Lawful}
    (joinFactoringLaws : ExactCases.JoinFactoringLaws algebra lawful)
    (schema : Schema)
    (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
    (caseCondition : List BooleanLiteral) (cursor : CaseCursor)
    (possibleTypes : PossibleTypeRegion) (runtimeType : Name)
    (variableValues fixedVariableValues : VariableValues)
    (hruntime : runtimeType ∈ possibleTypes)
    : lawful.le
        (summarizeFrom algebra schema parentType inheritedBooleanCondition
          caseCondition cursor possibleTypes runtimeType variableValues
          fixedVariableValues)
        ((cursor.summarizeDecisionWithPruning algebra schema [] inheritedBooleanCondition
            caseCondition possibleTypes
            (CaseCursor.BooleanEnvironment.concrete variableValues)
            fixedVariableValues).collapse
          algebra) := by
  rw [summarizeFrom]
  split <;> rename_i hbranches
  · rw [CaseCursor.summarizeDecisionWithPruning_nil_values algebra schema []
      inheritedBooleanCondition caseCondition cursor possibleTypes
      (CaseCursor.BooleanEnvironment.concrete variableValues) fixedVariableValues hbranches]
    exact CaseCursor.summarizeFieldGroups_le_decision_complete algebra joinFactoringLaws schema _
      variableValues fixedVariableValues
  · rename_i branch rest
    rw [CaseCursor.summarizeDecisionWithPruning_cons_values algebra schema []
      inheritedBooleanCondition caseCondition cursor possibleTypes
      (CaseCursor.BooleanEnvironment.concrete variableValues) fixedVariableValues branch rest
      hbranches]
    cases hcondition : branch.condition with
    | typeCondition typeName =>
        simp only
        let regions :=
          possibleTypeRegions possibleTypes [branch.body.condition.possibleTypes]
        let region := chooseTypeRegion runtimeType possibleTypes regions
        have hregion : region ∈ regions ∧ runtimeType ∈ region := by
          exact chooseTypeRegion_mem possibleTypes
            [branch.body.condition.possibleTypes] runtimeType hruntime
        rw [BooleanDecision.collapse_joinMap]
        cases hselect
              : possibleTypesSubset region branch.body.condition.possibleTypes with
        | false =>
            apply lawful.le_trans _
              (((cursor.skipBranch rest).summarizeDecisionWithPruning algebra schema []
                inheritedBooleanCondition caseCondition region
                (CaseCursor.BooleanEnvironment.concrete variableValues)
                  fixedVariableValues).collapse algebra)
            · exact summarizeFrom_le algebra joinFactoringLaws schema parentType
                inheritedBooleanCondition caseCondition (cursor.skipBranch rest)
                region runtimeType variableValues fixedVariableValues hregion.2
            · simpa [regions, region, hselect] using lawful.le_joinMap_of_mem
                (fun candidate hcandidate =>
                  ((if possibleTypesSubset candidate
                        branch.body.condition.possibleTypes then
                      (cursor.selectBranch branch.body rest).summarizeDecisionWithPruning algebra schema
                        [] inheritedBooleanCondition caseCondition candidate
                        (CaseCursor.BooleanEnvironment.concrete variableValues) fixedVariableValues
                    else
                      (cursor.skipBranch rest).summarizeDecisionWithPruning algebra schema []
                        inheritedBooleanCondition caseCondition candidate
                        (CaseCursor.BooleanEnvironment.concrete variableValues) fixedVariableValues
                    ).collapse algebra))
                hregion.1
        | true =>
            apply lawful.le_trans _
              (((cursor.selectBranch branch.body rest).summarizeDecisionWithPruning algebra schema []
                inheritedBooleanCondition caseCondition region
                (CaseCursor.BooleanEnvironment.concrete variableValues)
                  fixedVariableValues).collapse algebra)
            · exact summarizeFrom_le algebra joinFactoringLaws schema parentType
                inheritedBooleanCondition caseCondition
                (cursor.selectBranch branch.body rest) region runtimeType variableValues
                fixedVariableValues hregion.2
            · simpa [regions, region, hselect] using lawful.le_joinMap_of_mem
                (fun candidate hcandidate =>
                  ((if possibleTypesSubset candidate
                        branch.body.condition.possibleTypes then
                      (cursor.selectBranch branch.body rest).summarizeDecisionWithPruning algebra schema
                        [] inheritedBooleanCondition caseCondition candidate
                        (CaseCursor.BooleanEnvironment.concrete variableValues) fixedVariableValues
                    else
                      (cursor.skipBranch rest).summarizeDecisionWithPruning algebra schema []
                        inheritedBooleanCondition caseCondition candidate
                        (CaseCursor.BooleanEnvironment.concrete variableValues) fixedVariableValues
                    ).collapse algebra))
                hregion.1
    | booleanLiteral literal =>
        simp only
        cases hvalue
              : inputValueBoolean? variableValues (.variable literal.variableName) with
        | none =>
            rw [CaseCursor.BooleanEnvironment.concrete_statusForVariable, hvalue]
            simp only [Option.getD_none]
            exact summarizeFrom_le algebra joinFactoringLaws schema parentType
              inheritedBooleanCondition
              (.negative literal.variableName :: caseCondition)
              (cursor.resolveBooleanBranch branch.body rest literal false) possibleTypes
              runtimeType variableValues fixedVariableValues hruntime
        | some value =>
            rw [CaseCursor.BooleanEnvironment.concrete_statusForVariable, hvalue]
            simp only [Option.getD_some]
            exact summarizeFrom_le algebra joinFactoringLaws schema parentType
              inheritedBooleanCondition
              ((if value then .positive literal.variableName else .negative literal.variableName)
                :: caseCondition)
              (cursor.resolveBooleanBranch branch.body rest literal value) possibleTypes
              runtimeType variableValues fixedVariableValues hruntime
termination_by caseCursorUnresolvedCount cursor
decreasing_by
  all_goals first
    | apply selectBranch_unresolved_lt <;> assumption
    | apply skipBranch_unresolved_lt <;> assumption
    | apply resolveBooleanBranch_unresolved_lt <;> assumption

theorem summarize_le
    (algebra : Algebra) {lawful : algebra.Lawful}
    (joinFactoringLaws : ExactCases.JoinFactoringLaws algebra lawful)
    (schema : Schema)
    (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
    (cursor : CaseCursor) (possibleTypes : PossibleTypeRegion)
    (runtimeType : Name) (variableValues fixedVariableValues : VariableValues)
    (hruntime : runtimeType ∈ possibleTypes)
    : lawful.le
        (summarize algebra schema parentType inheritedBooleanCondition cursor
          possibleTypes runtimeType variableValues fixedVariableValues)
        (CaseCursor.summarize algebra schema inheritedBooleanCondition cursor
          possibleTypes variableValues fixedVariableValues) := by
  unfold summarize CaseCursor.summarize
  exact summarizeFrom_le algebra joinFactoringLaws schema parentType
    inheritedBooleanCondition [] cursor possibleTypes runtimeType variableValues
    fixedVariableValues hruntime

private def namedFieldToExecutable (field : NamedField) : ExecutableField :=
  {
    fieldName := field.field.fieldName
    arguments := field.field.arguments
    selectionSet := field.field.selectionSet
  }

private def fieldGroupToExecutableGroup (group : FieldGroup)
    : Name × List ExecutableField :=
  (
    group.responseName,
    group.fields.map
      fun field =>
        {
          fieldName := field.fieldName
          arguments := field.arguments
          selectionSet := field.selectionSet
        }
  )

private theorem fieldGroupToExecutableGroup_addFieldWithResponseName
    (responseName : Name) (field : Field) (groups : List FieldGroup)
    : (ConditionTree.addFieldWithResponseName responseName field groups).map
        fieldGroupToExecutableGroup
      = addExecutableGroup
          (
            responseName,
            [{
              fieldName := field.fieldName
              arguments := field.arguments
              selectionSet := field.selectionSet
            }]
          )
          (groups.map fieldGroupToExecutableGroup) := by
  induction groups with
  | nil => simp [ConditionTree.addFieldWithResponseName,
      addExecutableGroup, fieldGroupToExecutableGroup, FieldGroup.fields]
  | cons group rest ih =>
      by_cases heq : responseName = group.responseName
      · subst responseName
        simp [ConditionTree.addFieldWithResponseName, addExecutableGroup,
          fieldGroupToExecutableGroup, FieldGroup.fields, List.map_append]
      · have hfalse : (responseName == group.responseName) = false := by
          exact Bool.eq_false_iff.mpr fun htrue => heq (beq_iff_eq.mp htrue)
        have hfalse' : (group.responseName == responseName) = false := by
          exact Bool.eq_false_iff.mpr fun htrue => heq (beq_iff_eq.mp htrue).symm
        simp [ConditionTree.addFieldWithResponseName, addExecutableGroup,
          fieldGroupToExecutableGroup, hfalse, hfalse', ih]

private theorem fieldGroupToExecutableGroup_collectFieldGroups (fields : List NamedField)
    : (ConditionTree.collectFieldGroups fields).map fieldGroupToExecutableGroup
      = groupExecutableFields
          (fields.map
            fun field =>
              (field.responseName, namedFieldToExecutable field)) := by
  unfold ConditionTree.collectFieldGroups groupExecutableFields
  have hfold : ∀ (rest : List NamedField) (groups : List FieldGroup),
      (rest.foldl
          (fun current field => ConditionTree.addFieldToGroups field current)
          groups).map fieldGroupToExecutableGroup
        = rest.foldl
            (fun current field =>
              addExecutableGroup
                (field.responseName, [namedFieldToExecutable field]) current)
            (groups.map fieldGroupToExecutableGroup) := by
    intro rest groups
    induction rest generalizing groups with
    | nil => rfl
    | cons field tail ih =>
        rw [List.foldl_cons, List.foldl_cons, ih]
        unfold ConditionTree.addFieldToGroups
        rw [fieldGroupToExecutableGroup_addFieldWithResponseName]
        rfl
  rw [List.foldl_map]
  simpa [namedFieldToExecutable] using hfold fields []

theorem toExecutableGroup_keys (groups : List CollectedFieldGroup)
    : (groups.map CollectedFieldGroup.toExecutableGroup).map Prod.fst
      = groups.map CollectedFieldGroup.responseName := by
  induction groups with
  | nil => rfl
  | cons group rest ih =>
      simp [CollectedFieldGroup.toExecutableGroup, CollectedFieldGroup.responseName, ih]

private theorem toExecutableGroup_collectFieldGroups
    (inheritedBooleanCondition : List BooleanLiteral) (condition : Condition)
    (groups : List FieldGroup)
    : (TreeSummary.fieldGroupsWithContext inheritedBooleanCondition condition groups).map
        CollectedFieldGroup.toExecutableGroup
      = groups.map fieldGroupToExecutableGroup := by
  simp [TreeSummary.fieldGroupsWithContext,
    CollectedFieldGroup.toExecutableGroup, CollectedFieldGroup.responseName,
    CollectedFieldGroup.fields, fieldGroupToExecutableGroup, List.map_map]

private def runtimeNamedFields (variableValues : VariableValues)
    (runtimeType : Name) (tree : Tree)
    : List NamedField :=
  tree.storedFieldEntries.filterMap
    fun entry =>
      if entry.1.allows variableValues runtimeType then some entry.2 else none

private def pendingRuntimeNamedFields (variableValues : VariableValues)
    (runtimeType : Name) (branches : List (Branch Tree))
    : List NamedField :=
  branches.flatMap fun branch => runtimeNamedFields variableValues runtimeType branch.body

private theorem runtimeNamedFields_map
    (runtimeType : Name) (variableValues : VariableValues) (tree : Tree)
    : (runtimeNamedFields variableValues runtimeType tree).map
        (fun field => (field.responseName, namedFieldToExecutable field))
      = tree.collectRuntimeFields variableValues runtimeType := by
  unfold runtimeNamedFields Tree.collectRuntimeFields
  induction tree.storedFieldEntries with
  | nil => simp [runtimeFieldsForEntries]
  | cons entry rest ih =>
      cases hallows : entry.1.allows variableValues runtimeType with
      | false =>
          simp only [List.filterMap_cons, hallows, Bool.false_eq_true, ite_false,
            runtimeFieldsForEntries, List.flatMap_cons, List.nil_append]
          change (rest.filterMap fun entry =>
              if entry.1.allows variableValues runtimeType = true then
                some entry.2 else none).map
                (fun field => (field.responseName,
                  namedFieldToExecutable field))
            = runtimeFieldsForEntries variableValues runtimeType rest
          exact ih
      | true =>
          simp only [List.filterMap_cons, hallows, ite_true, List.map_cons,
            runtimeFieldsForEntries, List.flatMap_cons, List.singleton_append]
          congr 1

private theorem possibleTypesSubset_eq_contains_of_constant
    (region allowed : PossibleTypes) (runtimeType : Name)
    (hruntime : runtimeType ∈ region)
    (hconstant
      : ∀ typeName,
          typeName ∈ region -> allowed.contains typeName = allowed.contains runtimeType)
    : possibleTypesSubset region allowed = allowed.contains runtimeType := by
  unfold possibleTypesSubset
  cases hallowed : allowed.contains runtimeType with
  | true =>
      apply List.all_eq_true.mpr
      intro typeName hmem
      rw [hconstant typeName hmem, hallowed]
  | false =>
      exact List.all_eq_false.mpr ⟨runtimeType, hruntime, by rw [hallowed]; simp⟩

private theorem branchSelected_eq_bodyAllows
    (schema : Schema) (variableValues : VariableValues) (runtimeType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (parentCondition : Condition) (branch : Branch Tree)
    (region : PossibleTypeRegion)
    (hinherited : booleanConditionAllows variableValues inheritedBooleanCondition = true)
    (hparent : parentCondition.allows variableValues runtimeType = true)
    (hcoherent
      : conditionForBranch? schema inheritedBooleanCondition parentCondition
          branch.condition
        = some branch.body.condition)
    (hruntime : runtimeType ∈ region)
    (huniform
      : match branch.condition with
        | .typeCondition _typeName =>
            ∀ candidate,
              candidate ∈ region
              -> branch.body.condition.possibleTypes.contains candidate
                  = branch.body.condition.possibleTypes.contains runtimeType
        | .booleanLiteral _literal => True)
    : (match branch.condition with
        | .typeCondition _typeName =>
            possibleTypesSubset region branch.body.condition.possibleTypes
        | .booleanLiteral literal => booleanConditionAllows variableValues [literal])
      = branch.body.condition.allows variableValues runtimeType := by
  rcases branch with ⟨condition, body⟩
  cases condition with
  | typeCondition typeName =>
      simp only [conditionForBranch?] at hcoherent
      split at hcoherent
      · contradiction
      · rename_i hnonempty
        simp only [Option.some.injEq] at hcoherent
        rw [← hcoherent] at huniform
        rw [← hcoherent]
        rw [possibleTypesSubset_eq_contains_of_constant region
          (intersectPossibleTypes parentCondition.possibleTypes
            (schema.getPossibleTypes typeName)) runtimeType hruntime huniform]
        rcases Bool.and_eq_true_iff.mp hparent with ⟨hpossible, hboolean⟩
        simp [Condition.allows, hboolean]
  | booleanLiteral literal =>
      have hnext := conditionForBranch?_runtime schema variableValues runtimeType
        inheritedBooleanCondition parentCondition (.booleanLiteral literal) hinherited
      rw [hcoherent] at hnext
      simp only [conditionOptionAllows, hparent, Bool.true_and,
        BranchCondition.allows] at hnext
      simpa [booleanConditionAllows] using hnext.symm

private theorem runtimeNamedFields_eq_nil_of_condition_false
    (schema : Schema) (variableValues : VariableValues)
    (parentType runtimeType : Name)
    (inheritedBooleanCondition : List BooleanLiteral) (tree : Tree)
    (hinherited : booleanConditionAllows variableValues inheritedBooleanCondition = true)
    (hcondition : tree.condition.allows variableValues runtimeType = false)
    (hcoherent : tree.BranchesCoherent schema inheritedBooleanCondition)
    : runtimeNamedFields variableValues runtimeType tree = [] := by
  have hsource := tree.runtimeReductionBundles_sourceFields schema variableValues
    parentType runtimeType inheritedBooleanCondition hinherited hcoherent
  rw [Tree.runtimeReductionBundles, ite_eq_right (by simpa using hcondition),
    RuntimeFieldBundle.allSourceEntries] at hsource
  have hexecutable : tree.collectRuntimeFields variableValues runtimeType = [] := by
    simpa [RuntimeFieldBundle.allSourceEntries] using hsource.symm
  have hmapped := runtimeNamedFields_map runtimeType variableValues tree
  rw [hexecutable] at hmapped
  cases hfields : runtimeNamedFields variableValues runtimeType tree with
  | nil => rfl
  | cons field rest => simp [hfields] at hmapped

private theorem runtimeNamedFields_eq_local_append_pending
    (variableValues : VariableValues) (runtimeType : Name) (tree : Tree)
    (hallows : tree.condition.allows variableValues runtimeType = true)
    : runtimeNamedFields variableValues runtimeType tree
      = CaseCursor.localNamedFields tree
        ++ pendingRuntimeNamedFields variableValues runtimeType tree.branches := by
  unfold runtimeNamedFields pendingRuntimeNamedFields CaseCursor.localNamedFields
  rw [Tree.storedFieldEntries, List.filterMap_append]
  have hbranches
      : (branchStoredFieldEntries tree.branches).filterMap
          (fun entry =>
            if entry.1.allows variableValues runtimeType then some entry.2 else none)
        = tree.branches.flatMap
            fun branch =>
              (branch.body.storedFieldEntries).filterMap
                fun entry =>
                  if entry.1.allows variableValues runtimeType then
                    some entry.2
                  else
                    none := by
    induction tree.branches with
    | nil => simp [branchStoredFieldEntries]
    | cons branch rest ih =>
        simp [branchStoredFieldEntries, List.filterMap_append, ih]
  rw [hbranches]
  congr 1
  induction tree.fields with
  | nil => rfl
  | cons group rest ih =>
      rw [List.flatMap_cons, List.filterMap_append, List.flatMap_cons, ih]
      congr 1
      induction group.fields with
      | nil => rfl
      | cons field fields tail_ih => simp [hallows, tail_ih]

private def BranchValid (schema : Schema)
    (inheritedBooleanCondition : List BooleanLiteral)
    (variableValues : VariableValues) (runtimeType : Name)
    (branch : Branch Tree)
    : Prop :=
  ∃ parentCondition,
    parentCondition.allows variableValues runtimeType = true
    ∧ conditionForBranch? schema inheritedBooleanCondition parentCondition
        branch.condition
      = some branch.body.condition
    ∧ branch.body.BranchesCoherent schema inheritedBooleanCondition

private def PendingValid (schema : Schema)
    (inheritedBooleanCondition : List BooleanLiteral)
    (variableValues : VariableValues) (runtimeType : Name)
    (branches : List (Branch Tree))
    : Prop :=
  ∀ branch,
    branch ∈ branches
    -> BranchValid schema inheritedBooleanCondition variableValues runtimeType branch

private theorem pendingValid_of_coherent
    (schema : Schema) (inheritedBooleanCondition : List BooleanLiteral)
    (variableValues : VariableValues) (runtimeType : Name)
    (parentCondition : Condition) (branches : List (Branch Tree))
    (hparent : parentCondition.allows variableValues runtimeType = true)
    (hcoherent
      : branchesCoherent schema inheritedBooleanCondition parentCondition branches)
    : PendingValid schema inheritedBooleanCondition variableValues runtimeType
        branches := by
  intro branch hbranch
  induction branches with
  | nil => simp at hbranch
  | cons head rest ih =>
      rw [branchesCoherent] at hcoherent
      rcases List.mem_cons.mp hbranch with rfl | hbranch
      · exact ⟨parentCondition, hparent, hcoherent.1, hcoherent.2.1⟩
      · exact ih hcoherent.2.2 hbranch

private theorem pendingValid_append
    {schema : Schema} {inheritedBooleanCondition : List BooleanLiteral}
    {variableValues : VariableValues} {runtimeType : Name}
    {left right : List (Branch Tree)}
    (hleft
      : PendingValid schema inheritedBooleanCondition variableValues runtimeType left)
    (hright
      : PendingValid schema inheritedBooleanCondition variableValues runtimeType right)
    : PendingValid schema inheritedBooleanCondition variableValues runtimeType
        (left ++ right) := by
  intro branch hbranch
  exact (List.mem_append.mp hbranch).elim (hleft branch) (hright branch)

private theorem pendingRuntimeNamedFields_append
    (variableValues : VariableValues) (runtimeType : Name)
    (left right : List (Branch Tree))
    : pendingRuntimeNamedFields variableValues runtimeType (left ++ right)
      = pendingRuntimeNamedFields variableValues runtimeType left
        ++ pendingRuntimeNamedFields variableValues runtimeType right := by
  simp [pendingRuntimeNamedFields]

private theorem selectedValue_eq_bodyAllows
    (schema : Schema) (inheritedBooleanCondition : List BooleanLiteral)
    (variableValues : VariableValues) (runtimeType : Name)
    (possibleTypes : PossibleTypeRegion) (branch : Branch Tree)
    (hbranch
      : BranchValid schema inheritedBooleanCondition variableValues runtimeType branch)
    (hinherited : booleanConditionAllows variableValues inheritedBooleanCondition = true)
    (hruntime : runtimeType ∈ possibleTypes)
    : let regions :=
        possibleTypeRegions possibleTypes [branch.body.condition.possibleTypes]
      let region := chooseTypeRegion runtimeType possibleTypes regions
      (match branch.condition with
        | .typeCondition _typeName =>
            possibleTypesSubset region branch.body.condition.possibleTypes
        | .booleanLiteral literal => booleanConditionAllows variableValues [literal])
      = branch.body.condition.allows variableValues runtimeType := by
  rcases hbranch with ⟨parentCondition, hparent, hcoherent, _hbody⟩
  let regions := possibleTypeRegions possibleTypes [branch.body.condition.possibleTypes]
  let region := chooseTypeRegion runtimeType possibleTypes regions
  have hregion := chooseTypeRegion_mem possibleTypes
    [branch.body.condition.possibleTypes] runtimeType hruntime
  apply branchSelected_eq_bodyAllows schema variableValues runtimeType
    inheritedBooleanCondition parentCondition branch region hinherited hparent hcoherent
    hregion.2
  cases hcondition : branch.condition with
  | typeCondition typeName =>
      intro candidate hcandidate
      have huniform := (possibleTypeRegions_exact possibleTypes
        [branch.body.condition.possibleTypes]).2.2 region hregion.1
      exact huniform candidate hcandidate runtimeType hregion.2
        branch.body.condition.possibleTypes (by simp)
  | booleanLiteral literal => trivial

private theorem resolve_trace
    (inheritedBooleanCondition caseCondition : List BooleanLiteral)
    (cursor : CaseCursor) (possibleTypes : PossibleTypeRegion)
    (runtimeType : Name) (variableValues : VariableValues)
    (hruntime : runtimeType ∈ possibleTypes)
    : let trace := CaseTrace.ofCursor variableValues runtimeType cursor
      let resolved :=
        resolve inheritedBooleanCondition caseCondition cursor possibleTypes
          runtimeType variableValues
      resolved.cursor.namedFields = trace.namedFields
      ∧ resolved.possibleTypes
        = possibleTypeMembershipClass possibleTypes trace.typeConditions runtimeType
      ∧ resolved.inheritedBooleanCondition
        = Internal.extendBooleanCondition inheritedBooleanCondition
            (trace.booleanLiterals.reverse ++ caseCondition) := by
  rw [resolve.eq_1]
  split <;> rename_i hbranches
  · simp only [CaseTrace.ofCursor, hbranches, CaseTrace.ofBranches,
      CaseTrace.Trace.append, CaseTrace.Trace.empty, List.append_nil,
      List.reverse_nil, List.nil_append]
    constructor
    · trivial
    · constructor
      · unfold possibleTypeMembershipClass
        symm
        exact List.filter_eq_self.mpr fun _ _ => by simp
      · trivial
  · rename_i branch rest
    cases hcondition : branch.condition with
    | typeCondition typeName =>
        dsimp only
        let regions :=
          possibleTypeRegions possibleTypes [branch.body.condition.possibleTypes]
        let region := chooseTypeRegion runtimeType possibleTypes regions
        have hregion := chooseTypeRegion_mem possibleTypes
          [branch.body.condition.possibleTypes] runtimeType hruntime
        have hregionEq : region = possibleTypeMembershipClass possibleTypes
            [branch.body.condition.possibleTypes] runtimeType :=
          possibleTypeRegions_membershipClass possibleTypes
            [branch.body.condition.possibleTypes] region hregion.1 runtimeType hregion.2
        have huniform := (possibleTypeRegions_exact possibleTypes
          [branch.body.condition.possibleTypes]).2.2 region hregion.1
        have hselected : possibleTypesSubset region branch.body.condition.possibleTypes
            = branch.body.condition.possibleTypes.contains runtimeType :=
          possibleTypesSubset_eq_contains_of_constant region
            branch.body.condition.possibleTypes runtimeType hregion.2
            (fun candidate hcandidate =>
              huniform candidate hcandidate runtimeType hregion.2
                branch.body.condition.possibleTypes (by simp))
        dsimp only [region] at hregionEq hselected hregion
        cases hcontains : branch.body.condition.possibleTypes.contains runtimeType
        · have hnotmem : runtimeType ∉ branch.body.condition.possibleTypes := by
            intro hmem
            exact Bool.noConfusion
              (hcontains.symm.trans (List.contains_iff_mem.mpr hmem))
          rw [hselected, hcontains, hregionEq]
          simp only [Bool.false_eq_true, ite_false]
          have ih := resolve_trace inheritedBooleanCondition caseCondition
            (cursor.skipBranch rest) region runtimeType variableValues hregion.2
          simpa [CaseTrace.ofCursor, CaseTrace.ofBranches, CaseTrace.Trace.append,
            CaseTrace.Trace.empty, CaseTrace.branchObservation,
            CaseTrace.branchSelected, CaseCursor.skipBranch, CaseCursor.namedFields,
            hbranches, hcondition,
            hcontains, hnotmem, region, hregionEq, possibleTypeMembershipClass_append,
            List.append_assoc] using ih
        · have hmem : runtimeType ∈ branch.body.condition.possibleTypes :=
            List.contains_iff_mem.mp hcontains
          rw [hselected, hcontains, hregionEq]
          simp only [ite_true]
          have ih := resolve_trace inheritedBooleanCondition caseCondition
            (cursor.selectBranch branch.body rest) region runtimeType variableValues
            hregion.2
          simpa [CaseTrace.ofCursor, CaseTrace.ofTree, CaseTrace.ofBranches,
            CaseTrace.ofBranches_append,
            CaseTrace.Trace.append, CaseTrace.Trace.empty,
            CaseTrace.branchObservation, CaseTrace.branchSelected,
            CaseCursor.selectBranch, CaseCursor.namedFields, hbranches, hcondition,
            hcontains, hmem, region, hregionEq, possibleTypeMembershipClass_append,
            List.append_assoc] using ih
    | booleanLiteral literal =>
        dsimp only
        cases hvalue
              : inputValueBoolean? variableValues (.variable literal.variableName) with
        | none =>
            cases literal with
            | positive variableName =>
                simp only [BooleanLiteral.variableName] at hvalue
                have hlookup :
                    (inputValueBoolean? variableValues (.variable variableName)).getD
                      false = false := by simp [hvalue]
                have ih := resolve_trace inheritedBooleanCondition
                  (.negative variableName :: caseCondition)
                  (cursor.resolveBooleanBranch branch.body rest (.positive variableName)
                    false) possibleTypes runtimeType variableValues hruntime
                simpa [CaseTrace.ofCursor, CaseTrace.ofTree, CaseTrace.ofBranches,
                  CaseTrace.ofBranches_append, CaseTrace.Trace.append,
                  CaseTrace.Trace.empty, CaseTrace.branchObservation,
                  CaseTrace.branchSelected, CaseTrace.selectedLiteral,
                  CaseForest.booleanValue, hlookup, CaseCursor.resolveBooleanBranch,
                  CaseCursor.selectBranch, CaseCursor.skipBranch, CaseCursor.namedFields,
                  hbranches, hcondition, BooleanLiteral.requiredValue,
                  BooleanLiteral.variableName, possibleTypeMembershipClass_append,
                  List.append_assoc]
                  using ih
            | negative variableName =>
                simp only [BooleanLiteral.variableName] at hvalue
                have hlookup :
                    (inputValueBoolean? variableValues (.variable variableName)).getD
                      false = false := by simp [hvalue]
                have ih := resolve_trace inheritedBooleanCondition
                  (.negative variableName :: caseCondition)
                  (cursor.resolveBooleanBranch branch.body rest (.negative variableName)
                    false) possibleTypes runtimeType variableValues hruntime
                simpa [CaseTrace.ofCursor, CaseTrace.ofTree, CaseTrace.ofBranches,
                  CaseTrace.ofBranches_append, CaseTrace.Trace.append,
                  CaseTrace.Trace.empty, CaseTrace.branchObservation,
                  CaseTrace.branchSelected, CaseTrace.selectedLiteral,
                  CaseForest.booleanValue, hlookup, CaseCursor.resolveBooleanBranch,
                  CaseCursor.selectBranch, CaseCursor.skipBranch, CaseCursor.namedFields,
                  hbranches, hcondition, BooleanLiteral.requiredValue,
                  BooleanLiteral.variableName, possibleTypeMembershipClass_append,
                  List.append_assoc]
                  using ih
        | some value =>
            cases value with
            | false =>
                cases literal with
                | positive variableName =>
                    simp only [BooleanLiteral.variableName] at hvalue
                    have hlookup :
                        (inputValueBoolean? variableValues (.variable variableName)).getD
                          false = false := by simp [hvalue]
                    have ih := resolve_trace inheritedBooleanCondition
                      (.negative variableName :: caseCondition)
                      (cursor.resolveBooleanBranch branch.body rest
                        (.positive variableName) false) possibleTypes runtimeType
                        variableValues hruntime
                    simpa [CaseTrace.ofCursor, CaseTrace.ofTree, CaseTrace.ofBranches,
                      CaseTrace.ofBranches_append, CaseTrace.Trace.append,
                      CaseTrace.Trace.empty, CaseTrace.branchObservation,
                      CaseTrace.branchSelected, CaseTrace.selectedLiteral,
                      CaseForest.booleanValue, hlookup, CaseCursor.resolveBooleanBranch,
                      CaseCursor.selectBranch, CaseCursor.skipBranch,
                      CaseCursor.namedFields, hbranches, hcondition,
                      BooleanLiteral.requiredValue, BooleanLiteral.variableName,
                      possibleTypeMembershipClass_append, List.append_assoc]
                      using ih
                | negative variableName =>
                    simp only [BooleanLiteral.variableName] at hvalue
                    have hlookup :
                        (inputValueBoolean? variableValues (.variable variableName)).getD
                          false = false := by simp [hvalue]
                    have ih := resolve_trace inheritedBooleanCondition
                      (.negative variableName :: caseCondition)
                      (cursor.resolveBooleanBranch branch.body rest
                        (.negative variableName) false) possibleTypes runtimeType
                        variableValues hruntime
                    simpa [CaseTrace.ofCursor, CaseTrace.ofTree, CaseTrace.ofBranches,
                      CaseTrace.ofBranches_append, CaseTrace.Trace.append,
                      CaseTrace.Trace.empty, CaseTrace.branchObservation,
                      CaseTrace.branchSelected, CaseTrace.selectedLiteral,
                      CaseForest.booleanValue, hlookup, CaseCursor.resolveBooleanBranch,
                      CaseCursor.selectBranch, CaseCursor.skipBranch,
                      CaseCursor.namedFields, hbranches, hcondition,
                      BooleanLiteral.requiredValue, BooleanLiteral.variableName,
                      possibleTypeMembershipClass_append, List.append_assoc]
                      using ih
            | true =>
                cases literal with
                | positive variableName =>
                    simp only [BooleanLiteral.variableName] at hvalue
                    have hlookup :
                        (inputValueBoolean? variableValues (.variable variableName)).getD
                          false = true := by simp [hvalue]
                    have ih := resolve_trace inheritedBooleanCondition
                      (.positive variableName :: caseCondition)
                      (cursor.resolveBooleanBranch branch.body rest
                        (.positive variableName) true) possibleTypes runtimeType
                        variableValues hruntime
                    simpa [CaseTrace.ofCursor, CaseTrace.ofTree, CaseTrace.ofBranches,
                      CaseTrace.ofBranches_append, CaseTrace.Trace.append,
                      CaseTrace.Trace.empty, CaseTrace.branchObservation,
                      CaseTrace.branchSelected, CaseTrace.selectedLiteral,
                      CaseForest.booleanValue, hlookup, CaseCursor.resolveBooleanBranch,
                      CaseCursor.selectBranch, CaseCursor.skipBranch,
                      CaseCursor.namedFields, hbranches, hcondition,
                      BooleanLiteral.requiredValue, BooleanLiteral.variableName,
                      possibleTypeMembershipClass_append, List.append_assoc]
                      using ih
                | negative variableName =>
                    simp only [BooleanLiteral.variableName] at hvalue
                    have hlookup :
                        (inputValueBoolean? variableValues (.variable variableName)).getD
                          false = true := by simp [hvalue]
                    have ih := resolve_trace inheritedBooleanCondition
                      (.positive variableName :: caseCondition)
                      (cursor.resolveBooleanBranch branch.body rest
                        (.negative variableName) true) possibleTypes runtimeType
                        variableValues hruntime
                    simpa [CaseTrace.ofCursor, CaseTrace.ofTree, CaseTrace.ofBranches,
                      CaseTrace.ofBranches_append, CaseTrace.Trace.append,
                      CaseTrace.Trace.empty, CaseTrace.branchObservation,
                      CaseTrace.branchSelected, CaseTrace.selectedLiteral,
                      CaseForest.booleanValue, hlookup, CaseCursor.resolveBooleanBranch,
                      CaseCursor.selectBranch, CaseCursor.skipBranch,
                      CaseCursor.namedFields, hbranches, hcondition,
                      BooleanLiteral.requiredValue, BooleanLiteral.variableName,
                      possibleTypeMembershipClass_append, List.append_assoc]
                      using ih
termination_by caseCursorUnresolvedCount cursor
decreasing_by
  all_goals first
    | apply nextTypeBranch_unresolved_lt <;> assumption
    | apply resolveBooleanBranch_unresolved_lt <;> assumption
    | apply selectBranch_unresolved_lt <;> assumption
    | apply skipBranch_unresolved_lt <;> assumption

theorem fieldGroups_eq_trace
    (inheritedBooleanCondition : List BooleanLiteral)
    (cursor : CaseCursor) (possibleTypes : PossibleTypeRegion)
    (runtimeType : Name) (variableValues : VariableValues)
    (hruntime : runtimeType ∈ possibleTypes)
    : fieldGroups inheritedBooleanCondition cursor possibleTypes
        runtimeType variableValues
      = CaseTrace.fieldGroups inheritedBooleanCondition possibleTypes runtimeType
          (CaseTrace.ofCursor variableValues runtimeType cursor) := by
  have htrace := resolve_trace inheritedBooleanCondition [] cursor possibleTypes
    runtimeType variableValues hruntime
  unfold fieldGroups CaseTrace.fieldGroups CaseTrace.inheritedBooleanCondition
    CaseTrace.possibleTypes CaseCursor.fieldGroups
  dsimp only
  rw [htrace.1, htrace.2.1, htrace.2.2]
  simp

theorem fieldGroupsFrom_eq_trace
    (inheritedBooleanCondition caseCondition : List BooleanLiteral)
    (cursor : CaseCursor) (possibleTypes : PossibleTypeRegion)
    (runtimeType : Name) (variableValues : VariableValues)
    (hruntime : runtimeType ∈ possibleTypes)
    : fieldGroupsFrom inheritedBooleanCondition caseCondition cursor possibleTypes
        runtimeType variableValues
      = CaseTrace.fieldGroups inheritedBooleanCondition possibleTypes runtimeType
          (CaseTrace.withCaseCondition caseCondition
            (CaseTrace.ofCursor variableValues runtimeType cursor)) := by
  have htrace := resolve_trace inheritedBooleanCondition caseCondition cursor
    possibleTypes runtimeType variableValues hruntime
  unfold fieldGroupsFrom CaseTrace.fieldGroups CaseTrace.inheritedBooleanCondition
    CaseTrace.possibleTypes CaseTrace.withCaseCondition CaseCursor.fieldGroups
  dsimp only
  rw [htrace.1, htrace.2.1, htrace.2.2]
  simp [List.reverse_append]

private theorem booleanConditionAllows_singleton
    (variableValues : VariableValues) (literal : BooleanLiteral)
    : booleanConditionAllows variableValues [literal]
      = (literal.requiredValue
          == (inputValueBoolean? variableValues (.variable literal.variableName)).getD
              false) := by
  cases literal with
  | positive variableName =>
      simp only [booleanConditionAllows, BooleanLiteral.allows,
        BooleanLiteral.toDirective, directiveAllowsSelectionBool,
        BooleanLiteral.requiredValue, BooleanLiteral.variableName, Bool.and_true]
      cases hvalue : inputValueBoolean? variableValues (.variable variableName) with
      | none => simp
      | some value => cases value <;> simp
  | negative variableName =>
      simp only [booleanConditionAllows, BooleanLiteral.allows,
        BooleanLiteral.toDirective, directiveAllowsSelectionBool,
        BooleanLiteral.requiredValue, BooleanLiteral.variableName, Bool.and_true]
      cases hvalue : inputValueBoolean? variableValues (.variable variableName) with
      | none => simp
      | some value => cases value <;> simp

private theorem resolve_namedFields
    (schema : Schema) (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (caseCondition : List BooleanLiteral) (cursor : CaseCursor)
    (possibleTypes : PossibleTypeRegion) (runtimeType : Name)
    (variableValues : VariableValues)
    (hinherited : booleanConditionAllows variableValues inheritedBooleanCondition = true)
    (hruntime : runtimeType ∈ possibleTypes)
    (hvalid
      : PendingValid schema inheritedBooleanCondition variableValues runtimeType
          cursor.pendingBranches)
    : let resolved :=
        resolve inheritedBooleanCondition caseCondition cursor possibleTypes
          runtimeType variableValues
      resolved.cursor.namedFields
        ++ pendingRuntimeNamedFields variableValues runtimeType
            resolved.cursor.pendingBranches
      = cursor.namedFields
        ++ pendingRuntimeNamedFields variableValues runtimeType
            cursor.pendingBranches := by
  rw [resolve.eq_1]
  split <;> rename_i hbranches
  · rfl
  · rename_i branch rest
    have hhead := hvalid branch (by simp [hbranches])
    have hrest : PendingValid schema inheritedBooleanCondition variableValues runtimeType
        rest := by
      intro candidate hcandidate
      exact hvalid candidate (by simp [hbranches, hcandidate])
    cases hcondition : branch.condition with
    | typeCondition typeName =>
        let regions :=
          possibleTypeRegions possibleTypes [branch.body.condition.possibleTypes]
        let region := chooseTypeRegion runtimeType possibleTypes regions
        have hregion := chooseTypeRegion_mem possibleTypes
          [branch.body.condition.possibleTypes] runtimeType hruntime
        have hselected := selectedValue_eq_bodyAllows schema inheritedBooleanCondition
          variableValues runtimeType possibleTypes branch hhead hinherited hruntime
        simp only [hcondition] at hselected
        cases hselect
              : possibleTypesSubset region branch.body.condition.possibleTypes with
        | true =>
            have hbodyAllows : branch.body.condition.allows variableValues runtimeType = true :=
              hselected ▸ hselect
            have hbodyValid :=
              pendingValid_of_coherent schema inheritedBooleanCondition
                variableValues runtimeType branch.body.condition branch.body.branches
                hbodyAllows (by simpa [Tree.BranchesCoherent] using hhead.choose_spec.2.2)
            have hnextValid := pendingValid_append hbodyValid hrest
            have ih := resolve_namedFields schema parentType inheritedBooleanCondition
              caseCondition (cursor.selectBranch branch.body rest) region runtimeType
              variableValues hinherited hregion.2 hnextValid
            change possibleTypesSubset
                (chooseTypeRegion runtimeType possibleTypes
                  (possibleTypeRegions possibleTypes
                    [branch.body.condition.possibleTypes]))
                branch.body.condition.possibleTypes = true at hselect
            simp only [hselect, ite_true]
            apply ih.trans
            rw [CaseCursor.selectBranch, pendingRuntimeNamedFields_append]
            have hbody := runtimeNamedFields_eq_local_append_pending variableValues
              runtimeType branch.body hbodyAllows
            simp only [hbranches, pendingRuntimeNamedFields, List.flatMap_cons]
            rw [hbody]
            simp [CaseCursor.namedFields, pendingRuntimeNamedFields, List.append_assoc]
        | false =>
            have hbodyAllows : branch.body.condition.allows variableValues runtimeType = false :=
              hselected ▸ hselect
            have hbodyNil := runtimeNamedFields_eq_nil_of_condition_false schema
              variableValues parentType runtimeType inheritedBooleanCondition branch.body
              hinherited hbodyAllows hhead.choose_spec.2.2
            have ih := resolve_namedFields schema parentType inheritedBooleanCondition
              caseCondition (cursor.skipBranch rest) region runtimeType variableValues
              hinherited hregion.2 hrest
            change possibleTypesSubset
                (chooseTypeRegion runtimeType possibleTypes
                  (possibleTypeRegions possibleTypes
                    [branch.body.condition.possibleTypes]))
                branch.body.condition.possibleTypes = false at hselect
            simp only [hselect]
            apply ih.trans
            simp [CaseCursor.skipBranch, CaseCursor.namedFields, hbranches,
              pendingRuntimeNamedFields, hbodyNil]
    | booleanLiteral literal =>
        let value :=
          (inputValueBoolean? variableValues (.variable literal.variableName)).getD false
        have hselected := selectedValue_eq_bodyAllows schema inheritedBooleanCondition
          variableValues runtimeType possibleTypes branch hhead hinherited hruntime
        simp only [hcondition] at hselected
        by_cases hselect : literal.requiredValue = value
        · have hliteral : booleanConditionAllows variableValues [literal] = true := by
            rw [booleanConditionAllows_singleton]
            simp [value, hselect]
          have hbodyAllows : branch.body.condition.allows variableValues runtimeType = true :=
            hselected ▸ hliteral
          have hbodyValid :=
            pendingValid_of_coherent schema inheritedBooleanCondition
              variableValues runtimeType branch.body.condition branch.body.branches
              hbodyAllows (by simpa [Tree.BranchesCoherent] using hhead.choose_spec.2.2)
          have hnextValid := pendingValid_append hbodyValid hrest
          have ih :=
            resolve_namedFields schema parentType inheritedBooleanCondition
              ((if value then
                  .positive literal.variableName
                else
                  .negative literal.variableName)
                :: caseCondition)
              (cursor.resolveBooleanBranch branch.body rest literal value) possibleTypes
              runtimeType variableValues hinherited hruntime
              (by
                simpa [CaseCursor.resolveBooleanBranch, hselect, CaseCursor.selectBranch]
                  using hnextValid)
          simp only
          apply ih.trans
          simp only [CaseCursor.resolveBooleanBranch, hselect, ite_true,
            CaseCursor.selectBranch, pendingRuntimeNamedFields_append]
          have hbody := runtimeNamedFields_eq_local_append_pending variableValues
            runtimeType branch.body hbodyAllows
          simp only [hbranches, pendingRuntimeNamedFields, List.flatMap_cons]
          rw [hbody]
          simp [CaseCursor.namedFields, pendingRuntimeNamedFields, List.append_assoc]
        · have hliteral : booleanConditionAllows variableValues [literal] = false := by
            rw [booleanConditionAllows_singleton]
            simp [value, hselect]
          have hbodyAllows : branch.body.condition.allows variableValues runtimeType = false :=
            hselected ▸ hliteral
          have hbodyNil := runtimeNamedFields_eq_nil_of_condition_false schema
            variableValues parentType runtimeType inheritedBooleanCondition branch.body
            hinherited hbodyAllows hhead.choose_spec.2.2
          have ih :=
            resolve_namedFields schema parentType inheritedBooleanCondition
              ((if value then
                  .positive literal.variableName
                else
                  .negative literal.variableName)
                :: caseCondition)
              (cursor.resolveBooleanBranch branch.body rest literal value) possibleTypes
              runtimeType variableValues hinherited hruntime
              (by
                simpa [CaseCursor.resolveBooleanBranch, hselect, CaseCursor.skipBranch]
                  using hrest)
          simp only
          apply ih.trans
          simp [CaseCursor.resolveBooleanBranch, hselect, CaseCursor.skipBranch,
            CaseCursor.namedFields, hbranches, pendingRuntimeNamedFields, hbodyNil]
termination_by caseCursorUnresolvedCount cursor
decreasing_by
  all_goals first
    | apply nextTypeBranch_unresolved_lt <;> assumption
    | apply resolveBooleanBranch_unresolved_lt <;> assumption
    | apply selectBranch_unresolved_lt <;> assumption
    | apply skipBranch_unresolved_lt <;> assumption

private theorem selectedBooleanLiteral_allows
    (variableValues : VariableValues) (variableName : Name)
    : let value := (inputValueBoolean? variableValues (.variable variableName)).getD false
      let literal :=
        if value then
          BooleanLiteral.positive variableName
        else
          BooleanLiteral.negative variableName
      booleanConditionAllows variableValues [literal] = true := by
  cases hvalue : inputValueBoolean? variableValues (.variable variableName) with
  | none =>
      simp [hvalue, booleanConditionAllows, BooleanLiteral.allows,
        BooleanLiteral.toDirective, directiveAllowsSelectionBool]
  | some value =>
      cases value <;> simp [hvalue, booleanConditionAllows, BooleanLiteral.allows,
        BooleanLiteral.toDirective, directiveAllowsSelectionBool]

private theorem extendBooleanCondition_allows
    (inheritedBooleanCondition : List BooleanLiteral)
    (caseCondition : List BooleanLiteral) (variableValues : VariableValues)
    (hinherited : booleanConditionAllows variableValues inheritedBooleanCondition = true)
    (hcase : booleanConditionAllows variableValues caseCondition = true)
    : booleanConditionAllows variableValues
        (extendBooleanCondition inheritedBooleanCondition caseCondition)
      = true := by
  unfold extendBooleanCondition
  have hsource :
      booleanConditionAllows variableValues
          (inheritedBooleanCondition ++ caseCondition)
        = true := by
    rw [booleanConditionAllows_append, hinherited, hcase, Bool.true_and]
  cases hcanonical
        : canonicalBooleanCondition (inheritedBooleanCondition ++ caseCondition) with
  | none => simpa [hcanonical] using hinherited
  | some candidate =>
      simp only [Option.getD_some]
      rw [← canonicalBooleanCondition_some_allows variableValues _ _ hcanonical]
      exact hsource

private theorem resolve_conditions
    (inheritedBooleanCondition : List BooleanLiteral)
    (caseCondition : List BooleanLiteral) (cursor : CaseCursor)
    (possibleTypes : PossibleTypeRegion) (runtimeType : Name)
    (variableValues : VariableValues)
    (hinherited : booleanConditionAllows variableValues inheritedBooleanCondition = true)
    (hcase : booleanConditionAllows variableValues caseCondition = true)
    (hruntime : runtimeType ∈ possibleTypes)
    : let resolved :=
        resolve inheritedBooleanCondition caseCondition cursor
          possibleTypes runtimeType variableValues
      runtimeType ∈ resolved.possibleTypes
      ∧ booleanConditionAllows variableValues resolved.inheritedBooleanCondition
        = true := by
  rw [resolve.eq_1]
  split <;> rename_i hbranches
  · exact ⟨hruntime, extendBooleanCondition_allows inheritedBooleanCondition
      caseCondition variableValues hinherited hcase⟩
  · rename_i branch rest
    cases hcondition : branch.condition with
    | typeCondition typeName =>
        have hregion := chooseTypeRegion_mem possibleTypes
          [branch.body.condition.possibleTypes] runtimeType hruntime
        simp only
        exact resolve_conditions inheritedBooleanCondition caseCondition _ _
          runtimeType variableValues hinherited hcase hregion.2
    | booleanLiteral literal =>
        simp only
        let value :=
          (inputValueBoolean? variableValues (.variable literal.variableName)).getD false
        let selectedLiteral :=
          if value then BooleanLiteral.positive literal.variableName
          else BooleanLiteral.negative literal.variableName
        have hselected : booleanConditionAllows variableValues [selectedLiteral] = true :=
          selectedBooleanLiteral_allows variableValues literal.variableName
        have hselected' : selectedLiteral.allows variableValues = true := by
          simpa [booleanConditionAllows] using hselected
        have hnextCase : booleanConditionAllows variableValues
            (selectedLiteral :: caseCondition) = true := by
          simp [booleanConditionAllows, hselected', hcase]
        exact resolve_conditions inheritedBooleanCondition
          (selectedLiteral :: caseCondition) _ possibleTypes runtimeType
          variableValues hinherited hnextCase hruntime
termination_by caseCursorUnresolvedCount cursor
decreasing_by
  all_goals first
    | apply nextTypeBranch_unresolved_lt <;> assumption
    | apply resolveBooleanBranch_unresolved_lt <;> assumption
    | apply selectBranch_unresolved_lt <;> assumption
    | apply skipBranch_unresolved_lt <;> assumption

theorem fieldGroups_conditions
    (inheritedBooleanCondition : List BooleanLiteral)
    (cursor : CaseCursor) (possibleTypes : PossibleTypeRegion)
    (runtimeType : Name) (variableValues : VariableValues)
    (hinherited : booleanConditionAllows variableValues inheritedBooleanCondition = true)
    (hruntime : runtimeType ∈ possibleTypes)
    (group : CollectedFieldGroup)
    (hgroup
      : group
        ∈ fieldGroups inheritedBooleanCondition cursor possibleTypes
            runtimeType variableValues)
    : booleanConditionAllows variableValues group.inheritedBooleanCondition = true
      ∧ group.condition.allows variableValues runtimeType = true := by
  have hresolved := resolve_conditions inheritedBooleanCondition [] cursor possibleTypes
    runtimeType variableValues hinherited rfl hruntime
  unfold fieldGroups CaseCursor.fieldGroups at hgroup
  rcases List.mem_map.mp hgroup with ⟨sourceGroup, hsourceGroup, rfl⟩
  constructor
  · exact hresolved.2
  · simp [Condition.allows, hresolved.1, booleanConditionAllows]

theorem fieldGroups_shape
    (inheritedBooleanCondition : List BooleanLiteral)
    (cursor : CaseCursor) (possibleTypes : PossibleTypeRegion)
    (runtimeType : Name) (variableValues : VariableValues)
    (group : CollectedFieldGroup)
    (hgroup
      : group
        ∈ fieldGroups inheritedBooleanCondition cursor possibleTypes
            runtimeType variableValues)
    : group.selections ≠ []
      ∧ ∀ selection,
          selection ∈ group.selections
          -> ∃ field : Field, selection = field.toSelection group.responseName := by
  unfold fieldGroups CaseCursor.fieldGroups at hgroup
  rcases List.mem_map.mp hgroup with ⟨sourceGroup, hsourceGroup, rfl⟩
  constructor
  · exact CollectedFieldGroup.selections_ne_nil _
  · intro selection hselection
    rcases List.mem_map.mp hselection with ⟨field, hfield, rfl⟩
    exact ⟨field, rfl⟩

private theorem resolve_pendingBranches
    (inheritedBooleanCondition : List BooleanLiteral)
    (caseCondition : List BooleanLiteral) (cursor : CaseCursor)
    (possibleTypes : PossibleTypeRegion) (runtimeType : Name)
    (variableValues : VariableValues)
    : (resolve inheritedBooleanCondition caseCondition cursor possibleTypes
        runtimeType variableValues).cursor.pendingBranches
      = [] := by
  rw [resolve.eq_1]
  split <;> rename_i hbranches
  · exact hbranches
  · rename_i branch rest
    cases hcondition : branch.condition with
    | typeCondition typeName =>
        simp only
        exact resolve_pendingBranches inheritedBooleanCondition caseCondition _ _
          runtimeType variableValues
    | booleanLiteral literal =>
        simp only
        let value :=
          (inputValueBoolean? variableValues (.variable literal.variableName)).getD false
        exact resolve_pendingBranches inheritedBooleanCondition
          ((if value then .positive literal.variableName else .negative literal.variableName)
            :: caseCondition) _ possibleTypes runtimeType variableValues
termination_by caseCursorUnresolvedCount cursor
decreasing_by
  all_goals first
    | apply nextTypeBranch_unresolved_lt <;> assumption
    | apply resolveBooleanBranch_unresolved_lt <;> assumption
    | apply selectBranch_unresolved_lt <;> assumption
    | apply skipBranch_unresolved_lt <;> assumption

theorem fieldGroupsToExecutable_eq_collectRuntimeFieldGroups
    (schema : Schema) (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral) (tree : Tree)
    (runtimeType : Name) (variableValues : VariableValues)
    (hinherited : booleanConditionAllows variableValues inheritedBooleanCondition = true)
    (hcondition : tree.condition.allows variableValues runtimeType = true)
    (hcoherent : tree.BranchesCoherent schema inheritedBooleanCondition)
    (hruntime : runtimeType ∈ tree.condition.possibleTypes)
    : (fieldGroups inheritedBooleanCondition (.ofConditionTree tree)
        tree.condition.possibleTypes runtimeType variableValues).map
        CollectedFieldGroup.toExecutableGroup
      = tree.collectRuntimeFieldGroups variableValues runtimeType := by
  have hvalid :=
    pendingValid_of_coherent schema inheritedBooleanCondition variableValues runtimeType
      tree.condition tree.branches hcondition
      (by simpa [Tree.BranchesCoherent] using hcoherent)
  have hnames := resolve_namedFields schema parentType inheritedBooleanCondition []
    (.ofConditionTree tree) tree.condition.possibleTypes runtimeType variableValues
    hinherited hruntime hvalid
  let resolved := resolve inheritedBooleanCondition [] (.ofConditionTree tree)
    tree.condition.possibleTypes runtimeType variableValues
  have hterminal : resolved.cursor.pendingBranches = [] := by
    exact resolve_pendingBranches inheritedBooleanCondition [] (.ofConditionTree tree)
      tree.condition.possibleTypes runtimeType variableValues
  have hnamed : resolved.cursor.namedFields = runtimeNamedFields variableValues runtimeType tree := by
    have hroot := runtimeNamedFields_eq_local_append_pending variableValues runtimeType tree
      hcondition
    change resolved.cursor.namedFields
        ++ pendingRuntimeNamedFields variableValues runtimeType
          resolved.cursor.pendingBranches
      = _ at hnames
    rw [hterminal] at hnames
    simp only [pendingRuntimeNamedFields, List.flatMap_nil, List.append_nil] at hnames
    have hroot' :
        (CaseCursor.ofConditionTree tree).namedFields
            ++ pendingRuntimeNamedFields variableValues runtimeType
              (CaseCursor.ofConditionTree tree).pendingBranches
          = runtimeNamedFields variableValues runtimeType tree := by
      simpa [CaseCursor.ofConditionTree, CaseCursor.namedFields] using hroot.symm
    exact hnames.trans hroot'
  unfold fieldGroups
  change (resolved.cursor.fieldGroups resolved.inheritedBooleanCondition
      resolved.possibleTypes).map
      CollectedFieldGroup.toExecutableGroup = _
  rw [CaseCursor.fieldGroups,
    toExecutableGroup_collectFieldGroups,
    fieldGroupToExecutableGroup_collectFieldGroups, hnamed,
    runtimeNamedFields_map]
  rfl

end RuntimeCase
end ExactCases
end TreeSummary
end GraphQL
