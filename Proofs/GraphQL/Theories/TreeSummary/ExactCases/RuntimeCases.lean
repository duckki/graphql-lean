import GraphQL.Theories.TreeSummary.ExactCases
import Proofs.GraphQL.Theories.ConditionTree.Extraction
import Proofs.GraphQL.Theories.ConditionTree.Reduce.RuntimeBundles
import Proofs.GraphQL.Theories.ConditionTree.RuntimeExtraction
import Proofs.GraphQL.Theories.TreeSummary.Algebra
import Proofs.GraphQL.Theories.TreeSummary.ExactCases.Cases

/-! Proof-only deterministic runtime paths through the exact-case-tree fold. -/

namespace GraphQL
namespace TreeSummary
namespace ExactCases

open GraphQL.ConditionTree
open GraphQL.ConditionTree.Termination
open GraphQL.Execution
open TreeSummary.Measure
open Measure

namespace RuntimeCase

section Interpreter

def chooseTypeRegion (runtimeType : Name) (fallback : PossibleTypeRegion)
    : List PossibleTypeRegion -> PossibleTypeRegion
  | [] => fallback
  | region :: rest =>
      if region.contains runtimeType then
        region
      else
        chooseTypeRegion runtimeType fallback rest

structure Resolved where
  tree : CaseForest
  possibleTypes : PossibleTypeRegion
  inheritedBooleanCondition : List BooleanLiteral

def resolve (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (tree : CaseForest) (possibleTypes : PossibleTypeRegion)
    (runtimeType : Name) (variableValues : VariableValues)
    : Resolved :=
  if _hbranches : tree.hasUnresolvedBranches then
    let region :=
      chooseTypeRegion runtimeType possibleTypes (tree.typeRegions possibleTypes)
    resolve parentType
      (extendBooleanCondition inheritedBooleanCondition tree.booleanVariables
        variableValues)
      (tree.resolveBranches region variableValues) region runtimeType variableValues
  else
    { tree, possibleTypes, inheritedBooleanCondition }
termination_by
  (caseForestResponseDepth tree, caseForestUnresolvedCount tree, 3, 0)
decreasing_by
  apply quadruple_lt_of_depth_le_of_control_lt
  · exact resolveBranches_responseDepth_le region variableValues tree
  · exact resolveBranches_unresolvedCount_lt region variableValues tree (by assumption)

def fieldGroups (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (tree : CaseForest) (possibleTypes : PossibleTypeRegion)
    (runtimeType : Name) (variableValues : VariableValues)
    : List CollectedFieldGroup :=
  let resolved :=
    resolve parentType inheritedBooleanCondition tree possibleTypes runtimeType
      variableValues
  resolved.tree.fieldGroups resolved.inheritedBooleanCondition resolved.possibleTypes

def summarize (algebra : Algebra) (schema : Schema)
    (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
    (tree : CaseForest) (possibleTypes : PossibleTypeRegion)
    (runtimeType : Name) (variableValues : VariableValues)
    (fixedVariableValues : VariableValues := variableValues)
    : algebra.Summary :=
  if _hbranches : tree.hasUnresolvedBranches then
    let region :=
      chooseTypeRegion runtimeType possibleTypes (tree.typeRegions possibleTypes)
    summarize algebra schema parentType
      (extendBooleanCondition inheritedBooleanCondition tree.booleanVariables
        variableValues)
      (tree.resolveBranches region variableValues) region runtimeType
      variableValues fixedVariableValues
  else
    CaseForest.summarizeFieldGroups algebra schema
      (tree.fieldGroups inheritedBooleanCondition possibleTypes)
      variableValues fixedVariableValues
termination_by
  (caseForestResponseDepth tree, caseForestUnresolvedCount tree, 3, 0)
decreasing_by
  apply quadruple_lt_of_depth_le_of_control_lt
  · exact resolveBranches_responseDepth_le region variableValues tree
  · exact resolveBranches_unresolvedCount_lt region variableValues tree (by assumption)

end Interpreter

-----------------------------------------------------------------------------------------
-- Runtime correspondence
-----------------------------------------------------------------------------------------

private def namedFieldToExecutable (parentType : Name) (field : NamedField)
    : ExecutableField :=
  {
    parentType
    responseName := field.responseName
    fieldName := field.field.fieldName
    arguments := field.field.arguments
    selectionSet := field.field.selectionSet
  }

private def fieldGroupToExecutableGroup (parentType : Name) (group : FieldGroup)
    : Name × List ExecutableField :=
  (
    group.responseName,
    group.fields.map
      fun field =>
        {
          parentType
          responseName := group.responseName
          fieldName := field.fieldName
          arguments := field.arguments
          selectionSet := field.selectionSet
        }
  )

private theorem fieldGroupToExecutableGroup_addFieldWithResponseName
    (parentType responseName : Name) (field : Field)
    (groups : List FieldGroup)
    : (ConditionTree.addFieldWithResponseName responseName field groups).map
        (fieldGroupToExecutableGroup parentType)
      = addExecutableGroup
          (
            responseName,
            [{
              parentType
              responseName
              fieldName := field.fieldName
              arguments := field.arguments
              selectionSet := field.selectionSet
            }]
          )
          (groups.map (fieldGroupToExecutableGroup parentType)) := by
  induction groups with
  | nil => simp [ConditionTree.addFieldWithResponseName,
      addExecutableGroup, fieldGroupToExecutableGroup, FieldGroup.fields]
  | cons group rest ih =>
      by_cases heq : responseName = group.responseName
      · subst responseName
        simp [ConditionTree.addFieldWithResponseName,
          addExecutableGroup, fieldGroupToExecutableGroup,
          FieldGroup.fields, List.map_append]
      · have hfalse : (responseName == group.responseName) = false := by
          exact Bool.eq_false_iff.mpr fun htrue => heq (beq_iff_eq.mp htrue)
        have hfalse' : (group.responseName == responseName) = false := by
          exact Bool.eq_false_iff.mpr fun htrue => heq (beq_iff_eq.mp htrue).symm
        simp [ConditionTree.addFieldWithResponseName,
          addExecutableGroup, fieldGroupToExecutableGroup,
          hfalse, hfalse', ih]

private theorem fieldGroupToExecutableGroup_collectFieldGroups
    (parentType : Name) (fields : List NamedField)
    : (ConditionTree.collectFieldGroups fields).map
        (fieldGroupToExecutableGroup parentType)
      = groupExecutableFields (fields.map (namedFieldToExecutable parentType)) := by
  unfold ConditionTree.collectFieldGroups groupExecutableFields
  have hfold : ∀ (rest : List NamedField) (groups : List FieldGroup),
      (rest.foldl
          (fun current field => ConditionTree.addFieldToGroups field current)
          groups).map (fieldGroupToExecutableGroup parentType)
        = rest.foldl
            (fun current field =>
              addExecutableGroup
                (field.responseName, [namedFieldToExecutable parentType field]) current)
            (groups.map (fieldGroupToExecutableGroup parentType)) := by
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

def collectedFieldGroupToExecutableGroup (executionParentType : Name)
    (group : CollectedFieldGroup)
    : Name × List ExecutableField :=
  (
    group.responseName,
    group.selections.filterMap
      fun selection =>
        match selection with
        | .field responseName fieldName arguments _directives selectionSet =>
            some
              {
                parentType := executionParentType
                responseName
                fieldName
                arguments
                selectionSet
              }
        | .inlineFragment _typeCondition _directives _selectionSet => none
  )

private theorem fieldSelectionsToExecutableFields
    (executionParentType responseName : Name) (fields : List Field)
    : (fields.map (Field.toSelection responseName)).filterMap
        (fun selection =>
          match selection with
          | .field selectedResponseName fieldName arguments _directives selectionSet =>
              some
                ({
                    parentType := executionParentType
                    responseName := selectedResponseName
                    fieldName
                    arguments
                    selectionSet
                  }
                  : ExecutableField)
          | .inlineFragment _typeCondition _directives _selectionSet => none)
      = fields.map
          fun field =>
            ({
                parentType := executionParentType
                responseName
                fieldName := field.fieldName
                arguments := field.arguments
                selectionSet := field.selectionSet
              }
              : ExecutableField) := by
  induction fields with
  | nil => rfl
  | cons field rest ih =>
      simp [Field.toSelection, ih]

private theorem collectedFieldGroupToExecutableGroup_collectFieldGroups
    (executionParentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral) (condition : Condition)
    (groups : List FieldGroup)
    : (TreeSummary.collectFieldGroups inheritedBooleanCondition condition groups).map
        (collectedFieldGroupToExecutableGroup executionParentType)
      = groups.map (fieldGroupToExecutableGroup executionParentType) := by
  unfold TreeSummary.collectFieldGroups
  rw [List.map_map]
  apply List.map_congr_left
  intro group hgroup
  change collectedFieldGroupToExecutableGroup executionParentType
      {
        inheritedBooleanCondition
        condition
        fieldGroup := group
      }
    = fieldGroupToExecutableGroup executionParentType group
  apply Prod.ext
  · rfl
  · unfold collectedFieldGroupToExecutableGroup fieldGroupToExecutableGroup
    unfold CollectedFieldGroup.responseName CollectedFieldGroup.selections
      FieldGroup.selections
    exact fieldSelectionsToExecutableFields executionParentType group.responseName
      group.fields

private def runtimeNamedFields (variableValues : VariableValues)
    (runtimeType : Name) (tree : Tree)
    : List NamedField :=
  tree.storedFieldEntries.filterMap
    fun entry =>
      if entry.1.allows variableValues runtimeType then some entry.2 else none

private theorem runtimeNamedFields_map
    (parentType runtimeType : Name) (variableValues : VariableValues)
    (tree : Tree)
    : (runtimeNamedFields variableValues runtimeType tree).map
        (namedFieldToExecutable parentType)
      = tree.collectRuntimeFields variableValues parentType runtimeType := by
  unfold runtimeNamedFields Tree.collectRuntimeFields
  induction tree.storedFieldEntries with
  | nil => simp [runtimeFieldsForEntries]
  | cons entry rest ih =>
      cases hallows : entry.1.allows variableValues runtimeType <;>
        simp [runtimeFieldsForEntries, hallows, ih, namedFieldToExecutable]

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
      exact List.all_eq_true.mpr fun typeName hmem => by
        rw [hconstant typeName hmem, hallowed]
  | false =>
      exact List.all_eq_false.mpr
        ⟨runtimeType, hruntime, by rw [hallowed]; simp⟩

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
        rw [possibleTypesSubset_eq_contains_of_constant
          region
          (intersectPossibleTypes parentCondition.possibleTypes
            (schema.getPossibleTypes typeName))
          runtimeType hruntime huniform]
        rcases Bool.and_eq_true_iff.mp hparent with ⟨hpossible, hboolean⟩
        simp only [Condition.allows,
          SelectionConditions.contains_intersectPossibleTypes,
          hpossible, hboolean, Bool.true_and]
        simp
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
    parentType parentType runtimeType inheritedBooleanCondition hinherited hcoherent
  rw [Tree.runtimeReductionBundles, if_neg (by simpa using hcondition),
    RuntimeFieldBundle.allSourceFields] at hsource
  have hexecutable : tree.collectRuntimeFields variableValues parentType runtimeType = [] := by
    simpa [RuntimeFieldBundle.allSourceFields] using hsource.symm
  have hmapped := runtimeNamedFields_map parentType runtimeType variableValues tree
  rw [hexecutable] at hmapped
  cases hfields : runtimeNamedFields variableValues runtimeType tree with
  | nil => rfl
  | cons field rest => simp [hfields] at hmapped

private theorem selectedBody_runtimeNamedFields
    (schema : Schema) (variableValues : VariableValues)
    (parentType runtimeType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (body : Tree) (selected : Bool)
    (hinherited : booleanConditionAllows variableValues inheritedBooleanCondition = true)
    (hcoherent : body.BranchesCoherent schema inheritedBooleanCondition)
    (hselected : selected = body.condition.allows variableValues runtimeType)
    : (if selected then [body] else []).flatMap
        (runtimeNamedFields variableValues runtimeType)
      = body.storedFieldEntries.filterMap
          fun entry =>
            if entry.1.allows variableValues runtimeType then some entry.2 else none := by
  change (if selected then [body] else []).flatMap
      (runtimeNamedFields variableValues runtimeType)
    = runtimeNamedFields variableValues runtimeType body
  rw [hselected]
  cases hallows : body.condition.allows variableValues runtimeType with
  | true => simp
  | false =>
      have hnil := runtimeNamedFields_eq_nil_of_condition_false schema variableValues
        parentType runtimeType inheritedBooleanCondition body hinherited hallows hcoherent
      simp [hnil]

private theorem selectedChildren_runtimeNamedFields
    (schema : Schema) (variableValues : VariableValues) (runtimeType : Name)
    (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
    (parentCondition : Condition) (branches : List (Branch Tree))
    (region : PossibleTypeRegion)
    (hinherited : booleanConditionAllows variableValues inheritedBooleanCondition = true)
    (hparent : parentCondition.allows variableValues runtimeType = true)
    (hcoherent
      : branchesCoherent schema inheritedBooleanCondition parentCondition branches)
    (hruntime : runtimeType ∈ region)
    (huniform
      : ∀ branch,
          branch ∈ branches
          -> match branch.condition with
              | .typeCondition _typeName =>
                  ∀ candidate,
                    candidate ∈ region
                    -> branch.body.condition.possibleTypes.contains candidate
                        = branch.body.condition.possibleTypes.contains runtimeType
              | .booleanLiteral _literal => True)
    : (CaseForest.selectedChildren region variableValues branches).flatMap
        (runtimeNamedFields variableValues runtimeType)
      = (branchStoredFieldEntries branches).filterMap
          fun entry =>
            if entry.1.allows variableValues runtimeType then some entry.2 else none := by
  cases branches with
  | nil => simp [CaseForest.selectedChildren, branchStoredFieldEntries]
  | cons branch rest =>
      rw [branchesCoherent] at hcoherent
      have hselected := branchSelected_eq_bodyAllows schema variableValues runtimeType
        inheritedBooleanCondition parentCondition branch region hinherited hparent
        hcoherent.1 hruntime (huniform branch (by simp))
      have hrest := selectedChildren_runtimeNamedFields schema variableValues
        runtimeType parentType inheritedBooleanCondition parentCondition rest region
        hinherited hparent hcoherent.2.2 hruntime (by
          intro candidate hcandidate
          exact huniform candidate (by simp [hcandidate]))
      rw [CaseForest.selectedChildren, branchStoredFieldEntries,
        List.filterMap_append]
      cases hcondition : branch.condition with
      | typeCondition typeName =>
          simp only [hcondition] at hselected ⊢
          have hbody := selectedBody_runtimeNamedFields schema variableValues typeName runtimeType
            inheritedBooleanCondition branch.body
            (possibleTypesSubset region branch.body.condition.possibleTypes)
            hinherited hcoherent.2.1 hselected
          rw [← hbody, ← hrest]
          cases possibleTypesSubset region branch.body.condition.possibleTypes <;> simp
      | booleanLiteral literal =>
          simp only [hcondition] at hselected ⊢
          have hbody := selectedBody_runtimeNamedFields schema variableValues parentType runtimeType
            inheritedBooleanCondition branch.body
            (booleanConditionAllows variableValues [literal])
            hinherited hcoherent.2.1 hselected
          rw [← hbody, ← hrest]
          cases booleanConditionAllows variableValues [literal] <;> simp
termination_by sizeOf branches
decreasing_by
  all_goals
    subst branches
    cases branch
    simp_wf
    omega

private def ActiveTreesValid (schema : Schema)
    (inheritedBooleanCondition : List BooleanLiteral)
    (variableValues : VariableValues) (runtimeType : Name)
    (trees : List Tree)
    : Prop :=
  ∀ tree,
    tree ∈ trees
    -> tree.condition.allows variableValues runtimeType = true
        ∧ tree.BranchesCoherent schema inheritedBooleanCondition

private theorem branchBodyPossibleTypes_mem
    (tree : CaseForest) (item : Tree) (hitem : item ∈ tree.activeTrees)
    (branch : Branch Tree) (hbranch : branch ∈ item.branches)
    (typeName : Name) (hcondition : branch.condition = .typeCondition typeName)
    : branch.body.condition.possibleTypes ∈ tree.typeBranchPossibleTypes := by
  unfold CaseForest.typeBranchPossibleTypes CaseForest.branches
  apply List.mem_filterMap.mpr
  refine ⟨branch, ?_, ?_⟩
  · exact List.mem_flatMap.mpr ⟨item, hitem, hbranch⟩
  · simp [hcondition]

private theorem selectedChildren_valid
    (schema : Schema) (variableValues : VariableValues) (runtimeType : Name)
    (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
    (parentCondition : Condition) (branches : List (Branch Tree))
    (region : PossibleTypeRegion)
    (hinherited : booleanConditionAllows variableValues inheritedBooleanCondition = true)
    (hparent : parentCondition.allows variableValues runtimeType = true)
    (hcoherent
      : branchesCoherent schema inheritedBooleanCondition parentCondition branches)
    (hruntime : runtimeType ∈ region)
    (huniform
      : ∀ branch,
          branch ∈ branches
          -> match branch.condition with
              | .typeCondition _typeName =>
                  ∀ candidate,
                    candidate ∈ region
                    -> branch.body.condition.possibleTypes.contains candidate
                        = branch.body.condition.possibleTypes.contains runtimeType
              | .booleanLiteral _literal => True)
    : ActiveTreesValid schema inheritedBooleanCondition variableValues runtimeType
        (CaseForest.selectedChildren region variableValues branches) := by
  cases branches with
  | nil => simp [CaseForest.selectedChildren, ActiveTreesValid]
  | cons branch rest =>
      rw [branchesCoherent] at hcoherent
      have hselected := branchSelected_eq_bodyAllows schema variableValues runtimeType
        inheritedBooleanCondition parentCondition branch region hinherited hparent
        hcoherent.1 hruntime (huniform branch (by simp))
      have hrest := selectedChildren_valid schema variableValues runtimeType
        parentType inheritedBooleanCondition parentCondition rest region hinherited
        hparent hcoherent.2.2 hruntime (by
          intro candidate hcandidate
          exact huniform candidate (by simp [hcandidate]))
      intro item hitem
      cases hcondition : branch.condition with
      | typeCondition typeName =>
          simp only [CaseForest.selectedChildren, hcondition] at hitem
          simp only [hcondition] at hselected
          rw [hselected] at hitem
          cases hallows : branch.body.condition.allows variableValues runtimeType with
          | false =>
              simp only [hallows, Bool.false_eq_true, if_false] at hitem
              exact hrest item hitem
          | true =>
              simp only [hallows, if_true, List.mem_cons] at hitem
              rcases hitem with hequal | htail
              · subst item
                exact ⟨hallows, hcoherent.2.1⟩
              · exact hrest item htail
      | booleanLiteral literal =>
          simp only [CaseForest.selectedChildren, hcondition] at hitem
          simp only [hcondition] at hselected
          rw [hselected] at hitem
          cases hallows : branch.body.condition.allows variableValues runtimeType with
          | false =>
              simp only [hallows, Bool.false_eq_true, if_false] at hitem
              exact hrest item hitem
          | true =>
              simp only [hallows, if_true, List.mem_cons] at hitem
              rcases hitem with hequal | htail
              · subst item
                exact ⟨hallows, hcoherent.2.1⟩
              · exact hrest item htail
termination_by sizeOf branches
decreasing_by
  all_goals
    subst branches
    cases branch
    simp_wf
    omega

private theorem resolveActiveTrees_valid_aux
    (schema : Schema) (variableValues : VariableValues) (runtimeType : Name)
    (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
    (items : List Tree) (region : PossibleTypeRegion)
    (hinherited : booleanConditionAllows variableValues inheritedBooleanCondition = true)
    (hvalid
      : ActiveTreesValid schema inheritedBooleanCondition variableValues runtimeType
          items)
    (hruntime : runtimeType ∈ region)
    (huniform
      : ∀ item,
          item ∈ items
          -> ∀ branch,
              branch ∈ item.branches
              -> match branch.condition with
                  | .typeCondition _typeName =>
                      ∀ candidate,
                        candidate ∈ region
                        -> branch.body.condition.possibleTypes.contains candidate
                            = branch.body.condition.possibleTypes.contains runtimeType
                  | .booleanLiteral _literal => True)
    : ActiveTreesValid schema inheritedBooleanCondition variableValues runtimeType
        (CaseForest.resolveActiveTrees region variableValues items) := by
  induction items with
  | nil => simp [CaseForest.resolveActiveTrees, ActiveTreesValid]
  | cons current rest ih =>
      have hcurrent := hvalid current (by simp)
      have hcurrentCoherent :
          branchesCoherent schema inheritedBooleanCondition current.condition
            current.branches := by
        simpa [Tree.BranchesCoherent] using hcurrent.2
      have hselected := selectedChildren_valid schema variableValues runtimeType
        parentType inheritedBooleanCondition current.condition current.branches region
        hinherited hcurrent.1 hcurrentCoherent hruntime (huniform current (by simp))
      have hrest := ih
        (by
          intro candidate hcandidate
          exact hvalid candidate (by simp [hcandidate]))
        (by
          intro candidate hcandidate
          exact huniform candidate (by simp [hcandidate]))
      intro item hitem
      simp only [CaseForest.resolveActiveTrees, List.mem_cons,
        List.mem_append] at hitem
      rcases hitem with hlocal | hselectedMem | hrestMem
      · subst item
        exact ⟨hcurrent.1, by simp [Tree.BranchesCoherent, branchesCoherent]⟩
      · exact hselected item hselectedMem
      · exact hrest item hrestMem

private theorem resolveActiveTrees_valid
    (schema : Schema) (variableValues : VariableValues) (runtimeType : Name)
    (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
    (tree : CaseForest) (scope region : PossibleTypeRegion)
    (hinherited : booleanConditionAllows variableValues inheritedBooleanCondition = true)
    (hvalid
      : ActiveTreesValid schema inheritedBooleanCondition variableValues runtimeType
          tree.activeTrees)
    (hruntime : runtimeType ∈ region)
    (hregion : region ∈ tree.typeRegions scope)
    : ActiveTreesValid schema inheritedBooleanCondition variableValues runtimeType
        (CaseForest.resolveActiveTrees region variableValues tree.activeTrees) := by
  have huniform := (CaseForest.typeRegions_exact tree scope).2.2
    region hregion runtimeType hruntime
  apply resolveActiveTrees_valid_aux schema variableValues runtimeType parentType
    inheritedBooleanCondition tree.activeTrees region hinherited hvalid hruntime
  intro item hitem branch hbranch
  cases hcondition : branch.condition with
  | typeCondition typeName =>
      intro candidate hcandidate
      exact (huniform candidate hcandidate branch.body.condition.possibleTypes
        (branchBodyPossibleTypes_mem tree item hitem branch hbranch
          typeName hcondition)).symm
  | booleanLiteral literal => trivial

private theorem branchless_runtimeNamedFields
    (variableValues : VariableValues) (runtimeType : Name) (tree : Tree)
    (hallows : tree.condition.allows variableValues runtimeType = true)
    : runtimeNamedFields variableValues runtimeType { tree with branches := [] }
      = tree.fields.flatMap
          fun group =>
            group.fields.map
              fun field =>
                ({ responseName := group.responseName, field } : NamedField) := by
  unfold runtimeNamedFields
  rw [Tree.storedFieldEntries]
  simp only [branchStoredFieldEntries, List.append_nil]
  induction tree.fields with
  | nil => rfl
  | cons group rest ih =>
      rw [List.flatMap_cons, List.filterMap_append, List.flatMap_cons, ih]
      congr 1
      induction group.fields with
      | nil => rfl
      | cons field fields tail_ih =>
          simp [hallows, tail_ih]

private theorem runtimeNamedFields_eq_local_append_branches
    (variableValues : VariableValues) (runtimeType : Name) (tree : Tree)
    (hallows : tree.condition.allows variableValues runtimeType = true)
    : runtimeNamedFields variableValues runtimeType tree
      = (tree.fields.flatMap
          fun group =>
            group.fields.map
              fun field =>
                ({ responseName := group.responseName, field } : NamedField))
        ++ (branchStoredFieldEntries tree.branches).filterMap
            fun entry =>
              if entry.1.allows variableValues runtimeType then
                some entry.2
              else
                none := by
  unfold runtimeNamedFields
  rw [Tree.storedFieldEntries, List.filterMap_append]
  congr 1
  have hlocal := branchless_runtimeNamedFields variableValues runtimeType tree hallows
  unfold runtimeNamedFields at hlocal
  rw [Tree.storedFieldEntries] at hlocal
  simpa [branchStoredFieldEntries] using hlocal

private theorem resolveActiveTrees_runtimeNamedFields_aux
    (schema : Schema) (variableValues : VariableValues) (runtimeType : Name)
    (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
    (items : List Tree) (region : PossibleTypeRegion)
    (hinherited : booleanConditionAllows variableValues inheritedBooleanCondition = true)
    (hvalid
      : ActiveTreesValid schema inheritedBooleanCondition variableValues runtimeType
          items)
    (hruntime : runtimeType ∈ region)
    (huniform
      : ∀ item,
          item ∈ items
          -> ∀ branch,
              branch ∈ item.branches
              -> match branch.condition with
                  | .typeCondition _typeName =>
                      ∀ candidate,
                        candidate ∈ region
                        -> branch.body.condition.possibleTypes.contains candidate
                            = branch.body.condition.possibleTypes.contains runtimeType
                  | .booleanLiteral _literal => True)
    : (CaseForest.resolveActiveTrees region variableValues items).flatMap
        (runtimeNamedFields variableValues runtimeType)
      = items.flatMap (runtimeNamedFields variableValues runtimeType) := by
  induction items with
  | nil => simp [CaseForest.resolveActiveTrees]
  | cons current rest ih =>
      have hcurrent := hvalid current (by simp)
      unfold Tree.BranchesCoherent at hcurrent
      have hbranches := selectedChildren_runtimeNamedFields schema variableValues
        runtimeType parentType inheritedBooleanCondition current.condition
        current.branches region hinherited hcurrent.1 hcurrent.2 hruntime (by
          exact huniform current (by simp))
      have htail := ih
        (by
          intro candidate hcandidate
          exact hvalid candidate (by simp [hcandidate]))
        (by
          intro candidate hcandidate
          exact huniform candidate (by simp [hcandidate]))
      rw [CaseForest.resolveActiveTrees, List.flatMap_cons,
        List.flatMap_append, htail]
      rw [branchless_runtimeNamedFields variableValues runtimeType current hcurrent.1,
        hbranches]
      change _ = runtimeNamedFields variableValues runtimeType current
        ++ rest.flatMap (runtimeNamedFields variableValues runtimeType)
      rw [runtimeNamedFields_eq_local_append_branches variableValues runtimeType current
        hcurrent.1]
      simp [List.append_assoc]

private theorem resolveActiveTrees_runtimeNamedFields
    (schema : Schema) (variableValues : VariableValues) (runtimeType : Name)
    (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
    (tree : CaseForest) (scope region : PossibleTypeRegion)
    (hinherited : booleanConditionAllows variableValues inheritedBooleanCondition = true)
    (hvalid
      : ActiveTreesValid schema inheritedBooleanCondition variableValues runtimeType
          tree.activeTrees)
    (hruntime : runtimeType ∈ region)
    (hregion : region ∈ tree.typeRegions scope)
    : (CaseForest.resolveActiveTrees region variableValues tree.activeTrees).flatMap
        (runtimeNamedFields variableValues runtimeType)
      = tree.activeTrees.flatMap (runtimeNamedFields variableValues runtimeType) := by
  have huniform := (CaseForest.typeRegions_exact tree scope).2.2
    region hregion runtimeType hruntime
  apply resolveActiveTrees_runtimeNamedFields_aux schema variableValues runtimeType
    parentType inheritedBooleanCondition tree.activeTrees region hinherited hvalid hruntime
  intro item hitem branch hbranch
  cases hcondition : branch.condition with
  | typeCondition typeName =>
      intro candidate hcandidate
      exact (huniform candidate hcandidate branch.body.condition.possibleTypes
        (branchBodyPossibleTypes_mem tree item hitem branch hbranch
          typeName hcondition)).symm
  | booleanLiteral literal => trivial

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
      | true =>
          have hmem := List.contains_iff_mem.mp hcontains
          simp [hmem]
      | false =>
          have hnotmem : runtimeType ∉ region := by
            intro hmem
            have htrue : region.contains runtimeType = true :=
              List.contains_iff_mem.mpr hmem
            exact Bool.noConfusion (hcontains.symm.trans htrue)
          have hrest : ∃ candidate, candidate ∈ rest ∧ runtimeType ∈ candidate := by
            rcases hexists with ⟨candidate, hcandidate, hruntime⟩
            simp only [List.mem_cons] at hcandidate
            rcases hcandidate with rfl | hcandidate
            · exact False.elim (hnotmem hruntime)
            · exact ⟨candidate, hcandidate, hruntime⟩
          have hchosen := ih hrest
          exact ⟨List.mem_cons_of_mem region hchosen.1, hchosen.2⟩

theorem chooseTypeRegion_mem
    (tree : CaseForest) (scope : PossibleTypeRegion)
    (runtimeType : Name) (hruntime : runtimeType ∈ scope)
    : let chosen := chooseTypeRegion runtimeType scope (tree.typeRegions scope)
      chosen ∈ tree.typeRegions scope ∧ runtimeType ∈ chosen := by
  have hexact := CaseForest.typeRegions_exact tree scope
  rcases hexact.2.1 runtimeType hruntime with ⟨region, hregion, _hunique⟩
  exact chooseTypeRegion_mem_of_exists runtimeType scope (tree.typeRegions scope)
    ⟨region, hregion.1, hregion.2⟩

private theorem namedFields_eq_runtimeNamedFields_of_branchless_aux
    (schema : Schema) (inheritedBooleanCondition : List BooleanLiteral)
    (variableValues : VariableValues) (runtimeType : Name)
    (items : List Tree)
    (hvalid
      : ActiveTreesValid schema inheritedBooleanCondition variableValues runtimeType
          items)
    (hbranches : ∀ item, item ∈ items -> item.branches = [])
    : (items.flatMap
        fun item =>
          item.fields.flatMap
            fun group =>
              group.fields.map
                fun field =>
                  ({ responseName := group.responseName, field } : NamedField))
      = items.flatMap (runtimeNamedFields variableValues runtimeType) := by
  induction items with
  | nil => rfl
  | cons current rest ih =>
      have hcurrentBranches := hbranches current (by simp)
      have hcurrent := hvalid current (by simp)
      have hrestValid :
          ActiveTreesValid schema inheritedBooleanCondition variableValues runtimeType
            rest := by
        intro candidate hcandidate
        exact hvalid candidate (by simp [hcandidate])
      have hrestBranches : ∀ item, item ∈ rest -> item.branches = [] := by
        intro item hitem
        exact hbranches item (by simp [hitem])
      rw [List.flatMap_cons, List.flatMap_cons, ih hrestValid hrestBranches]
      have hlocal := branchless_runtimeNamedFields variableValues runtimeType current
        hcurrent.1
      have heq : { current with branches := [] } = current := by
        cases current
        simp_all
      rw [heq] at hlocal
      exact congrArg
        (fun fields =>
          fields ++ rest.flatMap (runtimeNamedFields variableValues runtimeType))
        hlocal.symm

private theorem namedFields_eq_runtimeNamedFields_of_branchless
    (schema : Schema) (inheritedBooleanCondition : List BooleanLiteral)
    (variableValues : VariableValues) (runtimeType : Name)
    (tree : CaseForest)
    (hvalid
      : ActiveTreesValid schema inheritedBooleanCondition variableValues runtimeType
          tree.activeTrees)
    (hbranches : tree.hasUnresolvedBranches = false)
    : tree.namedFields
      = tree.activeTrees.flatMap (runtimeNamedFields variableValues runtimeType) := by
  apply namedFields_eq_runtimeNamedFields_of_branchless_aux schema
    inheritedBooleanCondition variableValues runtimeType tree.activeTrees hvalid
  intro item hitem
  unfold CaseForest.hasUnresolvedBranches at hbranches
  have hitemBranches := List.any_eq_false.mp hbranches item hitem
  simpa using hitemBranches

private theorem resolve_namedFields
    (schema : Schema) (parentType : Name)
    (fixedInheritedBooleanCondition currentInheritedBooleanCondition
      : List BooleanLiteral)
    (tree : CaseForest) (possibleTypes : PossibleTypeRegion)
    (runtimeType : Name) (variableValues : VariableValues)
    (hinherited
      : booleanConditionAllows variableValues fixedInheritedBooleanCondition = true)
    (hvalid
      : ActiveTreesValid schema fixedInheritedBooleanCondition variableValues
          runtimeType tree.activeTrees)
    (hruntime : runtimeType ∈ possibleTypes)
    : let resolved :=
        resolve parentType currentInheritedBooleanCondition tree possibleTypes
          runtimeType variableValues
      resolved.tree.namedFields
      = tree.activeTrees.flatMap (runtimeNamedFields variableValues runtimeType) := by
  rw [RuntimeCase.resolve]
  split <;> rename_i hbranches
  · let region :=
      chooseTypeRegion runtimeType possibleTypes (tree.typeRegions possibleTypes)
    have hregion := chooseTypeRegion_mem tree possibleTypes runtimeType hruntime
    let resolvedTree := tree.resolveBranches region variableValues
    have hvalidResolved :
        ActiveTreesValid schema fixedInheritedBooleanCondition variableValues
          runtimeType resolvedTree.activeTrees := by
      simpa [resolvedTree, CaseForest.resolveBranches] using
        resolveActiveTrees_valid schema variableValues runtimeType parentType
          fixedInheritedBooleanCondition tree possibleTypes region hinherited hvalid
          hregion.2 hregion.1
    have hfields :
        resolvedTree.activeTrees.flatMap
            (runtimeNamedFields variableValues runtimeType)
          = tree.activeTrees.flatMap
              (runtimeNamedFields variableValues runtimeType) := by
      simpa [resolvedTree, CaseForest.resolveBranches] using
        resolveActiveTrees_runtimeNamedFields schema variableValues runtimeType
          parentType fixedInheritedBooleanCondition tree possibleTypes region
          hinherited hvalid hregion.2 hregion.1
    exact (resolve_namedFields schema parentType fixedInheritedBooleanCondition
      (extendBooleanCondition currentInheritedBooleanCondition
        tree.booleanVariables variableValues)
      resolvedTree region runtimeType variableValues hinherited hvalidResolved
      hregion.2).trans hfields
  · have hbranchesFalse : tree.hasUnresolvedBranches = false := by
      cases hvalue : tree.hasUnresolvedBranches with
      | false => rfl
      | true => exact False.elim (hbranches hvalue)
    exact namedFields_eq_runtimeNamedFields_of_branchless schema
      fixedInheritedBooleanCondition variableValues runtimeType tree hvalid
      hbranchesFalse
termination_by
  (caseForestResponseDepth tree, caseForestUnresolvedCount tree, 3, 0)
decreasing_by
  apply quadruple_lt_of_depth_le_of_control_lt
  · exact resolveBranches_responseDepth_le region variableValues tree
  · exact resolveBranches_unresolvedCount_lt region variableValues tree (by assumption)

private theorem generatedBooleanCondition_allows
    (variableNames : BooleanVariableNames) (variableValues : VariableValues)
    : booleanConditionAllows variableValues
        (variableNames.filterMap
          fun variableName => do
            let value ← inputValueBoolean? variableValues (.variable variableName)
            pure <| if value then .positive variableName else .negative variableName)
      = true := by
  let literalFor : Name -> Option BooleanLiteral := fun variableName => do
    let value ← inputValueBoolean? variableValues (.variable variableName)
    pure <| if value then .positive variableName else .negative variableName
  change booleanConditionAllows variableValues
    (variableNames.filterMap literalFor) = true
  induction variableNames with
  | nil => rfl
  | cons variableName rest ih =>
      cases hvalue : inputValueBoolean? variableValues (.variable variableName) with
      | none => simpa [List.filterMap_cons, literalFor, hvalue] using ih
      | some value =>
          cases value <;>
            simpa [List.filterMap_cons, literalFor, hvalue,
              booleanConditionAllows, BooleanLiteral.allows,
              BooleanLiteral.toDirective, directiveAllowsSelectionBool] using ih

private theorem extendBooleanCondition_allows
    (inheritedBooleanCondition : List BooleanLiteral)
    (variableNames : BooleanVariableNames) (variableValues : VariableValues)
    (hinherited : booleanConditionAllows variableValues inheritedBooleanCondition = true)
    : booleanConditionAllows variableValues
        (extendBooleanCondition inheritedBooleanCondition variableNames variableValues)
      = true := by
  unfold extendBooleanCondition
  have hsource :
      booleanConditionAllows variableValues
          (inheritedBooleanCondition
            ++ variableNames.filterMap fun variableName => do
              let value ← inputValueBoolean? variableValues (.variable variableName)
              pure <| if value then .positive variableName else .negative variableName)
        = true := by
    rw [booleanConditionAllows_append, hinherited,
      generatedBooleanCondition_allows, Bool.true_and]
  cases hcanonical
        : canonicalBooleanCondition
            (inheritedBooleanCondition
              ++ variableNames.filterMap
                  fun variableName => do
                    let value ← inputValueBoolean? variableValues (.variable variableName)
                    pure
                    <|  if value then
                          .positive variableName
                        else
                          .negative variableName) with
  | none => simpa [hcanonical] using hinherited
  | some candidate =>
      simp only [Option.getD_some]
      rw [← canonicalBooleanCondition_some_allows variableValues _ _ hcanonical]
      exact hsource

private theorem resolve_conditions
    (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
    (tree : CaseForest) (possibleTypes : PossibleTypeRegion)
    (runtimeType : Name) (variableValues : VariableValues)
    (hinherited : booleanConditionAllows variableValues inheritedBooleanCondition = true)
    (hruntime : runtimeType ∈ possibleTypes)
    : let resolved :=
        resolve parentType inheritedBooleanCondition tree possibleTypes runtimeType
          variableValues
      runtimeType ∈ resolved.possibleTypes
      ∧ booleanConditionAllows variableValues resolved.inheritedBooleanCondition
        = true := by
    rw [RuntimeCase.resolve]
    split <;> rename_i hbranches
    · have hregion := chooseTypeRegion_mem tree possibleTypes runtimeType hruntime
      exact resolve_conditions parentType
        (extendBooleanCondition inheritedBooleanCondition tree.booleanVariables
          variableValues)
        (tree.resolveBranches
          (chooseTypeRegion runtimeType possibleTypes (tree.typeRegions possibleTypes))
          variableValues)
        (chooseTypeRegion runtimeType possibleTypes (tree.typeRegions possibleTypes))
        runtimeType variableValues
        (extendBooleanCondition_allows inheritedBooleanCondition tree.booleanVariables
          variableValues hinherited)
        hregion.2
    · exact ⟨hruntime, hinherited⟩
termination_by
  (caseForestResponseDepth tree, caseForestUnresolvedCount tree, 3, 0)
decreasing_by
  apply quadruple_lt_of_depth_le_of_control_lt
  · exact resolveBranches_responseDepth_le _ variableValues tree
  · exact resolveBranches_unresolvedCount_lt _ variableValues tree (by assumption)

theorem fieldGroups_conditions
    (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
    (tree : CaseForest) (possibleTypes : PossibleTypeRegion)
    (runtimeType : Name) (variableValues : VariableValues)
    (hinherited : booleanConditionAllows variableValues inheritedBooleanCondition = true)
    (hruntime : runtimeType ∈ possibleTypes)
    (group : CollectedFieldGroup)
    (hgroup
      : group
        ∈ fieldGroups parentType inheritedBooleanCondition tree possibleTypes
            runtimeType variableValues)
    : booleanConditionAllows variableValues group.inheritedBooleanCondition = true
      ∧ group.condition.allows variableValues runtimeType = true := by
  have hresolved := resolve_conditions parentType inheritedBooleanCondition tree
    possibleTypes runtimeType variableValues hinherited hruntime
  unfold fieldGroups CaseForest.fieldGroups at hgroup
  rcases List.mem_map.mp hgroup with ⟨sourceGroup, hsourceGroup, rfl⟩
  constructor
  · exact hresolved.2
  · simp [Condition.allows, hresolved.1, booleanConditionAllows]

theorem fieldGroupsToExecutable_eq
    (schema : Schema) (parentType executionParentType : Name)
    (fixedInheritedBooleanCondition currentInheritedBooleanCondition
      : List BooleanLiteral)
    (tree : CaseForest) (possibleTypes : PossibleTypeRegion)
    (runtimeType : Name) (variableValues : VariableValues)
    (hinherited
      : booleanConditionAllows variableValues fixedInheritedBooleanCondition = true)
    (hvalid
      : ActiveTreesValid schema fixedInheritedBooleanCondition variableValues runtimeType
          tree.activeTrees)
    (hruntime : runtimeType ∈ possibleTypes)
    : (fieldGroups parentType currentInheritedBooleanCondition tree possibleTypes
        runtimeType variableValues).map
        (collectedFieldGroupToExecutableGroup executionParentType)
      = groupExecutableFields
          ((tree.activeTrees.flatMap (runtimeNamedFields variableValues runtimeType)).map
            (namedFieldToExecutable executionParentType)) := by
  let resolved := resolve parentType currentInheritedBooleanCondition tree possibleTypes
    runtimeType variableValues
  have hnames := resolve_namedFields schema parentType fixedInheritedBooleanCondition
    currentInheritedBooleanCondition tree possibleTypes runtimeType variableValues
    hinherited hvalid hruntime
  change (TreeSummary.collectFieldGroups resolved.inheritedBooleanCondition
            { possibleTypes := resolved.possibleTypes, booleanCondition := [] }
            (ConditionTree.collectFieldGroups resolved.tree.namedFields)).map
            (collectedFieldGroupToExecutableGroup executionParentType)
          = _
  rw [collectedFieldGroupToExecutableGroup_collectFieldGroups,
    fieldGroupToExecutableGroup_collectFieldGroups]
  rw [hnames]

theorem fieldGroupsToExecutable_eq_collectRuntimeFieldGroups
    (schema : Schema) (parentType executionParentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral) (tree : Tree)
    (runtimeType : Name) (variableValues : VariableValues)
    (hinherited : booleanConditionAllows variableValues inheritedBooleanCondition = true)
    (hcondition : tree.condition.allows variableValues runtimeType = true)
    (hcoherent : tree.BranchesCoherent schema inheritedBooleanCondition)
    (hruntime : runtimeType ∈ tree.condition.possibleTypes)
    : (fieldGroups parentType inheritedBooleanCondition (.ofConditionTree tree)
        tree.condition.possibleTypes runtimeType variableValues).map
        (collectedFieldGroupToExecutableGroup executionParentType)
      = tree.collectRuntimeFieldGroups variableValues executionParentType
          runtimeType := by
  have hvalid :
      ActiveTreesValid schema inheritedBooleanCondition variableValues runtimeType
        (CaseForest.ofConditionTree tree).activeTrees := by
    intro item hitem
    simp only [CaseForest.ofConditionTree, List.mem_singleton] at hitem
    subst item
    exact ⟨hcondition, hcoherent⟩
  have hgroups := fieldGroupsToExecutable_eq schema parentType executionParentType
    inheritedBooleanCondition inheritedBooleanCondition (.ofConditionTree tree)
    tree.condition.possibleTypes runtimeType variableValues hinherited hvalid hruntime
  simpa [CaseForest.ofConditionTree, Tree.collectRuntimeFieldGroups,
    runtimeNamedFields_map executionParentType runtimeType variableValues tree] using
    hgroups

theorem fieldGroups_shape
    (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
    (tree : CaseForest) (possibleTypes : PossibleTypeRegion)
    (runtimeType : Name) (variableValues : VariableValues)
    (group : CollectedFieldGroup)
    (hgroup
      : group
        ∈ fieldGroups parentType inheritedBooleanCondition tree possibleTypes
            runtimeType variableValues)
    : group.selections ≠ []
      ∧ ∀ selection,
          selection ∈ group.selections
          -> ∃ field : Field, selection = field.toSelection group.responseName := by
  unfold fieldGroups CaseForest.fieldGroups at hgroup
  rcases List.mem_map.mp hgroup with ⟨sourceGroup, hsourceGroup, rfl⟩
  constructor
  · exact CollectedFieldGroup.selections_ne_nil _
  · intro selection hselection
    rcases List.mem_map.mp hselection with ⟨field, hfield, rfl⟩
    exact ⟨field, rfl⟩

theorem summarize_eq_resolved
    (algebra : Algebra) (schema : Schema) (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (tree : CaseForest) (possibleTypes : PossibleTypeRegion)
    (runtimeType : Name) (variableValues : VariableValues)
    (fixedVariableValues : VariableValues := variableValues)
    : summarize algebra schema parentType inheritedBooleanCondition tree
        possibleTypes runtimeType variableValues fixedVariableValues
      = CaseForest.summarizeFieldGroups algebra schema
          (fieldGroups parentType inheritedBooleanCondition tree possibleTypes
            runtimeType variableValues)
          variableValues fixedVariableValues := by
    rw [summarize, fieldGroups, resolve]
    split <;> rename_i hbranches
    · exact summarize_eq_resolved algebra schema parentType
        (extendBooleanCondition inheritedBooleanCondition tree.booleanVariables
          variableValues)
        (tree.resolveBranches
          (chooseTypeRegion runtimeType possibleTypes (tree.typeRegions possibleTypes))
          variableValues)
        (chooseTypeRegion runtimeType possibleTypes (tree.typeRegions possibleTypes))
        runtimeType variableValues fixedVariableValues
    · rfl
termination_by
  (caseForestResponseDepth tree, caseForestUnresolvedCount tree, 3, 0)
decreasing_by
  apply quadruple_lt_of_depth_le_of_control_lt
  · exact resolveBranches_responseDepth_le _ variableValues tree
  · exact resolveBranches_unresolvedCount_lt _ variableValues tree (by assumption)

theorem summarize_le
    (algebra : Algebra) (lawful : algebra.Lawful) (schema : Schema)
    (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
    (tree : CaseForest) (possibleTypes : PossibleTypeRegion)
    (runtimeType : Name) (variableValues : VariableValues)
    (fixedVariableValues : VariableValues := variableValues)
    (hruntime : runtimeType ∈ possibleTypes)
    : lawful.le
        (summarize algebra schema parentType inheritedBooleanCondition tree
          possibleTypes runtimeType variableValues fixedVariableValues)
        (CaseForest.summarize algebra schema parentType
          inheritedBooleanCondition tree possibleTypes variableValues
          fixedVariableValues) := by
  rw [RuntimeCase.summarize, CaseForest.summarize]
  split <;> rename_i hbranches
  · let region :=
      chooseTypeRegion runtimeType possibleTypes (tree.typeRegions possibleTypes)
    have hregion := chooseTypeRegion_mem tree possibleTypes runtimeType hruntime
    apply lawful.le_trans _
      (CaseForest.summarize algebra schema parentType
        (extendBooleanCondition inheritedBooleanCondition tree.booleanVariables
          variableValues)
        (tree.resolveBranches region variableValues) region variableValues
        fixedVariableValues)
    · exact summarize_le algebra lawful schema parentType
        (extendBooleanCondition inheritedBooleanCondition tree.booleanVariables
          variableValues)
        (tree.resolveBranches region variableValues) region runtimeType
        variableValues fixedVariableValues hregion.2
    · unfold CaseForest.summarizeTypeRegions
      exact lawful.le_joinMap_of_mem
        (fun selected _hselected =>
          CaseForest.summarize algebra schema parentType
            (extendBooleanCondition inheritedBooleanCondition tree.booleanVariables
              variableValues)
            (tree.resolveBranches selected variableValues) selected variableValues
            fixedVariableValues)
        hregion.1
  · exact lawful.le_refl _
termination_by
  (caseForestResponseDepth tree, caseForestUnresolvedCount tree, 3, 0)
decreasing_by
  apply quadruple_lt_of_depth_le_of_control_lt
  · exact resolveBranches_responseDepth_le region variableValues tree
  · apply resolveBranches_unresolvedCount_lt
    assumption

end RuntimeCase
end ExactCases
end TreeSummary
end GraphQL
