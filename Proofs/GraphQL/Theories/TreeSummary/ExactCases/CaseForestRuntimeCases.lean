import GraphQL.Theories.TreeSummary.ExactCases
import Proofs.GraphQL.Theories.ConditionTree.Extraction
import Proofs.GraphQL.Theories.ConditionTree.Reduce.RuntimeBundles
import Proofs.GraphQL.Theories.ConditionTree.RuntimeExtraction
import Proofs.GraphQL.Theories.TreeSummary.Algebra
import Proofs.GraphQL.Theories.TreeSummary.ExactCases.CaseForestTrace
import Proofs.GraphQL.Theories.TreeSummary.PossibleTypeRegions

/-! Proof-only deterministic runtime paths through the exact-case forest. -/

namespace GraphQL
namespace TreeSummary
namespace ExactCases

open GraphQL.ConditionTree
open GraphQL.ConditionTree.Termination
open GraphQL.Execution
open _root_.GraphQL.TreeSummary.Measure
open _root_.GraphQL.TreeSummary.ExactCases.Measure

theorem CaseForest.typeRegions_uniform (forest : CaseForest) (scope : PossibleTypes)
    (region : PossibleTypeRegion) (hregion : region ∈ forest.typeRegions scope)
    (left : Name) (hleft : left ∈ region) (right : Name) (hright : right ∈ region)
    (allowed : PossibleTypes) (hallowed : allowed ∈ forest.typeBranchPossibleTypes)
    : allowed.contains left = allowed.contains right := by
  exact (possibleTypeRegions_exact scope forest.typeBranchPossibleTypes).2.2
    region hregion left hleft right hright allowed hallowed

namespace CaseForestRuntimeCase

section Interpreter

def chooseTypeRegion (runtimeType : Name) (fallback : PossibleTypeRegion)
    : List PossibleTypeRegion -> PossibleTypeRegion
  | [] => fallback
  | region :: rest =>
      if region.contains runtimeType then
        region
      else
        chooseTypeRegion runtimeType fallback rest

theorem chooseTypeRegion_eq_scope_of_no_typeBranches
    (tree : CaseForest) (scope : PossibleTypeRegion) (runtimeType : Name)
    (htypes : tree.typeBranchPossibleTypes = [])
    : chooseTypeRegion runtimeType scope (tree.typeRegions scope) = scope := by
  by_cases hscope : scope = []
  · simp [CaseForest.typeRegions, htypes, possibleTypeRegions, hscope,
      chooseTypeRegion]
  · simp [CaseForest.typeRegions, htypes, possibleTypeRegions, hscope,
      chooseTypeRegion]

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
      (CaseForest.extendBooleanCondition inheritedBooleanCondition tree.booleanVariables
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
      (CaseForest.extendBooleanCondition inheritedBooleanCondition tree.booleanVariables
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
          simp only [List.filterMap_cons, hallows, Bool.false_eq_true, if_false,
            runtimeFieldsForEntries, List.flatMap_cons, List.nil_append]
          change (rest.filterMap fun entry =>
              if entry.1.allows variableValues runtimeType = true then
                some entry.2 else none).map
                (fun field => (field.responseName,
                  namedFieldToExecutable field))
            = runtimeFieldsForEntries variableValues runtimeType rest
          exact ih
      | true =>
          simp only [List.filterMap_cons, hallows, if_true, List.map_cons,
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
    parentType runtimeType inheritedBooleanCondition hinherited hcoherent
  rw [Tree.runtimeReductionBundles, if_neg (by simpa using hcondition),
    RuntimeFieldBundle.allSourceEntries] at hsource
  have hexecutable : tree.collectRuntimeFields variableValues runtimeType = [] := by
    simpa [RuntimeFieldBundle.allSourceEntries] using hsource.symm
  have hmapped := runtimeNamedFields_map runtimeType variableValues tree
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
  have huniform := tree.typeRegions_uniform scope region hregion runtimeType hruntime
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
  have huniform := tree.typeRegions_uniform scope region hregion runtimeType hruntime
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
  have hexact := possibleTypeRegions_exact scope tree.typeBranchPossibleTypes
  rcases hexact.2.1 runtimeType hruntime with ⟨region, hregion, _hunique⟩
  exact chooseTypeRegion_mem_of_exists runtimeType scope
    (possibleTypeRegions scope tree.typeBranchPossibleTypes)
    ⟨region, hregion.1, hregion.2⟩

theorem chooseTypeRegion_eq_membershipClass
    (tree : CaseForest) (scope : PossibleTypeRegion)
    (runtimeType : Name) (hruntime : runtimeType ∈ scope)
    : chooseTypeRegion runtimeType scope (tree.typeRegions scope)
      = possibleTypeMembershipClass scope tree.typeBranchPossibleTypes runtimeType := by
  have hchosen := chooseTypeRegion_mem tree scope runtimeType hruntime
  unfold CaseForest.typeRegions at hchosen ⊢
  exact possibleTypeRegions_membershipClass scope tree.typeBranchPossibleTypes
    _ hchosen.1 runtimeType hchosen.2

theorem chooseTypeRegion_eq_of_mem
    (tree : CaseForest) (scope : PossibleTypeRegion)
    (runtimeType : Name) (hruntime : runtimeType ∈ scope)
    (region : PossibleTypeRegion) (hregion : region ∈ tree.typeRegions scope)
    (hregionRuntime : runtimeType ∈ region)
    : chooseTypeRegion runtimeType scope (tree.typeRegions scope) = region := by
  have hchosen := chooseTypeRegion_mem tree scope runtimeType hruntime
  unfold CaseForest.typeRegions at hchosen hregion ⊢
  have hchosenClass := possibleTypeRegions_membershipClass scope
    tree.typeBranchPossibleTypes _ hchosen.1 runtimeType hchosen.2
  have hregionClass := possibleTypeRegions_membershipClass scope
    tree.typeBranchPossibleTypes region hregion runtimeType hregionRuntime
  exact hchosenClass.trans hregionClass.symm

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
  rw [resolve.eq_1]
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
      (CaseForest.extendBooleanCondition currentInheritedBooleanCondition
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
        (variableNames.map
          fun variableName =>
            if CaseForest.booleanValue variableValues variableName then
              .positive variableName
            else
              .negative variableName)
      = true := by
  induction variableNames with
  | nil => rfl
  | cons variableName rest ih =>
      cases hvalue : inputValueBoolean? variableValues (.variable variableName) with
      | none =>
          simpa [CaseForest.booleanValue, hvalue, booleanConditionAllows,
            BooleanLiteral.allows, BooleanLiteral.toDirective,
            directiveAllowsSelectionBool] using ih
      | some value =>
          cases value <;>
            simpa [CaseForest.booleanValue, hvalue, booleanConditionAllows,
              BooleanLiteral.allows,
              BooleanLiteral.toDirective, directiveAllowsSelectionBool] using ih

private theorem extendBooleanCondition_allows
    (inheritedBooleanCondition : List BooleanLiteral)
    (variableNames : BooleanVariableNames) (variableValues : VariableValues)
    (hinherited : booleanConditionAllows variableValues inheritedBooleanCondition = true)
    : booleanConditionAllows variableValues
        (CaseForest.extendBooleanCondition inheritedBooleanCondition variableNames
          variableValues)
      = true := by
  unfold CaseForest.extendBooleanCondition Internal.extendBooleanCondition
  dsimp only
  have hsource :
      booleanConditionAllows variableValues
          (inheritedBooleanCondition
            ++ variableNames.map fun variableName =>
              if CaseForest.booleanValue variableValues variableName then
                .positive variableName
              else
                .negative variableName)
        = true := by
    rw [booleanConditionAllows_append, hinherited,
      generatedBooleanCondition_allows, Bool.true_and]
  cases hcanonical
        : canonicalBooleanCondition
            (inheritedBooleanCondition
              ++ variableNames.map
                  fun variableName =>
                    if CaseForest.booleanValue variableValues variableName then
                      .positive variableName
                    else
                      .negative variableName) with
  | none =>
      simpa only [Option.getD_none] using hinherited
  | some candidate =>
      simp only [Option.getD_some]
      rw [← canonicalBooleanCondition_some_allows variableValues _ _ hcanonical]
      exact hsource

private theorem canonicalBooleanCondition_exists_of_allows
    (variableValues : VariableValues) (source : List BooleanLiteral)
    (hallows : booleanConditionAllows variableValues source = true)
    : ∃ target, canonicalBooleanCondition source = some target := by
  cases hcanonical : canonicalBooleanCondition source with
  | none =>
      have hfalse := canonicalBooleanCondition_none_not_allows variableValues source
        hcanonical
      rw [hallows] at hfalse
      contradiction
  | some target => exact ⟨target, rfl⟩

theorem internalExtend_allows
    (variableValues : VariableValues)
    (inherited additions : List BooleanLiteral)
    (hinherited : booleanConditionAllows variableValues inherited = true)
    (hadditions : booleanConditionAllows variableValues additions = true)
    : booleanConditionAllows variableValues
        (Internal.extendBooleanCondition inherited additions)
      = true := by
  have hsource : booleanConditionAllows variableValues (inherited ++ additions) = true := by
    rw [booleanConditionAllows_append, hinherited, hadditions, Bool.true_and]
  obtain ⟨target, hcanonical⟩ :=
    canonicalBooleanCondition_exists_of_allows variableValues
      (inherited ++ additions) hsource
  unfold Internal.extendBooleanCondition
  rw [hcanonical]
  simp only [Option.getD_some]
  rw [← canonicalBooleanCondition_some_allows variableValues _ _ hcanonical]
  exact hsource

theorem internalExtend_append
    (variableValues : VariableValues)
    (inherited left right : List BooleanLiteral)
    (hinherited : booleanConditionAllows variableValues inherited = true)
    (hleft : booleanConditionAllows variableValues left = true)
    (hright : booleanConditionAllows variableValues right = true)
    : Internal.extendBooleanCondition
        (Internal.extendBooleanCondition inherited left) right
      = Internal.extendBooleanCondition inherited (left ++ right) := by
  have hsourceLeft :
      booleanConditionAllows variableValues (inherited ++ left) = true := by
    rw [booleanConditionAllows_append, hinherited, hleft, Bool.true_and]
  obtain ⟨leftCanonical, hleftCanonical⟩ :=
    canonicalBooleanCondition_exists_of_allows variableValues
      (inherited ++ left) hsourceLeft
  have hextendLeft :
      Internal.extendBooleanCondition inherited left = leftCanonical := by
    unfold Internal.extendBooleanCondition
    rw [hleftCanonical]
    rfl
  have hleftCanonicalAllows :
      booleanConditionAllows variableValues leftCanonical = true := by
    rw [← canonicalBooleanCondition_some_allows variableValues _ _ hleftCanonical]
    exact hsourceLeft
  have hsourceSequential :
      booleanConditionAllows variableValues (leftCanonical ++ right) = true := by
    rw [booleanConditionAllows_append, hleftCanonicalAllows, hright,
      Bool.true_and]
  have hsourceCombined :
      booleanConditionAllows variableValues (inherited ++ (left ++ right)) = true := by
    rw [booleanConditionAllows_append, hinherited,
      booleanConditionAllows_append, hleft, hright, Bool.true_and]
    rfl
  obtain ⟨sequentialCanonical, hsequentialCanonical⟩ :=
    canonicalBooleanCondition_exists_of_allows variableValues
      (leftCanonical ++ right) hsourceSequential
  obtain ⟨combinedCanonical, hcombinedCanonical⟩ :=
    canonicalBooleanCondition_exists_of_allows variableValues
      (inherited ++ (left ++ right)) hsourceCombined
  have hcanonicalEq : sequentialCanonical = combinedCanonical :=
    SelectionConditions.canonicalBooleanCondition_eq_of_mem_iff hsequentialCanonical
      hcombinedCanonical fun literal => by
        simpa only [List.mem_append,
          SelectionConditions.canonicalBooleanCondition_mem_iff
            hleftCanonical literal] using
          (or_assoc :
            ((literal ∈ inherited ∨ literal ∈ left) ∨ literal ∈ right) ↔
              literal ∈ inherited ∨ (literal ∈ left ∨ literal ∈ right))
  rw [hextendLeft]
  unfold Internal.extendBooleanCondition
  rw [hsequentialCanonical, hcombinedCanonical]
  simp only [Option.getD_some]
  exact hcanonicalEq

private theorem internalExtend_eq_of_mem_iff
    (variableValues : VariableValues)
    (inherited left right : List BooleanLiteral)
    (hinherited : booleanConditionAllows variableValues inherited = true)
    (hleft : booleanConditionAllows variableValues left = true)
    (hright : booleanConditionAllows variableValues right = true)
    (hmembership : ∀ literal, literal ∈ left ↔ literal ∈ right)
    : Internal.extendBooleanCondition inherited left
      = Internal.extendBooleanCondition inherited right := by
  have hsourceLeft : booleanConditionAllows variableValues (inherited ++ left) = true := by
    rw [booleanConditionAllows_append, hinherited, hleft, Bool.true_and]
  have hsourceRight : booleanConditionAllows variableValues (inherited ++ right) = true := by
    rw [booleanConditionAllows_append, hinherited, hright, Bool.true_and]
  obtain ⟨leftCanonical, hleftCanonical⟩ :=
    canonicalBooleanCondition_exists_of_allows variableValues
      (inherited ++ left) hsourceLeft
  obtain ⟨rightCanonical, hrightCanonical⟩ :=
    canonicalBooleanCondition_exists_of_allows variableValues
      (inherited ++ right) hsourceRight
  have hcanonicalEq : leftCanonical = rightCanonical :=
    SelectionConditions.canonicalBooleanCondition_eq_of_mem_iff hleftCanonical
      hrightCanonical fun literal => by
        simp only [List.mem_append]
        rw [hmembership literal]
  unfold Internal.extendBooleanCondition
  rw [hleftCanonical, hrightCanonical]
  simpa only [Option.getD_some]

theorem booleanConditionAllows_reverse
    (variableValues : VariableValues) (condition : List BooleanLiteral)
    : booleanConditionAllows variableValues condition.reverse
      = booleanConditionAllows variableValues condition := by
  induction condition with
  | nil => rfl
  | cons literal rest ih =>
      rw [List.reverse_cons, booleanConditionAllows_append, ih]
      simp [booleanConditionAllows, Bool.and_comm]

private theorem resolve_trace
    (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
    (tree : CaseForest) (possibleTypes : PossibleTypeRegion)
    (runtimeType : Name) (variableValues : VariableValues)
    (hnormalized
      : Internal.extendBooleanCondition inheritedBooleanCondition []
        = inheritedBooleanCondition)
    (hinherited : booleanConditionAllows variableValues inheritedBooleanCondition = true)
    (hruntime : runtimeType ∈ possibleTypes)
    : let trace := CaseTrace.ofForest variableValues runtimeType tree
      let resolved :=
        resolve parentType inheritedBooleanCondition tree possibleTypes runtimeType
          variableValues
      resolved.tree.namedFields = trace.namedFields
      ∧ resolved.possibleTypes
        = possibleTypeMembershipClass possibleTypes trace.typeConditions runtimeType
      ∧ resolved.inheritedBooleanCondition
        = CaseTrace.inheritedBooleanCondition inheritedBooleanCondition trace := by
  rw [resolve.eq_1]
  split <;> rename_i hbranches
  · let region :=
      chooseTypeRegion runtimeType possibleTypes (tree.typeRegions possibleTypes)
    have hregion := chooseTypeRegion_mem tree possibleTypes runtimeType hruntime
    have hregionEq := chooseTypeRegion_eq_membershipClass tree possibleTypes
      runtimeType hruntime
    let nextTree := tree.resolveBranches region variableValues
    let frontier := tree.booleanVariables.map
      (CaseTrace.selectedLiteral variableValues)
    have hfrontierAllows :
        booleanConditionAllows variableValues frontier = true := by
      change booleanConditionAllows variableValues
          (tree.booleanVariables.map fun variableName =>
            if CaseForest.booleanValue variableValues variableName then
              .positive variableName
            else
              .negative variableName) = true
      exact generatedBooleanCondition_allows tree.booleanVariables variableValues
    have hnextInherited :
        CaseForest.extendBooleanCondition inheritedBooleanCondition
            tree.booleanVariables variableValues =
          Internal.extendBooleanCondition inheritedBooleanCondition frontier := by
      rfl
    have hnextAllows := extendBooleanCondition_allows inheritedBooleanCondition
      tree.booleanVariables variableValues hinherited
    have hnextNormalized :
        Internal.extendBooleanCondition
            (CaseForest.extendBooleanCondition inheritedBooleanCondition
              tree.booleanVariables variableValues) [] =
          CaseForest.extendBooleanCondition inheritedBooleanCondition
            tree.booleanVariables variableValues := by
      rw [hnextInherited,
        internalExtend_append variableValues inheritedBooleanCondition frontier []
          hinherited hfrontierAllows (by rfl)]
      simp
    have ih := resolve_trace parentType
      (CaseForest.extendBooleanCondition inheritedBooleanCondition
        tree.booleanVariables variableValues)
      nextTree region runtimeType variableValues hnextNormalized hnextAllows hregion.2
    have hnamed := CaseTrace.resolveBranches_namedFields tree possibleTypes region
      hregion.1 runtimeType hregion.2 variableValues
    have htypes := CaseTrace.resolveBranches_typeConditions tree possibleTypes region
      hregion.1 runtimeType hregion.2 variableValues
    have hbooleans := CaseTrace.resolveBranches_booleanLiterals tree possibleTypes region
      hregion.1 runtimeType hregion.2 variableValues
    dsimp only [nextTree, region] at ih hnamed htypes hbooleans hregionEq hregion
    rw [hregionEq] at htypes
    constructor
    · exact ih.1.trans hnamed.symm
    · constructor
      · rw [ih.2.1, hregionEq,
          possibleTypeMembershipClass_append]
        apply possibleTypeMembershipClass_perm
        rw [CaseTrace.frontierTypeConditions_eq] at htypes
        exact htypes.symm
      · rw [ih.2.2, hnextInherited]
        unfold CaseTrace.inheritedBooleanCondition
        let nextTrace := CaseTrace.ofForest variableValues runtimeType
          (tree.resolveBranches
            (chooseTypeRegion runtimeType possibleTypes (tree.typeRegions possibleTypes))
            variableValues)
        have hnextTraceAllows :
            booleanConditionAllows variableValues nextTrace.booleanLiterals.reverse = true := by
          rw [booleanConditionAllows_reverse]
          exact CaseTrace.ofForest_booleanLiterals_allow variableValues runtimeType _
        rw [internalExtend_append variableValues inheritedBooleanCondition frontier
          nextTrace.booleanLiterals.reverse hinherited hfrontierAllows hnextTraceAllows]
        apply internalExtend_eq_of_mem_iff variableValues inheritedBooleanCondition
          (frontier ++ nextTrace.booleanLiterals.reverse)
          (CaseTrace.ofForest variableValues runtimeType tree).booleanLiterals.reverse
          hinherited
        · rw [booleanConditionAllows_append, hfrontierAllows, hnextTraceAllows]
          rfl
        · rw [booleanConditionAllows_reverse]
          exact CaseTrace.ofForest_booleanLiterals_allow variableValues runtimeType tree
        · intro literal
          rw [List.mem_append, List.mem_reverse, List.mem_reverse]
          have hfrontierMem :=
            (CaseTrace.frontierBooleanLiterals_mem_iff variableValues tree literal).symm
          change literal ∈ tree.booleanVariables.map
                (CaseTrace.selectedLiteral variableValues) ∨
              literal ∈ nextTrace.booleanLiterals ↔
            literal ∈ (CaseTrace.ofForest variableValues runtimeType tree).booleanLiterals
          rw [hfrontierMem]
          have hperm :
              literal ∈ (CaseTrace.ofForest variableValues runtimeType tree).booleanLiterals ↔
                literal ∈ CaseTrace.frontierBooleanLiterals variableValues
                    tree.branches ++ nextTrace.booleanLiterals :=
            hbooleans.mem_iff
          simp only [List.mem_append] at hperm
          constructor
          · rintro (hfrontier | hnext)
            · exact (hperm).mpr (Or.inl hfrontier)
            · exact (hperm).mpr (Or.inr hnext)
          · intro horiginal
            rcases (hperm).mp horiginal with hfrontier | hnext
            · exact Or.inl hfrontier
            · exact Or.inr hnext
  · have hfalse : tree.hasUnresolvedBranches = false := by
      cases hvalue : tree.hasUnresolvedBranches with
      | false => rfl
      | true => exact (hbranches hvalue).elim
    have htrace := CaseTrace.ofForest_branchless variableValues runtimeType tree hfalse
    constructor
    · exact htrace.1.symm
    · constructor
      · rw [htrace.2.1]
        unfold possibleTypeMembershipClass
        symm
        exact List.filter_eq_self.mpr fun _ _ => by simp
      · unfold CaseTrace.inheritedBooleanCondition
        rw [htrace.2.2]
        simpa using hnormalized.symm
termination_by
  (caseForestResponseDepth tree, caseForestUnresolvedCount tree, 3, 0)
decreasing_by
  apply quadruple_lt_of_depth_le_of_control_lt
  · exact resolveBranches_responseDepth_le region variableValues tree
  · exact resolveBranches_unresolvedCount_lt region variableValues tree (by assumption)

theorem fieldGroups_eq_trace
    (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
    (tree : CaseForest) (possibleTypes : PossibleTypeRegion)
    (runtimeType : Name) (variableValues : VariableValues)
    (hnormalized
      : Internal.extendBooleanCondition inheritedBooleanCondition []
        = inheritedBooleanCondition)
    (hinherited : booleanConditionAllows variableValues inheritedBooleanCondition = true)
    (hruntime : runtimeType ∈ possibleTypes)
    : fieldGroups parentType inheritedBooleanCondition tree possibleTypes runtimeType
        variableValues
      = CaseTrace.fieldGroups inheritedBooleanCondition possibleTypes runtimeType
          (CaseTrace.ofForest variableValues runtimeType tree) := by
  have htrace := resolve_trace parentType inheritedBooleanCondition tree possibleTypes
    runtimeType variableValues hnormalized hinherited hruntime
  unfold fieldGroups CaseTrace.fieldGroups CaseTrace.inheritedBooleanCondition
    CaseTrace.possibleTypes CaseForest.fieldGroups
  dsimp only
  rw [htrace.1, htrace.2.1, htrace.2.2]
  rfl

private theorem resolve_trace_of_typeFree
    (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
    (tree : CaseForest) (possibleTypes : PossibleTypeRegion)
    (runtimeType : Name) (variableValues : VariableValues)
    (hnormalized
      : Internal.extendBooleanCondition inheritedBooleanCondition []
        = inheritedBooleanCondition)
    (hinherited : booleanConditionAllows variableValues inheritedBooleanCondition = true)
    (htypes : (CaseTrace.ofForest variableValues runtimeType tree).typeConditions = [])
    : let trace := CaseTrace.ofForest variableValues runtimeType tree
      let resolved :=
        resolve parentType inheritedBooleanCondition tree possibleTypes runtimeType
          variableValues
      resolved.tree.namedFields = trace.namedFields
      ∧ resolved.possibleTypes = possibleTypes
      ∧ resolved.inheritedBooleanCondition
        = CaseTrace.inheritedBooleanCondition inheritedBooleanCondition trace := by
  rw [resolve.eq_1]
  split <;> rename_i hbranches
  · have hstep := CaseTrace.resolveBranches_typeFree tree possibleTypes runtimeType
      variableValues htypes
    have hregionEq :
        chooseTypeRegion runtimeType possibleTypes (tree.typeRegions possibleTypes) =
          possibleTypes := by
      exact chooseTypeRegion_eq_scope_of_no_typeBranches tree possibleTypes runtimeType
        hstep.1
    let nextTree := tree.resolveBranches possibleTypes variableValues
    let frontier := tree.booleanVariables.map
      (CaseTrace.selectedLiteral variableValues)
    have hfrontierAllows :
        booleanConditionAllows variableValues frontier = true := by
      change booleanConditionAllows variableValues
          (tree.booleanVariables.map fun variableName =>
            if CaseForest.booleanValue variableValues variableName then
              .positive variableName
            else
              .negative variableName) = true
      exact generatedBooleanCondition_allows tree.booleanVariables variableValues
    have hnextInherited :
        CaseForest.extendBooleanCondition inheritedBooleanCondition
            tree.booleanVariables variableValues =
          Internal.extendBooleanCondition inheritedBooleanCondition frontier := by
      rfl
    have hnextAllows := extendBooleanCondition_allows inheritedBooleanCondition
      tree.booleanVariables variableValues hinherited
    have hnextNormalized :
        Internal.extendBooleanCondition
            (CaseForest.extendBooleanCondition inheritedBooleanCondition
              tree.booleanVariables variableValues) [] =
          CaseForest.extendBooleanCondition inheritedBooleanCondition
            tree.booleanVariables variableValues := by
      rw [hnextInherited,
        internalExtend_append variableValues inheritedBooleanCondition frontier []
          hinherited hfrontierAllows (by rfl)]
      simp
    have ih := resolve_trace_of_typeFree parentType
      (CaseForest.extendBooleanCondition inheritedBooleanCondition
        tree.booleanVariables variableValues)
      nextTree possibleTypes runtimeType variableValues hnextNormalized hnextAllows
      hstep.2.2.1
    rw [hregionEq]
    dsimp only [nextTree] at ih
    constructor
    · exact ih.1.trans hstep.2.1.symm
    · constructor
      · exact ih.2.1
      · rw [ih.2.2, hnextInherited]
        unfold CaseTrace.inheritedBooleanCondition
        let nextTrace := CaseTrace.ofForest variableValues runtimeType
          (tree.resolveBranches possibleTypes variableValues)
        have hnextTraceAllows :
            booleanConditionAllows variableValues nextTrace.booleanLiterals.reverse = true := by
          rw [booleanConditionAllows_reverse]
          exact CaseTrace.ofForest_booleanLiterals_allow variableValues runtimeType _
        rw [internalExtend_append variableValues inheritedBooleanCondition frontier
          nextTrace.booleanLiterals.reverse hinherited hfrontierAllows hnextTraceAllows]
        apply internalExtend_eq_of_mem_iff variableValues inheritedBooleanCondition
          (frontier ++ nextTrace.booleanLiterals.reverse)
          (CaseTrace.ofForest variableValues runtimeType tree).booleanLiterals.reverse
          hinherited
        · rw [booleanConditionAllows_append, hfrontierAllows, hnextTraceAllows]
          rfl
        · rw [booleanConditionAllows_reverse]
          exact CaseTrace.ofForest_booleanLiterals_allow variableValues runtimeType tree
        · intro literal
          rw [List.mem_append, List.mem_reverse, List.mem_reverse]
          have hfrontierMem :=
            (CaseTrace.frontierBooleanLiterals_mem_iff variableValues tree literal).symm
          change literal ∈ tree.booleanVariables.map
                (CaseTrace.selectedLiteral variableValues) ∨
              literal ∈ nextTrace.booleanLiterals ↔
            literal ∈ (CaseTrace.ofForest variableValues runtimeType tree).booleanLiterals
          rw [hfrontierMem]
          simpa only [List.mem_append] using hstep.2.2.2.mem_iff.symm
  · have hfalse : tree.hasUnresolvedBranches = false := by
      cases hvalue : tree.hasUnresolvedBranches with
      | false => rfl
      | true => exact (hbranches hvalue).elim
    have htrace := CaseTrace.ofForest_branchless variableValues runtimeType tree hfalse
    constructor
    · exact htrace.1.symm
    · constructor
      · rfl
      · unfold CaseTrace.inheritedBooleanCondition
        rw [htrace.2.2]
        simpa using hnormalized.symm
termination_by
  (caseForestResponseDepth tree, caseForestUnresolvedCount tree, 3, 0)
decreasing_by
  apply quadruple_lt_of_depth_le_of_control_lt
  · exact resolveBranches_responseDepth_le possibleTypes variableValues tree
  · exact resolveBranches_unresolvedCount_lt possibleTypes variableValues tree
      (by assumption)

theorem fieldGroups_eq_trace_of_typeFree
    (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
    (tree : CaseForest) (possibleTypes : PossibleTypeRegion)
    (runtimeType : Name) (variableValues : VariableValues)
    (hnormalized
      : Internal.extendBooleanCondition inheritedBooleanCondition []
        = inheritedBooleanCondition)
    (hinherited : booleanConditionAllows variableValues inheritedBooleanCondition = true)
    (htypes : (CaseTrace.ofForest variableValues runtimeType tree).typeConditions = [])
    : fieldGroups parentType inheritedBooleanCondition tree possibleTypes runtimeType
        variableValues
      = CaseTrace.fieldGroups inheritedBooleanCondition possibleTypes runtimeType
          (CaseTrace.ofForest variableValues runtimeType tree) := by
  have htrace := resolve_trace_of_typeFree parentType inheritedBooleanCondition tree
    possibleTypes runtimeType variableValues hnormalized hinherited htypes
  unfold fieldGroups CaseTrace.fieldGroups CaseTrace.inheritedBooleanCondition
    CaseTrace.possibleTypes CaseForest.fieldGroups
  dsimp only
  rw [htrace.1, htrace.2.1, htrace.2.2]
  rw [htypes]
  unfold possibleTypeMembershipClass
  rw [List.filter_eq_self.mpr (fun _ _ => by simp)]
  rfl

private theorem localNamedFieldGroups_responseDepth
    (groups : List ConditionTree.FieldGroup)
    : Termination.selectionSetResponseDepth
        ((groups.flatMap
            fun group =>
              group.fields.map
                fun field => { responseName := group.responseName, field }).map
          NamedField.toSelection)
      = conditionFieldGroupsResponseDepth groups := by
  induction groups with
  | nil =>
      simp only [List.flatMap_nil, List.map_nil,
        Termination.selectionSetResponseDepth, conditionFieldGroupsResponseDepth]
  | cons group rest ih =>
      rw [List.flatMap_cons, List.map_append,
        Termination.selectionSetResponseDepth_append,
        conditionFieldGroupsResponseDepth]
      have hgroup :
          (group.fields.map
              fun field => { responseName := group.responseName, field }).map
              NamedField.toSelection = group.selections := by
        simp [FieldGroup.selections, FieldGroup.fields, Field.toSelection,
          NamedField.toSelection]
      rw [hgroup, conditionFieldGroupResponseDepth, ih]

private theorem activeTreesNamedFields_responseDepth_le (trees : List Tree)
    : Termination.selectionSetResponseDepth
        ((trees.flatMap
            fun tree =>
              tree.fields.flatMap
                fun group =>
                  group.fields.map
                    fun field =>
                      { responseName := group.responseName, field }).map
          NamedField.toSelection)
      ≤ activeTreesResponseDepth trees := by
  induction trees with
  | nil => simp [activeTreesResponseDepth, Termination.selectionSetResponseDepth]
  | cons tree rest ih =>
      rw [List.flatMap_cons, List.map_append,
        Termination.selectionSetResponseDepth_append,
        activeTreesResponseDepth, localNamedFieldGroups_responseDepth tree.fields]
      simp only [conditionTreeResponseDepth]
      exact Nat.max_le.mpr
        ⟨Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _),
          Nat.le_trans ih (Nat.le_max_right _ _)⟩

private theorem forestFieldGroups_responseDepth_le
    (inheritedBooleanCondition : List BooleanLiteral)
    (possibleTypes : PossibleTypeRegion) (tree : CaseForest)
    : collectedFieldGroupsResponseDepth
        (tree.fieldGroups inheritedBooleanCondition possibleTypes)
      ≤ caseForestResponseDepth tree := by
  rw [CaseForest.fieldGroups,
    collectedFieldGroupsResponseDepth_fieldGroupsWithContext]
  exact Nat.le_trans
    (conditionFieldGroupsResponseDepth_collectFieldGroups tree.namedFields)
    (activeTreesNamedFields_responseDepth_le tree.activeTrees)

private theorem resolve_responseDepth_le
    (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
    (tree : CaseForest) (possibleTypes : PossibleTypeRegion)
    (runtimeType : Name) (variableValues : VariableValues)
    : caseForestResponseDepth
        (resolve parentType inheritedBooleanCondition tree possibleTypes runtimeType
          variableValues).tree
      ≤ caseForestResponseDepth tree := by
  rw [resolve.eq_1]
  split <;> rename_i hbranches
  · let region :=
      chooseTypeRegion runtimeType possibleTypes (tree.typeRegions possibleTypes)
    have ih := resolve_responseDepth_le parentType
      (CaseForest.extendBooleanCondition inheritedBooleanCondition tree.booleanVariables
        variableValues)
      (tree.resolveBranches region variableValues) region runtimeType variableValues
    exact Nat.le_trans ih (resolveBranches_responseDepth_le region variableValues tree)
  · exact Nat.le_refl _
termination_by
  (caseForestResponseDepth tree, caseForestUnresolvedCount tree, 3, 0)
decreasing_by
  apply quadruple_lt_of_depth_le_of_control_lt
  · exact resolveBranches_responseDepth_le region variableValues tree
  · exact resolveBranches_unresolvedCount_lt region variableValues tree (by assumption)

theorem fieldGroups_responseDepth_le
    (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
    (tree : CaseForest) (possibleTypes : PossibleTypeRegion)
    (runtimeType : Name) (variableValues : VariableValues)
    : collectedFieldGroupsResponseDepth
        (fieldGroups parentType inheritedBooleanCondition tree possibleTypes runtimeType
          variableValues)
      ≤ caseForestResponseDepth tree := by
  unfold fieldGroups
  dsimp only
  exact Nat.le_trans
    (forestFieldGroups_responseDepth_le
      (resolve parentType inheritedBooleanCondition tree possibleTypes runtimeType
        variableValues).inheritedBooleanCondition
      (resolve parentType inheritedBooleanCondition tree possibleTypes runtimeType
        variableValues).possibleTypes
      (resolve parentType inheritedBooleanCondition tree possibleTypes runtimeType
        variableValues).tree)
    (resolve_responseDepth_le parentType inheritedBooleanCondition tree possibleTypes
      runtimeType variableValues)

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
    rw [resolve.eq_1]
    split <;> rename_i hbranches
    · have hregion := chooseTypeRegion_mem tree possibleTypes runtimeType hruntime
      exact resolve_conditions parentType
        (CaseForest.extendBooleanCondition inheritedBooleanCondition tree.booleanVariables
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
    (schema : Schema) (parentType : Name)
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
        CollectedFieldGroup.toExecutableGroup
      = groupExecutableFields
          ((tree.activeTrees.flatMap (runtimeNamedFields variableValues runtimeType)).map
            fun field => (field.responseName, namedFieldToExecutable field)) := by
  let resolved := resolve parentType currentInheritedBooleanCondition tree possibleTypes
    runtimeType variableValues
  have hnames := resolve_namedFields schema parentType fixedInheritedBooleanCondition
    currentInheritedBooleanCondition tree possibleTypes runtimeType variableValues
    hinherited hvalid hruntime
  change (TreeSummary.fieldGroupsWithContext resolved.inheritedBooleanCondition
            { possibleTypes := resolved.possibleTypes, booleanCondition := [] }
            (ConditionTree.collectFieldGroups resolved.tree.namedFields)).map
            CollectedFieldGroup.toExecutableGroup
          = _
  rw [toExecutableGroup_collectFieldGroups,
    fieldGroupToExecutableGroup_collectFieldGroups]
  rw [hnames]

theorem fieldGroupsToExecutable_eq_collectRuntimeFieldGroups
    (schema : Schema) (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral) (tree : Tree)
    (runtimeType : Name) (variableValues : VariableValues)
    (hinherited : booleanConditionAllows variableValues inheritedBooleanCondition = true)
    (hcondition : tree.condition.allows variableValues runtimeType = true)
    (hcoherent : tree.BranchesCoherent schema inheritedBooleanCondition)
    (hruntime : runtimeType ∈ tree.condition.possibleTypes)
    : (fieldGroups parentType inheritedBooleanCondition (.ofConditionTree tree)
        tree.condition.possibleTypes runtimeType variableValues).map
        CollectedFieldGroup.toExecutableGroup
      = tree.collectRuntimeFieldGroups variableValues runtimeType := by
  have hvalid :
      ActiveTreesValid schema inheritedBooleanCondition variableValues runtimeType
        (CaseForest.ofConditionTree tree).activeTrees := by
    intro item hitem
    simp only [CaseForest.ofConditionTree, List.mem_singleton] at hitem
    subst item
    exact ⟨hcondition, hcoherent⟩
  have hgroups := fieldGroupsToExecutable_eq schema parentType
    inheritedBooleanCondition inheritedBooleanCondition (.ofConditionTree tree)
    tree.condition.possibleTypes runtimeType variableValues hinherited hvalid hruntime
  simpa [CaseForest.ofConditionTree, Tree.collectRuntimeFieldGroups,
    runtimeNamedFields_map runtimeType variableValues tree] using
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
    rw [summarize.eq_1, fieldGroups, resolve.eq_1]
    split <;> rename_i hbranches
    · exact summarize_eq_resolved algebra schema parentType
        (CaseForest.extendBooleanCondition inheritedBooleanCondition tree.booleanVariables
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
        (CaseForest.summarize algebra schema
          inheritedBooleanCondition tree possibleTypes variableValues
          fixedVariableValues) := by
  rw [summarize.eq_1, CaseForest.summarize]
  split <;> rename_i hbranches
  · cases htypes : tree.typeBranchPossibleTypes.isEmpty with
    | true =>
        have hempty : tree.typeBranchPossibleTypes = [] := List.isEmpty_iff.mp htypes
        have hregionEq :
            chooseTypeRegion runtimeType possibleTypes (tree.typeRegions possibleTypes) =
              possibleTypes := by
          exact chooseTypeRegion_eq_scope_of_no_typeBranches tree possibleTypes runtimeType
            hempty
        simp only [if_true, hregionEq]
        exact summarize_le algebra lawful schema parentType
          (CaseForest.extendBooleanCondition inheritedBooleanCondition tree.booleanVariables
            variableValues)
          (tree.resolveBranches possibleTypes variableValues) possibleTypes runtimeType
          variableValues fixedVariableValues hruntime
    | false =>
        simp only [Bool.false_eq_true, if_false]
        let region :=
          chooseTypeRegion runtimeType possibleTypes (tree.typeRegions possibleTypes)
        have hregion := chooseTypeRegion_mem tree possibleTypes runtimeType hruntime
        apply lawful.le_trans _
          (CaseForest.summarize algebra schema
            (CaseForest.extendBooleanCondition inheritedBooleanCondition
              tree.booleanVariables variableValues)
            (tree.resolveBranches region variableValues) region variableValues
            fixedVariableValues)
        · exact summarize_le algebra lawful schema parentType
            (CaseForest.extendBooleanCondition inheritedBooleanCondition
              tree.booleanVariables variableValues)
            (tree.resolveBranches region variableValues) region runtimeType
            variableValues fixedVariableValues hregion.2
        · unfold CaseForest.summarizeTypeRegions
          exact lawful.le_joinMap_of_mem
            (fun selected _hselected =>
              CaseForest.summarize algebra schema
                (CaseForest.extendBooleanCondition inheritedBooleanCondition
                  tree.booleanVariables variableValues)
                (tree.resolveBranches selected variableValues) selected variableValues
                fixedVariableValues)
            hregion.1
  · exact lawful.le_refl _
termination_by
  (caseForestResponseDepth tree, caseForestUnresolvedCount tree, 3, 0)
decreasing_by
  all_goals
    apply quadruple_lt_of_depth_le_of_control_lt
    · exact resolveBranches_responseDepth_le _ variableValues tree
    · apply resolveBranches_unresolvedCount_lt
      assumption

end CaseForestRuntimeCase
end ExactCases
end TreeSummary
end GraphQL
