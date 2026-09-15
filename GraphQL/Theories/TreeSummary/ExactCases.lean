import GraphQL.Theories.TreeSummary.Soundness
import GraphQL.SchemaWellFormedness
import GraphQL.Validation

/-! Exact-case tree-summary traversal.

This backend enumerates every feasible combination of simultaneously active syntactic
condition subtrees before invoking field handlers. The condition cases are exact; the
analysis algebra may still intentionally approximate their summaries.
-/

namespace GraphQL
namespace TreeSummary

open GraphQL.ConditionTree
open GraphQL.ConditionTree.Termination
open GraphQL.Execution
open GraphQL.AnnotatedExecution
open Measure

universe u v

namespace ExactCases

-----------------------------------------------------------------------------------------
-- Exact-case condition helpers
-----------------------------------------------------------------------------------------

namespace Internal

def extendBooleanCondition (inheritedBooleanCondition caseCondition : List BooleanLiteral)
    : List BooleanLiteral :=
  (canonicalBooleanCondition (inheritedBooleanCondition ++ caseCondition)).getD
    inheritedBooleanCondition

end Internal

/-- Boolean control context shared by every selection-set scope in one exact case.
Symbolic contexts split absent Boolean values lazily. Concrete contexts instead use the
request's coerced values and resolve an absent Boolean as `false`. -/
inductive CaseCursor.BooleanEnvironment where
  | symbolic (caseValues : Execution.VariableValues)
  | concrete (variableValues : Execution.VariableValues)
deriving Repr

namespace CaseCursor.BooleanEnvironment

def variableValues : CaseCursor.BooleanEnvironment -> Execution.VariableValues
  | .symbolic values => values
  | .concrete values => values

/-- Immutable request knowledge used only by condition-tree extraction. Case splitting
extends `variableValues`, but those speculative assignments must not prune syntax. -/
def pruningValues : CaseCursor.BooleanEnvironment -> Execution.VariableValues
  | .symbolic _caseValues => []
  | .concrete values => values

/-- Variable-independent request context. Every Boolean is unresolved until traversal
reaches its first literal. -/
def unresolved : CaseCursor.BooleanEnvironment :=
  .symbolic []

/-- Records one symbolic case choice; concrete request contexts remain immutable. -/
def assign (environment : CaseCursor.BooleanEnvironment) (variableName : Name)
    (value : Bool)
    : CaseCursor.BooleanEnvironment :=
  match environment with
  | .symbolic values => .symbolic ((variableName, .boolean value) :: values)
  | .concrete values => .concrete values

/-- A supplied Boolean is known. An absent/non-Boolean symbolic value is unresolved,
while the same concrete request value selects the directive's false behavior. -/
def statusForVariable (environment : CaseCursor.BooleanEnvironment) (variableName : Name)
    : Option Bool :=
  match inputValueBoolean? environment.variableValues (.variable variableName) with
  | some value => some value
  | none =>
      match environment with
      | .symbolic _caseValues => none
      | .concrete _values => some false

end CaseCursor.BooleanEnvironment

namespace Internal

/-- A lazily constructed exact-case decision. Tests remain explicit across field and
sibling composition, so repeated uses of one operation variable stay correlated.
`join` preserves a factored type-case partition without forcing unrelated Boolean
supports from disjoint type regions into a Cartesian product. -/
inductive BooleanDecision (Summary : Type u) where
  | leaf (summary : Summary)
  | split (variableName : Name) (onFalse onTrue : BooleanDecision Summary)
  | join (left right : BooleanDecision Summary)
deriving Repr

namespace BooleanDecision

private def nodeCount : BooleanDecision α -> Nat
  | .leaf _summary => 1
  | .split _variableName onFalse onTrue =>
      1 + nodeCount onFalse + nodeCount onTrue
  | .join left right => 1 + nodeCount left + nodeCount right

def map (transform : α -> β) : BooleanDecision α -> BooleanDecision β
  | .leaf summary => .leaf (transform summary)
  | .split variableName onFalse onTrue =>
      .split variableName (map transform onFalse) (map transform onTrue)
  | .join left right => .join (map transform left) (map transform right)

/-- Cofactors a decision by one binary test result. Every later occurrence of the selected
test is removed, including occurrences below unrelated earlier tests. -/
def restrict (selectedVariable : Name) (selectedValue : Bool)
    : BooleanDecision α -> BooleanDecision α
  | .leaf summary => .leaf summary
  | .split variableName onFalse onTrue =>
      if variableName = selectedVariable then
        match selectedValue with
        | false => restrict selectedVariable false onFalse
        | true => restrict selectedVariable true onTrue
      else
        .split variableName
          (restrict selectedVariable selectedValue onFalse)
          (restrict selectedVariable selectedValue onTrue)
  | .join left right =>
      .join
        (restrict selectedVariable selectedValue left)
        (restrict selectedVariable selectedValue right)

private theorem nodeCount_restrict_le (selectedVariable : Name)
    (selectedValue : Bool)
    (decision : BooleanDecision α)
    : nodeCount (decision.restrict selectedVariable selectedValue)
      ≤ nodeCount decision := by
  induction decision with
  | leaf => simp [restrict, nodeCount]
  | split variableName onFalse onTrue ihFalse ihTrue =>
      simp only [restrict]
      split
      · cases selectedValue <;> simp_all [nodeCount] <;> omega
      · simp only [nodeCount]
        omega
  | join left right ihLeft ihRight =>
      simp only [restrict, nodeCount]
      omega

/-- Pointwise composition of two ordered decision trees. When one side does not yet
branch on the earlier variable, that side is shared by both alternatives. The same
variable is therefore aligned rather than expanded into incompatible cross-products. -/
def zipWith (variableOrder : BooleanVariableNames) (operation : α -> β -> γ)
    : BooleanDecision α -> BooleanDecision β -> BooleanDecision γ
  | .leaf left, right => right.map (operation left)
  | left, .leaf right => left.map fun value => operation value right
  | .join leftFirst leftSecond, right =>
      .join
        (zipWith variableOrder operation leftFirst right)
        (zipWith variableOrder operation leftSecond right)
  | left, .join rightFirst rightSecond =>
      .join
        (zipWith variableOrder operation left rightFirst)
        (zipWith variableOrder operation left rightSecond)
  | .split leftVariable leftFalse leftTrue,
    .split rightVariable rightFalse rightTrue =>
      if leftVariable = rightVariable then
        .split leftVariable
          (zipWith variableOrder operation leftFalse rightFalse)
          (zipWith variableOrder operation leftTrue rightTrue)
      else if variableOrder.idxOf leftVariable < variableOrder.idxOf rightVariable then
        .split leftVariable
          (zipWith variableOrder operation leftFalse
            ((BooleanDecision.split rightVariable rightFalse rightTrue).restrict
              leftVariable false))
          (zipWith variableOrder operation leftTrue
            ((BooleanDecision.split rightVariable rightFalse rightTrue).restrict
              leftVariable true))
      else
        .split rightVariable
          (zipWith variableOrder operation
            ((BooleanDecision.split leftVariable leftFalse leftTrue).restrict
              rightVariable false)
            rightFalse)
          (zipWith variableOrder operation
            ((BooleanDecision.split leftVariable leftFalse leftTrue).restrict
              rightVariable true)
            rightTrue)
termination_by left right => nodeCount left + nodeCount right
decreasing_by
  all_goals simp only [nodeCount]
  all_goals try omega
  all_goals
    have hrightFalse := nodeCount_restrict_le leftVariable false
      (.split rightVariable rightFalse rightTrue)
    have hrightTrue := nodeCount_restrict_le leftVariable true
      (.split rightVariable rightFalse rightTrue)
    have hleftFalse := nodeCount_restrict_le rightVariable false
      (.split leftVariable leftFalse leftTrue)
    have hleftTrue := nodeCount_restrict_le rightVariable true
      (.split leftVariable leftFalse leftTrue)
    simp only [nodeCount] at hrightFalse hrightTrue hleftFalse hleftTrue
    omega

def collapse (algebra : Algebra) : BooleanDecision algebra.Summary -> algebra.Summary
  | .leaf summary => summary
  | .split _variableName onFalse onTrue =>
      algebra.join (collapse algebra onFalse) (collapse algebra onTrue)
  | .join left right =>
      algebra.join (collapse algebra left) (collapse algebra right)

/-- A completed type alternative no longer needs a structural `join`. This smart
constructor retains factoring while either side still has Boolean/type decisions,
and otherwise combines the two finished summaries immediately. -/
def joinCases (join : α -> α -> α) (left right : BooleanDecision α) : BooleanDecision α :=
  match left, right with
  | .leaf leftSummary, .leaf rightSummary => .leaf (join leftSummary rightSummary)
  | left, right => .join left right

/-- Compacts only a finished selection-set boundary. All recursive `field` applications
have already happened, so this changes decision representation without asking
analyses to make `field` monotone. -/
def compact (join : α -> α -> α) : BooleanDecision α -> BooleanDecision α
  | .leaf summary => .leaf summary
  | .split variableName onFalse onTrue =>
      .split variableName (compact join onFalse) (compact join onTrue)
  | .join left right =>
      joinCases join (compact join left) (compact join right)

def combineMap (algebra : Algebra) (variableOrder : BooleanVariableNames)
    (items : List α)
    (summarize : ∀ item, item ∈ items -> BooleanDecision algebra.Summary)
    : BooleanDecision algebra.Summary :=
  match items with
  | [] => .leaf algebra.empty
  | item :: rest =>
      zipWith variableOrder algebra.combine
        (summarize item (by simp))
        (combineMap algebra variableOrder rest
          fun candidate hcandidate => summarize candidate (by simp [hcandidate]))
termination_by items

def joinMap (algebra : Algebra) (items : List α)
    (summarize : ∀ item, item ∈ items -> BooleanDecision algebra.Summary)
    : BooleanDecision algebra.Summary :=
  match items with
  | [] => .leaf algebra.empty
  | item :: [] => summarize item (by simp)
  | item :: next :: rest =>
      .join
        (summarize item (by simp))
        (joinMap algebra (next :: rest)
          fun candidate hcandidate => summarize candidate (by simp [hcandidate]))
termination_by items

end BooleanDecision

end Internal

-----------------------------------------------------------------------------------------
-- Incremental branch-local scheduler
-----------------------------------------------------------------------------------------

/-- One selection-set boundary under construction. Activated fields are stored as
newest-first chunks, so selecting a deeply nested path never copies the accumulated
prefix. `pendingBranches` is a preorder work list: selecting its head schedules that
branch body's children before later siblings. -/
structure CaseCursor where
  namedFieldChunksRev : List (List NamedField)
  pendingBranches : List (Branch Tree)
deriving Repr

namespace CaseCursor

def localNamedFields (tree : Tree) : List NamedField :=
  tree.fields.flatMap
    fun group =>
      group.fields.map fun field => { responseName := group.responseName, field }

/-- Logical source-order view materialized only when a completed case needs grouping. -/
def namedFields (cursor : CaseCursor) : List NamedField :=
  cursor.namedFieldChunksRev.reverse.flatten

def ofConditionTree (tree : Tree) : CaseCursor :=
  { namedFieldChunksRev := [localNamedFields tree], pendingBranches := tree.branches }

/-- Rejects the current branch and continues with its siblings. -/
def skipBranch (cursor : CaseCursor) (rest : List (Branch Tree)) : CaseCursor :=
  { cursor with pendingBranches := rest }

/-- Selects the current branch. Its local fields become globally active at this response
boundary, while its child branches are scheduled before the remaining siblings. -/
def selectBranch (cursor : CaseCursor) (body : Tree) (rest : List (Branch Tree))
    : CaseCursor :=
  {
    namedFieldChunksRev := localNamedFields body :: cursor.namedFieldChunksRev
    pendingBranches := body.branches ++ rest
  }

def resolveBooleanBranch (cursor : CaseCursor) (body : Tree)
    (rest : List (Branch Tree)) (literal : BooleanLiteral) (value : Bool)
    : CaseCursor :=
  if literal.requiredValue = value then
    cursor.selectBranch body rest
  else
    cursor.skipBranch rest

def fieldGroups (inheritedBooleanCondition : List BooleanLiteral)
    (possibleTypes : PossibleTypeRegion) (cursor : CaseCursor)
    : List CollectedFieldGroup :=
  let condition : Condition := { possibleTypes, booleanCondition := [] }
  TreeSummary.fieldGroupsWithContext inheritedBooleanCondition condition
    (ConditionTree.collectFieldGroups cursor.namedFields)

end CaseCursor

-----------------------------------------------------------------------------------------
-- Batched case-forest scheduler
-----------------------------------------------------------------------------------------

/-- A supplied-variable request uses the compatibility-region scheduler. Every tree in
the forest contributes fields to the same execution case; selecting a compatible
branch activates its body for the next batched frontier. -/
structure CaseForest where
  activeTrees : List Tree
deriving Repr

namespace CaseForest

def ofConditionTree (tree : Tree) : CaseForest :=
  { activeTrees := [tree] }

def branches (forest : CaseForest) : List (Branch Tree) :=
  forest.activeTrees.flatMap Tree.branches

def hasUnresolvedBranches (forest : CaseForest) : Bool :=
  forest.activeTrees.any fun tree => !tree.branches.isEmpty

def typeBranchPossibleTypes (forest : CaseForest) : List PossibleTypes :=
  forest.branches.filterMap
    fun branch =>
      match branch.condition with
      | .typeCondition _typeName => some branch.body.condition.possibleTypes
      | .booleanLiteral _literal => none

/-- This is exactly Core's partition into nonempty compatibility regions. Boolean-only
frontier progress is handled directly by `summarize`, not by a synthetic empty region. -/
def typeRegions (scope : PossibleTypes) (forest : CaseForest) : List PossibleTypeRegion :=
  possibleTypeRegions scope forest.typeBranchPossibleTypes

def booleanVariables (forest : CaseForest) : BooleanVariableNames :=
  (forest.branches.filterMap
    fun branch =>
      match branch.condition with
      | .typeCondition _typeName => none
      | .booleanLiteral literal => some literal.variableName).eraseDups

/-- Closed environments determine missing, null, and non-Boolean values as
false, matching directive evaluation for a closed request. -/
def booleanValue (variableValues : Execution.VariableValues) (variableName : Name)
    : Bool :=
  (inputValueBoolean? variableValues (.variable variableName)).getD false

def selectedChildren (possibleTypes : PossibleTypeRegion)
    (variableValues : Execution.VariableValues)
    : List (Branch Tree) -> List Tree
  | [] => []
  | branch :: rest =>
      match branch.condition with
      | .typeCondition _typeName =>
          if possibleTypesSubset possibleTypes branch.body.condition.possibleTypes then
            branch.body :: selectedChildren possibleTypes variableValues rest
          else
            selectedChildren possibleTypes variableValues rest
      | .booleanLiteral literal =>
          if booleanConditionAllows variableValues [literal] then
            branch.body :: selectedChildren possibleTypes variableValues rest
          else
            selectedChildren possibleTypes variableValues rest

def resolveActiveTrees (possibleTypes : PossibleTypeRegion)
    (variableValues : Execution.VariableValues)
    : List Tree -> List Tree
  | [] => []
  | tree :: rest =>
      { tree with branches := [] }
      :: (selectedChildren possibleTypes variableValues tree.branches
          ++ resolveActiveTrees possibleTypes variableValues rest)

def resolveBranches (possibleTypes : PossibleTypeRegion)
    (variableValues : Execution.VariableValues) (forest : CaseForest)
    : CaseForest :=
  { activeTrees := resolveActiveTrees possibleTypes variableValues forest.activeTrees }

def namedFields (forest : CaseForest) : List NamedField :=
  forest.activeTrees.flatMap
    fun tree =>
      tree.fields.flatMap
        fun group =>
          group.fields.map fun field => { responseName := group.responseName, field }

def fieldGroups (inheritedBooleanCondition : List BooleanLiteral)
    (possibleTypes : PossibleTypeRegion) (forest : CaseForest)
    : List CollectedFieldGroup :=
  let condition : Condition := { possibleTypes, booleanCondition := [] }
  TreeSummary.fieldGroupsWithContext inheritedBooleanCondition condition
    (ConditionTree.collectFieldGroups forest.namedFields)

/-- Records every request assignment observed at the frontier, including the implicit
false value of a missing, null, or non-Boolean input. -/
def extendBooleanCondition (inheritedBooleanCondition : List BooleanLiteral)
    (variableNames : BooleanVariableNames)
    (variableValues : Execution.VariableValues)
    : List BooleanLiteral :=
  let caseCondition :=
    variableNames.map
      fun variableName =>
        if booleanValue variableValues variableName then
          BooleanLiteral.positive variableName
        else
          BooleanLiteral.negative variableName
  Internal.extendBooleanCondition inheritedBooleanCondition caseCondition

end CaseForest

-----------------------------------------------------------------------------------------
-- Exact-case termination measures
-----------------------------------------------------------------------------------------

namespace Measure

mutual
  /-- The number of syntactic branch nodes still unresolved in one condition tree. -/
  def unresolvedBranchCount (tree : Tree) : Nat :=
    unresolvedBranchesCount tree.branches
  termination_by 2 * sizeOf tree
  decreasing_by
    cases tree
    simp_wf
    omega

  def unresolvedBranchesCount : List (Branch Tree) -> Nat
    | [] => 0
    | branch :: rest =>
        1 + unresolvedBranchCount branch.body + unresolvedBranchesCount rest
  termination_by branches => 2 * sizeOf branches + 1
  decreasing_by
    all_goals
      cases branch
      simp_wf
      omega
end

private theorem localNamedFieldGroups_responseDepth
    (groups : List ConditionTree.FieldGroup)
    : selectionSetResponseDepth
        ((groups.flatMap
            fun group =>
              group.fields.map
                fun field => { responseName := group.responseName, field }).map
          NamedField.toSelection)
      = conditionFieldGroupsResponseDepth groups := by
  induction groups with
  | nil =>
      simp only [List.flatMap_nil, List.map_nil, selectionSetResponseDepth,
        conditionFieldGroupsResponseDepth]
  | cons group rest ih =>
      rw [List.flatMap_cons, List.map_append,
        selectionSetResponseDepth_append, conditionFieldGroupsResponseDepth]
      have hgroup :
          (group.fields.map
              fun field => { responseName := group.responseName, field }).map
              NamedField.toSelection
            = group.selections := by
        simp [FieldGroup.selections, NamedField.toSelection, Function.comp_def]
      rw [hgroup]
      change
        max (selectionSetResponseDepth group.selections)
            (selectionSetResponseDepth
              ((rest.flatMap fun group =>
                group.fields.map
                  fun field => { responseName := group.responseName, field }).map
                NamedField.toSelection))
          = max (conditionFieldGroupResponseDepth group)
              (conditionFieldGroupsResponseDepth rest)
      rw [ih]
      rfl

def caseCursorResponseDepth (cursor : CaseCursor) : Nat :=
  max
    (selectionSetResponseDepth (cursor.namedFields.map NamedField.toSelection))
    (conditionBranchesResponseDepth cursor.pendingBranches)

def caseCursorUnresolvedCount (cursor : CaseCursor) : Nat :=
  unresolvedBranchesCount cursor.pendingBranches

private theorem unresolvedBranchesCount_append (left right : List (Branch Tree))
    : unresolvedBranchesCount (left ++ right)
      = unresolvedBranchesCount left + unresolvedBranchesCount right := by
  induction left with
  | nil => simp [unresolvedBranchesCount]
  | cons branch rest ih =>
      simp [unresolvedBranchesCount, ih, Nat.add_assoc]

private theorem conditionBranchesResponseDepth_append_local
    (left right : List (Branch Tree))
    : conditionBranchesResponseDepth (left ++ right)
      = max (conditionBranchesResponseDepth left)
          (conditionBranchesResponseDepth right) := by
  induction left with
  | nil => simp [conditionBranchesResponseDepth]
  | cons branch rest ih =>
      simp [conditionBranchesResponseDepth, ih, Nat.max_assoc]

private theorem cursorLocalNamedFields_responseDepth (tree : Tree)
    : selectionSetResponseDepth
        ((CaseCursor.localNamedFields tree).map NamedField.toSelection)
      = conditionFieldGroupsResponseDepth tree.fields := by
  exact localNamedFieldGroups_responseDepth tree.fields

private theorem caseCursorResponseDepth_ofConditionTree (tree : Tree)
    : caseCursorResponseDepth (.ofConditionTree tree)
      = conditionTreeResponseDepth tree := by
  simp [caseCursorResponseDepth, CaseCursor.ofConditionTree, CaseCursor.namedFields,
    cursorLocalNamedFields_responseDepth, conditionTreeResponseDepth]

private theorem skipBranch_responseDepth_le (cursor : CaseCursor)
    (branch : Branch Tree) (rest : List (Branch Tree))
    (hbranches : cursor.pendingBranches = branch :: rest)
    : caseCursorResponseDepth (cursor.skipBranch rest)
      ≤ caseCursorResponseDepth cursor := by
  simp only [caseCursorResponseDepth, CaseCursor.skipBranch,
    hbranches, conditionBranchesResponseDepth]
  exact Nat.max_le.mpr
    ⟨Nat.le_max_left _ _,
      Nat.le_trans (Nat.le_max_right _ _)
        (Nat.le_max_right _ _)⟩

private theorem selectBranch_responseDepth_le (cursor : CaseCursor)
    (branch : Branch Tree) (rest : List (Branch Tree))
    (hbranches : cursor.pendingBranches = branch :: rest)
    : caseCursorResponseDepth (cursor.selectBranch branch.body rest)
      ≤ caseCursorResponseDepth cursor := by
  have hnamedFields :
      (cursor.selectBranch branch.body rest).namedFields
        = cursor.namedFields ++ CaseCursor.localNamedFields branch.body := by
    simp [CaseCursor.selectBranch, CaseCursor.namedFields]
  rw [caseCursorResponseDepth, caseCursorResponseDepth, hnamedFields,
    List.map_append,
    selectionSetResponseDepth_append, cursorLocalNamedFields_responseDepth,
    CaseCursor.selectBranch, hbranches, conditionBranchesResponseDepth_append_local,
    conditionBranchesResponseDepth,
    conditionTreeResponseDepth]
  omega

private theorem skipBranch_unresolvedCount_lt (cursor : CaseCursor)
    (branch : Branch Tree) (rest : List (Branch Tree))
    (hbranches : cursor.pendingBranches = branch :: rest)
    : caseCursorUnresolvedCount (cursor.skipBranch rest)
      < caseCursorUnresolvedCount cursor := by
  simp [caseCursorUnresolvedCount, CaseCursor.skipBranch,
    hbranches, unresolvedBranchesCount]
  omega

private theorem selectBranch_unresolvedCount_lt (cursor : CaseCursor)
    (branch : Branch Tree) (rest : List (Branch Tree))
    (hbranches : cursor.pendingBranches = branch :: rest)
    : caseCursorUnresolvedCount (cursor.selectBranch branch.body rest)
      < caseCursorUnresolvedCount cursor := by
  simp [caseCursorUnresolvedCount, CaseCursor.selectBranch,
    hbranches, unresolvedBranchesCount_append, unresolvedBranchCount,
    unresolvedBranchesCount]

private theorem resolveBooleanBranch_responseDepth_le (cursor : CaseCursor)
    (branch : Branch Tree) (rest : List (Branch Tree))
    (hbranches : cursor.pendingBranches = branch :: rest)
    (literal : BooleanLiteral) (value : Bool)
    : caseCursorResponseDepth (cursor.resolveBooleanBranch branch.body rest literal value)
      ≤ caseCursorResponseDepth cursor := by
  unfold CaseCursor.resolveBooleanBranch
  split
  · exact selectBranch_responseDepth_le cursor branch rest hbranches
  · exact skipBranch_responseDepth_le cursor branch rest hbranches

private theorem resolveBooleanBranch_unresolvedCount_lt (cursor : CaseCursor)
    (branch : Branch Tree) (rest : List (Branch Tree))
    (hbranches : cursor.pendingBranches = branch :: rest)
    (literal : BooleanLiteral) (value : Bool)
    : caseCursorUnresolvedCount
        (cursor.resolveBooleanBranch branch.body rest literal value)
      < caseCursorUnresolvedCount cursor := by
  unfold CaseCursor.resolveBooleanBranch
  split
  · exact selectBranch_unresolvedCount_lt cursor branch rest hbranches
  · exact skipBranch_unresolvedCount_lt cursor branch rest hbranches

private theorem cursorFieldGroupsResponseDepth_le
    (inheritedBooleanCondition : List BooleanLiteral)
    (possibleTypes : PossibleTypeRegion) (cursor : CaseCursor)
    : collectedFieldGroupsResponseDepth
        (cursor.fieldGroups inheritedBooleanCondition possibleTypes)
      ≤ caseCursorResponseDepth cursor := by
  rw [CaseCursor.fieldGroups,
    collectedFieldGroupsResponseDepth_fieldGroupsWithContext]
  exact Nat.le_trans
    (conditionFieldGroupsResponseDepth_collectFieldGroups cursor.namedFields)
    (Nat.le_max_left _ _)

def activeTreesResponseDepth : List Tree -> Nat
  | [] => 0
  | tree :: rest =>
      max (conditionTreeResponseDepth tree) (activeTreesResponseDepth rest)

def caseForestResponseDepth (forest : CaseForest) : Nat :=
  activeTreesResponseDepth forest.activeTrees

def activeTreesUnresolvedCount : List Tree -> Nat
  | [] => 0
  | tree :: rest => unresolvedBranchCount tree + activeTreesUnresolvedCount rest

def caseForestUnresolvedCount (forest : CaseForest) : Nat :=
  activeTreesUnresolvedCount forest.activeTrees

private theorem forestNamedFields_responseDepth_le (trees : List Tree)
    : selectionSetResponseDepth
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
  | nil => simp [activeTreesResponseDepth, selectionSetResponseDepth]
  | cons tree rest ih =>
      rw [List.flatMap_cons, List.map_append, selectionSetResponseDepth_append,
        activeTreesResponseDepth, localNamedFieldGroups_responseDepth tree.fields]
      simp only [conditionTreeResponseDepth]
      exact Nat.max_le.mpr
        ⟨Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _),
          Nat.le_trans ih (Nat.le_max_right _ _)⟩

private theorem forestFieldGroupsResponseDepth_le
    (inheritedBooleanCondition : List BooleanLiteral)
    (possibleTypes : PossibleTypeRegion) (forest : CaseForest)
    : collectedFieldGroupsResponseDepth
        (forest.fieldGroups inheritedBooleanCondition possibleTypes)
      ≤ caseForestResponseDepth forest := by
  rw [CaseForest.fieldGroups,
    collectedFieldGroupsResponseDepth_fieldGroupsWithContext]
  exact Nat.le_trans
    (conditionFieldGroupsResponseDepth_collectFieldGroups forest.namedFields)
    (forestNamedFields_responseDepth_le forest.activeTrees)

private theorem selectedChildren_unresolvedCount_le
    (possibleTypes : PossibleTypeRegion)
    (variableValues : Execution.VariableValues)
    (branches : List (Branch Tree))
    : activeTreesUnresolvedCount
        (CaseForest.selectedChildren possibleTypes variableValues branches)
      ≤ unresolvedBranchesCount branches := by
  induction branches with
  | nil => simp [CaseForest.selectedChildren, activeTreesUnresolvedCount,
      unresolvedBranchesCount]
  | cons branch rest ih =>
      rw [CaseForest.selectedChildren]
      split <;> split <;>
        simp only [activeTreesUnresolvedCount, unresolvedBranchesCount] <;>
        omega

private theorem activeTreesUnresolvedCount_append (left right : List Tree)
    : activeTreesUnresolvedCount (left ++ right)
      = activeTreesUnresolvedCount left + activeTreesUnresolvedCount right := by
  induction left with
  | nil => simp [activeTreesUnresolvedCount]
  | cons tree rest ih =>
      simp [activeTreesUnresolvedCount, ih, Nat.add_assoc]

private theorem activeTreesResponseDepth_append (left right : List Tree)
    : activeTreesResponseDepth (left ++ right)
      = max (activeTreesResponseDepth left) (activeTreesResponseDepth right) := by
  induction left with
  | nil => simp [activeTreesResponseDepth]
  | cons tree rest ih =>
      simp [activeTreesResponseDepth, ih, Nat.max_assoc]

private theorem selectedChildren_responseDepth_le
    (possibleTypes : PossibleTypeRegion)
    (variableValues : Execution.VariableValues)
    (branches : List (Branch Tree))
    : activeTreesResponseDepth
        (CaseForest.selectedChildren possibleTypes variableValues branches)
      ≤ conditionBranchesResponseDepth branches := by
  induction branches with
  | nil => simp [CaseForest.selectedChildren, activeTreesResponseDepth,
      conditionBranchesResponseDepth]
  | cons branch rest ih =>
      rw [CaseForest.selectedChildren]
      split <;> split <;>
        simp only [activeTreesResponseDepth, conditionBranchesResponseDepth] at *
      all_goals first
        | exact Nat.max_le.mpr
            ⟨Nat.le_max_left _ _, Nat.le_trans ih (Nat.le_max_right _ _)⟩
        | exact Nat.le_trans ih (Nat.le_max_right _ _)

private theorem resolveActiveTrees_responseDepth_le
    (possibleTypes : PossibleTypeRegion)
    (variableValues : Execution.VariableValues) (trees : List Tree)
    : activeTreesResponseDepth
        (CaseForest.resolveActiveTrees possibleTypes variableValues trees)
      ≤ activeTreesResponseDepth trees := by
  induction trees with
  | nil => simp [CaseForest.resolveActiveTrees, activeTreesResponseDepth]
  | cons tree rest ih =>
      rw [CaseForest.resolveActiveTrees, activeTreesResponseDepth,
        activeTreesResponseDepth_append, activeTreesResponseDepth]
      have hselected :=
        selectedChildren_responseDepth_le possibleTypes variableValues tree.branches
      simp only [conditionTreeResponseDepth, conditionBranchesResponseDepth, Nat.max_zero]
      exact Nat.max_le.mpr
        ⟨Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _),
          Nat.max_le.mpr
            ⟨Nat.le_trans hselected
                (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)),
              Nat.le_trans ih (Nat.le_max_right _ _)⟩⟩

private theorem selectedChildren_unresolvedCount_lt
    (possibleTypes : PossibleTypeRegion)
    (variableValues : Execution.VariableValues)
    (branch : Branch Tree) (rest : List (Branch Tree))
    : activeTreesUnresolvedCount
        (CaseForest.selectedChildren possibleTypes variableValues (branch :: rest))
      < unresolvedBranchesCount (branch :: rest) := by
  rw [CaseForest.selectedChildren]
  have hrest := selectedChildren_unresolvedCount_le possibleTypes variableValues rest
  split <;> split <;>
    simp only [activeTreesUnresolvedCount, unresolvedBranchesCount] <;>
    omega

private theorem resolveActiveTrees_unresolvedCount_le
    (possibleTypes : PossibleTypeRegion)
    (variableValues : Execution.VariableValues) (trees : List Tree)
    : activeTreesUnresolvedCount
        (CaseForest.resolveActiveTrees possibleTypes variableValues trees)
      ≤ activeTreesUnresolvedCount trees := by
  induction trees with
  | nil => simp [CaseForest.resolveActiveTrees, activeTreesUnresolvedCount]
  | cons tree rest ih =>
      rw [CaseForest.resolveActiveTrees, activeTreesUnresolvedCount,
        activeTreesUnresolvedCount]
      simp only [unresolvedBranchCount, unresolvedBranchesCount, Nat.zero_add]
      rw [activeTreesUnresolvedCount_append]
      have hbranches :=
        selectedChildren_unresolvedCount_le possibleTypes variableValues tree.branches
      omega

private theorem resolveActiveTrees_unresolvedCount_lt_of_any
    (possibleTypes : PossibleTypeRegion)
    (variableValues : Execution.VariableValues) (trees : List Tree)
    (hbranches : trees.any fun tree => !tree.branches.isEmpty)
    : activeTreesUnresolvedCount
        (CaseForest.resolveActiveTrees possibleTypes variableValues trees)
      < activeTreesUnresolvedCount trees := by
  induction trees with
  | nil => simp at hbranches
  | cons tree rest ih =>
      simp only [List.any_cons, Bool.or_eq_true] at hbranches
      rw [CaseForest.resolveActiveTrees, activeTreesUnresolvedCount,
        activeTreesUnresolvedCount]
      simp only [unresolvedBranchCount, unresolvedBranchesCount, Nat.zero_add]
      rw [activeTreesUnresolvedCount_append]
      rcases hbranches with htree | hrest
      · cases htreeBranches : tree.branches with
        | nil => simp [htreeBranches] at htree
        | cons branch branches =>
            have hcurrent := selectedChildren_unresolvedCount_lt possibleTypes
              variableValues branch branches
            have htail :=
              resolveActiveTrees_unresolvedCount_le possibleTypes variableValues rest
            omega
      · have hcurrent := selectedChildren_unresolvedCount_le possibleTypes
          variableValues tree.branches
        have htail := ih hrest
        omega

theorem resolveBranches_unresolvedCount_lt
    (possibleTypes : PossibleTypeRegion)
    (variableValues : Execution.VariableValues) (forest : CaseForest)
    (hbranches : forest.hasUnresolvedBranches = true)
    : caseForestUnresolvedCount (forest.resolveBranches possibleTypes variableValues)
      < caseForestUnresolvedCount forest := by
  exact resolveActiveTrees_unresolvedCount_lt_of_any possibleTypes variableValues
    forest.activeTrees hbranches

theorem resolveBranches_responseDepth_le
    (possibleTypes : PossibleTypeRegion)
    (variableValues : Execution.VariableValues) (forest : CaseForest)
    : caseForestResponseDepth (forest.resolveBranches possibleTypes variableValues)
      ≤ caseForestResponseDepth forest := by
  exact resolveActiveTrees_responseDepth_le possibleTypes variableValues forest.activeTrees

end Measure

open Measure

-----------------------------------------------------------------------------------------
-- Exact-case cursor implementation
-----------------------------------------------------------------------------------------

namespace CaseCursor

open Internal

private def decisionCursorPhase : Nat := 2
private def decisionCursorFieldGroupsPhase : Nat := 1
private def decisionCursorChildTypesPhase : Nat := 0

mutual
  /-- Follows the condition tree one branch at a time. A type branch partitions only the
  current region, and an unresolved Boolean branches only when this exact cursor
  reaches its literal. Both decisions therefore remain local to that tree node. -/
  def summarizeDecisionWithPruning (algebra : Algebra) (schema : Schema)
      (variableOrder : BooleanVariableNames)
      (inheritedBooleanCondition caseCondition : List BooleanLiteral)
      (cursor : CaseCursor) (possibleTypes : PossibleTypeRegion)
      (environment : CaseCursor.BooleanEnvironment)
      (pruningValues : Execution.VariableValues)
      : BooleanDecision algebra.Summary :=
    match _hbranches : cursor.pendingBranches with
    | [] =>
        summarizeFieldGroupsDecisionWithPruning algebra schema variableOrder
          (cursor.fieldGroups
            (extendBooleanCondition inheritedBooleanCondition caseCondition)
            possibleTypes)
          environment pruningValues
    | branch :: rest =>
        match branch.condition with
        | .typeCondition _typeName =>
            BooleanDecision.joinMap algebra
              (possibleTypeRegions possibleTypes [branch.body.condition.possibleTypes])
              fun region _hregion =>
                if possibleTypesSubset region branch.body.condition.possibleTypes then
                  summarizeDecisionWithPruning algebra schema variableOrder
                    inheritedBooleanCondition caseCondition
                    (cursor.selectBranch branch.body rest) region environment
                    pruningValues
                else
                  summarizeDecisionWithPruning algebra schema variableOrder
                    inheritedBooleanCondition caseCondition
                    (cursor.skipBranch rest) region environment pruningValues
        | .booleanLiteral literal =>
            match environment.statusForVariable literal.variableName with
            | some value =>
                let selectedLiteral :=
                  if value then
                    BooleanLiteral.positive literal.variableName
                  else
                    BooleanLiteral.negative literal.variableName
                summarizeDecisionWithPruning algebra schema variableOrder
                  inheritedBooleanCondition (selectedLiteral :: caseCondition)
                  (cursor.resolveBooleanBranch branch.body rest literal value)
                  possibleTypes environment pruningValues
            | none =>
                .split literal.variableName
                  (summarizeDecisionWithPruning algebra schema variableOrder
                    inheritedBooleanCondition
                    (.negative literal.variableName :: caseCondition)
                    (cursor.resolveBooleanBranch branch.body rest literal false)
                    possibleTypes (environment.assign literal.variableName false)
                    pruningValues)
                  (summarizeDecisionWithPruning algebra schema variableOrder
                    inheritedBooleanCondition
                    (.positive literal.variableName :: caseCondition)
                    (cursor.resolveBooleanBranch branch.body rest literal true)
                    possibleTypes (environment.assign literal.variableName true)
                    pruningValues)
  termination_by
    (
      caseCursorResponseDepth cursor,
      caseCursorUnresolvedCount cursor,
      decisionCursorPhase,
      0
    )
  decreasing_by
    all_goals first
      | apply quadruple_lt_of_depth_le_of_control_le_of_phase_lt
        · exact cursorFieldGroupsResponseDepth_le
            (extendBooleanCondition inheritedBooleanCondition caseCondition)
            possibleTypes cursor
        · exact Nat.zero_le _
        · decide
      | apply quadruple_lt_of_depth_le_of_control_lt
        · exact resolveBooleanBranch_responseDepth_le cursor branch rest _hbranches
            literal _
        · exact resolveBooleanBranch_unresolvedCount_lt cursor branch rest _hbranches
            literal _
      | apply quadruple_lt_of_depth_le_of_control_lt
        · exact selectBranch_responseDepth_le cursor branch rest _hbranches
        · exact selectBranch_unresolvedCount_lt cursor branch rest _hbranches
      | apply quadruple_lt_of_depth_le_of_control_lt
        · exact skipBranch_responseDepth_le cursor branch rest _hbranches
        · exact skipBranch_unresolvedCount_lt cursor branch rest _hbranches

  def summarizeFieldGroupsDecisionWithPruning (algebra : Algebra) (schema : Schema)
      (variableOrder : BooleanVariableNames)
      (groups : List CollectedFieldGroup) (environment : CaseCursor.BooleanEnvironment)
      (pruningValues : Execution.VariableValues)
      : BooleanDecision algebra.Summary :=
    BooleanDecision.combineMap algebra variableOrder groups
      fun group _hgroup =>
        (summarizeChildTypesDecisionWithPruning algebra schema variableOrder group
          (childParentTypes schema group) environment pruningValues).map
          (algebra.field group)
  termination_by
    (
      collectedFieldGroupsResponseDepth groups,
      0,
      decisionCursorFieldGroupsPhase,
      sizeOf groups
    )
  decreasing_by
    apply quadruple_lt_of_depth_le_of_control_le_of_phase_lt
    · exact collectedFieldGroupResponseDepth_le_of_mem group groups _hgroup
    · exact Nat.le_refl _
    · decide

  def summarizeChildTypesDecisionWithPruning (algebra : Algebra) (schema : Schema)
      (variableOrder : BooleanVariableNames)
      (group : CollectedFieldGroup) (parentTypes : TypeNames)
      (environment : CaseCursor.BooleanEnvironment)
      (pruningValues : Execution.VariableValues)
      : BooleanDecision algebra.Summary :=
    BooleanDecision.joinMap algebra parentTypes
      fun childParentType _hparentType =>
        let childTree :=
          group.childTreeWithKnownFalsePruning schema childParentType pruningValues
        summarizeDecisionWithPruning algebra schema variableOrder
          group.childInheritedBooleanCondition [] (.ofConditionTree childTree)
          childTree.condition.possibleTypes environment pruningValues
  termination_by
    (
      collectedFieldGroupResponseDepth group,
      0,
      decisionCursorChildTypesPhase,
      sizeOf parentTypes
    )
  decreasing_by
    apply Prod.Lex.left
    have hchild :=
      conditionTreeResponseDepth_ofSelectionSetInScopeWithKnownFalsePruning schema
        childParentType group.childInheritedBooleanCondition
        pruningValues group.mergedSelectionSet
    rw [caseCursorResponseDepth_ofConditionTree]
    exact Nat.lt_of_le_of_lt hchild (Nat.lt_succ_self _)
end

end CaseCursor

-----------------------------------------------------------------------------------------
-- Exact-case forest implementation
-----------------------------------------------------------------------------------------

namespace CaseForest

private def forestPhase : Nat := 3
private def typeRegionsPhase : Nat := 2
private def fieldGroupsPhase : Nat := 1
private def childTypesPhase : Nat := 0

mutual
  /-- Resolves a Boolean-only frontier directly, or the entire active frontier for every
  genuine compatibility region, before any field handler runs. This path operates
  directly on summaries and constructs no decision tree. -/
  def summarize (algebra : Algebra) (schema : Schema)
      (inheritedBooleanCondition : List BooleanLiteral)
      (forest : CaseForest) (possibleTypes : PossibleTypeRegion)
      (variableValues fixedVariableValues : Execution.VariableValues)
      : algebra.Summary :=
    if hbranches : forest.hasUnresolvedBranches then
      if forest.typeBranchPossibleTypes.isEmpty then
        summarize algebra schema
          (CaseForest.extendBooleanCondition inheritedBooleanCondition
            forest.booleanVariables variableValues)
          (forest.resolveBranches possibleTypes variableValues) possibleTypes
          variableValues fixedVariableValues
      else
        summarizeTypeRegions algebra schema inheritedBooleanCondition forest
          (forest.typeRegions possibleTypes) variableValues hbranches fixedVariableValues
    else
      summarizeFieldGroups algebra schema
        (forest.fieldGroups inheritedBooleanCondition possibleTypes)
        variableValues fixedVariableValues
  termination_by
    (caseForestResponseDepth forest, caseForestUnresolvedCount forest, forestPhase, 0)
  decreasing_by
    · apply quadruple_lt_of_depth_le_of_control_lt
      · exact resolveBranches_responseDepth_le possibleTypes variableValues forest
      · exact resolveBranches_unresolvedCount_lt possibleTypes variableValues forest hbranches
    · apply quadruple_lt_of_depth_le_of_control_le_of_phase_lt
      · exact Nat.le_refl _
      · exact Nat.le_refl _
      · decide
    · apply quadruple_lt_of_depth_le_of_control_le_of_phase_lt
      · exact forestFieldGroupsResponseDepth_le inheritedBooleanCondition
          possibleTypes forest
      · exact Nat.zero_le _
      · decide

  def summarizeTypeRegions (algebra : Algebra) (schema : Schema)
      (inheritedBooleanCondition : List BooleanLiteral)
      (forest : CaseForest) (regions : List PossibleTypeRegion)
      (variableValues : Execution.VariableValues)
      (_hbranches : forest.hasUnresolvedBranches = true)
      (fixedVariableValues : Execution.VariableValues)
      : algebra.Summary :=
    TreeSummary.joinMap algebra regions
      fun region _hregion =>
        summarize algebra schema
          (CaseForest.extendBooleanCondition inheritedBooleanCondition
            forest.booleanVariables variableValues)
          (forest.resolveBranches region variableValues) region variableValues
          fixedVariableValues
  termination_by
    (
      caseForestResponseDepth forest,
      caseForestUnresolvedCount forest,
      typeRegionsPhase,
      sizeOf regions
    )
  decreasing_by
    apply quadruple_lt_of_depth_le_of_control_lt
    · exact resolveBranches_responseDepth_le region variableValues forest
    · exact resolveBranches_unresolvedCount_lt region variableValues forest _hbranches

  def summarizeFieldGroups (algebra : Algebra) (schema : Schema)
      (groups : List CollectedFieldGroup)
      (variableValues fixedVariableValues : Execution.VariableValues)
      : algebra.Summary :=
    TreeSummary.combineMap algebra groups
      fun group _hgroup =>
        algebra.field group
          (summarizeChildTypes algebra schema group
            (childParentTypes schema group) variableValues fixedVariableValues)
  termination_by
    (collectedFieldGroupsResponseDepth groups, 0, fieldGroupsPhase, sizeOf groups)
  decreasing_by
    apply quadruple_lt_of_depth_le_of_control_le_of_phase_lt
    · exact collectedFieldGroupResponseDepth_le_of_mem group groups _hgroup
    · exact Nat.le_refl _
    · decide

  def summarizeChildTypes (algebra : Algebra) (schema : Schema)
      (group : CollectedFieldGroup) (parentTypes : TypeNames)
      (variableValues fixedVariableValues : Execution.VariableValues)
      : algebra.Summary :=
    TreeSummary.joinMap algebra parentTypes
      fun childParentType _hparentType =>
        let childTree :=
          group.childTreeWithKnownFalsePruning schema childParentType fixedVariableValues
        summarize algebra schema group.childInheritedBooleanCondition
          (.ofConditionTree childTree) childTree.condition.possibleTypes variableValues
          fixedVariableValues
  termination_by
    (collectedFieldGroupResponseDepth group, 0, childTypesPhase, sizeOf parentTypes)
  decreasing_by
    apply Prod.Lex.left
    have hchild :=
      conditionTreeResponseDepth_ofSelectionSetInScopeWithKnownFalsePruning schema
        childParentType group.childInheritedBooleanCondition fixedVariableValues
        group.mergedSelectionSet
    simp only [CaseForest.ofConditionTree, caseForestResponseDepth,
      activeTreesResponseDepth, Nat.max_zero]
    exact Nat.lt_of_le_of_lt hchild (Nat.lt_succ_self _)
end

end CaseForest

-----------------------------------------------------------------------------------------
-- Exact-case summary entry points
-----------------------------------------------------------------------------------------

/-- Builds the lazy Boolean decision tree under the pruning context canonically derived
from `environment`. The variable order is shared by every recursive child scope. -/
def Internal.summarizeConditionTreeDecision (algebra : Algebra) (schema : Schema)
    (inheritedBooleanCondition : List BooleanLiteral)
    (tree : Tree) (variableOrder : BooleanVariableNames)
    (environment : CaseCursor.BooleanEnvironment)
    : Internal.BooleanDecision algebra.Summary :=
  (CaseCursor.summarizeDecisionWithPruning algebra schema variableOrder
    inheritedBooleanCondition [] (.ofConditionTree tree)
    tree.condition.possibleTypes environment environment.pruningValues).compact
    algebra.join

/-- Factorized cursor evaluation of one tree. Absent values remain unresolved and split
lazily when their first literal is reached. -/
def CaseCursor.summarizeConditionTree (algebra : Algebra) (schema : Schema)
    (inheritedBooleanCondition : List BooleanLiteral)
    (tree : Tree) (caseValues : Execution.VariableValues)
    : algebra.Summary :=
  let variables := (conditionTreeBooleanVariables tree).eraseDups
  (Internal.summarizeConditionTreeDecision algebra schema inheritedBooleanCondition tree
    variables (.symbolic caseValues)).collapse
    algebra

/-- Batched forest evaluation of one tree under supplied request variables. -/
def CaseForest.summarizeConditionTree (algebra : Algebra) (schema : Schema)
    (inheritedBooleanCondition : List BooleanLiteral)
    (tree : Tree) (variableValues : Execution.VariableValues)
    (fixedVariableValues : Execution.VariableValues := variableValues)
    : algebra.Summary :=
  summarize algebra schema inheritedBooleanCondition
    (.ofConditionTree tree) tree.condition.possibleTypes variableValues
    fixedVariableValues

def CaseCursor.summarizeSelectionSet (algebra : Algebra) (schema : Schema)
    (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
    (selectionSet : List Selection) (caseValues : Execution.VariableValues)
    : algebra.Summary :=
  summarizeConditionTree algebra schema inheritedBooleanCondition
    (ConditionTree.ofSelectionSetInScopeWithKnownFalsePruning schema parentType
      inheritedBooleanCondition [] selectionSet)
    caseValues

def CaseForest.summarizeSelectionSet (algebra : Algebra) (schema : Schema)
    (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
    (selectionSet : List Selection) (variableValues : Execution.VariableValues)
    : algebra.Summary :=
  summarizeConditionTree algebra schema inheritedBooleanCondition
    (ConditionTree.ofSelectionSetInScopeWithKnownFalsePruning schema parentType
      inheritedBooleanCondition variableValues selectionSet)
    variableValues variableValues

/-- Operation summary with every Boolean variable initially unresolved. -/
def summarizeOperation (algebra : Algebra) (schema : Schema) (operation : Operation)
    : algebra.Summary :=
  CaseCursor.summarizeSelectionSet algebra schema (operation.rootType schema) []
    operation.selectionSet []

/-- Summarizes one supplied-variable execution case after applying operation defaults.
The resulting context is closed: Boolean values are known, while missing or null values
behave like false for modeled directives. The batched path constructs no Boolean
decision tree. -/
def summarizeOperationWithVariables
    (algebraFor : Execution.VariableValues -> Algebra) (schema : Schema)
    (variableValues : Execution.VariableValues) (operation : Operation)
    : (algebraFor (Execution.coerceVariableValues operation variableValues)).Summary :=
  let coercedVariableValues := Execution.coerceVariableValues operation variableValues
  CaseForest.summarizeSelectionSet (algebraFor coercedVariableValues) schema
    (operation.rootType schema) [] operation.selectionSet coercedVariableValues

-----------------------------------------------------------------------------------------
-- Exact-case soundness contract for analyses
-----------------------------------------------------------------------------------------

/-- Local soundness contract shared by both evaluators. It relates one concrete response
fold to one abstract tree-fold constructor and imposes no factoring requirements.
Field compatibility and argument-name uniqueness are supplied by valid operation
execution. -/
structure Soundness
    (concrete : ConcreteAlgebra.{u}) (abstract : Algebra.{v})
    (schema : Schema) (variableValues : VariableValues)
    extends SoundnessCore concrete abstract where
  field_sound
    : ∀ group parentType field fieldDefinition value children abstractChildren,
        group.representativeMatches field
        -> parentType ∈ group.condition.possibleTypes
        -> (field.arguments.map Argument.name).Nodup
        -> schema.lookupField parentType field.fieldName = some fieldDefinition
        -> fieldDefinition.outputType ∈ group.fieldOutputTypes schema
        -> group.FieldDefinitionsCompatible schema
        -> approximates children
            (foldChildSummaryForValue abstract abstractChildren value)
        -> approximates
            (concrete.field
              (resolvedFieldProvenance schema variableValues parentType fieldDefinition
                field)
              value children)
            (abstract.field group abstractChildren)

/-- ExactCases-specific extension of the core algebra laws. The core witness is an index,
so every additional law necessarily uses the same order carried by soundness. -/
structure JoinFactoringLaws (abstract : Algebra.{v}) (core : abstract.Lawful) : Prop where
  /-- ExactCases preserves type-region alternatives below branch-local Boolean decisions.
  Their collapse must be monotone when corresponding branches are refined. -/
  join_le
    : ∀ left right upper,
        core.le left upper
        -> core.le right upper
        -> core.le (abstract.join left right) upper
  /-- Factored type alternatives remain sound when simultaneous or field composition is
  delayed across the decision tree. -/
  combine_join_le
    : ∀ left right other,
        core.le (abstract.combine (abstract.join left right) other)
          (abstract.join (abstract.combine left other) (abstract.combine right other))
  field_join_le
    : ∀ group left right,
        core.le (abstract.field group (abstract.join left right))
          (abstract.join (abstract.field group left) (abstract.field group right))

/-- The cursor evaluator additionally needs laws that move type joins through delayed
simultaneous and field composition. -/
structure SoundnessWithFactoring
    (concrete : ConcreteAlgebra.{u}) (abstract : Algebra.{v})
    (schema : Schema) (variableValues : VariableValues)
    extends Soundness concrete abstract schema variableValues where
  joinFactoringLaws : JoinFactoringLaws abstract abstractLawful

-----------------------------------------------------------------------------------------
-- Exact-case soundness statements
-----------------------------------------------------------------------------------------

/-- Soundness of the variable-independent operation analysis. Its theorem witness is
`ExactCases.analysisSound`. -/
def AnalysisSound
    {concrete : ConcreteAlgebra.{u}} {abstract : Algebra.{v}} {schema : Schema}
    (soundnessFor : ∀ values, SoundnessWithFactoring concrete abstract schema values)
    (operation : Operation)
    : Prop :=
  SchemaWellFormedness.schemaWellFormed schema
  -> Validation.operationDefinitionValid schema operation
  -> ∀ (ObjectRef : Type) (resolvers : Resolvers ObjectRef)
        (variableValues : VariableValues) (source : ResolverValue ObjectRef),
      let coercedVariableValues := Execution.coerceVariableValues operation variableValues
      (soundnessFor coercedVariableValues).approximates
        (foldAnnotatedResponse concrete
          (executeQueryAnnotated schema resolvers variableValues operation source))
        (summarizeOperation abstract schema operation)

/-- Per-operation soundness of a variable-indexed exact-case analysis. Its theorem
witness is `ExactCases.analysisWithVariablesSound`. -/
def AnalysisWithVariablesSound
    {concrete : ConcreteAlgebra.{u}}
    (algebraFor : VariableValues -> Algebra.{v}) {schema : Schema}
    (soundnessFor : ∀ values, Soundness concrete (algebraFor values) schema values)
    (operation : Operation)
    : Prop :=
  SchemaWellFormedness.schemaWellFormed schema
  -> Validation.operationDefinitionValid schema operation
  -> ∀ (ObjectRef : Type) (resolvers : Resolvers ObjectRef)
        (variableValues : VariableValues) (source : ResolverValue ObjectRef),
      let coercedVariableValues := Execution.coerceVariableValues operation variableValues
      (soundnessFor coercedVariableValues).approximates
        (foldAnnotatedResponse concrete
          (executeQueryAnnotated schema resolvers variableValues operation source))
        (summarizeOperationWithVariables algebraFor schema variableValues operation)

end ExactCases

end TreeSummary
end GraphQL
