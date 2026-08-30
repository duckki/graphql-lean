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
inductive BooleanEnvironment where
  | symbolic (caseValues : Execution.VariableValues)
  | concrete (variableValues : Execution.VariableValues)
deriving Repr

namespace BooleanEnvironment

def variableValues : BooleanEnvironment -> Execution.VariableValues
  | .symbolic values => values
  | .concrete values => values

-- Immutable request knowledge used only by condition-tree extraction. Case splitting
-- extends `variableValues`, but those speculative assignments must not prune syntax.
def pruningValues : BooleanEnvironment -> Execution.VariableValues
  | .symbolic _caseValues => []
  | .concrete values => values

/-- Variable-independent request context. Every Boolean is unresolved until traversal
reaches its first literal. -/
def unresolved : BooleanEnvironment :=
  .symbolic []

/-- Records one symbolic case choice; concrete request contexts remain immutable. -/
def assign (environment : BooleanEnvironment) (variableName : Name) (value : Bool)
    : BooleanEnvironment :=
  match environment with
  | .symbolic values => .symbolic ((variableName, .boolean value) :: values)
  | .concrete values => .concrete values

/-- A supplied Boolean is known. An absent/non-Boolean symbolic value is unresolved,
while the same concrete request value selects the directive's false behavior. -/
def statusForVariable (environment : BooleanEnvironment) (variableName : Name)
    : Option Bool :=
  match inputValueBoolean? environment.variableValues (.variable variableName) with
  | some value => some value
  | none =>
      match environment with
      | .symbolic _caseValues => none
      | .concrete _values => some false

end BooleanEnvironment

namespace Internal

-- A lazily constructed exact-case decision. Tests remain explicit across field and
-- sibling composition, so repeated uses of one operation variable stay correlated.
-- `join` preserves a factored type-case partition without forcing unrelated Boolean
-- supports from disjoint type regions into a Cartesian product.
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

-- Cofactors a decision by one binary test result. Every later occurrence of the selected
-- test is removed, including occurrences below unrelated earlier tests.
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

-- Pointwise composition of two ordered decision trees. When one side does not yet
-- branch on the earlier variable, that side is shared by both alternatives. The same
-- variable is therefore aligned rather than expanded into incompatible cross-products.
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

-- A completed type alternative no longer needs a structural `join`. This smart
-- constructor retains factoring while either side still has Boolean/type decisions,
-- and otherwise combines the two finished summaries immediately.
def joinCases (join : α -> α -> α) (left right : BooleanDecision α) : BooleanDecision α :=
  match left, right with
  | .leaf leftSummary, .leaf rightSummary => .leaf (join leftSummary rightSummary)
  | left, right => .join left right

-- Compacts only a finished selection-set boundary. All recursive `field` applications
-- have already happened, so this changes decision representation without asking
-- analyses to make `field` monotone.
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

-- Logical source-order view materialized only when a completed case needs grouping.
def namedFields (cursor : CaseCursor) : List NamedField :=
  cursor.namedFieldChunksRev.reverse.flatten

def ofConditionTree (tree : Tree) : CaseCursor :=
  { namedFieldChunksRev := [localNamedFields tree], pendingBranches := tree.branches }

-- Rejects the current branch and continues with its siblings.
def skipBranch (cursor : CaseCursor) (rest : List (Branch Tree)) : CaseCursor :=
  { cursor with pendingBranches := rest }

-- Selects the current branch. Its local fields become globally active at this response
-- boundary, while its child branches are scheduled before the remaining siblings.
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
-- Exact-case termination measures
-----------------------------------------------------------------------------------------

namespace Measure

mutual
  -- The number of syntactic branch nodes still unresolved in one condition tree.
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

end Measure

open Measure

-----------------------------------------------------------------------------------------
-- Exact-case summary implementation
-----------------------------------------------------------------------------------------

namespace CaseCursor

open Internal

private def decisionCursorPhase : Nat := 2
private def decisionCursorFieldGroupsPhase : Nat := 1
private def decisionCursorChildTypesPhase : Nat := 0

mutual
  -- Follows the condition tree one branch at a time. A type branch partitions only the
  -- current region, and an unresolved Boolean branches only when this exact cursor
  -- reaches its literal. Both decisions therefore remain local to that tree node.
  def summarizeDecisionWithPruning (algebra : Algebra) (schema : Schema)
      (variableOrder : BooleanVariableNames)
      (inheritedBooleanCondition caseCondition : List BooleanLiteral)
      (cursor : CaseCursor) (possibleTypes : PossibleTypeRegion)
      (environment : BooleanEnvironment)
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
      (groups : List CollectedFieldGroup) (environment : BooleanEnvironment)
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
      (environment : BooleanEnvironment)
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
-- Exact-case summary entry points
-----------------------------------------------------------------------------------------

-- Builds the lazy Boolean decision tree under the pruning context canonically derived
-- from `environment`. The variable order is shared by every recursive child scope.
def Internal.summarizeConditionTreeDecision (algebra : Algebra) (schema : Schema)
    (inheritedBooleanCondition : List BooleanLiteral)
    (tree : Tree) (variableOrder : BooleanVariableNames)
    (environment : BooleanEnvironment)
    : Internal.BooleanDecision algebra.Summary :=
  (CaseCursor.summarizeDecisionWithPruning algebra schema variableOrder
    inheritedBooleanCondition [] (.ofConditionTree tree)
    tree.condition.possibleTypes environment environment.pruningValues).compact
    algebra.join

/-- Summarizes one tree under the pruning context canonically derived from its Boolean
environment. -/
def summarizeConditionTree (algebra : Algebra) (schema : Schema)
    (inheritedBooleanCondition : List BooleanLiteral)
    (tree : Tree) (environment : BooleanEnvironment)
    : algebra.Summary :=
  let variables := (conditionTreeBooleanVariables tree).eraseDups
  (Internal.summarizeConditionTreeDecision algebra schema inheritedBooleanCondition tree
    variables environment).collapse
    algebra

/-- Extracts and summarizes a selection set under an explicit Boolean context. -/
def summarizeSelectionSet (algebra : Algebra) (schema : Schema)
    (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
    (selectionSet : List Selection) (environment : BooleanEnvironment)
    : algebra.Summary :=
  summarizeConditionTree algebra schema inheritedBooleanCondition
    (ConditionTree.ofSelectionSetInScopeWithKnownFalsePruning schema parentType
      inheritedBooleanCondition environment.pruningValues selectionSet)
    environment

/-- Operation summary with every Boolean variable initially unresolved. -/
def summarizeOperation (algebra : Algebra) (schema : Schema) (operation : Operation)
    : algebra.Summary :=
  summarizeSelectionSet algebra schema (operation.rootType schema) []
    operation.selectionSet
    BooleanEnvironment.unresolved

/-- Summarizes one supplied-variable execution case after applying operation defaults.
The resulting context is total: Boolean values are known, while missing or null values
behave like false for modeled directives. No Boolean split is constructed on this path;
only the incrementally scheduled type alternatives remain to be collapsed. -/
def summarizeOperationWithVariables
    (algebraFor : Execution.VariableValues -> Algebra) (schema : Schema)
    (variableValues : Execution.VariableValues) (operation : Operation)
    : (algebraFor (Execution.coerceVariableValues operation variableValues)).Summary :=
  let coercedVariableValues := Execution.coerceVariableValues operation variableValues
  summarizeSelectionSet (algebraFor coercedVariableValues) schema
    (operation.rootType schema) [] operation.selectionSet
    (BooleanEnvironment.concrete coercedVariableValues)

-----------------------------------------------------------------------------------------
-- Exact-case soundness contract for analyses
-----------------------------------------------------------------------------------------

/-- ExactCases-specific extension of the core algebra laws. The core witness is an index,
so every additional law necessarily uses the same order carried by soundness. -/
structure JoinFactoringLaws (abstract : Algebra.{v}) (core : abstract.Lawful) : Prop where
  -- ExactCases preserves type-region alternatives below branch-local Boolean decisions.
  -- Their collapse must be monotone when corresponding branches are refined.
  join_le
    : ∀ left right upper,
        core.le left upper
        -> core.le right upper
        -> core.le (abstract.join left right) upper
  -- Factored type alternatives remain sound when simultaneous or field composition is
  -- delayed across the decision tree.
  combine_join_le
    : ∀ left right other,
        core.le (abstract.combine (abstract.join left right) other)
          (abstract.join (abstract.combine left other) (abstract.combine right other))
  field_join_le
    : ∀ group left right,
        core.le (abstract.field group (abstract.join left right))
          (abstract.join (abstract.field group left) (abstract.field group right))

-- The exact static group contains the executable field syntax that produced one
-- concrete resolver call. Runtime execution supplies the parent type separately because
-- one group can represent several possible object parents.
def groupRepresentsField (group : CollectedFieldGroup) (field : ExecutableField) : Prop :=
  .field field.responseName field.fieldName field.arguments [] field.selectionSet
  ∈ group.selections

/-- Local soundness contract for the exact-case traversal. It relates one concrete
response fold to one abstract tree-fold constructor at a time and imposes no leastness
requirement. -/
structure Soundness
    (concrete : ConcreteAlgebra.{u}) (abstract : Algebra.{v})
    (schema : Schema) (variableValues : VariableValues)
    extends SoundnessCore concrete abstract where
  joinFactoringLaws : JoinFactoringLaws abstract abstractLawful
  field_sound
    : ∀ group field fieldDefinition value children abstractChildren,
        field.parentType ∈ group.condition.possibleTypes
        -> groupRepresentsField group field
        -> schema.lookupField field.parentType field.fieldName = some fieldDefinition
        -> fieldDefinition.outputType ∈ group.fieldOutputTypes schema
        -> approximates children
            (foldChildSummaryForValue abstract abstractChildren value)
        -> approximates
            (concrete.field
              (resolvedFieldProvenance schema variableValues fieldDefinition field)
              value children)
            (abstract.field group abstractChildren)

-----------------------------------------------------------------------------------------
-- Exact-case soundness statements
-----------------------------------------------------------------------------------------

/-- Per-operation soundness of an exact-case analysis. Its theorem witness is
`ExactCases.analysisSound`. -/
def AnalysisSound
    {concrete : ConcreteAlgebra.{u}} {abstract : Algebra.{v}} {schema : Schema}
    (soundnessFor : ∀ values, Soundness concrete abstract schema values)
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
