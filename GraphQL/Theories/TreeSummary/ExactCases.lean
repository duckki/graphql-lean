import GraphQL.Theories.TreeSummary.ResponseFold
import GraphQL.Theories.ConditionTree.Execution

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

-- `ConditionTree.Tree` is extracted from one selection set. An exact-case forest is a
-- semantic work state: every active tree is a condition-tree subtree whose
-- local fields are present in the same runtime case. More active trees are introduced
-- when compatible branches are selected; they must be analyzed together because their
-- fields can share a response name.
structure CaseForest where
  activeTrees : List Tree
deriving Repr
namespace CaseForest

-- The initial exact-case forest contains only the extracted condition tree.
def ofConditionTree (tree : Tree) : CaseForest :=
  { activeTrees := [tree] }

def branches (tree : CaseForest) : List (Branch Tree) :=
  tree.activeTrees.flatMap Tree.branches

def hasUnresolvedBranches (tree : CaseForest) : Bool :=
  tree.activeTrees.any fun item => !item.branches.isEmpty

def typeBranchPossibleTypes (tree : CaseForest) : List PossibleTypes :=
  tree.branches.filterMap
    fun branch =>
      match branch.condition with
      | .typeCondition _typeName => some branch.body.condition.possibleTypes
      | .booleanLiteral _literal => none

-- Exact type regions for the current execution frontier. Its proof witness is
-- `CaseForest.typeRegions_exact` in the case proof module.
def typeRegions (scope : PossibleTypes) (tree : CaseForest) : List PossibleTypeRegion :=
  possibleTypeRegions scope tree.typeBranchPossibleTypes

def booleanVariables (tree : CaseForest) : BooleanVariableNames :=
  (tree.branches.filterMap
    fun branch =>
      match branch.condition with
      | .typeCondition _typeName => none
      | .booleanLiteral literal => some literal.variableName).eraseDups

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
  | item :: rest =>
      { item with branches := [] }
      :: (selectedChildren possibleTypes variableValues item.branches
          ++ resolveActiveTrees possibleTypes variableValues rest)

-- Resolves every active tree's current branches for one runtime case. The branchless copy
-- of a tree is followed by its selected bodies, preserving syntactic preorder. The selected
-- bodies remain unresolved and therefore form the next recursive frontier.
def resolveBranches (possibleTypes : PossibleTypeRegion)
    (variableValues : Execution.VariableValues) (tree : CaseForest)
    : CaseForest :=
  { activeTrees := resolveActiveTrees possibleTypes variableValues tree.activeTrees }

-- Fields from every simultaneously active syntactic root, in analyzer preorder.
def namedFields (tree : CaseForest) : List NamedField :=
  tree.activeTrees.flatMap
    fun item =>
      item.fields.flatMap
        fun group =>
          group.fields.map fun field => { responseName := group.responseName, field }

-- One terminal execution case, globally grouped by response name before an algebra's
-- field handler is called.
def fieldGroups (inheritedBooleanCondition : List BooleanLiteral)
    (possibleTypes : PossibleTypeRegion) (tree : CaseForest)
    : List CollectedFieldGroup :=
  let condition : Condition := { possibleTypes, booleanCondition := [] }
  TreeSummary.collectFieldGroups inheritedBooleanCondition condition
    (ConditionTree.collectFieldGroups tree.namedFields)

end CaseForest

def extendBooleanCondition
    (inheritedBooleanCondition : List BooleanLiteral)
    (variableNames : BooleanVariableNames)
    (variableValues : Execution.VariableValues)
    : List BooleanLiteral :=
  (canonicalBooleanCondition
    (inheritedBooleanCondition
      ++ variableNames.filterMap
          fun variableName => do
            let value ←
              Execution.inputValueBoolean? variableValues (.variable variableName)
            pure
            <| if value then .positive variableName else .negative variableName)).getD
    inheritedBooleanCondition

-- One operation-global fact about a modeled Boolean variable. Missing values are fixed
-- before tree traversal; unresolved values are assigned lazily by the first exact-case
-- node that needs them.
inductive BooleanStatus where
  | missing
  | unresolved
  | known (value : Bool)
deriving Repr, DecidableEq

abbrev BooleanStatuses := List (Name × BooleanStatus)

-- Boolean control context shared by every selection-set scope in one exact case.
-- `variableValues` retains the complete request environment for argument-sensitive
-- algebras; `statuses` distinguishes an absent value from an unresolved truth value.
structure BooleanEnvironment where
  statuses : BooleanStatuses
  variableValues : Execution.VariableValues
  -- Immutable request knowledge used only by condition-tree extraction. Case splitting
  -- extends `variableValues`, but those speculative assignments must not prune syntax.
  fixedVariableValues : Execution.VariableValues
deriving Repr

namespace BooleanEnvironment

-- Empty request context used by variable-independent entry points. Operation support is
-- completed as missing or unresolved before traversal reaches any condition branch.
def unknown : BooleanEnvironment :=
  { statuses := [], variableValues := [], fixedVariableValues := [] }

def status? (environment : BooleanEnvironment) (variableName : Name)
    : Option BooleanStatus :=
  environment.statuses.lookup variableName

def withStatus (environment : BooleanEnvironment) (variableName : Name)
    (status : BooleanStatus)
    : BooleanEnvironment :=
  { environment with statuses := (variableName, status) :: environment.statuses }

def assign (environment : BooleanEnvironment) (variableName : Name) (value : Bool)
    : BooleanEnvironment :=
  {
    environment with
      statuses := (variableName, .known value) :: environment.statuses
      variableValues :=
        (variableName, .boolean value) :: environment.variableValues
  }

-- A total context for a concrete, already-coerced request. Every variable is either a
-- known Boolean or fixed missing; no truth-value split remains for tree traversal.
def ofCompleteValues (variables : BooleanVariableNames)
    (variableValues : Execution.VariableValues)
    : BooleanEnvironment :=
  {
    statuses :=
      variables.map
        fun variableName =>
          let status :=
            match inputValueBoolean? variableValues (.variable variableName) with
            | some value => .known value
            | none => .missing
          (variableName, status)
    variableValues
    fixedVariableValues := variableValues
  }

-- Streams globally fixed missing/presence environments. Truth values marked
-- `unresolved` remain symbolic and are split only when an exact-case node needs them.
def summarizeCompletions (algebra : Algebra)
    (summarize : BooleanEnvironment -> algebra.Summary)
    : BooleanVariableNames -> BooleanEnvironment -> algebra.Summary
  | [], environment => summarize environment
  | variableName :: rest, environment =>
      match environment.status? variableName with
      | some _status => summarizeCompletions algebra summarize rest environment
      | none =>
          match inputValueBoolean? environment.variableValues
                  (.variable variableName) with
          | some value =>
              summarizeCompletions algebra summarize rest
                (environment.withStatus variableName (.known value))
          | none =>
              match lookupVariableValue? environment.variableValues variableName with
              | some _nonBooleanValue =>
                  summarizeCompletions algebra summarize rest
                    (environment.withStatus variableName .missing)
              | none =>
                  algebra.join
                    (summarizeCompletions algebra summarize rest
                      (environment.withStatus variableName .missing))
                    (summarizeCompletions algebra summarize rest
                      (environment.withStatus variableName .unresolved))
termination_by variables => variables

end BooleanEnvironment

-- A lazily constructed Boolean decision tree. Splits remain explicit across field and
-- sibling composition, so repeated uses of one operation variable stay correlated.
inductive BooleanDecision (Summary : Type u) where
  | leaf (summary : Summary)
  | split (variableName : Name) (onFalse onTrue : BooleanDecision Summary)
deriving Repr

namespace BooleanDecision

def nodeCount : BooleanDecision α -> Nat
  | .leaf _summary => 1
  | .split _variableName onFalse onTrue =>
      1 + nodeCount onFalse + nodeCount onTrue

def map (transform : α -> β) : BooleanDecision α -> BooleanDecision β
  | .leaf summary => .leaf (transform summary)
  | .split variableName onFalse onTrue =>
      .split variableName (map transform onFalse) (map transform onTrue)

-- Selects one globally consistent path through a decision. The assignment is a total
-- proof parameter; only variables actually reached by this decision are inspected.
def evaluate (assignment : Name -> Bool) : BooleanDecision α -> α
  | .leaf summary => summary
  | .split variableName onFalse onTrue =>
      if assignment variableName then
        evaluate assignment onTrue
      else
        evaluate assignment onFalse

-- Cofactors a decision by one global variable assignment. Every later test of the
-- selected variable is removed, including occurrences below unrelated earlier tests.
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

private theorem nodeCount_restrict_le (selectedVariable : Name) (selectedValue : Bool)
    (decision : BooleanDecision α)
    : (decision.restrict selectedVariable selectedValue).nodeCount
      ≤ decision.nodeCount := by
  induction decision with
  | leaf => simp [restrict, nodeCount]
  | split variableName onFalse onTrue ihFalse ihTrue =>
      simp only [restrict]
      split
      · cases selectedValue <;> simp_all [nodeCount] <;> omega
      · simp only [nodeCount]
        omega

-- Pointwise composition of two ordered decision trees. When one side does not yet
-- branch on the earlier variable, that side is shared by both alternatives. The same
-- variable is therefore aligned rather than expanded into incompatible cross-products.
def zipWith (variableOrder : BooleanVariableNames) (operation : α -> β -> γ)
    : BooleanDecision α -> BooleanDecision β -> BooleanDecision γ
  | .leaf left, right => right.map (operation left)
  | left, .leaf right => left.map fun value => operation value right
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
  all_goals
    simp only [nodeCount]
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

def joinMap (algebra : Algebra) (variableOrder : BooleanVariableNames)
    (items : List α)
    (summarize : ∀ item, item ∈ items -> BooleanDecision algebra.Summary)
    : BooleanDecision algebra.Summary :=
  match items with
  | [] => .leaf algebra.empty
  | item :: [] => summarize item (by simp)
  | item :: next :: rest =>
      zipWith variableOrder algebra.join
        (summarize item (by simp))
        (joinMap algebra variableOrder (next :: rest)
          fun candidate hcandidate => summarize candidate (by simp [hcandidate]))
termination_by items

end BooleanDecision

def BooleanEnvironment.nextUnresolved (environment : BooleanEnvironment)
    (remainingVariables localVariables : BooleanVariableNames)
    : Option Name :=
  remainingVariables.find?
    fun variableName =>
      variableName ∈ localVariables
      && match environment.status? variableName with
          | some .missing | some (.known _value) => false
          | some .unresolved | none => true

-- A context is fully resolved for a variable support when every supported variable is
-- explicitly fixed as missing or has a known Boolean value. Consequently, completion
-- leaves the context unchanged and no tree-local frontier can request another split.
def BooleanEnvironment.ResolvedFor (environment : BooleanEnvironment)
    (variables : BooleanVariableNames)
    : Prop :=
  ∀ variableName,
    variableName ∈ variables
    -> (∃ value, environment.status? variableName = some (.known value))
        ∨ environment.status? variableName = some .missing

-----------------------------------------------------------------------------------------
-- Exact-case termination measures
-----------------------------------------------------------------------------------------

namespace Measure

def activeTreesResponseDepth : List Tree -> Nat
  | [] => 0
  | tree :: rest =>
      max (conditionTreeResponseDepth tree) (activeTreesResponseDepth rest)

def caseForestResponseDepth (tree : CaseForest) : Nat :=
  activeTreesResponseDepth tree.activeTrees

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

def activeTreesUnresolvedCount : List Tree -> Nat
  | [] => 0
  | tree :: rest => unresolvedBranchCount tree + activeTreesUnresolvedCount rest

def caseForestUnresolvedCount (tree : CaseForest) : Nat :=
  activeTreesUnresolvedCount tree.activeTrees

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

private theorem exactCaseNamedFields_responseDepth_le_activeTrees (items : List Tree)
    : selectionSetResponseDepth
        ((items.flatMap
            fun item =>
              item.fields.flatMap
                fun group =>
                  group.fields.map
                    fun field => { responseName := group.responseName, field }).map
          NamedField.toSelection)
      ≤ activeTreesResponseDepth items := by
  induction items with
  | nil => simp [activeTreesResponseDepth, selectionSetResponseDepth]
  | cons tree rest ih =>
      rw [List.flatMap_cons, List.map_append, selectionSetResponseDepth_append,
        activeTreesResponseDepth,
        localNamedFieldGroups_responseDepth tree.fields]
      simp only [conditionTreeResponseDepth]
      exact Nat.max_le.mpr
        ⟨Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _),
          Nat.le_trans ih (Nat.le_max_right _ _)⟩

theorem fieldGroupsResponseDepth_le
    (inheritedBooleanCondition : List BooleanLiteral)
    (possibleTypes : PossibleTypeRegion) (tree : CaseForest)
    : collectedFieldGroupsResponseDepth
        (tree.fieldGroups inheritedBooleanCondition possibleTypes)
      ≤ caseForestResponseDepth tree := by
  rw [CaseForest.fieldGroups,
    collectedFieldGroupsResponseDepth_collectFieldGroups]
  exact Nat.le_trans
    (conditionFieldGroupsResponseDepth_collectFieldGroups tree.namedFields)
    (exactCaseNamedFields_responseDepth_le_activeTrees tree.activeTrees)

private theorem selectedChildren_count_le
    (possibleTypes : PossibleTypeRegion)
    (variableValues : Execution.VariableValues)
    (branches : List (Branch Tree))
    : activeTreesUnresolvedCount
        (CaseForest.selectedChildren possibleTypes variableValues branches)
      ≤ unresolvedBranchesCount branches := by
  induction branches with
  | nil => simp [CaseForest.selectedChildren,
      activeTreesUnresolvedCount, unresolvedBranchesCount]
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
  | nil => simp [CaseForest.selectedChildren,
      activeTreesResponseDepth, conditionBranchesResponseDepth]
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
    (variableValues : Execution.VariableValues) (items : List Tree)
    : activeTreesResponseDepth
        (CaseForest.resolveActiveTrees possibleTypes variableValues items)
      ≤ activeTreesResponseDepth items := by
  induction items with
  | nil => simp [CaseForest.resolveActiveTrees,
      activeTreesResponseDepth]
  | cons item rest ih =>
      rw [CaseForest.resolveActiveTrees, activeTreesResponseDepth,
        activeTreesResponseDepth_append,
        activeTreesResponseDepth]
      have hselected :=
        selectedChildren_responseDepth_le possibleTypes variableValues
          item.branches
      simp only [conditionTreeResponseDepth, conditionBranchesResponseDepth, Nat.max_zero]
      exact Nat.max_le.mpr
        ⟨Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _),
          Nat.max_le.mpr
            ⟨Nat.le_trans hselected
                (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)),
              Nat.le_trans ih (Nat.le_max_right _ _)⟩⟩

private theorem selectedChildren_count_lt
    (possibleTypes : PossibleTypeRegion)
    (variableValues : Execution.VariableValues)
    (branch : Branch Tree) (rest : List (Branch Tree))
    : activeTreesUnresolvedCount
        (CaseForest.selectedChildren possibleTypes variableValues (branch :: rest))
      < unresolvedBranchesCount (branch :: rest) := by
  rw [CaseForest.selectedChildren]
  have hrest :=
    selectedChildren_count_le possibleTypes variableValues rest
  split <;> split <;>
    simp only [activeTreesUnresolvedCount, unresolvedBranchesCount] <;>
    omega

private theorem resolveActiveTrees_unresolvedCount_le
    (possibleTypes : PossibleTypeRegion)
    (variableValues : Execution.VariableValues) (items : List Tree)
    : activeTreesUnresolvedCount
        (CaseForest.resolveActiveTrees possibleTypes variableValues items)
      ≤ activeTreesUnresolvedCount items := by
  induction items with
  | nil => simp [CaseForest.resolveActiveTrees, activeTreesUnresolvedCount]
  | cons item rest ih =>
      rw [CaseForest.resolveActiveTrees, activeTreesUnresolvedCount,
        activeTreesUnresolvedCount]
      simp only [unresolvedBranchCount, unresolvedBranchesCount, Nat.zero_add]
      rw [activeTreesUnresolvedCount_append]
      have hbranches :=
        selectedChildren_count_le possibleTypes variableValues item.branches
      omega

private theorem resolveActiveTrees_unresolvedCount_lt_of_any
    (possibleTypes : PossibleTypeRegion)
    (variableValues : Execution.VariableValues) (items : List Tree)
    (hbranches : items.any fun item => !item.branches.isEmpty)
    : activeTreesUnresolvedCount
        (CaseForest.resolveActiveTrees possibleTypes variableValues items)
      < activeTreesUnresolvedCount items := by
  induction items with
  | nil => simp at hbranches
  | cons item rest ih =>
      simp only [List.any_cons, Bool.or_eq_true] at hbranches
      rw [CaseForest.resolveActiveTrees, activeTreesUnresolvedCount,
        activeTreesUnresolvedCount]
      simp only [unresolvedBranchCount, unresolvedBranchesCount, Nat.zero_add]
      rw [activeTreesUnresolvedCount_append]
      rcases hbranches with hitem | hrest
      · cases hitemBranches : item.branches with
        | nil => simp [hitemBranches] at hitem
        | cons branch branches =>
            have hcurrent :=
              selectedChildren_count_lt possibleTypes variableValues
                branch branches
            have htail :=
              resolveActiveTrees_unresolvedCount_le possibleTypes variableValues rest
            omega
      · have hcurrent :=
          selectedChildren_count_le possibleTypes variableValues item.branches
        have htail := ih hrest
        omega

theorem resolveBranches_unresolvedCount_lt
    (possibleTypes : PossibleTypeRegion)
    (variableValues : Execution.VariableValues) (tree : CaseForest)
    (hbranches : tree.hasUnresolvedBranches = true)
    : caseForestUnresolvedCount (tree.resolveBranches possibleTypes variableValues)
      < caseForestUnresolvedCount tree := by
  exact resolveActiveTrees_unresolvedCount_lt_of_any possibleTypes variableValues
    tree.activeTrees hbranches

theorem resolveBranches_responseDepth_le
    (possibleTypes : PossibleTypeRegion)
    (variableValues : Execution.VariableValues) (tree : CaseForest)
    : caseForestResponseDepth (tree.resolveBranches possibleTypes variableValues)
      ≤ caseForestResponseDepth tree := by
  exact resolveActiveTrees_responseDepth_le possibleTypes variableValues tree.activeTrees

end Measure

open Measure

-----------------------------------------------------------------------------------------
-- Exact-case summary implementation
-----------------------------------------------------------------------------------------

namespace CaseForest

private def summarizePhase : Nat := 3
private def typeRegionsPhase : Nat := 2
private def fieldGroupsPhase : Nat := 1
private def childTypesPhase : Nat := 0

mutual
  -- Recursively resolves one exact-case forest. No field handler runs while an
  -- active tree still has an unresolved syntactic branch: a selected combination first
  -- becomes another exact-case forest, so fields contributed by compatible subtrees are
  -- collected together rather than combined algebraically after separate analyses.
  def summarize (algebra : Algebra) (schema : Schema)
      (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
      (tree : CaseForest) (possibleTypes : PossibleTypeRegion)
      (variableValues : Execution.VariableValues)
      (fixedVariableValues : Execution.VariableValues)
      : algebra.Summary :=
    if hbranches : tree.hasUnresolvedBranches then
      summarizeTypeRegions algebra schema parentType
        inheritedBooleanCondition tree (tree.typeRegions possibleTypes)
        variableValues hbranches fixedVariableValues
    else
      summarizeFieldGroups algebra schema
        (tree.fieldGroups inheritedBooleanCondition possibleTypes)
        variableValues fixedVariableValues
  termination_by
    (caseForestResponseDepth tree, caseForestUnresolvedCount tree, summarizePhase, 0)
  decreasing_by
    · apply quadruple_lt_of_depth_le_of_control_le_of_phase_lt
      · exact Nat.le_refl _
      · exact Nat.le_refl _
      · decide
    · apply quadruple_lt_of_depth_le_of_control_le_of_phase_lt
      · exact fieldGroupsResponseDepth_le inheritedBooleanCondition possibleTypes tree
      · exact Nat.zero_le _
      · decide

  def summarizeTypeRegions (algebra : Algebra)
      (schema : Schema) (parentType : Name)
      (inheritedBooleanCondition : List BooleanLiteral)
      (tree : CaseForest) (regions : List PossibleTypeRegion)
      (variableValues : Execution.VariableValues)
      (_hbranches : tree.hasUnresolvedBranches = true)
      (fixedVariableValues : Execution.VariableValues)
      : algebra.Summary :=
    joinMap algebra regions
      fun region _hregion =>
        summarize algebra schema parentType
          (extendBooleanCondition inheritedBooleanCondition tree.booleanVariables
            variableValues)
          (tree.resolveBranches region variableValues) region variableValues
          fixedVariableValues
  termination_by
    (
      caseForestResponseDepth tree,
      caseForestUnresolvedCount tree,
      typeRegionsPhase,
      sizeOf regions
    )
  decreasing_by
    apply quadruple_lt_of_depth_le_of_control_lt
    · exact resolveBranches_responseDepth_le region variableValues tree
    · have hcount :=
        resolveBranches_unresolvedCount_lt region variableValues tree _hbranches
      exact hcount

  def summarizeFieldGroups (algebra : Algebra) (schema : Schema)
      (groups : List CollectedFieldGroup)
      (variableValues : Execution.VariableValues)
      (fixedVariableValues : Execution.VariableValues)
      : algebra.Summary :=
    combineMap algebra groups
      (fun group _hgroup =>
        algebra.field group
          (summarizeChildTypes algebra schema group
            (childParentTypes schema group) variableValues fixedVariableValues))
  termination_by
    (collectedFieldGroupsResponseDepth groups, 0, fieldGroupsPhase, sizeOf groups)
  decreasing_by
    apply quadruple_lt_of_depth_le_of_control_le_of_phase_lt
    · exact collectedFieldGroupResponseDepth_le_of_mem group groups _hgroup
    · exact Nat.le_refl _
    · decide

  def summarizeChildTypes (algebra : Algebra) (schema : Schema)
      (group : CollectedFieldGroup) (parentTypes : TypeNames)
      (variableValues : Execution.VariableValues)
      (fixedVariableValues : Execution.VariableValues)
      : algebra.Summary :=
    joinMap algebra parentTypes
      (fun childParentType _hparentType =>
        let childTree :=
          group.childTreeWithKnownFalsePruning schema childParentType fixedVariableValues
        summarize algebra schema childParentType
          group.childInheritedBooleanCondition
          (.ofConditionTree childTree) childTree.condition.possibleTypes
          variableValues fixedVariableValues)
  termination_by
    (collectedFieldGroupResponseDepth group, 0, childTypesPhase, sizeOf parentTypes)
  decreasing_by
    apply Prod.Lex.left
    have hchild :=
      conditionTreeResponseDepth_ofSelectionSetInScopeWithKnownFalsePruning schema
        childParentType group.childInheritedBooleanCondition fixedVariableValues
        group.mergedSelectionSet
    simp only [CaseForest.ofConditionTree,
      caseForestResponseDepth, activeTreesResponseDepth,
      Nat.max_zero]
    exact Nat.lt_of_le_of_lt hchild (Nat.lt_succ_self _)
end

private def decisionSummarizePhase : Nat := 3
private def decisionTypeRegionsPhase : Nat := 2
private def decisionFieldGroupsPhase : Nat := 1
private def decisionChildTypesPhase : Nat := 0

private def decisionControlCount (tree : CaseForest)
    (remainingVariables : BooleanVariableNames)
    : Nat :=
  caseForestUnresolvedCount tree + remainingVariables.length

mutual
  -- Exact traversal with lazy Boolean truth-value splitting. Missing values have
  -- already been fixed in `environment`; an unresolved value becomes a decision only
  -- when it occurs on the current condition frontier.
  def summarizeDecision (algebra : Algebra) (schema : Schema)
      (variableOrder remainingVariables : BooleanVariableNames)
      (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
      (tree : CaseForest) (possibleTypes : PossibleTypeRegion)
      (environment : BooleanEnvironment)
      : BooleanDecision algebra.Summary :=
    if hbranches : tree.hasUnresolvedBranches then
      match _hnext : environment.nextUnresolved remainingVariables
                      tree.booleanVariables with
      | some variableName =>
          .split variableName
            (summarizeDecision algebra schema variableOrder
              (remainingVariables.erase variableName) parentType
              inheritedBooleanCondition tree possibleTypes
              (environment.assign variableName false))
            (summarizeDecision algebra schema variableOrder
              (remainingVariables.erase variableName) parentType
              inheritedBooleanCondition tree possibleTypes
              (environment.assign variableName true))
      | none =>
          summarizeTypeRegionsDecision algebra schema variableOrder remainingVariables
            parentType inheritedBooleanCondition tree (tree.typeRegions possibleTypes)
            environment hbranches
    else
      summarizeFieldGroupsDecision algebra schema variableOrder remainingVariables
        (tree.fieldGroups inheritedBooleanCondition possibleTypes) environment
  termination_by
    (
      caseForestResponseDepth tree,
      decisionControlCount tree remainingVariables,
      decisionSummarizePhase,
      0
    )
  decreasing_by
    · apply quadruple_lt_of_depth_le_of_control_lt
      · exact Nat.le_refl _
      · have hmem := List.mem_of_find?_eq_some _hnext
        have hlength := List.length_erase_of_mem hmem
        have hpositive : 0 < remainingVariables.length :=
          List.length_pos_of_mem hmem
        unfold decisionControlCount
        rw [hlength]
        omega
    · apply quadruple_lt_of_depth_le_of_control_lt
      · exact Nat.le_refl _
      · have hmem := List.mem_of_find?_eq_some _hnext
        have hlength := List.length_erase_of_mem hmem
        have hpositive : 0 < remainingVariables.length :=
          List.length_pos_of_mem hmem
        unfold decisionControlCount
        rw [hlength]
        omega
    · apply quadruple_lt_of_depth_le_of_control_le_of_phase_lt
      · exact Nat.le_refl _
      · exact Nat.le_refl _
      · decide
    · apply quadruple_lt_of_depth_le_of_control_le_of_phase_lt
      · exact fieldGroupsResponseDepth_le inheritedBooleanCondition
          possibleTypes tree
      · unfold decisionControlCount
        omega
      · decide

  def summarizeTypeRegionsDecision (algebra : Algebra) (schema : Schema)
      (variableOrder remainingVariables : BooleanVariableNames)
      (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
      (tree : CaseForest) (regions : List PossibleTypeRegion)
      (environment : BooleanEnvironment)
      (_hbranches : tree.hasUnresolvedBranches = true)
      : BooleanDecision algebra.Summary :=
    BooleanDecision.joinMap algebra variableOrder regions
      fun region _hregion =>
        summarizeDecision algebra schema variableOrder remainingVariables parentType
          (extendBooleanCondition inheritedBooleanCondition tree.booleanVariables
            environment.variableValues)
          (tree.resolveBranches region environment.variableValues) region environment
  termination_by
    (
      caseForestResponseDepth tree,
      decisionControlCount tree remainingVariables,
      decisionTypeRegionsPhase,
      sizeOf regions
    )
  decreasing_by
    apply quadruple_lt_of_depth_le_of_control_lt
    · exact resolveBranches_responseDepth_le region environment.variableValues tree
    · have hcount := resolveBranches_unresolvedCount_lt region
        environment.variableValues tree _hbranches
      unfold decisionControlCount
      omega

  def summarizeFieldGroupsDecision (algebra : Algebra) (schema : Schema)
      (variableOrder remainingVariables : BooleanVariableNames)
      (groups : List CollectedFieldGroup) (environment : BooleanEnvironment)
      : BooleanDecision algebra.Summary :=
    BooleanDecision.combineMap algebra variableOrder groups
      fun group _hgroup =>
        (summarizeChildTypesDecision algebra schema variableOrder remainingVariables group
          (childParentTypes schema group) environment).map
          (algebra.field group)
  termination_by
    (
      collectedFieldGroupsResponseDepth groups,
      remainingVariables.length,
      decisionFieldGroupsPhase,
      sizeOf groups
    )
  decreasing_by
    apply quadruple_lt_of_depth_le_of_control_le_of_phase_lt
    · exact collectedFieldGroupResponseDepth_le_of_mem group groups _hgroup
    · exact Nat.le_refl _
    · decide

  def summarizeChildTypesDecision (algebra : Algebra) (schema : Schema)
      (variableOrder remainingVariables : BooleanVariableNames)
      (group : CollectedFieldGroup) (parentTypes : TypeNames)
      (environment : BooleanEnvironment)
      : BooleanDecision algebra.Summary :=
    BooleanDecision.joinMap algebra variableOrder parentTypes
      fun childParentType _hparentType =>
        let childTree :=
          group.childTreeWithKnownFalsePruning schema childParentType
            environment.fixedVariableValues
        summarizeDecision algebra schema variableOrder remainingVariables childParentType
          group.childInheritedBooleanCondition (.ofConditionTree childTree)
          childTree.condition.possibleTypes environment
  termination_by
    (
      collectedFieldGroupResponseDepth group,
      remainingVariables.length,
      decisionChildTypesPhase,
      sizeOf parentTypes
    )
  decreasing_by
    apply Prod.Lex.left
    have hchild :=
      conditionTreeResponseDepth_ofSelectionSetInScopeWithKnownFalsePruning schema
        childParentType group.childInheritedBooleanCondition
        environment.fixedVariableValues group.mergedSelectionSet
    simp only [CaseForest.ofConditionTree, caseForestResponseDepth,
      activeTreesResponseDepth, Nat.max_zero]
    exact Nat.lt_of_le_of_lt hchild (Nat.lt_succ_self _)
end

end CaseForest

-----------------------------------------------------------------------------------------
-- Exact-case summary entry points
-----------------------------------------------------------------------------------------

def operationBooleanVariables (operation : Operation) : BooleanVariableNames :=
  (selectionSetBooleanVariables operation.selectionSet).eraseDups

-- Builds the lazy Boolean decision tree for one extracted condition tree. The variable
-- order is shared by every recursive child scope, so pointwise composition can align
-- repeated uses of one variable without constructing incompatible cross-products.
def summarizeConditionTreeDecision (algebra : Algebra) (schema : Schema)
    (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
    (tree : Tree) (variableOrder : BooleanVariableNames)
    (environment : BooleanEnvironment)
    : BooleanDecision algebra.Summary :=
  CaseForest.summarizeDecision algebra schema variableOrder variableOrder parentType
    inheritedBooleanCondition (.ofConditionTree tree) tree.condition.possibleTypes
    environment

-- Summarizes one tree under an explicit Boolean context. Statuses already present in
-- the context are respected; absent support variables are completed as either missing
-- or present-but-unresolved, and unresolved truth values are split only when reached.
def summarizeConditionTree (algebra : Algebra) (schema : Schema)
    (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
    (tree : Tree) (environment : BooleanEnvironment)
    : algebra.Summary :=
  let variables := (conditionTreeBooleanVariables tree).eraseDups
  BooleanEnvironment.summarizeCompletions algebra
    (fun completed =>
      (summarizeConditionTreeDecision algebra schema parentType
        inheritedBooleanCondition tree variables completed).collapse
        algebra)
    variables environment

-- Extracts and summarizes a selection set under an explicit Boolean context.
def summarizeSelectionSet (algebra : Algebra) (schema : Schema)
    (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
    (selectionSet : List Selection) (environment : BooleanEnvironment)
    : algebra.Summary :=
  summarizeConditionTree algebra schema parentType inheritedBooleanCondition
    (ConditionTree.ofSelectionSetInScopeWithKnownFalsePruning schema parentType
      inheritedBooleanCondition environment.fixedVariableValues selectionSet)
    environment

-- Operation summary with every Boolean variable initially unknown.
def summarizeOperation (algebra : Algebra) (schema : Schema) (operation : Operation)
    : algebra.Summary :=
  summarizeSelectionSet algebra schema (operation.rootType schema) []
    operation.selectionSet BooleanEnvironment.unknown

-- Summarizes one supplied-variable execution case after applying operation defaults.
-- The resulting context is total: Boolean values are known and missing or null values
-- reject both modeled directives. The resolved fast path therefore evaluates the case
-- tree directly, without constructing or collapsing a Boolean decision tree.
def summarizeOperationWithVariables
    (algebraFor : Execution.VariableValues -> Algebra) (schema : Schema)
    (variableValues : Execution.VariableValues) (operation : Operation)
    : (algebraFor (Execution.coerceVariableValues operation variableValues)).Summary :=
  let coercedVariableValues := Execution.coerceVariableValues operation variableValues
  let parentType := operation.rootType schema
  let tree :=
    ConditionTree.ofSelectionSetInScopeWithKnownFalsePruning schema parentType []
      coercedVariableValues operation.selectionSet
  CaseForest.summarize (algebraFor coercedVariableValues) schema parentType []
    (.ofConditionTree tree) tree.condition.possibleTypes coercedVariableValues
    coercedVariableValues

-----------------------------------------------------------------------------------------
-- PossibleTypeRegion invariant
-----------------------------------------------------------------------------------------

-- Exact symbolic partition induced by type-condition membership. The first conjunct
-- excludes empty/out-of-scope regions, the second gives unique coverage of every
-- possible runtime type, and the third says every condition is constant on a region.
-- Its theorem witness is `possibleTypeRegions_exact` in
-- `Proofs.GraphQL.Theories.TreeSummary.ExactCases.Cases`.
def PossibleTypeRegionsExact (scope : PossibleTypes) (conditions : List PossibleTypes)
    : Prop :=
  let regions := possibleTypeRegions scope conditions
  (∀ region,
    region ∈ regions -> region ≠ [] ∧ ∀ typeName, typeName ∈ region -> typeName ∈ scope)
  ∧ (∀ typeName,
      typeName ∈ scope
      -> ∃ region,
          (region ∈ regions ∧ typeName ∈ region)
          ∧ ∀ candidate, candidate ∈ regions ∧ typeName ∈ candidate -> candidate = region)
  ∧ (∀ region,
      region ∈ regions
      -> ∀ left,
          left ∈ region
          -> ∀ right,
              right ∈ region
              -> ∀ allowed,
                  allowed ∈ conditions -> allowed.contains left = allowed.contains right)

-----------------------------------------------------------------------------------------
-- Exact-case soundness
-----------------------------------------------------------------------------------------

-- The exact static group contains the executable field syntax that produced one
-- concrete resolver call. Runtime execution supplies the parent type separately because
-- one group can represent several possible object parents.
def groupRepresentsField (group : CollectedFieldGroup) (field : ExecutableField) : Prop :=
  .field field.responseName field.fieldName field.arguments [] field.selectionSet
  ∈ group.selections

-- Local soundness contract for the exact-case traversal. It relates one concrete
-- response fold to one abstract tree-fold constructor at a time and imposes no
-- leastness requirement.
structure Compatible
    (concrete : ConcreteAlgebra.{u}) (abstract : Algebra.{v})
    (schema : Schema) (variableValues : VariableValues)
    extends CompatibilityCore concrete abstract where
  field_related
    : ∀ group field schemaDefinition value children abstractChildren,
        field.parentType ∈ group.condition.possibleTypes
        -> groupRepresentsField group field
        -> schema.lookupField field.parentType field.fieldName = some schemaDefinition
        -> schemaDefinition.outputType ∈ group.fieldOutputTypes schema
        -> related children (foldChildSummaryForValue abstract abstractChildren value)
        -> related
            (concrete.field
              (resolvedFieldProvenance schema variableValues schemaDefinition field)
              value children)
            (abstract.field group abstractChildren)

-- Soundness for an analysis whose algebra and compatibility proof depend on the
-- operation's coerced variable environment. Its theorem witness is
-- `ExactCases.operationWithVariablesSoundWithFuel`.
def OperationWithVariablesSoundWithFuel
    {concrete : ConcreteAlgebra.{u}}
    (algebraFor : VariableValues -> Algebra.{v}) {schema : Schema}
    (compatibleFor : ∀ values, Compatible concrete (algebraFor values) schema values)
    (operation : Operation)
    : Prop :=
  SchemaWellFormedness.schemaWellFormed schema
  -> Validation.operationDefinitionValid schema operation
  -> ∀ (ObjectRef : Type) (resolvers : Resolvers ObjectRef)
        (variableValues : VariableValues) (fuel : Nat)
        (source : ResolverValue ObjectRef),
      let coercedVariableValues := Execution.coerceVariableValues operation variableValues
      (compatibleFor coercedVariableValues).related
        (foldAnnotatedResponse concrete
          (executeQueryAnnotatedWithFuel schema resolvers variableValues operation fuel
            source))
        (summarizeOperationWithVariables algebraFor schema variableValues operation)

-- Default-executor form of `OperationWithVariablesSoundWithFuel`. Its theorem witness
-- is `ExactCases.operationWithVariablesSound`.
def OperationWithVariablesSound
    {concrete : ConcreteAlgebra.{u}}
    (algebraFor : VariableValues -> Algebra.{v}) {schema : Schema}
    (compatibleFor : ∀ values, Compatible concrete (algebraFor values) schema values)
    (operation : Operation)
    : Prop :=
  SchemaWellFormedness.schemaWellFormed schema
  -> Validation.operationDefinitionValid schema operation
  -> ∀ (ObjectRef : Type) (resolvers : Resolvers ObjectRef)
        (variableValues : VariableValues) (source : ResolverValue ObjectRef),
      let coercedVariableValues := Execution.coerceVariableValues operation variableValues
      (compatibleFor coercedVariableValues).related
        (foldAnnotatedResponse concrete
          (executeQueryAnnotated schema resolvers variableValues operation source))
        (summarizeOperationWithVariables algebraFor schema variableValues operation)

-- Every variable-indexed exact-case analysis supplying compatible concrete semantics is
-- sound. Its theorem witness is `ExactCases.analysisWithVariablesSound`.
def AnalysisWithVariablesSound
    (algebraFor : VariableValues -> Algebra.{v}) (schema : Schema)
    (operation : Operation)
    : Prop :=
  ∀ (concrete : ConcreteAlgebra.{u})
    (compatibleFor : ∀ values, Compatible concrete (algebraFor values) schema values),
    OperationWithVariablesSound algebraFor compatibleFor operation

-- Soundness of summarizing an operation through the explicit-context selection-set
-- entry point with a fixed, variable-independent analysis algebra. Its theorem witness
-- is `ExactCases.operationContextSound` in the exact soundness proof module.
def OperationContextSound
    {concrete : ConcreteAlgebra.{u}} {abstract : Algebra.{v}} {schema : Schema}
    (compatibleFor : ∀ values, Compatible concrete abstract schema values)
    (operation : Operation)
    : Prop :=
  SchemaWellFormedness.schemaWellFormed schema
  -> Validation.operationDefinitionValid schema operation
  -> ∀ (ObjectRef : Type) (resolvers : Resolvers ObjectRef)
        (variableValues : VariableValues) (source : ResolverValue ObjectRef)
        (environment : BooleanEnvironment),
      let coercedVariableValues := Execution.coerceVariableValues operation variableValues
      environment.variableValues = coercedVariableValues
      -> environment.fixedVariableValues = coercedVariableValues
      -> environment.ResolvedFor (operationBooleanVariables operation)
      -> (compatibleFor coercedVariableValues).related
          (foldAnnotatedResponse concrete
            (executeQueryAnnotated schema resolvers variableValues operation source))
          (summarizeSelectionSet abstract schema (operation.rootType schema) []
            operation.selectionSet environment)

-- Soundness of the same explicit-context selection-set entry point for an analysis
-- whose algebra depends on the coerced request values. The supplied context must
-- represent those values and fully resolve the operation's Boolean support. Its theorem
-- witness is
-- `ExactCases.operationContextWithVariablesSound` in the exact soundness proof module.
def OperationContextWithVariablesSound
    {concrete : ConcreteAlgebra.{u}}
    (algebraFor : VariableValues -> Algebra.{v}) {schema : Schema}
    (compatibleFor : ∀ values, Compatible concrete (algebraFor values) schema values)
    (operation : Operation)
    : Prop :=
  SchemaWellFormedness.schemaWellFormed schema
  -> Validation.operationDefinitionValid schema operation
  -> ∀ (ObjectRef : Type) (resolvers : Resolvers ObjectRef)
        (variableValues : VariableValues) (source : ResolverValue ObjectRef)
        (environment : BooleanEnvironment),
      let coercedVariableValues := Execution.coerceVariableValues operation variableValues
      environment.variableValues = coercedVariableValues
      -> environment.fixedVariableValues = coercedVariableValues
      -> environment.ResolvedFor (operationBooleanVariables operation)
      -> (compatibleFor coercedVariableValues).related
          (foldAnnotatedResponse concrete
            (executeQueryAnnotated schema resolvers variableValues operation source))
          (summarizeSelectionSet (algebraFor coercedVariableValues) schema
            (operation.rootType schema) [] operation.selectionSet environment)

-- Soundness against the fuel-parameterized annotated executor. Its generic theorem
-- witness is `ExactCases.operationSoundWithFuel` in
-- `Proofs.GraphQL.Theories.TreeSummary.ExactCases.Soundness`.
def OperationSoundWithFuel
    {concrete : ConcreteAlgebra.{u}} {abstract : Algebra.{v}} {schema : Schema}
    (compatibleFor : ∀ values, Compatible concrete abstract schema values)
    (operation : Operation)
    : Prop :=
  SchemaWellFormedness.schemaWellFormed schema
  -> Validation.operationDefinitionValid schema operation
  -> ∀ (ObjectRef : Type) (resolvers : Resolvers ObjectRef)
        (variableValues : VariableValues) (fuel : Nat)
        (source : ResolverValue ObjectRef),
      let coercedVariableValues := Execution.coerceVariableValues operation variableValues
      (compatibleFor coercedVariableValues).related
        (foldAnnotatedResponse concrete
          (executeQueryAnnotatedWithFuel schema resolvers variableValues operation fuel
            source))
        (summarizeOperation abstract schema operation)

-- Soundness against the default annotated executor. Its generic theorem witness is
-- `ExactCases.operationSound` in
-- `Proofs.GraphQL.Theories.TreeSummary.ExactCases.Soundness`.
def OperationSound
    {concrete : ConcreteAlgebra.{u}} {abstract : Algebra.{v}} {schema : Schema}
    (compatibleFor : ∀ values, Compatible concrete abstract schema values)
    (operation : Operation)
    : Prop :=
  SchemaWellFormedness.schemaWellFormed schema
  -> Validation.operationDefinitionValid schema operation
  -> ∀ (ObjectRef : Type) (resolvers : Resolvers ObjectRef)
        (variableValues : VariableValues) (source : ResolverValue ObjectRef),
      let coercedVariableValues := Execution.coerceVariableValues operation variableValues
      (compatibleFor coercedVariableValues).related
        (foldAnnotatedResponse concrete
          (executeQueryAnnotated schema resolvers variableValues operation source))
        (summarizeOperation abstract schema operation)

-- Every exact-case analysis that supplies the local compatibility contract is sound.
-- Its theorem witness is `ExactCases.analysisSound` in the exact soundness proof module.
def AnalysisSound (abstract : Algebra.{v}) (schema : Schema) (operation : Operation)
    : Prop :=
  ∀ (concrete : ConcreteAlgebra.{u})
    (compatibleFor : ∀ values, Compatible concrete abstract schema values),
    OperationSound compatibleFor operation

end ExactCases

end TreeSummary
end GraphQL
