import GraphQL.Theories.TreeSummary.ExactCases

/-! Generic best bounds and optional optimality contracts for the exact-case backend. -/

namespace GraphQL
namespace TreeSummary

open GraphQL.ConditionTree
open GraphQL.Execution

universe u v

-----------------------------------------------------------------------------------------
-- Optimality contracts for exact-case traversal
-----------------------------------------------------------------------------------------

namespace Optimality

-- `estimate` bounds a nonempty set of attainable concrete outcomes and is below every
-- other such bound. The named fields expose feasibility, soundness, and leastness
-- directly. Nonemptiness is essential for constructors such as additive composition to
-- preserve best bounds.
structure BestBound {ConcreteSummary : Type u} {AbstractSummary : Type v}
    (le : AbstractSummary -> AbstractSummary -> Prop)
    (related : ConcreteSummary -> AbstractSummary -> Prop)
    (attainable : ConcreteSummary -> Prop) (estimate : AbstractSummary)
    : Prop where
  feasible : ∃ concrete, attainable concrete
  sound : ∀ concrete, attainable concrete -> related concrete estimate
  least
    : ∀ candidate,
        (∀ concrete, attainable concrete -> related concrete candidate)
        -> le estimate candidate

end Optimality

open Optimality

-- Predicate-valued collecting domain retaining every concrete alternative.
abbrev OutcomeSet (Summary : Type u) := Summary -> Prop

namespace OutcomeSet

def singleton (value : Summary) : OutcomeSet Summary :=
  fun candidate => candidate = value

def combine (operation : Summary -> Summary -> Summary) (left right : OutcomeSet Summary)
    : OutcomeSet Summary :=
  fun outcome =>
    ∃ leftOutcome rightOutcome,
      left leftOutcome ∧ right rightOutcome ∧ outcome = operation leftOutcome rightOutcome

def union (left right : OutcomeSet Summary) : OutcomeSet Summary :=
  fun outcome => left outcome ∨ right outcome

-- Relational image of a set under a possibly nondeterministic concrete step.
def bind {ResultSummary : Type v} (source : OutcomeSet Summary)
    (next : Summary -> OutcomeSet ResultSummary)
    : OutcomeSet ResultSummary :=
  fun outcome => ∃ input, source input ∧ next input outcome

end OutcomeSet

namespace ExactCases

-- Analysis-independent semantics of recursively feasible exact cases. `combine`
-- supplies simultaneous composition; `fieldOutcomes` supplies every concrete result of
-- one collected response-name group. The semantics contains no abstract summary,
-- execution model, or best-bound proof.
structure CaseSemantics where
  Summary : Type u
  empty : Summary
  combine : Summary -> Summary -> Summary
  fieldOutcomes : CollectedFieldGroup -> Summary -> OutcomeSet Summary

-- Comparison, concrete-to-abstract relation, and local laws needed to transport best
-- bounds through the exact traversal. The recursive case semantics itself remains
-- independent of these laws.
structure BestTransferLaws (semantics : CaseSemantics.{u}) (abstract : Algebra.{v})
    : Type (max u v) where
  related : semantics.Summary -> abstract.Summary -> Prop
  le : abstract.Summary -> abstract.Summary -> Prop
  empty_best : BestBound le related (OutcomeSet.singleton semantics.empty) abstract.empty
  combine_best
    : ∀ left right abstractLeft abstractRight,
        BestBound le related left abstractLeft
        -> BestBound le related right abstractRight
        -> BestBound le related
            (OutcomeSet.combine semantics.combine left right)
            (abstract.combine abstractLeft abstractRight)
  field_best
    : ∀ group children abstractChildren,
        BestBound le related children abstractChildren
        -> BestBound le related
            (OutcomeSet.bind children (semantics.fieldOutcomes group))
            (abstract.field group abstractChildren)
  join_best
    : ∀ left right abstractLeft abstractRight,
        BestBound le related left abstractLeft
        -> BestBound le related right abstractRight
        -> BestBound le related (OutcomeSet.union left right)
            (abstract.join abstractLeft abstractRight)

end ExactCases

-----------------------------------------------------------------------------------------
-- Exact-case summary optimality statement
-----------------------------------------------------------------------------------------

namespace ExactCases

-- A total truth assignment used only to select paths through unresolved Boolean
-- decisions. Missing-versus-present status remains in `BooleanEnvironment` and is fixed
-- independently before a case derivation begins.
abbrev BooleanAssignment := Name -> Bool

mutual
  -- One feasible outcome of the lazy exact-case traversal under a fixed global truth
  -- assignment. The relation mirrors condition semantics, not an `Algebra`: it chooses
  -- one Boolean path, one feasible type region, and concrete field outcomes.
  inductive CaseForest.ContextOutcome (semantics : CaseSemantics.{u}) (schema : Schema)
      : BooleanVariableNames -> BooleanVariableNames -> BooleanAssignment
        -> BooleanEnvironment -> Name -> List BooleanLiteral -> CaseForest
        -> PossibleTypeRegion -> semantics.Summary -> Prop
    | split
      (variableOrder remainingVariables assignment environment parentType
        inheritedBooleanCondition tree possibleTypes variableName outcome)
      (hbranches : tree.hasUnresolvedBranches = true)
      (hnext
        : environment.nextUnresolved remainingVariables tree.booleanVariables
          = some variableName)
      (houtcome
        : CaseForest.ContextOutcome semantics schema variableOrder
            (remainingVariables.erase variableName) assignment
            (environment.assign variableName (assignment variableName)) parentType
            inheritedBooleanCondition tree possibleTypes outcome)
      : CaseForest.ContextOutcome semantics schema variableOrder remainingVariables
          assignment environment parentType inheritedBooleanCondition tree possibleTypes
          outcome
    | noTypeRegion
      (variableOrder remainingVariables assignment environment parentType
        inheritedBooleanCondition tree possibleTypes)
      (hbranches : tree.hasUnresolvedBranches = true)
      (hnext : environment.nextUnresolved remainingVariables tree.booleanVariables = none)
      (hregions : tree.typeRegions possibleTypes = [])
      : CaseForest.ContextOutcome semantics schema variableOrder remainingVariables
          assignment environment parentType inheritedBooleanCondition tree possibleTypes
          semantics.empty
    | resolve
      (variableOrder remainingVariables assignment environment parentType
        inheritedBooleanCondition tree possibleTypes region outcome)
      (hbranches : tree.hasUnresolvedBranches = true)
      (hnext : environment.nextUnresolved remainingVariables tree.booleanVariables = none)
      (hregion : region ∈ tree.typeRegions possibleTypes)
      (houtcome
        : CaseForest.ContextOutcome semantics schema variableOrder remainingVariables
            assignment environment parentType
            (extendBooleanCondition inheritedBooleanCondition tree.booleanVariables
              environment.variableValues)
            (tree.resolveBranches region environment.variableValues) region outcome)
      : CaseForest.ContextOutcome semantics schema variableOrder remainingVariables
          assignment environment parentType inheritedBooleanCondition tree possibleTypes
          outcome
    | fields
      (variableOrder remainingVariables assignment environment parentType
        inheritedBooleanCondition tree possibleTypes outcome)
      (hbranches : tree.hasUnresolvedBranches = false)
      (houtcome
        : CaseForest.ContextFieldGroupsOutcome semantics schema variableOrder
            remainingVariables assignment environment
            (tree.fieldGroups inheritedBooleanCondition possibleTypes) outcome)
      : CaseForest.ContextOutcome semantics schema variableOrder remainingVariables
          assignment environment parentType inheritedBooleanCondition tree possibleTypes
          outcome

  -- Simultaneous response-name groups share one assignment and environment. This is the
  -- relational counterpart of pointwise decision composition and rules out inconsistent
  -- sibling choices for repeated variables.
  inductive CaseForest.ContextFieldGroupsOutcome (semantics : CaseSemantics.{u})
      (schema : Schema)
      : BooleanVariableNames -> BooleanVariableNames -> BooleanAssignment
        -> BooleanEnvironment -> List CollectedFieldGroup -> semantics.Summary -> Prop
    | nil (variableOrder remainingVariables assignment environment)
      : CaseForest.ContextFieldGroupsOutcome semantics schema variableOrder
          remainingVariables assignment environment [] semantics.empty
    | cons
      (variableOrder remainingVariables assignment environment group rest children
        fieldOutcome restOutcome)
      (hchildren
        : CaseForest.ContextChildTypesOutcome semantics schema variableOrder
            remainingVariables assignment environment group
            (childParentTypes schema group) children)
      (hfield : semantics.fieldOutcomes group children fieldOutcome)
      (hrest
        : CaseForest.ContextFieldGroupsOutcome semantics schema variableOrder
            remainingVariables assignment environment rest restOutcome)
      : CaseForest.ContextFieldGroupsOutcome semantics schema variableOrder
          remainingVariables assignment environment (group :: rest)
          (semantics.combine fieldOutcome restOutcome)

  -- One feasible child output type is chosen while retaining the same global Boolean
  -- assignment for the recursive child selection set.
  inductive CaseForest.ContextChildTypesOutcome (semantics : CaseSemantics.{u})
      (schema : Schema)
      : BooleanVariableNames -> BooleanVariableNames -> BooleanAssignment
        -> BooleanEnvironment -> CollectedFieldGroup -> TypeNames
        -> semantics.Summary -> Prop
    | none (variableOrder remainingVariables assignment environment group)
      : CaseForest.ContextChildTypesOutcome semantics schema variableOrder
          remainingVariables assignment environment group [] semantics.empty
    | some
      (variableOrder remainingVariables assignment environment group parentTypes
        childParentType outcome)
      (hparentType : childParentType ∈ parentTypes)
      (houtcome
        : CaseForest.ContextOutcome semantics schema variableOrder remainingVariables
            assignment environment childParentType group.childInheritedBooleanCondition
            (.ofConditionTree
              (group.childTreeWithKnownFalsePruning schema childParentType
                environment.fixedVariableValues))
            (group.childTreeWithKnownFalsePruning schema childParentType
              environment.fixedVariableValues).condition.possibleTypes outcome)
      : CaseForest.ContextChildTypesOutcome semantics schema variableOrder
          remainingVariables assignment environment group parentTypes outcome
end

namespace BooleanEnvironment

-- Independent semantics for fixing missing-versus-present status globally. A supplied
-- Boolean becomes known, a supplied non-Boolean value is missing, and an absent value
-- admits both missing and present-but-unresolved completions.
def Completion : BooleanVariableNames -> BooleanEnvironment -> BooleanEnvironment -> Prop
  | [], initial, completed => completed = initial
  | variableName :: rest, initial, completed =>
      match initial.status? variableName with
      | some _status => Completion rest initial completed
      | none =>
          match inputValueBoolean? initial.variableValues (.variable variableName) with
          | some value =>
              Completion rest (initial.withStatus variableName (.known value)) completed
          | none =>
              match lookupVariableValue? initial.variableValues variableName with
              | some _nonBooleanValue =>
                  Completion rest (initial.withStatus variableName .missing) completed
              | none =>
                  Completion rest (initial.withStatus variableName .missing) completed
                  ∨ Completion rest (initial.withStatus variableName .unresolved)
                      completed
termination_by variables => variables

end BooleanEnvironment

-- Feasible outcomes of an extracted condition tree under an explicit initial context.
-- Missing-versus-present completion is global; truth values remain symbolic until the
-- relational traversal reaches their first relevant condition frontier.
def conditionTreeContextOutcomes (semantics : CaseSemantics.{u})
    (schema : Schema) (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral) (tree : Tree)
    (initial : BooleanEnvironment)
    : OutcomeSet semantics.Summary :=
  let variables := (conditionTreeBooleanVariables tree).eraseDups
  fun outcome =>
    ∃ completed,
      BooleanEnvironment.Completion variables initial completed
      ∧ ∃ assignment,
          CaseForest.ContextOutcome semantics schema variables variables assignment
            completed parentType inheritedBooleanCondition (.ofConditionTree tree)
            tree.condition.possibleTypes outcome

-- Feasible outcomes of a selection hierarchy under an explicit initial context.
def selectionSetContextOutcomes (semantics : CaseSemantics.{u})
    (schema : Schema) (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (selectionSet : List Selection) (initial : BooleanEnvironment)
    : OutcomeSet semantics.Summary :=
  conditionTreeContextOutcomes semantics schema parentType inheritedBooleanCondition
    (ConditionTree.ofSelectionSetInScopeWithKnownFalsePruning schema parentType
      inheritedBooleanCondition initial.fixedVariableValues selectionSet)
    initial

-- Feasible outcomes of a lazy operation summary under an explicit Boolean context.
def operationContextOutcomes (semantics : CaseSemantics.{u})
    (schema : Schema) (operation : Operation) (initial : BooleanEnvironment)
    : OutcomeSet semantics.Summary :=
  selectionSetContextOutcomes semantics schema (operation.rootType schema) []
    operation.selectionSet initial

-- The lazy operation summary is the least bound of its independently feasible cases.
-- Its generic witness is `ExactCases.operationContextOptimal` in
-- `Proofs.GraphQL.Theories.TreeSummary.ExactCasesOptimality`.
def OperationContextOptimal (semantics : CaseSemantics.{u}) (abstract : Algebra.{v})
    (le : abstract.Summary -> abstract.Summary -> Prop)
    (related : semantics.Summary -> abstract.Summary -> Prop)
    (schema : Schema) (operation : Operation) (initial : BooleanEnvironment)
    : Prop :=
  BestBound le related
    (operationContextOutcomes semantics schema operation initial)
    (summarizeSelectionSet abstract schema (operation.rootType schema) []
      operation.selectionSet initial)

-- Feasible outcomes of an operation with every Boolean variable initially unknown.
def operationOutcomes (semantics : CaseSemantics.{u})
    (schema : Schema) (operation : Operation)
    : OutcomeSet semantics.Summary :=
  operationContextOutcomes semantics schema operation BooleanEnvironment.unknown

-- Feasible outcomes after applying operation defaults and supplied values.
def operationOutcomesWithVariables (semantics : CaseSemantics.{u})
    (schema : Schema) (variableValues : VariableValues) (operation : Operation)
    : OutcomeSet semantics.Summary :=
  let coercedVariableValues := Execution.coerceVariableValues operation variableValues
  operationContextOutcomes semantics schema operation
    (BooleanEnvironment.ofCompleteValues (operationBooleanVariables operation)
      coercedVariableValues)

-- The default exact-case operation summary is the least bound of its feasible cases.
-- Its generic witness is `ExactCases.operationOptimal`.
def OperationOptimal (semantics : CaseSemantics.{u}) (abstract : Algebra.{v})
    (le : abstract.Summary -> abstract.Summary -> Prop)
    (related : semantics.Summary -> abstract.Summary -> Prop)
    (schema : Schema) (operation : Operation)
    : Prop :=
  BestBound le related (operationOutcomes semantics schema operation)
    (summarizeOperation abstract schema operation)

-- The variable-aware exact-case operation summary is the least bound of its feasible
-- cases. Its generic witness is `ExactCases.operationWithVariablesOptimal`.
def OperationWithVariablesOptimal
    (semantics : CaseSemantics.{u})
    (abstractFor : VariableValues -> Algebra.{v})
    (schema : Schema) (variableValues : VariableValues) (operation : Operation)
    (le
      : (abstractFor (Execution.coerceVariableValues operation variableValues)).Summary
        -> (abstractFor (Execution.coerceVariableValues operation variableValues)).Summary
        -> Prop)
    (related
      : semantics.Summary
        -> (abstractFor (Execution.coerceVariableValues operation variableValues)).Summary
        -> Prop)
    : Prop :=
  BestBound le related
    (operationOutcomesWithVariables semantics schema variableValues operation)
    (summarizeOperationWithVariables abstractFor schema variableValues operation)

end ExactCases
end TreeSummary
end GraphQL
