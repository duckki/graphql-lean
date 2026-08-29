import GraphQL.Theories.TreeSummary.ExactCases

/-! Generic best bounds and optimality contracts for the exact-case backend. -/

namespace GraphQL
namespace TreeSummary

open GraphQL.ConditionTree
open GraphQL.Execution

universe u v

-----------------------------------------------------------------------------------------
-- BestBound: The abstract summary representing the least upper bound of possible
--            concrete summaries
-----------------------------------------------------------------------------------------

namespace Optimality

-- `estimate` bounds a nonempty set of attainable concrete outcomes and is below every
-- other such bound. The named fields expose feasibility, soundness, and leastness
-- directly. Nonemptiness is essential for constructors such as additive composition to
-- preserve best bounds.
structure BestBound {ConcreteSummary : Type u} {AbstractSummary : Type v}
    (le : AbstractSummary -> AbstractSummary -> Prop)
    (approximates : ConcreteSummary -> AbstractSummary -> Prop)
    (attainable : ConcreteSummary -> Prop) (estimate : AbstractSummary)
    : Prop where
  feasible : ∃ concrete, attainable concrete
  sound : ∀ concrete, attainable concrete -> approximates concrete estimate
  least
    : ∀ candidate,
        (∀ concrete, attainable concrete -> approximates concrete candidate)
        -> le estimate candidate

end Optimality

open Optimality

-----------------------------------------------------------------------------------------
-- OutcomeSet: a set of analysis outcomes
-----------------------------------------------------------------------------------------

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

-----------------------------------------------------------------------------------------
-- Exact-case optimality contract for analyses
-----------------------------------------------------------------------------------------

namespace ExactCases

-- Analysis-generic semantics of recursively feasible exact cases. `combine`
-- supplies simultaneous composition; `fieldOutcomes` supplies every concrete result of
-- one collected response-name group.
structure OutcomeSemantics where
  Summary : Type u
  empty : Summary
  combine : Summary -> Summary -> Summary
  fieldOutcomes : CollectedFieldGroup -> Summary -> OutcomeSet Summary

-- Local laws transporting best bounds through the exact traversal.
structure BestTransferLaws (semantics : OutcomeSemantics.{u}) (abstract : Algebra.{v})
    : Type (max u v) where
  approximates : semantics.Summary -> abstract.Summary -> Prop
  le : abstract.Summary -> abstract.Summary -> Prop
  empty_best
    : BestBound le approximates (OutcomeSet.singleton semantics.empty) abstract.empty
  combine_best
    : ∀ left right abstractLeft abstractRight,
        BestBound le approximates left abstractLeft
        -> BestBound le approximates right abstractRight
        -> BestBound le approximates
            (OutcomeSet.combine semantics.combine left right)
            (abstract.combine abstractLeft abstractRight)
  field_best
    : ∀ group children abstractChildren,
        BestBound le approximates children abstractChildren
        -> BestBound le approximates
            (OutcomeSet.bind children (semantics.fieldOutcomes group))
            (abstract.field group abstractChildren)
  join_best
    : ∀ left right abstractLeft abstractRight,
        BestBound le approximates left abstractLeft
        -> BestBound le approximates right abstractRight
        -> BestBound le approximates (OutcomeSet.union left right)
            (abstract.join abstractLeft abstractRight)

end ExactCases

-----------------------------------------------------------------------------------------
-- Concrete outcome specification
-----------------------------------------------------------------------------------------

namespace ExactCases

-- A total truth assignment shared by every response-name group and recursive child in
-- one feasible case. Complete environments ignore it; symbolic environments consult it
-- only when traversal first reaches an unresolved variable.
abbrev BooleanAssignment := Name -> Bool

namespace BooleanAssignment

-- A total assignment respects every Boolean value already fixed by the initial
-- environment. Values for unresolved variables remain unconstrained.
def Extends (assignment : BooleanAssignment) (environment : BooleanEnvironment) : Prop :=
  ∀ variableName value,
    environment.statusForVariable variableName = some value
    -> assignment variableName = value

end BooleanAssignment

mutual
  -- One independently feasible outcome of the incremental cursor. The relation chooses
  -- one local type region and follows one globally consistent Boolean assignment; it
  -- does not invoke the executable summary fold or mention an analysis algebra.
  inductive CaseCursor.ContextOutcome (semantics : OutcomeSemantics.{u}) (schema : Schema)
      : BooleanAssignment -> BooleanEnvironment -> List BooleanLiteral
        -> List BooleanLiteral -> CaseCursor -> PossibleTypeRegion
        -> semantics.Summary -> Prop
    | noTypeRegion
      (assignment environment inheritedBooleanCondition caseCondition cursor
        possibleTypes branch rest typeName)
      (hbranches : cursor.pendingBranches = branch :: rest)
      (hcondition : branch.condition = .typeCondition typeName)
      (hregions
        : possibleTypeRegions possibleTypes [branch.body.condition.possibleTypes] = [])
      : CaseCursor.ContextOutcome semantics schema assignment environment
          inheritedBooleanCondition caseCondition cursor possibleTypes semantics.empty
    | selectTypeRegion
      (assignment environment inheritedBooleanCondition caseCondition cursor
        possibleTypes branch rest typeName region outcome)
      (hbranches : cursor.pendingBranches = branch :: rest)
      (hcondition : branch.condition = .typeCondition typeName)
      (hregion
        : region
          ∈ possibleTypeRegions possibleTypes [branch.body.condition.possibleTypes])
      (hselected : possibleTypesSubset region branch.body.condition.possibleTypes = true)
      (houtcome
        : CaseCursor.ContextOutcome semantics schema assignment environment
            inheritedBooleanCondition caseCondition
            (cursor.selectBranch branch.body rest) region outcome)
      : CaseCursor.ContextOutcome semantics schema assignment environment
          inheritedBooleanCondition caseCondition cursor possibleTypes outcome
    | skipTypeRegion
      (assignment environment inheritedBooleanCondition caseCondition cursor
        possibleTypes branch rest typeName region outcome)
      (hbranches : cursor.pendingBranches = branch :: rest)
      (hcondition : branch.condition = .typeCondition typeName)
      (hregion
        : region
          ∈ possibleTypeRegions possibleTypes [branch.body.condition.possibleTypes])
      (hskipped : possibleTypesSubset region branch.body.condition.possibleTypes = false)
      (houtcome
        : CaseCursor.ContextOutcome semantics schema assignment environment
            inheritedBooleanCondition caseCondition (cursor.skipBranch rest) region
            outcome)
      : CaseCursor.ContextOutcome semantics schema assignment environment
          inheritedBooleanCondition caseCondition cursor possibleTypes outcome
    | knownBoolean
      (assignment environment inheritedBooleanCondition caseCondition cursor
        possibleTypes branch rest literal value outcome)
      (hbranches : cursor.pendingBranches = branch :: rest)
      (hcondition : branch.condition = .booleanLiteral literal)
      (hstatus : environment.statusForVariable literal.variableName = some value)
      (houtcome
        : CaseCursor.ContextOutcome semantics schema assignment environment
            inheritedBooleanCondition
            ((if value then
                BooleanLiteral.positive literal.variableName
              else
                BooleanLiteral.negative literal.variableName)
              :: caseCondition)
            (cursor.resolveBooleanBranch branch.body rest literal value) possibleTypes
            outcome)
      : CaseCursor.ContextOutcome semantics schema assignment environment
          inheritedBooleanCondition caseCondition cursor possibleTypes outcome
    | splitBoolean
      (assignment environment inheritedBooleanCondition caseCondition cursor
        possibleTypes branch rest literal outcome)
      (hbranches : cursor.pendingBranches = branch :: rest)
      (hcondition : branch.condition = .booleanLiteral literal)
      (hstatus : environment.statusForVariable literal.variableName = none)
      (houtcome
        : CaseCursor.ContextOutcome semantics schema assignment
            (environment.assign literal.variableName (assignment literal.variableName))
            inheritedBooleanCondition
            ((if assignment literal.variableName then
                BooleanLiteral.positive literal.variableName
              else
                BooleanLiteral.negative literal.variableName)
              :: caseCondition)
            (cursor.resolveBooleanBranch branch.body rest literal
              (assignment literal.variableName))
            possibleTypes outcome)
      : CaseCursor.ContextOutcome semantics schema assignment environment
          inheritedBooleanCondition caseCondition cursor possibleTypes outcome
    | fields
      (assignment environment inheritedBooleanCondition caseCondition cursor
        possibleTypes outcome)
      (hbranches : cursor.pendingBranches = [])
      (houtcome
        : CaseCursor.ContextFieldGroupsOutcome semantics schema assignment environment
            (cursor.fieldGroups
              (Internal.extendBooleanCondition inheritedBooleanCondition caseCondition)
              possibleTypes)
            outcome)
      : CaseCursor.ContextOutcome semantics schema assignment environment
          inheritedBooleanCondition caseCondition cursor possibleTypes outcome

  -- All response-name groups at one boundary use the same assignment and environment,
  -- ruling out inconsistent choices for repeated variables in sibling groups.
  inductive CaseCursor.ContextFieldGroupsOutcome (semantics : OutcomeSemantics.{u})
      (schema : Schema)
      : BooleanAssignment -> BooleanEnvironment -> List CollectedFieldGroup
        -> semantics.Summary -> Prop
    | nil (assignment environment)
      : CaseCursor.ContextFieldGroupsOutcome semantics schema assignment environment []
          semantics.empty
    | cons
      (assignment environment group rest children fieldOutcome restOutcome)
      (hchildren
        : CaseCursor.ContextChildTypesOutcome semantics schema assignment environment
            group (childParentTypes schema group) children)
      (hfield : semantics.fieldOutcomes group children fieldOutcome)
      (hrest
        : CaseCursor.ContextFieldGroupsOutcome semantics schema assignment environment
            rest restOutcome)
      : CaseCursor.ContextFieldGroupsOutcome semantics schema assignment environment
          (group :: rest) (semantics.combine fieldOutcome restOutcome)

  -- A recursively selected field group chooses one feasible child output type while
  -- retaining the assignment shared by the enclosing response boundary.
  inductive CaseCursor.ContextChildTypesOutcome (semantics : OutcomeSemantics.{u})
      (schema : Schema)
      : BooleanAssignment -> BooleanEnvironment -> CollectedFieldGroup -> TypeNames
        -> semantics.Summary -> Prop
    | none (assignment environment group)
      : CaseCursor.ContextChildTypesOutcome semantics schema assignment environment group
          [] semantics.empty
    | some
      (assignment environment group parentTypes childParentType outcome)
      (hparentType : childParentType ∈ parentTypes)
      (houtcome
        : let childTree :=
            group.childTreeWithKnownFalsePruning schema childParentType
              environment.pruningValues
          CaseCursor.ContextOutcome semantics schema assignment environment
            group.childInheritedBooleanCondition [] (.ofConditionTree childTree)
            childTree.condition.possibleTypes outcome)
      : CaseCursor.ContextChildTypesOutcome semantics schema assignment environment group
          parentTypes outcome
end

-- Feasible outcomes of an extracted condition tree under an explicit initial context.
-- This definition is independent of the executable fold and abstract analysis.
def conditionTreeOutcomes (semantics : OutcomeSemantics.{u})
    (schema : Schema) (inheritedBooleanCondition : List BooleanLiteral) (tree : Tree)
    (initial : BooleanEnvironment)
    : OutcomeSet semantics.Summary :=
  fun outcome =>
    ∃ assignment,
      assignment.Extends initial
      ∧ CaseCursor.ContextOutcome semantics schema assignment initial
          inheritedBooleanCondition [] (.ofConditionTree tree)
          tree.condition.possibleTypes outcome

-- Feasible outcomes of a selection hierarchy under an explicit initial context.
def selectionSetOutcomes (semantics : OutcomeSemantics.{u})
    (schema : Schema) (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (selectionSet : List Selection) (initial : BooleanEnvironment)
    : OutcomeSet semantics.Summary :=
  conditionTreeOutcomes semantics schema inheritedBooleanCondition
    (ConditionTree.ofSelectionSetInScopeWithKnownFalsePruning schema parentType
      inheritedBooleanCondition initial.pruningValues selectionSet)
    initial

-- Feasible outcomes of an operation with every Boolean variable initially unresolved.
def operationOutcomes (semantics : OutcomeSemantics.{u})
    (schema : Schema) (operation : Operation)
    : OutcomeSet semantics.Summary :=
  selectionSetOutcomes semantics schema (operation.rootType schema) []
    operation.selectionSet BooleanEnvironment.unresolved

-- Feasible outcomes after applying operation defaults and supplied values.
def operationOutcomesWithVariables (semantics : OutcomeSemantics.{u})
    (schema : Schema) (variableValues : VariableValues) (operation : Operation)
    : OutcomeSet semantics.Summary :=
  let coercedVariableValues := Execution.coerceVariableValues operation variableValues
  selectionSetOutcomes semantics schema (operation.rootType schema) []
    operation.selectionSet
    (BooleanEnvironment.ofCompleteValues coercedVariableValues)

end ExactCases

-----------------------------------------------------------------------------------------
-- Exact-case summary optimality statements
-----------------------------------------------------------------------------------------

namespace ExactCases

-- Per-operation optimality of the default exact-case analysis. Its generic witness is
-- `ExactCases.analysisOptimal`.
def AnalysisOptimal
    {semantics : OutcomeSemantics.{u}} {abstract : Algebra.{v}}
    (laws : BestTransferLaws semantics abstract)
    (schema : Schema) (operation : Operation)
    : Prop :=
  BestBound laws.le laws.approximates (operationOutcomes semantics schema operation)
    (summarizeOperation abstract schema operation)

-- Per-operation optimality of a variable-aware exact-case analysis. Its generic witness
-- is `ExactCases.analysisWithVariablesOptimal`.
def AnalysisWithVariablesOptimal
    {semantics : OutcomeSemantics.{u}}
    (abstractFor : VariableValues -> Algebra.{v})
    (schema : Schema) (variableValues : VariableValues) (operation : Operation)
    (laws
      : BestTransferLaws semantics
          (abstractFor (Execution.coerceVariableValues operation variableValues)))
    : Prop :=
  BestBound laws.le laws.approximates
    (operationOutcomesWithVariables semantics schema variableValues operation)
    (summarizeOperationWithVariables abstractFor schema variableValues operation)

end ExactCases

end TreeSummary
end GraphQL
