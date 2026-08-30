import GraphQL.Theories.TreeSummary.ExactCases

/-! Relational outcome semantics and best-bound contracts for the exact-case backend.

The framework follows an abstract-interpretation-style design: `OutcomeSet` is a
collecting semantics, an `Algebra` supplies abstract transfer operations, and `BestBound`
expresses the best approximation relative to an analysis-defined relation. Execution
soundness is proved separately. A Galois connection is intentionally not required by
this interface.
-/

namespace GraphQL
namespace TreeSummary

open GraphQL.ConditionTree
open GraphQL.Execution

universe u v w

-----------------------------------------------------------------------------------------
-- BestBound: The abstract summary representing the least upper bound of possible
--            concrete summaries
-----------------------------------------------------------------------------------------

namespace Optimality

/-- `estimate` bounds a nonempty set of attainable concrete outcomes and is below every
other such bound. The named fields expose feasibility, soundness, and leastness
directly. Nonemptiness is essential for constructors such as additive composition to
preserve best bounds. -/
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

/-- Predicate-valued collecting domain retaining every concrete alternative. -/
abbrev OutcomeSet (Summary : Type u) := Summary -> Prop

namespace OutcomeSet

/-- The collecting set containing exactly `value`. -/
def singleton (value : Summary) : OutcomeSet Summary :=
  fun candidate => candidate = value

/-- Pointwise simultaneous composition of two collecting sets. -/
def combine (operation : Summary -> Summary -> Summary) (left right : OutcomeSet Summary)
    : OutcomeSet Summary :=
  fun outcome =>
    ∃ leftOutcome rightOutcome,
      left leftOutcome ∧ right rightOutcome ∧ outcome = operation leftOutcome rightOutcome

/-- Alternative composition of two collecting sets. -/
def union (left right : OutcomeSet Summary) : OutcomeSet Summary :=
  fun outcome => left outcome ∨ right outcome

/-- Relational image of a set under a possibly nondeterministic concrete step. -/
def bind {ResultSummary : Type v} (source : OutcomeSet Summary)
    (next : Summary -> OutcomeSet ResultSummary)
    : OutcomeSet ResultSummary :=
  fun outcome => ∃ input, source input ∧ next input outcome

end OutcomeSet

-----------------------------------------------------------------------------------------
-- Exact-case optimality contract for analyses
-----------------------------------------------------------------------------------------

namespace ExactCases

/-- Analysis-generic semantics of recursively feasible exact cases. `combine` supplies
simultaneous composition; `fieldOutcomes` supplies the modeled results of one collected
response-name group. -/
structure OutcomeSemantics where
  Summary : Type u
  empty : Summary
  combine : Summary -> Summary -> Summary
  fieldOutcomes : CollectedFieldGroup -> Summary -> OutcomeSet Summary

/-- Local laws requiring every abstract transfer to preserve best bounds through the
exact traversal. -/
structure BestTransferLaws (semantics : OutcomeSemantics.{u}) (abstract : Algebra.{v})
    (le : abstract.Summary -> abstract.Summary -> Prop)
    : Type (max u v) where
  approximates : semantics.Summary -> abstract.Summary -> Prop
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

/-- A total truth assignment shared by every response-name group and recursive child in
one feasible case. Concrete environments ignore it; symbolic environments consult it
only when traversal first reaches an unresolved variable. -/
abbrev BooleanAssignment := Name -> Bool

namespace BooleanAssignment

/-- A total assignment respects every Boolean value already fixed by the initial
environment. Values for unresolved variables remain unconstrained. -/
def Extends (assignment : BooleanAssignment) (environment : BooleanEnvironment) : Prop :=
  ∀ variableName value,
    environment.statusForVariable variableName = some value
    -> assignment variableName = value

end BooleanAssignment

/-- Records one total assignment for the listed variables. Symbolic environments gain
the corresponding case values; concrete environments remain unchanged because the
request already fixes every directive result. -/
def BooleanEnvironment.assignVariables (environment : BooleanEnvironment)
    (variables : BooleanVariableNames) (assignment : BooleanAssignment)
    : BooleanEnvironment :=
  variables.foldl
    (fun current variableName =>
      current.assign variableName (assignment variableName))
    environment

mutual
  /-- One feasible outcome in the relational semantics of the incremental cursor. The
  relation chooses one local type region and follows one globally consistent Boolean
  assignment; it does not invoke the executable summary fold or mention an analysis
  algebra. -/
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

  /-- All response-name groups at one boundary use the same assignment and environment,
  ruling out inconsistent choices for repeated variables in sibling groups. -/
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

  /-- A recursively selected field group chooses one feasible child output type while
  retaining the assignment shared by the enclosing response boundary. -/
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

/-- Feasible outcomes of an extracted condition tree under an explicit initial context.
This definition is independent of the executable fold and abstract analysis. -/
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

/-- Feasible outcomes of a selection hierarchy under an explicit initial context. -/
def selectionSetOutcomes (semantics : OutcomeSemantics.{u})
    (schema : Schema) (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (selectionSet : List Selection) (initial : BooleanEnvironment)
    : OutcomeSet semantics.Summary :=
  conditionTreeOutcomes semantics schema inheritedBooleanCondition
    (ConditionTree.ofSelectionSetInScopeWithKnownFalsePruning schema parentType
      inheritedBooleanCondition initial.pruningValues selectionSet)
    initial

/-- Feasible outcomes of an operation with every Boolean variable initially unresolved. -/
def operationOutcomes (semantics : OutcomeSemantics.{u})
    (schema : Schema) (operation : Operation)
    : OutcomeSet semantics.Summary :=
  selectionSetOutcomes semantics schema (operation.rootType schema) []
    operation.selectionSet BooleanEnvironment.unresolved

/-- Feasible outcomes after applying operation defaults and supplied values. -/
def operationOutcomesWithVariables (semantics : OutcomeSemantics.{u})
    (schema : Schema) (variableValues : VariableValues) (operation : Operation)
    : OutcomeSet semantics.Summary :=
  let coercedVariableValues := Execution.coerceVariableValues operation variableValues
  selectionSetOutcomes semantics schema (operation.rootType schema) []
    operation.selectionSet
    (BooleanEnvironment.concrete coercedVariableValues)

end ExactCases

-----------------------------------------------------------------------------------------
-- Exact-case summary optimality statements
-----------------------------------------------------------------------------------------

namespace ExactCases

/-- Per-operation optimality of the default exact-case analysis. Its generic witness is
`ExactCases.analysisOptimal`. -/
def AnalysisOptimal
    {semantics : OutcomeSemantics.{u}} {abstract : Algebra.{v}}
    {le : abstract.Summary -> abstract.Summary -> Prop}
    (laws : BestTransferLaws semantics abstract le)
    (schema : Schema) (operation : Operation)
    : Prop :=
  BestBound le laws.approximates (operationOutcomes semantics schema operation)
    (summarizeOperation abstract schema operation)

/-- Per-operation optimality of a variable-aware exact-case analysis. Its generic witness
is `ExactCases.analysisWithVariablesOptimal`. -/
def AnalysisWithVariablesOptimal
    {semantics : OutcomeSemantics.{u}}
    (abstractFor : VariableValues -> Algebra.{v})
    (schema : Schema) (variableValues : VariableValues) (operation : Operation)
    {le
      : (abstractFor (Execution.coerceVariableValues operation variableValues)).Summary
        -> (abstractFor (Execution.coerceVariableValues operation variableValues)).Summary
        -> Prop}
    (laws
      : BestTransferLaws semantics
          (abstractFor (Execution.coerceVariableValues operation variableValues)) le)
    : Prop :=
  BestBound le laws.approximates
    (operationOutcomesWithVariables semantics schema variableValues operation)
    (summarizeOperationWithVariables abstractFor schema variableValues operation)

end ExactCases

-----------------------------------------------------------------------------------------
-- Relational outcome semantics: adequacy statements
-----------------------------------------------------------------------------------------

namespace OutcomeSet

/-- `candidate` is a common abstract upper bound of every modeled outcome. -/
def IsUpperBound {AbstractSummary : Type v}
    (approximates : Summary -> AbstractSummary -> Prop)
    (outcomes : OutcomeSet Summary) (candidate : AbstractSummary)
    : Prop :=
  ∀ outcome, outcomes outcome -> approximates outcome candidate

end OutcomeSet

namespace ExactCases

-----------------------------------------------------------------------------------------
-- Execution coverage
-----------------------------------------------------------------------------------------

/-- Semantic exhaustiveness of modeled outcomes at one active selection-set boundary.
Every common abstract bound of the recursively feasible outcomes also bounds every
annotated execution result. Error/null bubbling at the boundary contributes the
concrete algebra's empty result. Its theorem witness is
`ExactCases.selectionSetExecutionCovered` in the exact-case optimality proof module. -/
def SelectionSetExecutionCovered
    {semantics : OutcomeSemantics.{u}} {concrete : ConcreteAlgebra.{v}}
    {abstract : Algebra.{w}} {schema : Schema} (variableValues : VariableValues)
    (soundness : Soundness concrete abstract schema variableValues)
    (laws : BestTransferLaws semantics abstract soundness.abstractLawful.le)
    (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (selectionSet : List Selection)
    : Prop :=
  ∀ (ObjectRef : Type) (resolvers : Resolvers ObjectRef)
    (fuel : Nat) (runtimeType : Name) (ref : ObjectRef),
    booleanConditionAllows variableValues inheritedBooleanCondition = true
    -> schema.typeIncludesObject parentType runtimeType
    ->  let source : ResolverValue ObjectRef := .object runtimeType ref
        let runtimeGroups :=
          collectFields schema variableValues runtimeType source selectionSet
        let executionResult :=
          AnnotatedExecution.executeQueryAnnotatedCollectedFields schema resolvers
            variableValues fuel source runtimeGroups
        let concreteOutcome := foldAnnotatedResponseFieldsResult concrete executionResult
        ∀ candidate,
          OutcomeSet.IsUpperBound laws.approximates
            (selectionSetOutcomes semantics schema parentType inheritedBooleanCondition
              selectionSet (BooleanEnvironment.concrete variableValues))
            candidate
          -> soundness.approximates concreteOutcome candidate

-----------------------------------------------------------------------------------------
-- Boolean-case exactness
-----------------------------------------------------------------------------------------

/-- Resolving one previously unknown Boolean variable partitions the same modeled
outcomes into its false and true cofactors. Outcome values may coincide, so this is an
exhaustive union rather than a disjointness claim. Its theorem witness is
`ExactCases.selectionSetBooleanSplitExact` in the exact-case optimality proof module. -/
def SelectionSetBooleanSplitExact
    (semantics : OutcomeSemantics.{u}) (schema : Schema) (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (selectionSet : List Selection) (initial : BooleanEnvironment)
    (variableName : Name)
    : Prop :=
  initial.statusForVariable variableName = none
  -> ∀ outcome,
      selectionSetOutcomes semantics schema parentType inheritedBooleanCondition
        selectionSet initial outcome
      ↔ selectionSetOutcomes semantics schema parentType inheritedBooleanCondition
          selectionSet (initial.assign variableName false) outcome
        ∨ selectionSetOutcomes semantics schema parentType inheritedBooleanCondition
            selectionSet (initial.assign variableName true) outcome

/-- Outcomes are exactly the union of assignments that resolve every Boolean variable
occurring in the extracted selection hierarchy. Assigning a symbolic environment
preserves its initial pruning policy, so this statement isolates Boolean case enumeration
from the separately modeled known-false extraction optimization. Its theorem witness is
`ExactCases.selectionSetResolvedAssignmentsExact` in the exact-case optimality proof
module. -/
def SelectionSetResolvedAssignmentsExact
    (semantics : OutcomeSemantics.{u}) (schema : Schema) (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (selectionSet : List Selection) (initial : BooleanEnvironment)
    : Prop :=
  let tree :=
    ConditionTree.ofSelectionSetInScopeWithKnownFalsePruning schema parentType
      inheritedBooleanCondition initial.pruningValues selectionSet
  let variables := (conditionTreeBooleanVariables tree).eraseDups
  ∀ outcome,
    selectionSetOutcomes semantics schema parentType inheritedBooleanCondition
      selectionSet initial outcome
    ↔ ∃ assignment : BooleanAssignment,
        assignment.Extends initial
        ∧ selectionSetOutcomes semantics schema parentType
            inheritedBooleanCondition selectionSet
            (initial.assignVariables variables assignment)
            outcome

-----------------------------------------------------------------------------------------
-- Outcome inhabitance
-----------------------------------------------------------------------------------------

/-- Local field-transfer totality is a simple sufficient condition under which recursive
case enumeration cannot get stuck at an analysis-defined field step. -/
def OutcomeSemantics.FieldOutcomesInhabited (semantics : OutcomeSemantics.{u}) : Prop :=
  ∀ group children, ∃ outcome, semantics.fieldOutcomes group children outcome

/-- Every selection hierarchy has at least one modeled outcome whenever every local
field transfer admits an outcome. Empty type scopes contribute `semantics.empty`. Its
theorem witness is `ExactCases.selectionSetOutcomesInhabited` in the exact-case
optimality proof module. -/
def SelectionSetOutcomesInhabited
    (semantics : OutcomeSemantics.{u}) (schema : Schema) (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (selectionSet : List Selection) (initial : BooleanEnvironment)
    : Prop :=
  semantics.FieldOutcomesInhabited
  -> ∃ outcome,
      selectionSetOutcomes semantics schema parentType inheritedBooleanCondition
        selectionSet initial outcome

-----------------------------------------------------------------------------------------
-- Runtime field-group adequacy
-----------------------------------------------------------------------------------------

/-- Observes the collected response-name groups at one selection-set boundary while
deliberately ignoring recursively modeled child outcomes. This semantics compares the
outcome specification with runtime `collectFields` independently of an analysis. -/
def OutcomeSemantics.boundaryFieldGroups : OutcomeSemantics :=
  {
    Summary := List CollectedFieldGroup
    empty := []
    combine := List.append
    fieldOutcomes := fun group _children => OutcomeSet.singleton [group]
  }

/-- A statically collected group list and a runtime group list contain the same response
names and executable field occurrences, up to the order intentionally ignored by field
collection. The runtime parent type is inserted into the static fields during conversion.
Executable fields retain their response name, so flattened-field agreement also retains
each occurrence's response-name association. This is a heterogeneous matching relation,
not a homogeneous equivalence relation. -/
structure CollectedGroupsMatchRuntimeGroups
    (runtimeType : Name) (collected : List CollectedFieldGroup)
    (runtime : List (Name × List ExecutableField))
    : Prop where
  keysPerm : (collected.map CollectedFieldGroup.responseName).Perm (runtime.map Prod.fst)
  fieldsPerm
    : ((collected.map fun group => group.toExecutableGroup runtimeType).flatMap
        Prod.snd).Perm
        (runtime.flatMap Prod.snd)

/-- At one complete request context, the feasible exact cases collect exactly the
response-name groups selected by runtime `collectFields`. The forward direction
represents every runtime object type by a modeled case; the reverse direction gives every
modeled case a feasible runtime object-type representative. The statement uses a
field-group observation of `OutcomeSemantics`, so it is independent of an analysis
algebra and its summary order. Its theorem witness is
`ExactCases.selectionSetRuntimeGroupsExact` in the exact-case optimality proof module. -/
def SelectionSetRuntimeGroupsExact
    (schema : Schema) (variableValues : VariableValues) (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (selectionSet : List Selection)
    : Prop :=
  let cases :=
    selectionSetOutcomes OutcomeSemantics.boundaryFieldGroups schema parentType
      inheritedBooleanCondition selectionSet
      (BooleanEnvironment.concrete variableValues)
  (∃ runtimeType, schema.typeIncludesObject parentType runtimeType)
  -> booleanConditionAllows variableValues inheritedBooleanCondition = true
  -> (∀ runtimeType,
        schema.typeIncludesObject parentType runtimeType
        -> ∃ groups,
            cases groups
            ∧ CollectedGroupsMatchRuntimeGroups runtimeType groups
                (collectFields schema variableValues runtimeType
                  (.object runtimeType () : ResolverValue Unit) selectionSet))
      ∧ (∀ groups,
          cases groups
          -> ∃ runtimeType,
              schema.typeIncludesObject parentType runtimeType
              ∧ CollectedGroupsMatchRuntimeGroups runtimeType groups
                  (collectFields schema variableValues runtimeType
                    (.object runtimeType () : ResolverValue Unit) selectionSet))

end ExactCases

end TreeSummary
end GraphQL
