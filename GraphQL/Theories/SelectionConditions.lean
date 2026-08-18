import GraphQL.Execution

/-! Static Boolean and type conditions extracted from GraphQL selection sets.

This module contains the condition algebra shared by analyses of conditional selections.
It deliberately has no condition-tree representation: consumers can use the flat
conditioned-field stream directly or retain source paths in their own representation.

Extraction stops at nested response-field boundaries. Nested field selection sets remain
raw syntax and can be extracted independently by a recursive consumer.
-/

namespace GraphQL
namespace SelectionConditions

open GraphQL.Execution

-----------------------------------------------------------------------------------------
-- Modeled Boolean-variable support
-----------------------------------------------------------------------------------------

-- The variable controlled by one modeled conditional directive. Constant conditions and
-- unsupported directives contribute no variable to the condition support.
def directiveBooleanVariable? : DirectiveApplication -> Option Name
  | .skip (.variable variableName) => some variableName
  | .include (.variable variableName) => some variableName
  | _directive => none

mutual
  -- Variables are collected through nested field boundaries because a recursive
  -- consumer may analyze each child selection set independently.
  def selectionBooleanVariables : Selection -> List Name
    | .field _responseName _fieldName _arguments directives selectionSet =>
        directives.filterMap directiveBooleanVariable?
        ++ selectionSetBooleanVariables selectionSet
    | .inlineFragment _typeCondition directives selectionSet =>
        directives.filterMap directiveBooleanVariable?
        ++ selectionSetBooleanVariables selectionSet

  def selectionSetBooleanVariables : List Selection -> List Name
    | [] => []
    | selection :: rest =>
        selectionBooleanVariables selection ++ selectionSetBooleanVariables rest
end

-----------------------------------------------------------------------------------------
-- Conditions
-----------------------------------------------------------------------------------------

-- Intersection keeps the left list's order. Starting at the parent type's possible
-- types therefore gives equivalent intersections identical keys.
def intersectPossibleTypes (left right : List Name) : List Name :=
  left.filter (fun objectType => right.contains objectType)

-- Boolean literals contributed by modeled conditional directives. `positive x` means
-- `@include(if: $x)` and `negative x` means `@skip(if: $x)`.
inductive BooleanLiteral where
  | positive (variableName : Name)
  | negative (variableName : Name)
deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

namespace BooleanLiteral

def complement : BooleanLiteral -> BooleanLiteral
  | .positive variableName => .negative variableName
  | .negative variableName => .positive variableName

def variableName : BooleanLiteral -> Name
  | .positive variableName => variableName
  | .negative variableName => variableName

-- Boolean value that satisfies this literal.
def requiredValue : BooleanLiteral -> Bool
  | .positive _variableName => true
  | .negative _variableName => false

-- Canonical ordering is variable name first, then positive before negative.
def orderedBeforeOrEqual (left right : BooleanLiteral) : Bool :=
  if left.variableName == right.variableName then
    left.requiredValue || !right.requiredValue
  else
    decide (left.variableName ≤ right.variableName)

def toDirective : BooleanLiteral -> DirectiveApplication
  | .positive variableName => .include (.variable variableName)
  | .negative variableName => .skip (.variable variableName)

-- Runtime truth of one canonical Boolean literal.
def allows (variableValues : VariableValues) (literal : BooleanLiteral) : Bool :=
  directiveAllowsSelectionBool variableValues literal.toDirective

end BooleanLiteral

-- A directive that always allows its selection contributes no literal; `none`
-- represents a directive that never allows it and makes the governed selection
-- infeasible. An argument that does not resolve to a Boolean behaves like `false`
-- at runtime, so an unsupported `@skip` argument is a no-op while an unsupported
-- `@include` argument is infeasible.
def literalsForDirective : DirectiveApplication -> Option (List BooleanLiteral)
  | .include (.variable variableName) => some [.positive variableName]
  | .skip (.variable variableName) => some [.negative variableName]
  | .include (.boolean true) => some []
  | .include (.boolean false) => none
  | .skip (.boolean true) => none
  | .skip (.boolean false) => some []
  | .include _unsupportedArgument => none
  | .skip _unsupportedArgument => some []

def insertBooleanLiteral (literal : BooleanLiteral)
    : List BooleanLiteral -> Option (List BooleanLiteral)
  | [] => some [literal]
  | condition@(candidate :: rest) =>
      if literal == candidate then
        some condition
      else if literal.complement == candidate then
        none
      else if literal.orderedBeforeOrEqual candidate then
        some (literal :: condition)
      else
        match insertBooleanLiteral literal rest with
        | none => none
        | some inserted => some (candidate :: inserted)

-- A canonical conjunction is sorted and duplicate-free. The empty list is true;
-- `none` represents a positive/negative contradiction.
def canonicalBooleanCondition : List BooleanLiteral -> Option (List BooleanLiteral)
  | [] => some []
  | literal :: rest => do
      let condition ← canonicalBooleanCondition rest
      insertBooleanLiteral literal condition

-- Disjoint clauses describing the assignments in `condition` that do not satisfy
-- `cover`. Each missing literal splits off the branch that falsifies it and retains
-- the satisfying branch for the rest of `cover`. The input conditions are normally
-- canonical, but the construction and its runtime meaning do not depend on ordering.
def subtractBooleanCondition (condition : List BooleanLiteral)
    : List BooleanLiteral -> List (List BooleanLiteral)
  | [] => []
  | literal :: rest =>
      if condition.contains literal.complement then
        [condition]
      else if condition.contains literal then
        subtractBooleanCondition condition rest
      else
        (literal.complement :: condition)
        :: subtractBooleanCondition (literal :: condition) rest

-- Removes one cover from every still-uncovered clause.
def subtractBooleanConditions (conditions : List (List BooleanLiteral))
    (cover : List BooleanLiteral)
    : List (List BooleanLiteral) :=
  conditions.flatMap fun condition => subtractBooleanCondition condition cover

-- Clauses in `condition` that remain after subtracting the union of `covers`.
def uncoveredBooleanConditions
    : List (List BooleanLiteral)
      -> List (List BooleanLiteral) -> List (List BooleanLiteral)
  | conditions, [] => conditions
  | conditions, cover :: rest =>
      uncoveredBooleanConditions (subtractBooleanConditions conditions cover) rest

-- Whether every Boolean assignment satisfying `condition` also satisfies at least one
-- clause in `covers`. This symbolic subtraction avoids enumerating all assignments.
def booleanConditionCoveredByBool (condition : List BooleanLiteral)
    (covers : List (List BooleanLiteral))
    : Bool :=
  (uncoveredBooleanConditions [condition] covers).isEmpty

def literalsForDirectives : List DirectiveApplication -> Option (List BooleanLiteral)
  | [] => some []
  | directive :: rest => do
      let literals ← literalsForDirective directive
      let restLiterals ← literalsForDirectives rest
      pure (literals ++ restLiterals)

-- The cumulative type and Boolean condition of a source selection.
structure Condition where
  possibleTypes : List Name
  booleanCondition : List BooleanLiteral
deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

def rootCondition (schema : Schema) (parentType : Name) : Condition :=
  {
    possibleTypes := schema.getPossibleTypes parentType
    booleanCondition := []
  }

def booleanConditionAllows (variableValues : VariableValues) : List BooleanLiteral -> Bool
  | [] => true
  | literal :: rest =>
      literal.allows variableValues && booleanConditionAllows variableValues rest

-- Runtime truth of a cumulative condition.
def Condition.allows (variableValues : VariableValues) (runtimeType : Name)
    (condition : Condition)
    : Bool :=
  condition.possibleTypes.contains runtimeType
  && booleanConditionAllows variableValues condition.booleanCondition

-- Feasibility is relative to the globally inherited Boolean condition of the parent
-- field: its possible-type intersection is inhabited and its global Boolean
-- conjunction is satisfiable.
def Condition.FeasibleUnder (condition : Condition)
    (inheritedBooleanCondition : List BooleanLiteral)
    : Prop :=
  condition.possibleTypes ≠ []
  ∧ (canonicalBooleanCondition
      (inheritedBooleanCondition ++ condition.booleanCondition)).isSome

-- Each source-path edge contributes exactly one condition. An inline fragment is
-- expanded deterministically into its type condition first, followed by Boolean
-- literals in directive syntax order.
inductive BranchCondition where
  | typeCondition (typeName : Name)
  | booleanLiteral (literal : BooleanLiteral)
deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

namespace BranchCondition

def isTypeCondition : BranchCondition -> Bool
  | .typeCondition _typeName => true
  | .booleanLiteral _literal => false

def parentType (condition : BranchCondition) (currentParentType : Name) : Name :=
  match condition with
  | .typeCondition typeName => typeName
  | .booleanLiteral _literal => currentParentType

def toSelection (condition : BranchCondition) (selectionSet : List Selection)
    : Selection :=
  match condition with
  | .typeCondition typeName => .inlineFragment (some typeName) [] selectionSet
  | .booleanLiteral literal => .inlineFragment none [literal.toDirective] selectionSet

def allows (schema : Schema) (variableValues : VariableValues) (runtimeType : Name)
    : BranchCondition -> Bool
  | .typeCondition typeName => schema.typeIncludesObjectBool typeName runtimeType
  | .booleanLiteral literal => literal.allows variableValues

end BranchCondition

def branchConditionsForDirectives? (directives : List DirectiveApplication)
    : Option (List BranchCondition) := do
  let booleanLiterals ← literalsForDirectives directives
  pure (booleanLiterals.map BranchCondition.booleanLiteral)

def branchConditionsForInlineFragment? (typeCondition : Option Name)
    (directives : List DirectiveApplication)
    : Option (List BranchCondition) := do
  let booleanBranches ← branchConditionsForDirectives? directives
  pure (typeCondition.toList.map BranchCondition.typeCondition ++ booleanBranches)

def conditionForBranch? (schema : Schema)
    (inheritedBooleanCondition : List BooleanLiteral)
    (start : Condition) (branch : BranchCondition)
    : Option Condition :=
  match branch with
  | .typeCondition typeName =>
      let possibleTypes :=
        intersectPossibleTypes start.possibleTypes (schema.getPossibleTypes typeName)
      if possibleTypes.isEmpty then
        none
      else
        some { start with possibleTypes }
  | .booleanLiteral literal => do
      let candidate ← canonicalBooleanCondition (start.booleanCondition ++ [literal])
      let booleanCondition :=
        candidate.filter (fun item => !inheritedBooleanCondition.contains item)
      let _globalBooleanCondition ←
        canonicalBooleanCondition (inheritedBooleanCondition ++ booleanCondition)
      some { start with booleanCondition }

def conditionForBranches? (schema : Schema)
    (inheritedBooleanCondition : List BooleanLiteral)
    : Condition -> List BranchCondition -> Option Condition
  | start, [] => some start
  | start, branch :: rest => do
      let condition ← conditionForBranch? schema inheritedBooleanCondition start branch
      conditionForBranches? schema inheritedBooleanCondition condition rest

def parentTypeForBranches (start : Name) (branches : List BranchCondition) : Name :=
  branches.foldl (fun parentType branch => branch.parentType parentType) start

def booleanBranchConditions (branches : List BranchCondition) : List BranchCondition :=
  branches.filterMap
    fun branch =>
      match branch with
      | .typeCondition _typeName => none
      | .booleanLiteral literal => some (.booleanLiteral literal)

def branchConditionsAllow (schema : Schema) (variableValues : VariableValues)
    (runtimeType : Name)
    : List BranchCondition -> Bool
  | [] => true
  | branch :: rest =>
      branch.allows schema variableValues runtimeType
      && branchConditionsAllow schema variableValues runtimeType rest

-----------------------------------------------------------------------------------------
-- Flat extraction
-----------------------------------------------------------------------------------------

-- A response-field occurrence with its modeled directives removed. Nested selections
-- stay raw because they form a separate extraction boundary.
structure Field where
  responseName : Name
  fieldName : Name
  arguments : List Argument
  selectionSet : List Selection
deriving Repr

-- A field occurrence annotated by the cumulative condition under which it is active.
structure ConditionedField where
  condition : Condition
  field : Field
deriving Repr

def extractFields (schema : Schema) (inheritedBooleanCondition : List BooleanLiteral)
    (currentCondition : Condition)
    : List Selection -> List ConditionedField
  | [] => []
  | .field responseName fieldName arguments directives selectionSet :: rest =>
      let head :=
        match branchConditionsForDirectives? directives with
        | none => []
        | some nextBranches =>
            match conditionForBranches? schema inheritedBooleanCondition
                    currentCondition nextBranches with
            | none => []
            | some nextCondition =>
                [{
                  condition := nextCondition
                  field := { responseName, fieldName, arguments, selectionSet }
                }]
      head ++ extractFields schema inheritedBooleanCondition currentCondition rest
  | .inlineFragment typeCondition directives selectionSet :: rest =>
      let child :=
        match branchConditionsForInlineFragment? typeCondition directives with
        | none => []
        | some nextBranches =>
            match conditionForBranches? schema inheritedBooleanCondition
                    currentCondition nextBranches with
            | none => []
            | some nextCondition =>
                extractFields schema inheritedBooleanCondition nextCondition selectionSet
      child ++ extractFields schema inheritedBooleanCondition currentCondition rest
termination_by selectionSet => SelectionSet.size selectionSet
decreasing_by
  all_goals
    simp_wf
    simp_all [SelectionSet.size, Selection.size]
    omega

-- Extracts one selection-set boundary rooted at a named composite type.
def ofSelectionSetInScope (schema : Schema) (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral) (selectionSet : List Selection)
    : List ConditionedField :=
  extractFields schema inheritedBooleanCondition (rootCondition schema parentType)
    selectionSet

def ofSelectionSet (schema : Schema) (parentType : Name) (selectionSet : List Selection)
    : List ConditionedField :=
  ofSelectionSetInScope schema parentType [] selectionSet

-- Extracts a boundary whose root is an exact possible-object region rather than the
-- possible objects of one named interface or union.
def ofTypeRegion (schema : Schema) (region : List Name) (selectionSet : List Selection)
    : List ConditionedField :=
  extractFields schema [] { possibleTypes := region, booleanCondition := [] } selectionSet

-- Runtime interpretation of a flat conditioned-field boundary. The cumulative
-- condition is the complete gate; extracted fields no longer carry modeled directives.
def runtimeFields (variableValues : VariableValues)
    (executionParentType runtimeType : Name) (entries : List ConditionedField)
    : List ExecutableField :=
  entries.flatMap
    fun entry =>
      if entry.condition.allows variableValues runtimeType then
        [{
          parentType := executionParentType
          responseName := entry.field.responseName
          fieldName := entry.field.fieldName
          arguments := entry.field.arguments
          selectionSet := entry.field.selectionSet
        }]
      else
        []

end SelectionConditions
end GraphQL
