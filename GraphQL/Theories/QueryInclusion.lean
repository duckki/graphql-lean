import GraphQL.SchemaWellFormedness
import GraphQL.Theories.ResponsePath

/-! Syntactic GraphQL query inclusion over selected response paths. -/

namespace GraphQL
namespace QueryInclusion

open Execution

-----------------------------------------------------------------------------------------
-- Variables used by modeled conditional directives
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
-- Shared variable definitions and comparison condition variables
-----------------------------------------------------------------------------------------

-- The definitions on the left whose names are also declared on the right. Query-inclusion
-- correctness uses this projection together with operation validity, which rejects
-- duplicate variable names.
def variableDefinitionsSharedWith (left right : List VariableDefinition)
    : List VariableDefinition :=
  left.filter
    fun definition =>
      right.any fun candidate => candidate.name == definition.name

-- Only names declared by both operations are constrained. Their raw types and defaults
-- must agree; definition order and definitions occurring on only one side remain free.
def sharedVariableDefinitionsSyntacticallyCompatible
    (left right : List VariableDefinition)
    : Prop :=
  variableDefinitionsSyntacticallyEquivalent
    (variableDefinitionsSharedWith left right)
    (variableDefinitionsSharedWith right left)

instance sharedVariableDefinitionsSyntacticallyCompatibleDecidable
    : DecidableRel sharedVariableDefinitionsSyntacticallyCompatible :=
  fun _left _right => by
    unfold sharedVariableDefinitionsSyntacticallyCompatible
    infer_instance

def sharedVariableDefinitionsSyntacticallyCompatibleBool
    (left right : List VariableDefinition)
    : Bool :=
  decide (sharedVariableDefinitionsSyntacticallyCompatible left right)

-- The complete Boolean environment for comparing two selection sets is their union.
-- Occurrence order and duplicate uses do not affect conditional execution.
def comparisonConditionVariables (left right : List Selection) : List Name :=
  (selectionSetBooleanVariables left ++ selectionSetBooleanVariables right).eraseDups

-----------------------------------------------------------------------------------------
-- Path-based syntactic query inclusion
-----------------------------------------------------------------------------------------

-- Syntactic inclusion compares selected response paths under every complete Boolean
-- assignment over the comparison conditions. Path steps carry the right operation's
-- argument syntax; their matcher handles argument reordering and field provenance.
-- One-sided variable definitions are unrestricted.
def includes (schema : Schema) (left right : Operation) : Prop :=
  sharedVariableDefinitionsSyntacticallyCompatible left.variableDefinitions
    right.variableDefinitions
  ∧ ∀ (assignment : BoolCase),
      boolVarsComplete
        (comparisonConditionVariables left.selectionSet right.selectionSet)
        (boolCaseVariableValues assignment)
      -> ∀ path,
          ResponsePath.operationSelectsPath schema right assignment path
          -> ResponsePath.operationSelectsPath schema left assignment path

-----------------------------------------------------------------------------------------
-- Common implementation utilities
-----------------------------------------------------------------------------------------

def executableFieldsMergedSelectionSet (fields : List ExecutableField) : List Selection :=
  fields.flatMap ExecutableField.selectionSet

-----------------------------------------------------------------------------------------
-- Exhaustive query-inclusion decision procedure (reference implementation)
-----------------------------------------------------------------------------------------

-- Field collection observes an object source only through its runtime type. A unit ref
-- therefore gives the checker a canonical source for each possible runtime object.
def collectRuntimeFieldGroups (schema : Schema) (variableValues : VariableValues)
    (parentType runtimeType : Name) (selectionSet : List Selection)
    : List (Name × List ExecutableField) :=
  Execution.collectFields schema variableValues parentType
    (.object runtimeType PUnit.unit) selectionSet

def executableGroupIncludedBool (schema : Schema)
    (parentType : Name)
    (childIncludes : TypeRef -> List Selection -> List Selection -> Bool)
    (leftGroups : List (Name × List ExecutableField))
    (rightGroup : Name × List ExecutableField)
    : Bool :=
  leftGroups.any
    fun leftGroup =>
      leftGroup.1 == rightGroup.1
      && match leftGroup.2, rightGroup.2 with
          | leftField :: _leftRest, rightField :: _rightRest =>
              leftField.fieldName == rightField.fieldName
              && Argument.argumentsSyntacticallyEquivalentBool leftField.arguments
                  rightField.arguments
              && match schema.lookupField parentType rightField.fieldName with
                  | none => false
                  | some definition =>
                      if definition.outputType.isCompositeBool schema then
                        childIncludes definition.outputType
                          (executableFieldsMergedSelectionSet leftGroup.2)
                          (executableFieldsMergedSelectionSet rightGroup.2)
                      else
                        true
          | _, _ => false

def executableGroupsIncludeBool (schema : Schema)
    (parentType : Name)
    (childIncludes : TypeRef -> List Selection -> List Selection -> Bool)
    (leftGroups rightGroups : List (Name × List ExecutableField))
    : Bool :=
  rightGroups.all
    fun rightGroup =>
      executableGroupIncludedBool schema parentType childIncludes leftGroups rightGroup

mutual
  -- Compares one concrete runtime-object case.
  def selectionSetIncludesAtRuntimeBoolWithFuel (schema : Schema) (fuel : Nat)
      (parentType runtimeType : Name)
      (variableValues : VariableValues)
      (leftSelectionSet rightSelectionSet : List Selection)
      : Bool :=
    match fuel with
    | 0 =>
        (collectRuntimeFieldGroups schema variableValues parentType runtimeType
          rightSelectionSet).isEmpty
    | fuel + 1 =>
        let leftGroups :=
          collectRuntimeFieldGroups schema variableValues parentType runtimeType
            leftSelectionSet
        let rightGroups :=
          collectRuntimeFieldGroups schema variableValues parentType runtimeType
            rightSelectionSet
        executableGroupsIncludeBool schema parentType
          (fun outputType leftSelectionSet rightSelectionSet =>
            (schema.getPossibleTypes outputType.namedType).all
              fun childRuntimeType =>
                selectionSetIncludesBoolWithFuel schema fuel childRuntimeType
                  variableValues leftSelectionSet rightSelectionSet)
          leftGroups rightGroups

  -- Compares the field groups active for every possible runtime type under one
  -- Boolean assignment, then recursively compares composite children. `fuel` bounds
  -- nested response-field descent.
  def selectionSetIncludesBoolWithFuel (schema : Schema) (fuel : Nat) (parentType : Name)
      (variableValues : VariableValues)
      (leftSelectionSet rightSelectionSet : List Selection)
      : Bool :=
    (schema.getPossibleTypes parentType).all
      fun runtimeType =>
        selectionSetIncludesAtRuntimeBoolWithFuel schema fuel parentType runtimeType
          variableValues leftSelectionSet rightSelectionSet
end

-- Every total Boolean assignment over the variables that can affect modeled directives.
-- Because each variable is explicitly present, operation defaults cannot affect field
-- collection in these cases.
def booleanVariableAssignments : List Name -> List VariableValues
  | [] => [[]]
  | variableName :: rest =>
      let tailCases : List VariableValues := booleanVariableAssignments rest
      let falseCases : List VariableValues :=
        tailCases.map
          fun values => (variableName, ConstInputValue.boolean false) :: values
      let trueCases : List VariableValues :=
        tailCases.map fun values => (variableName, ConstInputValue.boolean true) :: values
      falseCases ++ trueCases

-- Exhaustively checks every Boolean assignment and possible runtime type. The checker
-- is total on raw syntax; correctness is stated below for well-formed schemas and valid
-- operations. Its soundness proof is the talk exercise.
def includesBoolReference (schema : Schema) (left right : Operation) : Bool :=
  if left.rootType schema == right.rootType schema
      && sharedVariableDefinitionsSyntacticallyCompatibleBool left.variableDefinitions
          right.variableDefinitions then
    let parentType := right.rootType schema
    let variables := comparisonConditionVariables left.selectionSet right.selectionSet
    let fuel := right.size + 1
    booleanVariableAssignments variables
    |>.all
        fun variableValues =>
          selectionSetIncludesBoolWithFuel schema fuel parentType
            variableValues left.selectionSet right.selectionSet
  else
    false

-----------------------------------------------------------------------------------------
-- `includesBoolReference` soundness and completeness statements
-----------------------------------------------------------------------------------------

-- Acceptance implies selected-path inclusion for valid operations under a well-formed
-- schema. This proposition is the target of the soundness proof exercise; defining the
-- statement does not prove it.
def IncludesBoolReferenceSound (schema : Schema) (left right : Operation) : Prop :=
  SchemaWellFormedness.schemaWellFormed schema
  -> Validation.operationDefinitionValid schema left
  -> Validation.operationDefinitionValid schema right
  -> includesBoolReference schema left right = true
  -> includes schema left right

-- Conversely, selected-path inclusion implies acceptance under the same assumptions.
-- Shared-variable compatibility is already part of `includes`.
def IncludesBoolReferenceComplete (schema : Schema) (left right : Operation) : Prop :=
  SchemaWellFormedness.schemaWellFormed schema
  -> Validation.operationDefinitionValid schema left
  -> Validation.operationDefinitionValid schema right
  -> includes schema left right
  -> includesBoolReference schema left right = true

end QueryInclusion
end GraphQL
