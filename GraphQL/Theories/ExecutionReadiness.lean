import GraphQL.Execution
import GraphQL.Theories.SelectionConditions

/-!
Static execution-readiness definitions shared by theories.

Boolean-support extraction identifies the variables used by conditional execution;
completeness says that an environment gives every variable in that support a concrete
Boolean value. The coercion predicates describe argument readiness for one concrete
supplied-variable environment. Concrete argument defaults support constructing
coercible environments after validation. These conditions supplement operation
validity: an otherwise valid operation may reject a particular runtime assignment.
-/

namespace GraphQL

open Execution

-----------------------------------------------------------------------------------------
-- Boolean variables from operation
-----------------------------------------------------------------------------------------

-- Boolean environments are shared by analyses that explore conditional selections.
-- A case supplies concrete Boolean values and may be layered over an existing runtime
-- environment.
abbrev BoolVar := Name

mutual
  def inputValueBooleanVariables : InputValue -> List BoolVar
    | .variable name => [name]
    | .list values => inputValuesBooleanVariables values
    | .object fields => inputObjectFieldsBooleanVariables fields
    | _ => []

  def inputValuesBooleanVariables : List InputValue -> List BoolVar
    | [] => []
    | value :: rest =>
        inputValueBooleanVariables value ++ inputValuesBooleanVariables rest

  def inputObjectFieldsBooleanVariables : List (Name × InputValue) -> List BoolVar
    | [] => []
    | (_name, value) :: rest =>
        inputValueBooleanVariables value ++ inputObjectFieldsBooleanVariables rest
end

def directiveBooleanVariables : DirectiveApplication -> List BoolVar
  | .skip ifArgument => inputValueBooleanVariables ifArgument
  | .include ifArgument => inputValueBooleanVariables ifArgument

def directivesBooleanVariables : List DirectiveApplication -> List BoolVar
  | [] => []
  | directive :: rest =>
      directiveBooleanVariables directive ++ directivesBooleanVariables rest

mutual
  def selectionBooleanVariables : Selection -> List BoolVar
    | .field _responseName _fieldName _arguments directives selectionSet =>
        directivesBooleanVariables directives ++ selectionSetBooleanVariables selectionSet
    | .inlineFragment _typeCondition directives selectionSet =>
        directivesBooleanVariables directives ++ selectionSetBooleanVariables selectionSet

  def selectionSetBooleanVariables : List Selection -> List BoolVar
    | [] => []
    | selection :: rest =>
        selectionBooleanVariables selection ++ selectionSetBooleanVariables rest
end

def boolVariableMem (varName : BoolVar) : List BoolVar -> Bool
  | [] => false
  | candidate :: rest =>
      if candidate == varName then true else boolVariableMem varName rest

def dedupBoolVars : List BoolVar -> List BoolVar
  | [] => []
  | varName :: rest =>
      let dedupedRest := dedupBoolVars rest
      if boolVariableMem varName dedupedRest then
        dedupedRest
      else
        varName :: dedupedRest

-- Named operation-global Boolean-variable support used by execution and normalization
-- theories.
def operationBoolVars (operation : Operation) : List BoolVar :=
  dedupBoolVars (selectionSetBooleanVariables operation.selectionSet)

-----------------------------------------------------------------------------------------
-- Boolean variable assignment completeness
-----------------------------------------------------------------------------------------

-- A runtime variable environment is complete for a Boolean-variable support when
-- every variable in that support resolves to a Boolean value.
def boolVarsComplete (variables : List BoolVar) (variableValues : VariableValues)
    : Prop :=
  ∀ varName,
    varName ∈ variables
    -> ∃ value, inputValueBoolean? variableValues (.variable varName) = some value

def operationBoolVarsComplete (operation : Operation) (variableValues : VariableValues)
    : Prop :=
  boolVarsComplete (operationBoolVars operation) variableValues

-----------------------------------------------------------------------------------------
-- Boolean variable assignments
-----------------------------------------------------------------------------------------

abbrev BoolCase := List (BoolVar × Bool)

def boolCaseVariableValues (boolCase : BoolCase) (base : VariableValues := [])
    : VariableValues :=
  boolCase.map (fun entry => (entry.1, .boolean entry.2)) ++ base

-----------------------------------------------------------------------------------------
-- Argument coercion safety
-----------------------------------------------------------------------------------------

mutual
  def selectionArgumentsCoercible (schema : Schema)
      (variableValues : VariableValues) (parentType : Name)
      : Selection -> Prop
    | .field _responseName fieldName arguments directives selectionSet =>
        selectionDirectivesAllowBool variableValues directives = true
        -> ∀ definition,
            schema.lookupField parentType fieldName = some definition
            -> (coerceArgumentValues schema variableValues definition.arguments
                    arguments).isSuccess
                  = true
                ∧ ∀ runtimeType,
                    schema.typeIncludesObjectBool definition.outputType.namedType
                        runtimeType
                      = true
                    -> selectionSetArgumentsCoercible schema variableValues runtimeType
                        selectionSet
    | .inlineFragment typeCondition directives selectionSet =>
        selectionDirectivesAllowBool variableValues directives = true
        -> (match typeCondition with
            | none => True
            | some condition =>
                schema.typeIncludesObjectBool condition parentType = true)
        -> selectionSetArgumentsCoercible schema variableValues parentType selectionSet

  def selectionSetArgumentsCoercible (schema : Schema)
      (variableValues : VariableValues) (parentType : Name)
      : List Selection -> Prop
    | [] => True
    | selection :: rest =>
        selectionArgumentsCoercible schema variableValues parentType selection
        ∧ selectionSetArgumentsCoercible schema variableValues parentType rest
end

def operationArgumentsCoercible (schema : Schema)
    (suppliedValues : VariableValues) (operation : Operation)
    : Prop :=
  selectionSetArgumentsCoercible schema
    (coerceVariableValues operation suppliedValues) (operation.rootType schema)
    operation.selectionSet

-----------------------------------------------------------------------------------------
-- Field output type inhabitance
-----------------------------------------------------------------------------------------

-- A non-null, non-list composite return needs a possible object type to admit an
-- error-free value. A nullable return can be null, and a list return (even a non-null
-- list of non-null objects) can be empty. Runtime-type and directive conditions are
-- not themselves required to be feasible: an impossible inline-fragment scope
-- contributes no field-execution obligation. The selected-field predicate applies
-- this condition only to composite output types. Repeated non-null wrappers are
-- invalid schema syntax; the recursive case supports proofs over raw type refs.
def nonNullNonListOutputTypeInhabited (schema : Schema) : TypeRef -> Prop
  | .nonNull (.named typeName) =>
      schema.getPossibleTypes typeName ≠ []
  | .nonNull (.nonNull inner) =>
      nonNullNonListOutputTypeInhabited schema (.nonNull inner)
  | _ => True

mutual
  def selectionCompositeFieldTypesInhabited (schema : Schema)
      (variableValues : VariableValues) (parentType : Name)
      : Selection -> Prop
    | .field _ fieldName _ directives selectionSet =>
        selectionDirectivesAllowBool variableValues directives = true
        -> ∀ definition,
            schema.lookupField parentType fieldName = some definition
            -> definition.outputType.isCompositeBool schema = true
            -> nonNullNonListOutputTypeInhabited schema definition.outputType
                ∧ ∀ runtimeType,
                    schema.typeIncludesObjectBool definition.outputType.namedType
                        runtimeType
                      = true
                    -> selectionSetCompositeFieldTypesInhabited schema variableValues
                        runtimeType selectionSet
    | .inlineFragment none directives selectionSet =>
        selectionDirectivesAllowBool variableValues directives = true
        -> selectionSetCompositeFieldTypesInhabited schema variableValues parentType
            selectionSet
    | .inlineFragment (some typeCondition) directives selectionSet =>
        selectionDirectivesAllowBool variableValues directives = true
        -> schema.typeIncludesObjectBool typeCondition parentType = true
        -> selectionSetCompositeFieldTypesInhabited schema variableValues parentType
            selectionSet

  def selectionSetCompositeFieldTypesInhabited (schema : Schema)
      (variableValues : VariableValues) (parentType : Name)
      (selectionSet : List Selection)
      : Prop :=
    ∀ selection,
      selection ∈ selectionSet
      -> selectionCompositeFieldTypesInhabited schema variableValues parentType selection
end

-- Every environment must have inhabited outputs on its enabled execution paths.
-- Keeping one environment throughout the traversal preserves correlated conditions.
def operationCompositeFieldTypesInhabited (schema : Schema) (operation : Operation)
    : Prop :=
  ∀ variableValues,
    selectionSetCompositeFieldTypesInhabited schema variableValues
      (operation.rootType schema) operation.selectionSet

-----------------------------------------------------------------------------------------
-- Required argument defaults in possible runtime types
-----------------------------------------------------------------------------------------

-- Operation validation checks supplied arguments at their declared field location.
-- A concrete implementation can omit a default from that location. For an omitted
-- non-null argument, execution then has no value to coerce, regardless of variables.
def omittedNonNullArgumentsHaveDefaults (definitions : List InputValueDefinition)
    (arguments : List Argument)
    : Prop :=
  ∀ definition,
    definition ∈ definitions
    -> definition.inputType.isNonNull = true
    -> Argument.lookupValue? arguments definition.name = none
    -> definition.defaultValue.isSome = true

def omittedNonNullArgumentsHaveDefaultsBool (definitions : List InputValueDefinition)
    (arguments : List Argument)
    : Bool :=
  definitions.all
    fun definition =>
      !definition.inputType.isNonNull
      || (Argument.lookupValue? arguments definition.name).isSome
      || definition.defaultValue.isSome

mutual
  def selectionCoercibleInPossibleTypes (schema : Schema)
      (variableValues : VariableValues) (parentType : Name)
      : Selection -> Prop
    | .field _ fieldName arguments directives children =>
        selectionDirectivesAllowBool variableValues directives = true
        -> match schema.lookupField parentType fieldName with
            | none => True
            | some definition =>
                omittedNonNullArgumentsHaveDefaults definition.arguments arguments
                ∧ ∀ objectType,
                    objectType ∈ schema.getPossibleTypes definition.outputType.namedType
                    -> selectionSetCoercibleInPossibleTypes schema variableValues
                        objectType children
    | .inlineFragment none directives children =>
        selectionDirectivesAllowBool variableValues directives = true
        -> selectionSetCoercibleInPossibleTypes schema variableValues parentType children
    | .inlineFragment (some condition) directives children =>
        selectionDirectivesAllowBool variableValues directives = true
        -> schema.typeIncludesObjectBool condition parentType = true
        -> selectionSetCoercibleInPossibleTypes schema variableValues parentType children

  def selectionSetCoercibleInPossibleTypes (schema : Schema)
      (variableValues : VariableValues) (parentType : Name)
      : List Selection -> Prop
    | [] => True
    | selection :: rest =>
        selectionCoercibleInPossibleTypes schema variableValues parentType selection
        ∧ selectionSetCoercibleInPossibleTypes schema variableValues parentType rest
end

-- Supplement to validation under a well-formed schema, sufficient for constructing
-- coercible, fully supplied environments. Only paths enabled in an environment impose
-- obligations; fragments retain the enclosing runtime object type.
-- Related spec issue: https://github.com/graphql/graphql-spec/issues/1121
def operationCoercibleInPossibleTypes (schema : Schema) (operation : Operation) : Prop :=
  ∀ variableValues,
    selectionSetCoercibleInPossibleTypes schema variableValues (operation.rootType schema)
      operation.selectionSet

-----------------------------------------------------------------------------------------
-- Static execution-error checker
-----------------------------------------------------------------------------------------

namespace ExecutionReadiness

-- Counts failed local obligations, once per field occurrence and feasible runtime
-- object scope. They are diagnostic counts, not the error count of a response.
-- Distinct source branches and object implementations are counted separately.
structure Result where
  argumentDefaultErrors : Nat := 0
  uninhabitedOutputErrors : Nat := 0
deriving Repr, BEq, DecidableEq

namespace Result

def errorCount (result : Result) : Nat :=
  result.argumentDefaultErrors + result.uninhabitedOutputErrors

def isSuccess (result : Result) : Bool :=
  result.errorCount == 0

def add (left right : Result) : Result :=
  {
    argumentDefaultErrors := left.argumentDefaultErrors + right.argumentDefaultErrors
    uninhabitedOutputErrors :=
      left.uninhabitedOutputErrors + right.uninhabitedOutputErrors
  }

end Result

def nonNullNonListOutputTypeInhabitedBool (schema : Schema) : TypeRef -> Bool
  | .nonNull (.named typeName) => !(schema.getPossibleTypes typeName).isEmpty
  | .nonNull (.nonNull inner) =>
      nonNullNonListOutputTypeInhabitedBool schema (.nonNull inner)
  | _ => true

-- A conjunction of signed variables suffices for modeled skip/include directives.
-- Conditions are inherited across field boundaries; sibling branches remain independent.
def withDirectives? (condition : List SelectionConditions.BooleanLiteral)
    (directives : List DirectiveApplication)
    : Option (List SelectionConditions.BooleanLiteral) := do
  let literals ← SelectionConditions.literalsForDirectives directives
  SelectionConditions.canonicalBooleanCondition (condition ++ literals)

mutual
  def checkSelection (schema : Schema)
      (runtimeType : Name) (condition : List SelectionConditions.BooleanLiteral)
      : Selection -> Result
    | .field _ fieldName arguments directives children =>
        match withDirectives? condition directives with
        | none => {}
        | some nextCondition =>
            match schema.lookupField runtimeType fieldName with
            | none => {}
            | some definition =>
                let localErrors : Result :=
                  {
                    argumentDefaultErrors :=
                      if omittedNonNullArgumentsHaveDefaultsBool definition.arguments
                          arguments then
                        0
                      else
                        1
                    uninhabitedOutputErrors :=
                      if definition.outputType.isCompositeBool schema
                          && !nonNullNonListOutputTypeInhabitedBool schema
                                definition.outputType then
                        1
                      else
                        0
                  }
                (schema.getPossibleTypes definition.outputType.namedType).foldl
                  (fun errors childType =>
                    errors.add
                      (checkSelectionSet schema childType nextCondition children))
                  localErrors
    | .inlineFragment typeCondition directives children =>
        if typeCondition.any
            (fun typeName =>
              !schema.typeIncludesObjectBool typeName runtimeType) then
          {}
        else
          match withDirectives? condition directives with
          | none => {}
          | some nextCondition =>
              checkSelectionSet schema runtimeType nextCondition children

  def checkSelectionSet (schema : Schema)
      (runtimeType : Name) (condition : List SelectionConditions.BooleanLiteral)
      : List Selection -> Result
    | [] => {}
    | selection :: rest =>
        (checkSelection schema runtimeType condition selection).add
          (checkSelectionSet schema runtimeType condition rest)
end

end ExecutionReadiness

-- Static checks corresponding to concrete argument defaults and composite-output
-- inhabitance, with infeasible type and Boolean branches pruned. Intended for validated
-- operations under well-formed schemas. No supplied values, resolvers, or Boolean-case
-- enumeration are needed. An omitted non-null argument validated at an interface must
-- have a default there; this checks that its concrete implementation also has one.
-- Supplied arguments are already validated and need no default check. Variable defaults
-- do not fix Boolean feasibility, since callers can override them. Nullable and list
-- returns do not suppress feasible descendants. Counts describe errors on feasible
-- branches, not a guarantee that every execution reaches those branches.
def checkExecutionError (schema : Schema) (operation : Operation)
    : ExecutionReadiness.Result :=
  ExecutionReadiness.checkSelectionSet schema
    (operation.rootType schema) [] operation.selectionSet

-----------------------------------------------------------------------------------------
-- Checker correctness
-----------------------------------------------------------------------------------------

-- Zero diagnostic counts certify both readiness predicates on feasible paths.
def CheckExecutionErrorSound (schema : Schema) (operation : Operation) : Prop :=
  (checkExecutionError schema operation).errorCount = 0
  -> operationCompositeFieldTypesInhabited schema operation
      ∧ operationCoercibleInPossibleTypes schema operation

-- Operations satisfying both predicates have no checker errors.
def CheckExecutionErrorComplete (schema : Schema) (operation : Operation) : Prop :=
  operationCompositeFieldTypesInhabited schema operation
    ∧ operationCoercibleInPossibleTypes schema operation
  -> (checkExecutionError schema operation).errorCount = 0

end GraphQL
