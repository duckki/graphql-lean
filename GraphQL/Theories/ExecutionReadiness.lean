import GraphQL.Execution

/-!
Static execution-readiness definitions shared by theories.

Boolean-support extraction identifies the variables used by conditional execution;
completeness says that an environment gives every variable in that support a concrete
Boolean value. The coercion predicates describe argument readiness for one concrete
supplied-variable environment. Both readiness conditions are deliberately separate
from operation validity: an otherwise valid operation may reject a particular runtime
assignment.
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

-- Argument-coercion readiness for every concrete runtime object represented by a
-- possibly abstract parent type.
def selectionSetArgumentsCoercibleInPossibleTypes (schema : Schema)
    (variableValues : VariableValues) (parentType : Name)
    (selectionSet : List Selection)
    : Prop :=
  ∀ runtimeType,
    schema.typeIncludesObjectBool parentType runtimeType = true
    -> selectionSetArgumentsCoercible schema variableValues runtimeType selectionSet

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
  def selectionCompositeFieldTypesInhabited (schema : Schema) (parentType : Name)
      : Selection -> Prop
    | .field _responseName fieldName _arguments _directives selectionSet =>
        ∀ definition,
          schema.lookupField parentType fieldName = some definition
          -> definition.outputType.isCompositeBool schema = true
          -> nonNullNonListOutputTypeInhabited schema definition.outputType
              ∧ ∀ runtimeType,
                  schema.typeIncludesObjectBool definition.outputType.namedType
                      runtimeType
                    = true
                  -> selectionSetCompositeFieldTypesInhabited schema runtimeType
                      selectionSet
    | .inlineFragment none _directives selectionSet =>
        selectionSetCompositeFieldTypesInhabited schema parentType selectionSet
    | .inlineFragment (some typeCondition) _directives selectionSet =>
        schema.typeIncludesObjectBool typeCondition parentType = true
        -> selectionSetCompositeFieldTypesInhabited schema parentType selectionSet

  def selectionSetCompositeFieldTypesInhabited (schema : Schema)
      (parentType : Name) (selectionSet : List Selection)
      : Prop :=
    ∀ selection,
      selection ∈ selectionSet
      -> selectionCompositeFieldTypesInhabited schema parentType selection
end

def operationCompositeFieldTypesInhabited (schema : Schema) (operation : Operation)
    : Prop :=
  selectionSetCompositeFieldTypesInhabited schema (operation.rootType schema)
    operation.selectionSet

end GraphQL
