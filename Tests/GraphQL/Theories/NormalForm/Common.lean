import GraphQL.Theories.NormalForm

namespace GraphQL
namespace Tests
namespace NormalForm

open GraphQL.NormalForm

def rootType : Name := "Query"

def stringFieldDefinition (name : Name) : FieldDefinition :=
  { name := name, outputType := .named "String", arguments := [] }

def objectFieldDefinition (name typeName : Name) : FieldDefinition :=
  { name := name, outputType := .named typeName, arguments := [] }

def groundTypingSchema : Schema :=
  {
    queryType := rootType
    types :=
      [
        .object
          {
            name := rootType
            fields :=
              [
                objectFieldDefinition "hero" "Human",
                objectFieldDefinition "search" "Character"
              ]
            interfaces := []
          },
        .interface
          {
            name := "Character"
            fields :=
              [stringFieldDefinition "id", stringFieldDefinition "name"]
            interfaces := []
          },
        .object
          {
            name := "Human"
            fields :=
              [
                stringFieldDefinition "id",
                stringFieldDefinition "name",
                stringFieldDefinition "homePlanet",
                objectFieldDefinition "companion" "Character"
              ]
            interfaces := ["Character"]
          },
        .object
          {
            name := "Droid"
            fields :=
              [
                stringFieldDefinition "id",
                stringFieldDefinition "name",
                stringFieldDefinition "primaryFunction"
              ]
            interfaces := ["Character"]
          }
      ]
  }

def booleanVariableDefinition (name : Name) : VariableDefinition :=
  { name := name, typeRef := .nonNull (.named "Boolean") }

def operationWith (selectionSet : List Selection) : Operation :=
  {
    name := some "NormalFormSmoke"
    variableDefinitions :=
      [booleanVariableDefinition "x", booleanVariableDefinition "y"]
    selectionSet := selectionSet
  }

mutual
  def selectionWellFormedBool : Selection -> Bool
    | .field _responseName _fieldName _arguments _directives selectionSet =>
        selectionSetWellFormedBool selectionSet
    | .inlineFragment _typeCondition _directives selectionSet =>
        !selectionSet.isEmpty && selectionSetWellFormedBool selectionSet

  def selectionSetWellFormedBool : List Selection -> Bool
    | [] => true
    | selection :: rest =>
        selectionWellFormedBool selection && selectionSetWellFormedBool rest
end

def operationWellFormedBool (operation : Operation) : Bool :=
  !operation.selectionSet.isEmpty && selectionSetWellFormedBool operation.selectionSet

def listEqBool (eq : α -> α -> Bool) : List α -> List α -> Bool
  | [], [] => true
  | left :: lefts, right :: rights =>
      eq left right && listEqBool eq lefts rights
  | _, _ => false

def optionNameEqBool : Option Name -> Option Name -> Bool
  | none, none => true
  | some left, some right => left == right
  | _, _ => false

def typeRefEqBool : TypeRef -> TypeRef -> Bool
  | .named left, .named right => left == right
  | .list left, .list right => typeRefEqBool left right
  | .nonNull left, .nonNull right => typeRefEqBool left right
  | _, _ => false

mutual
  def inputValueEqBool : InputValue -> InputValue -> Bool
    | .null, .null => true
    | .int left, .int right => left == right
    | .float left, .float right => left == right
    | .string left, .string right => left == right
    | .boolean left, .boolean right => left == right
    | .enum left, .enum right => left == right
    | .variable left, .variable right => left == right
    | .list left, .list right => inputValueListEqBool left right
    | .object left, .object right => inputObjectFieldsEqBool left right
    | _, _ => false

  def inputValueListEqBool : List InputValue -> List InputValue -> Bool
    | [], [] => true
    | left :: lefts, right :: rights =>
        inputValueEqBool left right && inputValueListEqBool lefts rights
    | _, _ => false

  def inputObjectFieldsEqBool
      : List (Name × InputValue) -> List (Name × InputValue) -> Bool
    | [], [] => true
    | (leftName, leftValue) :: lefts, (rightName, rightValue) :: rights =>
        (leftName == rightName)
        && inputValueEqBool leftValue rightValue
        && inputObjectFieldsEqBool lefts rights
    | _, _ => false
end

mutual
  def constInputValueEqBool : ConstInputValue -> ConstInputValue -> Bool
    | .null, .null => true
    | .int left, .int right => left == right
    | .float left, .float right => left == right
    | .string left, .string right => left == right
    | .boolean left, .boolean right => left == right
    | .enum left, .enum right => left == right
    | .list left, .list right => constInputValueListEqBool left right
    | .object left, .object right => constInputObjectFieldsEqBool left right
    | _, _ => false

  def constInputValueListEqBool : List ConstInputValue -> List ConstInputValue -> Bool
    | [], [] => true
    | left :: lefts, right :: rights =>
        constInputValueEqBool left right && constInputValueListEqBool lefts rights
    | _, _ => false

  def constInputObjectFieldsEqBool
      : List (Name × ConstInputValue) -> List (Name × ConstInputValue) -> Bool
    | [], [] => true
    | (leftName, leftValue) :: lefts, (rightName, rightValue) :: rights =>
        (leftName == rightName)
        && constInputValueEqBool leftValue rightValue
        && constInputObjectFieldsEqBool lefts rights
    | _, _ => false
end

def optionConstInputValueEqBool : Option ConstInputValue -> Option ConstInputValue -> Bool
  | none, none => true
  | some left, some right => constInputValueEqBool left right
  | _, _ => false

def argumentEqBool (left right : Argument) : Bool :=
  (left.name == right.name) && inputValueEqBool left.value right.value

def variableDefinitionEqBool (left right : VariableDefinition) : Bool :=
  (left.name == right.name)
  && typeRefEqBool left.typeRef right.typeRef
  && optionConstInputValueEqBool left.defaultValue right.defaultValue

def directiveEqBool : DirectiveApplication -> DirectiveApplication -> Bool
  | .skip left, .skip right => inputValueEqBool left right
  | .include left, .include right => inputValueEqBool left right
  | _, _ => false

mutual
  def selectionEqBool : Selection -> Selection -> Bool
    | .field leftResponseName leftFieldName leftArguments leftDirectives leftSelectionSet,
      .field rightResponseName rightFieldName rightArguments rightDirectives
        rightSelectionSet =>
        (leftResponseName == rightResponseName)
        && (leftFieldName == rightFieldName)
        && listEqBool argumentEqBool leftArguments rightArguments
        && listEqBool directiveEqBool leftDirectives rightDirectives
        && selectionSetEqBool leftSelectionSet rightSelectionSet
    | .inlineFragment leftTypeCondition leftDirectives leftSelectionSet,
      .inlineFragment rightTypeCondition rightDirectives rightSelectionSet =>
        optionNameEqBool leftTypeCondition rightTypeCondition
        && listEqBool directiveEqBool leftDirectives rightDirectives
        && selectionSetEqBool leftSelectionSet rightSelectionSet
    | _, _ => false

  def selectionSetEqBool : List Selection -> List Selection -> Bool
    | [], [] => true
    | left :: lefts, right :: rights =>
        selectionEqBool left right && selectionSetEqBool lefts rights
    | _, _ => false
end

def operationEqBool (left right : Operation) : Bool :=
  optionNameEqBool left.name right.name
  && (left.operationType == right.operationType)
  && listEqBool variableDefinitionEqBool
      left.variableDefinitions right.variableDefinitions
  && selectionSetEqBool left.selectionSet right.selectionSet

def optionOperationEqBool : Option Operation -> Option Operation -> Bool
  | none, none => true
  | some left, some right => operationEqBool left right
  | _, _ => false

mutual
  def responseEqBool : Execution.ResponseValue -> Execution.ResponseValue -> Bool
    | .null, .null => true
    | .scalar left, .scalar right => left == right
    | .object left, .object right => responseFieldsEqBool left right
    | .list left, .list right => responseListEqBool left right
    | _, _ => false

  def responseListEqBool
      : List Execution.ResponseValue -> List Execution.ResponseValue -> Bool
    | [], [] => true
    | left :: lefts, right :: rights =>
        responseEqBool left right && responseListEqBool lefts rights
    | _, _ => false

  def responseFieldsEqBool
      : List (Name × Execution.ResponseValue) -> List (Name × Execution.ResponseValue)
        -> Bool
    | [], [] => true
    | (leftName, leftValue) :: lefts, (rightName, rightValue) :: rights =>
        (leftName == rightName)
        && responseEqBool leftValue rightValue
        && responseFieldsEqBool lefts rights
    | _, _ => false
end

syntax "field " str : term
syntax "field " str "{" term,* "}" : term
syntax "spread" "{" term,* "}" : term
syntax "on " str "{" term,* "}" : term
syntax "query" "{" term,* "}" : term

macro_rules
  | `(field $name:str) => do
      let term ← `(Selection.field $name $name [] [] [])
      pure term.raw
  | `(field $name:str { $selection,* }) => do
      let term ← `(Selection.field $name $name [] [] [$selection,*])
      pure term.raw
  | `(spread { $selection,* }) => do
      let term ← `(Selection.inlineFragment none [] [$selection,*])
      pure term.raw
  | `(on $typeCondition:str { $selection,* }) => do
      let term ← `(Selection.inlineFragment (some $typeCondition) [] [$selection,*])
      pure term.raw
  | `(query { $selection,* }) => do
      let term ← `(operationWith [$selection,*])
      pure term.raw

def completeNormalizationRootBoolCaseBranchesFor
    (variables : List BoolVar)
    (selectionSetForCase : BoolCase -> List Selection)
    : List Selection :=
  List.flatten
    ((allBoolCases variables).map
      (fun boolCase =>
        match selectionSetForCase boolCase with
        | [] => []
        | selection :: rest =>
            wrapWithBoolCase boolCase (selection :: rest)))

end NormalForm
end Tests
end GraphQL
