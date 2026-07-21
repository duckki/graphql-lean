import GraphQL.Operation

/-!
Common helpers for executable GraphQL algorithms.

These definitions are utilities used to compare selections. They are intentionally
syntax-level equality checks, not semantic field-merge or argument-equivalence predicates.
-/

namespace GraphQL

namespace Algorithms

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

def argumentEqBool (left right : Argument) : Bool :=
  (left.name == right.name) && inputValueEqBool left.value right.value

def argumentListEqBool : List Argument -> List Argument -> Bool
  | [], [] => true
  | left :: lefts, right :: rights =>
      argumentEqBool left right && argumentListEqBool lefts rights
  | _, _ => false

def directiveEqBool : DirectiveApplication -> DirectiveApplication -> Bool
  | .skip left, .skip right => inputValueEqBool left right
  | .include left, .include right => inputValueEqBool left right
  | _, _ => false

def directiveListEqBool : List DirectiveApplication -> List DirectiveApplication -> Bool
  | [], [] => true
  | left :: lefts, right :: rights =>
      directiveEqBool left right && directiveListEqBool lefts rights
  | _, _ => false

mutual
  def selectionEqBool : Selection -> Selection -> Bool
    | .field leftResponse leftName leftArguments leftDirectives leftSelections,
      .field rightResponse rightName rightArguments rightDirectives rightSelections =>
        (leftResponse == rightResponse)
        && (leftName == rightName)
        && argumentListEqBool leftArguments rightArguments
        && directiveListEqBool leftDirectives rightDirectives
        && selectionSetEqBool leftSelections rightSelections
    | .inlineFragment leftType leftDirectives leftSelections,
      .inlineFragment rightType rightDirectives rightSelections =>
        (leftType == rightType)
        && directiveListEqBool leftDirectives rightDirectives
        && selectionSetEqBool leftSelections rightSelections
    | _, _ => false

  def selectionSetEqBool : List Selection -> List Selection -> Bool
    | [], [] => true
    | left :: lefts, right :: rights =>
        selectionEqBool left right && selectionSetEqBool lefts rights
    | _, _ => false
end

end Algorithms

end GraphQL
