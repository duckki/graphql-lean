import GraphQL.Theories.ResponseShape
import Tests.GraphQL.Theories.NormalForm.CompleteNormalization

namespace GraphQL
namespace Tests
namespace ResponseShape

open GraphQL.ResponseShape

mutual
  def responseShapeObservationSize
      : GraphQL.ResponseShape.ResponseShape -> Nat
    | .object positions => 1 + responsePositionObservationSizes positions

  def responsePositionObservationSizes : List ResponsePosition -> Nat
    | [] => 0
    | position :: rest =>
        responsePositionObservationSize position
        + responsePositionObservationSizes rest

  def responsePositionObservationSize : ResponsePosition -> Nat
    | .mk _responseName possibleDefinitions =>
        1 + possibleDefinitionObservationSizes possibleDefinitions

  def possibleDefinitionObservationSizes : List PossibleDefinitions -> Nat
    | [] => 0
    | possible :: rest =>
        possibleDefinitionObservationSize possible
        + possibleDefinitionObservationSizes rest

  def possibleDefinitionObservationSize : PossibleDefinitions -> Nat
    | .mk _objectTypes definitions =>
        1 + shapeDefinitionObservationSizes definitions

  def shapeDefinitionObservationSizes : List ShapeDefinition -> Nat
    | [] => 0
    | definition :: rest =>
        shapeDefinitionObservationSize definition
        + shapeDefinitionObservationSizes rest

  def shapeDefinitionObservationSize : ShapeDefinition -> Nat
    | .mk _clause _field none => 1
    | .mk _clause _field (some subshape) =>
        1 + responseShapeObservationSize subshape
end

def definitionsAtResponseNameWithDepth
    : Nat -> Name -> GraphQL.ResponseShape.ResponseShape -> Nat
  | 0, _responseName, _shape => 0
  | depth + 1, responseName, .object positions =>
      positions.foldl
        (fun count position =>
          let directCount :=
            if position.responseName == responseName then
              position.possibleDefinitions.foldl
                (fun subtotal possible =>
                  subtotal + possible.definitions.length)
                0
            else
              0
          let childCount :=
            position.possibleDefinitions.foldl
              (fun subtotal possible =>
                subtotal
                + possible.definitions.foldl
                    (fun definitionSubtotal definition =>
                      definitionSubtotal
                      + match definition.subshape with
                        | none => 0
                        | some child =>
                            definitionsAtResponseNameWithDepth
                              depth responseName child)
                    0)
              0
          count + directCount + childCount)
        0

def definitionsAtResponseName
    (responseName : Name) (shape : GraphQL.ResponseShape.ResponseShape) : Nat :=
  definitionsAtResponseNameWithDepth
    (responseShapeObservationSize shape) responseName shape

def decodedSupport
    (decoded : Except ShapeBuildError OperationShape)
    : List NormalForm.BoolVar :=
  match decoded with
  | .ok shape => shape.boolSupport
  | .error _ => []

def decodedDefinitionsAt
    (responseName : Name)
    (decoded : Except ShapeBuildError OperationShape) : Nat :=
  match decoded with
  | .ok shape => definitionsAtResponseName responseName shape.root
  | .error _ => 0

def decodedShapeValidBool
    (schema : Schema)
    (decoded : Except ShapeBuildError OperationShape) : Bool :=
  match decoded with
  | .ok shape =>
      decide (shape.WellFormed schema)
      && decide shape.FullMinterm
  | .error _ => false

def abstractShape :=
  computeOperationShape
    NormalForm.groundTypingSchema NormalForm.abstractFieldInputQuery

theorem decodeAbstractGroundingSmoke :
    decodedShapeValidBool NormalForm.groundTypingSchema abstractShape
    && decodedSupport abstractShape == []
    && decodedDefinitionsAt "search" abstractShape == 1
    && decodedDefinitionsAt "id" abstractShape == 2
    && decodedDefinitionsAt "homePlanet" abstractShape == 1 := by
  native_decide

def twoVariableShape :=
  computeOperationShape
    NormalForm.groundTypingSchema
    NormalForm.completeNormalizationDirectiveInputQuery

theorem decodeTwoVariableOperationSmoke :
    decodedShapeValidBool NormalForm.groundTypingSchema twoVariableShape
    && decodedSupport twoVariableShape == ["x", "y"]
    && decodedDefinitionsAt "hero" twoVariableShape == 4
    && decodedDefinitionsAt "id" twoVariableShape == 4
    && decodedDefinitionsAt "name" twoVariableShape == 2
    && decodedDefinitionsAt "homePlanet" twoVariableShape == 2 := by
  native_decide

def nestedAbstractShape :=
  computeOperationShape
    NormalForm.groundTypingSchema
    NormalForm.completeNormalizationNestedDirectiveInputQuery

theorem decodeNestedAbstractGroundingSmoke :
    decodedShapeValidBool NormalForm.groundTypingSchema nestedAbstractShape
    && decodedSupport nestedAbstractShape == ["x"]
    && decodedDefinitionsAt "hero" nestedAbstractShape == 2
    && decodedDefinitionsAt "companion" nestedAbstractShape == 2
    && decodedDefinitionsAt "id" nestedAbstractShape == 2 := by
  native_decide

def argumentFieldDefinition : FieldDefinition :=
  {
    name := "lookup"
    outputType := .named "String"
    arguments := [{ name := "term", inputType := .named "String" }]
  }

def argumentSchema : Schema :=
  {
    queryType := "Query"
    types :=
      [
        .object
          {
            name := "Query"
            fields := [argumentFieldDefinition]
          }
      ]
  }

def aliasedArgumentOperation : Operation :=
  {
    name := some "AliasedArgument"
    selectionSet :=
      [
        .field "matched" "lookup"
          [{ name := "term", value := .string "sample" }]
          [] []
      ]
  }

def aliasedArgumentShape :=
  computeOperationShape argumentSchema aliasedArgumentOperation

def decodedAliasedArgumentBool : Bool :=
  match aliasedArgumentShape with
  | .ok shape =>
      match shape.root.positions with
      | [position] =>
          match position.possibleDefinitions with
          | [possible] =>
              match possible.objectTypes, possible.definitions with
              | ["Query"], [ShapeDefinition.mk clause fieldHead none] =>
                  position.responseName == "matched"
                  && fieldHead.fieldName == "lookup"
                  && argumentsEquivalentBool fieldHead.arguments
                      [{ name := "term", value := .string "sample" }]
                  && clause.completeMintermBool []
                  && decide (shape.WellFormed argumentSchema)
              | _, _ => false
          | _ => false
      | _ => false
  | .error _ => false

theorem decodeAliasAndArgumentsSmoke :
    decodedAliasedArgumentBool := by
  native_decide

def emptyBooleanCasesOperation : Operation :=
  {
    name := some "EmptyBooleanCases"
    variableDefinitions :=
      [{ name := "x", typeRef := .nonNull (.named "Boolean") }]
    selectionSet :=
      [
        .field "matched" "lookup" []
          [.include (.variable "x"), .skip (.variable "x")]
          []
      ]
  }

def emptyBooleanCasesShape :=
  computeOperationShape argumentSchema emptyBooleanCasesOperation

theorem decodePreservesSupportWhenEveryCaseIsEmpty :
    decodedShapeValidBool argumentSchema emptyBooleanCasesShape
    && decodedSupport emptyBooleanCasesShape == ["x"]
    && match emptyBooleanCasesShape with
      | .ok shape => shape.root.positions.isEmpty
      | .error _ => false := by
  native_decide

def nonlexicalSupportOperation : Operation :=
  {
    name := some "NonlexicalSupport"
    variableDefinitions :=
      [
        { name := "z", typeRef := .nonNull (.named "Boolean") },
        { name := "a", typeRef := .nonNull (.named "Boolean") }
      ]
    selectionSet :=
      [
        .field "first" "lookup" [] [.include (.variable "z")] [],
        .field "second" "lookup" [] [.include (.variable "a")] []
      ]
  }

def nonlexicalSupportShape :=
  computeOperationShape argumentSchema nonlexicalSupportOperation

theorem decodeCanonicalizesClausesIndependentlyOfSupportOrder :
    decodedShapeValidBool argumentSchema nonlexicalSupportShape
    && decodedSupport nonlexicalSupportShape == ["z", "a"] := by
  native_decide

def malformedLeaf : Selection :=
  .field "matched" "lookup" [] [] []

def nonDirectiveStemResult : Except ShapeBuildError ResponseShape :=
  decodeCompleteRoot argumentSchema ["x"] "Query"
    [.inlineFragment none [] [malformedLeaf]]

def incompleteMintermResult : Except ShapeBuildError ResponseShape :=
  decodeCompleteRoot argumentSchema ["x", "y"] "Query"
    [
      .inlineFragment none
        [.include (.variable "x")]
        [malformedLeaf]
    ]

def duplicateStemVariableResult : Except ShapeBuildError ResponseShape :=
  decodeCompleteRoot argumentSchema ["x", "y"] "Query"
    [
      .inlineFragment none
        [.include (.variable "x")]
        [
          .inlineFragment none
            [.skip (.variable "x")]
            [malformedLeaf]
        ]
    ]

def rejectedWithBool
    (expected : ShapeBuildError)
    : Except ShapeBuildError ResponseShape -> Bool
  | .ok _shape => false
  | .error actual => decide (actual = expected)

theorem rejectNonDirectiveStemSmoke :
    rejectedWithBool
      (.booleanStemDirectiveCount 0) nonDirectiveStemResult := by
  native_decide

theorem rejectIncompleteMintermSmoke :
    rejectedWithBool .missingBooleanStem incompleteMintermResult := by
  native_decide

theorem rejectDuplicateStemVariableSmoke :
    rejectedWithBool
      (.duplicateStemVariable "x") duplicateStemVariableResult := by
  native_decide

end ResponseShape
end Tests
end GraphQL
