import Proofs.GraphQL.Theories.ResponseShape.Denotation
import Tests.GraphQL.Theories.ResponseShape.Compute

namespace GraphQL
namespace Tests
namespace ResponseShape

open GraphQL.ResponseShape

private def definitionActiveBool
    (assignment : NormalForm.BoolCase) (definition : ShapeDefinition) : Bool :=
  definition.clause.holdsInBool assignment

private def possibleDefinitionsDenoteSingletonBool
    (assignment : NormalForm.BoolCase) (runtimeObject : Name)
    (possible : PossibleDefinitions) : Bool :=
  decide (runtimeObject ∈ possible.objectTypes)
  && possible.definitions.any (definitionActiveBool assignment)

private def responsePositionDenotesSingletonBool
    (assignment : NormalForm.BoolCase) (runtimeObject responseName : Name)
    (position : ResponsePosition) : Bool :=
  decide (position.responseName = responseName)
  && position.possibleDefinitions.any
      (possibleDefinitionsDenoteSingletonBool assignment runtimeObject)

private def responseShapeDenotesSingletonBool
    (schema : Schema) (assignment : NormalForm.BoolCase)
    (parentType runtimeObject responseName : Name) :
    GraphQL.ResponseShape.ResponseShape -> Bool
  | .object positions =>
      schema.typeIncludesObjectBool parentType runtimeObject
      && positions.any
          (responsePositionDenotesSingletonBool
            assignment runtimeObject responseName)

private theorem responseShapeDenotesSingletonBool_sound
    (schema : Schema) (assignment : NormalForm.BoolCase)
    (parentType runtimeObject responseName : Name)
    (shape : GraphQL.ResponseShape.ResponseShape)
    (hdenotes : responseShapeDenotesSingletonBool schema assignment
      parentType runtimeObject responseName shape = true) :
    ∃ fieldHead,
      shape.DenotesPath schema assignment parentType
        [PathStep.mk runtimeObject responseName fieldHead] := by
  cases shape with
  | object positions =>
      rcases Bool.and_eq_true_iff.mp hdenotes with
        ⟨hruntime, hposition⟩
      rw [List.any_eq_true] at hposition
      rcases hposition with ⟨position, hpositionMem, hposition⟩
      rcases Bool.and_eq_true_iff.mp hposition with
        ⟨hresponseName, hpossible⟩
      rw [List.any_eq_true] at hpossible
      rcases hpossible with ⟨possible, hpossibleMem, hpossible⟩
      rcases Bool.and_eq_true_iff.mp hpossible with
        ⟨hruntimeMem, hdefinition⟩
      rw [List.any_eq_true] at hdefinition
      rcases hdefinition with ⟨definition, hdefinitionMem, hdefinition⟩
      have hresponseName' : position.responseName = responseName :=
        of_decide_eq_true hresponseName
      have hclause' : definition.clause.HoldsIn assignment :=
        (Clause.holdsInBool_iff assignment definition.clause).mp hdefinition
      refine ⟨definition.field, ?_⟩
      simpa [hresponseName'] using
        (GraphQL.ResponseShape.ResponseShape.DenotesPath.field
          (by
            simpa [Schema.typeIncludesObjectBool,
              Schema.typeIncludesObject] using hruntime)
          hpositionMem hpossibleMem (of_decide_eq_true hruntimeMem)
          hdefinitionMem hclause')

private def decodedRootOrEmpty
    : Except ShapeBuildError OperationShape ->
      GraphQL.ResponseShape.ResponseShape
  | .error _ => .object []
  | .ok shape => shape.root

/-- The Boolean fixture denotes its expected root field as a singleton path. -/
theorem twoVariableDenotesHeroPathSmoke :
    ∃ fieldHead,
      (decodedRootOrEmpty twoVariableShape).DenotesPath
        NormalForm.groundTypingSchema
        [("x", false), ("y", false)] "Query"
        [PathStep.mk "Query" "hero" fieldHead] := by
  apply responseShapeDenotesSingletonBool_sound
  native_decide

/-- Counts active stored definitions at a response name, following active parents. -/
def activeDefinitionsAtResponseNameWithDepth
    : Nat -> NormalForm.BoolCase -> Name ->
      GraphQL.ResponseShape.ResponseShape -> Nat
  | 0, _assignment, _responseName, _shape => 0
  | depth + 1, assignment, responseName, .object positions =>
      positions.foldl
        (fun count position =>
          count
          + position.possibleDefinitions.foldl
              (fun groupCount possible =>
                groupCount
                + possible.definitions.foldl
                    (fun definitionCount definition =>
                      if definition.clause.holdsInBool assignment then
                        definitionCount
                        + (if position.responseName == responseName then 1 else 0)
                        + match definition.subshape with
                          | none => 0
                          | some child =>
                              activeDefinitionsAtResponseNameWithDepth depth
                                assignment responseName child
                      else
                        definitionCount)
                    0)
              0)
        0

/-- Counts active definitions in a decoded fixture shape. -/
def activeDecodedDefinitionsAt
    (assignment : NormalForm.BoolCase) (responseName : Name)
    (decoded : Except ShapeBuildError OperationShape) : Nat :=
  match decoded with
  | .error _ => 0
  | .ok shape =>
      activeDefinitionsAtResponseNameWithDepth
        (responseShapeObservationSize shape.root)
        assignment responseName shape.root

/-- Clause activation selects exactly the expected two-variable fixture branch. -/
theorem twoVariableDenotationFalseFalseSmoke :
    activeDecodedDefinitionsAt
        [("x", false), ("y", false)] "hero" twoVariableShape = 1
      ∧ activeDecodedDefinitionsAt
          [("x", false), ("y", false)] "name" twoVariableShape = 0
      ∧ activeDecodedDefinitionsAt
          [("x", false), ("y", false)] "homePlanet" twoVariableShape = 1 := by
  native_decide

/-- Changing both assignment bits activates the complementary optional fields. -/
theorem twoVariableDenotationTrueTrueSmoke :
    activeDecodedDefinitionsAt
        [("x", true), ("y", true)] "hero" twoVariableShape = 1
      ∧ activeDecodedDefinitionsAt
          [("x", true), ("y", true)] "name" twoVariableShape = 1
      ∧ activeDecodedDefinitionsAt
          [("x", true), ("y", true)] "homePlanet" twoVariableShape = 0 := by
  native_decide

/-- Recursive denotation follows active parents into the nested fixture. -/
theorem nestedDenotationSmoke :
    activeDecodedDefinitionsAt
        [("x", false)] "id" nestedAbstractShape = 0
      ∧ activeDecodedDefinitionsAt
          [("x", true)] "id" nestedAbstractShape = 2 := by
  native_decide

end ResponseShape
end Tests
end GraphQL
