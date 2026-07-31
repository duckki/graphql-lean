import GraphQL.Algorithms.Common
import GraphQL.Theories.ResponseShape.Clause

/-! Executable validity predicates for response-shape syntax. -/

namespace GraphQL

namespace ResponseShape

/-- Semantic input-value equivalence after canonical object-field ordering. -/
def inputValueEquivalentBool (left right : InputValue) : Bool :=
  Algorithms.inputValueEqBool left.canonical right.canonical

/-- Executable semantic equivalence for one field argument. -/
def argumentEquivalentBool (left right : Argument) : Bool :=
  (left.name == right.name)
  && inputValueEquivalentBool left.value right.value

/-- Executable bilateral set equivalence for field argument lists. -/
def argumentsEquivalentBool (left right : List Argument) : Bool :=
  left.all (fun argument => right.any (argumentEquivalentBool argument))
  && right.all
      (fun argument =>
        left.any (fun candidate => argumentEquivalentBool candidate argument))

namespace GroundSet

/--
Checks that a concrete object set is nonempty, canonical, object-typed, and
contained in the possible objects of its parent scope.
-/
def validBool
    (schema : Schema) (parentType : Name)
    (objectTypes : List GroundObject) : Bool :=
  !objectTypes.isEmpty
  && ResponseShape.namesStrictlyIncreasing objectTypes
  && objectTypes.all
      (fun objectType =>
        NormalForm.objectTypeNameBool schema objectType
        && schema.typeIncludesObjectBool parentType objectType)

/-- A canonical nonempty concrete-object subset of a GraphQL output scope. -/
def Valid
    (schema : Schema) (parentType : Name)
    (objectTypes : List GroundObject) : Prop :=
  validBool schema parentType objectTypes = true

instance instDecidableValid
    (schema : Schema) (parentType : Name) (objectTypes : List GroundObject)
    : Decidable (Valid schema parentType objectTypes) := by
  unfold Valid
  infer_instance

end GroundSet

/-- Checks whether two definitions agree on the presence of a child shape. -/
def childKindsEqualBool
    (left right : ShapeDefinition) : Bool :=
  left.subshape.isSome == right.subshape.isSome

/-- Checks field identity, arguments, output type, and child kind compatibility. -/
def definitionsCompatibleBool
    (left right : ShapeDefinition) : Bool :=
  (left.field.fieldName == right.field.fieldName)
  && argumentsEquivalentBool left.field.arguments right.field.arguments
  && decide (left.field.outputType = right.field.outputType)
  && childKindsEqualBool left right

/-- Checks pairwise compatibility of a list of active definitions. -/
def definitionsPairwiseCompatibleBool : List ShapeDefinition -> Bool
  | [] => true
  | definition :: rest =>
      rest.all (definitionsCompatibleBool definition)
      && definitionsPairwiseCompatibleBool rest

/-- Selects the active definitions of one group for a concrete object. -/
def activeDefinitionsIn
    (objectType : GroundObject) (assignment : NormalForm.BoolCase)
    (possible : PossibleDefinitions) : List ShapeDefinition :=
  if possible.objectTypes.contains objectType then
    possible.definitions.filter
      (fun definition => definition.clause.holdsInBool assignment)
  else
    []

/-- Selects all active definitions for a concrete object across groups. -/
def activeDefinitions
    (objectType : GroundObject) (assignment : NormalForm.BoolCase)
    : List PossibleDefinitions -> List ShapeDefinition
  | [] => []
  | possible :: rest =>
      activeDefinitionsIn objectType assignment possible
      ++ activeDefinitions objectType assignment rest

/-- Checks that each applicable group has at most one active definition. -/
def applicableGroupsUnambiguousBool
    (objectType : GroundObject) (assignment : NormalForm.BoolCase)
    (groups : List PossibleDefinitions) : Bool :=
  groups.all
    (fun possible =>
      decide ((activeDefinitionsIn objectType assignment possible).length ≤ 1))

/-- Checks one response position at one object and Boolean assignment. -/
def responseCaseValidBool
    (objectType : GroundObject) (assignment : NormalForm.BoolCase)
    (position : ResponsePosition) : Bool :=
  applicableGroupsUnambiguousBool
      objectType assignment position.possibleDefinitions
  && definitionsPairwiseCompatibleBool
      (activeDefinitions objectType assignment position.possibleDefinitions)

/-- Checks all concrete objects and complete assignments for one position. -/
def responsePositionCasesValidBool
    (schema : Schema) (support : List NormalForm.BoolVar) (parentType : Name)
    (position : ResponsePosition) : Bool :=
  (schema.getPossibleTypes parentType).all
    (fun objectType =>
      (NormalForm.allBoolCases support).all
        (fun assignment => responseCaseValidBool objectType assignment position))

mutual
  /--
  Checks response-name uniqueness, concrete ground-set validity, guarded field
  compatibility for every object and complete assignment, and recursive child kind.
  -/
  def ResponseShape.wellFormedBool
      (schema : Schema) (support : List NormalForm.BoolVar) (parentType : Name)
      : ResponseShape -> Bool
    | .object positions =>
        decide (positions.map ResponsePosition.responseName).Nodup
        && responsePositionsWellFormedBool schema support parentType positions

  /-- Checks recursive well-formedness for a list of response positions. -/
  def responsePositionsWellFormedBool
      (schema : Schema) (support : List NormalForm.BoolVar) (parentType : Name)
      : List ResponsePosition -> Bool
    | [] => true
    | position :: rest =>
        position.wellFormedBool schema support parentType
        && responsePositionsWellFormedBool schema support parentType rest

  /-- Checks one response position and all of its concrete definition groups. -/
  def ResponsePosition.wellFormedBool
      (schema : Schema) (support : List NormalForm.BoolVar) (parentType : Name)
      : ResponsePosition -> Bool
    | .mk responseName possibleDefinitions =>
        responsePositionCasesValidBool schema support parentType
            (.mk responseName possibleDefinitions)
        && possibleDefinitionsWellFormedBool
            schema support parentType possibleDefinitions

  /-- Checks recursive well-formedness for concrete definition groups. -/
  def possibleDefinitionsWellFormedBool
      (schema : Schema) (support : List NormalForm.BoolVar) (parentType : Name)
      : List PossibleDefinitions -> Bool
    | [] => true
    | possible :: rest =>
        possible.wellFormedBool schema support parentType
        && possibleDefinitionsWellFormedBool schema support parentType rest

  /-- Checks one concrete object set and its guarded field definitions. -/
  def PossibleDefinitions.wellFormedBool
      (schema : Schema) (support : List NormalForm.BoolVar) (parentType : Name)
      : PossibleDefinitions -> Bool
    | .mk objectTypes definitions =>
        GroundSet.validBool schema parentType objectTypes
        && shapeDefinitionsWellFormedBool schema support definitions

  /-- Checks recursive well-formedness for guarded field definitions. -/
  def shapeDefinitionsWellFormedBool
      (schema : Schema) (support : List NormalForm.BoolVar)
      : List ShapeDefinition -> Bool
    | [] => true
    | definition :: rest =>
        definition.wellFormedBool schema support
        && shapeDefinitionsWellFormedBool schema support rest

  /-- Checks one clause, field output type, and optional recursive child. -/
  def ShapeDefinition.wellFormedBool
      (schema : Schema) (support : List NormalForm.BoolVar)
      : ShapeDefinition -> Bool
    | .mk clause field subshape =>
        clause.validBool support
        && if field.outputType.isCompositeBool schema then
            match subshape with
            | some child =>
                child.wellFormedBool schema support field.outputType.namedType
            | none => false
          else if NormalForm.leafTypeNameBool schema field.outputType.namedType then
            subshape.isNone
          else
            false
end

/-- A recursively valid response shape in one GraphQL output-type scope, with
duplicate-free declared Boolean support. -/
def ResponseShape.WellFormed
    (schema : Schema) (support : List NormalForm.BoolVar) (parentType : Name)
    (shape : ResponseShape) : Prop :=
  decide support.Nodup
  && shape.wellFormedBool schema support parentType
  = true

instance instDecidableResponseShapeWellFormed
    (schema : Schema) (support : List NormalForm.BoolVar) (parentType : Name)
    (shape : ResponseShape)
    : Decidable (shape.WellFormed schema support parentType) := by
  unfold ResponseShape.WellFormed
  infer_instance

/-- Operation-root consistency together with recursive shape well-formedness. -/
def OperationShape.WellFormed
    (schema : Schema) (shape : OperationShape) : Prop :=
  shape.rootType = shape.operationType.rootType schema
  ∧ shape.root.WellFormed schema shape.boolSupport shape.rootType

instance instDecidableOperationShapeWellFormed
    (schema : Schema) (shape : OperationShape)
    : Decidable (shape.WellFormed schema) := by
  unfold OperationShape.WellFormed
  infer_instance

mutual
  /-- Checks that every definition in a response shape uses a complete minterm. -/
  def ResponseShape.fullMintermBool
      (support : List NormalForm.BoolVar) : ResponseShape -> Bool
    | .object positions =>
        responsePositionsFullMintermBool support positions

  /-- Checks complete-minterm use for a list of response positions. -/
  def responsePositionsFullMintermBool
      (support : List NormalForm.BoolVar) : List ResponsePosition -> Bool
    | [] => true
    | position :: rest =>
        position.fullMintermBool support
        && responsePositionsFullMintermBool support rest

  /-- Checks complete-minterm use in one response position. -/
  def ResponsePosition.fullMintermBool
      (support : List NormalForm.BoolVar) : ResponsePosition -> Bool
    | .mk _responseName possibleDefinitions =>
        possibleDefinitionsFullMintermBool support possibleDefinitions

  /-- Checks complete-minterm use for concrete definition groups. -/
  def possibleDefinitionsFullMintermBool
      (support : List NormalForm.BoolVar) : List PossibleDefinitions -> Bool
    | [] => true
    | possible :: rest =>
        possible.fullMintermBool support
        && possibleDefinitionsFullMintermBool support rest

  /-- Checks complete-minterm use in one concrete definition group. -/
  def PossibleDefinitions.fullMintermBool
      (support : List NormalForm.BoolVar) : PossibleDefinitions -> Bool
    | .mk _objectTypes definitions =>
        shapeDefinitionsFullMintermBool support definitions

  /-- Checks complete-minterm use for guarded field definitions. -/
  def shapeDefinitionsFullMintermBool
      (support : List NormalForm.BoolVar) : List ShapeDefinition -> Bool
    | [] => true
    | definition :: rest =>
        definition.fullMintermBool support
        && shapeDefinitionsFullMintermBool support rest

  /-- Checks one guarded definition and its optional recursive child. -/
  def ShapeDefinition.fullMintermBool
      (support : List NormalForm.BoolVar) : ShapeDefinition -> Bool
    | .mk clause _field subshape =>
        clause.completeMintermBool support
        && match subshape with
          | none => true
          | some child => child.fullMintermBool support
end

/-- Every guarded definition in an operation shape uses a complete minterm. -/
def OperationShape.FullMinterm (shape : OperationShape) : Prop :=
  shape.root.fullMintermBool shape.boolSupport = true

instance instDecidableOperationShapeFullMinterm (shape : OperationShape)
    : Decidable shape.FullMinterm := by
  unfold OperationShape.FullMinterm
  infer_instance

mutual
  /--
  Strong validity for executable field heads. This remains proposition-valued
  because the repository's general input-value validation relation is inductive.
  -/
  def ResponseShape.ExecutableValid
      (schema : Schema) (variableDefinitions : List VariableDefinition)
      (support : List NormalForm.BoolVar) (parentType : Name)
      : ResponseShape -> Prop
    | shape@(.object positions) =>
        shape.WellFormed schema support parentType
        ∧ responsePositionsExecutableValid
            schema variableDefinitions support positions

  /-- Requires executable validity for a list of response positions. -/
  def responsePositionsExecutableValid
      (schema : Schema) (variableDefinitions : List VariableDefinition)
      (support : List NormalForm.BoolVar)
      : List ResponsePosition -> Prop
    | [] => True
    | position :: rest =>
        position.ExecutableValid schema variableDefinitions support
        ∧ responsePositionsExecutableValid
            schema variableDefinitions support rest

  /-- Requires executable validity for one response position. -/
  def ResponsePosition.ExecutableValid
      (schema : Schema) (variableDefinitions : List VariableDefinition)
      (support : List NormalForm.BoolVar)
      : ResponsePosition -> Prop
    | .mk _responseName possibleDefinitions =>
        possibleDefinitionsExecutableValid
          schema variableDefinitions support possibleDefinitions

  /-- Requires executable validity for concrete definition groups. -/
  def possibleDefinitionsExecutableValid
      (schema : Schema) (variableDefinitions : List VariableDefinition)
      (support : List NormalForm.BoolVar)
      : List PossibleDefinitions -> Prop
    | [] => True
    | possible :: rest =>
        possible.ExecutableValid schema variableDefinitions support
        ∧ possibleDefinitionsExecutableValid
            schema variableDefinitions support rest

  /-- Requires executable validity for one concrete definition group. -/
  def PossibleDefinitions.ExecutableValid
      (schema : Schema) (variableDefinitions : List VariableDefinition)
      (support : List NormalForm.BoolVar)
      : PossibleDefinitions -> Prop
    | .mk objectTypes definitions =>
        shapeDefinitionsExecutableValid
          schema variableDefinitions support objectTypes definitions

  /-- Requires executable validity for guarded field definitions. -/
  def shapeDefinitionsExecutableValid
      (schema : Schema) (variableDefinitions : List VariableDefinition)
      (support : List NormalForm.BoolVar) (objectTypes : List GroundObject)
      : List ShapeDefinition -> Prop
    | [] => True
    | definition :: rest =>
        definition.ExecutableValid
          schema variableDefinitions support objectTypes
        ∧ shapeDefinitionsExecutableValid
            schema variableDefinitions support objectTypes rest

  /-- Requires schema-valid arguments and recursively valid child fields. -/
  def ShapeDefinition.ExecutableValid
      (schema : Schema) (variableDefinitions : List VariableDefinition)
      (support : List NormalForm.BoolVar) (objectTypes : List GroundObject)
      : ShapeDefinition -> Prop
    | .mk _clause field subshape =>
        (∀ objectType,
            objectType ∈ objectTypes
            -> ∃ fieldDefinition,
                schema.lookupField objectType field.fieldName = some fieldDefinition
                ∧ field.outputType = fieldDefinition.outputType
                ∧ Validation.argumentsValid
                    schema fieldDefinition.arguments variableDefinitions
                    field.arguments)
        ∧ match subshape with
          | none => True
          | some child =>
              child.ExecutableValid
                schema variableDefinitions support field.outputType.namedType
end

/-- Operation-level executable validity for every concrete field definition. -/
def OperationShape.ExecutableValid
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (shape : OperationShape) : Prop :=
  shape.WellFormed schema
  ∧ shape.root.ExecutableValid
      schema variableDefinitions shape.boolSupport shape.rootType

end ResponseShape

end GraphQL
