import GraphQL.Theories.NormalForm

/-!
Non-spec response-shape syntax derived from complete-normal GraphQL operations.

The syntax keeps raw lists separate from validity predicates. This permits later
verified compaction without embedding ordering and uniqueness proofs in every
shape value.
-/

namespace GraphQL

namespace ResponseShape

/-- The name of one concrete object type represented by a shape. -/
abbrev GroundObject := Name

/-- A Boolean variable paired with the value required by a clause. -/
abbrev BoolLiteral := NormalForm.BoolVar × Bool

/-- A conjunction of Boolean literals. The empty conjunction represents true. -/
structure Clause where
  literals : List BoolLiteral
deriving Repr, DecidableEq

/-- Field identity and output information at one concrete response position. -/
structure FieldHead where
  fieldName : Name
  arguments : List Argument
  outputType : TypeRef
deriving Repr

mutual
  /-- Response positions selected from one object-valued response. -/
  inductive ResponseShape where
    | object : List ResponsePosition -> ResponseShape

  /-- One response name and its possible concrete definitions. -/
  inductive ResponsePosition where
    | mk :
        (responseName : Name) ->
        (possibleDefinitions : List PossibleDefinitions) ->
        ResponsePosition

  /-- Definitions that apply to a nonempty set of concrete object types. -/
  inductive PossibleDefinitions where
    | mk :
        (objectTypes : List GroundObject) ->
        (definitions : List ShapeDefinition) ->
        PossibleDefinitions

  /-- One guarded field definition and its optional composite child shape. -/
  inductive ShapeDefinition where
    | mk :
        (clause : Clause) ->
        (field : FieldHead) ->
        (subshape : Option ResponseShape) ->
        ShapeDefinition
end

deriving instance Repr for
  ResponseShape, ResponsePosition, PossibleDefinitions, ShapeDefinition

instance : Inhabited ResponseShape :=
  ⟨.object []⟩

/-- The response positions stored in a shape object. -/
def ResponseShape.positions : ResponseShape -> List ResponsePosition
  | .object positions => positions

/-- The response name represented by an entry. -/
def ResponsePosition.responseName : ResponsePosition -> Name
  | .mk responseName _possibleDefinitions => responseName

/-- The concrete-definition groups represented by an entry. -/
def ResponsePosition.possibleDefinitions
    : ResponsePosition -> List PossibleDefinitions
  | .mk _responseName possibleDefinitions => possibleDefinitions

/-- The concrete object types represented by a definition group. -/
def PossibleDefinitions.objectTypes : PossibleDefinitions -> List GroundObject
  | .mk objectTypes _definitions => objectTypes

/-- The guarded field definitions represented by a definition group. -/
def PossibleDefinitions.definitions
    : PossibleDefinitions -> List ShapeDefinition
  | .mk _objectTypes definitions => definitions

/-- The Boolean clause guarding a shape definition. -/
def ShapeDefinition.clause : ShapeDefinition -> Clause
  | .mk clause _field _subshape => clause

/-- The field head stored by a shape definition. -/
def ShapeDefinition.field : ShapeDefinition -> FieldHead
  | .mk _clause field _subshape => field

/-- The composite child shape stored by a shape definition, when present. -/
def ShapeDefinition.subshape : ShapeDefinition -> Option ResponseShape
  | .mk _clause _field subshape => subshape

/-- The shape of a complete operation together with its source Boolean support. -/
structure OperationShape where
  operationType : OperationType
  rootType : Name
  /-- Source-operation support, including variables whose cases normalize to empty. -/
  boolSupport : List NormalForm.BoolVar
  root : ResponseShape
deriving Repr

/-- One concrete field step in a response-shape path. -/
structure PathStep where
  parentObject : GroundObject
  responseName : Name
  field : FieldHead
deriving Repr

/-- A complete Boolean assignment paired with a nonempty response-shape path. -/
structure ShapeObligation where
  assignment : NormalForm.BoolCase
  path : List PathStep
deriving Repr

end ResponseShape

end GraphQL
