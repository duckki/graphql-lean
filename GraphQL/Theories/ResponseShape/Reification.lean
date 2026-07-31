import GraphQL.Theories.ResponseShape.Clause

/-!
Executable reification of full-minterm response shapes as complete-normal
GraphQL operation syntax.
-/

namespace GraphQL

namespace ResponseShape

mutual
  /-- Reifies one response shape in its GraphQL output-type scope. -/
  def ResponseShape.reifySelectionSet
      (schema : Schema) (assignment : NormalForm.BoolCase) (parentType : Name)
      : ResponseShape -> List Selection
    | .object positions =>
        if NormalForm.objectTypeNameBool schema parentType then
          reifyResponsePositions schema assignment parentType positions
        else
          (schema.getPossibleTypes parentType).filterMap
            (fun objectType =>
              match reifyResponsePositions schema assignment objectType positions with
              | [] => none
              | selections =>
                  some (.inlineFragment (some objectType) [] selections))

  /-- Reifies the active fields at every response position for one object. -/
  def reifyResponsePositions
      (schema : Schema) (assignment : NormalForm.BoolCase)
      (objectType : GroundObject)
      : List ResponsePosition -> List Selection
    | [] => []
    | position :: rest =>
        position.reifyFields schema assignment objectType
        ++ reifyResponsePositions schema assignment objectType rest

  /-- Reifies the active definitions of one response position for one object. -/
  def ResponsePosition.reifyFields
      (schema : Schema) (assignment : NormalForm.BoolCase)
      (objectType : GroundObject) : ResponsePosition -> List Selection
    | .mk responseName possibleDefinitions =>
        reifyPossibleDefinitions
          schema assignment objectType responseName possibleDefinitions

  /-- Reifies the definition groups applicable to one concrete object. -/
  def reifyPossibleDefinitions
      (schema : Schema) (assignment : NormalForm.BoolCase)
      (objectType : GroundObject) (responseName : Name)
      : List PossibleDefinitions -> List Selection
    | [] => []
    | possible :: rest =>
        possible.reifyFields schema assignment objectType responseName
        ++ reifyPossibleDefinitions
            schema assignment objectType responseName rest

  /-- Reifies a definition group when it contains the current object. -/
  def PossibleDefinitions.reifyFields
      (schema : Schema) (assignment : NormalForm.BoolCase)
      (objectType : GroundObject) (responseName : Name)
      : PossibleDefinitions -> List Selection
    | .mk objectTypes definitions =>
        if objectTypes.contains objectType then
          reifyShapeDefinitions schema assignment responseName definitions
        else
          []

  /-- Reifies the definitions whose clauses hold in the current assignment. -/
  def reifyShapeDefinitions
      (schema : Schema) (assignment : NormalForm.BoolCase)
      (responseName : Name) : List ShapeDefinition -> List Selection
    | [] => []
    | definition :: rest =>
        let reifiedRest :=
          reifyShapeDefinitions schema assignment responseName rest
        if definition.clause.holdsInBool assignment then
          definition.reifyField schema assignment responseName :: reifiedRest
        else
          reifiedRest

  /-- Reifies one active definition as a directive-free field selection. -/
  def ShapeDefinition.reifyField
      (schema : Schema) (assignment : NormalForm.BoolCase)
      (responseName : Name) : ShapeDefinition -> Selection
    | .mk _clause field subshape =>
        let selectionSet :=
          match subshape with
          | none => []
          | some child =>
              child.reifySelectionSet
                schema assignment field.outputType.namedType
        .field responseName field.fieldName field.arguments [] selectionSet
end

/--
Reifies every nonempty complete Boolean case of an operation shape. Empty cases
remain absent, so source Boolean support continues to live in `OperationShape`.
-/
def reifyCompleteSelectionSet
    (schema : Schema) (shape : OperationShape) : List Selection :=
  List.flatten
    ((NormalForm.allBoolCases shape.boolSupport).map
      (fun assignment =>
        match shape.root.reifySelectionSet schema assignment shape.rootType with
        | [] => []
        | selection :: rest =>
            NormalForm.wrapWithBoolCase assignment (selection :: rest)))

/-- Reifies an operation shape while retaining source operation metadata. -/
def reifyOperation
    (schema : Schema) (source : Operation) (shape : OperationShape) : Operation :=
  {
    source with
      operationType := shape.operationType
      selectionSet := reifyCompleteSelectionSet schema shape
  }

end ResponseShape

end GraphQL
