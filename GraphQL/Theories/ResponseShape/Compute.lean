import GraphQL.Theories.ResponseShape.Clause

/-!
Total decoding of complete-normal operations into response shapes.

The decoder checks the grammar emitted by `completeNormalizeOperation`: complete
Boolean stems at the root and directive-free, concrete-object-grounded bodies
below them. Acceptance is intentionally broader than provenance from that
normalizer; image-sensitive theorems retain the source operation and schema
premises.
-/

namespace GraphQL

namespace ResponseShape

/-- Typed failures produced while decoding purported complete-normal syntax. -/
inductive ShapeBuildError where
  | duplicateSupportVariable (varName : NormalForm.BoolVar)
  | missingBooleanStem
  | typedBooleanStem (typeCondition : Name)
  | booleanStemDirectiveCount (actual : Nat)
  | invalidBooleanStemDirective
  | booleanStemChildCount (remainingVariables actual : Nat)
  | emptyBooleanCase
  | stemVariableOutsideSupport (varName : NormalForm.BoolVar)
  | duplicateStemVariable (varName : NormalForm.BoolVar)
  /-- A directly checked stem omitted a support variable. Top-level decoding
  supplies exactly one literal per support entry, so it does not emit this. -/
  | missingStemVariable (varName : NormalForm.BoolVar)
  | duplicateBooleanCase
  | groundDirectivesRemain (actual : Nat)
  | selectionKindMismatch (parentType : Name)
  | duplicateResponseName (responseName : Name)
  | duplicateGroundObject (objectType : Name)
  | anonymousGroundFragment
  | nonObjectGroundFragment (typeCondition : Name)
  | impossibleTypeScope (parentType typeCondition : Name)
  | emptyGroundFragment (typeCondition : Name)
  | missingSchemaField (parentType fieldName : Name)
  | invalidFieldOutputType (fieldName typeName : Name)
  | leafFieldHasSubselections (fieldName : Name)
  | unknownTypeScope (typeName : Name)
  /-- The checked literals still failed the complete-minterm test. Top-level
  decoding rejects duplicate support first, but direct low-level calls can
  reach this fallback. -/
  | internalInvariantViolation
deriving Repr, DecidableEq

/-- Adds a definition group, merging only an identical concrete object set. -/
def insertPossibleDefinitions
    (incoming : PossibleDefinitions)
    : List PossibleDefinitions -> List PossibleDefinitions
  | [] => [incoming]
  | current :: rest =>
      if current.objectTypes == incoming.objectTypes then
        .mk current.objectTypes (current.definitions ++ incoming.definitions) :: rest
      else
        current :: insertPossibleDefinitions incoming rest

/-- Combines concrete definition groups while preserving their first-seen order. -/
def mergePossibleDefinitions
    (left right : List PossibleDefinitions) : List PossibleDefinitions :=
  right.foldl (fun merged incoming => insertPossibleDefinitions incoming merged) left

/-- Adds a response position, merging entries with the same response name. -/
def insertResponsePosition
    (incoming : ResponsePosition)
    : List ResponsePosition -> List ResponsePosition
  | [] => [incoming]
  | current :: rest =>
      if current.responseName == incoming.responseName then
        .mk current.responseName
          (mergePossibleDefinitions
            current.possibleDefinitions incoming.possibleDefinitions)
        :: rest
      else
        current :: insertResponsePosition incoming rest

/-- Combines response positions while preserving their first-seen order. -/
def mergeResponseShapes (left right : ResponseShape) : ResponseShape :=
  match left, right with
  | .object leftPositions, .object rightPositions =>
      .object
        (rightPositions.foldl
          (fun merged incoming => insertResponsePosition incoming merged)
          leftPositions)

/-- Builds the one-position shape contributed by a concrete field definition. -/
def singletonDefinitionShape
    (parentObject responseName : Name)
    (definition : ShapeDefinition) : ResponseShape :=
  .object [.mk responseName [.mk [parentObject] [definition]]]

/-- Checks whether a field selection uses a given response name. -/
def selectionHasResponseName (responseName : Name) : Selection -> Bool
  | .field candidate _fieldName _arguments _directives _selectionSet =>
      candidate == responseName
  | .inlineFragment .. => false

/-- Checks whether a typed inline fragment uses a given type condition. -/
def selectionHasTypeCondition (typeCondition : Name) : Selection -> Bool
  | .inlineFragment (some candidate) _directives _selectionSet =>
      candidate == typeCondition
  | _ => false

/-- Checks whether a schema name denotes an interface or union. -/
def abstractTypeNameBool (schema : Schema) (typeName : Name) : Bool :=
  match schema.lookupType typeName with
  | some (.interface _interfaceType) => true
  | some (.union _unionType) => true
  | _ => false

/--
Folds one directive-free ground selection set. Object scopes accept fields;
abstract scopes accept concrete typed fragments. Termination follows the same
`SelectionSet.size` metric as the normalizer.
-/
def foldGroundSelectionSet
    (schema : Schema) (clause : Clause) (parentType : Name)
    : (selectionSet : List Selection) -> Except ShapeBuildError ResponseShape
  | [] =>
      if NormalForm.objectTypeNameBool schema parentType
          || abstractTypeNameBool schema parentType then
        .ok (.object [])
      else
        .error (.unknownTypeScope parentType)
  | selection :: rest =>
      if NormalForm.objectTypeNameBool schema parentType then
        match selection with
        | .field responseName fieldName arguments directives selectionSet => do
            if !directives.isEmpty then
              .error (.groundDirectivesRemain directives.length)
            else if rest.any (selectionHasResponseName responseName) then
              .error (.duplicateResponseName responseName)
            else
              let fieldDefinition ←
                match schema.lookupField parentType fieldName with
                | some definition => .ok definition
                | none => .error (.missingSchemaField parentType fieldName)
              let outputTypeName := fieldDefinition.outputType.namedType
              let subshape ←
                if fieldDefinition.outputType.isCompositeBool schema then
                  let child ←
                    foldGroundSelectionSet schema clause outputTypeName selectionSet
                  .ok (some child)
                else if NormalForm.leafTypeNameBool schema outputTypeName then
                  if selectionSet.isEmpty then
                    .ok none
                  else
                    .error (.leafFieldHasSubselections fieldName)
                else
                  .error (.invalidFieldOutputType fieldName outputTypeName)
              let fieldHead : FieldHead :=
                {
                  fieldName := fieldName
                  arguments := arguments
                  outputType := fieldDefinition.outputType
                }
              let currentShape :=
                singletonDefinitionShape parentType responseName
                  (.mk clause fieldHead subshape)
              let restShape ←
                foldGroundSelectionSet schema clause parentType rest
              .ok (mergeResponseShapes currentShape restShape)
        | .inlineFragment .. =>
            .error (.selectionKindMismatch parentType)
      else if abstractTypeNameBool schema parentType then
        match selection with
        | .field .. =>
            .error (.selectionKindMismatch parentType)
        | .inlineFragment typeCondition directives selectionSet => do
            if !directives.isEmpty then
              .error (.groundDirectivesRemain directives.length)
            else
              let objectType ←
                match typeCondition with
                | some objectType => .ok objectType
                | none => .error .anonymousGroundFragment
              if rest.any (selectionHasTypeCondition objectType) then
                .error (.duplicateGroundObject objectType)
              else
                match schema.lookupObject objectType with
                | none => .error (.nonObjectGroundFragment objectType)
                | some _ =>
                    if !schema.typeIncludesObjectBool parentType objectType then
                      .error (.impossibleTypeScope parentType objectType)
                    else if selectionSet.isEmpty then
                      .error (.emptyGroundFragment objectType)
                    else
                      let currentShape ←
                        foldGroundSelectionSet schema clause objectType selectionSet
                      let restShape ←
                        foldGroundSelectionSet schema clause parentType rest
                      .ok (mergeResponseShapes currentShape restShape)
      else
        .error (.unknownTypeScope parentType)
termination_by selectionSet => SelectionSet.size selectionSet
decreasing_by
  all_goals
    simp [SelectionSet.size, Selection.size]
    omega

/-- Decodes one variable-valued `@include` or `@skip` stem directive. -/
def decodeStemDirective
    : DirectiveApplication -> Except ShapeBuildError BoolLiteral
  | .include (.variable varName) => .ok (varName, true)
  | .skip (.variable varName) => .ok (varName, false)
  | _ => .error .invalidBooleanStemDirective

/--
Decodes exactly the requested number of anonymous singleton-directive stem
layers and returns their literal list together with the final branch body.
-/
def decodeCompleteStem
    : (remainingVariables : Nat) -> Selection
      -> Except ShapeBuildError (List BoolLiteral × List Selection)
  | 0, _selection => .error .missingBooleanStem
  | remaining + 1, selection =>
      match selection with
      | .field .. => .error .missingBooleanStem
      | .inlineFragment (some typeCondition) _directives _body =>
          .error (.typedBooleanStem typeCondition)
      | .inlineFragment none directives body => do
          let directive ←
            match directives with
            | [directive] => .ok directive
            | _ => .error (.booleanStemDirectiveCount directives.length)
          let literal ← decodeStemDirective directive
          match remaining with
          | 0 =>
              if body.isEmpty then
                .error .emptyBooleanCase
              else
                .ok ([literal], body)
          | more + 1 =>
              match body with
              | [child] =>
                  let (restLiterals, branchBody) ←
                    decodeCompleteStem (more + 1) child
                  .ok (literal :: restLiterals, branchBody)
              | _ =>
                  .error
                    (.booleanStemChildCount (more + 1) body.length)

/-- Returns the first name whose value occurs again later in the list. -/
def firstDuplicate? : List Name -> Option Name
  | [] => none
  | candidate :: rest =>
      if rest.contains candidate then some candidate else firstDuplicate? rest

/-- Returns the first literal whose variable is outside the declared support. -/
def firstOutsideSupport?
    (support : List NormalForm.BoolVar) : List BoolLiteral -> Option NormalForm.BoolVar
  | [] => none
  | literal :: rest =>
      if support.contains literal.1 then
        firstOutsideSupport? support rest
      else
        some literal.1

/-- Returns the first support variable absent from a decoded literal list. -/
def firstMissingStemVariable?
    (literals : List BoolLiteral)
    : List NormalForm.BoolVar -> Option NormalForm.BoolVar
  | [] => none
  | varName :: rest =>
      if literals.any (fun literal => literal.1 == varName) then
        firstMissingStemVariable? literals rest
      else
        some varName

/-- Validates and canonicalizes the literal list decoded from one root stem. -/
def clauseFromCompleteStem
    (support : List NormalForm.BoolVar) (literals : List BoolLiteral)
    : Except ShapeBuildError Clause := do
  match firstOutsideSupport? support literals with
  | some varName => .error (.stemVariableOutsideSupport varName)
  | none =>
      match firstDuplicate? (literals.map Prod.fst) with
      | some varName => .error (.duplicateStemVariable varName)
      | none =>
          match firstMissingStemVariable? literals support with
          | some varName => .error (.missingStemVariable varName)
          | none =>
              let clause := Clause.canonical { literals := literals }
              if clause.completeMintermBool support then
                .ok clause
              else
                .error .internalInvariantViolation

/-- Executable equality used to reject repeated decoded Boolean cases. -/
def clausesEqualBool (left right : Clause) : Bool :=
  decide (left = right)

/--
Decodes nonempty-support root branches while retaining clauses already seen.
The state is exposed so proofs can state the invariant that generated Boolean
cases remain distinct throughout the fold.
-/
def decodeRootBranches
    (schema : Schema) (support : List NormalForm.BoolVar) (rootType : Name)
    (seen : List Clause)
    : List Selection -> Except ShapeBuildError ResponseShape
  | [] => .ok (.object [])
  | selection :: rest => do
      let (literals, branchBody) ← decodeCompleteStem support.length selection
      let clause ← clauseFromCompleteStem support literals
      if seen.any (clausesEqualBool clause) then
        .error .duplicateBooleanCase
      else
        let branchShape ←
          foldGroundSelectionSet schema clause rootType branchBody
        let restShape ←
          decodeRootBranches schema support rootType (clause :: seen) rest
        .ok (mergeResponseShapes branchShape restShape)

/-- Decodes a complete-normal root selection set using source Boolean support. -/
def decodeCompleteRoot
    (schema : Schema) (support : List NormalForm.BoolVar) (rootType : Name)
    (selectionSet : List Selection) : Except ShapeBuildError ResponseShape := do
  match firstDuplicate? support with
  | some varName => .error (.duplicateSupportVariable varName)
  | none =>
      match support with
      | [] =>
          foldGroundSelectionSet schema { literals := [] } rootType selectionSet
      | _ :: _ =>
          decodeRootBranches schema support rootType [] selectionSet

/--
Decodes an operation already claimed to be complete-normal. Boolean support is
supplied separately because empty normalized cases do not retain source variables.
-/
def decodeCompleteOperationShape
    (schema : Schema) (support : List NormalForm.BoolVar)
    (normalized : Operation) : Except ShapeBuildError OperationShape := do
  let rootType := normalized.rootType schema
  let root ← decodeCompleteRoot schema support rootType normalized.selectionSet
  .ok
    {
      operationType := normalized.operationType
      rootType := rootType
      boolSupport := support
      root := root
    }

/-- Computes a response shape through complete normalization and total decoding. -/
def computeOperationShape
    (schema : Schema) (operation : Operation)
    : Except ShapeBuildError OperationShape :=
  let support := NormalForm.operationBoolVars operation
  let normalized := NormalForm.completeNormalizeOperation schema operation
  decodeCompleteOperationShape schema support normalized

end ResponseShape

end GraphQL
