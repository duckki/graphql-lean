import GraphQL.Theories.ResponseShape.Compute
import GraphQL.Theories.ResponseShape.Relations

/-!
Executable data for proof-carrying response-shape comparison.

The first comparator deliberately enumerates every Boolean assignment. For a
combined support of length `n`, `NormalForm.allBoolCases` contributes exactly
`2^n` cases before path traversal. This explicit exponential algorithm is the
initial verified reference implementation; it is not a symbolic optimizer.

All applicable path obligations and their stable syntactic origins are built
before any accepted/rejected/unknown classification. Duplicate semantic paths
remain distinct obligations when they came from distinct enumeration indices.
Mutual and strict equivalence reuse these oriented obligations and accepted
bases rather than starting a separate path traversal.
-/

namespace GraphQL

namespace ResponseShape

namespace Comparison

mutual
  /-- Structural path enumeration core for one response shape. -/
  def enumerateShapeCore
      : ResponseShape → Schema → NormalForm.BoolCase → Name → List (List PathStep)
    | .object positions, schema, assignment, parentType =>
        enumeratePositionsCore positions schema assignment parentType

  /-- Structural path enumeration core for one response position. -/
  def enumeratePositionCore
      : ResponsePosition → Schema → NormalForm.BoolCase → Name → List (List PathStep)
    | .mk responseName possibles, schema, assignment, parentType =>
        enumeratePossiblesCore possibles schema assignment parentType responseName

  /-- Structural path enumeration core for one possible-definition group. -/
  def enumeratePossibleCore
      : PossibleDefinitions → Schema → NormalForm.BoolCase → Name → Name
        → List (List PathStep)
    | .mk objectTypes definitions, schema, assignment, parentType, responseName =>
        objectTypes.flatMap
          fun runtimeObject =>
            if schema.typeIncludesObjectBool parentType runtimeObject then
              enumerateDefinitionsCore
                definitions schema assignment responseName runtimeObject
            else
              []

  /-- Structural path enumeration core for one guarded definition. -/
  def enumerateDefinitionCore
      : ShapeDefinition → Schema → NormalForm.BoolCase → Name → Name
        → List (List PathStep)
    | .mk clause field subshape, schema, assignment, responseName, runtimeObject =>
        if clause.holdsInBool assignment then
          let step : PathStep :=
            {
              parentObject := runtimeObject
              responseName := responseName
              field := field
            }
          [step] :: enumerateSubshapeCore subshape schema assignment step field
        else
          []

  /-- Structural path enumeration core for response-position lists. -/
  def enumeratePositionsCore
      : List ResponsePosition → Schema → NormalForm.BoolCase → Name → List (List PathStep)
    | [], _schema, _assignment, _parentType => []
    | position :: rest, schema, assignment, parentType =>
        enumeratePositionCore position schema assignment parentType
        ++ enumeratePositionsCore rest schema assignment parentType

  /-- Structural path enumeration core for possible-definition lists. -/
  def enumeratePossiblesCore
      : List PossibleDefinitions → Schema → NormalForm.BoolCase → Name → Name
        → List (List PathStep)
    | [], _schema, _assignment, _parentType, _responseName => []
    | possible :: rest, schema, assignment, parentType, responseName =>
        enumeratePossibleCore possible schema assignment parentType responseName
        ++ enumeratePossiblesCore rest schema assignment parentType responseName

  /-- Structural path enumeration core for guarded-definition lists. -/
  def enumerateDefinitionsCore
      : List ShapeDefinition → Schema → NormalForm.BoolCase → Name → Name
        → List (List PathStep)
    | [], _schema, _assignment, _responseName, _runtimeObject => []
    | definition :: rest, schema, assignment, responseName, runtimeObject =>
        enumerateDefinitionCore definition schema assignment responseName runtimeObject
        ++ enumerateDefinitionsCore rest schema assignment responseName runtimeObject

  /-- Prefixes every recursively enumerated child path with its parent step. -/
  def enumerateSubshapeCore
      : Option ResponseShape → Schema → NormalForm.BoolCase → PathStep → FieldHead
        → List (List PathStep)
    | none, _schema, _assignment, _step, _field => []
    | some child, schema, assignment, step, field =>
        (enumerateShapeCore child schema assignment field.outputType.namedType).map
          (List.cons step)
end

end Comparison

/-- Every exact nonempty path denoted by a shape for one assignment, including
both singleton field paths and recursively prefixed child paths. -/
def ResponseShape.enumeratePaths
    (schema : Schema) (assignment : NormalForm.BoolCase) (parentType : Name)
    (shape : ResponseShape)
    : List (List PathStep) :=
  Comparison.enumerateShapeCore shape schema assignment parentType

/-- Stable syntactic identity of an enumerated comparison obligation. -/
structure ObligationOrigin where
  assignmentIndex : Nat
  pathIndex : Nat
deriving Repr, DecidableEq

/-- One required path together with its stable enumeration identity. -/
structure ApplicableObligation where
  origin : ObligationOrigin
  obligation : ShapeObligation
deriving Repr

/--
Enumerates every required path at every assignment of the duplicate-free union
support. The outer assignment enumeration has `2^n` entries for union-support
length `n`; paths are then structurally enumerated for each entry.
-/
def applicableObligations (schema : Schema) (required provided : OperationShape)
    : List ApplicableObligation :=
  (NormalForm.allBoolCases
    (supportUnion required.boolSupport provided.boolSupport)).zipIdx.flatMap
    fun assignmentWithIndex =>
      let assignment := assignmentWithIndex.1
      let assignmentIndex := assignmentWithIndex.2
      (required.root.enumeratePaths schema assignment required.rootType).zipIdx.map
        fun pathWithIndex =>
          {
            origin :=
              {
                assignmentIndex := assignmentIndex
                pathIndex := pathWithIndex.2
              }
            obligation :=
              {
                assignment := assignment
                path := pathWithIndex.1
              }
          }

/-- The first concrete provided path semantically covering a required path. -/
def firstCoveringPath? (requiredPath : List PathStep)
    : List (List PathStep) → Option (List PathStep)
  | [] => none
  | providedPath :: rest =>
      if pathsSemanticallyEquivalentBool providedPath requiredPath then
        some providedPath
      else
        firstCoveringPath? requiredPath rest

/-- Executable coverage of one exact required path by candidate provided paths. -/
def pathCoveredBool (providedPaths : List (List PathStep)) (requiredPath : List PathStep)
    : Bool :=
  (firstCoveringPath? requiredPath providedPaths).isSome

/-- Outcome-independent comparison input for one applicable obligation. -/
structure ObligationContribution where
  origin : ObligationOrigin
  obligation : ShapeObligation
  providedPaths : List (List PathStep)
  covered : Bool
deriving Repr

/-- Classifies one applicable obligation against the provided shape. -/
def ApplicableObligation.toContribution
    (schema : Schema) (provided : OperationShape)
    (applicable : ApplicableObligation)
    : ObligationContribution :=
  let providedPaths :=
    provided.root.enumeratePaths schema applicable.obligation.assignment provided.rootType
  {
    origin := applicable.origin
    obligation := applicable.obligation
    providedPaths := providedPaths
    covered := pathCoveredBool providedPaths applicable.obligation.path
  }

/-- Computes every obligation contribution before any verdict classification. -/
def obligationContributions (schema : Schema) (required provided : OperationShape)
    : List ObligationContribution :=
  (applicableObligations schema required provided).map
    (ApplicableObligation.toContribution schema provided)

/-- The first contribution lacking a semantically equivalent provided path. -/
def firstUncoveredContribution?
    : List ObligationContribution → Option ObligationContribution
  | [] => none
  | contribution :: rest =>
      if contribution.covered then
        firstUncoveredContribution? rest
      else
        some contribution

/-- Concrete diagnostics for every proof-carrying way shape subset can fail.
`operationTypeMismatch` is unreachable while `OperationType` contains only the
`.query` constructor. -/
inductive SubsetCounterexample where
  | operationTypeMismatch (requiredOperationType providedOperationType : OperationType)
  | rootTypeMismatch (requiredRootType providedRootType : Name)
  | uncovered
    (origin : ObligationOrigin)
    (obligation : ShapeObligation)
    (availableProvidedPaths : List (List PathStep))
deriving Repr

/-- Computes semantic failures before consulting three-valued readiness. The
operation-type equality is automatic in the current single-constructor model,
so its mismatch branch is unreachable. -/
def shapeSubsetCounterexample? (schema : Schema) (required provided : OperationShape)
    : Option SubsetCounterexample :=
  if decide (required.operationType = provided.operationType) then
    if decide (required.rootType = provided.rootType) then
      match firstUncoveredContribution?
              (obligationContributions schema required provided) with
      | none => none
      | some contribution =>
          some
            (.uncovered contribution.origin contribution.obligation
              contribution.providedPaths)
    else
      some (.rootTypeMismatch required.rootType provided.rootType)
  else
    some (.operationTypeMismatch required.operationType provided.operationType)

/-- Readiness required for a positive proof-carrying result at the API boundary. -/
def ShapeComparisonReady (schema : Schema) (required provided : OperationShape) : Prop :=
  required.WellFormed schema
  ∧ required.FullMinterm
  ∧ provided.WellFormed schema
  ∧ provided.FullMinterm

instance instDecidableShapeComparisonReady (schema : Schema) (required provided : OperationShape)
    : Decidable (ShapeComparisonReady schema required provided) := by
  unfold ShapeComparisonReady
  infer_instance

/-- A concrete first readiness failure for an otherwise semantically covered pair. -/
inductive ShapeUnknownReason where
  | requiredNotWellFormed
  | requiredNotFullMinterm
  | providedNotWellFormed
  | providedNotFullMinterm
deriving Repr, DecidableEq

/-- Computes the first readiness failure in a stable diagnostic order. -/
def readinessFailure? (schema : Schema) (required provided : OperationShape)
    : Option ShapeUnknownReason :=
  if decide (required.WellFormed schema) then
    if decide required.FullMinterm then
      if decide (provided.WellFormed schema) then
        if decide provided.FullMinterm then
          none
        else
          some .providedNotFullMinterm
      else
        some .providedNotWellFormed
    else
      some .requiredNotFullMinterm
  else
    some .requiredNotWellFormed

/-- The first source Boolean variable whose membership differs between two
supports. Both sides are queried extensionally; support order and duplicates
are not observable. -/
def firstBoolSupportMismatch? (left right : List NormalForm.BoolVar)
    : Option NormalForm.BoolVar :=
  (supportUnion left right).find?
    fun varName =>
      !(decide (varName ∈ left ↔ varName ∈ right))

/-- Executable extensional equality of source Boolean supports. -/
def boolSupportEquivalentBool (left right : List NormalForm.BoolVar) : Bool :=
  (firstBoolSupportMismatch? left right).isNone

/-- Proof that one applicable exact path has a semantically equivalent provider. -/
structure CoverageWitness
    (schema : Schema) (required provided : OperationShape)
    (applicable : ApplicableObligation) where
  requiredDenotes
    : required.root.DenotesPath schema applicable.obligation.assignment
        required.rootType applicable.obligation.path
  providedPath : List PathStep
  providedDenotes
    : provided.root.DenotesPath schema applicable.obligation.assignment
        provided.rootType providedPath
  pathsEquivalent : PathsSemanticallyEquivalent providedPath applicable.obligation.path

/-- Finite accepted basis, retaining a proof-relevant provider for every origin. -/
structure SubsetAcceptedBasis (schema : Schema) (required provided : OperationShape) where
  operationTypeEq : required.operationType = provided.operationType
  rootTypeEq : required.rootType = provided.rootType
  coverage
    : ∀ applicable,
        applicable ∈ applicableObligations schema required provided
        → CoverageWitness schema required provided applicable

/-- Accepted finite bases for both directions of footprint equivalence. -/
structure ShapeEquivalentAcceptedBasis
    (schema : Schema) (left right : OperationShape) where
  leftToRight : SubsetAcceptedBasis schema left right
  rightToLeft : SubsetAcceptedBasis schema right left

/-- A directional subset counterexample disproving footprint equivalence. -/
inductive ShapeEquivalentCounterexample where
  | leftNotSubsetRight (counterexample : SubsetCounterexample)
  | rightNotSubsetLeft (counterexample : SubsetCounterexample)
deriving Repr

/-- Accepted footprint bases plus the exact extensional support proof. -/
structure StrictShapeEquivalentAcceptedBasis
    (schema : Schema) (left right : OperationShape) where
  shapeEquivalent : ShapeEquivalentAcceptedBasis schema left right
  boolSupportEquivalent : BoolSupportEquivalent left.boolSupport right.boolSupport

/-- A strict-equivalence failure is either directional footprint failure or a
concrete source Boolean variable whose support membership differs. -/
inductive StrictShapeEquivalentCounterexample where
  | footprint (counterexample : ShapeEquivalentCounterexample)
  | boolSupportMismatch (varName : NormalForm.BoolVar)
deriving Repr

/-- Generic proof-carrying three-valued verdict. -/
inductive CertifiedVerdict
    (P : Prop) (AcceptedBasis Counterexample UnknownReason : Type) where
  | accepted (proof : P) (basis : AcceptedBasis)
  | rejected (proof : ¬ P) (witness : Counterexample)
  | unknown (reason : UnknownReason)

/-- Proof-carrying verdict type for one oriented shape-subset comparison. -/
abbrev ShapeSubsetVerdict (schema : Schema) (required provided : OperationShape) :=
  CertifiedVerdict
    (ShapeSubset schema required provided)
    (SubsetAcceptedBasis schema required provided)
    SubsetCounterexample
    ShapeUnknownReason

/-- Proof-carrying verdict type for mutual response-footprint inclusion. -/
abbrev ShapeEquivalentVerdict (schema : Schema) (left right : OperationShape) :=
  CertifiedVerdict
    (ShapeEquivalent schema left right)
    (ShapeEquivalentAcceptedBasis schema left right)
    ShapeEquivalentCounterexample
    ShapeUnknownReason

/-- Proof-carrying verdict type for footprint and Boolean-support equivalence. -/
abbrev StrictShapeEquivalentVerdict (schema : Schema) (left right : OperationShape) :=
  CertifiedVerdict
    (StrictShapeEquivalent schema left right)
    (StrictShapeEquivalentAcceptedBasis schema left right)
    StrictShapeEquivalentCounterexample
    ShapeUnknownReason

/-- Accepted operation comparison data, retaining both computed shapes and the
finite basis returned by their strict comparison. The strict relation includes
operation-type equality, though that conjunct is currently vacuous because the
scoped `OperationType` has only `.query`. -/
structure OperationEquivalenceAcceptedBasis
    (schema : Schema) (left right : Operation) where
  leftShape : OperationShape
  rightShape : OperationShape
  leftComputed : computeOperationShape schema left = .ok leftShape
  rightComputed : computeOperationShape schema right = .ok rightShape
  strictBasis : StrictShapeEquivalentAcceptedBasis schema leftShape rightShape

/-- A strict shape counterexample together with the two operation shapes on
which it was computed. -/
structure OperationEquivalenceCounterexample
    (schema : Schema) (left right : Operation) where
  leftShape : OperationShape
  rightShape : OperationShape
  leftComputed : computeOperationShape schema left = .ok leftShape
  rightComputed : computeOperationShape schema right = .ok rightShape
  strictCounterexample : StrictShapeEquivalentCounterexample
deriving Repr

/-- Readiness-only reasons why operation comparison cannot return a Boolean
decision. Shape construction failures are distinguished by input side; once
both shapes exist, the strict comparator's readiness reason is preserved. -/
inductive OperationEquivalenceUnknownReason where
  | leftShapeBuild (error : ShapeBuildError)
  | rightShapeBuild (error : ShapeBuildError)
  | shapeReadiness (reason : ShapeUnknownReason)
deriving Repr, DecidableEq

/-- Proof-carrying operation comparison over the exact two computed shapes.
The accepted proposition is kept inline rather than minting another semantic
relation. -/
abbrev OperationEquivalenceVerdict (schema : Schema) (left right : Operation) :=
  CertifiedVerdict
    (∃ leftShape rightShape,
      computeOperationShape schema left = .ok leftShape
      ∧ computeOperationShape schema right = .ok rightShape
      ∧ StrictShapeEquivalent schema leftShape rightShape)
    (OperationEquivalenceAcceptedBasis schema left right)
    (OperationEquivalenceCounterexample schema left right)
    OperationEquivalenceUnknownReason

end ResponseShape

end GraphQL
