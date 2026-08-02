import Proofs.GraphQL.Theories.ResponseShape.Comparison.Strict
import Tests.GraphQL.Theories.ResponseShape.PremiseSatisfiability

/-!
Executable differential tests for response-shape subset and strict-equivalence
comparison.

The eight `FlatCase` fixtures enumerate three independent path-presence bits.
`flatSubsetOracle` compares those bits directly, without using response-shape
denotation, comparison relations, counterexample search, or either decider.
-/

namespace GraphQL
namespace Tests
namespace ResponseShape
namespace Comparison

open GraphQL.ResponseShape

/-- Three independent assignment/path facts represented by a flat fixture. -/
structure FlatCaseBits where
  alphaFalse : Bool
  alphaTrue : Bool
  betaTrue : Bool
deriving Repr, DecidableEq

/-- The complete eight-case universe of three flat path-presence bits. -/
inductive FlatCase where
  | empty
  | alphaFalse
  | alphaTrue
  | alphaBoth
  | betaTrue
  | alphaFalseBetaTrue
  | alphaTrueBetaTrue
  | all
deriving Repr, DecidableEq

/-- The three independent facts carried by one explicit flat case. -/
def FlatCase.bits : FlatCase → FlatCaseBits
  | .empty => ⟨false, false, false⟩
  | .alphaFalse => ⟨true, false, false⟩
  | .alphaTrue => ⟨false, true, false⟩
  | .alphaBoth => ⟨true, true, false⟩
  | .betaTrue => ⟨false, false, true⟩
  | .alphaFalseBetaTrue => ⟨true, false, true⟩
  | .alphaTrueBetaTrue => ⟨false, true, true⟩
  | .all => ⟨true, true, true⟩

/-- The explicit finite fixture universe used for all 64 ordered pairs. -/
def allFlatCases : List FlatCase :=
  [
    .empty,
    .alphaFalse,
    .alphaTrue,
    .alphaBoth,
    .betaTrue,
    .alphaFalseBetaTrue,
    .alphaTrueBetaTrue,
    .all
  ]

def flatFieldHead (arguments : List Argument := []) : FieldHead :=
  {
    fieldName := "left"
    arguments := arguments
    outputType := .named "String"
  }

def flatDefinition (value : Bool) (arguments : List Argument := []) : ShapeDefinition :=
  .mk { literals := [("x", value)] } (flatFieldHead arguments) none

def flatPosition (responseName : Name) (definitions : List ShapeDefinition)
    : ResponsePosition :=
  .mk responseName [.mk ["Query"] definitions]

def alphaDefinitions (bits : FlatCaseBits) : List ShapeDefinition :=
  (if bits.alphaFalse then [flatDefinition false] else [])
  ++ (if bits.alphaTrue then [flatDefinition true] else [])

def flatPositions (bits : FlatCaseBits) : List ResponsePosition :=
  (if bits.alphaFalse || bits.alphaTrue then
      [flatPosition "alpha" (alphaDefinitions bits)]
    else
      [])
  ++ (if bits.betaTrue then
        [flatPosition "beta" [flatDefinition true]]
      else
        [])

/-- A ready flat operation shape generated solely from one case's bits. -/
def flatShape (fixture : FlatCase) : OperationShape :=
  {
    operationType := .query
    rootType := "Query"
    boolSupport := ["x"]
    root := .object (flatPositions fixture.bits)
  }

/-- Independent set-inclusion oracle over the fixture's three raw bits. -/
def flatSubsetOracle (required provided : FlatCase) : Bool :=
  let requiredBits := required.bits
  let providedBits := provided.bits
  (!requiredBits.alphaFalse || providedBits.alphaFalse)
  && (!requiredBits.alphaTrue || providedBits.alphaTrue)
  && (!requiredBits.betaTrue || providedBits.betaTrue)

/-- Constructor-only observation of a proof-carrying verdict. -/
inductive CertifiedVerdictTag where
  | accepted
  | rejected
  | unknown
deriving Repr, DecidableEq

/-- Erases proofs and payloads while retaining the verdict constructor. -/
def certifiedVerdictTag
    {P : Prop} {AcceptedBasis Counterexample UnknownReason : Type}
    (verdict : CertifiedVerdict P AcceptedBasis Counterexample UnknownReason)
    : CertifiedVerdictTag :=
  match verdict with
  | .accepted _ _ => .accepted
  | .rejected _ _ => .rejected
  | .unknown _ => .unknown

/-- The oracle's expected ready-pair verdict constructor. -/
def expectedFlatVerdictTag (required provided : FlatCase) : CertifiedVerdictTag :=
  if flatSubsetOracle required provided then .accepted else .rejected

/-- One ordered-pair check, including positive readiness facts on both sides. -/
def flatPairCheck (required provided : FlatCase) : Bool :=
  decide ((flatShape required).WellFormed minimalSchema)
  && decide (flatShape required).FullMinterm
  && decide ((flatShape provided).WellFormed minimalSchema)
  && decide (flatShape provided).FullMinterm
  && decide
      (flatSubsetOracle required provided
        = decide (ShapeSubset minimalSchema (flatShape required) (flatShape provided)))
  && decide
      (certifiedVerdictTag
          (decideShapeSubset minimalSchema (flatShape required) (flatShape provided))
        = expectedFlatVerdictTag required provided)

/-- Independent mutual-footprint oracle: all three raw bits must agree. -/
def flatShapeEquivalentOracle (left right : FlatCase) : Bool :=
  let leftBits := left.bits
  let rightBits := right.bits
  (leftBits.alphaFalse == rightBits.alphaFalse)
  && (leftBits.alphaTrue == rightBits.alphaTrue)
  && (leftBits.betaTrue == rightBits.betaTrue)

/-- The mutual-footprint oracle's expected ready-pair verdict constructor. -/
def expectedFlatShapeEquivalentVerdictTag (left right : FlatCase) : CertifiedVerdictTag :=
  if flatShapeEquivalentOracle left right then .accepted else .rejected

/-- One mutual-footprint ordered-pair check, including both fixtures' positive
readiness facts. -/
def flatShapeEquivalentPairCheck (left right : FlatCase) : Bool :=
  decide ((flatShape left).WellFormed minimalSchema)
  && decide (flatShape left).FullMinterm
  && decide ((flatShape right).WellFormed minimalSchema)
  && decide (flatShape right).FullMinterm
  && decide
      (flatShapeEquivalentOracle left right
        = decide (ShapeEquivalent minimalSchema (flatShape left) (flatShape right)))
  && decide
      (certifiedVerdictTag
          (decideShapeEquivalent minimalSchema (flatShape left) (flatShape right))
        = expectedFlatShapeEquivalentVerdictTag left right)

/-- Strict comparison uses the same footprint oracle because every flat fixture
has the identical Boolean support. -/
def flatStrictEquivalentOracle (left right : FlatCase) : Bool :=
  flatShapeEquivalentOracle left right

/-- The strict oracle's expected ready-pair verdict constructor. -/
def expectedFlatStrictVerdictTag (left right : FlatCase) : CertifiedVerdictTag :=
  if flatStrictEquivalentOracle left right then .accepted else .rejected

/-- One strict ordered-pair check, including positive facts for both fixtures. -/
def flatStrictPairCheck (left right : FlatCase) : Bool :=
  decide ((flatShape left).WellFormed minimalSchema)
  && decide (flatShape left).FullMinterm
  && decide ((flatShape right).WellFormed minimalSchema)
  && decide (flatShape right).FullMinterm
  && decide
      (flatStrictEquivalentOracle left right
        = decide (StrictShapeEquivalent minimalSchema (flatShape left) (flatShape right)))
  && decide
      (certifiedVerdictTag
          (decideStrictShapeEquivalent minimalSchema (flatShape left) (flatShape right))
        = expectedFlatStrictVerdictTag left right)

private def flatPathStepEqBool (left right : PathStep) : Bool :=
  (left.parentObject == right.parentObject)
  && (left.responseName == right.responseName)
  && (left.field.fieldName == right.field.fieldName)
  && Algorithms.argumentListEqBool left.field.arguments right.field.arguments
  && decide (left.field.outputType = right.field.outputType)

private def flatPathEqBool : List PathStep → List PathStep → Bool
  | [], [] => true
  | left :: leftRest, right :: rightRest =>
      flatPathStepEqBool left right && flatPathEqBool leftRest rightRest
  | _, _ => false

private def flatPathListEqBool : List (List PathStep) → List (List PathStep) → Bool
  | [], [] => true
  | left :: leftRest, right :: rightRest =>
      flatPathEqBool left right && flatPathListEqBool leftRest rightRest
  | _, _ => false

def expectedFlatPath (responseName : Name) (arguments : List Argument := [])
    : List PathStep :=
  [{
    parentObject := "Query"
    responseName := responseName
    field := flatFieldHead arguments
  }]

private def uncoveredPayloadFieldsMatchBool
    (actualOrigin : ObligationOrigin)
    (actualObligation : ShapeObligation)
    (actualAvailablePaths : List (List PathStep))
    (expectedOrigin : ObligationOrigin)
    (expectedAssignment : NormalForm.BoolCase)
    (expectedPath : List PathStep)
    (expectedAvailablePaths : List (List PathStep))
    : Bool :=
  decide (actualOrigin = expectedOrigin)
  && decide (actualObligation.assignment = expectedAssignment)
  && flatPathEqBool actualObligation.path expectedPath
  && flatPathListEqBool actualAvailablePaths expectedAvailablePaths

/-- Executable exact observer for the concrete `uncovered` rejection payload. -/
def uncoveredPayloadMatchesBool
    (required provided : OperationShape)
    (expectedOrigin : ObligationOrigin)
    (expectedAssignment : NormalForm.BoolCase)
    (expectedPath : List PathStep)
    (expectedAvailablePaths : List (List PathStep))
    : Bool :=
  match decideShapeSubset minimalSchema required provided with
  | .rejected _ (.uncovered actualOrigin actualObligation actualAvailablePaths) =>
      uncoveredPayloadFieldsMatchBool
        actualOrigin actualObligation actualAvailablePaths
        expectedOrigin expectedAssignment expectedPath expectedAvailablePaths
  | _ => false

/-- Exact observer for a right-to-left uncovered payload returned by mutual
footprint comparison. -/
def shapeEquivalentRightUncoveredPayloadMatchesBool
    (left right : OperationShape)
    (expectedOrigin : ObligationOrigin)
    (expectedAssignment : NormalForm.BoolCase)
    (expectedPath : List PathStep)
    (expectedAvailablePaths : List (List PathStep))
    : Bool :=
  match decideShapeEquivalent minimalSchema left right with
  | .rejected _
      (.rightNotSubsetLeft
        (.uncovered actualOrigin actualObligation actualAvailablePaths)) =>
      uncoveredPayloadFieldsMatchBool
        actualOrigin actualObligation actualAvailablePaths
        expectedOrigin expectedAssignment expectedPath expectedAvailablePaths
  | _ => false

/-- Exact observer for a left-to-right uncovered payload wrapped by the strict
footprint counterexample. -/
def strictUncoveredPayloadMatchesBool
    (left right : OperationShape)
    (expectedOrigin : ObligationOrigin)
    (expectedAssignment : NormalForm.BoolCase)
    (expectedPath : List PathStep)
    (expectedAvailablePaths : List (List PathStep))
    : Bool :=
  match decideStrictShapeEquivalent minimalSchema left right with
  | .rejected _
      (.footprint
        (.leftNotSubsetRight
          (.uncovered actualOrigin actualObligation actualAvailablePaths))) =>
      uncoveredPayloadFieldsMatchBool
        actualOrigin actualObligation actualAvailablePaths
        expectedOrigin expectedAssignment expectedPath expectedAvailablePaths
  | _ => false

/-- Exact observer for the concrete support variable in a strict rejection. -/
def strictSupportMismatch? (left right : OperationShape) : Option NormalForm.BoolVar :=
  match decideStrictShapeEquivalent minimalSchema left right with
  | .rejected _ (.boolSupportMismatch varName) => some varName
  | _ => none

/-- Constructor/reason observation for any comparison unknown verdict. -/
def verdictUnknownReason?
    {P : Prop} {AcceptedBasis Counterexample : Type}
    (verdict : CertifiedVerdict P AcceptedBasis Counterexample ShapeUnknownReason)
    : Option ShapeUnknownReason :=
  match verdict with
  | .unknown reason => some reason
  | _ => none

/-- The flat universe has eight cases, 64 ordered pairs, two assignments, and
the all-bits fixture contributes both response paths in the true case. -/
theorem flatUniverseCardinalityAndPaths
    : allFlatCases.length = 8
      ∧ allFlatCases.length * allFlatCases.length = 64
      ∧ NormalForm.allBoolCases ["x"] = [[("x", false)], [("x", true)]]
      ∧ flatPathListEqBool
          ((flatShape .all).root.enumeratePaths minimalSchema [("x", false)] "Query")
          [expectedFlatPath "alpha"]
      ∧ flatPathListEqBool
          ((flatShape .all).root.enumeratePaths minimalSchema [("x", true)] "Query")
          [expectedFlatPath "alpha", expectedFlatPath "beta"] := by
  decide

/-- Kernel-evaluated differential guard over every one of the 64 ordered pairs.
It compares the independent bit oracle with both the proposition's `Decidable`
instance and the proof-carrying API's constructor. -/
theorem flatUniverseExhaustiveSubsetComparison
    : allFlatCases.all
        fun required =>
          allFlatCases.all fun provided => flatPairCheck required provided := by
  set_option maxHeartbeats 0 in
    decide

/-- The independent mutual-footprint oracle agrees with the public proposition
decider and proof-carrying verdict constructor on all 64 ready ordered pairs. -/
theorem flatUniverseExhaustiveShapeEquivalentComparison
    : allFlatCases.all
        fun left =>
          allFlatCases.all fun right => flatShapeEquivalentPairCheck left right := by
  set_option maxHeartbeats 0 in
    decide

/-- The independent equality-of-bits oracle agrees with the strict proposition
and proof-carrying verdict constructor on all 64 ready ordered pairs. -/
theorem flatUniverseExhaustiveStrictComparison
    : allFlatCases.all
        fun left =>
          allFlatCases.all fun right => flatStrictPairCheck left right := by
  set_option maxHeartbeats 0 in
    decide

/-- A direct proper-subset pair is ready and accepted. -/
theorem directFlatAcceptedPair
    : (flatShape .alphaFalse).WellFormed minimalSchema
      ∧ (flatShape .alphaFalse).FullMinterm
      ∧ (flatShape .alphaBoth).WellFormed minimalSchema
      ∧ (flatShape .alphaBoth).FullMinterm
      ∧ flatSubsetOracle .alphaFalse .alphaBoth = true
      ∧ ShapeSubset minimalSchema (flatShape .alphaFalse) (flatShape .alphaBoth)
      ∧ certifiedVerdictTag
          (decideShapeSubset minimalSchema (flatShape .alphaFalse) (flatShape .alphaBoth))
        = .accepted := by
  decide

/-- Reversing the same proper-subset pair is ready and rejected. -/
theorem directFlatRejectedPair
    : (flatShape .alphaBoth).WellFormed minimalSchema
      ∧ (flatShape .alphaBoth).FullMinterm
      ∧ (flatShape .alphaFalse).WellFormed minimalSchema
      ∧ (flatShape .alphaFalse).FullMinterm
      ∧ flatSubsetOracle .alphaBoth .alphaFalse = false
      ∧ ¬ShapeSubset minimalSchema (flatShape .alphaBoth) (flatShape .alphaFalse)
      ∧ certifiedVerdictTag
          (decideShapeSubset minimalSchema (flatShape .alphaBoth) (flatShape .alphaFalse))
        = .rejected := by
  decide

def firstArgument : Argument :=
  { name := "first", value := .int 1 }

def secondArgument : Argument :=
  { name := "second", value := .string "sample" }

def changedFirstArgument : Argument :=
  { name := "first", value := .int 2 }

def argumentShape (arguments : List Argument) : OperationShape :=
  {
    operationType := .query
    rootType := "Query"
    boolSupport := ["x"]
    root :=
      .object
        [flatPosition "matched"
          [flatDefinition false arguments, flatDefinition true arguments]]
  }

/-- Argument order is semantically unobservable to subset comparison. -/
theorem reorderedArgumentsAccepted
    : (argumentShape [firstArgument, secondArgument]).WellFormed minimalSchema
      ∧ (argumentShape [firstArgument, secondArgument]).FullMinterm
      ∧ (argumentShape [secondArgument, firstArgument]).WellFormed minimalSchema
      ∧ (argumentShape [secondArgument, firstArgument]).FullMinterm
      ∧ Argument.argumentsEquivalent
          [firstArgument, secondArgument] [secondArgument, firstArgument]
      ∧ ShapeSubset minimalSchema
          (argumentShape [firstArgument, secondArgument])
          (argumentShape [secondArgument, firstArgument])
      ∧ certifiedVerdictTag
          (decideShapeSubset minimalSchema
            (argumentShape [firstArgument, secondArgument])
            (argumentShape [secondArgument, firstArgument]))
        = .accepted := by
  have harguments : Argument.argumentsEquivalent
      [firstArgument, secondArgument] [secondArgument, firstArgument] := by
    rw [← argumentsEquivalentBool_iff]
    decide
  exact ⟨by decide, by decide, by decide, by decide, harguments,
    by decide, by decide⟩

/-- F3 is set semantics, so duplicate arguments do not add multiplicity. -/
theorem duplicateArgumentsUseSetSemantics
    : (argumentShape [firstArgument, firstArgument]).WellFormed minimalSchema
      ∧ (argumentShape [firstArgument, firstArgument]).FullMinterm
      ∧ (argumentShape [firstArgument]).WellFormed minimalSchema
      ∧ (argumentShape [firstArgument]).FullMinterm
      ∧ Argument.argumentsEquivalent [firstArgument, firstArgument] [firstArgument]
      ∧ Argument.argumentsEquivalent [firstArgument] [firstArgument, firstArgument]
      ∧ ShapeSubset minimalSchema
          (argumentShape [firstArgument, firstArgument])
          (argumentShape [firstArgument])
      ∧ ShapeSubset minimalSchema
          (argumentShape [firstArgument])
          (argumentShape [firstArgument, firstArgument])
      ∧ certifiedVerdictTag
          (decideShapeSubset minimalSchema
            (argumentShape [firstArgument, firstArgument])
            (argumentShape [firstArgument]))
        = .accepted
      ∧ certifiedVerdictTag
          (decideShapeSubset minimalSchema
            (argumentShape [firstArgument])
            (argumentShape [firstArgument, firstArgument]))
        = .accepted := by
  have hforward : Argument.argumentsEquivalent
      [firstArgument, firstArgument] [firstArgument] := by
    rw [← argumentsEquivalentBool_iff]
    decide
  have hbackward : Argument.argumentsEquivalent
      [firstArgument] [firstArgument, firstArgument] := by
    rw [← argumentsEquivalentBool_iff]
    decide
  exact ⟨by decide, by decide, by decide, by decide, hforward, hbackward,
    by decide, by decide, by decide, by decide⟩

/-- A missing false-assignment provider returns the exact first uncovered
assignment/path and an empty available-provider list. -/
theorem missingAssignmentRejectionPayload
    : (flatShape .alphaFalse).WellFormed minimalSchema
      ∧ (flatShape .alphaFalse).FullMinterm
      ∧ (flatShape .alphaTrue).WellFormed minimalSchema
      ∧ (flatShape .alphaTrue).FullMinterm
      ∧ ¬ShapeSubset minimalSchema (flatShape .alphaFalse) (flatShape .alphaTrue)
      ∧ uncoveredPayloadMatchesBool
          (flatShape .alphaFalse) (flatShape .alphaTrue)
          { assignmentIndex := 0, pathIndex := 0 }
          [("x", false)] (expectedFlatPath "alpha") [] := by
  decide

/-- A semantic argument mismatch returns the exact assignment/required path and
the concrete, differently-argumented provider path. -/
theorem mismatchedArgumentsRejectionPayload
    : (argumentShape [firstArgument]).WellFormed minimalSchema
      ∧ (argumentShape [firstArgument]).FullMinterm
      ∧ (argumentShape [changedFirstArgument]).WellFormed minimalSchema
      ∧ (argumentShape [changedFirstArgument]).FullMinterm
      ∧ ¬Argument.argumentsEquivalent [firstArgument] [changedFirstArgument]
      ∧ ¬ShapeSubset minimalSchema
          (argumentShape [firstArgument]) (argumentShape [changedFirstArgument])
      ∧ uncoveredPayloadMatchesBool
          (argumentShape [firstArgument]) (argumentShape [changedFirstArgument])
          { assignmentIndex := 0, pathIndex := 0 }
          [("x", false)] (expectedFlatPath "matched" [firstArgument])
          [expectedFlatPath "matched" [changedFirstArgument]] := by
  have harguments : ¬Argument.argumentsEquivalent
      [firstArgument] [changedFirstArgument] := by
    rw [← argumentsEquivalentBool_iff]
    decide
  exact ⟨by decide, by decide, by decide, by decide, harguments,
    by decide, by decide⟩

/-- The strict comparator preserves the reordered- and duplicate-argument F3
positives while checking footprint inclusion in both directions. -/
theorem strictArgumentEnvelopeAccepted
    : ShapeComparisonReady minimalSchema
        (argumentShape [firstArgument, secondArgument])
        (argumentShape [secondArgument, firstArgument])
      ∧ StrictShapeEquivalent minimalSchema
          (argumentShape [firstArgument, secondArgument])
          (argumentShape [secondArgument, firstArgument])
      ∧ certifiedVerdictTag
          (decideStrictShapeEquivalent minimalSchema
            (argumentShape [firstArgument, secondArgument])
            (argumentShape [secondArgument, firstArgument]))
        = .accepted
      ∧ ShapeComparisonReady minimalSchema
          (argumentShape [firstArgument, firstArgument])
          (argumentShape [firstArgument])
      ∧ StrictShapeEquivalent minimalSchema
          (argumentShape [firstArgument, firstArgument])
          (argumentShape [firstArgument])
      ∧ certifiedVerdictTag
          (decideStrictShapeEquivalent minimalSchema
            (argumentShape [firstArgument, firstArgument])
            (argumentShape [firstArgument]))
        = .accepted := by
  decide

/-- Mutual comparison first accepts left-to-right coverage, then returns the
exact uncovered true-assignment payload from its right-to-left search. -/
theorem shapeEquivalentRightToLeftRejectionPayload
    : (flatShape .alphaFalse).WellFormed minimalSchema
      ∧ (flatShape .alphaFalse).FullMinterm
      ∧ (flatShape .alphaBoth).WellFormed minimalSchema
      ∧ (flatShape .alphaBoth).FullMinterm
      ∧ ShapeSubset minimalSchema (flatShape .alphaFalse) (flatShape .alphaBoth)
      ∧ ¬ShapeSubset minimalSchema (flatShape .alphaBoth) (flatShape .alphaFalse)
      ∧ ¬ShapeEquivalent minimalSchema (flatShape .alphaFalse) (flatShape .alphaBoth)
      ∧ certifiedVerdictTag
          (decideShapeEquivalent minimalSchema
            (flatShape .alphaFalse) (flatShape .alphaBoth))
        = .rejected
      ∧ shapeEquivalentRightUncoveredPayloadMatchesBool
          (flatShape .alphaFalse) (flatShape .alphaBoth)
          { assignmentIndex := 1, pathIndex := 0 }
          [("x", true)] (expectedFlatPath "alpha") [] := by
  decide

/-- A strict footprint rejection preserves the exact directional uncovered
assignment/path payload under its strict counterexample wrapper. -/
theorem strictFootprintRejectionPayload
    : (flatShape .alphaFalse).WellFormed minimalSchema
      ∧ (flatShape .alphaFalse).FullMinterm
      ∧ (flatShape .alphaTrue).WellFormed minimalSchema
      ∧ (flatShape .alphaTrue).FullMinterm
      ∧ ¬StrictShapeEquivalent minimalSchema
          (flatShape .alphaFalse) (flatShape .alphaTrue)
      ∧ strictUncoveredPayloadMatchesBool
          (flatShape .alphaFalse) (flatShape .alphaTrue)
          { assignmentIndex := 0, pathIndex := 0 }
          [("x", false)] (expectedFlatPath "alpha") [] := by
  decide

def emptyShapeWithSupport (support : List NormalForm.BoolVar) : OperationShape :=
  { flatShape .empty with boolSupport := support }

/-- Strict support equality is extensional, so source-support order is not
observable for two ready fixtures with the same footprint. -/
theorem reorderedBoolSupportsAccepted
    : (emptyShapeWithSupport ["x", "y"]).WellFormed minimalSchema
      ∧ (emptyShapeWithSupport ["x", "y"]).FullMinterm
      ∧ (emptyShapeWithSupport ["y", "x"]).WellFormed minimalSchema
      ∧ (emptyShapeWithSupport ["y", "x"]).FullMinterm
      ∧ BoolSupportEquivalent ["x", "y"] ["y", "x"]
      ∧ StrictShapeEquivalent minimalSchema
          (emptyShapeWithSupport ["x", "y"])
          (emptyShapeWithSupport ["y", "x"])
      ∧ certifiedVerdictTag
          (decideStrictShapeEquivalent minimalSchema
            (emptyShapeWithSupport ["x", "y"])
            (emptyShapeWithSupport ["y", "x"]))
        = .accepted := by
  decide

/-- Equal footprints with unequal supports reject with the exact first
membership-mismatched source variable. -/
theorem strictSupportMismatchPayload
    : (emptyShapeWithSupport ["x"]).WellFormed minimalSchema
      ∧ (emptyShapeWithSupport ["x"]).FullMinterm
      ∧ (emptyShapeWithSupport ["x", "y"]).WellFormed minimalSchema
      ∧ (emptyShapeWithSupport ["x", "y"]).FullMinterm
      ∧ ShapeEquivalent minimalSchema
          (emptyShapeWithSupport ["x"])
          (emptyShapeWithSupport ["x", "y"])
      ∧ ¬StrictShapeEquivalent minimalSchema
          (emptyShapeWithSupport ["x"])
          (emptyShapeWithSupport ["x", "y"])
      ∧ firstBoolSupportMismatch? ["x"] ["x", "y"] = some "y"
      ∧ strictSupportMismatch?
          (emptyShapeWithSupport ["x"])
          (emptyShapeWithSupport ["x", "y"])
        = some "y" := by
  decide

def malformedMissingRequired : OperationShape :=
  { flatShape .alphaFalse with boolSupport := ["x", "x"] }

def malformedCoveredRequired : OperationShape :=
  { flatShape .empty with boolSupport := ["x", "x"] }

/-- A semantic counterexample outranks readiness failure: the malformed
required shape is still rejected rather than classified as unknown. -/
theorem semanticRejectionPrecedesUnknown
    : ¬malformedMissingRequired.WellFormed minimalSchema
      ∧ ¬malformedMissingRequired.FullMinterm
      ∧ (flatShape .empty).WellFormed minimalSchema
      ∧ (flatShape .empty).FullMinterm
      ∧ ¬ShapeComparisonReady minimalSchema malformedMissingRequired (flatShape .empty)
      ∧ ¬ShapeSubset minimalSchema malformedMissingRequired (flatShape .empty)
      ∧ certifiedVerdictTag
          (decideShapeSubset minimalSchema malformedMissingRequired (flatShape .empty))
        = .rejected := by
  decide

/-- A semantically covered malformed pair reports the first exact readiness
reason, exercising the executable unknown characterization. -/
theorem coveredMalformedPairIsUnknown
    : ¬malformedCoveredRequired.WellFormed minimalSchema
      ∧ malformedCoveredRequired.FullMinterm
      ∧ (flatShape .empty).WellFormed minimalSchema
      ∧ (flatShape .empty).FullMinterm
      ∧ ShapeSubset minimalSchema malformedCoveredRequired (flatShape .empty)
      ∧ ¬ShapeComparisonReady minimalSchema malformedCoveredRequired (flatShape .empty)
      ∧ verdictUnknownReason?
          (decideShapeSubset minimalSchema malformedCoveredRequired (flatShape .empty))
        = some .requiredNotWellFormed := by
  decide

/-- Strict comparison also gives a semantic footprint rejection precedence
over the malformed required fixture's readiness failure. -/
theorem strictSemanticRejectionPrecedesUnknown
    : ¬malformedMissingRequired.WellFormed minimalSchema
      ∧ ¬malformedMissingRequired.FullMinterm
      ∧ (flatShape .empty).WellFormed minimalSchema
      ∧ (flatShape .empty).FullMinterm
      ∧ ¬ShapeComparisonReady minimalSchema malformedMissingRequired (flatShape .empty)
      ∧ ¬StrictShapeEquivalent minimalSchema malformedMissingRequired (flatShape .empty)
      ∧ certifiedVerdictTag
          (decideStrictShapeEquivalent minimalSchema
            malformedMissingRequired (flatShape .empty))
        = .rejected := by
  decide

/-- A concrete support mismatch also rejects before readiness is consulted,
even though the left empty-footprint shape has duplicate source support. -/
theorem strictSupportRejectionPrecedesUnknown
    : ¬malformedCoveredRequired.WellFormed minimalSchema
      ∧ malformedCoveredRequired.FullMinterm
      ∧ (emptyShapeWithSupport ["y"]).WellFormed minimalSchema
      ∧ (emptyShapeWithSupport ["y"]).FullMinterm
      ∧ ¬ShapeComparisonReady minimalSchema malformedCoveredRequired (emptyShapeWithSupport ["y"])
      ∧ ShapeEquivalent minimalSchema
          malformedCoveredRequired (emptyShapeWithSupport ["y"])
      ∧ ¬StrictShapeEquivalent minimalSchema
          malformedCoveredRequired (emptyShapeWithSupport ["y"])
      ∧ certifiedVerdictTag
          (decideStrictShapeEquivalent minimalSchema
            malformedCoveredRequired (emptyShapeWithSupport ["y"]))
        = .rejected
      ∧ strictSupportMismatch? malformedCoveredRequired (emptyShapeWithSupport ["y"])
        = some "x" := by
  decide

/-- Strict comparison reports the same exact first readiness reason when
footprints and extensional support are covered but the required shape is raw. -/
theorem strictCoveredMalformedPairIsUnknown
    : ¬malformedCoveredRequired.WellFormed minimalSchema
      ∧ malformedCoveredRequired.FullMinterm
      ∧ (flatShape .empty).WellFormed minimalSchema
      ∧ (flatShape .empty).FullMinterm
      ∧ boolSupportEquivalentBool
          malformedCoveredRequired.boolSupport (flatShape .empty).boolSupport
        = true
      ∧ BoolSupportEquivalent
          malformedCoveredRequired.boolSupport (flatShape .empty).boolSupport
      ∧ StrictShapeEquivalent minimalSchema malformedCoveredRequired (flatShape .empty)
      ∧ ¬ShapeComparisonReady minimalSchema malformedCoveredRequired (flatShape .empty)
      ∧ verdictUnknownReason?
          (decideStrictShapeEquivalent minimalSchema
            malformedCoveredRequired (flatShape .empty))
        = some .requiredNotWellFormed := by
  decide

private def twoStepNestedField : FieldDefinition :=
  { name := "nested", outputType := .named "Query" }

private def twoStepQueryType : ObjectType :=
  { name := "Query", fields := [minimalField, twoStepNestedField] }

private def twoStepSchema : Schema :=
  { queryType := "Query", types := [.object twoStepQueryType] }

private def twoStepLeafHead (arguments : List Argument := []) : FieldHead :=
  { fieldName := "left", arguments := arguments, outputType := .named "String" }

private def twoStepParentHead : FieldHead :=
  { fieldName := "nested", arguments := [], outputType := .named "Query" }

private def twoStepChild (arguments : List Argument) : ResponseShape :=
  .object
    [.mk "leaf"
      [.mk ["Query"]
        [.mk { literals := [("x", true)] } (twoStepLeafHead arguments) none]]]

private def twoStepShape (arguments : List Argument) : OperationShape :=
  {
    operationType := .query
    rootType := "Query"
    boolSupport := ["x"]
    root :=
      .object
        [.mk "outer"
          [.mk ["Query"]
            [.mk { literals := [("x", true)] } twoStepParentHead
              (some (twoStepChild arguments))]]]
  }

private def twoStepOuterPathStep : PathStep :=
  { parentObject := "Query", responseName := "outer", field := twoStepParentHead }

private def twoStepLeafPathStep (arguments : List Argument := []) : PathStep :=
  { parentObject := "Query", responseName := "leaf", field := twoStepLeafHead arguments }

/-- Reordering arguments on a child field preserves both footprint directions
and therefore strict equivalence of the nested shapes. -/
theorem reorderedChildArgumentsAccepted
    : (twoStepShape [firstArgument, secondArgument]).WellFormed twoStepSchema
      ∧ (twoStepShape [firstArgument, secondArgument]).FullMinterm
      ∧ (twoStepShape [secondArgument, firstArgument]).WellFormed twoStepSchema
      ∧ (twoStepShape [secondArgument, firstArgument]).FullMinterm
      ∧ Argument.argumentsEquivalent
          [firstArgument, secondArgument] [secondArgument, firstArgument]
      ∧ Argument.argumentsEquivalent
          [secondArgument, firstArgument] [firstArgument, secondArgument]
      ∧ ShapeSubset twoStepSchema
          (twoStepShape [firstArgument, secondArgument])
          (twoStepShape [secondArgument, firstArgument])
      ∧ ShapeSubset twoStepSchema
          (twoStepShape [secondArgument, firstArgument])
          (twoStepShape [firstArgument, secondArgument])
      ∧ StrictShapeEquivalent twoStepSchema
          (twoStepShape [firstArgument, secondArgument])
          (twoStepShape [secondArgument, firstArgument])
      ∧ certifiedVerdictTag
          (decideStrictShapeEquivalent twoStepSchema
            (twoStepShape [firstArgument, secondArgument])
            (twoStepShape [secondArgument, firstArgument]))
        = .accepted := by
  have hforward : Argument.argumentsEquivalent
      [firstArgument, secondArgument] [secondArgument, firstArgument] := by
    rw [← argumentsEquivalentBool_iff]
    decide
  have hbackward : Argument.argumentsEquivalent
      [secondArgument, firstArgument] [firstArgument, secondArgument] := by
    rw [← argumentsEquivalentBool_iff]
    decide
  exact ⟨by decide, by decide, by decide, by decide, hforward, hbackward,
    by decide, by decide, by decide, by decide⟩

private def twoStepRequired : OperationShape := twoStepShape [firstArgument]

private def twoStepProvided : OperationShape := twoStepShape [changedFirstArgument]

/-- Observes the enumerator's complete nested rejection witness rather than
only the verdict constructor. -/
private def twoStepUncoveredPayloadMatches : Bool :=
  match decideShapeSubset twoStepSchema twoStepRequired twoStepProvided with
  | .rejected _ (.uncovered origin obligation availablePaths) =>
      decide (origin = { assignmentIndex := 1, pathIndex := 1 })
      && decide (obligation.assignment = [("x", true)])
      && flatPathEqBool obligation.path
          [twoStepOuterPathStep, twoStepLeafPathStep [firstArgument]]
      && flatPathListEqBool availablePaths
          [[twoStepOuterPathStep],
            [twoStepOuterPathStep, twoStepLeafPathStep [changedFirstArgument]]
          ]
  | _ => false

/-- Changing a child-field argument value rejects with its exact two-step
obligation and the concrete nested provider paths. -/
theorem changedChildArgumentRejectedWithTwoStepPayload
    : twoStepRequired.WellFormed twoStepSchema
      ∧ twoStepRequired.FullMinterm
      ∧ twoStepProvided.WellFormed twoStepSchema
      ∧ twoStepProvided.FullMinterm
      ∧ ¬Argument.argumentsEquivalent [firstArgument] [changedFirstArgument]
      ∧ ¬ShapeSubset twoStepSchema twoStepRequired twoStepProvided
      ∧ twoStepUncoveredPayloadMatches = true := by
  have harguments : ¬Argument.argumentsEquivalent
      [firstArgument] [changedFirstArgument] := by
    rw [← argumentsEquivalentBool_iff]
    decide
  exact ⟨by decide, by decide, by decide, by decide, harguments,
    by decide, by decide⟩

end Comparison
end ResponseShape
end Tests
end GraphQL
