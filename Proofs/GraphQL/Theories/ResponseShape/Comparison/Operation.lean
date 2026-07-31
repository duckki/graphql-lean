import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Uniqueness
import Proofs.GraphQL.Theories.ResponseShape.Comparison.Strict
import Proofs.GraphQL.Theories.ResponseShape.Compute.Totality
import Proofs.GraphQL.Theories.ResponseShape.Correspondence.Canonicity

/-!
Proof-carrying executable comparison of source operations.

The comparator first computes both operation shapes, then delegates unchanged to
the strict shape comparator. Shape construction failures are outer readiness
reasons. Once both shapes exist, strict semantic failures still outrank shape
readiness exactly as they do in `decideStrictShapeEquivalent`.
-/

namespace GraphQL

namespace ResponseShape

/-- The retained operation-level accepted basis independently proves the inline
existential proposition over the exact computed shapes. -/
theorem OperationEquivalenceAcceptedBasis.sound
    {schema : Schema} {left right : Operation}
    (basis : OperationEquivalenceAcceptedBasis schema left right)
    : ∃ leftShape rightShape,
        computeOperationShape schema left = .ok leftShape
        ∧ computeOperationShape schema right = .ok rightShape
        ∧ StrictShapeEquivalent schema leftShape rightShape := by
  exact ⟨basis.leftShape, basis.rightShape, basis.leftComputed,
    basis.rightComputed, basis.strictBasis.sound⟩

private def computeOperationShapeResult (schema : Schema) (operation : Operation)
    : Except ShapeBuildError
        { shape : OperationShape
          // computeOperationShape schema operation = .ok shape } :=
  match computeOperationShape schema operation with
  | .ok shape => .ok ⟨shape, rfl⟩
  | .error error => .error error

private theorem computeOperationShapeResult_map (schema : Schema) (operation : Operation)
    : (computeOperationShapeResult schema operation).map Subtype.val
      = computeOperationShape schema operation := by
  unfold computeOperationShapeResult
  cases computeOperationShape schema operation <;> rfl

private theorem computeOperationShapeResult_eq_ok
    (schema : Schema) (operation : Operation) (shape : OperationShape)
    (hcompute : computeOperationShape schema operation = .ok shape)
    : computeOperationShapeResult schema operation = .ok ⟨shape, hcompute⟩ := by
  have hmap := computeOperationShapeResult_map schema operation
  have hmapOk :
      (computeOperationShapeResult schema operation).map Subtype.val =
        .ok shape := hmap.trans hcompute
  cases hresult : computeOperationShapeResult schema operation with
  | error error =>
      rw [hresult] at hmapOk
      contradiction
  | ok payload =>
      rw [hresult] at hmapOk
      have hvalue : payload.val = shape := Except.ok.inj hmapOk
      have hpayload : payload = ⟨shape, hcompute⟩ := Subtype.ext hvalue
      exact congrArg Except.ok hpayload

/-- Computes both source-operation shapes and delegates their comparison to the
strict shape comparator. Its operation-type mismatch branch is unreachable in
the current single-constructor `OperationType` model. -/
def decideOperationEquivalence (schema : Schema) (left right : Operation)
    : OperationEquivalenceVerdict schema left right :=
  match computeOperationShapeResult schema left with
  | .error error => .unknown (.leftShapeBuild error)
  | .ok ⟨leftShape, hleft⟩ =>
      match computeOperationShapeResult schema right with
      | .error error => .unknown (.rightShapeBuild error)
      | .ok ⟨rightShape, hright⟩ =>
          match decideStrictShapeEquivalent schema leftShape rightShape with
          | .accepted proof basis =>
              .accepted
                ⟨leftShape, rightShape, hleft, hright, proof⟩
                {
                  leftShape := leftShape
                  rightShape := rightShape
                  leftComputed := hleft
                  rightComputed := hright
                  strictBasis := basis
                }
          | .rejected proof witness =>
              .rejected
                (fun ⟨actualLeft, actualRight, hactualLeft, hactualRight, hstrict⟩ => by
                  have hleftEq : actualLeft = leftShape := by
                    rw [hleft] at hactualLeft
                    exact (Except.ok.inj hactualLeft).symm
                  have hrightEq : actualRight = rightShape := by
                    rw [hright] at hactualRight
                    exact (Except.ok.inj hactualRight).symm
                  subst actualLeft
                  subst actualRight
                  exact proof hstrict)
                {
                  leftShape := leftShape
                  rightShape := rightShape
                  leftComputed := hleft
                  rightComputed := hright
                  strictCounterexample := witness
                }
          | .unknown reason => .unknown (.shapeReadiness reason)

/-- Every accepted operation verdict carries a sound proof of strict
equivalence between the exact computed shapes. -/
theorem operationEquivalence_accepted_sound
    {schema : Schema} {left right : Operation}
    (haccepted
      : ∃ proof basis,
          decideOperationEquivalence schema left right
          = CertifiedVerdict.accepted proof basis)
    : ∃ leftShape rightShape,
        computeOperationShape schema left = .ok leftShape
        ∧ computeOperationShape schema right = .ok rightShape
        ∧ StrictShapeEquivalent schema leftShape rightShape := by
  rcases haccepted with ⟨_proof, basis, _hresult⟩
  exact basis.sound

/-- Every rejected operation verdict carries a sound negation of strict
equivalence between any two shapes computed from the inputs. -/
theorem operationEquivalence_rejected_sound
    {schema : Schema} {left right : Operation}
    (hrejected
      : ∃ proof witness,
          decideOperationEquivalence schema left right
          = CertifiedVerdict.rejected proof witness)
    : ¬ ∃ leftShape rightShape,
          computeOperationShape schema left = .ok leftShape
          ∧ computeOperationShape schema right = .ok rightShape
          ∧ StrictShapeEquivalent schema leftShape rightShape := by
  rcases hrejected with ⟨proof, _witness, _hresult⟩
  exact proof

/-- A strict rejection over two successfully computed shapes is preserved by
the operation wrapper, including its exact strict counterexample payload. -/
theorem decideOperationEquivalence_rejected_of_computed
    {schema : Schema} {left right : Operation}
    {leftShape rightShape : OperationShape}
    (hleftCompute : computeOperationShape schema left = .ok leftShape)
    (hrightCompute : computeOperationShape schema right = .ok rightShape)
    {strictProof : ¬ StrictShapeEquivalent schema leftShape rightShape}
    {strictWitness : StrictShapeEquivalentCounterexample}
    (hstrict
      : decideStrictShapeEquivalent schema leftShape rightShape
        = CertifiedVerdict.rejected strictProof strictWitness)
    : ∃ operationProof operationWitness,
        decideOperationEquivalence schema left right
          = CertifiedVerdict.rejected operationProof operationWitness
        ∧ operationWitness.strictCounterexample = strictWitness := by
  let operationProof :
      ¬ ∃ actualLeft actualRight,
          computeOperationShape schema left = .ok actualLeft
          ∧ computeOperationShape schema right = .ok actualRight
          ∧ StrictShapeEquivalent schema actualLeft actualRight :=
    fun ⟨actualLeft, actualRight, hactualLeft, hactualRight, hactualStrict⟩ => by
      rw [hleftCompute] at hactualLeft
      rw [hrightCompute] at hactualRight
      have hleftEq := Except.ok.inj hactualLeft
      have hrightEq := Except.ok.inj hactualRight
      subst actualLeft
      subst actualRight
      exact strictProof hactualStrict
  let operationWitness : OperationEquivalenceCounterexample schema left right :=
    {
      leftShape := leftShape
      rightShape := rightShape
      leftComputed := hleftCompute
      rightComputed := hrightCompute
      strictCounterexample := strictWitness
    }
  refine ⟨operationProof, operationWitness, ?_, rfl⟩
  have hleftResult :=
    computeOperationShapeResult_eq_ok schema left leftShape hleftCompute
  have hrightResult :=
    computeOperationShapeResult_eq_ok schema right rightShape hrightCompute
  unfold decideOperationEquivalence
  rw [hleftResult, hrightResult]
  simp only
  rw [hstrict]

/-- Successful shape computation transports strict support equality back to
the source operations. Both source-support equations are explicit because
complete-normal syntax can erase source variables from all-empty cases. -/
theorem operationBoolVarsEquivalent_of_computed_strictShapeEquivalent
    (schema : Schema) (left right : Operation)
    (leftShape rightShape : OperationShape)
    (hleftCompute : computeOperationShape schema left = .ok leftShape)
    (hrightCompute : computeOperationShape schema right = .ok rightShape)
    (hstrict : StrictShapeEquivalent schema leftShape rightShape)
    : NormalForm.operationBoolVarsEquivalent left right := by
  have hleftSupport :=
    computeOperationShape_support schema left leftShape hleftCompute
  have hrightSupport :=
    computeOperationShape_support schema right rightShape hrightCompute
  intro varName
  simpa [hleftSupport, hrightSupport] using hstrict.2 varName

/-- Successful ready computation rules out every operation-level `unknown`
reason. -/
theorem decideOperationEquivalence_not_unknown_of_computed
    {schema : Schema} {left right : Operation}
    {leftShape rightShape : OperationShape}
    (hleftCompute : computeOperationShape schema left = .ok leftShape)
    (hrightCompute : computeOperationShape schema right = .ok rightShape)
    (hready : ShapeComparisonReady schema leftShape rightShape)
    : ¬ ∃ reason,
          decideOperationEquivalence schema left right
          = CertifiedVerdict.unknown reason := by
  rintro ⟨reason, hunknown⟩
  have hleftResult :=
    computeOperationShapeResult_eq_ok schema left leftShape hleftCompute
  have hrightResult :=
    computeOperationShapeResult_eq_ok schema right rightShape hrightCompute
  unfold decideOperationEquivalence at hunknown
  rw [hleftResult, hrightResult] at hunknown
  simp only at hunknown
  rcases decideStrictShapeEquivalent_complete hready with
    ⟨proof, basis, hstrict⟩ | ⟨proof, witness, hstrict⟩
  · rw [hstrict] at hunknown
    contradiction
  · rw [hstrict] at hunknown
    contradiction

/-- Under successful ready shape computation, operation acceptance is exactly
strict equivalence of those computed shapes. -/
theorem decideOperationEquivalence_accepted_iff_of_computed
    {schema : Schema} {left right : Operation}
    {leftShape rightShape : OperationShape}
    (hleftCompute : computeOperationShape schema left = .ok leftShape)
    (hrightCompute : computeOperationShape schema right = .ok rightShape)
    (hready : ShapeComparisonReady schema leftShape rightShape)
    : (∃ proof basis,
        decideOperationEquivalence schema left right
        = CertifiedVerdict.accepted proof basis)
      ↔ StrictShapeEquivalent schema leftShape rightShape := by
  constructor
  · intro haccepted
    rcases operationEquivalence_accepted_sound haccepted with
      ⟨actualLeft, actualRight, hactualLeft, hactualRight, hstrict⟩
    rw [hleftCompute] at hactualLeft
    rw [hrightCompute] at hactualRight
    have hleftEq := Except.ok.inj hactualLeft
    have hrightEq := Except.ok.inj hactualRight
    subst actualLeft
    subst actualRight
    exact hstrict
  · intro hstrict
    cases hresult : decideOperationEquivalence schema left right with
    | accepted proof basis => exact ⟨proof, basis, rfl⟩
    | rejected proof witness =>
        exact False.elim
          (proof ⟨leftShape, rightShape, hleftCompute, hrightCompute, hstrict⟩)
    | unknown reason =>
        exact False.elim
          (decideOperationEquivalence_not_unknown_of_computed
            hleftCompute hrightCompute hready ⟨reason, hresult⟩)

/-- Every valid operation pair over a well-formed schema receives a definitive
accepted or rejected verdict; operation and shape readiness cannot produce
`unknown` on this intended domain. -/
theorem decideOperationEquivalence_complete
    {schema : Schema} {left right : Operation}
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hleftValid : Validation.operationDefinitionValid schema left)
    (hrightValid : Validation.operationDefinitionValid schema right)
    : (∃ proof basis,
        decideOperationEquivalence schema left right
        = CertifiedVerdict.accepted proof basis)
      ∨ (∃ proof witness,
          decideOperationEquivalence schema left right
          = CertifiedVerdict.rejected proof witness) := by
  rcases computeOperationShape_total schema left hschema hleftValid with
    ⟨leftShape, hleftCompute, hleftWellFormed, hleftFull, _hleftSupport⟩
  rcases computeOperationShape_total schema right hschema hrightValid with
    ⟨rightShape, hrightCompute, hrightWellFormed, hrightFull, _hrightSupport⟩
  have hready : ShapeComparisonReady schema leftShape rightShape :=
    ⟨hleftWellFormed, hleftFull, hrightWellFormed, hrightFull⟩
  cases hresult : decideOperationEquivalence schema left right with
  | accepted proof basis => exact Or.inl ⟨proof, basis, rfl⟩
  | rejected proof witness => exact Or.inr ⟨proof, witness, rfl⟩
  | unknown reason =>
      exact False.elim
        (decideOperationEquivalence_not_unknown_of_computed
          hleftCompute hrightCompute hready ⟨reason, hresult⟩)

/-- Acceptance is sound for the strongest source-operation semantics supported
by complete-normalization soundness: all executions whose variable values are
complete for the left operation's Boolean support. Equal variable definitions
remain explicit because response shapes do not retain defaults or declared
types. -/
theorem decideOperationEquivalence_accepted_semanticallyEquivalent
    {schema : Schema} {left right : Operation}
    (haccepted
      : ∃ proof basis,
          decideOperationEquivalence schema left right
          = CertifiedVerdict.accepted proof basis)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hleftValid : Validation.operationDefinitionValid schema left)
    (hrightValid : Validation.operationDefinitionValid schema right)
    (hdefinitions : left.variableDefinitions = right.variableDefinitions)
    : NormalForm.operationsSemanticallyEquivalentForCompleteBoolVars
        schema (NormalForm.operationBoolVars left) left right := by
  rcases operationEquivalence_accepted_sound haccepted with
    ⟨leftShape, rightShape, hleftCompute, hrightCompute, hstrict⟩
  have hsupport : NormalForm.operationBoolVarsEquivalent left right :=
    operationBoolVarsEquivalent_of_computed_strictShapeEquivalent
      schema left right leftShape rightShape hleftCompute hrightCompute hstrict
  have hnormalized :=
    (computeOperationShape_strictEquivalent_iff_normalizedEqualUpToReordering
      schema left right leftShape rightShape hschema hleftValid hrightValid
      hsupport hleftCompute hrightCompute).mp hstrict
  unfold NormalForm.operationsSemanticallyEquivalentForCompleteBoolVars
  intro ObjectRef resolvers variableValues fuel source hcomplete
  exact
    NormalForm.CompleteNormalization.completeNormalizeOperations_equalUpToReordering_semanticallyEquivalent
      hschema hleftValid hrightValid hdefinitions hsupport hnormalized
      resolvers variableValues fuel source hcomplete

/-- Under the normalizer's exact uniqueness premises, unrestricted semantic
equivalence forces the executable comparator to accept. No equality of variable
definitions is needed in this direction. -/
theorem decideOperationEquivalence_accepts_semanticallyEquivalent
    {schema : Schema} {left right : Operation}
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hleftValid : Validation.operationDefinitionValid schema left)
    (hrightValid : Validation.operationDefinitionValid schema right)
    (hleftFields : NormalForm.operationFieldsValidInPossibleTypes schema left)
    (hrightFields : NormalForm.operationFieldsValidInPossibleTypes schema right)
    (hleftBoolFeasible : NormalForm.operationBoolTypeConditionFeasible schema left)
    (hrightBoolFeasible : NormalForm.operationBoolTypeConditionFeasible schema right)
    (hsupport : NormalForm.operationBoolVarsEquivalent left right)
    (hsem : NormalForm.operationsSemanticallyEquivalent schema left right)
    : ∃ proof basis,
        decideOperationEquivalence schema left right
        = CertifiedVerdict.accepted proof basis := by
  rcases computeOperationShape_total schema left hschema hleftValid with
    ⟨leftShape, hleftCompute, hleftWellFormed, hleftFull, _hleftSupport⟩
  rcases computeOperationShape_total schema right hschema hrightValid with
    ⟨rightShape, hrightCompute, hrightWellFormed, hrightFull, _hrightSupport⟩
  have hnormalized :
      NormalForm.completeNormalOperationsEqualUpToReordering
        (NormalForm.completeNormalizeOperation schema left)
        (NormalForm.completeNormalizeOperation schema right) :=
    NormalForm.CompleteNormalization.completeNormalizeOperation_uniqueUpToReordering
      hschema hleftValid hrightValid hleftFields hrightFields
      hleftBoolFeasible hrightBoolFeasible hsupport hsem
  have hstrict : StrictShapeEquivalent schema leftShape rightShape :=
    (computeOperationShape_strictEquivalent_iff_normalizedEqualUpToReordering
      schema left right leftShape rightShape hschema hleftValid hrightValid
      hsupport hleftCompute hrightCompute).mpr hnormalized
  have hready : ShapeComparisonReady schema leftShape rightShape :=
    ⟨hleftWellFormed, hleftFull, hrightWellFormed, hrightFull⟩
  exact
    (decideOperationEquivalence_accepted_iff_of_computed
      hleftCompute hrightCompute hready).mpr hstrict

/-- Under the same uniqueness premises, a rejected comparator result rules out
unrestricted semantic equivalence. -/
theorem decideOperationEquivalence_rejected_not_semanticallyEquivalent
    {schema : Schema} {left right : Operation}
    (hrejected
      : ∃ proof witness,
          decideOperationEquivalence schema left right
          = CertifiedVerdict.rejected proof witness)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hleftValid : Validation.operationDefinitionValid schema left)
    (hrightValid : Validation.operationDefinitionValid schema right)
    (hleftFields : NormalForm.operationFieldsValidInPossibleTypes schema left)
    (hrightFields : NormalForm.operationFieldsValidInPossibleTypes schema right)
    (hleftBoolFeasible : NormalForm.operationBoolTypeConditionFeasible schema left)
    (hrightBoolFeasible : NormalForm.operationBoolTypeConditionFeasible schema right)
    (hsupport : NormalForm.operationBoolVarsEquivalent left right)
    : ¬ NormalForm.operationsSemanticallyEquivalent schema left right := by
  intro hsem
  rcases decideOperationEquivalence_accepts_semanticallyEquivalent
      hschema hleftValid hrightValid hleftFields hrightFields
      hleftBoolFeasible hrightBoolFeasible hsupport hsem with
    ⟨acceptedProof, acceptedBasis, haccepted⟩
  rcases hrejected with ⟨rejectedProof, rejectedWitness, hrejected⟩
  rw [hrejected] at haccepted
  contradiction

end ResponseShape

end GraphQL
