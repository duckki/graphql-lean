import Proofs.GraphQL.Theories.ResponseShape.Comparison.Subset

/-!
Proof-carrying executable decisions of mutual and strict response-shape
equivalence.

Both directional semantic searches share the subset comparator's finite
`2^n` assignment traversal and retain its proof-relevant accepted bases. The
strict comparator then checks Boolean-support membership extensionally. All
semantic and support failures are classified before readiness, so a concrete
rejection always outranks `unknown`.
-/

namespace GraphQL

namespace ResponseShape

/-- Absence of a support mismatch is exactly extensional support equality. -/
theorem firstBoolSupportMismatch?_eq_none_iff (left right : List NormalForm.BoolVar)
    : firstBoolSupportMismatch? left right = none ↔ BoolSupportEquivalent left right := by
  unfold BoolSupportEquivalent
  rw [firstBoolSupportMismatch?, List.find?_eq_none]
  constructor
  · intro hnone varName
    by_cases hunion : varName ∈ supportUnion left right
    · by_cases hequivalent : varName ∈ left ↔ varName ∈ right
      · exact hequivalent
      · exact False.elim
          (hnone varName hunion (by simp [hequivalent]))
    · have hleft : varName ∉ left := by
        intro hmem
        exact hunion
          ((mem_supportUnion_iff varName left right).mpr (Or.inl hmem))
      have hright : varName ∉ right := by
        intro hmem
        exact hunion
          ((mem_supportUnion_iff varName left right).mpr (Or.inr hmem))
      simp [hleft, hright]
  · intro hequivalent varName _hunion
    simp [hequivalent varName]

/-- The executable support bit decides membership equivalence rather than list
equality, so order and duplicate occurrences are unobservable. -/
theorem boolSupportEquivalentBool_iff (left right : List NormalForm.BoolVar)
    : boolSupportEquivalentBool left right = true ↔ BoolSupportEquivalent left right := by
  rw [boolSupportEquivalentBool, Option.isNone_iff_eq_none,
    firstBoolSupportMismatch?_eq_none_iff]

/-- A returned support variable has different membership on the two sides. -/
theorem firstBoolSupportMismatch?_eq_some_mismatch
    {left right : List NormalForm.BoolVar} {varName : NormalForm.BoolVar}
    (hsome : firstBoolSupportMismatch? left right = some varName)
    : ¬ (varName ∈ left ↔ varName ∈ right) := by
  have hfound :=
    List.find?_some
      (p := fun candidate =>
        !(decide (candidate ∈ left ↔ candidate ∈ right)))
      (by simpa only [firstBoolSupportMismatch?] using hsome)
  intro hequivalent
  simp [hequivalent] at hfound

/-- Every returned support mismatch disproves extensional support equality. -/
theorem firstBoolSupportMismatch?_eq_some_not_equivalent
    {left right : List NormalForm.BoolVar} {varName : NormalForm.BoolVar}
    (hsome : firstBoolSupportMismatch? left right = some varName)
    : ¬ BoolSupportEquivalent left right := by
  intro hequivalent
  exact (firstBoolSupportMismatch?_eq_some_mismatch hsome)
    (hequivalent varName)

/-- Extensional Boolean-support equivalence is constructively decidable. -/
instance instDecidableBoolSupportEquivalent (left right : List NormalForm.BoolVar)
    : Decidable (BoolSupportEquivalent left right) :=
  decidable_of_iff (boolSupportEquivalentBool left right = true)
    (boolSupportEquivalentBool_iff left right)

/-- Mutual shape subset is constructively decidable by its two finite semantic
searches. -/
instance instDecidableShapeEquivalent (schema : Schema) (left right : OperationShape)
    : Decidable (ShapeEquivalent schema left right) := by
  unfold ShapeEquivalent
  infer_instance

/-- Strict shape equivalence is constructively decidable by mutual subset and
the extensional support check. -/
instance instDecidableStrictShapeEquivalent
    (schema : Schema) (left right : OperationShape)
    : Decidable (StrictShapeEquivalent schema left right) := by
  unfold StrictShapeEquivalent
  infer_instance

/-- The retained directional finite bases independently prove mutual subset. -/
theorem ShapeEquivalentAcceptedBasis.sound
    {schema : Schema} {left right : OperationShape}
    (basis : ShapeEquivalentAcceptedBasis schema left right)
    : ShapeEquivalent schema left right :=
  ⟨basis.leftToRight.sound, basis.rightToLeft.sound⟩

/-- The strict accepted basis independently proves both footprint and support
equivalence. -/
theorem StrictShapeEquivalentAcceptedBasis.sound
    {schema : Schema} {left right : OperationShape}
    (basis : StrictShapeEquivalentAcceptedBasis schema left right)
    : StrictShapeEquivalent schema left right :=
  ⟨basis.shapeEquivalent.sound, basis.boolSupportEquivalent⟩

private inductive SemanticShapeEquivalentVerdict
    (schema : Schema) (left right : OperationShape) where
  | accepted
    (proof : ShapeEquivalent schema left right)
    (basis : ShapeEquivalentAcceptedBasis schema left right)
  | rejected
    (proof : ¬ ShapeEquivalent schema left right)
    (witness : ShapeEquivalentCounterexample)

/-- Computes both directional subset failures without consulting readiness or
starting any traversal separate from `shapeSubsetCounterexample?`. -/
private def decideSemanticShapeEquivalent (schema : Schema) (left right : OperationShape)
    : SemanticShapeEquivalentVerdict schema left right :=
  match hleftToRight : shapeSubsetCounterexample? schema left right with
  | some counterexample =>
      .rejected
        (fun hequivalent =>
          (shapeSubsetCounterexample?_eq_some_not_shapeSubset hleftToRight) hequivalent.1)
        (.leftNotSubsetRight counterexample)
  | none =>
      match hrightToLeft : shapeSubsetCounterexample? schema right left with
      | some counterexample =>
          .rejected
            (fun hequivalent =>
              (shapeSubsetCounterexample?_eq_some_not_shapeSubset hrightToLeft)
                hequivalent.2)
            (.rightNotSubsetLeft counterexample)
      | none =>
          .accepted
            ⟨(shapeSubsetCounterexample?_eq_none_iff_shapeSubset schema left right).mp
              hleftToRight,
              (shapeSubsetCounterexample?_eq_none_iff_shapeSubset schema right left).mp
                hrightToLeft
            ⟩
            {
              leftToRight :=
                subsetAcceptedBasis_of_noCounterexample hleftToRight
              rightToLeft :=
                subsetAcceptedBasis_of_noCounterexample hrightToLeft
            }

private inductive SemanticStrictShapeEquivalentVerdict
    (schema : Schema) (left right : OperationShape) where
  | accepted
    (proof : StrictShapeEquivalent schema left right)
    (basis : StrictShapeEquivalentAcceptedBasis schema left right)
  | rejected
    (proof : ¬ StrictShapeEquivalent schema left right)
    (witness : StrictShapeEquivalentCounterexample)

/-- Extends the mutual semantic decision with the extensional support check,
still without consulting readiness. -/
private def decideSemanticStrictShapeEquivalent
    (schema : Schema) (left right : OperationShape)
    : SemanticStrictShapeEquivalentVerdict schema left right :=
  match decideSemanticShapeEquivalent schema left right with
  | .rejected proof witness =>
      .rejected (fun hstrict => proof hstrict.1) (.footprint witness)
  | .accepted shapeProof shapeBasis =>
      match hsupport : firstBoolSupportMismatch? left.boolSupport right.boolSupport with
      | some varName =>
          .rejected
            (fun hstrict =>
              (firstBoolSupportMismatch?_eq_some_not_equivalent hsupport) hstrict.2)
            (.boolSupportMismatch varName)
      | none =>
          let supportProof :=
            (firstBoolSupportMismatch?_eq_none_iff left.boolSupport right.boolSupport).mp
              hsupport
          .accepted
            ⟨shapeProof, supportProof⟩
            {
              shapeEquivalent := shapeBasis
              boolSupportEquivalent := supportProof
            }

/--
Proof-carrying three-valued mutual-equivalence decision.

Both directional semantic searches precede readiness. Consequently either
directional counterexample rejects even when either shape is not ready;
`unknown` is possible only after mutual subset has been proved.
-/
def decideShapeEquivalent (schema : Schema) (left right : OperationShape)
    : ShapeEquivalentVerdict schema left right :=
  match decideSemanticShapeEquivalent schema left right with
  | .rejected proof witness => .rejected proof witness
  | .accepted proof basis =>
      match readinessFailure? schema left right with
      | some reason => .unknown reason
      | none => .accepted proof basis

/--
Proof-carrying three-valued strict-equivalence decision.

Directional footprint failures and the concrete support mismatch are all
checked before the shared readiness predicate. No support comparison uses list
equality.
-/
def decideStrictShapeEquivalent (schema : Schema) (left right : OperationShape)
    : StrictShapeEquivalentVerdict schema left right :=
  match decideSemanticStrictShapeEquivalent schema left right with
  | .rejected proof witness => .rejected proof witness
  | .accepted proof basis =>
      match readinessFailure? schema left right with
      | some reason => .unknown reason
      | none => .accepted proof basis

/-- Every accepted mutual-equivalence verdict carries a sound proof. -/
theorem shapeEquivalent_accepted_sound
    {schema : Schema} {left right : OperationShape}
    (haccepted
      : ∃ proof basis,
          decideShapeEquivalent schema left right = CertifiedVerdict.accepted proof basis)
    : ShapeEquivalent schema left right := by
  rcases haccepted with ⟨_proof, basis, _hresult⟩
  exact basis.sound

/-- Every rejected mutual-equivalence verdict carries a sound negation. -/
theorem shapeEquivalent_rejected_sound
    {schema : Schema} {left right : OperationShape}
    (hrejected
      : ∃ proof witness,
          decideShapeEquivalent schema left right
          = CertifiedVerdict.rejected proof witness)
    : ¬ ShapeEquivalent schema left right := by
  rcases hrejected with ⟨proof, _witness, _hresult⟩
  exact proof

/-- Mutual-equivalence `unknown` means exactly that both directional semantic
searches succeeded and their relation holds, but the shared readiness check
reported this reason. -/
theorem shapeEquivalent_unknown_characterization
    {schema : Schema} {left right : OperationShape}
    (reason : ShapeUnknownReason)
    : decideShapeEquivalent schema left right = CertifiedVerdict.unknown reason
      ↔ shapeSubsetCounterexample? schema left right = none
        ∧ shapeSubsetCounterexample? schema right left = none
        ∧ readinessFailure? schema left right = some reason
        ∧ ShapeEquivalent schema left right
        ∧ ¬ ShapeComparisonReady schema left right := by
  constructor
  · intro hunknown
    cases hsemantic : decideSemanticShapeEquivalent schema left right with
    | rejected proof witness =>
        simp [decideShapeEquivalent, hsemantic] at hunknown
    | accepted proof basis =>
        cases hreadiness : readinessFailure? schema left right with
        | none =>
            simp [decideShapeEquivalent, hsemantic, hreadiness] at hunknown
        | some actualReason =>
            have heq : actualReason = reason := by
              simpa [decideShapeEquivalent, hsemantic, hreadiness] using hunknown
            subst actualReason
            refine
              ⟨(shapeSubsetCounterexample?_eq_none_iff_shapeSubset
                  schema left right).mpr proof.1,
                (shapeSubsetCounterexample?_eq_none_iff_shapeSubset
                  schema right left).mpr proof.2,
                rfl, proof, ?_⟩
            intro hready
            have hnone :=
              (readinessFailure?_eq_none_iff schema left right).mpr hready
            rw [hreadiness] at hnone
            contradiction
  · rintro ⟨_hleftToRight, _hrightToLeft, hreadiness,
      hequivalent, _hnotReady⟩
    cases hsemantic : decideSemanticShapeEquivalent schema left right with
    | accepted proof basis =>
        simp [decideShapeEquivalent, hsemantic, hreadiness]
    | rejected proof witness =>
        exact False.elim (proof hequivalent)

/-- Under readiness, acceptance is equivalent to mutual footprint inclusion. -/
theorem decideShapeEquivalent_accepted_iff
    {schema : Schema} {left right : OperationShape}
    (hready : ShapeComparisonReady schema left right)
    : (∃ proof basis,
        decideShapeEquivalent schema left right = CertifiedVerdict.accepted proof basis)
      ↔ ShapeEquivalent schema left right := by
  constructor
  · exact shapeEquivalent_accepted_sound
  · intro hequivalent
    have hreadiness :=
      (readinessFailure?_eq_none_iff schema left right).mpr hready
    cases hsemantic : decideSemanticShapeEquivalent schema left right with
    | accepted proof basis =>
        exact ⟨proof, basis,
          by simp [decideShapeEquivalent, hsemantic, hreadiness]⟩
    | rejected proof witness =>
        exact False.elim (proof hequivalent)

/-- Under readiness, rejection is equivalent to failure of mutual footprint
inclusion. -/
theorem decideShapeEquivalent_rejected_iff
    {schema : Schema} {left right : OperationShape}
    (_hready : ShapeComparisonReady schema left right)
    : (∃ proof witness,
        decideShapeEquivalent schema left right = CertifiedVerdict.rejected proof witness)
      ↔ ¬ ShapeEquivalent schema left right := by
  constructor
  · exact shapeEquivalent_rejected_sound
  · intro hnotEquivalent
    cases hsemantic : decideSemanticShapeEquivalent schema left right with
    | accepted proof basis =>
        exact False.elim (hnotEquivalent proof)
    | rejected proof witness =>
        exact ⟨proof, witness,
          by simp [decideShapeEquivalent, hsemantic]⟩

/-- A ready mutual comparison returns accepted or rejected, never unknown. -/
theorem decideShapeEquivalent_complete
    {schema : Schema} {left right : OperationShape}
    (hready : ShapeComparisonReady schema left right)
    : (∃ proof basis,
        decideShapeEquivalent schema left right = CertifiedVerdict.accepted proof basis)
      ∨ (∃ proof witness,
          decideShapeEquivalent schema left right
          = CertifiedVerdict.rejected proof witness) := by
  cases hsemantic : decideSemanticShapeEquivalent schema left right with
  | accepted proof basis =>
      left
      have hreadiness :=
        (readinessFailure?_eq_none_iff schema left right).mpr hready
      exact ⟨proof, basis,
        by simp [decideShapeEquivalent, hsemantic, hreadiness]⟩
  | rejected proof witness =>
      right
      exact ⟨proof, witness,
        by simp [decideShapeEquivalent, hsemantic]⟩

/-- Every accepted strict-equivalence verdict carries a sound proof. -/
theorem strictShapeEquivalent_accepted_sound
    {schema : Schema} {left right : OperationShape}
    (haccepted
      : ∃ proof basis,
          decideStrictShapeEquivalent schema left right
          = CertifiedVerdict.accepted proof basis)
    : StrictShapeEquivalent schema left right := by
  rcases haccepted with ⟨_proof, basis, _hresult⟩
  exact basis.sound

/-- Every rejected strict-equivalence verdict carries a sound negation. -/
theorem strictShapeEquivalent_rejected_sound
    {schema : Schema} {left right : OperationShape}
    (hrejected
      : ∃ proof witness,
          decideStrictShapeEquivalent schema left right
          = CertifiedVerdict.rejected proof witness)
    : ¬ StrictShapeEquivalent schema left right := by
  rcases hrejected with ⟨proof, _witness, _hresult⟩
  exact proof

/-- Strict-equivalence `unknown` means exactly that both directional semantic
searches and the extensional support check succeeded, strict equivalence holds,
and the shared readiness check reported this reason. -/
theorem strictShapeEquivalent_unknown_characterization
    {schema : Schema} {left right : OperationShape}
    (reason : ShapeUnknownReason)
    : decideStrictShapeEquivalent schema left right = CertifiedVerdict.unknown reason
      ↔ shapeSubsetCounterexample? schema left right = none
        ∧ shapeSubsetCounterexample? schema right left = none
        ∧ firstBoolSupportMismatch? left.boolSupport right.boolSupport = none
        ∧ readinessFailure? schema left right = some reason
        ∧ StrictShapeEquivalent schema left right
        ∧ ¬ ShapeComparisonReady schema left right := by
  constructor
  · intro hunknown
    cases hsemantic : decideSemanticStrictShapeEquivalent schema left right with
    | rejected proof witness =>
        simp [decideStrictShapeEquivalent, hsemantic] at hunknown
    | accepted proof basis =>
        cases hreadiness : readinessFailure? schema left right with
        | none =>
            simp [decideStrictShapeEquivalent, hsemantic, hreadiness] at hunknown
        | some actualReason =>
            have heq : actualReason = reason := by
              simpa [decideStrictShapeEquivalent, hsemantic, hreadiness]
                using hunknown
            subst actualReason
            refine
              ⟨(shapeSubsetCounterexample?_eq_none_iff_shapeSubset
                  schema left right).mpr proof.1.1,
                (shapeSubsetCounterexample?_eq_none_iff_shapeSubset
                  schema right left).mpr proof.1.2,
                (firstBoolSupportMismatch?_eq_none_iff
                  left.boolSupport right.boolSupport).mpr proof.2,
                rfl, proof, ?_⟩
            intro hready
            have hnone :=
              (readinessFailure?_eq_none_iff schema left right).mpr hready
            rw [hreadiness] at hnone
            contradiction
  · rintro ⟨_hleftToRight, _hrightToLeft, _hsupport, hreadiness,
      hstrict, _hnotReady⟩
    cases hsemantic : decideSemanticStrictShapeEquivalent schema left right with
    | rejected proof witness =>
        exact False.elim (proof hstrict)
    | accepted proof basis =>
        simp [decideStrictShapeEquivalent, hsemantic, hreadiness]

/-- Under readiness, acceptance is equivalent to strict shape equivalence. -/
theorem decideStrictShapeEquivalent_accepted_iff
    {schema : Schema} {left right : OperationShape}
    (hready : ShapeComparisonReady schema left right)
    : (∃ proof basis,
        decideStrictShapeEquivalent schema left right
        = CertifiedVerdict.accepted proof basis)
      ↔ StrictShapeEquivalent schema left right := by
  constructor
  · exact strictShapeEquivalent_accepted_sound
  · intro hstrict
    have hreadiness :=
      (readinessFailure?_eq_none_iff schema left right).mpr hready
    cases hsemantic : decideSemanticStrictShapeEquivalent schema left right with
    | rejected proof witness =>
        exact False.elim (proof hstrict)
    | accepted proof basis =>
        exact ⟨proof, basis,
          by simp [decideStrictShapeEquivalent, hsemantic, hreadiness]⟩

/-- Under readiness, rejection is equivalent to failure of strict shape
equivalence. -/
theorem decideStrictShapeEquivalent_rejected_iff
    {schema : Schema} {left right : OperationShape}
    (_hready : ShapeComparisonReady schema left right)
    : (∃ proof witness,
        decideStrictShapeEquivalent schema left right
        = CertifiedVerdict.rejected proof witness)
      ↔ ¬ StrictShapeEquivalent schema left right := by
  constructor
  · exact strictShapeEquivalent_rejected_sound
  · intro hnotStrict
    cases hsemantic : decideSemanticStrictShapeEquivalent schema left right with
    | accepted proof basis =>
        exact False.elim (hnotStrict proof)
    | rejected proof witness =>
        exact ⟨proof, witness,
          by simp [decideStrictShapeEquivalent, hsemantic]⟩

/-- A ready strict comparison returns accepted or rejected, never unknown. -/
theorem decideStrictShapeEquivalent_complete
    {schema : Schema} {left right : OperationShape}
    (hready : ShapeComparisonReady schema left right)
    : (∃ proof basis,
        decideStrictShapeEquivalent schema left right
        = CertifiedVerdict.accepted proof basis)
      ∨ (∃ proof witness,
          decideStrictShapeEquivalent schema left right
          = CertifiedVerdict.rejected proof witness) := by
  cases hsemantic : decideSemanticStrictShapeEquivalent schema left right with
  | rejected proof witness =>
      right
      exact ⟨proof, witness,
        by simp [decideStrictShapeEquivalent, hsemantic]⟩
  | accepted proof basis =>
      left
      have hreadiness :=
        (readinessFailure?_eq_none_iff schema left right).mpr hready
      exact ⟨proof, basis,
        by simp [decideStrictShapeEquivalent, hsemantic, hreadiness]⟩

end ResponseShape

end GraphQL
