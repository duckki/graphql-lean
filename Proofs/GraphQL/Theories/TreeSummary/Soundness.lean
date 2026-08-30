import GraphQL.Theories.TreeSummary.Soundness

/-! Backend-independent lemmas for tree-summary response folds. -/

namespace GraphQL
namespace TreeSummary

open GraphQL.Execution
open GraphQL.AnnotatedExecution

universe u v

def foldAnnotatedResponseValueResult (algebra : ConcreteAlgebra)
    : Result AnnotatedResponseValue -> algebra.Summary
  | .error _errors => algebra.empty
  | .ok (value, _errors) => foldAnnotatedResponseValue algebra value

def foldAnnotatedResponseValuesResult (algebra : ConcreteAlgebra)
    : Result (List AnnotatedResponseValue) -> algebra.Summary
  | .error _errors => algebra.empty
  | .ok (values, _errors) => foldAnnotatedResponseValues algebra values

def foldChildSummaryForValueResult (algebra : Algebra) (childSummary : algebra.Summary)
    : Result AnnotatedResponseValue -> algebra.Summary
  | .error _errors => algebra.empty
  | .ok (value, _errors) => foldChildSummaryForValue algebra childSummary value

def foldChildSummaryForValuesResult (algebra : Algebra) (childSummary : algebra.Summary)
    : Result (List AnnotatedResponseValue) -> algebra.Summary
  | .error _errors => algebra.empty
  | .ok (values, _errors) => foldChildSummaryForValues algebra childSummary values

theorem foldAnnotatedResponseFields_append
    (algebra : ConcreteAlgebra.{u}) (lawful : algebra.Lawful)
    (left right : List AnnotatedResponseField)
    : foldAnnotatedResponseFields algebra (left ++ right)
      = algebra.combine (foldAnnotatedResponseFields algebra left)
          (foldAnnotatedResponseFields algebra right) := by
  induction left with
  | nil =>
      simpa [foldAnnotatedResponseFields] using
        (lawful.empty_combine (foldAnnotatedResponseFields algebra right)).symm
  | cons field rest ih =>
      cases field
      simp only [List.cons_append, foldAnnotatedResponseFields]
      rw [ih, lawful.combine_assoc]

namespace SoundnessCore

theorem empty_sound_any
    {concrete : ConcreteAlgebra.{u}} {abstract : Algebra.{v}}
    (soundness : SoundnessCore concrete abstract)
    (abstractValue : abstract.Summary)
    : soundness.approximates concrete.empty abstractValue :=
  soundness.approximates_upward concrete.empty abstract.empty abstractValue
    soundness.empty_sound (soundness.abstractLawful.empty_le abstractValue)

theorem combineFieldsResult_sound
    {concrete : ConcreteAlgebra.{u}} {abstract : Algebra.{v}}
    (soundness : SoundnessCore concrete abstract)
    (left right : Result (List AnnotatedResponseField))
    (abstractLeft abstractRight : abstract.Summary)
    (hleft
      : soundness.approximates
          (foldAnnotatedResponseFieldsResult concrete left) abstractLeft)
    (hright
      : soundness.approximates
          (foldAnnotatedResponseFieldsResult concrete right) abstractRight)
    : soundness.approximates
        (foldAnnotatedResponseFieldsResult concrete
          (Result.combine List.append left right))
        (abstract.combine abstractLeft abstractRight) := by
  cases left with
  | error leftErrors =>
      cases right <;> exact soundness.empty_sound_any _
  | ok left =>
      rcases left with ⟨leftFields, leftErrors⟩
      cases right with
      | error rightErrors => exact soundness.empty_sound_any _
      | ok right =>
          rcases right with ⟨rightFields, rightErrors⟩
          simp only [Result.combine, foldAnnotatedResponseFieldsResult] at hleft hright ⊢
          change soundness.approximates
            (foldAnnotatedResponseFields concrete (leftFields ++ rightFields))
            (abstract.combine abstractLeft abstractRight)
          rw [foldAnnotatedResponseFields_append concrete soundness.concreteLawful]
          exact soundness.combine_sound _ _ _ _ hleft hright

theorem combineValuesResult_sound
    {concrete : ConcreteAlgebra.{u}} {abstract : Algebra.{v}}
    (soundness : SoundnessCore concrete abstract)
    (left : Result AnnotatedResponseValue)
    (right : Result (List AnnotatedResponseValue))
    (abstractChild : abstract.Summary)
    (hleft
      : soundness.approximates (foldAnnotatedResponseValueResult concrete left)
          (foldChildSummaryForValueResult abstract abstractChild left))
    (hright
      : soundness.approximates (foldAnnotatedResponseValuesResult concrete right)
          (foldChildSummaryForValuesResult abstract abstractChild right))
    : let combined := Result.combine List.cons left right
      soundness.approximates (foldAnnotatedResponseValuesResult concrete combined)
        (foldChildSummaryForValuesResult abstract abstractChild combined) := by
  cases left with
  | error leftErrors =>
      cases right <;>
        simpa [Result.combine, foldAnnotatedResponseValuesResult,
          foldChildSummaryForValuesResult] using soundness.empty_sound
  | ok left =>
      rcases left with ⟨leftValue, leftErrors⟩
      cases right with
      | error rightErrors =>
          simpa [Result.combine, foldAnnotatedResponseValuesResult,
            foldChildSummaryForValuesResult] using soundness.empty_sound
      | ok right =>
          rcases right with ⟨rightValues, rightErrors⟩
          simp only [Result.combine, foldAnnotatedResponseValuesResult,
            foldChildSummaryForValuesResult, foldAnnotatedResponseValues,
            foldChildSummaryForValues]
          exact soundness.combine_sound _ _ _ _ hleft hright

theorem completeNonNullResult_sound
    {concrete : ConcreteAlgebra.{u}} {abstract : Algebra.{v}}
    (soundness : SoundnessCore concrete abstract)
    (completed : Result AnnotatedResponseValue)
    (abstractChild : abstract.Summary)
    (hcompleted
      : soundness.approximates (foldAnnotatedResponseValueResult concrete completed)
          (foldChildSummaryForValueResult abstract abstractChild completed))
    : soundness.approximates
        (foldAnnotatedResponseValueResult concrete
          (completeNonNullAnnotatedResponseValue completed))
        (foldChildSummaryForValueResult abstract abstractChild
          (completeNonNullAnnotatedResponseValue completed)) := by
  cases completed with
  | error errors =>
      simpa [completeNonNullAnnotatedResponseValue,
        foldAnnotatedResponseValueResult,
        foldChildSummaryForValueResult] using hcompleted
  | ok completed =>
      rcases completed with ⟨value, errors⟩
      cases value <;> cases errors <;>
        simp_all [completeNonNullAnnotatedResponseValue,
          foldAnnotatedResponseValueResult,
          foldChildSummaryForValueResult, foldAnnotatedResponseValue,
          foldChildSummaryForValue]
      all_goals exact soundness.empty_sound

end SoundnessCore
end TreeSummary
end GraphQL
