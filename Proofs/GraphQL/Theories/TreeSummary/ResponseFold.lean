import GraphQL.Theories.TreeSummary.ResponseFold

/-! Backend-independent lemmas for tree-summary response folds. -/

namespace GraphQL
namespace TreeSummary

open GraphQL.Execution
open GraphQL.AnnotatedExecution

universe u v

def foldAnnotatedResponseFieldsResult (algebra : ConcreteAlgebra)
    : Result (List AnnotatedResponseField) -> algebra.Summary
  | .error _errors => algebra.empty
  | .ok (fields, _errors) => foldAnnotatedResponseFields algebra fields

def foldAnnotatedResponseValueResult (algebra : ConcreteAlgebra)
    : Result AnnotatedResponseValue -> algebra.Summary
  | .error _errors => algebra.empty
  | .ok (value, _errors) => foldAnnotatedResponseValueChildren algebra value

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

namespace CompatibilityCore

theorem empty_related_any
    {concrete : ConcreteAlgebra.{u}} {abstract : Algebra.{v}}
    (compatible : CompatibilityCore concrete abstract)
    (abstractValue : abstract.Summary)
    : compatible.related concrete.empty abstractValue :=
  compatible.related_mono concrete.empty abstract.empty abstractValue
    compatible.empty_related (compatible.abstractLawful.empty_le abstractValue)

theorem combineFieldsResult_related
    {concrete : ConcreteAlgebra.{u}} {abstract : Algebra.{v}}
    (compatible : CompatibilityCore concrete abstract)
    (left right : Result (List AnnotatedResponseField))
    (abstractLeft abstractRight : abstract.Summary)
    (hleft
      : compatible.related (foldAnnotatedResponseFieldsResult concrete left) abstractLeft)
    (hright
      : compatible.related
          (foldAnnotatedResponseFieldsResult concrete right) abstractRight)
    : compatible.related
        (foldAnnotatedResponseFieldsResult concrete
          (Result.combine List.append left right))
        (abstract.combine abstractLeft abstractRight) := by
  cases left with
  | error leftErrors =>
      cases right <;> exact compatible.empty_related_any _
  | ok left =>
      rcases left with ⟨leftFields, leftErrors⟩
      cases right with
      | error rightErrors => exact compatible.empty_related_any _
      | ok right =>
          rcases right with ⟨rightFields, rightErrors⟩
          simp only [Result.combine, foldAnnotatedResponseFieldsResult] at hleft hright ⊢
          change compatible.related
            (foldAnnotatedResponseFields concrete (leftFields ++ rightFields))
            (abstract.combine abstractLeft abstractRight)
          rw [foldAnnotatedResponseFields_append concrete compatible.concreteLawful]
          exact compatible.combine_related _ _ _ _ hleft hright

theorem combineValuesResult_related
    {concrete : ConcreteAlgebra.{u}} {abstract : Algebra.{v}}
    (compatible : CompatibilityCore concrete abstract)
    (left : Result AnnotatedResponseValue)
    (right : Result (List AnnotatedResponseValue))
    (abstractChild : abstract.Summary)
    (hleft
      : compatible.related (foldAnnotatedResponseValueResult concrete left)
          (foldChildSummaryForValueResult abstract abstractChild left))
    (hright
      : compatible.related (foldAnnotatedResponseValuesResult concrete right)
          (foldChildSummaryForValuesResult abstract abstractChild right))
    : let combined := Result.combine List.cons left right
      compatible.related (foldAnnotatedResponseValuesResult concrete combined)
        (foldChildSummaryForValuesResult abstract abstractChild combined) := by
  cases left with
  | error leftErrors =>
      cases right <;>
        simpa [Result.combine, foldAnnotatedResponseValuesResult,
          foldChildSummaryForValuesResult] using compatible.empty_related
  | ok left =>
      rcases left with ⟨leftValue, leftErrors⟩
      cases right with
      | error rightErrors =>
          simpa [Result.combine, foldAnnotatedResponseValuesResult,
            foldChildSummaryForValuesResult] using compatible.empty_related
      | ok right =>
          rcases right with ⟨rightValues, rightErrors⟩
          simp only [Result.combine, foldAnnotatedResponseValuesResult,
            foldChildSummaryForValuesResult, foldAnnotatedResponseValues,
            foldChildSummaryForValues]
          exact compatible.combine_related _ _ _ _ hleft hright

theorem completeNonNullResult_related
    {concrete : ConcreteAlgebra.{u}} {abstract : Algebra.{v}}
    (compatible : CompatibilityCore concrete abstract)
    (completed : Result AnnotatedResponseValue)
    (abstractChild : abstract.Summary)
    (hcompleted
      : compatible.related (foldAnnotatedResponseValueResult concrete completed)
          (foldChildSummaryForValueResult abstract abstractChild completed))
    : compatible.related
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
          foldChildSummaryForValueResult, foldAnnotatedResponseValueChildren,
          foldChildSummaryForValue]
      all_goals exact compatible.empty_related

end CompatibilityCore
end TreeSummary
end GraphQL
