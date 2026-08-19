import GraphQL.Theories.AnnotatedExecution
import GraphQL.Theories.TreeSummary.Core

/-! Tree-summary folds over annotated execution responses. -/

namespace GraphQL
namespace TreeSummary

open GraphQL.AnnotatedExecution

universe u v

-----------------------------------------------------------------------------------------
-- Abstract algebra folding of annotated responses
-----------------------------------------------------------------------------------------

-- Replays only the child-response shape of one completed field value in an abstract
-- algebra. Null and scalar values have no child fields, objects contribute one child
-- summary, and lists combine the child shapes of their elements. Analyses define any
-- numeric cardinality or cost measure separately.
mutual
  def foldChildSummaryForValue (algebra : Algebra) (childSummary : algebra.Summary)
      : AnnotatedResponseValue -> algebra.Summary
    | .null => algebra.empty
    | .scalar _value => algebra.empty
    | .object _runtimeType _fields => childSummary
    | .list values => foldChildSummaryForValues algebra childSummary values

  def foldChildSummaryForValues (algebra : Algebra) (childSummary : algebra.Summary)
      : List AnnotatedResponseValue -> algebra.Summary
    | [] => algebra.empty
    | value :: rest =>
        algebra.combine
          (foldChildSummaryForValue algebra childSummary value)
          (foldChildSummaryForValues algebra childSummary rest)
end

-----------------------------------------------------------------------------------------
-- Concrete algebra over annotated responses
-----------------------------------------------------------------------------------------

-- A concrete algebra observes the exact resolver call selected by one execution.
-- `child` is synthesized from the object fields contained in the completed value;
-- lists combine the child summaries of all returned items. There is intentionally no
-- concrete `join`: execution has already selected one runtime path.
structure ConcreteAlgebra where
  Summary : Type u
  empty : Summary
  combine : Summary -> Summary -> Summary
  field : ResolvedFieldProvenance -> AnnotatedResponseValue -> Summary -> Summary

-- Concrete response folds form a monoid. A value is the witness used when execution
-- regrouping changes only the association of simultaneously returned fields.
structure ConcreteAlgebra.Lawful (algebra : ConcreteAlgebra.{u}) : Prop where
  combine_assoc
    : ∀ left middle right,
        algebra.combine (algebra.combine left middle) right
        = algebra.combine left (algebra.combine middle right)
  empty_combine : ∀ value, algebra.combine algebra.empty value = value
  combine_empty : ∀ value, algebra.combine value algebra.empty = value

-- Backend-independent obligations relating one concrete response fold to one abstract
-- summary algebra. Exact and syntactic traversal contracts extend this core with only
-- the field-transfer obligation specific to their grouping strategy.
structure CompatibilityCore (concrete : ConcreteAlgebra.{u}) (abstract : Algebra.{v})
    : Type (max u v) where
  related : concrete.Summary -> abstract.Summary -> Prop
  concreteLawful : concrete.Lawful
  abstractLawful : abstract.Lawful
  empty_related : related concrete.empty abstract.empty
  combine_related
    : ∀ concreteLeft abstractLeft concreteRight abstractRight,
        related concreteLeft abstractLeft
        -> related concreteRight abstractRight
        -> related (concrete.combine concreteLeft concreteRight)
            (abstract.combine abstractLeft abstractRight)
  related_mono
    : ∀ concreteValue abstractLower abstractUpper,
        related concreteValue abstractLower
        -> abstractLawful.le abstractLower abstractUpper
        -> related concreteValue abstractUpper

-- Folds an annotated response. Lists combine the summaries of their returned items, and
-- object fields combine the summaries of response-name groups executed together.
mutual
  def foldAnnotatedResponseValueChildren (algebra : ConcreteAlgebra)
      : AnnotatedResponseValue -> algebra.Summary
    | .null => algebra.empty
    | .scalar _value => algebra.empty
    | .object _runtimeType fields => foldAnnotatedResponseFields algebra fields
    | .list values => foldAnnotatedResponseValues algebra values

  def foldAnnotatedResponseValues (algebra : ConcreteAlgebra)
      : List AnnotatedResponseValue -> algebra.Summary
    | [] => algebra.empty
    | value :: rest =>
        algebra.combine
          (foldAnnotatedResponseValueChildren algebra value)
          (foldAnnotatedResponseValues algebra rest)

  def foldAnnotatedResponseFields (algebra : ConcreteAlgebra)
      : List AnnotatedResponseField -> algebra.Summary
    | [] => algebra.empty
    | .resolved _responseName call value :: rest =>
        algebra.combine
          (algebra.field call value (foldAnnotatedResponseValueChildren algebra value))
          (foldAnnotatedResponseFields algebra rest)
end

def foldAnnotatedResponse (algebra : ConcreteAlgebra) (annotated : AnnotatedResponse)
    : algebra.Summary :=
  foldAnnotatedResponseValueChildren algebra annotated.data

end TreeSummary
end GraphQL
