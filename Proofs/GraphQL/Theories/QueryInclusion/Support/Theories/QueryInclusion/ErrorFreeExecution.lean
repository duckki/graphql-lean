import GraphQL.Theories.QueryInclusion
import Proofs.GraphQL.Theories.QueryInclusion.Support.Algorithms.ExecutionUngrouped.Equivalence.Collection.StateInvariant
import Proofs.GraphQL.Theories.QueryInclusion.Support.Algorithms.ExecutionUngrouped.Equivalence.Core

/-! Supporting lemmas extracted from commit `7797374fd` for the talk exercises. -/

namespace GraphQL.QueryInclusion

open Execution
open SelectionConditions
open Algorithms.ExecutionUngroupedUncached
open Algorithms.ExecutionUngroupedUncached.Eager

def executableFieldsSameResolver (fields : List ExecutableField) : Prop :=
  ∀ first later,
    first ∈ fields
    -> later ∈ fields
    -> first.fieldName = later.fieldName
        ∧ Argument.argumentsEquivalent first.arguments later.arguments

abbrev RuntimePlan := Nat -> Name -> Name

def RuntimePlan.Valid (schema : Schema) (plan : RuntimePlan) : Prop :=
  ∀ depth typeName,
    schema.getPossibleTypes typeName ≠ []
    -> plan depth typeName ∈ schema.getPossibleTypes typeName

def RuntimePlan.cons (head : Name -> Name) (tail : RuntimePlan) : RuntimePlan
  | 0, typeName => head typeName
  | depth + 1, typeName => tail depth typeName

theorem RuntimePlan.Valid.cons
    {schema : Schema} {head : Name -> Name} {tail : RuntimePlan}
    (hhead
      : ∀ typeName,
          schema.getPossibleTypes typeName ≠ []
          -> head typeName ∈ schema.getPossibleTypes typeName)
    (htail : tail.Valid schema)
    : (RuntimePlan.cons head tail).Valid schema := by
  intro depth typeName hpossible
  cases depth with
  | zero => exact hhead typeName hpossible
  | succ depth => exact htail depth typeName hpossible

end GraphQL.QueryInclusion
