import GraphQL.Theories.TreeSummary.ExactCasesOptimality
import GraphQL.Theories.TreeSummary.Syntactic
import GraphQL.SchemaWellFormedness
import GraphQL.Validation

/-! Concrete response-size model for `MaxResponseSize`.

The size of a response is the number of selected response-object fields at every nesting
level. Lists do not themselves add fields, but repeat the fields contained by their
elements. The one external model parameter bounds the multiplicity of every list layer.
-/

namespace GraphQL
namespace TreeSummary
namespace MaxResponseSize

-----------------------------------------------------------------------------------------
-- Algebra definition
-----------------------------------------------------------------------------------------

-- Maximum multiplicity contributed by list wrappers in one output type when every
-- resolver list has at most `listSize` elements.
def listMultiplier (listSize : Nat) : TypeRef -> Nat
  | .named _typeName => 1
  | .list inner => listSize * listMultiplier listSize inner
  | .nonNull inner => listMultiplier listSize inner

-- Maximum multiplicity of any field output available under this group's possible
-- runtime parent types.
def fieldListMultiplier (schema : Schema) (listSize : Nat) (group : CollectedFieldGroup)
    : Nat :=
  (group.fieldOutputTypes schema).foldl
    (fun multiplier outputType =>
      max multiplier (listMultiplier listSize outputType))
    1

-- Compositional upper bound on the number of response fields. Every collected response
-- name contributes one plus its completed child summary, simultaneous contributions
-- add, and alternative possible child types are joined with `Nat.max`.
def algebra (schema : Schema) (listSize : Nat) : Algebra :=
  {
    Summary := Nat
    empty := 0
    field :=
      fun group childSummary =>
        1 + fieldListMultiplier schema listSize group * childSummary
    combine := Nat.add
    join := Nat.max
  }

-----------------------------------------------------------------------------------------
-- Public analysis entry points
-----------------------------------------------------------------------------------------

namespace ExactCases

-- Higher-precision response-size estimate obtained by enumerating every feasible
-- condition combination before globally collecting response names.
def estimateOperation (schema : Schema) (listSize : Nat) (operation : Operation) : Nat :=
  TreeSummary.ExactCases.summarizeOperation (algebra schema listSize) schema operation

-- Exact-case estimate after applying operation-variable defaults and supplied values.
def estimateOperationWithVariables (schema : Schema) (listSize : Nat)
    (variableValues : Execution.VariableValues) (operation : Operation)
    : Nat :=
  TreeSummary.ExactCases.summarizeOperationWithVariables
    (fun _values => algebra schema listSize) schema variableValues operation

end ExactCases

namespace Syntactic

-- Faster structural response-size estimate. Conditions are resolved in node-local type
-- and Boolean case families; response-name pieces from separate syntactic nodes may
-- remain separate contributions.
def estimateOperation (schema : Schema) (listSize : Nat) (operation : Operation) : Nat :=
  TreeSummary.Syntactic.summarizeOperation (algebra schema listSize) schema operation

-- Fast syntactic estimate after applying operation-variable defaults and supplied
-- values.
def estimateOperationWithVariables (schema : Schema) (listSize : Nat)
    (variableValues : Execution.VariableValues) (operation : Operation)
    : Nat :=
  TreeSummary.Syntactic.summarizeOperationWithVariables
    (fun _values => algebra schema listSize) schema variableValues operation

end Syntactic

-----------------------------------------------------------------------------------------
-- Concrete response-size specification
-----------------------------------------------------------------------------------------

open Execution

mutual
  def responseValueSize : ResponseValue -> Nat
    | .null => 0
    | .scalar _value => 0
    | .object fields => responseObjectFieldsSize fields
    | .list values => responseValuesSize values

  def responseValuesSize : List ResponseValue -> Nat
    | [] => 0
    | value :: rest => responseValueSize value + responseValuesSize rest

  def responseObjectFieldsSize : List (Name × ResponseValue) -> Nat
    | [] => 0
    | (_responseName, value) :: rest =>
        1 + responseValueSize value + responseObjectFieldsSize rest
end

-- Actual response size is defined directly on the public execution result. It counts
-- every response-object field at every nesting level; lists only repeat their contents.
def actualSize (response : Response) : Nat :=
  responseValueSize response.data

mutual
  def resolverValueListsBounded (listSize : Nat) : ResolverValue ObjectRef -> Prop
    | .null => True
    | .scalar _value => True
    | .object _typeName _ref => True
    | .list values =>
        values.length ≤ listSize ∧ resolverValuesListsBounded listSize values

  def resolverValuesListsBounded (listSize : Nat) : List (ResolverValue ObjectRef) -> Prop
    | [] => True
    | value :: rest =>
        resolverValueListsBounded listSize value
        ∧ resolverValuesListsBounded listSize rest
end

-- Every successful resolver result, including lists nested inside another list, obeys
-- the uniform list-size assumption. This is a caller-supplied execution assumption, not
-- a universally witnessed correctness statement.
def ResolversRespectListSize (listSize : Nat) (resolvers : Resolvers ObjectRef) : Prop :=
  ∀ parentType fieldName arguments source resolved,
    resolvers.resolve parentType fieldName arguments source = some resolved
    -> resolverValueListsBounded listSize resolved

-----------------------------------------------------------------------------------------
-- Soundness statements
-----------------------------------------------------------------------------------------

namespace ExactCases

-- Public response-size bound for the default executor. Its theorem witness is
-- `MaxResponseSize.ExactCases.analysisSound` in
-- `Proofs.GraphQL.Theories.TreeSummary.MaxResponseSize`.
def AnalysisSound (schema : Schema) (listSize : Nat) (operation : Operation) : Prop :=
  SchemaWellFormedness.schemaWellFormed schema
  -> Validation.operationDefinitionValid schema operation
  -> ∀ (ObjectRef : Type) (resolvers : Resolvers ObjectRef)
        (variableValues : VariableValues) (source : ResolverValue ObjectRef),
      ResolversRespectListSize listSize resolvers
      -> actualSize (executeQuery schema resolvers variableValues operation source)
          ≤ estimateOperation schema listSize operation

-- Variable-aware response-size bound for the default executor. Its theorem witness is
-- `MaxResponseSize.ExactCases.analysisWithVariablesSound` in the response-size proof
-- module.
def AnalysisWithVariablesSound (schema : Schema) (listSize : Nat) (operation : Operation)
    : Prop :=
  SchemaWellFormedness.schemaWellFormed schema
  -> Validation.operationDefinitionValid schema operation
  -> ∀ (ObjectRef : Type) (resolvers : Resolvers ObjectRef)
        (variableValues : VariableValues) (source : ResolverValue ObjectRef),
      ResolversRespectListSize listSize resolvers
      -> actualSize (executeQuery schema resolvers variableValues operation source)
          ≤ estimateOperationWithVariables schema listSize variableValues operation

end ExactCases

namespace Syntactic

-- Public response-size bound for the fast syntactic estimator. Its direct theorem
-- witness is `MaxResponseSize.Syntactic.analysisSound` in the proof module.
def AnalysisSound (schema : Schema) (listSize : Nat) (operation : Operation) : Prop :=
  SchemaWellFormedness.schemaWellFormed schema
  -> Validation.operationDefinitionValid schema operation
  -> ∀ (ObjectRef : Type) (resolvers : Resolvers ObjectRef)
        (variableValues : VariableValues) (source : ResolverValue ObjectRef),
      ResolversRespectListSize listSize resolvers
      -> actualSize (executeQuery schema resolvers variableValues operation source)
          ≤ estimateOperation schema listSize operation

-- Variable-aware response-size bound for the fast estimator and default executor. Its
-- theorem witness is `MaxResponseSize.Syntactic.analysisWithVariablesSound` in the
-- response-size proof module.
def AnalysisWithVariablesSound (schema : Schema) (listSize : Nat) (operation : Operation)
    : Prop :=
  SchemaWellFormedness.schemaWellFormed schema
  -> Validation.operationDefinitionValid schema operation
  -> ∀ (ObjectRef : Type) (resolvers : Resolvers ObjectRef)
        (variableValues : VariableValues) (source : ResolverValue ObjectRef),
      ResolversRespectListSize listSize resolvers
      -> actualSize (executeQuery schema resolvers variableValues operation source)
          ≤ estimateOperationWithVariables schema listSize variableValues operation

end Syntactic

-----------------------------------------------------------------------------------------
-- Optimality statements
-----------------------------------------------------------------------------------------

namespace ExactCases

-- Local outcome semantics used by the exact-case optimality theorem. A field may
-- realize any child multiplicity through the model's maximum; the maximum itself is
-- included.
def outcomeSemantics (schema : Schema) (listSize : Nat)
    : TreeSummary.ExactCases.OutcomeSemantics :=
  {
    Summary := Nat
    empty := 0
    combine := Nat.add
    fieldOutcomes :=
      fun group childSummary outcome =>
        ∃ multiplicity,
          multiplicity ≤ fieldListMultiplier schema listSize group
          ∧ outcome = 1 + multiplicity * childSummary
  }

-- The unknown-variable exact-case estimate is the least upper bound of its recursively
-- feasible modeled response sizes. Its witness is
-- `MaxResponseSize.ExactCases.analysisOptimal` in the response-size proof module.
def AnalysisOptimal (schema : Schema) (listSize : Nat) (operation : Operation) : Prop :=
  Optimality.BestBound Nat.le Nat.le
    (TreeSummary.ExactCases.operationOutcomes (outcomeSemantics schema listSize)
      schema operation)
    (estimateOperation schema listSize operation)

-- Variable-aware form of `AnalysisOptimal`. Its witness is
-- `MaxResponseSize.ExactCases.analysisWithVariablesOptimal` in the response-size proof
-- module.
def AnalysisWithVariablesOptimal (schema : Schema) (listSize : Nat)
    (variableValues : Execution.VariableValues) (operation : Operation)
    : Prop :=
  Optimality.BestBound Nat.le Nat.le
    (TreeSummary.ExactCases.operationOutcomesWithVariables
      (outcomeSemantics schema listSize) schema variableValues operation)
    (estimateOperationWithVariables schema listSize variableValues operation)

end ExactCases

end MaxResponseSize
end TreeSummary
end GraphQL
