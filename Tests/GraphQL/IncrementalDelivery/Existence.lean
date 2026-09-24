import Proofs.GraphQL.IncrementalDelivery.Correctness.QueryExistence
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Initialization existence is unconditional, not a supplied-history assumption. -/

namespace GraphQL.IncrementalDelivery.Tests.Existence
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.WorkScheduler

/-- Arbitrary operations, environments, fuel, and source values have an observation.
Witness: the universal prefix-existence theorem, without a scheduler premise.
-/
example (schema : Schema) (resolvers : Resolvers ObjectRef) (variables : VariableValues)
    (operation : Operation) (fuel : Nat) (source : ResolverValue ObjectRef)
    : ∃ result,
        queryObservation schema resolvers variables operation fuel source result false :=
  queryObservation_exists schema resolvers variables operation fuel source

/-- A single proof-only factory conforms for all prepared query work, not just one
hard-coded fixture. Witness: generated initialization and the maximal source language.
-/
example (schema : Schema) (resolvers : Resolvers ObjectRef) (variables : VariableValues)
    (operation : Operation) (fuel : Nat) (source : ResolverValue ObjectRef)
    : initializedScheduler.Conforms
        ((executeRootSelectionSetCore schema resolvers variables fuel
            (operation.rootType schema) source operation.selectionSet).run
          0).1.work :=
  executeRoot_initializedScheduler_conforms schema resolvers variables fuel
    (operation.rootType schema) source operation.selectionSet

/-- An outer defer can be only an ancestor placeholder, with no actual contributing
task. Witness: the minimum actual node ignores absent dependency keys.
-/
def skippedAncestor : List Selection := [defer [defer [field "a"]]]

/-- Deferred producers, streamed items, and nested deferred children all remain in the
initialization domain. Witness: the same general theorem, without a stream-free premise.
-/
def nestedStream : List Selection :=
  [defer [field "users" [defer [field "name"]] [.stream (.boolean true) (some (.int 0))]]]

/-- Shared defer owners are allowed without selecting a wire owner or future trace. -/
def overlapping : List Selection := [defer [field "a"], defer [field "a"]]

/-- A failed deferred outcome does not make initialization vacuous. -/
def failed : List Selection := [defer [field "required"]]

#guard
  [skippedAncestor, nestedStream, overlapping, failed].all
    (fun selections =>
      ((executeRootSelectionSetCore schema resolvers [] 8 "Query" (.object "Query" 0)
          selections).run
        0).1.work.size
      != 0)

/-- The mixed/error fixtures have observations without supplying any history or source.
Witness: universal existence; the guard above separately checks their nonempty work.
-/
example (selections : List Selection)
    : ∃ result,
        queryObservation schema resolvers [] { selectionSet := selections } 8
          (.object "Query" 0) result false :=
  queryObservation_exists schema resolvers [] { selectionSet := selections } 8
    (.object "Query" 0)

/-- Exhausted fuel still has a counted-error observation. Witness: existence includes
ordinary error responses, rather than requiring a successful query domain.
-/
example
    : ∃ result,
        queryObservation schema resolvers []
          { selectionSet := nestedStream } 0 (.object "Query" 0) result false :=
  queryObservation_exists schema resolvers [] { selectionSet := nestedStream } 0
    (.object "Query" 0)

end GraphQL.IncrementalDelivery.Tests.Existence
