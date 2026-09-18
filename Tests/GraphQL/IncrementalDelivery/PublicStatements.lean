import Proofs.GraphQL.IncrementalDelivery.Correctness

/-! Every public query-correctness proposition has a witness at its exact public type. -/

namespace GraphQL.IncrementalDelivery.Tests.PublicStatements
open GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution

/-- Public finite progress needs no shape, scheduler, history, or success premise.
-/
example (schema : Schema) (operation : Operation) : queryOutcomeExists schema operation :=
  queryOutcomeExists_holds schema operation

/-- Directive-free equivalence needs no premises beyond its public statement. -/
example (schema : Schema) (operation : Operation)
    : incrementalDirectiveFreeExecutionEquivalentToBasic schema operation :=
  incrementalDirectiveFreeExecutionEquivalentToBasic_holds schema operation

/-- The public mergedExecutionEquivalentToBasic statement needs no additional premises. -/
example (schema : Schema) (operation : Operation)
    : mergedExecutionEquivalentToBasic schema operation :=
  mergedExecutionEquivalentToBasic_holds schema operation

/-- The public deliveryIDsEventuallyComplete statement needs no additional premises. -/
example (schema : Schema) (operation : Operation)
    : deliveryIDsEventuallyComplete schema operation :=
  deliveryIDsEventuallyComplete_holds schema operation

/-- The public deliveryIDsUnique statement needs no additional premises. -/
example (schema : Schema) (operation : Operation) : deliveryIDsUnique schema operation :=
  deliveryIDsUnique_holds schema operation

/-- The public deliveryPatchesAnnounced statement needs no additional premises. -/
example (schema : Schema) (operation : Operation)
    : deliveryPatchesAnnounced schema operation :=
  deliveryPatchesAnnounced_holds schema operation

/-- The public deliveryIDUsageValid statement needs no additional premises. -/
example (schema : Schema) (operation : Operation)
    : deliveryIDUsageValid schema operation :=
  deliveryIDUsageValid_holds schema operation

/-- The public deliveryIDsCompleteExactlyOnce statement needs no additional premises. -/
example (schema : Schema) (operation : Operation)
    : deliveryIDsCompleteExactlyOnce schema operation :=
  deliveryIDsCompleteExactlyOnce_holds schema operation

/-- The public deliveryLifecycleValid statement needs no additional premises. -/
example (schema : Schema) (operation : Operation)
    : deliveryLifecycleValid schema operation :=
  deliveryLifecycleValid_holds schema operation

/-- The public deliverySlicesDisjoint statement needs no additional premises. -/
example (schema : Schema) (operation : Operation)
    : deliverySlicesDisjoint schema operation :=
  deliverySlicesDisjoint_holds schema operation

/-- Full position coverage needs no premises beyond its public statement. -/
example (schema : Schema) (operation : Operation)
    : deliveredResponsePositionsEquivalentToBasic schema operation :=
  deliveredResponsePositionsEquivalentToBasic_holds schema operation

/-- The public basicLeavesDeliveredExactlyOnce statement needs no additional premises. -/
example (schema : Schema) (operation : Operation)
    : basicLeavesDeliveredExactlyOnce schema operation :=
  basicLeavesDeliveredExactlyOnce_holds schema operation

section SuccessfulOutcomes

variable {ObjectRef : Type} {schema : Schema} {resolvers : Resolvers ObjectRef}
  {variables : VariableValues} {operation : Operation} {fuel : Nat}
  {source : ResolverValue ObjectRef} {result : QueryResult}
  (observed : queryOutcome schema resolvers variables operation fuel source result)
  (zero : result.totalErrors = 0)

/-- Raw execution completeness follows from a complete outcome and zero errors. -/
example : result.executionComplete :=
  (queryOutcome_executionComplete_iff observed).mpr zero

/-- Reconstruction requires no separately supplied lifecycle/completeness certificate. -/
example
    : ∃ response,
        mergeQueryResult result = some response
        ∧ GraphQL.Execution.Response.semanticEquivalent response
            (GraphQL.Execution.executeQueryWithFuel schema resolvers variables
              operation.eraseIncrementalDirectives fuel source) :=
  mergedExecutionEquivalentToBasic_holds schema operation
    resolvers variables fuel source result observed zero

/-- Position coverage uses only the complete observation and its zero error count. -/
example (containers : Bool)
    : ∃ slices,
        result.DeliversSlices containers slices
        ∧ slices.flatten.Perm
            (ResponsePositions.value containers []
              (GraphQL.Execution.executeQueryWithFuel schema resolvers variables
                operation.eraseIncrementalDirectives fuel source).data) :=
  deliveredResponsePositionsEquivalentToBasic_holds schema operation
    resolvers variables fuel source result observed zero containers

/-- Exactly-once leaves uses the same simplified public premises. -/
example
    : ∃ slices,
        result.DeliversSlices false slices
        ∧ ∀ path ∈
            ResponsePositions.value false []
              (GraphQL.Execution.executeQueryWithFuel schema resolvers variables
                operation.eraseIncrementalDirectives fuel source).data,
            slices.flatten.count path = 1 :=
  basicLeavesDeliveredExactlyOnce_holds schema operation
    resolvers variables fuel source result observed zero

end SuccessfulOutcomes

end GraphQL.IncrementalDelivery.Tests.PublicStatements
