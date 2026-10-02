import Proofs.GraphQL.IncrementalDelivery.Correctness.QueryCoverage

/-! Public mixed-query coverage witnesses and typed container/leaf projection. -/

namespace GraphQL.IncrementalDelivery.Tests.QueryCoverage
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Correctness

/-- The exact public coverage proposition holds for every schema and raw operation. -/
example (schema : Schema) (operation : Operation)
    : deliveredResponsePositionsEquivalentToBasic schema operation :=
  deliveredResponsePositionsEquivalentToBasic_holds schema operation

/-- Leaf-once has no extra domain premise beyond the public complete-success boundary. -/
example (schema : Schema) (operation : Operation)
    : basicLeavesDeliveredExactlyOnce schema operation :=
  basicLeavesDeliveredExactlyOnce_holds schema operation

/-- Empty containers are retained in container mode but contribute no scalar/null leaves. -/
example
    : (TypedResponse.value [] (.object [("empty", .list [])])).filterMap
        (TypedResponse.entryPath false)
      = [] :=
  rfl

/-- Equal scalar values at different list indices remain distinct typed positions. -/
example
    : (TypedResponse.items [] 2 [.scalar "same", .scalar "same"]).filterMap
        (TypedResponse.entryPath false)
      = [[.index 2], [.index 3]] :=
  rfl

end GraphQL.IncrementalDelivery.Tests.QueryCoverage
