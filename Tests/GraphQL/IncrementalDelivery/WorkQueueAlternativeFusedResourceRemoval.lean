import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedResourceRemoval

/-! The actual endpoint and resource witness belong to the same removal reduction. -/

namespace AlternativeFusedResourceRemovalChecks
open GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement

example : FusedRemovalResourceSafety := FusedRemovalResourceSafety_holds

#print axioms FusedRemovalResourceSafety_holds
#print axioms ResourceState.observeFusedRemoval_foreign

end AlternativeFusedResourceRemovalChecks
