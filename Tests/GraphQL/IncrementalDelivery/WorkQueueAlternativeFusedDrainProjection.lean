import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedDrainProjection

/-! Exact local and independently constructed generated-prefix mixed-drain targets. -/

namespace AlternativeFusedDrainProjectionChecks
open GraphQL.IncrementalDelivery.AlternativeWorkQueue

example : FusedDrainProjection := FusedDrainProjection_holds
example : GeneratedReferenceDrainProjection := GeneratedReferenceDrainProjection_holds

#print axioms State.removeGroup_walk_stopped
#print axioms State.removeGroup_stopped
#print axioms State.drainReadyGroups_go_stopped
#print axioms State.drainReadyGroups_stopped
#print axioms State.drainReadyGroups_go_projection
#print axioms FusedDrainProjection_holds
#print axioms GeneratedReferenceDrainProjection_holds

end AlternativeFusedDrainProjectionChecks
