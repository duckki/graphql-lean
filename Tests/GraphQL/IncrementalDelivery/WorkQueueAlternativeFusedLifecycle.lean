import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationTermination

/-! Unconditional actual-handler flag preservation and aligned initialized replay flags.
Explicit abrupt stopping remains distinct from semantic work termination.
-/

namespace AlternativeFusedLifecycleChecks
open GraphQL.IncrementalDelivery.AlternativeWorkQueue

#print axioms State.removeGroup_walk_terminated
#print axioms State.removeGroup_terminated
#print axioms State.drainReadyGroups_go_terminated
#print axioms State.drainReadyGroups_terminated
#print axioms State.taskFailure_terminated
#print axioms State.taskSuccess_terminated
#print axioms State.streamItems_terminated
#print axioms State.handleGraphEvent_terminated
#print axioms State.handleGraphEvents_flagsAligned
#print axioms State.runNormalized_flagsAligned

end AlternativeFusedLifecycleChecks
