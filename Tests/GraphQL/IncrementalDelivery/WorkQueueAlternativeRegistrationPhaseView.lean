import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationSnapshotProjection

/-! Registration views are proof-only phase notation. Their accounting/record projection
is derived on the original source domain, not used as an executable cleanup observer.
-/

namespace AlternativeRegistrationPhaseViewChecks
open GraphQL.IncrementalDelivery
open AlternativeWorkQueue
open NativeRefinement

example {work inputs event}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (valid : ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ [event]))
    (started : ReferenceWorkQueue.inputsStarted work inputs = true)
    : SnapshotProjection ((State.initialize work).runNormalized inputs).1.queue event :=
  generatedSnapshot_projection generated valid started

#print axioms referencePrefix_snapshotProjection
#print axioms generatedSnapshot_projection

end AlternativeRegistrationPhaseViewChecks
