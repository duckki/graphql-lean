import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationNormalizedReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.Conformance

/-! Checked reductions from the unchanged generated replay target to factory conformance.

These are conditional proof reductions, not closed replay or conformance witnesses.
RegistrationNormalizedReplay supplies the generated replay witness used by these reductions.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue

-----------------------------------------------------------------------------------------
-- Public roots retain their original source and generated-work domains
-----------------------------------------------------------------------------------------

/-- Checked conformance reduction reuses the complete reference witness and exact premises.
Witness: factory equality transports all four independent WorkQueue contract clauses.
-/
theorem createWorkQueueForScheduleConforms_of_factory
    (factory : createWorkQueueForScheduleMatchesReference)
    : createWorkQueueForScheduleConforms := by
  intro work schedule generated nonempty valid
  rw [factory work schedule generated nonempty valid]
  exact ReferenceWorkQueue.createWorkQueueForScheduleConforms_holds
    work schedule generated nonempty valid

/-- The only semantic leaf needed by these factory/conformance reductions is public replay.
This is a checked dependency edge, not an assertion that the replay leaf is proved.
-/
theorem createWorkQueueForScheduleConforms_of_replay (replay : replayMatchesReference)
    : createWorkQueueForScheduleConforms :=
  createWorkQueueForScheduleConforms_of_factory
    (createWorkQueueForScheduleMatchesReference_of_replay replay)

end GraphQL.IncrementalDelivery.AlternativeWorkQueue
