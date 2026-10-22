import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StoredValueRetention
import Tests.GraphQL.IncrementalDelivery.Fixtures.StoredValueStartup

/-! Startup removal retains buffered records exactly when a contributing owner survives. -/

namespace GraphQL.IncrementalDelivery.Tests.WorkSchedulerValueStartup
open GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Tests.Fixtures.StoredValueStartup

/-- Immediate failure removal can discard a buffered value with no surviving owner.
This rules out unconditional lookup retention even with an empty availability snapshot.
-/
theorem last_owner_removal_discards_buffer
    : lastOwner.taskNode? buffered.task.occurrence = some buffered
      ∧ (lastOwner.startNewWork startup).1.taskNode? buffered.task.occurrence = none
      ∧ (lastOwner.startNewWork startup).2 = [⟨failingGroup, 1⟩] := by cbv

/-- The generic survivor theorem retains the exact buffered record during failed startup. -/
theorem surviving_owner_retains_buffer
    : (queue.startNewWork startup).1.taskNode? buffered.task.occurrence
      = some buffered := by
  exact State.startNewWork_lookup_existing
    (by rfl)
    startup []
    (contributor := survivingGroup)
    (owner := survivor)
    (contributes := by simp [buffered])
    (live := by cbv; exact .head _)
    (same := rfl)

end GraphQL.IncrementalDelivery.Tests.WorkSchedulerValueStartup
