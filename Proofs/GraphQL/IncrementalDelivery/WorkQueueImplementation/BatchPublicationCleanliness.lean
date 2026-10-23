import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureRetentionReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PublicationReplay

/-! Valid fixed outcomes keep successful object values outside available rejection caches. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- A source-witnessed object value cannot also have an available task rejection.
Witness: both outcomes refer to the same fixed task; source validity excludes a failure
for a successful task even when its notification occurs later in the supplied batch.
-/
theorem ValidGraphEvents.objectValue_not_availableFailure
    {work events batch occurrence value} (valid : ValidGraphEvents work events)
    (included : batch.Subset events) (source : ObjectValueFrom events occurrence value)
    (errors : Nat)
    : (occurrence, errors) ∉ GraphEvent.availableFailures batch := by
  obtain ⟨result, success, _⟩ := source
  have succeeds : TaskSucceeds work occurrence :=
    valid.groupSettlements_succeed (List.mem_reverse.mpr
    (List.mem_flatMap.mpr ⟨.taskSuccess occurrence result, success, by
      simp [GraphEvent.groupSuccesses]⟩))
  intro available
  obtain ⟨event, member, failed⟩ := List.mem_filterMap.mp available
  have failure : occurrence ∈ event.groupFailures := by
    cases event <;> simp_all [GraphEvent.groupFailures]
  exact valid.succeeds_not_failureSettlements succeeds (List.mem_reverse.mpr
    (List.mem_flatMap.mpr ⟨event, included member, failure⟩))

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
