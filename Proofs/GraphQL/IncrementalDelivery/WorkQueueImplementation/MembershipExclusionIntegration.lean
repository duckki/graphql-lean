import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskMembershipIntegration
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PublishedMemberships
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PublicationReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskProducerOrder

/-! Fresh source child work cannot reinstall a previously published group membership. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Group metadata and fresh task integration preserve publication exclusions
-----------------------------------------------------------------------------------------

/-- A matched fresh input cannot offer a child whose value was already published.
Witness: child source order excludes earlier settlement of that occurrence; every entry
of the exact object inventory has an earlier source-success witness. This derives the
integration exclusion from existing source semantics, not an added freshness law.
-/
theorem GraphEvent.MatchesWork.childTask_not_published
    {work before event} {queue : State} {published : List ObjectPublication} {task : Task}
    (matching : GraphEvent.MatchesWork work event) (valid : ValidGraphEvents work before)
    (fresh : event.Fresh before)
    (inventory : queue.PublicationInventory (ObjectValueFrom before) published)
    (member : task ∈ event.childTasks)
    : task.occurrence ∉ published.map Prod.fst := by
  intro emitted
  obtain ⟨publication, listed, same⟩ := List.mem_map.mp emitted
  exact matching.childTasks_unsettled valid fresh member
    (same ▸ (inventory.provenance publication listed).identity)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
