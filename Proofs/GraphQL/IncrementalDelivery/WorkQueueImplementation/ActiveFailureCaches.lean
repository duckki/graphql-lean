import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.DrainNormalForm

/-! A completed sound drain leaves no replayable rejection on an active live group. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Every active live group has no retained member rejection to replay. -/
def State.NoActiveCachedFailure (queue : State) : Prop :=
  ∀ node ∈ queue.groupNodes,
    node.group.node.ref ∈ queue.rootGroups → queue.rejectedTask? node = none

/-- A completed drain leaves active groups waiting without a retained member rejection.
Witness: unique final refs identify each live record's lookup, and sound registered task
ownership makes every rejected iteration remove a live node within the supplied budget.
-/
theorem State.drainReadyGroups_noActiveCachedFailure (queue : State)
    {work : Execution.Work} (sound : queue.GroupMembershipSound)
    (registered : queue.StartedTasksRegistered)
    (matching : queue.RegisteredTasksMatch work)
    (unique : queue.drainReadyGroups.1.GroupRefsUnique)
    : queue.drainReadyGroups.1.NoActiveCachedFailure := by
  intro node member active
  have found := unique.groupNode?_of_mem member
  exact (queue.drainReadyGroups_normalForm sound registered matching _ active _ found).1

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
