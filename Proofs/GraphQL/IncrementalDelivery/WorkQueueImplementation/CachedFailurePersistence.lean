import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CancelledGroupReporting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupPublication
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskEligibility

/-! Concrete retained rejection witnesses, without arbitrary-state persistence claims. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- A failed ref is cancelled or remains live with a replayable task rejection.
This proof predicate observes actual task records; it introduces no group failure cache.
-/
def State.FailureRetained (queue : State) (ref : NodeRef) : Prop :=
  ref ∈ queue.cancelledGroups
  ∨ ∃ node ∈ queue.groupNodes,
      node.group.node.ref = ref ∧ (queue.rejectedTask? node).isSome = true

/-- A concretely retained failure with no live record has a cancellation marker.
Witness: unique refs turn the live rejection alternative into the excluded lookup.
-/
theorem State.FailureRetained.cancelled_of_absent {queue : State} {ref}
    (retained : queue.FailureRetained ref) (unique : queue.GroupRefsUnique)
    (absent : queue.groupNode? ref = none)
    : ref ∈ queue.cancelledGroups := by
  rcases retained with cancelled | ⟨node, member, same, rejected⟩
  · exact cancelled
  · have found := unique.groupNode?_of_mem member
    rw [same, absent] at found
    contradiction

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
