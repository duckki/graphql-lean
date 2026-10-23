import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupNoticeTaskProvenance
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NoticeTaskProducers

/-! Concrete retained notice contents on the same matching and consumed source. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- A noticed descriptor retains concrete unpublished tasks.
The queue record and contents facts share one emitting boundary. `failed` is the
proof inventory; `received` supplies successful registration prerequisites.
The prerequisites concern source success, not already-published producer values. This package
is derived evidence, not a source assumption or scheduler-contract premise.
-/
def RetainedNoticeContents (work : Execution.Work) (matching : PublicationMatching)
    (events : List Execution.WorkQueueEvent) (_failed : List Occurrence)
    (received : List GraphEvent) (child : Execution.DeliveryNode)
    : Prop :=
  (∃ dependencies producer, NodeAt work child .group dependencies producer)
  ∧ ∃ queue : State,
    ∃ node : GroupNode,
      queue.groupNode? child.ref = some node
      ∧ node.group.node = child
      ∧ node.tasks ≠ []
      ∧ queue.GroupMembershipSound
      ∧ queue.RegisteredTasksMatch work
      ∧ TaskProducersSucceeded work queue.tasks received
      ∧ ∀ occurrence ∈ node.tasks, ¬Published matching events occurrence

/-- Concrete retained contents supply a real unpublished contributor.
Witness: pruning retained a nonempty task list, whose sound membership and registered
descriptor give the original work occurrence. Producer readiness still decides cancellation safety.
-/
theorem RetainedNoticeContents.recorded_or_unpublished
    {work matching events failures cut received child}
    (contents
      : RetainedNoticeContents work matching events (failedBefore failures cut) received
          child)
    : HasRecordedFailure work failures cut child.ref
      ∨ ∃ occurrence owners,
          TaskHasOwners work occurrence owners
          ∧ child.ref ∈ owners
          ∧ ¬Published matching events occurrence := by
  obtain ⟨_, queue, node, found, same, retained, sound, registered,
    _, unpublished⟩ := contents
  have member := List.mem_of_find?_eq_some found
  obtain ⟨occurrence, listed⟩ := List.exists_mem_of_ne_nil _ retained
  obtain ⟨task, taskMember, sameTask, owner⟩ := sound node member occurrence listed
  obtain ⟨_, payload, producer, _, known⟩ := (registered task taskMember).1
  rw [sameTask] at known
  exact .inr ⟨occurrence, _, ⟨producer, payload, known⟩, same ▸ owner,
    unpublished occurrence listed⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
