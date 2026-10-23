import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskEligibility
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CachedFailures
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.HealthyContributors
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RecordCancellation

/-! Causal health excludes retained rejections on a healthy contributor.
These are semantic proof facts, not executable settlement guards.
-/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- A task's supported rejection invalidates each of its contributing owners. -/
theorem State.CachedFailuresSupported.rejectedTask_ownersInvalidated
    {queue : State} {work failed node}
    (supported : queue.CachedFailuresSupported work failed)
    (member : node ∈ queue.taskNodes) (rejected : node.rejection.isSome = true)
    : ∀ ref ∈ node.task.groups.map Execution.DeliveryNode.ref,
        GroupInvalidated work failed ref := by
  intro ref included
  obtain ⟨group, contributes, rfl⟩ := List.mem_map.mp included
  exact supported.invalidated member rejected contributes

/-- A rejected task cannot occur in a still-healthy group's sound membership list. -/
theorem State.GroupMembershipSound.rejectedTask_absentFromHealthy {queue : State}
    {work failed} (sound : queue.GroupMembershipSound)
    (registered : queue.StartedTasksRegistered)
    (matching : queue.RegisteredTasksMatch work)
    (supported : queue.CachedFailuresSupported work failed)
    {taskNode : TaskNode} (taskMember : taskNode ∈ queue.taskNodes)
    (rejected : taskNode.rejection.isSome = true) {node : GroupNode}
    (member : node ∈ queue.groupNodes)
    (healthy : ¬GroupInvalidated work failed node.group.node.ref)
    : taskNode.task.occurrence ∉ node.tasks := by
  intro listed
  exact healthy (supported.rejectedTask_ownersInvalidated taskMember rejected _
    (sound.startedOwner registered matching taskMember member listed))

/-- A healthy group has no retained task rejection for release-time replay. -/
theorem State.CachedFailuresSupported.healthy_rejectedTask_none {queue : State}
    {work failed group} (supported : queue.CachedFailuresSupported work failed)
    (sound : queue.GroupMembershipSound) (registered : queue.StartedTasksRegistered)
    (matching : queue.RegisteredTasksMatch work) (member : group ∈ queue.groupNodes)
    (healthy : ¬GroupInvalidated work failed group.group.node.ref)
    : queue.rejectedTask? group = none := by
  apply State.rejectedTask?_eq_none_iff.mpr
  intro occurrence listed node found
  have same : node.task.occurrence = occurrence :=
    (occurrence_beq_iff_eq _ _).mp
      (List.find?_some (p := fun candidate : TaskNode => candidate.task.occurrence == occurrence)
        found)
  by_cases rejected : node.rejection = none
  · exact rejected
  · have present : node.rejection.isSome = true := by
      cases value : node.rejection with
      | none => exact (rejected value).elim
      | some errors => rfl
    exact False.elim (sound.rejectedTask_absentFromHealthy registered matching supported
      (List.mem_of_find?_eq_some found) present member healthy (same.symm ▸ listed))

/-- An unpublished rejected computation is causally cancelled through its owners. -/
theorem State.CachedFailuresSupported.rejectedTask_cancelled {queue : State}
    {work failed published node}
    (supported : queue.CachedFailuresSupported work failed)
    (member : node ∈ queue.taskNodes) (rejected : node.rejection.isSome = true)
    (known
      : TaskHasOwners work node.task.occurrence
          (node.task.groups.map Execution.DeliveryNode.ref))
    (nonempty : node.task.groups ≠ []) (unpublished : ¬published node.task.occurrence)
    : Causality.TaskCancelled work failed published node.task.occurrence := by
  refine .owners known unpublished (by simpa using nonempty) ?_
  intro ref included
  exact (supported.rejectedTask_ownersInvalidated member rejected ref
          included).toCausality
    published

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
