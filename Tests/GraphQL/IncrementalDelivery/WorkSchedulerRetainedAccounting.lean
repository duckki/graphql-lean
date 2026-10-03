import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ActiveLinks
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RegistrationHistory

/-! Focused proof regressions for retained-failure counters and release-time draining.
These internal-state fixtures exercise the rebuilt bookkeeping witnesses independently
of the implementation proof umbrella still awaiting migration.
-/

namespace GraphQL.IncrementalDelivery.Tests.WorkSchedulerRetainedAccounting
open GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

private def root : Execution.DeliveryNode := { ref := 0, path := [] }
private def parent : Execution.DeliveryNode := { ref := 1, path := [] }
private def child : Execution.DeliveryNode := { ref := 2, path := [] }
private def shared : Occurrence := .executionGroup [0]
private def remaining : Occurrence := .executionGroup [1]
private def parentTask : Occurrence := .executionGroup [2]

private def sharedNode : TaskNode := { task := ⟨shared, [root, child]⟩ }
private def parentNode : TaskNode := { task := ⟨parentTask, [parent]⟩ }

/-- One active and one latent owner share the failed task; the latent owner also
has another unsettled task. This is an internal bookkeeping fixture, not a query theorem.
-/
private def beforeFailure : State :=
  {
    rootGroups := [root.ref, parent.ref]
    registeredGroups := [root.ref, parent.ref, child.ref]
    groupNodes :=
      [
        { group := ⟨root, none⟩, tasks := [shared], pending := 1 },
        {
          group := ⟨parent, none⟩,
          childGroups := [child.ref],
          tasks := [parentTask],
          pending := 1
        },
        { group := ⟨child, some parent.ref⟩, tasks := [shared, remaining], pending := 2 }
      ]
    taskNodes := [sharedNode, parentNode]
    tasks := [sharedNode.task, parentNode.task, ⟨remaining, [child]⟩]
  }

/-- The failure witness handles mixed active/latent contributors without assuming
they are all removed. Witness: concrete ownership, uniqueness, and freshness premises.
-/
theorem shared_failure_pending
    : (beforeFailure.taskFailure shared 2).1.PendingTracks [shared] := by
  have tracks : beforeFailure.PendingTracks [] := by
    simp [State.PendingTracks, GroupNode.PendingTracks, unsettledCount, beforeFailure]
  have refs : beforeFailure.GroupRefsUnique := by
    unfold State.GroupRefsUnique
    decide
  have memberships : beforeFailure.TaskMembershipsUnique := by
    simp [State.TaskMembershipsUnique, beforeFailure, shared, remaining]
  apply tracks.taskFailure refs memberships shared 2 sharedNode rfl (by decide) (by simp)
  · decide
  · simp [State.OwnedExactlyBy, beforeFailure, sharedNode, shared,
      remaining, parentTask, root, parent, child]

/-- The active owner closes, while the latent owner's count decreases once and its
remaining task survives. Witness: direct reduction of the same public handler.
-/
theorem shared_failure_retains_remaining
    : let after := (beforeFailure.taskFailure shared 2).1
      after.groupNode? root.ref = none
      ∧ (after.groupNode? child.ref).map GroupNode.pending = some 1
      ∧ (after.groupNode? child.ref).map GroupNode.tasks = some [remaining]
      ∧ (after.groupNode? child.ref).map GroupNode.failure = some (some 2) := by
  cbv

/-- Failure preserves registration, sound membership, active links, and the other
task's latent link. Witness: the rebuilt handler theorems on a nonempty survivor state.
-/
theorem shared_failure_links
    : let after := (beforeFailure.taskFailure shared 2).1
      after.StartedTasksRegistered
      ∧ after.GroupMembershipSound
      ∧ after.ActiveTaskLinks
      ∧ after.TaskLinkedOn remaining [child.ref] := by
  have registered : beforeFailure.StartedTasksRegistered := by
    simp [State.StartedTasksRegistered, beforeFailure]
  have sound : beforeFailure.GroupMembershipSound := by
    simp [State.GroupMembershipSound, beforeFailure, sharedNode, parentNode,
      shared, remaining, parentTask, root, parent, child]
  have active : beforeFailure.ActiveTaskLinks := by
    simp [State.ActiveTaskLinks, State.RootTaskLinkedOn, beforeFailure,
      sharedNode, parentNode, shared, remaining, parentTask, root, parent, child]
  have latent : beforeFailure.TaskLinkedOn remaining [child.ref] := by
    simp [State.TaskLinkedOn, beforeFailure, root, parent, child]
  exact ⟨
    registered.taskFailure shared 2,
    sound.taskFailure shared 2,
    active.taskFailure shared 2,
    latent.taskFailure shared 2 (by decide)
  ⟩

/-- A genuinely surviving started node is distinct from the failed occurrence.
Witness: the generic survivor theorem instantiated at the still-active parent task.
-/
theorem shared_failure_survivor
    : parentNode ∈ beforeFailure.taskNodes ∧ parentNode.task.occurrence ≠ shared := by
  apply beforeFailure.taskFailure_startedSurvivor shared 2
  cbv
  exact List.mem_singleton_self _

/-- A successful ready parent releases a child whose failure has already settled.
The removed root remains in the permanent registry, allowing a no-reactivation check.
-/
private def beforeDrain : State :=
  {
    rootGroups := [parent.ref]
    registeredGroups := [root.ref, parent.ref, child.ref]
    groupNodes :=
      [
        { group := ⟨parent, none⟩, childGroups := [child.ref] },
        { group := ⟨child, some parent.ref⟩, failure := some 2 }
      ]
  }

/-- Both recursive drain branches preserve pending counts, membership uniqueness,
registered-task provenance, and retirement. Witness: the generic drain induction's
four independently instantiated preservation theorems.
-/
theorem drain_invariants
    : beforeDrain.drainReadyGroups.1.PendingTracks []
      ∧ beforeDrain.drainReadyGroups.1.TaskMembershipsUnique
      ∧ beforeDrain.drainReadyGroups.1.RegisteredTasksMatch .empty
      ∧ beforeDrain.drainReadyGroups.1.RetiredGroup root.ref := by
  have tracks : beforeDrain.PendingTracks [] := by
    simp [State.PendingTracks, GroupNode.PendingTracks, unsettledCount, beforeDrain]
  have memberships : beforeDrain.TaskMembershipsUnique := by
    simp [State.TaskMembershipsUnique, beforeDrain]
  have matching : beforeDrain.RegisteredTasksMatch .empty := by
    simp [State.RegisteredTasksMatch, beforeDrain]
  have retired : beforeDrain.RetiredGroup root.ref := by
    unfold State.RetiredGroup
    decide
  exact ⟨tracks.drainReadyGroups, memberships.drainReadyGroups,
    matching.drainReadyGroups, retired.drainReadyGroups⟩

/-- The drain actually crosses a successful parent closure and a retained child
failure, not merely a no-op branch. Witness: exact public transition reduction.
-/
theorem drain_releases_then_fails
    : beforeDrain.drainReadyGroups.1.groupNodes = []
      ∧ beforeDrain.drainReadyGroups.2
        = [.groupSuccess parent [child] [], .groupFailure child 2] := by
  cbv

end GraphQL.IncrementalDelivery.Tests.WorkSchedulerRetainedAccounting
