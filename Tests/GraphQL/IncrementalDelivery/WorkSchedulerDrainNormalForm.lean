import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.DrainNormalForm
import Tests.GraphQL.IncrementalDelivery.Fixtures.DrainNormalForm

/-! Ready release chains exhaust the live-node budget without charging stale roots. -/

namespace GraphQL.IncrementalDelivery.Tests.WorkSchedulerDrainNormalForm
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Tests.Fixtures.DrainNormalForm

/-- Successful draining releases a child whose cached failure becomes a separate notice.
Witness: executable evaluation with a stale leading root, which spends no budget. Startup
removes the failed child immediately; the caller must forward its queued notification.
-/
theorem ready_chain_drain_output
    : readyChain.drainReadyGroups.2.1 = [.groupSuccess parent [child] []]
      ∧ readyChain.drainReadyGroups.2.2 = [⟨child, 3⟩]
      ∧ readyChain.drainReadyGroups.1.groupNodes = []
      ∧ readyChain.drainReadyGroups.1.rootGroups = [99] := by cbv

/-- The finite drain normal-form theorem covers the same stale-root success/failure chain.
Witness: apply the generic budget theorem, rather than assume that released children are
unsettled or that root entries all have live nodes.
-/
theorem ready_chain_normal_form
    : ∀ ref ∈ readyChain.drainReadyGroups.1.rootGroups,
        ∀ node,
          readyChain.drainReadyGroups.1.groupNode? ref = some node
          → node.pending ≠ 0 := by
  have sound : readyChain.GroupMembershipSound := by
    simp [State.GroupMembershipSound, readyChain, failedTask, parent, child]
  have registered : readyChain.StartedTasksRegistered := by
    simp [State.StartedTasksRegistered, readyChain]
  have matching : readyChain.RegisteredTasksMatch readyWork := by
    intro task member
    have same : task = failedTask := by simpa only [readyChain, List.mem_singleton] using member
    subst task
    exact ⟨⟨[], .object [] (.error 3), none, rfl,  .executionGroup (WorkQueueSemantics.Located.root (root := readyWork))⟩, rfl⟩
  exact readyChain.drainReadyGroups_normalForm sound registered matching

/-- A cached rejection on an active pending group awaits its FIFO notification.
Witness: draining alone preserves the intermediate state; batch dispatch consumes the
failure notification and emits the failed completion before queue termination.
-/
theorem active_cached_rejection_waits_for_notification
    : activeCached.drainReadyGroups = (activeCached, [], [])
      ∧ (activeCached.handleGraphEvents [.taskFailure failedTask.occurrence 3]).2
        = [.groupFailure child 3, .workQueueTermination] := by cbv

end GraphQL.IncrementalDelivery.Tests.WorkSchedulerDrainNormalForm
