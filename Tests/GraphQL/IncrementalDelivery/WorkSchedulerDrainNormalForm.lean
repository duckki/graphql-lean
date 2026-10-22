import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.DrainNormalForm

/-! Ready release chains exhaust the live-node budget without charging stale roots. -/

namespace GraphQL.IncrementalDelivery.Tests.WorkSchedulerDrainNormalForm
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.ReferenceWorkQueue

private def parent : DeliveryNode := { ref := 2, path := [] }
private def child : DeliveryNode := { ref := 3, path := [] }

private def failedTask : Task := { occurrence := .executionGroup [], groups := [child] }

private def readyWork : Execution.Work :=
  .executionGroup [⟨child, [parent]⟩] [] { result := .error 3 } .empty

private def readyChain : State :=
  {
    rootGroups := [99, parent.ref]
    groupNodes :=
      [
        { group := { node := parent }, childGroups := [child.ref] },
        {
          group := { node := child, parent := some parent.ref },
          tasks := [failedTask.occurrence],
          pending := 1
        }
      ]
    tasks := [failedTask]
    taskNodes := [{ task := failedTask, rejection := some 3 }]
  }

/-- Two live nodes suffice to drain a success followed by its newly active failed child.
Witness: executable evaluation with a stale leading root entry, which spends no budget.
The stale ref remains but has no live lookup; no root-presence invariant is claimed here.
-/
theorem ready_chain_drain_output
    : readyChain.drainReadyGroups.2
        = [.groupSuccess parent [child] [], .groupFailure child 3]
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
          → readyChain.drainReadyGroups.1.rejectedTask? node = none
            ∧ node.pending ≠ 0 := by
  have sound : readyChain.GroupMembershipSound := by
    simp [State.GroupMembershipSound, readyChain, failedTask, parent, child]
  have registered : readyChain.StartedTasksRegistered := by
    simp [State.StartedTasksRegistered, readyChain]
  have matching : readyChain.RegisteredTasksMatch readyWork := by
    intro task member
    have same : task = failedTask := by simpa only [readyChain, List.mem_singleton] using member
    subst task
    exact ⟨⟨[], .object [] (.error 3), none, rfl, .executionGroup .root⟩, rfl⟩
  exact readyChain.drainReadyGroups_normalForm sound registered matching

end GraphQL.IncrementalDelivery.Tests.WorkSchedulerDrainNormalForm
