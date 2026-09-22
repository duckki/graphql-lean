import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.DrainNormalForm

/-! Ready release chains exhaust the live-node budget without charging stale roots. -/

namespace GraphQL.IncrementalDelivery.Tests.WorkSchedulerDrainNormalForm
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.ReferenceWorkQueue

private def parent : DeliveryNode := { key := 2, path := [] }
private def child : DeliveryNode := { key := 3, path := [] }

private def readyChain : State :=
  {
    rootGroups := [99, parent.key]
    groupNodes :=
      [
        { group := { node := parent }, childGroups := [child.key] },
        { group := { node := child, parent := some parent.key }, failure := some 3 }
      ]
  }

/-- Two live nodes suffice to drain a success followed by its newly active failed child.
Witness: executable evaluation with a stale leading root entry, which spends no budget.
The stale key remains but has no live lookup; no root-presence invariant is claimed here.
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
    : ∀ key ∈ readyChain.drainReadyGroups.1.rootGroups,
        ∀ node,
          readyChain.drainReadyGroups.1.groupNode? key = some node
          → node.failure = none ∧ node.pending ≠ 0 :=
  readyChain.drainReadyGroups_normalForm

end GraphQL.IncrementalDelivery.Tests.WorkSchedulerDrainNormalForm
