import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.DrainPublicationLedger
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.UncancelledRetirementClosure

/-! Buffered ancestor data precedes a child's value block within the same ready drain. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Interpret one common publication ledger at every internal drain boundary
-----------------------------------------------------------------------------------------

/-- Cancellation refs at a bounded drain prefix remain recorded at the full endpoint.
Witness: split the actual drain at `steps`, then use suffix cancellation monotonicity.
-/
theorem State.drainReadyGroups_go_prefix_cancelledSubset (queue : State)
    {steps fuel : Nat} (bounded : steps ≤ fuel)
    : (State.drainReadyGroups.go steps queue).1.cancelledGroups.Subset
        (State.drainReadyGroups.go fuel queue).1.cancelledGroups := by
  have split := State.drainReadyGroups_go_add steps (fuel - steps) queue
  rw [Nat.add_sub_of_le bounded] at split
  rw [split]
  exact State.drainReadyGroups_go_cancelledGroups_subset _ _

/-- An uncancelled ancestor's buffered contribution precedes the child's value block.
Witness: the exact pre-flush drain boundary has retired every task-bearing ancestor.
Prefix owner conservation on the supplied ledger then rules out retention there. The
child may have become active during this same drain; prior activation is not assumed.
-/
theorem State.drainReadyGroups_go_ancestorValue_before {queue original : State}
    {work parents} {published : List ObjectPublication} {fuel : Nat}
    (generated : ExecutedWork work) (matching : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ group dependencies,
          GroupRecordAt work group dependencies → dependencies = parents group.ref)
    (live : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (roots : queue.RootAncestorsRetired work)
    (closed : queue.UncancelledRetiredAncestors work)
    (prefixes
      : ∀ steps,
          steps ≤ fuel
          → original.StoredOwnersConserved
              (published.take
                ((State.drainReadyGroups.go steps queue).2.flatMap
                  WorkQueueEvent.objectValues).length)
              (State.drainReadyGroups.go steps queue).1)
    {index group values dependencies ref occurrence node value}
    (selected
      : (State.drainReadyGroups.go fuel queue).2[index]?
        = some (.groupValues group values))
    (record : GroupRecordAt work group dependencies) (ancestor : ref ∈ dependencies)
    (found : original.taskNode? occurrence = some node) (stored : node.value = some value)
    (known
      : TaskHasOwners work occurrence (node.task.groups.map Execution.DeliveryNode.ref))
    (contributes : ref ∈ node.task.groups.map Execution.DeliveryNode.ref)
    (present : ref ∈ original.groupNodes.map (fun owner => owner.group.node.ref))
    (uncancelled : ref ∉ (State.drainReadyGroups.go fuel queue).1.cancelledGroups)
    : (occurrence, value)
      ∈ published.take
          (((State.drainReadyGroups.go fuel queue).2.take index).flatMap
            WorkQueueEvent.objectValues).length := by
  obtain ⟨steps, current, bounded, _, active, _, _, same, exactPrefix⟩ :=
    State.drainReadyGroups_go_value_boundary fuel queue selected
  have prefixRoots := (State.drainReadyGroups_go_uncancelledRetirement closed generated
    matching links canonical live tasks roots steps).1
  have retired := prefixRoots current.group.node.ref active group dependencies record
    (congrArg Execution.DeliveryNode.ref same.symm) ref ancestor occurrence _ known contributes
  have notCancelled : ref ∉ (State.drainReadyGroups.go steps queue).1.cancelledGroups :=
    fun member => uncancelled
      (State.drainReadyGroups_go_prefix_cancelledSubset queue (Nat.le_of_lt bounded) member)
  have emitted := (prefixes steps (Nat.le_of_lt bounded)
    occurrence node value found stored ref contributes present notCancelled).resolve_right
      (fun retained => retired.2 retained.2)
  simpa only [exactPrefix] using emitted

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
