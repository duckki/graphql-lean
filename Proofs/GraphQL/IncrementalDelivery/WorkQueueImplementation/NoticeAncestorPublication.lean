import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ReleaseAncestorCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.OwnerFoldBoundaries
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupFailureNotices
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CancellationMonotonicity

/-! Buffered ancestor data is published by the precise owner-fold notice boundary. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- A silent ancestor's retirement forces publication, not a fabricated completion
-----------------------------------------------------------------------------------------

/-- A notice's buffered ancestor data precedes its owner-fold carrier, even if pruned.
Witness: recover the exact processed-owner boundary. Its released child has retired
task-bearing ancestors, and conservation on that same ledger prefix excludes retaining
their buffered data. The ancestor need not emit a completion or be the carrier's owner.
-/
theorem State.ReleaseOwners.ownerCarrier_ancestorValue {queue : State}
    {work parents owners published} (prefixes : queue.ReleaseOwners owners published)
    (generated : ExecutedWork work) (records : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (live : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (roots : queue.RootAncestorsRetired work)
    {index group groups streams child dependencies ref occurrence node value}
    (selected
      : (owners.foldl successGroupStep (queue, [], {})).2.1[index]?
        = some (.groupSuccess group groups streams))
    (noticed : child ∈ groups) (known : GroupRecordAt work child dependencies)
    (ancestor : ref ∈ dependencies)
    (found : queue.taskNode? occurrence = some node) (stored : node.value = some value)
    (task
      : TaskHasOwners work occurrence (node.task.groups.map Execution.DeliveryNode.ref))
    (contributes : ref ∈ node.task.groups.map Execution.DeliveryNode.ref)
    (present : ref ∈ queue.groupNodes.map (fun owner => owner.group.node.ref))
    (uncancelled : ref ∉ queue.cancelledGroups)
    : (occurrence, value)
      ∈ published.take
          (((owners.foldl successGroupStep (queue, [], {})).2.1.take index).flatMap
            WorkQueueEvent.objectValues).length := by
  obtain ⟨steps, bound, exactPrefix⟩ := successGroupFold_carrier_boundary queue owners selected
  let boundary := (owners.take (steps + 1)).foldl successGroupStep (queue, [], {})
  have atBoundary : boundary.2.1[index]? = some (.groupSuccess group groups streams) := by
    rw [← exactPrefix, List.getElem?_take_of_lt (Nat.lt_succ_self _)]
    exact selected
  have inOutput : child.ref ∈ boundary.2.1.flatMap rawGroupNoticeRefs :=
    List.mem_flatMap.mpr ⟨_, List.mem_of_getElem? atBoundary,
      List.mem_map_of_mem (f := Execution.DeliveryNode.ref) noticed⟩
  rw [← successGroupFold_groupNotices queue (owners.take (steps + 1))] at inOutput
  obtain ⟨released, member, sameRef⟩ := List.mem_map.mp inOutput
  have ancestry := (successGroupFold_ancestorsRetired generated records links canonical
    live tasks roots (owners.take (steps + 1))).2 released member
  have retired := ancestry child dependencies known sameRef.symm ref ancestor occurrence _
    task contributes
  have retained := prefixes.ownerFold (steps + 1) (by omega)
    occurrence node value found stored ref contributes present
    (by simpa only [successGroupFold_cancelledGroups] using uncancelled)
  have emitted := retained.resolve_right (fun kept => retired.2 kept.2)
  have count : (boundary.2.1.flatMap WorkQueueEvent.objectValues).length
      = (((owners.foldl successGroupStep (queue, [], {})).2.1.take index).flatMap
          WorkQueueEvent.objectValues).length := by
    rw [← exactPrefix, List.take_add_one, selected]
    simp [WorkQueueEvent.objectValues]
  change (occurrence, value) ∈ published.take
    (boundary.2.1.flatMap WorkQueueEvent.objectValues).length at emitted
  rwa [count] at emitted

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
