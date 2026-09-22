import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ParentLinkReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.IntegrationPathCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ProducerSupport

/-! Healthy task-produced groups inherit concrete coverage from a live producer contributor. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Connect a newly integrated contributor to an already covered supporting producer owner
-----------------------------------------------------------------------------------------

/-- A healthy live task-produced group inherits root coverage through its producer.
Witness: pending accounting supplies a live supporting contributor before settlement;
integration preserves its old root path and complete parent links. Healthy retirement
excludes missing intermediate parents, connecting the new child through taskless wrappers.
The coverage premise concerns only the producer's existing healthy contributors, not the
new child. All other premises are independent concrete bookkeeping certificates.
-/
theorem State.HealthyRegisteredTaskAccounting.childGroup_integrated_root_coverage
    {queue : State} {work : Execution.Work} {parents settled failed}
    (accounted : queue.HealthyRegisteredTaskAccounting work settled failed)
    (tracks : queue.HealthyPendingTracks work settled failed)
    (taskMatching : queue.RegisteredTasksMatch work) (generated : ExecutedWork work)
    (records : queue.GroupNodesMatchWork work)
    (retirement : queue.HealthyRetiredAncestors work failed)
    (cancelled : queue.CancelledRecordsSupported work failed)
    (links : queue.ParentLinksComplete parents) (unique : queue.GroupKeysUnique)
    (registered : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (closed : queue.ParentRegistryClosed parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    {producer : Task} (producerMember : producer ∈ queue.tasks)
    (fresh : producer.occurrence ∉ settled) {result : TaskResult}
    (matching : (GraphEvent.taskSuccess producer.occurrence result).MatchesWork work)
    {group : Group} (member : group ∈ result.work.groups)
    (contributing
      : ∃ task ∈ result.work.tasks,
          group.node.key ∈ task.groups.map Execution.DeliveryNode.key)
    (healthy : ¬GroupRecordInvalidated work failed group.node.key)
    (covered
      : ∀ node ∈ queue.groupNodes,
          node.group.node.key ∈ producer.groups.map Execution.DeliveryNode.key
          → ¬GroupInvalidated work failed node.group.node.key
          → ∃ root ∈ queue.rootGroups, queue.LiveDescendant root node.group.node.key)
    : let integrated :=
        (queue.maybeIntegrateWork result.work (some producer.occurrence)).1
      (∃ node, integrated.groupNode? group.node.key = some node)
      → ∃ root ∈ integrated.rootGroups,
          integrated.LiveDescendant root group.node.key := by
  intro integrated survives
  obtain ⟨dependencies, childKnown, owner, ownerMember, ownerHealthy, ownerContributes,
    _, _, support⟩ := accounted.childGroup_live_support tracks taskMatching generated
      producerMember fresh matching member contributing
      (fun invalid => healthy invalid.toRecordInvalidated)
  obtain ⟨root, active, path⟩ := covered owner ownerMember ownerContributes ownerHealthy
  have oldPath : integrated.LiveDescendant root owner.group.node.key :=
    path.maybeIntegrateWork unique result.work (some producer.occurrence)
  have rootActive : root ∈ integrated.rootGroups := by
    rwa [State.maybeIntegrateWork_rootGroups]
  rcases support with same | ancestor
  · exact ⟨root, rootActive, same ▸ oldPath⟩
  · have groupCanonical : ∀ candidate ∈ result.work.groups,
        candidate.parent = (parents candidate.node.key).head? :=
      fun _ included => matching.taskChildGroups_parentCanonical canonical included
    have newRecords : ∀ candidate ∈ result.work.groups,
        ∃ ancestors, GroupRecordAt work candidate.node ancestors :=
      fun _ included => matching.taskChildGroups_recordAt included
    have newCancelled := cancelled.maybeIntegrateWork result.work (some producer.occurrence)
      (by
        intro candidate included
        obtain ⟨ancestors, known⟩ := newRecords candidate included
        exact ⟨ancestors, known, by rw [canonical _ _ known]; exact groupCanonical _ included⟩)
    have newRetirement := retirement.maybeIntegrateWork result.work
      (some producer.occurrence) newCancelled
    have newRegistry := closed.maybeIntegrateWork registered result.work groupCanonical
      matching.childParentsCovered (some producer.occurrence)
    have newRegistered := queue.maybeIntegrateWork_registration registered tasks result.work
      matching.childTasksCovered (some producer.occurrence)
    have newLinks := links.maybeIntegrateWork unique registered closed result.work
      groupCanonical (some producer.occurrence)
    have newMatching := records.maybeIntegrateWork result.work newRecords
      (some producer.occurrence)
    obtain ⟨child, childFound⟩ := survives
    obtain ⟨childDependencies, childRecord⟩ := newMatching child
      (List.mem_of_find?_eq_some childFound)
    have descriptor := generated.record_eq_node childRecord childKnown
      (State.groupNode?_key childFound)
    obtain ⟨⟨_, payload, taskProducer, _, knownTask⟩, _⟩ := taskMatching producer producerMember
    have descendant : integrated.LiveDescendant owner.group.node.key group.node.key := by
      rw [← descriptor]
      exact newLinks.healthy_ancestor_path generated newMatching newRetirement newRegistered.1
        newRegistry canonical (descriptor.symm ▸ childFound)
        (descriptor.symm ▸ groupRecordAt_of_nodeAt childKnown) (descriptor.symm ▸ healthy)
        ancestor (show TaskHasOwners work producer.occurrence
          (producer.groups.map Execution.DeliveryNode.key) from ⟨taskProducer, payload, knownTask⟩)
        ownerContributes oldPath.target_present
    exact ⟨root, rootActive, oldPath.trans descendant⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
