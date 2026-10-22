import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.UncancelledAncestorPaths
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.HandlerPreparedFrames
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ProducerSupport

/-! Live task-produced groups inherit paths from uncancelled unsettled producer owners. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- A surviving task-produced group has a root path before successful owner release.
The live child excludes cancellation of its supporting producer owner. Success-only owner
accounting keeps that unsettled supporter live; canonical links connect its descendants. -/
theorem UncancelledReplayFrame.taskSuccess_childGroup_integrated_root_coverage
    {queue work parents before occurrence result incoming task ref}
    (frame : UncancelledReplayFrame queue work parents before)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (fresh : occurrence ∉ GraphEvent.groupSettlements before)
    (available : List (Occurrence × Nat))
    (found : (queue.cacheTaskFailures available).taskNode? occurrence = some incoming)
    (covered
      : let current := queue.cacheTaskFailures available
        ∀ ref ∈ incoming.task.groups.map Execution.DeliveryNode.ref,
          (∃ node, current.groupNode? ref = some node)
          → ∃ root ∈ current.rootGroups, current.LiveDescendant root ref)
    (member : task ∈ result.work.tasks)
    (contributing : ref ∈ task.groups.map Execution.DeliveryNode.ref)
    : let current := queue.cacheTaskFailures available
      let stored := current.putTaskNode { incoming with value := some result.value }
      let prepared := (stored.maybeIntegrateWork result.work (some occurrence)).1
      (∃ node, prepared.groupNode? ref = some node)
      → ∃ root ∈ prepared.rootGroups, prepared.LiveDescendant root ref := by
  intro current stored prepared survives
  obtain ⟨preparedParent, preparedRoots⟩ := frame.taskSuccess_preparedFrames generated canonical occurrence
    result matching incoming available found
  obtain ⟨childDescriptor, dependencies, childKnown, refEq, owner, contributes, support⟩ :=
    matching.childContributor_producer_support generated member contributing
  have lookup := State.taskNode?_some found
  have pending := frame.pending.cacheTaskFailures available
  have registered := pending.started incoming lookup.1
  have taskMatch := pending.matching incoming.task registered
  obtain ⟨_, taskPayload, producer, taskOccurrence, knownTask⟩ := taskMatch.1
  have incomingKnown : TaskHasOwners work incoming.task.occurrence
      (incoming.task.groups.map Execution.DeliveryNode.ref) :=
    ⟨producer, taskPayload, taskOccurrence.symm ▸ knownTask⟩
  have certificate := (pending.registration.children incoming.task registered).sourceChild lookup.2 matching
  have descriptors : ∀ candidate ∈ result.work.groups, ∃ dependencies,
      GroupRecordAt work candidate.node dependencies ∧ candidate.parent = dependencies.head? := by
    intro candidate member
    obtain ⟨dependencies, known⟩ := matching.taskChildGroups_recordAt member
    exact ⟨dependencies, known, by rw [canonical _ _ known]; exact matching.taskChildGroups_parentCanonical canonical member⟩
  obtain ⟨_, _, _, exactGroups, _⟩ := matching
  have sameGroups : incoming.task.groups = result.value.deliveryGroups :=
    Option.some.inj (taskMatch.2.symm.trans (lookup.2.symm ▸ exactGroups))
  have ownerContributes : owner ∈ incoming.task.groups.map Execution.DeliveryNode.ref := by
    rwa [sameGroups]
  obtain ⟨child, childFound⟩ := survives
  have childMember := List.mem_of_find?_eq_some childFound
  have childRecord := groupRecordAt_of_nodeAt childKnown
  have childRef := State.groupNode?_ref childFound
  have markers := ((frame.markers.cacheTaskFailures available).putTaskNode
    { incoming with value := some result.value }).maybeIntegrateWork
      (frame.parent.cacheTaskFailures available).closed canonical result.work (some occurrence)
        generated pending.registration.live descriptors certificate.parentRefs
  have cancellations := ((frame.cancellations.cacheTaskFailures available).putTaskNode
    { incoming with value := some result.value }).maybeIntegrateWork result.work (some occurrence)
  have ownerSafe : owner ∉ prepared.cancelledGroups := by
    rcases support with same | ancestor
    · rw [same]
      exact childRef ▸ cancellations.live_uncancelled childMember
    · exact markers.live_record_ancestors preparedParent.safe preparedParent.fields
        preparedParent.closed preparedParent.live canonical childRecord
        ⟨child, childMember, childRef.trans refEq.symm⟩ owner ancestor incoming.task.occurrence _
        incomingKnown ownerContributes
  have oldSafe : owner ∉ current.cancelledGroups := by
    intro cancelled
    apply ownerSafe
    change owner ∈ (stored.maybeIntegrateWork result.work (some occurrence)).1.cancelledGroups
    rw [State.maybeIntegrateWork_cancelledGroups stored result.work (some occurrence)]
    exact stored.addGroups_cancelledGroups_subset result.work.groups cancelled
  obtain ⟨supporter, supporterMember, sameRef, _⟩ := (frame.owners.cacheTaskFailures available)
    incoming.task registered (lookup.2.symm ▸ fresh) owner ownerContributes oldSafe
  obtain ⟨root, active, path⟩ := covered owner ownerContributes
    ⟨supporter, sameRef ▸ (frame.parent.cacheTaskFailures available).keys.groupNode?_of_mem
      supporterMember⟩
  have storedPath : stored.LiveDescendant root owner :=
    path.of_groupNodes_eq (queue := current) rfl
  have oldPath := storedPath.maybeIntegrateWork (frame.parent.cacheTaskFailures available).keys
    result.work (some occurrence)
  have rootActive : root ∈ prepared.rootGroups := by
    rwa [State.maybeIntegrateWork_rootGroups]
  refine ⟨root, rootActive, ?_⟩
  rcases support with same | ancestor
  · exact same ▸ oldPath
  · obtain ⟨_, nodeRecord⟩ := preparedParent.records child childMember
    have descriptor := generated.record_eq_node nodeRecord childKnown (childRef.trans refEq.symm)
    have descendant := preparedParent.uncancelled_ancestor_path preparedRoots.retired
      generated canonical (childRef ▸ childFound) (descriptor.symm ▸ childRecord) ancestor
      incomingKnown ownerContributes oldPath.target_present
    exact oldPath.trans (by simpa only [descriptor, refEq] using descendant)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
