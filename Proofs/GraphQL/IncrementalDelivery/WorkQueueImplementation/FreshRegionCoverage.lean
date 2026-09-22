import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CandidateRootCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RecordCancellation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ParentlessRegistration
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PruningBudget
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamAvailability

/-! Healthy fresh regions connect to their new candidate roots before stream-item pruning. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Every healthy candidate of a fresh parent-closed region reaches a new candidate root.
Witness: restrict the candidate family to healthy records. Health propagates to immediate
parents, freshness makes each available, and supported cancellation leaves them live.
Complete parent links then supply concrete root paths. The restriction is proof-only and
does not filter the executable queue's candidates or impose a new source law.
-/
theorem State.ParentLinksComplete.fresh_region_root_coverage {queue : State}
    {work : Execution.Work} {parents failed}
    (complete : queue.ParentLinksComplete parents) (unique : queue.GroupKeysUnique)
    (registered : queue.LiveGroupsRegistered)
    (closed : queue.ParentRegistryClosed parents)
    (cancelled : queue.CancelledRecordsSupported work failed) (newWork : Work)
    (parentTask : Option Occurrence)
    (descriptors
      : ∀ group ∈ newWork.groups,
          ∃ dependencies,
            GroupRecordAt work group.node dependencies
            ∧ group.parent = dependencies.head?)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    (parentCovered : newWork.ParentsCovered)
    (fresh : ∀ group ∈ newWork.groups, group.node.key ∉ queue.registeredGroups)
    (forest : (queue.maybeIntegrateWork newWork parentTask).1.RemovalForest parents)
    {group : Group} (member : group ∈ newWork.groups)
    (healthy : ¬GroupRecordInvalidated work failed group.node.key)
    : let integrated := queue.maybeIntegrateWork newWork parentTask
      ∃ root ∈ integrated.2.newGroups.map Execution.DeliveryNode.key,
        integrated.1.LiveDescendant root group.node.key := by
  intro integrated
  classical
  let candidates := newWork.groups.filter
    (fun candidate => decide (¬GroupRecordInvalidated work failed candidate.node.key))
  have eligible {candidate : Group} : candidate ∈ candidates
      ↔ candidate ∈ newWork.groups ∧ ¬GroupRecordInvalidated work failed candidate.node.key := by
    simp only [candidates, List.mem_filter, decide_eq_true_eq]
  have exactParents : ∀ candidate ∈ newWork.groups,
      candidate.parent = (parents candidate.node.key).head? := by
    intro candidate included
    obtain ⟨dependencies, known, head⟩ := descriptors candidate included
    rwa [canonical _ _ known] at head
  have links := complete.maybeIntegrateWork unique registered closed newWork exactParents parentTask
  have newCancelled := cancelled.maybeIntegrateWork newWork parentTask descriptors
  have newKeys := unique.maybeIntegrateWork newWork parentTask
  apply links.candidates_root_coverage forest candidates
    (integrated.2.newGroups.map Execution.DeliveryNode.key)
    (fun candidate included => exactParents candidate (eligible.mp included).1)
  · intro candidate included parent head
    obtain ⟨original, candidateHealthy⟩ := eligible.mp included
    obtain ⟨ancestor, ancestorMember, ancestorKey⟩ := parentCovered candidate original parent head
    obtain ⟨dependencies, known, parentEq⟩ := descriptors candidate original
    have inDependencies : parent ∈ dependencies := by
      have first := parentEq.symm.trans head
      cases dependencies with
      | nil => cases first
      | cons key rest => exact List.mem_cons.mpr (.inl (Option.some.inj first).symm)
    exact ⟨
      ancestor,
      eligible.mpr
        ⟨
          ancestorMember,
          fun invalid =>
            candidateHealthy (.ancestor known inDependencies (ancestorKey ▸ invalid))
        ⟩,
      ancestorKey
    ⟩
  · intro candidate included
    obtain ⟨original, candidateHealthy⟩ := eligible.mp included
    have uncancelled := newCancelled.healthy_not_mem candidateHealthy
    rw [State.maybeIntegrateWork_cancelledGroups queue newWork parentTask] at uncancelled
    have present := queue.maybeIntegrateWork_registersKeys newWork parentTask candidate original
      (.inr (fresh candidate original)) uncancelled
    obtain ⟨node, nodeMember, sameKey⟩ := List.mem_map.mp present
    exact ⟨node, sameKey ▸ newKeys.groupNode?_of_mem nodeMember⟩
  · intro candidate included parentless
    have original := (eligible.mp included).1
    have absent : queue.groupNode? candidate.node.key = none := by
      cases found : queue.groupNode? candidate.node.key with
      | none => rfl
      | some node =>
          exact False.elim (fresh candidate original (State.groupNode?_key found ▸
            registered node (List.mem_of_find?_eq_some found)))
    exact queue.addGroups_parentless_candidate newWork.groups original parentless
      (fresh candidate original) absent
  · exact eligible.mpr ⟨member, healthy⟩

-----------------------------------------------------------------------------------------
-- A fresh stream item's pruning and activation preserve its healthy candidate coverage
-----------------------------------------------------------------------------------------

/-- Every surviving healthy candidate of a fresh item lies beneath an activated root.
Witness: healthy-region coverage before pruning, live canonical parentless candidates,
and complete frontier pruning through taskless wrappers. The item handler activates
the covering retained candidate; no already-announced child premise is used.
-/
theorem State.ParentLinksComplete.fresh_item_root_coverage {queue : State}
    {work : Execution.Work} {parents failed}
    (complete : queue.ParentLinksComplete parents) (unique : queue.GroupKeysUnique)
    (registered : queue.LiveGroupsRegistered)
    (closed : queue.ParentRegistryClosed parents)
    (cancelled : queue.CancelledRecordsSupported work failed) (item : StreamItem)
    (descriptors
      : ∀ group ∈ item.work.groups,
          ∃ dependencies,
            GroupRecordAt work group.node dependencies
            ∧ group.parent = dependencies.head?)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    (parentCovered : item.work.ParentsCovered)
    (fresh : ∀ group ∈ item.work.groups, group.node.key ∉ queue.registeredGroups)
    (forest : (queue.maybeIntegrateWork item.work).1.RemovalForest parents)
    {group : Group} (member : group ∈ item.work.groups)
    (healthy : ¬GroupRecordInvalidated work failed group.node.key)
    (survives
      : ∃ node, (queue.integrateStreamItem item).groupNode? group.node.key = some node)
    : ∃ root ∈ (queue.integrateStreamItem item).rootGroups,
        (queue.integrateStreamItem item).LiveDescendant root group.node.key := by
  let integrated := queue.maybeIntegrateWork item.work
  let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
  let released := { integrated.2 with newGroups := pruned.2 }
  have exactParents : ∀ candidate ∈ item.work.groups,
      candidate.parent = (parents candidate.node.key).head? := by
    intro candidate included
    obtain ⟨dependencies, known, head⟩ := descriptors candidate included
    rwa [canonical _ _ known] at head
  have covered := complete.fresh_region_root_coverage unique registered closed cancelled
    item.work none descriptors canonical parentCovered fresh forest member healthy
  obtain ⟨root, rootMember, path⟩ := covered
  obtain ⟨candidate, included, candidateKey⟩ := List.mem_map.mp rootMember
  have frontier : integrated.1.GroupFrontier integrated.2.newGroups := by
    intro child member node nodeMember incoming
    obtain ⟨candidate, included, same, parentless, _⟩ :=
      queue.addGroups_newGroup_candidate item.work.groups member
    have head := forest.canonical node nodeMember child.key incoming
    rw [← same, ← exactParents candidate included, parentless] at head
    cases head
  have beforeStart : ∃ node, pruned.1.groupNode? group.node.key = some node := by
    change ∃ node,
      (pruned.1.startNewWork released).groupNode? group.node.key = some node at survives
    simpa only [State.groupNode?, (State.startNewWork_groupCore _ _).1] using survives
  have rootsLive := State.maybeIntegrateWork_candidates_live unique item.work exactParents
  obtain ⟨retained, retainedMember, below⟩ :=
    State.pruneEmptyGroups_surviving_descendant forest.canonical forest.uniqueChildren frontier
      (distinctDeliveryNodes_keys_nodup _)
      rootsLive
      ⟨candidate, included, candidateKey.symm ▸ path⟩ beforeStart
  refine ⟨retained.key, ?_, ?_⟩
  · change retained.key ∈ (pruned.1.startNewWork released).rootGroups
    rw [(pruned.1.startNewWork_groupCore released).2.2]
    exact List.mem_append_right _ (List.mem_map_of_mem retainedMember)
  · exact below.of_groupNodes_eq (pruned.1.startNewWork_groupCore released).1

/-- Generated stream-item regions supply all new-group coverage premises from bookkeeping.
Witness: the region inventory derives key freshness; matched lowering supplies complete
parent chains and descriptors; generated metadata derives the integration forest.
Only the target's health and survival are conditional, as required for terminal accounting.
-/
theorem State.RegionInventory.streamItem_healthy_group_root_coverage {queue : State}
    {work : Execution.Work} {parents failed seen}
    (inventory : queue.RegionInventory work seen) (generated : ExecutedWork work)
    (complete : queue.ParentLinksComplete parents) (unique : queue.GroupKeysUnique)
    (registered : queue.LiveGroupsRegistered)
    (closed : queue.ParentRegistryClosed parents)
    (cancelled : queue.CancelledRecordsSupported work failed)
    (records : queue.GroupNodesMatchWork work) (children : queue.ChildGroupsUnique)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    {stream items} (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    {item : StreamItem} (itemMember : item ∈ items) (fresh : item.occurrence ∉ seen)
    {group : Group} (member : group ∈ item.work.groups)
    (healthy : ¬GroupRecordInvalidated work failed group.node.key)
    (survives
      : ∃ node, (queue.integrateStreamItem item).groupNode? group.node.key = some node)
    : ∃ root ∈ (queue.integrateStreamItem item).rootGroups,
        (queue.integrateStreamItem item).LiveDescendant root group.node.key := by
  have exactParents : ∀ candidate ∈ item.work.groups,
      candidate.parent = (parents candidate.node.key).head? :=
    fun _ included => matching.streamItem_childGroups_parentCanonical canonical itemMember included
  have descriptors : ∀ candidate ∈ item.work.groups,
      ∃ dependencies, GroupRecordAt work candidate.node dependencies :=
    fun _ included => matching.streamItem_childGroups_recordAt itemMember included
  have forest := State.RemovalForest.of_generated generated
    (children.maybeIntegrateWork item.work) (links.maybeIntegrateWork item.work exactParents)
    (records.maybeIntegrateWork item.work descriptors) canonical
  apply complete.fresh_item_root_coverage unique registered closed cancelled item
    (canonical := canonical)
    (parentCovered := matching.streamItem_parentsCovered itemMember)
    (fresh := inventory.streamItem_groupsFresh generated matching itemMember fresh)
    (forest := forest) (member := member) (healthy := healthy) (survives := survives)
  intro candidate included
  obtain ⟨dependencies, known⟩ := descriptors candidate included
  exact ⟨
    dependencies,
    known,
    by rw [canonical _ _ known]; exact exactParents candidate included
  ⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
