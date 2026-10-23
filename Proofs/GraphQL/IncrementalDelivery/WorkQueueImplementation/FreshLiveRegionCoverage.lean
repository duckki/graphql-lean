import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.UncancelledAncestorPaths
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FreshRegionCoverage

/-! Surviving fresh region candidates inherit new roots without failure-inventory health. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Every live candidate of a fresh parent-closed region reaches a fresh candidate root.
The proof family contains live candidates. Live-parent safety makes this family parent
closed even when other candidates were retired by earlier cancellation. -/
theorem ParentCutFrame.fresh_live_region_root_coverage
    {queue work parents newWork parentTask group}
    (frame : ParentCutFrame queue work parents)
    (generated : ExecutedWork work)
    (prepared
      : ParentCutFrame (queue.maybeIntegrateWork newWork parentTask).1 work parents)
    (descriptors
      : ∀ candidate ∈ newWork.groups,
          ∃ dependencies,
            GroupRecordAt work candidate.node dependencies
            ∧ candidate.parent = dependencies.head?)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (parentCovered : newWork.ParentsCovered)
    (fresh : ∀ candidate ∈ newWork.groups, candidate.node.ref ∉ queue.registeredGroups)
    (forest : (queue.maybeIntegrateWork newWork parentTask).1.RemovalForest parents)
    (member : group ∈ newWork.groups)
    (survives
      : ∃ node,
          (queue.maybeIntegrateWork newWork parentTask).1.groupNode? group.node.ref
          = some node)
    : ∃ root ∈
        (queue.maybeIntegrateWork newWork parentTask).2.newGroups.map
          Execution.DeliveryNode.ref,
        (queue.maybeIntegrateWork newWork parentTask).1.LiveDescendant root
          group.node.ref := by
  classical
  let integrated := queue.maybeIntegrateWork newWork parentTask
  let candidates := newWork.groups.filter
    (fun candidate => decide (∃ node, integrated.1.groupNode? candidate.node.ref = some node))
  have eligible {candidate : Group} : candidate ∈ candidates ↔ candidate ∈ newWork.groups
      ∧ ∃ node, integrated.1.groupNode? candidate.node.ref = some node := by
    simp only [candidates, List.mem_filter, decide_eq_true_eq]
  have fields : ∀ candidate ∈ newWork.groups,
      candidate.parent = (parents candidate.node.ref).head? := by
    intro candidate included
    obtain ⟨dependencies, known, head⟩ := descriptors candidate included
    rwa [canonical _ _ known] at head
  have candidateSupport := State.registrationSupported_of_fresh_candidates generated
    newWork.groups fresh descriptors (fun candidate member parent head =>
      (parentCovered candidate member parent head).resolve_left (by simp))
  have parentRefs : ∀ candidate ∈ newWork.groups, ∀ parent, candidate.parent = some parent →
      parent ∈ queue.registeredGroups ++ newWork.groups.map (fun group => group.node.ref) := by
    intro candidate member parent head
    obtain ⟨ancestor, included, same⟩ :=
      (parentCovered candidate member parent head).resolve_left (by simp)
    exact List.mem_append_right _ (List.mem_map.mpr ⟨ancestor, included, same⟩)
  apply prepared.complete.candidates_root_coverage forest candidates
    (integrated.2.newGroups.map Execution.DeliveryNode.ref)
    (fun candidate included => fields candidate (eligible.mp included).1)
  · intro candidate included parent head
    obtain ⟨original, child, childFound⟩ := eligible.mp included
    obtain ⟨ancestor, ancestorMember, ancestorRef⟩ :=
      (parentCovered candidate original parent head).resolve_left (by simp)
    have present := queue.maybeIntegrateWork_registersRefs newWork parentTask generated
      frame.live descriptors parentRefs ancestor ancestorMember (candidateSupport ancestor ancestorMember)
    obtain ⟨node, nodeMember, sameRef⟩ := List.mem_map.mp present
    exact ⟨ancestor, eligible.mpr ⟨ancestorMember, node,
      sameRef ▸ prepared.keys.groupNode?_of_mem nodeMember⟩, ancestorRef⟩
  · intro candidate included
    exact (eligible.mp included).2
  · intro candidate included parentless
    have original := (eligible.mp included).1
    have absent : queue.groupNode? candidate.node.ref = none := by
      cases found : queue.groupNode? candidate.node.ref with
      | none => rfl
      | some node =>
          exact False.elim (fresh candidate original (State.groupNode?_ref found ▸
            frame.live node (List.mem_of_find?_eq_some found)))
    exact queue.addGroups_parentless_candidate newWork.groups frame.live fields original
      parentless (fresh candidate original) absent
  · exact eligible.mpr ⟨member, survives⟩

/-- Every surviving group from a fresh stream item lies below an activated root. -/
theorem ParentCutFrame.streamItem_live_group_root_coverage
    {queue work parents seen stream items item group}
    (frame : ParentCutFrame queue work parents)
    (inventory : queue.RegionInventory work seen) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (itemMember : item ∈ items) (fresh : item.occurrence ∉ seen)
    (member : group ∈ item.work.groups) (available : List (Occurrence × Nat))
    (survives
      : ∃ node,
          (queue.integrateStreamItem item available).groupNode? group.node.ref
          = some node)
    : ∃ root ∈ (queue.integrateStreamItem item available).rootGroups,
        (queue.integrateStreamItem item available).LiveDescendant root
          group.node.ref := by
  let integrated := queue.maybeIntegrateWork item.work
  let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
  let released := { integrated.2 with newGroups := pruned.2 }
  have fields : ∀ candidate ∈ item.work.groups,
      candidate.parent = (parents candidate.node.ref).head? :=
    fun _ included => matching.streamItem_childGroups_parentCanonical canonical itemMember included
  have records : ∀ candidate ∈ item.work.groups,
      ∃ dependencies, GroupRecordAt work candidate.node dependencies :=
    fun _ included => matching.streamItem_childGroups_recordAt itemMember included
  have certificate := generated.declarations.sourceStreamItem matching itemMember queue.registeredGroups
  have prepared := frame.maybeIntegrateWork item.work records fields certificate none generated canonical
  have forest := State.RemovalForest.of_generated generated prepared.children prepared.links
    prepared.records canonical
  have beforeStart : ∃ node, pruned.1.groupNode? group.node.ref = some node := by
    change ∃ node,
      (pruned.1.startNewWork released available).1.groupNode? group.node.ref = some node at survives
    exact State.groupNode?_exists_before_subset
      (pruned.1.startNewWork_groupNodes_sublist released available).subset survives
  have beforePrune : ∃ node, integrated.1.groupNode? group.node.ref = some node :=
    State.groupNode?_exists_before_subset
      (integrated.1.pruneEmptyGroups_groupNodes_sublist integrated.2.newGroups).subset beforeStart
  have descriptors : ∀ candidate ∈ item.work.groups,
      ∃ dependencies, GroupRecordAt work candidate.node dependencies
        ∧ candidate.parent = dependencies.head? := by
    intro candidate included
    obtain ⟨dependencies, known⟩ := records candidate included
    exact ⟨dependencies, known, by rw [canonical _ _ known]; exact fields candidate included⟩
  obtain ⟨root, rootMember, path⟩ := frame.fresh_live_region_root_coverage generated prepared descriptors
    canonical (matching.streamItem_parentsCovered generated.declarations itemMember)
    (inventory.streamItem_groupsFresh generated matching itemMember fresh) forest member beforePrune
  obtain ⟨candidate, included, candidateRef⟩ := List.mem_map.mp rootMember
  have frontier : integrated.1.GroupFrontier integrated.2.newGroups := by
    intro child member node nodeMember incoming
    obtain ⟨candidate, included, same, parentless, _⟩ :=
      queue.addGroups_newGroup_candidate item.work.groups member
    have head := forest.canonical node nodeMember child.ref incoming
    rw [← same, ← fields candidate included, parentless] at head
    cases head
  have rootsLive := State.maybeIntegrateWork_candidates_live frame.keys frame.live item.work fields
  obtain ⟨retained, retainedMember, below⟩ :=
    State.pruneEmptyGroups_surviving_descendant forest.canonical forest.uniqueChildren frontier
      (State.addGroups_newGroups_unique _ _) rootsLive
      ⟨candidate, included, candidateRef.symm ▸ path⟩ beforeStart
  have prunedForest := forest.of_subset
    (integrated.1.pruneEmptyGroups_groupNodes_sublist integrated.2.newGroups).subset
  exact State.startNewWork_root_coverage prunedForest released
    ⟨retained.ref, List.mem_append_right _ (List.mem_map_of_mem retainedMember), below⟩
    available survives

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
