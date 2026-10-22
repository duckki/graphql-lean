import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.LiveAncestorCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FreshRegionCoverage

/-! Fresh item regions cover all surviving candidates, not just healthy candidates. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Restrict fresh candidates to actual live records, with no failure-health filter
-----------------------------------------------------------------------------------------

/-- Live candidates of a fresh parent-closed region reach its actual new root frontier.
Witness: freshness and the generated parent-closed declaration family support recursive
installation. Every candidate parent is live after registration. Filtering is proof-only.
-/
theorem State.ParentLinksComplete.fresh_live_region_root_coverage {queue : State}
    {work : Execution.Work} {parents} (complete : queue.ParentLinksComplete parents)
    (unique : queue.GroupRefsUnique) (registered : queue.LiveGroupsRegistered)
    (closed : queue.ParentRegistryClosed parents) (_safe : queue.LiveParentsUncancelled)
    (_fields : queue.GroupParentsCanonical parents) (generated : ExecutedWork work)
    (newWork : Work) (parentTask : Option Occurrence)
    (canonical : ∀ group ∈ newWork.groups, group.parent = (parents group.node.ref).head?)
    (parentCovered : newWork.ParentsCovered)
    (descriptors
      : ∀ candidate ∈ newWork.groups,
          ∃ dependencies,
            GroupRecordAt work candidate.node dependencies
            ∧ candidate.parent = dependencies.head?)
    (fresh : ∀ group ∈ newWork.groups, group.node.ref ∉ queue.registeredGroups)
    (forest : (queue.maybeIntegrateWork newWork parentTask).1.RemovalForest parents)
    {group : Group} (member : group ∈ newWork.groups)
    (survives
      : ∃ node,
          (queue.maybeIntegrateWork newWork parentTask).1.groupNode? group.node.ref
          = some node)
    : let integrated := queue.maybeIntegrateWork newWork parentTask
      ∃ root ∈ integrated.2.newGroups.map Execution.DeliveryNode.ref,
        integrated.1.LiveDescendant root group.node.ref := by
  intro integrated
  classical
  let candidates := newWork.groups.filter
    (fun candidate => (integrated.1.groupNode? candidate.node.ref).isSome)
  have eligible {candidate : Group} : candidate ∈ candidates
      ↔ candidate ∈ newWork.groups
        ∧ ∃ node, integrated.1.groupNode? candidate.node.ref = some node := by
    simp only [candidates, List.mem_filter, Option.isSome_iff_exists]
  have links := complete.maybeIntegrateWork unique registered closed newWork canonical parentTask
  have supported := State.registrationSupported_of_fresh_candidates generated newWork.groups
    fresh descriptors (fun candidate member parent head =>
      (parentCovered candidate member parent head).resolve_left (by simp))
  have parentRefs : ∀ candidate ∈ newWork.groups, ∀ parent, candidate.parent = some parent →
      parent ∈ queue.registeredGroups ++ newWork.groups.map (fun group => group.node.ref) := by
    intro candidate member parent head
    obtain ⟨ancestor, included, same⟩ :=
      (parentCovered candidate member parent head).resolve_left (by simp)
    exact List.mem_append_right _ (List.mem_map.mpr ⟨ancestor, included, same⟩)
  have nextKeys := unique.maybeIntegrateWork newWork parentTask
  apply links.candidates_root_coverage forest candidates
    (integrated.2.newGroups.map Execution.DeliveryNode.ref)
    (fun candidate included => canonical candidate (eligible.mp included).1)
  · intro candidate included parent parentEq
    have original := (eligible.mp included).1
    obtain ⟨ancestor, ancestorMember, ancestorKey⟩ :=
      (parentCovered candidate original parent parentEq).resolve_left (by simp)
    have present := queue.maybeIntegrateWork_registersRefs newWork parentTask generated
      registered descriptors parentRefs ancestor ancestorMember (supported ancestor ancestorMember)
    obtain ⟨parentNode, parentMember, sameKey⟩ := List.mem_map.mp present
    exact ⟨ancestor, eligible.mpr ⟨ancestorMember, parentNode,
      sameKey ▸ nextKeys.groupNode?_of_mem parentMember⟩, ancestorKey⟩
  · exact fun candidate included => (eligible.mp included).2
  · intro candidate included parentless
    have original := (eligible.mp included).1
    have absent : queue.groupNode? candidate.node.ref = none := by
      cases found : queue.groupNode? candidate.node.ref with
      | none => rfl
      | some node =>
          exact False.elim (fresh candidate original (State.groupNode?_ref found ▸
            registered node (List.mem_of_find?_eq_some found)))
    exact queue.addGroups_parentless_candidate newWork.groups registered canonical
      original parentless (fresh candidate original) absent
  · exact eligible.mpr ⟨member, survives⟩

-----------------------------------------------------------------------------------------
-- Taskless pruning and activation carry live candidate paths to active roots
-----------------------------------------------------------------------------------------

/-- Fresh stream-item integration covers every surviving candidate, including failed ones.
Witness: live-region coverage followed by the existing complete pruning frontier theorem.
No output notice, target health, or caller-supplied root is required.
-/
theorem State.ParentLinksComplete.fresh_live_item_root_coverage {queue : State}
    {work : Execution.Work} {parents} (complete : queue.ParentLinksComplete parents)
    (unique : queue.GroupRefsUnique) (registered : queue.LiveGroupsRegistered)
    (closed : queue.ParentRegistryClosed parents) (safe : queue.LiveParentsUncancelled)
    (fields : queue.GroupParentsCanonical parents) (generated : ExecutedWork work)
    (item : StreamItem)
    (canonical
      : ∀ group ∈ item.work.groups, group.parent = (parents group.node.ref).head?)
    (parentCovered : item.work.ParentsCovered)
    (descriptors
      : ∀ candidate ∈ item.work.groups,
          ∃ dependencies,
            GroupRecordAt work candidate.node dependencies
            ∧ candidate.parent = dependencies.head?)
    (fresh : ∀ group ∈ item.work.groups, group.node.ref ∉ queue.registeredGroups)
    (forest : (queue.maybeIntegrateWork item.work).1.RemovalForest parents)
    {group : Group} (member : group ∈ item.work.groups)
    (available : List (Occurrence × Nat) := [])
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
  have beforeStart : ∃ node, pruned.1.groupNode? group.node.ref = some node := by
    change ∃ node,
      (pruned.1.startNewWork released available).1.groupNode? group.node.ref = some node at survives
    exact State.groupNode?_exists_before_subset
      (pruned.1.startNewWork_groupNodes_sublist released available).subset survives
  have integratedSurvival : ∃ node, integrated.1.groupNode? group.node.ref = some node := by
    obtain ⟨node, found⟩ := beforeStart
    have member := (integrated.1.pruneEmptyGroups_groupNodes_sublist integrated.2.newGroups).subset
      (List.mem_of_find?_eq_some found)
    exact ⟨node, (State.groupNode?_ref found) ▸
      (unique.maybeIntegrateWork item.work).groupNode?_of_mem member⟩
  obtain ⟨root, rootMember, path⟩ := complete.fresh_live_region_root_coverage unique registered
    closed safe fields generated item.work none canonical parentCovered descriptors fresh forest member
    integratedSurvival
  obtain ⟨candidate, included, candidateKey⟩ := List.mem_map.mp rootMember
  have frontier : integrated.1.GroupFrontier integrated.2.newGroups := by
    intro child member node nodeMember incoming
    obtain ⟨candidate, included, same, parentless, _⟩ :=
      queue.addGroups_newGroup_candidate item.work.groups member
    have head := forest.canonical node nodeMember child.ref incoming
    rw [← same, ← canonical candidate included, parentless] at head
    cases head
  have rootsLive := State.maybeIntegrateWork_candidates_live unique registered item.work canonical
  obtain ⟨retained, retainedMember, below⟩ := State.pruneEmptyGroups_surviving_descendant
    forest.canonical forest.uniqueChildren frontier (State.addGroups_newGroups_unique _ _)
    rootsLive ⟨candidate, included, candidateKey.symm ▸ path⟩ beforeStart
  have prunedForest := forest.of_subset
    (integrated.1.pruneEmptyGroups_groupNodes_sublist integrated.2.newGroups).subset
  exact State.startNewWork_root_coverage prunedForest released
    ⟨retained.ref, List.mem_append_right _ (List.mem_map_of_mem retainedMember), below⟩
    available survives

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
