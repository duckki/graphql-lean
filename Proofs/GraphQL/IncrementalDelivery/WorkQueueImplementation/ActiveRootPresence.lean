import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PendingRootPresence
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.AncestorRelease
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.DrainAncestorCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NoticeAncestorRetirement

/-! Live supported roots through activation and recursive ready-group draining. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Independently derived structural facts used at internal root-processing boundaries
-----------------------------------------------------------------------------------------

/-- Proof-only bundle of group metadata, registry coverage, and protected live roots.
Its fields are implementation facts; it adds no source or scheduler-contract premise.
-/
structure LiveRootFrame (queue : State) (work : Execution.Work) (parents : Nat → NodeRefs)
    : Prop where
  refs : queue.GroupRefsUnique
  records : queue.GroupNodesMatchWork work
  links : queue.ChildLinksCanonical parents
  registered : queue.LiveGroupsRegistered
  tasks : queue.TaskGroupsRegistered
  roots : queue.RootAncestorsRetired work
  support
    : queue.GroupRefSupport
        (fun ref => ∃ dependencies, NodeHasDependencies work ref .group dependencies)
  present : queue.RootGroupsPresent

/-- Activation preserves the frame when each release is protected, live, and supported.
Witness: activation preserves group records and extends roots by exactly the releases.
-/
theorem LiveRootFrame.startNewWork {queue work parents}
    (frame : LiveRootFrame queue work parents) (released : NewWork)
    (protectedRoots : ∀ child ∈ released.newGroups, queue.AncestorsRetired work child.ref)
    (live
      : ∀ child ∈ released.newGroups,
          child.ref ∈ queue.groupNodes.map (fun node => node.group.node.ref))
    (supported
      : ∀ child ∈ released.newGroups,
          ∃ dependencies, NodeHasDependencies work child.ref .group dependencies)
    : LiveRootFrame (queue.startNewWork released) work parents := by
  have coverage := State.startNewWork_registration frame.registered frame.tasks released
  refine ⟨frame.refs.startNewWork _, frame.records.startNewWork _, frame.links.startNewWork _,
    coverage.1, coverage.2, frame.roots.startNewWork _ protectedRoots,
    frame.support.startNewWork _ supported, frame.present.startNewWork _ ?_⟩
  intro ref member
  obtain ⟨child, included, same⟩ := List.mem_map.mp member
  exact same ▸ live child included

/-- Removing a failed group retains live records for all surviving active roots.
Witness: removal filters identical refs from roots and records; retirement is permanent.
-/
theorem LiveRootFrame.removeGroup {queue work parents}
    (frame : LiveRootFrame queue work parents) (ref : NodeRef)
    : LiveRootFrame (queue.removeGroup ref) work parents := by
  exact ⟨frame.refs.removeGroup _, frame.records.removeGroup _, frame.links.removeGroup _,
    fun node member => frame.registered node (List.mem_filter.mp member).1,
    frame.tasks, frame.roots.mono (queue.removeGroup_rootsSubset _)
      (fun _ retired => retired.removeGroup _),
    frame.support.removeGroup _, frame.present.removeGroup _⟩

/-- Successful closure preserves the live-root frame before child activation.
Witness: supported-root protection retains every other active record, while flushing and
pruning preserve registration, canonical links, and the surviving roots' retired ancestry.
-/
theorem LiveRootFrame.finishGroupSuccess_unactivated {queue work parents}
    (frame : LiveRootFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    {group : GroupNode} (found : queue.groupNode? group.group.node.ref = some group)
    (active : group.group.node.ref ∈ queue.rootGroups)
    : LiveRootFrame (queue.finishGroupSuccess group).1 work parents := by
  have coverage := State.finishGroupSuccess_registration frame.registered frame.tasks group
  exact ⟨frame.refs.finishGroupSuccess _, frame.records.finishGroupSuccess _,
    frame.links.finishGroupSuccess _, coverage.1, coverage.2.1,
    frame.roots.mono (queue.finishGroupSuccess_rootsSubset _)
      (fun _ retired => retired.finishGroupSuccess _),
    (frame.support.finishGroupSuccess group).1,
    frame.present.supported_finishGroupSuccess generated frame.roots frame.records
      frame.links canonical frame.support found active⟩

/-- A live active successful closure preserves the frame and activates protected children.
Witness: supported-root preservation protects other roots; pruning certifies each actual
release before it is activated. No task-bearing premise is imposed on intermediate shells.
-/
theorem LiveRootFrame.finishGroupSuccess {queue work parents}
    (frame : LiveRootFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    {group : GroupNode} (found : queue.groupNode? group.group.node.ref = some group)
    (active : group.group.node.ref ∈ queue.rootGroups)
    : let result := queue.finishGroupSuccess group
      LiveRootFrame (result.1.startNewWork result.2.2) work parents := by
  have protection := State.finishGroupSuccess_ancestorsRetired generated frame.records
    frame.links canonical frame.registered (List.mem_of_find?_eq_some found)
    (frame.roots _ active)
  have support := frame.support.finishGroupSuccess group
  have closed := frame.finishGroupSuccess_unactivated generated canonical found active
  exact closed.startNewWork _ protection.2.2
    (fun child member => State.finishGroupSuccess_newGroupsPresent frame.refs group child.ref
      (List.mem_map_of_mem member)) support.2

-----------------------------------------------------------------------------------------
-- Every executable drain prefix retains live roots, including transient failed roots
-----------------------------------------------------------------------------------------

/-- Every bounded recursive drain preserves the complete live-root frame.
Witness: invert the real ready-root search. Successful closures activate certified live
children; failure closures filter roots and records together. Neither case assumes health.
-/
theorem LiveRootFrame.drainReadyGroups_go {queue work parents}
    (frame : LiveRootFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (fuel : Nat)
    : LiveRootFrame (State.drainReadyGroups.go fuel queue).1 work parents := by
  induction fuel generalizing queue with
  | zero => exact frame
  | succ fuel ih =>
      unfold State.drainReadyGroups.go
      dsimp only
      split
      · exact frame
      · rename_i node selected
        obtain ⟨ref, active, choice⟩ := List.exists_of_findSome?_eq_some selected
        cases found : queue.groupNode? ref with
        | none => simp [found] at choice
        | some candidate =>
            simp only [found] at choice
            change (if candidate.failure.isSome || candidate.pending == 0 then
              some candidate else none) = some node at choice
            split at choice
            · cases Option.some.inj choice
              have same := State.groupNode?_ref found
              cases cached : node.failure with
              | none =>
                  exact ih (frame.finishGroupSuccess generated canonical
                    (same ▸ found) (same ▸ active))
              | some errors => exact ih (frame.removeGroup node.group.node.ref)
            · contradiction

/-- The executable drain's chosen finite bound preserves live active roots.
Witness: specialize bounded frame preservation to the current live-node count.
-/
theorem LiveRootFrame.drainReadyGroups {queue work parents}
    (frame : LiveRootFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    : LiveRootFrame queue.drainReadyGroups.1 work parents :=
  frame.drainReadyGroups_go generated canonical queue.groupNodes.length

-----------------------------------------------------------------------------------------
-- Previously announced ancestors complete by the actual recursive-drain notice carrier
-----------------------------------------------------------------------------------------

/-- An uncancelled ancestor noticed by this drain prefix has already closed.
Witness: recover the actual pre-carrier drain state, preserve live roots through it, and
apply the child's retirement certificate immediately after the selected successful flush.
Raw tracking then excludes both active retention and cancellation at that exact boundary.
-/
theorem LiveRootFrame.drainNoticeAncestor_completed {queue work parents}
    (frame : LiveRootFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (fuel : Nat) {index group groups streams child dependencies ref}
    (selected
      : (State.drainReadyGroups.go fuel queue).2[index]?
        = some (.groupSuccess group groups streams))
    (noticed : child ∈ groups) (known : GroupRecordAt work child dependencies)
    (ancestor : ref ∈ dependencies)
    (uncancelled : ref ∉ (State.drainReadyGroups.go fuel queue).1.cancelledGroups)
    (announced
      : ref
        ∈ queue.rootGroups
          ++ ((State.drainReadyGroups.go fuel queue).2.take (index + 1)).flatMap
              rawGroupNoticeRefs)
    : ref
      ∈ ((State.drainReadyGroups.go fuel queue).2.take (index + 1)).flatMap
          rawGroupClosureRefs := by
  obtain ⟨steps, node, before, bounded, found, active, cached, zero, same, output,
    exactPrefix⟩ := queue.drainReadyGroups_go_success_boundary fuel selected
  let segment := State.drainReadyGroups.go steps queue
  let closed := segment.1.finishGroupSuccess node
  let next := closed.1.startNewWork closed.2.2
  have prefixFrame := frame.drainReadyGroups_go generated canonical steps
  have nextFrame := prefixFrame.finishGroupSuccess generated canonical found active
  have ancestry := State.finishGroupSuccess_ancestorsRetired generated prefixFrame.records
    prefixFrame.links canonical prefixFrame.registered (List.mem_of_find?_eq_some found)
    (prefixFrame.roots _ active)
  have emitted : child.ref ∈ closed.2.1.flatMap rawGroupNoticeRefs := by
    rw [output]
    exact List.mem_flatMap.mpr ⟨_, List.mem_append_right _ List.mem_cons_self,
      List.mem_map_of_mem (f := Execution.DeliveryNode.ref) noticed⟩
  rw [← segment.1.finishGroupSuccess_groupNotices node] at emitted
  obtain ⟨released, included, sameRef⟩ := List.mem_map.mp emitted
  have tracking := (queue.drainReadyGroups_go_groupNoticeTracking steps).append
    (segment.1.finishGroupSuccess_groupNoticeTracking node)
    (by rw [State.startNewWork_cancelledGroups, State.finishGroupSuccess_cancelledGroups]
        exact fun _ member => member)
  have atCarrier : (State.drainReadyGroups.go fuel queue).2.take (index + 1)
      = segment.2 ++ closed.2.1 := by
    rw [List.take_add_one, selected, exactPrefix, output, List.append_assoc]
    rfl
  rw [atCarrier] at announced ⊢
  apply tracking.completed_of_inactive_uncancelled announced
  · intro retained
    obtain ⟨_, owner, producer, ownerKnown, ownerRef⟩ := nextFrame.support.roots ref retained
    obtain ⟨occurrence, owners, payload, task, contributes⟩ := ownerKnown.group_task
    have retired : next.RetiredGroup ref :=
      (ancestry.2.2 released included child dependencies known sameRef.symm
        ref ancestor occurrence owners ⟨producer, payload, task⟩
        (ownerRef ▸ contributes)).startNewWork _
    exact retired.2 (nextFrame.present ref retained)
  · intro cancelled
    rw [State.startNewWork_cancelledGroups, State.finishGroupSuccess_cancelledGroups]
      at cancelled
    exact uncancelled (queue.drainReadyGroups_go_prefix_cancelledSubset
      (Nat.le_of_lt bounded) cancelled)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
