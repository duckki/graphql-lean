import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ProtectedRootPresence
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.OwnerFoldBoundaries
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupNoticeTracking

/-! Live roots and pending releases at exact single-pass contributor boundaries. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Pending releases remain live and protected until the owner pass activates them
-----------------------------------------------------------------------------------------

/-- Proof-only state for live roots and releases awaiting the end of the contributor pass.
The support field applies to active roots, not every taskless intermediate record.
-/
private structure ReleasePresence (queue : State) (work : Execution.Work)
    (parents : Nat → NodeRefs) (released : List Execution.DeliveryNode)
    : Prop where
  refs : queue.GroupRefsUnique
  groups : queue.GroupNodesMatchWork work
  links : queue.ChildLinksCanonical parents
  registered : queue.LiveGroupsRegistered
  tasks : queue.TaskGroupsRegistered
  roots : queue.RootAncestorsRetired work
  support
    : queue.GroupRefSupport
        (fun ref => ∃ dependencies, NodeHasDependencies work ref .group dependencies)
  present : queue.RootGroupsPresent
  releaseProtected : ∀ node ∈ released, queue.AncestorsRetired work node.ref
  releasePresent
    : ∀ node ∈ released, node.ref ∈ queue.groupNodes.map (fun node => node.group.node.ref)
  releaseInactive : ∀ node ∈ released, node.ref ∉ queue.rootGroups

/-- One actual contributor step preserves old roots and earlier pending releases.
Witness: successful closure has an active, supported owner. It preserves every distinct
protected ref; its newly pruned releases are live, protected, and not old active roots.
-/
private theorem ReleasePresence.step {acc : State × List WorkQueueEvent × NewWork}
    {work parents} (prior : ReleasePresence acc.1 work parents acc.2.2.newGroups)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (group : Execution.DeliveryNode)
    : ReleasePresence (successGroupStep acc group).1 work parents
        (successGroupStep acc group).2.2.newGroups := by
  obtain ⟨current, events, released⟩ := acc
  dsimp only [successGroupStep]
  split
  · exact prior
  · rename_i node found
    let updated := { node with pending := node.pending - 1 }
    let next := current.putGroupNode updated
    have member := List.mem_of_find?_eq_some found
    have matching : next.GroupNodesMatchWork work :=
      prior.groups.putGroupNode updated (prior.groups node member)
    have links : next.ChildLinksCanonical parents :=
      prior.links.putGroupNode updated (prior.links node member)
    have registered : next.LiveGroupsRegistered :=
      prior.registered.putGroupNode updated (prior.registered node member)
    have roots : next.RootAncestorsRetired work :=
      prior.roots.mono (fun _ active => active) (fun _ retired => retired.putGroupNode updated)
    have support : next.GroupRefSupport
        (fun ref => ∃ dependencies, NodeHasDependencies work ref .group dependencies) :=
      prior.support.putGroupNode updated (prior.support.contents node member)
    have present : next.RootGroupsPresent := by
      intro ref active
      rw [State.putGroupNode_refs]
      exact prior.present ref active
    have releaseProtected : ∀ entry ∈ released.newGroups,
        next.AncestorsRetired work entry.ref :=
      fun entry included => (prior.releaseProtected entry included).mono
        (fun _ retired => retired.putGroupNode updated)
    have releasePresent : ∀ entry ∈ released.newGroups,
        entry.ref ∈ next.groupNodes.map (fun node => node.group.node.ref) := by
      intro entry included
      rw [State.putGroupNode_refs]
      exact prior.releasePresent entry included
    split
    · rename_i finishes
      have active : updated.group.node.ref ∈ next.rootGroups := by
        have flags := Bool.and_eq_true_iff.mp finishes
        have refEq := State.groupNode?_ref found
        simpa only [updated, refEq, List.contains_iff_mem]
          using (Bool.and_eq_true_iff.mp flags.1).1
      have updatedMember : updated ∈ next.groupNodes := by
        exact List.mem_map.mpr ⟨node, member, by simp [updated]⟩
      have protection := State.finishGroupSuccess_ancestorsRetired generated matching links
        canonical registered updatedMember (roots _ active)
      have coverage := State.finishGroupSuccess_registration registered prior.tasks updated
      have refs := prior.refs.putGroupNode updated
      have lookup := refs.groupNode?_of_mem updatedMember
      refine ⟨refs.finishGroupSuccess updated, matching.finishGroupSuccess updated,
        links.finishGroupSuccess updated, coverage.1, coverage.2.1,
        roots.mono (next.finishGroupSuccess_rootsSubset updated)
          (fun _ retired => retired.finishGroupSuccess updated),
        (support.finishGroupSuccess updated).1,
        present.supported_finishGroupSuccess generated roots matching links canonical
          support lookup active, ?_, ?_, ?_⟩
      · intro entry included
        rcases List.mem_append.mp included with earlier | new
        · exact (releaseProtected entry earlier).mono
            (fun _ retired => retired.finishGroupSuccess updated)
        · exact protection.2.2 entry new
      · intro entry included
        rcases List.mem_append.mp included with earlier | new
        · obtain ⟨dependencies, owner, producer, known, same⟩ := support.roots _ active
          obtain ⟨occurrence, owners, payload, task, contributes⟩ := known.group_task
          apply (releaseProtected entry earlier).supported_finishGroupSuccess_present
            generated matching links canonical (releasePresent entry earlier) lookup
            ⟨producer, payload, task⟩ (same ▸ contributes)
          intro equal
          exact prior.releaseInactive entry earlier (equal ▸ active)
        · exact State.finishGroupSuccess_newGroupsPresent refs updated entry.ref
            (List.mem_map_of_mem new)
      · intro entry included laterActive
        have oldActive := next.finishGroupSuccess_rootsSubset updated laterActive
        rcases List.mem_append.mp included with earlier | new
        · exact prior.releaseInactive entry earlier oldActive
        · exact State.finishGroupSuccess_supported_release_inactive generated refs roots
            matching links canonical support registered lookup active new oldActive
    · exact ⟨prior.refs.putGroupNode updated, matching, links, registered, prior.tasks,
        roots, support, present, releaseProtected, releasePresent, prior.releaseInactive⟩

/-- The owner fold retains live roots and live, inactive, ancestor-protected releases.
Witness: iterate the phase-aware invariant along the actual single-pass contributor loop.
Taskless registration shells are allowed; only active roots need contributing support.
-/
theorem successGroupFold_supported_rootsPresent {queue : State} {work parents}
    (generated : ExecutedWork work) (refs : queue.GroupRefsUnique)
    (records : queue.GroupNodesMatchWork work) (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (registered : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (roots : queue.RootAncestorsRetired work)
    (support
      : queue.GroupRefSupport
          (fun ref => ∃ dependencies, NodeHasDependencies work ref .group dependencies))
    (present : queue.RootGroupsPresent) (groups : List Execution.DeliveryNode)
    : let result := groups.foldl successGroupStep (queue, [], {})
      result.1.RootGroupsPresent
      ∧ ∀ entry ∈ result.2.2.newGroups,
          result.1.AncestorsRetired work entry.ref
          ∧ entry.ref ∈ result.1.groupNodes.map (fun node => node.group.node.ref)
          ∧ entry.ref ∉ result.1.rootGroups := by
  have loop (more : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent × NewWork)
      (prior : ReleasePresence acc.1 work parents acc.2.2.newGroups)
      : let result := more.foldl successGroupStep acc
        ReleasePresence result.1 work parents result.2.2.newGroups := by
    induction more generalizing acc with
    | nil => exact prior
    | cons group rest ih => exact ih _ (prior.step generated canonical group)
  have final := loop groups (queue, [], {})
    ⟨refs, records, links, registered, tasks, roots, support, present,
      by simp, by simp, by simp⟩
  exact ⟨final.present, fun entry included =>
    ⟨final.releaseProtected entry included, final.releasePresent entry included,
      final.releaseInactive entry included⟩⟩

-----------------------------------------------------------------------------------------
-- An announced ancestor has closed by this carrier, not merely by the final handler state
-----------------------------------------------------------------------------------------

/-- A contributing ancestor is neither active nor a pending release at this exact carrier.
Witness: stop the owner fold immediately after the selected carrier. Its child's retired
ancestry excludes live ancestors, while the phase invariant keeps both classes live.
-/
theorem successGroupFold_noticeAncestor_status {queue : State} {work parents}
    (generated : ExecutedWork work) (refs : queue.GroupRefsUnique)
    (records : queue.GroupNodesMatchWork work) (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (registered : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (roots : queue.RootAncestorsRetired work)
    (support
      : queue.GroupRefSupport
          (fun ref => ∃ dependencies, NodeHasDependencies work ref .group dependencies))
    (present : queue.RootGroupsPresent) (owners : List Execution.DeliveryNode)
    {index group groups streams child dependencies ref occurrence contributors}
    (selected
      : (owners.foldl successGroupStep (queue, [], {})).2.1[index]?
        = some (.groupSuccess group groups streams))
    (noticed : child ∈ groups) (known : GroupRecordAt work child dependencies)
    (ancestor : ref ∈ dependencies) (task : TaskHasOwners work occurrence contributors)
    (contributes : ref ∈ contributors)
    : ref
        ∉ ((owners.foldl successGroupStep (queue, [], {})).2.1.take (index + 1)).flatMap
            rawGroupNoticeRefs
      ∧ (ref ∈ queue.rootGroups
          → ref
            ∈ ((owners.foldl successGroupStep (queue, [], {})).2.1.take
                (index + 1)).flatMap
                rawGroupClosureRefs) := by
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
  have presence := successGroupFold_supported_rootsPresent generated refs records links
    canonical registered tasks roots support present (owners.take (steps + 1))
  have retired := (presence.2 released member).1 child dependencies known sameRef.symm
    ref ancestor occurrence contributors task contributes
  rw [exactPrefix]
  constructor
  · intro announced
    rw [← successGroupFold_groupNotices queue (owners.take (steps + 1))] at announced
    obtain ⟨earlier, included, same⟩ := List.mem_map.mp announced
    exact retired.2 (same ▸ (presence.2 earlier included).2.1)
  · intro active
    rcases queue.successGroupFold_tracks_roots (owners.take (steps + 1)) ref active with
      kept | closed
    · exact False.elim (retired.2 (presence.1 ref kept))
    · exact closed

/-- Every initially active ancestor has completed by the selected owner-fold carrier.
Witness: active-root support supplies its structural contributor, and the exact-boundary
status theorem excludes retention. Root tracking supplies an actual earlier completion.
-/
theorem successGroupFold_noticeAncestor_completed {queue : State} {work parents}
    (generated : ExecutedWork work) (refs : queue.GroupRefsUnique)
    (records : queue.GroupNodesMatchWork work) (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (registered : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (roots : queue.RootAncestorsRetired work)
    (support
      : queue.GroupRefSupport
          (fun ref => ∃ dependencies, NodeHasDependencies work ref .group dependencies))
    (present : queue.RootGroupsPresent) (owners : List Execution.DeliveryNode)
    {index group groups streams child dependencies ref}
    (selected
      : (owners.foldl successGroupStep (queue, [], {})).2.1[index]?
        = some (.groupSuccess group groups streams))
    (noticed : child ∈ groups) (known : GroupRecordAt work child dependencies)
    (ancestor : ref ∈ dependencies) (active : ref ∈ queue.rootGroups)
    : ref
      ∈ ((owners.foldl successGroupStep (queue, [], {})).2.1.take (index + 1)).flatMap
          rawGroupClosureRefs := by
  obtain ⟨dependencies, node, producer, nodeKnown, same⟩ := support.roots ref active
  obtain ⟨occurrence, contributors, payload, task, contributes⟩ := nodeKnown.group_task
  exact (successGroupFold_noticeAncestor_status generated refs records links canonical
    registered tasks roots support present owners selected noticed known ancestor
    ⟨producer, payload, task⟩ (same ▸ contributes)).2 active

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
