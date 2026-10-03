import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.IntegrationPathCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ParentLinkCompleteness

/-! Canonical parentless candidates remain live through the exact registration passes. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- A parentless candidate cannot be refused because of an absent cancelled parent
-----------------------------------------------------------------------------------------

/-- Registering an available parentless descriptor leaves its ref live.
Witness: an existing lookup survives; otherwise fresh registration appends its shell.
This fact does not inspect the candidate's own historical cancellation marker.
-/
private theorem parentless_live (queue : State) (group : Group)
    (available : queue.GroupAvailable group.node.ref) (parentless : group.parent = none)
    : group.node.ref
      ∈ (queue.addGroup group).groupNodes.map (fun node => node.group.node.ref) := by
  rcases available with live | fresh
  · exact queue.addGroup_includesRefs group _ live
  · cases found : queue.groupNode? group.node.ref with
    | some node =>
        exact queue.addGroup_includesRefs group _
          (List.mem_map.mpr ⟨node, List.mem_of_find?_eq_some found, State.groupNode?_ref found⟩)
    | none =>
        simp [State.addGroup, fresh, found, parentless]

/-- Other-ref registration keeps availability; equal-ref parentless registration makes it live.
Witness: a different fresh ref cannot consume the target's permanent-registration slot.
-/
private theorem parentless_available {queue : State} {ref}
    (available : queue.GroupAvailable ref) (group : Group)
    (parentless : group.node.ref = ref → group.parent = none)
    : (queue.addGroup group).GroupAvailable ref := by
  by_cases same : group.node.ref = ref
  · exact .inl (same ▸ parentless_live queue group (same.symm ▸ available) (parentless same))
  · rcases available with live | fresh
    · exact .inl (queue.addGroup_includesRefs group ref live)
    · apply Or.inr
      unfold State.addGroup
      split
      · exact fresh
      · split <;> simp [fresh, Ne.symm same]

/-- A registration fold keeps its parentless candidate live, regardless of input order.
Witness: availability survives preceding descriptors and the matching descriptor installs
the ref; all subsequent registrations preserve it. Equal-ref descriptors share parentlessness.
-/
private theorem register_parentless_live (queue : State) (groups : List Group)
    {group : Group} (member : group ∈ groups)
    (available : queue.GroupAvailable group.node.ref)
    (canonical
      : ∀ candidate ∈ groups,
          candidate.node.ref = group.node.ref → candidate.parent = none)
    : group.node.ref
      ∈ (groups.foldl State.addGroup queue).groupNodes.map
          (fun node => node.group.node.ref) := by
  have preserve (more : List Group) (current : State) (ref : NodeRef)
      (live : ref ∈ current.groupNodes.map (fun node => node.group.node.ref))
      : ref ∈ (more.foldl State.addGroup current).groupNodes.map
          (fun node => node.group.node.ref) := by
    induction more generalizing current with
    | nil => exact live
    | cons head rest ih => exact ih _ (current.addGroup_includesRefs head ref live)
  induction groups generalizing queue with
  | nil => cases member
  | cons head rest ih =>
      rcases List.mem_cons.mp member with rfl | later
      · exact preserve rest _ _ (parentless_live queue group available
          (canonical group List.mem_cons_self rfl))
      · exact ih _ later (parentless_available available head (canonical head List.mem_cons_self))
          (fun candidate included => canonical candidate (List.mem_cons_of_mem _ included))

-----------------------------------------------------------------------------------------
-- Parent links and task/stream installation retain every newly live candidate root
-----------------------------------------------------------------------------------------

/-- Every canonical fresh parentless candidate remains live after both registration passes.
Witness: the registration fold installs its shell; the attachment pass preserves all refs.
No health, pending count, source validity, or descriptor-order premise is needed.
-/
theorem State.addGroups_parentless_live {queue : State} {parents : Nat → NodeRefs}
    (groups : List Group)
    (canonical : ∀ group ∈ groups, group.parent = (parents group.node.ref).head?)
    {group : Group} (member : group ∈ groups) (parentless : group.parent = none)
    (fresh : group.node.ref ∉ queue.registeredGroups)
    (absent : queue.groupNode? group.node.ref = none)
    : group.node.ref
      ∈ (queue.addGroups groups).1.groupNodes.map (fun node => node.group.node.ref) := by
  let candidates := groups.filter (fun group =>
    !queue.registeredGroups.contains group.node.ref && (queue.groupNode? group.node.ref).isNone)
  let link (current : State) (candidate : Group) : State :=
    match candidate.parent with
    | none => current
    | some parent =>
        match current.groupNode? parent with
        | none => current
        | some node =>
            let children := if node.childGroups.contains candidate.node.ref then
              node.childGroups else node.childGroups ++ [candidate.node.ref]
            current.putGroupNode { node with childGroups := children }
  have linked (more : List Group) (current : State)
      : (more.foldl link current).groupNodes.map (fun node => node.group.node.ref)
        = current.groupNodes.map (fun node => node.group.node.ref) := by
    induction more generalizing current with
    | nil => rfl
    | cons candidate rest ih =>
        rw [List.foldl_cons, ih]
        unfold link
        split
        · rfl
        · split
          · rfl
          · exact current.putGroupNode_refs _
  have live := register_parentless_live queue candidates
    (group := group) (by simp [candidates, member, fresh, absent]) (.inr fresh)
    (by
      intro candidate included same
      rw [canonical candidate (List.mem_filter.mp included).1, same,
        ← canonical group member, parentless])
  change group.node.ref ∈ (candidates.foldl link
    (candidates.foldl State.addGroup queue)).groupNodes.map (fun node => node.group.node.ref)
  rwa [linked]

/-- Every new canonical root candidate is live before integration's pruning stage.
Witness: parentless registration supplies a path of length zero; task and stream
installation preserve that path. This also covers taskless candidate shells.
-/
theorem State.maybeIntegrateWork_candidates_live {queue : State}
    {parents : Nat → NodeRefs} (unique : queue.GroupRefsUnique) (work : Work)
    (canonical : ∀ group ∈ work.groups, group.parent = (parents group.node.ref).head?)
    (parentTask : Option Occurrence := none)
    : ∀ group ∈ (queue.maybeIntegrateWork work parentTask).2.newGroups,
        ∃ node,
          (queue.maybeIntegrateWork work parentTask).1.groupNode? group.ref
          = some node := by
  intro group member
  obtain ⟨candidate, included, same, parentless, fresh, absent⟩ :=
    queue.addGroups_newGroup_candidate work.groups member
  have present := State.addGroups_parentless_live work.groups canonical
    included parentless (same.symm ▸ fresh) (same.symm ▸ absent)
  obtain ⟨node, nodeMember, nodeRef⟩ := List.mem_map.mp present
  have groupedRefs := unique.addGroups work.groups
  have groupedPath : (queue.addGroups work.groups).1.LiveDescendant group.ref group.ref :=
    .self (same ▸ nodeRef ▸ groupedRefs.groupNode?_of_mem nodeMember)
  have loop (more : List Task) (current : State) (refs : current.GroupRefsUnique)
      (path : current.LiveDescendant group.ref group.ref)
      : (more.foldl State.addTask current).LiveDescendant group.ref group.ref := by
    induction more generalizing current with
    | nil => exact path
    | cons task rest ih => exact ih _ (refs.addTask task) (path.addTask refs task)
  exact ((loop work.tasks _ groupedRefs groupedPath).addStreams work.streams
          parentTask).target_present

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
