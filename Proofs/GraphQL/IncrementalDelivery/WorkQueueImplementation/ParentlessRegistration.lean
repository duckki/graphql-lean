import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.IntegrationPathCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ParentLinkCompleteness

/-! Canonical parentless candidates remain live through recursive registration. -/

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
      intro registered
      rcases List.mem_append.mp (queue.addGroup_registeredGroups_subset group registered) with
        old | new
      · exact fresh old
      · exact same (List.mem_singleton.mp new).symm

/-- Every canonical fresh parentless candidate remains live after recursive registration.
Witness: parentless availability survives every installation, and traversal registers its ref.
No health, pending count, source validity, or descriptor-order premise is needed.
-/
theorem State.addGroups_parentless_live {queue : State} {parents : Nat → NodeRefs}
    (groups : List Group) (registered : queue.LiveGroupsRegistered)
    (canonical : ∀ group ∈ groups, group.parent = (parents group.node.ref).head?)
    {group : Group} (member : group ∈ groups) (parentless : group.parent = none)
    (fresh : group.node.ref ∉ queue.registeredGroups)
    (_absent : queue.groupNode? group.node.ref = none)
    : group.node.ref
      ∈ (queue.addGroups groups).1.groupNodes.map (fun node => node.group.node.ref) := by
  have available := State.addGroups_preserves (fun current => current.GroupAvailable group.node.ref)
    groups (fun _ candidate included prior => parentless_available prior candidate (fun same => by
      rw [canonical candidate included, same, ← canonical group member, parentless])) queue
    (Or.inr fresh)
  rcases available with live | missing
  · exact live
  · exact False.elim (missing ((queue.addGroups_registration registered groups).2.2 group member))

/-- Every new canonical root candidate is live before integration's pruning stage.
Witness: parentless registration supplies a path of length zero; task and stream
installation preserve that path. This also covers taskless candidate shells.
-/
theorem State.maybeIntegrateWork_candidates_live {queue : State}
    {parents : Nat → NodeRefs} (unique : queue.GroupRefsUnique)
    (registered : queue.LiveGroupsRegistered) (work : Work)
    (canonical : ∀ group ∈ work.groups, group.parent = (parents group.node.ref).head?)
    (parentTask : Option Occurrence := none)
    : ∀ group ∈ (queue.maybeIntegrateWork work parentTask).2.newGroups,
        ∃ node,
          (queue.maybeIntegrateWork work parentTask).1.groupNode? group.ref
          = some node := by
  intro group member
  obtain ⟨candidate, included, same, parentless, fresh, absent⟩ :=
    queue.addGroups_newGroup_candidate work.groups member
  have present := State.addGroups_parentless_live work.groups registered canonical
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
