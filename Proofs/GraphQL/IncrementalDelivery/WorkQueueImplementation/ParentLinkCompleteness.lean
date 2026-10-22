import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.HealthyAncestorCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.IntegrationPaths

/-! Completeness of canonical child links in recursive registration. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- The registration pass may defer links only for its explicitly fresh candidates
-----------------------------------------------------------------------------------------

/-- Every live parent-child pair is linked, or the child's ref is still pending attachment.
The allowance is used only while proving one immediate installation; it is not queue state.
-/
private def PendingParentLinks (queue : State) (parents : Nat → NodeRefs)
    (pending : NodeRefs)
    : Prop :=
  ∀ child ∈ queue.groupNodes,
  ∀ parent ∈ queue.groupNodes,
    (parents child.group.node.ref).head? = some parent.group.node.ref
    → child.group.node.ref ∈ pending ∨ child.group.node.ref ∈ parent.childGroups

-----------------------------------------------------------------------------------------
-- Updating a parent only grows edges, and discharges its selected child's pending ref
-----------------------------------------------------------------------------------------

/-- Growing child lists under a ref-preserving map retains all already established links.
Witness: recover both old records and transport the old edge through the larger parent list.
-/
private theorem PendingParentLinks.map {queue : State} {parents pending}
    (complete : PendingParentLinks queue parents pending) (update : GroupNode → GroupNode)
    (refs : ∀ node, (update node).group.node.ref = node.group.node.ref)
    (children
      : ∀ node ∈ queue.groupNodes, node.childGroups.Subset (update node).childGroups)
    : PendingParentLinks { queue with groupNodes := queue.groupNodes.map update }
        parents pending := by
  intro child childMember parent parentMember head
  obtain ⟨oldChild, oldChildMember, rfl⟩ := List.mem_map.mp childMember
  obtain ⟨oldParent, oldParentMember, rfl⟩ := List.mem_map.mp parentMember
  rw [refs, refs] at head
  rw [refs]
  exact (complete oldChild oldChildMember oldParent oldParentMember head).elim
    Or.inl (fun linked => .inr (children oldParent oldParentMember linked))

/-- A looked-up parent update preserves pending-link accounting when its children grow.
Witness: unique refs identify replaced records, then the ref-preserving map theorem applies.
-/
private theorem PendingParentLinks.putGroupNode {queue : State} {parents pending ref node}
    (complete : PendingParentLinks queue parents pending) (unique : queue.GroupRefsUnique)
    (found : queue.groupNode? ref = some node) (updated : GroupNode)
    (sameRef : updated.group.node.ref = node.group.node.ref)
    (children : node.childGroups.Subset updated.childGroups)
    : PendingParentLinks (queue.putGroupNode updated) parents pending := by
  apply complete.map
    (fun old => if old.group.node.ref == updated.group.node.ref then updated else old)
  · intro old
    split
    · rename_i same
      exact (beq_iff_eq.mp same).symm
    · rfl
  · intro old member
    split
    · rename_i same
      have equal := unique.sameNode member (List.mem_of_find?_eq_some found)
        ((beq_iff_eq.mp same).trans sameRef)
      exact equal ▸ children
    · exact List.Subset.refl _

/-- Proof notation for the immediate parent update after one shell installation. -/
private def attachChild (queue : State) (group : Group) : State :=
  match group.parent with
  | none => queue
  | some parent =>
      match queue.groupNode? parent with
      | none => queue
      | some node =>
          let children :=
            if node.childGroups.contains group.node.ref then
              node.childGroups
            else
              node.childGroups ++ [group.node.ref]
          queue.putGroupNode { node with childGroups := children }

/-- A single attachment discharges its candidate's missing-edge allowance.
Witness: a parentless candidate needs no edge, an absent parent supplies no live pair,
and a live parent's ref-replacing update installs the child in every matching record.
-/
private theorem attach_complete {queue : State} {parents pending group}
    (unique : queue.GroupRefsUnique)
    (complete : PendingParentLinks queue parents (group.node.ref :: pending))
    (canonical : group.parent = (parents group.node.ref).head?)
    : (attachChild queue group).GroupRefsUnique
      ∧ PendingParentLinks (attachChild queue group) parents pending := by
  unfold attachChild
  cases parentEq : group.parent with
  | none =>
      refine ⟨unique, ?_⟩
      intro child childMember parent parentMember head
      rcases complete child childMember parent parentMember head with unlinked | linked
      · rcases List.mem_cons.mp unlinked with same | later
        · rw [same, ← canonical, parentEq] at head
          contradiction
        · exact .inl later
      · exact .inr linked
  | some ref =>
      dsimp only
      cases found : queue.groupNode? ref with
      | none =>
          refine ⟨unique, ?_⟩
          intro child childMember parent parentMember head
          rcases complete child childMember parent parentMember head with unlinked | linked
          · rcases List.mem_cons.mp unlinked with same | later
            · rw [same, ← canonical, parentEq] at head
              have parentRef := Option.some.inj head
              have absent := List.find?_eq_none.mp found parent parentMember
              exact False.elim (absent (beq_iff_eq.mpr parentRef.symm))
            · exact .inl later
          · exact .inr linked
      | some node =>
          let children := if node.childGroups.contains group.node.ref then
            node.childGroups else node.childGroups ++ [group.node.ref]
          let updated : GroupNode := { node with childGroups := children }
          have grows : node.childGroups.Subset children := by
            dsimp only [children]
            split
            · exact List.Subset.refl _
            · exact List.subset_append_left _ _
          have attached : group.node.ref ∈ children := by
            dsimp only [children]
            split
            · rename_i listed
              simpa using listed
            · exact List.mem_append_right _ List.mem_cons_self
          have preserved := complete.putGroupNode unique found updated rfl grows
          refine ⟨unique.putGroupNode _, ?_⟩
          intro child childMember parent parentMember head
          rcases preserved child childMember parent parentMember head with unlinked | linked
          · rcases List.mem_cons.mp unlinked with same | later
            · rw [same, ← canonical, parentEq] at head
              have parentRef := Option.some.inj head
              obtain ⟨old, member, replaced⟩ := List.mem_map.mp parentMember
              change (if old.group.node.ref == node.group.node.ref then updated else old)
                = parent at replaced
              by_cases equal : old.group.node.ref == node.group.node.ref
              · rw [ite_eq_left equal] at replaced
                subst parent
                exact .inr (by simpa only [same] using attached)
              · rw [ite_eq_right equal] at replaced
                subst parent
                exact False.elim (equal (beq_iff_eq.mpr
                  (parentRef.symm.trans (State.groupNode?_ref found).symm)))
            · exact .inl later
          · exact .inr linked

-----------------------------------------------------------------------------------------
-- Immediate installation preserves completeness and live-parent registration
-----------------------------------------------------------------------------------------

private def LiveParentsRegistered (queue : State) (parents : Nat → NodeRefs) : Prop :=
  ∀ ref ∈ queue.groupNodes.map (fun node => node.group.node.ref),
    ∀ parent, (parents ref).head? = some parent → parent ∈ queue.registeredGroups

private theorem liveParents_addGroup {queue : State} {parents}
    (prior : LiveParentsRegistered queue parents)
    (registered : queue.LiveGroupsRegistered) (group : Group)
    (canonical : group.parent = (parents group.node.ref).head?)
    : LiveParentsRegistered (queue.addGroup group) parents := by
  have appended (parentReady : ∀ parent, group.parent = some parent → parent ∈ queue.registeredGroups)
      : LiveParentsRegistered {queue with
          registeredGroups := queue.registeredGroups ++ [group.node.ref],
          groupNodes := queue.groupNodes ++ [({group} : GroupNode)]} parents := by
    intro ref member parent head
    rw [List.map_append, List.map_singleton] at member
    rcases List.mem_append.mp member with old | fresh
    · exact List.mem_append_left _ (prior ref old parent head)
    · obtain rfl := List.mem_singleton.mp fresh
      exact List.mem_append_left _ (parentReady parent (canonical.trans head))
  unfold State.addGroup
  split
  · exact prior
  · split
    · exact appended (by intro parent same; rw [‹group.parent = none›] at same; cases same)
    · rename_i parent parentEq
      split
      · split <;> exact fun ref member ancestor head =>
          List.mem_append_left _ (prior ref member ancestor head)
      · rename_i node found
        intro ref member ancestor head
        rw [State.putGroupNode_refs] at member
        exact appended (fun other same => by
          have equal : parent = other := Option.some.inj (parentEq.symm.trans same)
          exact equal ▸ ((State.groupNode?_ref found) ▸
            registered node (List.mem_of_find?_eq_some found))) ref member ancestor head

private theorem complete_addGroup {queue : State} {parents}
    (complete : queue.ParentLinksComplete parents) (unique : queue.GroupRefsUnique)
    (closed : LiveParentsRegistered queue parents) (group : Group)
    (canonical : group.parent = (parents group.node.ref).head?)
    : (queue.addGroup group).ParentLinksComplete parents := by
  unfold State.addGroup
  split
  · exact complete
  · rename_i guard
    have absent : group.node.ref ∉ queue.registeredGroups
        ∧ queue.groupNode? group.node.ref = none := by simpa using guard
    let appended : State := {queue with
      registeredGroups := queue.registeredGroups ++ [group.node.ref],
      groupNodes := queue.groupNodes ++ [({group} : GroupNode)]}
    have pending : PendingParentLinks appended parents [group.node.ref] := by
      intro child childMember parent parentMember head
      rcases List.mem_append.mp childMember with oldChild | newChild
      · rcases List.mem_append.mp parentMember with oldParent | newParent
        · exact .inr (complete child oldChild parent oldParent head)
        · obtain rfl := List.mem_singleton.mp newParent
          exact False.elim (absent.1 (closed child.group.node.ref
            (List.mem_map_of_mem oldChild) group.node.ref head))
      · obtain rfl := List.mem_singleton.mp newChild
        exact .inl List.mem_cons_self
    have appendedUnique : appended.GroupRefsUnique := by
      have fresh : group.node.ref ∉ queue.groupNodes.map (fun node => node.group.node.ref) := by
        intro member
        obtain ⟨node, member, same⟩ := List.mem_map.mp member
        exact List.find?_eq_none.mp absent.2 node member (beq_iff_eq.mpr same)
      change ((queue.groupNodes ++ [({group} : GroupNode)]).map _).Nodup
      simpa [List.map_append, fresh] using List.nodup_append.mpr
        ⟨unique, by simp, by
          intro ref member other included same
          obtain rfl := List.mem_singleton.mp included
          exact fresh (same ▸ member)⟩
    have attached := (attach_complete appendedUnique pending canonical).2
    have result : (attachChild appended group).ParentLinksComplete parents := by
      intro child childMember parent parentMember head
      exact (attached child childMember parent parentMember head).resolve_left (by simp)
    split
    · simpa only [attachChild, ‹group.parent = none›, appended] using result
    · rename_i parent parentEq
      split
      · split <;> exact complete
      · rename_i node found
        have installed : appended.groupNode? parent = some node := by
          simp only [State.groupNode?, appended, List.find?_append]
          change (queue.groupNode? parent).or _ = some node
          simp [found]
        simpa only [attachChild, parentEq, installed, appended] using result

/-- Canonical recursive installation establishes every live immediate-parent edge.
Witness: each shell is attached immediately, and every live child's parent remains in
registration history. The invariant permits arbitrary candidate encounter order.
-/
theorem State.ParentLinksComplete.addGroups {queue : State} {parents}
    (complete : queue.ParentLinksComplete parents) (unique : queue.GroupRefsUnique)
    (registered : queue.LiveGroupsRegistered)
    (closed : queue.ParentRegistryClosed parents) (groups : List Group)
    (canonical : ∀ group ∈ groups, group.parent = (parents group.node.ref).head?)
    : (queue.addGroups groups).1.ParentLinksComplete parents := by
  let property (current : State) := current.ParentLinksComplete parents
    ∧ current.GroupRefsUnique ∧ current.LiveGroupsRegistered
      ∧ LiveParentsRegistered current parents
  have initial : property queue := by
    refine ⟨complete, unique, registered, ?_⟩
    intro ref member parent head
    obtain ⟨node, included, same⟩ := List.mem_map.mp member
    exact closed ref (same ▸ registered node included) parent head
  exact (State.addGroups_preserves property groups (fun current group member prior =>
    ⟨complete_addGroup prior.1 prior.2.1 prior.2.2.2 group (canonical group member),
      prior.2.1.addGroup group,
      prior.2.2.1.addGroup group,
      liveParents_addGroup prior.2.2.2 prior.2.2.1 group (canonical group member)⟩)
    queue initial).1

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
