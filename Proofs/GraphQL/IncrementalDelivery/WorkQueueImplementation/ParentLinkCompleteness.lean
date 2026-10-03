import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.HealthyAncestorCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.IntegrationPaths

/-! Completeness of canonical child links in the concrete registration passes. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- The registration pass may defer links only for its explicitly fresh candidates
-----------------------------------------------------------------------------------------

/-- Every live parent-child pair is linked, or the child's ref is still pending attachment.
The ref list describes the concrete second-pass input, not an extra runtime data structure.
-/
private def PendingParentLinks (queue : State) (parents : Nat → NodeRefs)
    (pending : NodeRefs)
    : Prop :=
  ∀ child ∈ queue.groupNodes,
  ∀ parent ∈ queue.groupNodes,
    (parents child.group.node.ref).head? = some parent.group.node.ref
    → child.group.node.ref ∈ pending ∨ child.group.node.ref ∈ parent.childGroups

/-- Membership-only registration produces only old records or newly appended empty shells.
Witness: inspect registration branches; the fold never modifies an existing record.
-/
private theorem register_origin (queue : State) (groups : List Group)
    : ∀ node ∈ (groups.foldl State.addGroup queue).groupNodes,
        node ∈ queue.groupNodes ∨ ∃ group ∈ groups, node = { group } := by
  induction groups generalizing queue with
  | nil => exact fun _ member => .inl member
  | cons group rest ih =>
      intro node member
      rcases ih _ node member with prior | ⟨other, later, same⟩
      · unfold State.addGroup at prior
        split at prior
        · exact .inl prior
        · split at prior
          · exact .inl prior
          · rcases List.mem_append.mp prior with old | added
            · exact .inl old
            · exact .inr ⟨group, List.mem_cons_self, List.mem_singleton.mp added⟩
      · exact .inr ⟨other, List.mem_cons_of_mem _ later, same⟩

/-- After fresh registration, only fresh child refs can lack their canonical live edge.
Witness: new children are pending; an old child cannot acquire a new parent because the
old permanent registry was parent-closed and no fresh ref belongs to that registry.
-/
private theorem register_pending {queue : State} {parents}
    (complete : queue.ParentLinksComplete parents)
    (registered : queue.LiveGroupsRegistered)
    (closed : queue.ParentRegistryClosed parents) (fresh : List Group)
    (newRefs : ∀ group ∈ fresh, group.node.ref ∉ queue.registeredGroups)
    : PendingParentLinks (fresh.foldl State.addGroup queue) parents
        (fresh.map (fun group => group.node.ref)) := by
  intro child childMember parent parentMember head
  rcases register_origin queue fresh child childMember with oldChild | ⟨group, member, same⟩
  · rcases register_origin queue fresh parent parentMember with oldParent | ⟨group, member, same⟩
    · exact .inr (complete child oldChild parent oldParent head)
    · have parentRegistered := closed child.group.node.ref (registered child oldChild)
        parent.group.node.ref head
      exact False.elim (newRefs group member (by simpa only [same] using parentRegistered))
  · exact .inl (List.mem_map.mpr ⟨group, member, by rw [same]⟩)

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

/-- Proof notation for the public second registration pass, with identical branch order. -/
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
-- Finish the exact two-pass registration algorithm
-----------------------------------------------------------------------------------------

/-- Registering canonical fresh groups establishes every live immediate-parent edge.
Witness: permanent parent closure protects old pairs during shell insertion; the second
pass discharges all fresh pending refs. Child-first order and duplicate references are allowed.
-/
theorem State.ParentLinksComplete.addGroups {queue : State} {parents}
    (complete : queue.ParentLinksComplete parents) (unique : queue.GroupRefsUnique)
    (registered : queue.LiveGroupsRegistered)
    (closed : queue.ParentRegistryClosed parents) (groups : List Group)
    (canonical : ∀ group ∈ groups, group.parent = (parents group.node.ref).head?)
    : (queue.addGroups groups).1.ParentLinksComplete parents := by
  let fresh := groups.filter (fun group =>
    !queue.registeredGroups.contains group.node.ref && (queue.groupNode? group.node.ref).isNone)
  have newRefs : ∀ group ∈ fresh, group.node.ref ∉ queue.registeredGroups := by
    intro group member
    have condition := (List.mem_filter.mp member).2
    simpa using (Bool.and_eq_true_iff.mp condition).1
  have registeredUnique : (fresh.foldl State.addGroup queue).GroupRefsUnique := by
    have loop (more : List Group) (current : State) (refs : current.GroupRefsUnique)
        : (more.foldl State.addGroup current).GroupRefsUnique := by
      induction more generalizing current with
      | nil => exact refs
      | cons group rest ih => exact ih _ (refs.addGroup group)
    exact loop fresh queue unique
  have loop (more : List Group) (current : State) (refs : current.GroupRefsUnique)
      (covered : PendingParentLinks current parents (more.map (fun group => group.node.ref)))
      (canonical : ∀ group ∈ more, group.parent = (parents group.node.ref).head?)
      : PendingParentLinks (more.foldl attachChild current) parents [] := by
    induction more generalizing current with
    | nil => exact covered
    | cons group rest ih =>
        have step := attach_complete refs covered (canonical group List.mem_cons_self)
        exact ih _ step.1 step.2
          (fun next member => canonical next (List.mem_cons_of_mem _ member))
  have final := loop fresh _ registeredUnique
    (register_pending complete registered closed fresh newRefs)
    (fun group member => canonical group (List.mem_filter.mp member).1)
  intro child childMember parent parentMember head
  rcases final child childMember parent parentMember head with impossible | linked
  · cases impossible
  · exact linked

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
