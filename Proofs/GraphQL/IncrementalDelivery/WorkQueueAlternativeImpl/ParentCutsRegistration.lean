import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ParentLinkReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CancellationRetirement

/-! Recursive parent registration and the cancellation boundary of live records.
These are derived bookkeeping facts, not additional host-source premises.
-/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Lowering registers parents before children
-----------------------------------------------------------------------------------------

/-- Each candidate's parent is known before that candidate is processed. -/
def ParentsBefore (known : NodeRefs) : List Group → Prop
  | [] => True
  | group :: rest =>
      (∀ parent, group.parent = some parent → parent ∈ known)
      ∧ ParentsBefore (known ++ [group.node.ref]) rest

theorem ParentsBefore.mono {known more groups} (ordered : ParentsBefore known groups)
    (included : known.Subset more)
    : ParentsBefore more groups := by
  induction groups generalizing known more with
  | nil => trivial
  | cons group rest ih =>
      exact ⟨
        fun parent same => included (ordered.1 parent same),
        ih ordered.2
          (by
            intro key member
            rcases List.mem_append.mp member with old | new
            · exact List.mem_append_left _ (included old)
            · exact List.mem_append_right _ new)
      ⟩

theorem ParentsBefore.append {known left right} (first : ParentsBefore known left)
    (second : ParentsBefore (known ++ left.map (fun group => group.node.ref)) right)
    : ParentsBefore known (left ++ right) := by
  induction left generalizing known with
  | nil => simpa using second
  | cons group rest ih =>
      refine ⟨first.1, ih first.2 ?_⟩
      simpa only [List.map_cons, List.append_assoc, List.singleton_append] using second

-----------------------------------------------------------------------------------------
-- Live records never name a cancelled immediate parent
-----------------------------------------------------------------------------------------

/-- Stronger than safe absent-parent cuts: every live record has an uncancelled parent. -/
def State.LiveParentsUncancelled (queue : State) : Prop :=
  ∀ node ∈ queue.groupNodes,
    ∀ parent, node.group.parent = some parent → parent ∉ queue.cancelledGroups

theorem State.LiveParentsUncancelled.map {queue : State}
    (safe : queue.LiveParentsUncancelled) (update : GroupNode → GroupNode)
    (same : ∀ node, (update node).group.parent = node.group.parent)
    : ({
        queue with
          groupNodes := queue.groupNodes.map update
      }).LiveParentsUncancelled := by
  intro node member parent parentEq
  obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
  exact safe old oldMember parent (by rwa [same] at parentEq)

theorem State.LiveParentsUncancelled.putGroupNode {queue : State}
    (safe : queue.LiveParentsUncancelled) (updated : GroupNode)
    (parentSafe
      : ∀ parent, updated.group.parent = some parent → parent ∉ queue.cancelledGroups)
    : (queue.putGroupNode updated).LiveParentsUncancelled := by
  intro node member parent parentEq
  obtain ⟨old, oldMember, same⟩ := List.mem_map.mp member
  split at same
  · subst node; exact parentSafe parent parentEq
  · subst node; exact safe old oldMember parent parentEq

/-- Installing below a live parent is safe because cancelled refs are retired.
A refused child may add a marker, but old live children's parents were already registered
and therefore cannot equal that fresh marker.
-/
theorem State.LiveParentsUncancelled.addGroup {queue : State} {parents}
    (safe : queue.LiveParentsUncancelled) (live : queue.LiveGroupsRegistered)
    (closed : queue.ParentRegistryClosed parents)
    (fields : queue.GroupParentsCanonical parents)
    (cancelled : queue.CancellationsRetired) (group : Group)
    : (queue.addGroup group).LiveParentsUncancelled := by
  unfold State.addGroup
  split
  · exact safe
  · rename_i absent
    have fresh : group.node.ref ∉ queue.registeredGroups :=
      (by simpa using absent :
        group.node.ref ∉ queue.registeredGroups ∧ queue.groupNode? group.node.ref = none).1
    have appended (parentSafe : ∀ parent, group.parent = some parent → parent ∉ queue.cancelledGroups)
        : ({queue with
            groupNodes := queue.groupNodes ++ [({group} : GroupNode)]} : State).LiveParentsUncancelled := by
      intro node member parent parentEq
      rcases List.mem_append.mp member with old | added
      · exact safe node old parent parentEq
      · obtain rfl := List.mem_singleton.mp added
        exact parentSafe parent parentEq
    split
    · exact appended (by intro parent same; rw [‹group.parent = none›] at same; cases same)
    · rename_i parent parentEq
      split
      · split
        · intro node member ancestor ancestorEq marked
          rcases List.mem_append.mp marked with old | added
          · exact safe node member ancestor ancestorEq old
          · have same := List.mem_singleton.mp added
            exact fresh (same ▸ closed.parent_registered live fields member ancestorEq)
        · exact safe
      · rename_i node found
        have parentSafe : ∀ other, group.parent = some other → other ∉ queue.cancelledGroups := by
          intro other same
          have equal : parent = other := Option.some.inj (parentEq.symm.trans same)
          exact equal ▸ (State.groupNode?_ref found) ▸
            cancelled.live_uncancelled (List.mem_of_find?_eq_some found)
        exact (appended parentSafe).putGroupNode _ (safe node (List.mem_of_find?_eq_some found))

private theorem parentRegistry_addGroup {queue : State} {parents}
    (closed : queue.ParentRegistryClosed parents) (group : Group)
    (canonical : group.parent = (parents group.node.ref).head?)
    (parentKnown : ∀ parent, group.parent = some parent → parent ∈ queue.registeredGroups)
    : (queue.addGroup group).ParentRegistryClosed parents := by
  intro ref member parent head
  have retained := queue.addGroup_registeredGroups_subset_old group
  rcases List.mem_append.mp (queue.addGroup_registeredGroups_subset group member) with old | fresh
  · exact retained (closed ref old parent head)
  · obtain rfl := List.mem_singleton.mp fresh
    exact retained (parentKnown parent (canonical.trans head))

/-- Recursive parent visits supply the safe registration order from declaration closure.
Witness: each installation retains registry closure, canonical fields, and the retirement
of cancelled refs. Candidate encounter order is unrestricted.
-/
theorem State.LiveParentsUncancelled.addGroups {queue : State} {work parents}
    (safe : queue.LiveParentsUncancelled) (live : queue.LiveGroupsRegistered)
    (closed : queue.ParentRegistryClosed parents)
    (fields : queue.GroupParentsCanonical parents)
    (cancelled : queue.CancellationsRetired) (groups : List Group)
    (generated : ExecutedWork work)
    (known : ∀ group ∈ groups, ∃ dependencies, GroupRecordAt work group.node dependencies)
    (canonical : ∀ group ∈ groups, group.parent = (parents group.node.ref).head?)
    (ancestry
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (covered
      : ∀ group ∈ groups,
          ∀ parent,
            group.parent = some parent
            → parent ∈ queue.registeredGroups
              ∨ ∃ candidate ∈ groups, candidate.node.ref = parent)
    : (queue.addGroups groups).1.LiveParentsUncancelled := by
  let property (current : State) := current.LiveParentsUncancelled
    ∧ current.LiveGroupsRegistered ∧ current.ParentRegistryClosed parents
    ∧ current.GroupParentsCanonical parents ∧ current.CancellationsRetired
    ∧ queue.registeredGroups ⊆ current.registeredGroups
  have ordered : ∀ group ∈ groups, ∀ parent, group.parent = some parent → parent < group.node.ref := by
    intro group member parent parentEq
    obtain ⟨dependencies, record⟩ := known group member
    exact generated.groupRecordAncestorSmaller record (List.mem_of_head? (by
      rw [ancestry _ _ record, ← canonical group member]; exact parentEq))
  exact (State.addGroups_preserves_parentRegistered property groups ordered
          (fun current group member _ visited prior => by
            have parentKnown
                : ∀ parent,
                    group.parent = some parent → parent ∈ current.registeredGroups := by
              intro parent parentEq
              rcases covered group member parent parentEq with old | fresh
              · exact prior.2.2.2.2.2 old
              · obtain ⟨candidate, included, same⟩ := fresh
                exact visited parent parentEq
                  (List.mem_map.mpr ⟨candidate, included, same⟩)
            exact ⟨
              prior.1.addGroup prior.2.1 prior.2.2.1 prior.2.2.2.1 prior.2.2.2.2.1 group,
              prior.2.1.addGroup group,
              parentRegistry_addGroup prior.2.2.1 group (canonical group member)
                parentKnown,
              prior.2.2.2.1.addGroup group (canonical group member),
              prior.2.2.2.2.1.addGroup group,
              prior.2.2.2.2.2.trans (current.addGroup_registeredGroups_subset_old group)
            ⟩)
          queue live ⟨safe, live, closed, fields, cancelled, List.Subset.refl _⟩).1

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
