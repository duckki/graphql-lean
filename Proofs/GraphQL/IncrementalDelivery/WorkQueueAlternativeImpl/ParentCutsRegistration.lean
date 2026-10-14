import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ParentLinkReplay

/-! Parent-first lowering and the cancellation boundary of concrete registration.
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

private theorem groupChain_keys (nodes : List Execution.DeliveryNode)
    : (Work.fromExecution.groupChain nodes).map (fun group => group.node.ref)
      = nodes.reverse.map Execution.DeliveryNode.ref := by
  induction nodes with
  | nil => rfl
  | cons node rest ih => simp [Work.fromExecution.groupChain, ih, List.reverse_cons]

/-- The full ancestor chain is lowered in parent-first order, including taskless shells. -/
theorem groupChain_parentsBefore (nodes : List Execution.DeliveryNode)
    : ParentsBefore [] (Work.fromExecution.groupChain nodes) := by
  induction nodes with
  | nil => trivial
  | cons node rest ih =>
      apply ih.append
      refine ⟨?_, trivial⟩
      intro parent same
      cases rest with
      | nil => cases same
      | cons ancestor tail =>
          have key : ancestor.ref = parent := Option.some.inj same
          simp [groupChain_keys, ← key]

/-- Every immediate execution chunk provides its own ordered parent-registration chain. -/
theorem workFromExecution_parentsBefore (work : Execution.Work) (address : Address := [])
    : ParentsBefore [] (Work.fromExecution work address).groups := by
  cases work with
  | empty | stream => trivial
  | combine left right =>
      exact (workFromExecution_parentsBefore left _).append
        ((workFromExecution_parentsBefore right _).mono
          (by intro key member; cases member))
  | executionGroup groups path outcome children =>
      change ParentsBefore [] (groups.flatMap _)
      induction groups with
      | nil => trivial
      | cons group rest ih =>
          exact (groupChain_parentsBefore _).append
            (ih.mono (by intro key member; cases member))
termination_by sizeOf work

/-- Removing candidates already registered retains the order needed by the fresh pass. -/
theorem ParentsBefore.filter {known groups} (ordered : ParentsBefore known groups)
    (keep : Group → Bool) (skipped : ∀ group, keep group = false → group.node.ref ∈ known)
    : ParentsBefore known (groups.filter keep) := by
  induction groups generalizing known with
  | nil => trivial
  | cons group rest ih =>
      cases kept : keep group with
      | true =>
          rw [List.filter_cons, kept]
          exact ⟨ordered.1, ih ordered.2 (fun other absent =>
            List.mem_append_left _ (skipped other absent))⟩
      | false =>
          rw [List.filter_cons, kept]
          apply ih (ordered.2.mono ?_) skipped
          intro key member
          rcases List.mem_append.mp member with old | new
          · exact old
          · exact List.mem_singleton.mp new ▸ skipped group kept

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

/-- Refusing a fresh child cannot invalidate an older record's parent: that parent was
already registered. Accepted candidates pass the explicit cancellation guard.
-/
theorem State.LiveParentsUncancelled.addGroup {queue : State} {parents}
    (safe : queue.LiveParentsUncancelled) (live : queue.LiveGroupsRegistered)
    (closed : queue.ParentRegistryClosed parents)
    (fields : queue.GroupParentsCanonical parents) (group : Group)
    : (queue.addGroup group).LiveParentsUncancelled := by
  unfold State.addGroup
  split
  · exact safe
  · rename_i absent
    have fresh : group.node.ref ∉ queue.registeredGroups :=
      (by simpa using absent :
        group.node.ref ∉ queue.registeredGroups ∧ queue.groupNode? group.node.ref = none).1
    split
    · intro node member parent parentEq cancelled
      rcases List.mem_append.mp cancelled with old | added
      · exact safe node member parent parentEq old
      · have same := List.mem_singleton.mp added
        exact fresh (same ▸ closed.parent_registered live fields member parentEq)
    · rename_i allowed
      intro node member parent parentEq
      rcases List.mem_append.mp member with old | added
      · exact safe node old parent parentEq
      · obtain rfl := List.mem_singleton.mp added
        change group.parent = some parent at parentEq
        intro cancelled
        change parent ∈ queue.cancelledGroups at cancelled
        exact allowed (by simp [parentEq, cancelled])

/-- One ordered registration preserves parent-closed registry and live-key coverage. -/
private theorem register_frame {queue : State} {parents}
    (live : queue.LiveGroupsRegistered) (closed : queue.ParentRegistryClosed parents)
    (group : Group)
    (canonical : group.parent = (parents group.node.ref).head?)
    (parentKnown : ∀ parent, group.parent = some parent → parent ∈ queue.registeredGroups)
    : (queue.addGroup group).LiveGroupsRegistered
      ∧ (queue.addGroup group).ParentRegistryClosed parents
      ∧ queue.registeredGroups.Subset (queue.addGroup group).registeredGroups
      ∧ group.node.ref ∈ (queue.addGroup group).registeredGroups := by
  unfold State.addGroup
  split
  · rename_i old
    refine ⟨live, closed, List.Subset.refl _, ?_⟩
    rcases (by simpa using old : group.node.ref ∈ queue.registeredGroups
      ∨ (queue.groupNode? group.node.ref).isSome = true) with known | found
    · exact known
    · cases lookup : queue.groupNode? group.node.ref with
      | none => simp [lookup] at found
      | some node =>
          exact State.groupNode?_ref lookup ▸ live node (List.mem_of_find?_eq_some lookup)
  · have nextClosed : ({ queue with registeredGroups := queue.registeredGroups
        ++ [group.node.ref] } : State).ParentRegistryClosed parents := by
      intro key member parent head
      rcases List.mem_append.mp member with old | new
      · exact List.mem_append_left _ (closed key old parent head)
      · obtain rfl := List.mem_singleton.mp new
        exact List.mem_append_left _ (parentKnown parent (canonical.trans head))
    dsimp only
    split
    · exact ⟨fun node member => List.mem_append_left _ (live node member), nextClosed,
        List.subset_append_left _ _, by simp⟩
    · refine ⟨?_, nextClosed, List.subset_append_left _ _, by simp⟩
      intro node member
      rcases List.mem_append.mp member with old | added
      · exact List.mem_append_left _ (live node old)
      · obtain rfl := List.mem_singleton.mp added
        simp

theorem State.LiveParentsUncancelled.addGroups {queue : State} {parents}
    (safe : queue.LiveParentsUncancelled) (live : queue.LiveGroupsRegistered)
    (closed : queue.ParentRegistryClosed parents)
    (fields : queue.GroupParentsCanonical parents) (groups : List Group)
    (canonical : ∀ group ∈ groups, group.parent = (parents group.node.ref).head?)
    (ordered : ParentsBefore [] groups)
    : (queue.addGroups groups).1.LiveParentsUncancelled := by
  let keep (group : Group) := !queue.registeredGroups.contains group.node.ref
    && (queue.groupNode? group.node.ref).isNone
  let fresh := groups.filter keep
  have skipped (group : Group) (absent : keep group = false)
      : group.node.ref ∈ queue.registeredGroups := by
    by_cases known : group.node.ref ∈ queue.registeredGroups
    · exact known
    · have missing : queue.groupNode? group.node.ref = none := by
        cases found : queue.groupNode? group.node.ref with
        | none => rfl
        | some node => exact False.elim (known (State.groupNode?_ref found ▸
            live node (List.mem_of_find?_eq_some found)))
      simp [keep, known, missing] at absent
  have freshOrdered : ParentsBefore queue.registeredGroups fresh :=
    (ordered.mono (by intro key member; cases member)).filter keep skipped
  have register (more : List Group) (current : State)
      (safe : current.LiveParentsUncancelled) (live : current.LiveGroupsRegistered)
      (closed : current.ParentRegistryClosed parents)
      (fields : current.GroupParentsCanonical parents)
      (ordered : ParentsBefore current.registeredGroups more)
      (canonical : ∀ group ∈ more, group.parent = (parents group.node.ref).head?)
      : (more.foldl State.addGroup current).LiveParentsUncancelled := by
    induction more generalizing current with
    | nil => exact safe
    | cons group rest ih =>
        obtain ⟨nextLive, nextClosed, retained, added⟩ := register_frame live closed group
          (canonical group List.mem_cons_self) ordered.1
        apply ih _ (safe.addGroup live closed fields group) nextLive nextClosed
          (fields.addGroup group (canonical group List.mem_cons_self))
          (ordered.2.mono ?_)
          (fun other member => canonical other (List.mem_cons_of_mem _ member))
        intro key member
        rcases List.mem_append.mp member with old | new
        · exact retained old
        · exact List.mem_singleton.mp new ▸ added
  let link (current : State) (group : Group) : State :=
    match group.parent with
    | none => current
    | some parent =>
        match current.groupNode? parent with
        | none => current
        | some node =>
            let children := if node.childGroups.contains group.node.ref then
              node.childGroups else node.childGroups ++ [group.node.ref]
            current.putGroupNode { node with childGroups := children }
  have attach (more : List Group) (current : State)
      (safe : current.LiveParentsUncancelled)
      : (more.foldl link current).LiveParentsUncancelled := by
    induction more generalizing current with
    | nil => exact safe
    | cons group rest ih =>
        apply ih
        unfold link
        split
        · exact safe
        · split
          · exact safe
          · rename_i node found
            exact safe.putGroupNode _ (safe node (List.mem_of_find?_eq_some found))
  exact attach fresh _ (register fresh queue safe live closed fields freshOrdered
    (fun group member => canonical group (List.mem_filter.mp member).1))

-----------------------------------------------------------------------------------------
-- Matching host inputs supply ordered child chunks
-----------------------------------------------------------------------------------------

theorem GraphEvent.MatchesWork.childParentsBefore {work occurrence result}
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    : ParentsBefore [] result.work.groups := by
  obtain ⟨_, producer, known, _, childrenWork⟩ := matching
  cases occurrence with
  | item => cases childrenWork
  | executionGroup address =>
      obtain ⟨groups, path, outcome, children, enclosing, located, _, _⟩ := known
      change locateWork work address = some
        ⟨.executionGroup groups path outcome children, producer, enclosing⟩ at located
      have lowering : result.work = Work.fromExecution children (address ++ [0]) := by
        simpa [taskChildWork?, located] using childrenWork.symm
      rw [lowering]
      exact workFromExecution_parentsBefore _ _

theorem GraphEvent.MatchesWork.streamItem_parentsBefore {work stream items}
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    {item : StreamItem} (member : item ∈ items)
    : ParentsBefore [] item.work.groups := by
  obtain ⟨_, producer, known, childrenWork⟩ := matching item member
  cases occurrence : item.occurrence with
  | executionGroup => simp [streamItemWork?, occurrence] at childrenWork
  | item address index =>
      rw [occurrence] at known
      obtain ⟨node, entries, enclosing, result, children, located, entry, _, _⟩ := known
      change locateWork work address = some ⟨.stream node entries, producer, enclosing⟩ at located
      have lowering : item.work = Work.fromExecution children (address ++ [index]) := by
        simpa [streamItemWork?, occurrence, located, entry] using childrenWork.symm
      rw [lowering]
      exact workFromExecution_parentsBefore _ _

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
