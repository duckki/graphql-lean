import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.LiveRegistration
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ProtectedRootPresence
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.IntegrationCandidates
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamPreparation

/-! Fresh integration paths cannot reach previously registered groups. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Registration installs no edge from a new group into the old registry
-----------------------------------------------------------------------------------------

/-- Groups outside `old` have child links only to refs outside that earlier registry.
Old parents may acquire new children; only the reverse direction is excluded.
-/
def State.FreshChildLinks (queue : State) (old : NodeRefs) : Prop :=
  ∀ node ∈ queue.groupNodes,
    node.group.node.ref ∉ old → ∀ child ∈ node.childGroups, child ∉ old

/-- A ref-replacing update preserves fresh links when its own children satisfy the rule.
Witness: every resulting node is either the supplied replacement or an unchanged record.
-/
theorem State.FreshChildLinks.putGroupNode {queue : State} {old : NodeRefs}
    (links : queue.FreshChildLinks old) (updated : GroupNode)
    (valid : updated.group.node.ref ∉ old → ∀ child ∈ updated.childGroups, child ∉ old)
    : (queue.putGroupNode updated).FreshChildLinks old := by
  intro node member fresh child included
  obtain ⟨prior, priorMember, same⟩ := List.mem_map.mp member
  split at same
  · subst node; exact valid fresh child included
  · subst node; exact links prior priorMember fresh child included

/-- A new shell has no children, and its immediate parent gains only a fresh ref.
Witness: the entry registry contains `old`, so a newly attached ref cannot point back
into it. Existing links are retained through the parent's metadata update.
-/
theorem State.FreshChildLinks.addGroup {queue : State} {old : NodeRefs}
    (links : queue.FreshChildLinks old) (group : Group)
    (registered : old ⊆ queue.registeredGroups)
    : (queue.addGroup group).FreshChildLinks old := by
  unfold State.addGroup
  split
  · exact links
  · rename_i absent
    have fresh : group.node.ref ∉ old := by
      intro member
      have missing : group.node.ref ∉ queue.registeredGroups
          ∧ queue.groupNode? group.node.ref = none := by simpa using absent
      exact missing.1 (registered member)
    have appended : ({queue with
        groupNodes := queue.groupNodes ++ [({group} : GroupNode)]} : State).FreshChildLinks old := by
      intro node member newRef child included
      rcases List.mem_append.mp member with prior | added
      · exact links node prior newRef child included
      · obtain rfl := List.mem_singleton.mp added
        cases included
    split
    · exact appended
    · split
      · split <;> exact links
      · rename_i node found
        apply appended.putGroupNode
        intro newParent child member
        split at member
        · exact links node (List.mem_of_find?_eq_some found) newParent child member
        · rcases List.mem_append.mp member with prior | added
          · exact links node (List.mem_of_find?_eq_some found) newParent child prior
          · exact List.mem_singleton.mp added ▸ fresh

/-- Recursive integration installs no edge from a fresh group into the entry registry.
Witness: live entry groups are registered, and every installation retains that registry
while attaching only its fresh child ref.
-/
theorem State.addGroups_freshChildLinks {queue : State}
    (registered : queue.LiveGroupsRegistered) (groups : List Group)
    : (queue.addGroups groups).1.FreshChildLinks queue.registeredGroups := by
  let property (current : State) := current.FreshChildLinks queue.registeredGroups
    ∧ queue.registeredGroups ⊆ current.registeredGroups
  have initial : property queue := by
    refine ⟨?_, List.Subset.refl _⟩
    intro node member absent
    exact False.elim (absent (registered node member))
  exact (State.addGroups_preserves property groups
          (fun current group _ prior =>
            ⟨
              prior.1.addGroup group prior.2,
              prior.2.trans (current.addGroup_registeredGroups_subset_old group)
            ⟩)
          queue initial).1

-----------------------------------------------------------------------------------------
-- Task and stream registration leave group child edges unchanged
-----------------------------------------------------------------------------------------

/-- Task registration changes group memberships and counts, but never child refs.
Witness: every owner update preserves the fresh-link condition of its looked-up record.
-/
theorem State.FreshChildLinks.addTask {queue : State} {old : NodeRefs}
    (links : queue.FreshChildLinks old) (task : Task)
    : (queue.addTask task).FreshChildLinks old := by
  let registered : State := { queue with tasks := queue.tasks ++ [task] }
  let step (current : State) (group : Execution.DeliveryNode) : State :=
    match current.groupNode? group.ref with
    | none => current
    | some node =>
        if node.tasks.contains task.occurrence then current
        else current.putGroupNode
          { node with tasks := node.tasks ++ [task.occurrence], pending := node.pending + 1 }
  have keep (current : State) (group : Execution.DeliveryNode)
      (prior : current.FreshChildLinks old) : (step current group).FreshChildLinks old := by
    unfold step
    split
    · exact prior
    · rename_i node found
      split
      · exact prior
      · exact prior.putGroupNode _ (prior node (List.mem_of_find?_eq_some found))
  have loop (more : List Execution.DeliveryNode) (current : State)
      (prior : current.FreshChildLinks old)
      : (more.foldl step current).FreshChildLinks old := by
    induction more generalizing current with
    | nil => exact prior
    | cons group rest ih => exact ih _ (keep current group prior)
  let current := task.groups.foldl step registered
  have retained := loop task.groups registered links
  change (if task.groups.any (fun group => current.rootGroups.contains group.ref)
      && (current.taskNode? task.occurrence).isNone then
    { current with taskNodes := current.taskNodes ++ [{ task }] }
    else current).FreshChildLinks old
  split <;> exact retained

/-- Stream registration leaves all group records unchanged.
Witness: each stream-registration branch changes only stream or task-node fields.
-/
theorem State.FreshChildLinks.addStreams {queue : State} {old : NodeRefs}
    (links : queue.FreshChildLinks old) (streams : List Stream)
    (parentTask : Option Occurrence)
    : (queue.addStreams streams parentTask).1.FreshChildLinks old := by
  unfold State.addStreams
  split
  · exact links
  · dsimp only
    split <;> exact links

/-- Integrated fresh groups cannot link back into the pre-integration registry.
Witness: group registration establishes the rule; task and stream registration retain it.
-/
theorem State.maybeIntegrateWork_freshChildLinks {queue : State}
    (registered : queue.LiveGroupsRegistered) (work : Work)
    (parentTask : Option Occurrence := none)
    : (queue.maybeIntegrateWork work parentTask).1.FreshChildLinks
        queue.registeredGroups := by
  have loop (more : List Task) (current : State)
      (links : current.FreshChildLinks queue.registeredGroups)
      : (more.foldl State.addTask current).FreshChildLinks queue.registeredGroups := by
    induction more generalizing current with
    | nil => exact links
    | cons task rest ih => exact ih _ (links.addTask task)
  exact (loop work.tasks _
          (queue.addGroups_freshChildLinks registered work.groups)).addStreams
    work.streams parentTask

-----------------------------------------------------------------------------------------
-- Pruning fresh roots cannot erase an old live group
-----------------------------------------------------------------------------------------

/-- A live path from a fresh group remains outside the old registry at its endpoint.
Witness: follow the fresh-child rule edge by edge, including through taskless shells.
-/
theorem State.FreshChildLinks.descendant {queue : State} {old : NodeRefs}
    {root target : Nat} (links : queue.FreshChildLinks old)
    (path : queue.LiveDescendant root target) (fresh : root ∉ old)
    : target ∉ old := by
  induction path with
  | self found => exact fresh
  | child found included below ih =>
      exact ih (links _ (List.mem_of_find?_eq_some found)
        ((State.groupNode?_ref found).symm ▸ fresh) _ included)

/-- Pruning the new integration frontier preserves every old active root's live record.
Witness: fresh paths cannot reach an old registered root. The general outside-subtree
pruning lemma therefore applies even when fresh taskless ancestors are actually removed.
-/
theorem State.RootGroupsPresent.pruneIntegratedWork {queue : State}
    (present : queue.RootGroupsPresent) (registered : queue.LiveGroupsRegistered)
    (work : Work) (parentTask : Option Occurrence := none)
    : let integrated := queue.maybeIntegrateWork work parentTask
      (integrated.1.pruneEmptyGroups integrated.2.newGroups).1.RootGroupsPresent := by
  let integrated := queue.maybeIntegrateWork work parentTask
  change (integrated.1.pruneEmptyGroups integrated.2.newGroups).1.RootGroupsPresent
  intro ref active
  have oldActive : ref ∈ queue.rootGroups := by
    simpa only [integrated, State.pruneEmptyGroups_rootGroups,
      State.maybeIntegrateWork_rootGroups]
      using active
  obtain ⟨node, member, same⟩ := List.mem_map.mp (present ref oldActive)
  have old : ref ∈ queue.registeredGroups := same ▸ registered node member
  apply State.pruneEmptyGroups_preserves_outside
    ((queue.maybeIntegrateWork_includesRefs work parentTask) ref (present ref oldActive))
  intro group included path
  change group ∈ (queue.addGroups work.groups).2 at included
  obtain ⟨_, _, _, _, fresh, _⟩ := queue.addGroups_newGroup_candidate work.groups included
  exact ((queue.maybeIntegrateWork_freshChildLinks registered work parentTask).descendant
    path fresh) old

-----------------------------------------------------------------------------------------
-- Stream-item preparation retains old roots while activating its pruned fresh frontier
-----------------------------------------------------------------------------------------

/-- Integrating an item keeps old roots live and activates only live pruned releases.
Witness: fresh paths exclude all old roots; the pruning contents certificate covers every
new release. This holds for arbitrary finite item work, including taskless wrappers.
-/
theorem State.RootGroupsPresent.integrateStreamItem_registered {queue : State}
    (present : queue.RootGroupsPresent) (registered : queue.LiveGroupsRegistered)
    (refs : queue.GroupRefsUnique) (item : StreamItem)
    (available : List (Occurrence × Nat) := [])
    : (queue.integrateStreamItem item available).RootGroupsPresent := by
  let integrated := queue.maybeIntegrateWork item.work
  let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
  let released := { integrated.2 with newGroups := pruned.2 }
  exact (present.pruneIntegratedWork registered item.work).startNewWork released
    (integrated.1.pruneEmptyGroups_keptPresent integrated.2.newGroups
      (refs.maybeIntegrateWork item.work)) available

/-- Matching item preparation preserves live roots through every integration and pruning.
Witness: iterate registered-root protection with the independent ref and registry laws.
The result is at the leading stream-values carrier, before any recursive draining.
-/
theorem State.RootGroupsPresent.preparedStreamItems {queue : State} {work stream items}
    (present : queue.RootGroupsPresent) (refs : queue.GroupRefsUnique)
    (registered : queue.LiveGroupsRegistered) (_tasks : queue.TaskGroupsRegistered)
    (_matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : (queue.preparedStreamItems items available).RootGroupsPresent := by
  have result := State.preparedStreamItems_preserves
    (fun current => current.GroupRefsUnique ∧ current.LiveGroupsRegistered
      ∧ current.RootGroupsPresent)
    (queue := queue) ⟨refs, registered, present⟩ items available (by
      intro current item _member prior
      let integrated := current.maybeIntegrateWork item.work
      let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
      let released := { integrated.2 with newGroups := pruned.2 }
      exact ⟨((prior.1.maybeIntegrateWork item.work).pruneEmptyGroups
        integrated.2.newGroups).startNewWork released available,
        prior.2.1.integrateStreamItem item available,
        prior.2.2.integrateStreamItem_registered prior.2.1 prior.1 item available⟩)
  exact result.2.2

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
