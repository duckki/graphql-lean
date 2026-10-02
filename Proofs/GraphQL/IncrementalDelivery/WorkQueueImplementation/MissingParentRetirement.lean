import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RetiredAncestorHealth
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.AncestorRelease

/-! Missing-parent retirement across successful removal and taskless pruning. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (ExecutionGroupValue)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Present or cancelled parents make the missing-parent retirement condition vacuous.
Witness: a successful lookup or retained cancellation contradicts the accepting boundary.
-/
theorem State.MissingParentAncestorsRetired.of_presentOrCancelledParents {queue : State}
    (work : Execution.Work)
    (covered
      : ∀ node ∈ queue.groupNodes,
          ∀ parent,
            node.group.parent = some parent
            → (queue.groupNode? parent).isSome = true ∨ parent ∈ queue.cancelledGroups)
    : queue.MissingParentAncestorsRetired work := by
  intro node member parent parentEq missing uncancelled
  rcases covered node member parent parentEq with present | cancelled
  · simp [missing] at present
  · exact False.elim (uncancelled cancelled)

-----------------------------------------------------------------------------------------
-- Removing a successful parent installs the child's retirement certificate
-----------------------------------------------------------------------------------------

/-- Filtering a protected parent preserves missing-parent retirement for every survivor.
Witness: an old missing parent uses its old certificate; a newly missing parent uses
the removed record's full ancestry and new permanent retirement. Canonical parent fields
identify the chain, without assuming the child occurs in the removed parent's link list.
-/
theorem State.MissingParentAncestorsRetired.filter_parent {queue : State} {work parents}
    (prior : queue.MissingParentAncestorsRetired work)
    (generated : ExecutedWork work) (matching : queue.GroupNodesMatchWork work)
    (parentFields : queue.GroupParentsCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    {removed : Execution.DeliveryNode} {parentDependencies}
    (parentKnown : GroupRecordAt work removed parentDependencies)
    (registered : removed.key ∈ queue.registeredGroups)
    (protectedParent : queue.AncestorsRetired work removed.key)
    : ({
        queue with
          groupNodes :=
            queue.groupNodes.filter (fun node => node.group.node.key != removed.key)
      }).MissingParentAncestorsRetired
        work := by
  let next : State := { queue with
    groupNodes := queue.groupNodes.filter
      (fun node => node.group.node.key != removed.key) }
  have preserves (key) (retired : queue.RetiredGroup key) : next.RetiredGroup key := by
    refine ⟨retired.1, ?_⟩
    intro live
    obtain ⟨node, included, same⟩ := List.mem_map.mp live
    exact retired.2 (List.mem_map.mpr ⟨node, (List.mem_filter.mp included).1, same⟩)
  intro node included parent parentEq missing uncancelled
  have oldMember := (List.mem_filter.mp included).1
  by_cases same : parent = removed.key
  · have retired : next.RetiredGroup removed.key := by
      apply State.RetiredGroup.of_lookup_none (queue := next) registered
      apply List.find?_eq_none.mpr
      intro candidate kept
      simpa using (List.mem_filter.mp kept).2
    obtain ⟨dependencies, known⟩ := matching node oldMember
    have head : dependencies.head? = some removed.key := by
      rw [canonical _ _ known, ← parentFields node oldMember, parentEq, same]
    exact State.AncestorsRetired.child generated known parentKnown head
      (protectedParent.mono preserves) retired
  · have wasMissing : queue.groupNode? parent = none := by
      cases found : queue.groupNode? parent with
      | none => rfl
      | some old =>
          have key := State.groupNode?_key found
          have retained : old ∈ next.groupNodes :=
            List.mem_filter.mpr ⟨List.mem_of_find?_eq_some found, by simp [key, same]⟩
          exact False.elim
            (List.find?_eq_none.mp missing old retained (beq_iff_eq.mpr key))
    exact (prior node oldMember parent parentEq wasMissing uncancelled).mono preserves

-----------------------------------------------------------------------------------------
-- The actual pruning traversal may create several successive missing parents
-----------------------------------------------------------------------------------------

/-- Taskless pruning preserves missing-parent retirement throughout its traversal.
Witness: the shared retirement traversal threads canonical parent fields and applies
the single-parent removal theorem at every protected candidate, including wrappers.
-/
theorem State.MissingParentAncestorsRetired.pruneEmptyGroups {queue : State}
    {work parents} (prior : queue.MissingParentAncestorsRetired work)
    (generated : ExecutedWork work) (matching : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (parentFields : queue.GroupParentsCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    (registered : queue.LiveGroupsRegistered) (groups : List Execution.DeliveryNode)
    (protectedGroups : ∀ group ∈ groups, queue.AncestorsRetired work group.key)
    : (queue.pruneEmptyGroups groups).1.MissingParentAncestorsRetired work := by
  have preserved := queue.pruneEmptyGroups_retirement_preserves generated matching links
    canonical registered groups protectedGroups
    (fun current => current.GroupParentsCanonical parents
      ∧ current.MissingParentAncestorsRetired work) (by
        intro current node matched _ recorded member protectedParent invariant
        obtain ⟨dependencies, record⟩ := matched node member
        exact ⟨fun candidate kept => invariant.1 candidate (List.mem_filter.mp kept).1,
          invariant.2.filter_parent generated matched invariant.1 canonical
            record (recorded node member) protectedParent⟩)
  exact (preserved.2 ⟨parentFields, prior⟩).2

-----------------------------------------------------------------------------------------
-- Task flushing and activation do not change parent relationships
-----------------------------------------------------------------------------------------

/-- Missing lookup is exactly absence from the live key list.
Witness: unfold the first-match lookup and its Boolean key equality.
-/
theorem State.groupNode?_eq_none_iff (queue : State) (key : Nat)
    : queue.groupNode? key = none
      ↔ key ∉ queue.groupNodes.map (fun node => node.group.node.key) := by
  constructor
  · intro absent member
    obtain ⟨node, live, same⟩ := List.mem_map.mp member
    exact List.find?_eq_none.mp absent node live (beq_iff_eq.mpr same)
  · intro absent
    apply List.find?_eq_none.mpr
    intro node member equal
    exact absent (List.mem_map.mpr ⟨node, member, beq_iff_eq.mp equal⟩)

/-- Missing-parent retirement depends only on group descriptors and permanent registries.
Witness: equal descriptor lists give equal live keys and old parent records; registry
equality transports each permanent ancestor retirement. Task and root fields are unused.
-/
theorem State.MissingParentAncestorsRetired.of_sameRecords {before after : State} {work}
    (prior : before.MissingParentAncestorsRetired work)
    (groups
      : after.groupNodes.map GroupNode.group = before.groupNodes.map GroupNode.group)
    (registered : after.registeredGroups = before.registeredGroups)
    (cancelled : after.cancelledGroups = before.cancelledGroups)
    : after.MissingParentAncestorsRetired work := by
  have keys : after.groupNodes.map (fun node => node.group.node.key)
      = before.groupNodes.map (fun node => node.group.node.key) := by
    have same := congrArg (List.map (fun group : Group => group.node.key)) groups
    simpa only [List.map_map, Function.comp_def] using same
  intro node member parent parentEq missing uncancelled
  have descriptor : node.group ∈ before.groupNodes.map GroupNode.group := by
    rw [← groups]
    exact List.mem_map_of_mem member
  obtain ⟨old, oldMember, same⟩ := List.mem_map.mp descriptor
  have wasMissing : before.groupNode? parent = none := by
    rw [State.groupNode?_eq_none_iff] at missing ⊢
    rwa [keys] at missing
  rw [cancelled] at uncancelled
  have certificate := prior old oldMember parent (same.symm ▸ parentEq) wasMissing uncancelled
  rw [same] at certificate
  exact certificate.mono
    (by
      intro key retired
      exact ⟨registered.symm ▸ retired.1, keys.symm ▸ retired.2⟩)

/-- Removing task memberships preserves every missing-parent retirement boundary.
Witness: group descriptors, live keys, and cancellation markers stay unchanged, while
permanent retirement survives the bookkeeping update.
-/
theorem State.MissingParentAncestorsRetired.removeTask {queue : State} {work}
    (prior : queue.MissingParentAncestorsRetired work) (occurrence : Occurrence)
    : (queue.removeTask occurrence).MissingParentAncestorsRetired work := by
  intro node member parent parentEq missing uncancelled
  obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
  have wasMissing : queue.groupNode? parent = none := by
    rw [State.groupNode?_eq_none_iff] at missing ⊢
    simpa only [State.removeTask, List.map_map, Function.comp_def] using missing
  exact (prior old oldMember parent parentEq wasMissing uncancelled).mono
    (fun _ retired => retired.removeTask occurrence)

/-- Activating released work preserves missing-parent retirement certificates.
Witness: activation leaves live group records and cancellation markers unchanged.
-/
theorem State.MissingParentAncestorsRetired.startNewWork {queue : State} {work}
    (prior : queue.MissingParentAncestorsRetired work) (released : NewWork)
    : (queue.startNewWork released).MissingParentAncestorsRetired work := by
  intro node member parent parentEq missing uncancelled
  rw [(queue.startNewWork_groupCore released).1] at member
  have wasMissing : queue.groupNode? parent = none := by
    simpa only [State.groupNode?, (queue.startNewWork_groupCore released).1] using missing
  rw [State.startNewWork_cancelledGroups] at uncancelled
  exact (prior node member parent parentEq wasMissing uncancelled).mono
    (fun _ retired => retired.startNewWork released)

-----------------------------------------------------------------------------------------
-- Full success closure flushes tasks, retires the parent, and prunes released children
-----------------------------------------------------------------------------------------

/-- Successful group closure preserves missing-parent retirement, including children
promoted through taskless wrappers. Witness: thread structural metadata through task
flushing, install the removed parent's certificate, then apply pruning preservation.
-/
theorem State.MissingParentAncestorsRetired.finishGroupSuccess {queue : State}
    {work parents} (prior : queue.MissingParentAncestorsRetired work)
    (generated : ExecutedWork work) (matching : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (parentFields : queue.GroupParentsCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    (registered : queue.LiveGroupsRegistered) {group : GroupNode}
    (member : group ∈ queue.groupNodes)
    (protectedParent : queue.AncestorsRetired work group.group.node.key)
    : (queue.finishGroupSuccess group).1.MissingParentAncestorsRetired work := by
  let step (acc : State × List ExecutionGroupValue × Keys) (occurrence : Occurrence) :=
    let (current, values, streams) := acc
    match current.taskNode? occurrence with
    | none => (current, values, streams)
    | some taskNode =>
        let values := match taskNode.value with
          | none => values
          | some value => values ++ [value]
        (current.removeTask occurrence, values, streams ++ taskNode.childStreams)
  let property (current : State) := current.GroupNodesMatchWork work
    ∧ current.ChildLinksCanonical parents ∧ current.GroupParentsCanonical parents
    ∧ current.LiveGroupsRegistered ∧ current.registeredGroups = queue.registeredGroups
    ∧ current.AncestorsRetired work group.group.node.key
    ∧ current.MissingParentAncestorsRetired work
  have loop (more : List Occurrence) (acc : State × List ExecutionGroupValue × Keys)
      (invariant : property acc.1) : property (more.foldl step acc).1 := by
    induction more generalizing acc with
    | nil => exact invariant
    | cons occurrence rest ih =>
        apply ih
        obtain ⟨current, values, streams⟩ := acc
        dsimp only [step]
        split
        · exact invariant
        · refine ⟨invariant.1.removeTask occurrence, invariant.2.1.removeTask occurrence,
            invariant.2.2.1.removeTask occurrence, ?_, invariant.2.2.2.2.1,
            invariant.2.2.2.2.2.1.mono (fun _ retired => retired.removeTask occurrence),
            invariant.2.2.2.2.2.2.removeTask occurrence⟩
          intro node included
          obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp included
          exact invariant.2.2.2.1 old oldMember
  let flushed := (group.tasks.foldl step (queue, [], [])).1
  have metadata : property flushed := loop group.tasks (queue, [], [])
    ⟨matching, links, parentFields, registered, rfl, protectedParent, prior⟩
  let current : State := { flushed with
    groupNodes := flushed.groupNodes.filter
      (fun node => node.group.node.key != group.group.node.key)
    rootGroups := flushed.rootGroups.filter (· != group.group.node.key) }
  obtain ⟨dependencies, parentKnown⟩ := matching group member
  have parentRegistered : group.group.node.key ∈ flushed.registeredGroups := by
    rw [metadata.2.2.2.2.1]
    exact registered group member
  have currentMissing : current.MissingParentAncestorsRetired work :=
    metadata.2.2.2.2.2.2.filter_parent generated metadata.1 metadata.2.2.1 canonical
      parentKnown parentRegistered metadata.2.2.2.2.2.1
  have preserves (key) (retired : flushed.RetiredGroup key) : current.RetiredGroup key := by
    refine ⟨retired.1, ?_⟩
    intro live
    obtain ⟨node, kept, same⟩ := List.mem_map.mp live
    exact retired.2 (List.mem_map.mpr ⟨node, (List.mem_filter.mp kept).1, same⟩)
  have retired : current.RetiredGroup group.group.node.key := by
    apply State.RetiredGroup.of_lookup_none (queue := current) parentRegistered
    apply List.find?_eq_none.mpr
    intro node kept
    simpa using (List.mem_filter.mp kept).2
  have currentMatching : current.GroupNodesMatchWork work :=
    fun node kept => metadata.1 node (List.mem_filter.mp kept).1
  have currentLinks : current.ChildLinksCanonical parents :=
    fun node kept => metadata.2.1 node (List.mem_filter.mp kept).1
  have currentParents : current.GroupParentsCanonical parents :=
    fun node kept => metadata.2.2.1 node (List.mem_filter.mp kept).1
  have currentRegistered : current.LiveGroupsRegistered :=
    fun node kept => metadata.2.2.2.1 node (List.mem_filter.mp kept).1
  let children := group.childGroups.filterMap
    (fun key => (current.groupNode? key).map (fun node => node.group.node))
  have protectedChildren : ∀ child ∈ children, current.AncestorsRetired work child.key := by
    intro child included
    obtain ⟨key, linked, selected⟩ := List.mem_filterMap.mp included
    cases found : current.groupNode? key with
    | none => simp [found] at selected
    | some node =>
        have same : node.group.node = child := by simpa [found] using selected
        obtain ⟨childDependencies, childKnown⟩ :=
          currentMatching node (List.mem_of_find?_eq_some found)
        have head : childDependencies.head? = some group.group.node.key := by
          rw [canonical _ _ childKnown, State.groupNode?_key found]
          exact links group member key linked
        exact same ▸ State.AncestorsRetired.child generated childKnown parentKnown head
          (metadata.2.2.2.2.2.1.mono preserves) retired
  exact currentMissing.pruneEmptyGroups generated currentMatching currentLinks
    currentParents canonical currentRegistered children protectedChildren

/-- Recursive draining preserves missing-parent retirement across both closure kinds.
Witness: successful closure protects every released child before activation; failure
removal marks newly missing parents as cancelled. The joint induction retains root
certificates and structural metadata, without a failure-health or admission premise.
-/
theorem State.MissingParentAncestorsRetired.drainReadyGroups {queue : State}
    {work parents} (prior : queue.MissingParentAncestorsRetired work)
    (generated : ExecutedWork work) (matching : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (parentFields : queue.GroupParentsCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    (registered : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (roots : queue.RootAncestorsRetired work)
    : queue.drainReadyGroups.1.MissingParentAncestorsRetired work := by
  let property (current : State) := current.MissingParentAncestorsRetired work
    ∧ current.RootAncestorsRetired work ∧ current.GroupNodesMatchWork work
    ∧ current.ChildLinksCanonical parents ∧ current.GroupParentsCanonical parents
    ∧ current.LiveGroupsRegistered ∧ current.TaskGroupsRegistered
  have preserved := State.drainReadyGroups_preserves property (by
    intro current node invariant member active _ _
    obtain ⟨boundary, protectedRoots, matched, linked, fields, live, covered⟩ := invariant
    have protectedParent := protectedRoots _ active
    have closed := State.finishGroupSuccess_ancestorsRetired generated matched linked
      canonical live member protectedParent
    have registration := State.finishGroupSuccess_registration live covered node
    have released := State.startNewWork_registration registration.1 registration.2.1
      (current.finishGroupSuccess node).2.2
    exact ⟨
      (boundary.finishGroupSuccess generated matched linked fields canonical
        live member protectedParent).startNewWork _,
      (protectedRoots.mono (current.finishGroupSuccess_rootsSubset node)
        (fun _ retired => retired.finishGroupSuccess node)).startNewWork _ closed.2.2,
      (matched.finishGroupSuccess node).startNewWork _,
      (linked.finishGroupSuccess node).startNewWork _,
      (fields.finishGroupSuccess node).startNewWork _,
      released.1, released.2⟩) (by
    intro current node errors invariant _ _ _
    obtain ⟨boundary, protectedRoots, matched, linked, fields, live, covered⟩ := invariant
    exact ⟨boundary.removeGroup _,
      protectedRoots.mono (current.removeGroup_rootsSubset node.group.node.key)
        (fun _ retired => retired.removeGroup _),
      matched.removeGroup _, linked.removeGroup _, fields.removeGroup _,
      (fun candidate member => live candidate (List.mem_filter.mp member).1), covered⟩)
    ⟨prior, roots, matching, links, parentFields, registered, tasks⟩
  exact preserved.1

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
