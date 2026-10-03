import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupMetadata
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RemovalBasics
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RecordCancellation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.HealthyRegistration

/-! Canonical child edges and cleanup removal of invalidated groups. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Canonical parent metadata of registered groups
-----------------------------------------------------------------------------------------

/-- A child ref cannot be linked from two distinct live parent refs. This
follows directly from the generated primary-parent assignment. -/
private theorem State.ChildLinksCanonical.uniqueParent
    {queue : State} {parents : Nat → NodeRefs}
    (links : queue.ChildLinksCanonical parents)
    {first second : GroupNode} (firstMember : first ∈ queue.groupNodes)
    (secondMember : second ∈ queue.groupNodes)
    {child : Nat} (firstLink : child ∈ first.childGroups)
    (secondLink : child ∈ second.childGroups)
    : first.group.node.ref = second.group.node.ref := by
  have left := links first firstMember child firstLink
  have right := links second secondMember child secondLink
  rw [right] at left
  exact Option.some.inj left.symm

/-- A linked, live child's stored parent agrees with its linking group. -/
private theorem State.ChildLinksCanonical.liveChildParent
    {queue : State} {parents : Nat → NodeRefs}
    (links : queue.ChildLinksCanonical parents)
    (canonical : queue.GroupParentsCanonical parents)
    {parent child : GroupNode}
    (parentMember : parent ∈ queue.groupNodes)
    (childMember : child ∈ queue.groupNodes)
    (linked : child.group.node.ref ∈ parent.childGroups)
    : child.group.parent = some parent.group.node.ref := by
  rw [canonical child childMember]
  exact links parent parentMember child.group.node.ref linked

/-- A live child record inherits invalidation along a canonical queue edge.
Witness: the edge is an actual registration dependency, including taskless wrappers.
-/
private theorem State.ChildLinksCanonical.childFailed
    {queue : State} {work : Execution.Work} {parents : Nat → NodeRefs}
    {failed : List Occurrence}
    (links : queue.ChildLinksCanonical parents)
    (matching : queue.GroupNodesMatchWork work)
    (workCanonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    {parent child : GroupNode}
    (parentMember : parent ∈ queue.groupNodes)
    (childMember : child ∈ queue.groupNodes)
    (linked : child.group.node.ref ∈ parent.childGroups)
    (parentFailed : GroupRecordInvalidated work failed parent.group.node.ref)
    : GroupRecordInvalidated work failed child.group.node.ref := by
  obtain ⟨dependencies, known⟩ := matching child childMember
  have head : dependencies.head? = some parent.group.node.ref := by
    rw [workCanonical child.group.node dependencies known]
    exact links parent parentMember child.group.node.ref linked
  have member : parent.group.node.ref ∈ dependencies := by
    cases dependencies with
    | nil => simp at head
    | cons first rest =>
        have firstEq : first = parent.group.node.ref := by
          simpa using Option.some.inj head
        subst first
        simp
  exact .ancestor known member parentFailed

/-- Proof-only name for the finite descendant-ref collection embedded in
`State.removeGroup`. It reuses the implementation's collector without duplicating
the traversal or adding executable queue state.
-/
private def State.collectedRemovalRefs (queue : State) (ref : NodeRef) : NodeRefs :=
  State.removeGroup.collect (queue.groupNodes.length + 1) queue [ref] []

/-- Any finite prefix of missing child refs is skipped without spending live-node fuel.
Witness: induction on the stale prefix using the implementation's missing-ref equation.
No generated-work or acyclicity assumption is needed for this traversal property.
-/
theorem State.removeGroup_collect_skipMissing
    (fuel : Nat) (queue : State) (missing pending removed : NodeRefs)
    (absent : ∀ ref ∈ missing, queue.groupNode? ref = none)
    : State.removeGroup.collect fuel queue (missing ++ pending) removed
      = State.removeGroup.collect fuel queue pending removed := by
  cases fuel with
  | zero => simp only [State.removeGroup.collect]
  | succ fuel =>
      induction missing with
      | nil => rfl
      | cons ref rest ih =>
          simp only [List.cons_append, State.removeGroup.collect,
            absent ref (by simp)]
          exact ih (fun child member => absent child (by simp [member]))

/-- Removing all stale refs from the pending frontier leaves the collected result
unchanged, including stale refs interleaved with live ones. Witness: induction on the
live-node budget and frontier, followed by the same statement for child frontiers.
-/
theorem State.removeGroup_collect_filterPresent
    (fuel : Nat) (queue : State) (pending removed : NodeRefs)
    : State.removeGroup.collect fuel queue pending removed
      = State.removeGroup.collect fuel queue
          (pending.filter (fun ref => (queue.groupNode? ref).isSome)) removed := by
  induction fuel generalizing pending removed with
  | zero => simp only [State.removeGroup.collect]
  | succ fuel ih =>
      induction pending generalizing removed with
      | nil => simp only [List.filter_nil]
      | cons ref rest tailIH =>
          cases found : queue.groupNode? ref with
          | none =>
              simpa only [List.filter_cons, State.removeGroup.collect, found,
                Option.isSome_none, Bool.false_eq_true, ↓reduceIte] using tailIH removed
          | some node =>
              simp only [List.filter_cons, State.removeGroup.collect, found,
                Option.isSome_some, ↓reduceIte]
              rw [ih (node.childGroups ++ rest) (ref :: removed),
                ih (node.childGroups ++ rest.filter
                  (fun next => (queue.groupNode? next).isSome)) (ref :: removed)]
              simp only [List.filter_append, List.filter_filter, Bool.and_self]

/-- The proof-side ref collector names exactly the implementation's local
recursive calculation for live group nodes. -/
private theorem State.removeGroup_groupNodes_eq (queue : State) (ref : NodeRef)
    : (queue.removeGroup ref).groupNodes
      = queue.groupNodes.filter
          (fun node =>
            !((queue.collectedRemovalRefs ref).contains node.group.node.ref)) :=
  rfl

/-- The same collected ref set controls active-root removal. -/
private theorem State.removeGroup_rootGroups_eq (queue : State) (ref : NodeRef)
    : (queue.removeGroup ref).rootGroups
      = queue.rootGroups.filter
          (fun root => !((queue.collectedRemovalRefs ref).contains root)) :=
  rfl

/-- Once a ref has entered the finite removal accumulator, all later
collector steps retain it. -/
private theorem State.collectedRemovalRefs_retains
    (fuel : Nat) (queue : State) (pending removed : NodeRefs)
    : removed.Subset (State.removeGroup.collect fuel queue pending removed) :=
  State.removeGroup_collect_retains fuel queue pending removed

/-- A found group always enters its own recursive-removal ref set. -/
private theorem State.collectedRemovalRefs_containsRoot
    (queue : State) (ref : NodeRef) (node : GroupNode)
    (found : queue.groupNode? ref = some node)
    : ref ∈ queue.collectedRemovalRefs ref := by
  change ref ∈ State.removeGroup.collect
    (queue.groupNodes.length + 1) queue [ref] []
  simp only [State.removeGroup.collect, found]
  have retained := State.collectedRemovalRefs_retains queue.groupNodes.length queue
    node.childGroups [ref]
  simpa only [List.append_nil] using retained (show ref ∈ ([ref] : NodeRefs) by simp)

/-- Removing a found group ref removes that ref from active roots too. -/
theorem State.removeGroup_rootAbsent
    (queue : State) (ref : NodeRef) (node : GroupNode)
    (found : queue.groupNode? ref = some node)
    : ref ∉ (queue.removeGroup ref).rootGroups := by
  intro member
  rw [queue.removeGroup_rootGroups_eq] at member
  have retained := (List.mem_filter.mp member).2
  have notCollected : ref ∉ queue.collectedRemovalRefs ref := by
    simpa using retained
  exact notCollected (queue.collectedRemovalRefs_containsRoot ref node found)

/-- Every collected ref has a failed-task cause through real registration ancestry.
Witness: induction follows canonical child links through contributor and taskless records.
-/
private theorem State.collectedRemovalRefs_failed
    {queue : State} {work : Execution.Work} {parents : Nat → NodeRefs}
    {failed : List Occurrence}
    (links : queue.ChildLinksCanonical parents)
    (matching : queue.GroupNodesMatchWork work)
    (workCanonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (ref : NodeRef) (rootFailed : GroupRecordInvalidated work failed ref)
    : ∀ node ∈ queue.groupNodes,
        node.group.node.ref ∈ queue.collectedRemovalRefs ref
        → GroupRecordInvalidated work failed node.group.node.ref := by
  have loop (fuel : Nat) (pending removed : NodeRefs)
      (pendingFailed : ∀ ref ∈ pending,
        ∀ node ∈ queue.groupNodes,
          node.group.node.ref = ref → GroupRecordInvalidated work failed ref)
      (removedFailed : ∀ ref ∈ removed,
        GroupRecordInvalidated work failed ref)
      : ∀ node ∈ queue.groupNodes,
          node.group.node.ref ∈
            State.removeGroup.collect fuel queue pending removed
          → GroupRecordInvalidated work failed node.group.node.ref := by
    induction fuel generalizing pending removed with
    | zero =>
        intro node _ member
        simp only [State.removeGroup.collect] at member
        exact removedFailed node.group.node.ref member
    | succ fuel ih =>
        induction pending generalizing removed with
        | nil =>
            intro node _ member
            simp only [State.removeGroup.collect] at member
            exact removedFailed node.group.node.ref member
        | cons head rest tailIH =>
            unfold State.removeGroup.collect
            cases found : queue.groupNode? head with
            | none =>
                apply tailIH removed
                · intro candidate member node nodeMember same
                  exact pendingFailed candidate (by simp [member])
                    node nodeMember same
                · exact removedFailed
            | some parent =>
                have parentMember : parent ∈ queue.groupNodes :=
                  List.mem_of_find?_eq_some found
                have parentRef : parent.group.node.ref = head :=
                  queue.groupNode?_ref found
                have parentFailed : GroupRecordInvalidated work failed
                    parent.group.node.ref := by
                  rw [parentRef]
                  exact pendingFailed head (by simp) parent parentMember parentRef
                have nextPending : ∀ candidate ∈ parent.childGroups ++ rest,
                    ∀ node ∈ queue.groupNodes,
                      node.group.node.ref = candidate
                      → GroupRecordInvalidated work failed candidate := by
                  intro candidate member node nodeMember same
                  rcases List.mem_append.mp member with child | tail
                  · have linked : node.group.node.ref ∈ parent.childGroups := by
                      rw [same]
                      exact child
                    have failure := links.childFailed matching workCanonical
                      parentMember nodeMember linked parentFailed
                    rw [same] at failure
                    exact failure
                  · exact pendingFailed candidate (by simp [tail])
                      node nodeMember same
                have nextRemoved : ∀ candidate ∈ head :: removed,
                    GroupRecordInvalidated work failed candidate := by
                  intro candidate member
                  rcases List.mem_cons.mp member with same | tail
                  · subst candidate
                    rw [← parentRef]
                    exact parentFailed
                  · exact removedFailed candidate tail
                exact ih (parent.childGroups ++ rest) (head :: removed)
                  nextPending nextRemoved
  intro node nodeMember member
  change node.group.node.ref ∈ State.removeGroup.collect
    (queue.groupNodes.length + 1) queue [ref] [] at member
  exact loop
    (queue.groupNodes.length + 1)
    [ref] []
    (by intro candidate member node _ same
        have equal : candidate = ref := List.mem_singleton.mp member
        exact equal ▸ rootFailed)
    (by intro candidate member; cases member)
    node nodeMember member

/-- Recursive cleanup retains every live record with no registration-invalidation cause.
Witness: removal provenance contradicts record health for any selected ref.
-/
theorem State.removeGroup_recordHealthyRetained
    {queue : State} {work : Execution.Work} {parents : Nat → NodeRefs}
    {failed : List Occurrence}
    (links : queue.ChildLinksCanonical parents)
    (matching : queue.GroupNodesMatchWork work)
    (workCanonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (ref : NodeRef) (rootFailed : GroupRecordInvalidated work failed ref)
    : ∀ node ∈ queue.groupNodes,
        ¬GroupRecordInvalidated work failed node.group.node.ref
        → node ∈ (queue.removeGroup ref).groupNodes := by
  intro node nodeMember healthy
  have notCollected : node.group.node.ref ∉ queue.collectedRemovalRefs ref := by
    intro member
    exact healthy (queue.collectedRemovalRefs_failed links matching
      workCanonical ref rootFailed node nodeMember member)
  rw [queue.removeGroup_groupNodes_eq]
  exact List.mem_filter.mpr ⟨nodeMember, by simp [notCollected]⟩

/-- Cleanup retains every healthy actual contributor of generated work.
Witness: record removal provenance and contributor invalidation are equivalent at its
`NodeAt` descriptor. Ancestor-only records are covered by the separate record theorem.
-/
theorem State.removeGroup_healthyRetained
    {queue : State} {work : Execution.Work} {parents : Nat → NodeRefs}
    {failed : List Occurrence}
    (generated : ExecutedWork work)
    (links : queue.ChildLinksCanonical parents)
    (matching : queue.GroupNodesMatchWork work)
    (workCanonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (ref : NodeRef) (rootFailed : GroupRecordInvalidated work failed ref)
    {node : GroupNode} (member : node ∈ queue.groupNodes)
    {dependencies producer}
    (known : NodeAt work node.group.node .group dependencies producer)
    (healthy : ¬GroupInvalidated work failed node.group.node.ref)
    : node ∈ (queue.removeGroup ref).groupNodes :=
  queue.removeGroup_recordHealthyRetained links matching workCanonical ref rootFailed node
    member
    (fun failure =>
      healthy ((generated.groupRecordInvalidated_iff_groupInvalidated known).mp failure))

-----------------------------------------------------------------------------------------
-- Failure removal records only causally invalidated cancellation refs
-----------------------------------------------------------------------------------------

/-- Removing an invalidated record preserves cancellation provenance for all descendants.
Witness: every newly recorded ref came from a live record reached through canonical edges;
the removal-causality theorem supplies its record-invalidation witness.
-/
theorem State.CancelledRecordsSupported.removeGroup
    {queue : State} {work : Execution.Work} {parents : Nat → NodeRefs}
    {failed : List Occurrence} (supported : queue.CancelledRecordsSupported work failed)
    (links : queue.ChildLinksCanonical parents)
    (matching : queue.GroupNodesMatchWork work)
    (workCanonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (ref : NodeRef) (rootFailed : GroupRecordInvalidated work failed ref)
    : (queue.removeGroup ref).CancelledRecordsSupported work failed := by
  intro cancelled member
  change cancelled ∈ queue.cancelledGroups ++ queue.collectedRemovalRefs ref at member
  rcases List.mem_append.mp member with old | added
  · exact supported cancelled old
  · have live := State.removeGroup_collect_mem (queue.groupNodes.length + 1) queue [ref] []
      added
    rcases live with impossible | ⟨node, member, same⟩
    · cases impossible
    · rw [← same] at added ⊢
      exact queue.collectedRemovalRefs_failed links matching workCanonical ref rootFailed
        node member added

-----------------------------------------------------------------------------------------
-- Registered-task accounting uses actual contributors, not every live record
-----------------------------------------------------------------------------------------

/-- Record-aware removal preserves actual registered tasks' healthy contributor nodes.
Witness: exact task provenance supplies contributor descriptors; record cleanup agrees
with original invalidation at those descriptors, regardless of intervening wrappers.
-/
theorem State.HealthyRegisteredTaskAccounting.removeInvalidatedGroup
    {queue work parents settled failed}
    (accounted : State.HealthyRegisteredTaskAccounting queue work settled failed)
    (taskMatching : queue.RegisteredTasksMatch work)
    (generated : ExecutedWork work)
    (links : queue.ChildLinksCanonical parents)
    (matching : queue.GroupNodesMatchWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (ref : NodeRef) (invalid : GroupRecordInvalidated work failed ref)
    : (queue.removeGroup ref).HealthyRegisteredTaskAccounting work settled failed := by
  intro task member fresh contributor owner healthy
  obtain ⟨node, nodeMember, same, linked⟩ := accounted task member fresh contributor owner healthy
  obtain ⟨group, groupMember, groupRef⟩ := List.mem_map.mp owner
  obtain ⟨dependencies, producer, known⟩ :=
    (taskMatching task member).contributorsLocated groupMember
  have recordHealthy : ¬GroupRecordInvalidated work failed node.group.node.ref := by
    intro failure
    have contributorFailure : GroupRecordInvalidated work failed group.ref := by
      rwa [groupRef, ← same]
    have cause := (generated.groupRecordInvalidated_iff_groupInvalidated known).mp
      contributorFailure
    exact healthy (groupRef ▸ cause)
  exact ⟨node, queue.removeGroup_recordHealthyRetained links matching canonical ref
    invalid node nodeMember recordHealthy, same, linked⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
