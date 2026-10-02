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

/-- A child key cannot be linked from two distinct live parent keys. This
follows directly from the generated primary-parent assignment. -/
private theorem State.ChildLinksCanonical.uniqueParent
    {queue : State} {parents : Nat → Keys}
    (links : queue.ChildLinksCanonical parents)
    {first second : GroupNode} (firstMember : first ∈ queue.groupNodes)
    (secondMember : second ∈ queue.groupNodes)
    {child : Nat} (firstLink : child ∈ first.childGroups)
    (secondLink : child ∈ second.childGroups)
    : first.group.node.key = second.group.node.key := by
  have left := links first firstMember child firstLink
  have right := links second secondMember child secondLink
  rw [right] at left
  exact Option.some.inj left.symm

/-- A linked, live child's stored parent agrees with its linking group. -/
private theorem State.ChildLinksCanonical.liveChildParent
    {queue : State} {parents : Nat → Keys}
    (links : queue.ChildLinksCanonical parents)
    (canonical : queue.GroupParentsCanonical parents)
    {parent child : GroupNode}
    (parentMember : parent ∈ queue.groupNodes)
    (childMember : child ∈ queue.groupNodes)
    (linked : child.group.node.key ∈ parent.childGroups)
    : child.group.parent = some parent.group.node.key := by
  rw [canonical child childMember]
  exact links parent parentMember child.group.node.key linked

/-- A live child record inherits invalidation along a canonical queue edge.
Witness: the edge is an actual registration dependency, including taskless wrappers.
-/
private theorem State.ChildLinksCanonical.childFailed
    {queue : State} {work : Execution.Work} {parents : Nat → Keys}
    {failed : List Occurrence}
    (links : queue.ChildLinksCanonical parents)
    (matching : queue.GroupNodesMatchWork work)
    (workCanonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    {parent child : GroupNode}
    (parentMember : parent ∈ queue.groupNodes)
    (childMember : child ∈ queue.groupNodes)
    (linked : child.group.node.key ∈ parent.childGroups)
    (parentFailed : GroupRecordInvalidated work failed parent.group.node.key)
    : GroupRecordInvalidated work failed child.group.node.key := by
  obtain ⟨dependencies, known⟩ := matching child childMember
  have head : dependencies.head? = some parent.group.node.key := by
    rw [workCanonical child.group.node dependencies known]
    exact links parent parentMember child.group.node.key linked
  have member : parent.group.node.key ∈ dependencies := by
    cases dependencies with
    | nil => simp at head
    | cons first rest =>
        have firstEq : first = parent.group.node.key := by
          simpa using Option.some.inj head
        subst first
        simp
  exact .ancestor known member parentFailed

/-- Proof-only name for the finite descendant-key collection embedded in
`State.removeGroup`. It reuses the implementation's collector without duplicating
the traversal or adding executable queue state.
-/
private def State.collectedRemovalKeys (queue : State) (key : Nat) : Keys :=
  State.removeGroup.collect (queue.groupNodes.length + 1) queue [key] []

/-- Any finite prefix of missing child keys is skipped without spending live-node fuel.
Witness: induction on the stale prefix using the implementation's missing-key equation.
No generated-work or acyclicity assumption is needed for this traversal property.
-/
theorem State.removeGroup_collect_skipMissing
    (fuel : Nat) (queue : State) (missing pending removed : Keys)
    (absent : ∀ key ∈ missing, queue.groupNode? key = none)
    : State.removeGroup.collect fuel queue (missing ++ pending) removed
      = State.removeGroup.collect fuel queue pending removed := by
  cases fuel with
  | zero => simp only [State.removeGroup.collect]
  | succ fuel =>
      induction missing with
      | nil => rfl
      | cons key rest ih =>
          simp only [List.cons_append, State.removeGroup.collect,
            absent key (by simp)]
          exact ih (fun child member => absent child (by simp [member]))

/-- Removing all stale keys from the pending frontier leaves the collected result
unchanged, including stale keys interleaved with live ones. Witness: induction on the
live-node budget and frontier, followed by the same statement for child frontiers.
-/
theorem State.removeGroup_collect_filterPresent
    (fuel : Nat) (queue : State) (pending removed : Keys)
    : State.removeGroup.collect fuel queue pending removed
      = State.removeGroup.collect fuel queue
          (pending.filter (fun key => (queue.groupNode? key).isSome)) removed := by
  induction fuel generalizing pending removed with
  | zero => simp only [State.removeGroup.collect]
  | succ fuel ih =>
      induction pending generalizing removed with
      | nil => simp only [List.filter_nil]
      | cons key rest tailIH =>
          cases found : queue.groupNode? key with
          | none =>
              simpa only [List.filter_cons, State.removeGroup.collect, found,
                Option.isSome_none, Bool.false_eq_true, ↓reduceIte] using tailIH removed
          | some node =>
              simp only [List.filter_cons, State.removeGroup.collect, found,
                Option.isSome_some, ↓reduceIte]
              rw [ih (node.childGroups ++ rest) (key :: removed),
                ih (node.childGroups ++ rest.filter
                  (fun next => (queue.groupNode? next).isSome)) (key :: removed)]
              simp only [List.filter_append, List.filter_filter, Bool.and_self]

/-- The proof-side key collector names exactly the implementation's local
recursive calculation for live group nodes. -/
private theorem State.removeGroup_groupNodes_eq (queue : State) (key : Nat)
    : (queue.removeGroup key).groupNodes
      = queue.groupNodes.filter
          (fun node =>
            !((queue.collectedRemovalKeys key).contains node.group.node.key)) :=
  rfl

/-- The same collected key set controls active-root removal. -/
private theorem State.removeGroup_rootGroups_eq (queue : State) (key : Nat)
    : (queue.removeGroup key).rootGroups
      = queue.rootGroups.filter
          (fun root => !((queue.collectedRemovalKeys key).contains root)) :=
  rfl

/-- Once a key has entered the finite removal accumulator, all later
collector steps retain it. -/
private theorem State.collectedRemovalKeys_retains
    (fuel : Nat) (queue : State) (pending removed : Keys)
    : removed.Subset (State.removeGroup.collect fuel queue pending removed) :=
  State.removeGroup_collect_retains fuel queue pending removed

/-- A found group always enters its own recursive-removal key set. -/
private theorem State.collectedRemovalKeys_containsRoot
    (queue : State) (key : Nat) (node : GroupNode)
    (found : queue.groupNode? key = some node)
    : key ∈ queue.collectedRemovalKeys key := by
  change key ∈ State.removeGroup.collect
    (queue.groupNodes.length + 1) queue [key] []
  simp only [State.removeGroup.collect, found]
  have retained := State.collectedRemovalKeys_retains queue.groupNodes.length queue
    node.childGroups [key]
  simpa only [List.append_nil] using retained (show key ∈ ([key] : Keys) by simp)

/-- Removing a found group key removes that key from active roots too. -/
theorem State.removeGroup_rootAbsent
    (queue : State) (key : Nat) (node : GroupNode)
    (found : queue.groupNode? key = some node)
    : key ∉ (queue.removeGroup key).rootGroups := by
  intro member
  rw [queue.removeGroup_rootGroups_eq] at member
  have retained := (List.mem_filter.mp member).2
  have notCollected : key ∉ queue.collectedRemovalKeys key := by
    simpa using retained
  exact notCollected (queue.collectedRemovalKeys_containsRoot key node found)

/-- Every collected key has a failed-task cause through real registration ancestry.
Witness: induction follows canonical child links through contributor and taskless records.
-/
private theorem State.collectedRemovalKeys_failed
    {queue : State} {work : Execution.Work} {parents : Nat → Keys}
    {failed : List Occurrence}
    (links : queue.ChildLinksCanonical parents)
    (matching : queue.GroupNodesMatchWork work)
    (workCanonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    (key : Nat) (rootFailed : GroupRecordInvalidated work failed key)
    : ∀ node ∈ queue.groupNodes,
        node.group.node.key ∈ queue.collectedRemovalKeys key
        → GroupRecordInvalidated work failed node.group.node.key := by
  have loop (fuel : Nat) (pending removed : Keys)
      (pendingFailed : ∀ key ∈ pending,
        ∀ node ∈ queue.groupNodes,
          node.group.node.key = key → GroupRecordInvalidated work failed key)
      (removedFailed : ∀ key ∈ removed,
        GroupRecordInvalidated work failed key)
      : ∀ node ∈ queue.groupNodes,
          node.group.node.key ∈
            State.removeGroup.collect fuel queue pending removed
          → GroupRecordInvalidated work failed node.group.node.key := by
    induction fuel generalizing pending removed with
    | zero =>
        intro node _ member
        simp only [State.removeGroup.collect] at member
        exact removedFailed node.group.node.key member
    | succ fuel ih =>
        induction pending generalizing removed with
        | nil =>
            intro node _ member
            simp only [State.removeGroup.collect] at member
            exact removedFailed node.group.node.key member
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
                have parentKey : parent.group.node.key = head :=
                  queue.groupNode?_key found
                have parentFailed : GroupRecordInvalidated work failed
                    parent.group.node.key := by
                  rw [parentKey]
                  exact pendingFailed head (by simp) parent parentMember parentKey
                have nextPending : ∀ candidate ∈ parent.childGroups ++ rest,
                    ∀ node ∈ queue.groupNodes,
                      node.group.node.key = candidate
                      → GroupRecordInvalidated work failed candidate := by
                  intro candidate member node nodeMember same
                  rcases List.mem_append.mp member with child | tail
                  · have linked : node.group.node.key ∈ parent.childGroups := by
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
                    rw [← parentKey]
                    exact parentFailed
                  · exact removedFailed candidate tail
                exact ih (parent.childGroups ++ rest) (head :: removed)
                  nextPending nextRemoved
  intro node nodeMember member
  change node.group.node.key ∈ State.removeGroup.collect
    (queue.groupNodes.length + 1) queue [key] [] at member
  exact loop
    (queue.groupNodes.length + 1)
    [key] []
    (by intro candidate member node _ same
        have equal : candidate = key := List.mem_singleton.mp member
        exact equal ▸ rootFailed)
    (by intro candidate member; cases member)
    node nodeMember member

/-- Recursive cleanup retains every live record with no registration-invalidation cause.
Witness: removal provenance contradicts record health for any selected key.
-/
theorem State.removeGroup_recordHealthyRetained
    {queue : State} {work : Execution.Work} {parents : Nat → Keys}
    {failed : List Occurrence}
    (links : queue.ChildLinksCanonical parents)
    (matching : queue.GroupNodesMatchWork work)
    (workCanonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    (key : Nat) (rootFailed : GroupRecordInvalidated work failed key)
    : ∀ node ∈ queue.groupNodes,
        ¬GroupRecordInvalidated work failed node.group.node.key
        → node ∈ (queue.removeGroup key).groupNodes := by
  intro node nodeMember healthy
  have notCollected : node.group.node.key ∉ queue.collectedRemovalKeys key := by
    intro member
    exact healthy (queue.collectedRemovalKeys_failed links matching
      workCanonical key rootFailed node nodeMember member)
  rw [queue.removeGroup_groupNodes_eq]
  exact List.mem_filter.mpr ⟨nodeMember, by simp [notCollected]⟩

/-- Cleanup retains every healthy actual contributor of generated work.
Witness: record removal provenance and contributor invalidation are equivalent at its
`NodeAt` descriptor. Ancestor-only records are covered by the separate record theorem.
-/
theorem State.removeGroup_healthyRetained
    {queue : State} {work : Execution.Work} {parents : Nat → Keys}
    {failed : List Occurrence}
    (generated : ExecutedWork work)
    (links : queue.ChildLinksCanonical parents)
    (matching : queue.GroupNodesMatchWork work)
    (workCanonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    (key : Nat) (rootFailed : GroupRecordInvalidated work failed key)
    {node : GroupNode} (member : node ∈ queue.groupNodes)
    {dependencies producer}
    (known : NodeAt work node.group.node .group dependencies producer)
    (healthy : ¬GroupInvalidated work failed node.group.node.key)
    : node ∈ (queue.removeGroup key).groupNodes :=
  queue.removeGroup_recordHealthyRetained links matching workCanonical key rootFailed node
    member
    (fun failure =>
      healthy ((generated.groupRecordInvalidated_iff_groupInvalidated known).mp failure))

-----------------------------------------------------------------------------------------
-- Failure removal records only causally invalidated cancellation keys
-----------------------------------------------------------------------------------------

/-- Removing an invalidated record preserves cancellation provenance for all descendants.
Witness: every newly recorded key came from a live record reached through canonical edges;
the removal-causality theorem supplies its record-invalidation witness.
-/
theorem State.CancelledRecordsSupported.removeGroup
    {queue : State} {work : Execution.Work} {parents : Nat → Keys}
    {failed : List Occurrence} (supported : queue.CancelledRecordsSupported work failed)
    (links : queue.ChildLinksCanonical parents)
    (matching : queue.GroupNodesMatchWork work)
    (workCanonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    (key : Nat) (rootFailed : GroupRecordInvalidated work failed key)
    : (queue.removeGroup key).CancelledRecordsSupported work failed := by
  intro cancelled member
  change cancelled ∈ queue.cancelledGroups ++ queue.collectedRemovalKeys key at member
  rcases List.mem_append.mp member with old | added
  · exact supported cancelled old
  · have live := State.removeGroup_collect_mem (queue.groupNodes.length + 1) queue [key] []
      added
    rcases live with impossible | ⟨node, member, same⟩
    · cases impossible
    · rw [← same] at added ⊢
      exact queue.collectedRemovalKeys_failed links matching workCanonical key rootFailed
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
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    (key : Nat) (invalid : GroupRecordInvalidated work failed key)
    : (queue.removeGroup key).HealthyRegisteredTaskAccounting work settled failed := by
  intro task member fresh contributor owner healthy
  obtain ⟨node, nodeMember, same, linked⟩ := accounted task member fresh contributor owner healthy
  obtain ⟨group, groupMember, groupKey⟩ := List.mem_map.mp owner
  obtain ⟨dependencies, producer, known⟩ :=
    (taskMatching task member).contributorsLocated groupMember
  have recordHealthy : ¬GroupRecordInvalidated work failed node.group.node.key := by
    intro failure
    have contributorFailure : GroupRecordInvalidated work failed group.key := by
      rwa [groupKey, ← same]
    have cause := (generated.groupRecordInvalidated_iff_groupInvalidated known).mp
      contributorFailure
    exact healthy (groupKey ▸ cause)
  exact ⟨node, queue.removeGroup_recordHealthyRetained links matching canonical key
    invalid node nodeMember recordHealthy, same, linked⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
