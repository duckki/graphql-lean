import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.UncancelledRetirement

/-! Successful group release preserves uncancelled retirement without failure premises. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (ExecutionGroupValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Flush tasks, retire the successful parent, and prune released wrappers
-----------------------------------------------------------------------------------------

/-- Successful closure preserves structurally closed uncancelled retirement.
Witness: task flushing retains certificates, filtering protects the completed parent,
and generated child links carry its certificate through every taskless pruning step.
-/
theorem State.UncancelledRetiredAncestors.finishGroupSuccess {queue : State}
    {work parents} (prior : queue.UncancelledRetiredAncestors work)
    (generated : ExecutedWork work) (matching : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    (registered : queue.LiveGroupsRegistered) {group : GroupNode}
    (member : group ∈ queue.groupNodes)
    (protectedParent : queue.AncestorsRetired work group.group.node.key)
    : (queue.finishGroupSuccess group).1.UncancelledRetiredAncestors work := by
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
    ∧ current.ChildLinksCanonical parents ∧ current.LiveGroupsRegistered
    ∧ current.registeredGroups = queue.registeredGroups
    ∧ current.AncestorsRetired work group.group.node.key
    ∧ current.UncancelledRetiredAncestors work
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
            ?_, invariant.2.2.2.1,
            invariant.2.2.2.2.1.mono (fun _ retired => retired.removeTask occurrence),
            invariant.2.2.2.2.2.removeTask occurrence⟩
          intro node included
          obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp included
          exact invariant.2.2.1 old oldMember
  let flushed := (group.tasks.foldl step (queue, [], [])).1
  have flushedFacts : property flushed := loop group.tasks (queue, [], [])
    ⟨matching, links, registered, rfl, protectedParent, prior⟩
  let current : State := { flushed with
    groupNodes := flushed.groupNodes.filter
      (fun node => node.group.node.key != group.group.node.key)
    rootGroups := flushed.rootGroups.filter (· != group.group.node.key) }
  have currentMatching : current.GroupNodesMatchWork work :=
    fun node included => flushedFacts.1 node (List.mem_filter.mp included).1
  have currentLinks : current.ChildLinksCanonical parents :=
    fun node included => flushedFacts.2.1 node (List.mem_filter.mp included).1
  have currentRegistered : current.LiveGroupsRegistered :=
    fun node included => flushedFacts.2.2.1 node (List.mem_filter.mp included).1
  have closure : current.UncancelledRetiredAncestors work :=
    flushedFacts.2.2.2.2.2.filter_parent flushedFacts.2.2.2.2.1
  have parentRetired : current.RetiredGroup group.group.node.key := by
    apply State.RetiredGroup.of_lookup_none
    · change group.group.node.key ∈ flushed.registeredGroups
      rw [flushedFacts.2.2.2.1]
      exact registered group member
    · apply List.find?_eq_none.mpr
      intro node included
      simpa using (List.mem_filter.mp included).2
  have parentProtected : current.AncestorsRetired work group.group.node.key := by
    apply flushedFacts.2.2.2.2.1.mono
    intro key retired
    refine ⟨retired.1, ?_⟩
    intro live
    obtain ⟨node, included, same⟩ := List.mem_map.mp live
    exact retired.2 (List.mem_map.mpr ⟨node, (List.mem_filter.mp included).1, same⟩)
  obtain ⟨dependencies, parentKnown⟩ := matching group member
  let children := group.childGroups.filterMap
    (fun key => (current.groupNode? key).map (fun node => node.group.node))
  have childProtected : ∀ child ∈ children, current.AncestorsRetired work child.key := by
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
          parentProtected parentRetired
  exact closure.pruneEmptyGroups generated currentMatching currentLinks canonical
    currentRegistered children childProtected

-----------------------------------------------------------------------------------------
-- The recursive drain jointly preserves roots and structural closure
-----------------------------------------------------------------------------------------

/-- Draining ready groups preserves uncancelled retirement using only structural metadata.
Witness: healthy closure installs ancestor certificates before promotion; failure removal
marks new retirements cancelled. The induction threads root certificates and registration.
-/
theorem State.drainReadyGroups_go_uncancelledRetirement {queue : State}
    {work parents} (prior : queue.UncancelledRetiredAncestors work)
    (generated : ExecutedWork work) (matching : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    (live : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (roots : queue.RootAncestorsRetired work) (fuel : Nat)
    : (State.drainReadyGroups.go fuel queue).1.RootAncestorsRetired work
      ∧ (State.drainReadyGroups.go fuel queue).1.UncancelledRetiredAncestors work := by
  let property (current : State) := current.GroupNodesMatchWork work
    ∧ current.ChildLinksCanonical parents ∧ current.LiveGroupsRegistered
    ∧ current.TaskGroupsRegistered ∧ current.RootAncestorsRetired work
    ∧ current.UncancelledRetiredAncestors work
  have result : property (State.drainReadyGroups.go fuel queue).1 := by
    apply State.drainReadyGroups_go_preserves property
      (valid := ⟨matching, links, live, tasks, roots, prior⟩)
    · intro current node invariant member active _ _
      have parentProtected := invariant.2.2.2.2.1 _ active
      have certificates := current.finishGroupSuccess_ancestorsRetired generated
        invariant.1 invariant.2.1 canonical invariant.2.2.1 member parentProtected
      have registered := current.finishGroupSuccess_registration
        invariant.2.2.1 invariant.2.2.2.1 node
      have activated := State.startNewWork_registration registered.1 registered.2.1
        (current.finishGroupSuccess node).2.2
      have closedRoots := invariant.2.2.2.2.1.mono
        (current.finishGroupSuccess_rootsSubset node)
        (fun _ retired => retired.finishGroupSuccess node)
      exact ⟨(invariant.1.finishGroupSuccess node).startNewWork _,
        (invariant.2.1.finishGroupSuccess node).startNewWork _,
        activated.1, activated.2,
        closedRoots.startNewWork _ certificates.2.2,
        (invariant.2.2.2.2.2.finishGroupSuccess generated invariant.1 invariant.2.1
          canonical invariant.2.2.1 member parentProtected).startNewWork _⟩
    · intro current node errors invariant _ _ _
      exact ⟨invariant.1.removeGroup _, invariant.2.1.removeGroup _,
        fun child included => invariant.2.2.1 child (List.mem_filter.mp included).1,
        invariant.2.2.2.1,
        invariant.2.2.2.2.1.mono (current.removeGroup_rootsSubset _)
          (fun _ retired => retired.removeGroup _),
        invariant.2.2.2.2.2.removeGroup _⟩
  exact result.2.2.2.2

/-- The complete drain retains roots and structural retirement at its actual final budget.
Witness: specialize the arbitrary-prefix preservation theorem to the initial group count.
-/
theorem State.drainReadyGroups_uncancelledRetirement {queue : State}
    {work parents} (prior : queue.UncancelledRetiredAncestors work)
    (generated : ExecutedWork work) (matching : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    (live : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (roots : queue.RootAncestorsRetired work)
    : queue.drainReadyGroups.1.RootAncestorsRetired work
      ∧ queue.drainReadyGroups.1.UncancelledRetiredAncestors work :=
  State.drainReadyGroups_go_uncancelledRetirement prior generated matching links canonical
    live tasks roots queue.groupNodes.length

/-- The single-pass contributor fold retains structural retirement closure.
Witness: root certificates justify each successful removal; later decrements preserve
earlier retirements. Metadata and root certificates are threaded through actual states.
-/
theorem successGroupFold_uncancelledRetirement {queue : State} {work parents}
    (prior : queue.UncancelledRetiredAncestors work)
    (generated : ExecutedWork work) (matching : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    (live : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (roots : queue.RootAncestorsRetired work) (groups : List Execution.DeliveryNode)
    : let result := (groups.foldl successGroupStep (queue, [], {})).1
      result.GroupNodesMatchWork work
      ∧ result.ChildLinksCanonical parents
      ∧ result.LiveGroupsRegistered
      ∧ result.TaskGroupsRegistered
      ∧ result.RootAncestorsRetired work
      ∧ result.UncancelledRetiredAncestors work := by
  let property (current : State) := current.GroupNodesMatchWork work
    ∧ current.ChildLinksCanonical parents ∧ current.LiveGroupsRegistered
    ∧ current.TaskGroupsRegistered ∧ current.RootAncestorsRetired work
    ∧ current.UncancelledRetiredAncestors work
  have step (acc : State × List WorkQueueEvent × NewWork) (group : Execution.DeliveryNode)
      (invariant : property acc.1) : property (successGroupStep acc group).1 := by
    obtain ⟨current, events, released⟩ := acc
    dsimp only [successGroupStep]
    split
    · exact invariant
    · rename_i node found
      let updated := { node with pending := node.pending - 1 }
      let next := current.putGroupNode updated
      have member := List.mem_of_find?_eq_some found
      have nextFacts : property next :=
        ⟨invariant.1.putGroupNode _ (invariant.1 node member),
          invariant.2.1.putGroupNode _ (invariant.2.1 node member),
          invariant.2.2.1.putGroupNode _ (invariant.2.2.1 node member),
          invariant.2.2.2.1,
          invariant.2.2.2.2.1.mono (fun _ member => member)
            (fun _ retired => retired.putGroupNode updated),
          invariant.2.2.2.2.2.putGroupNode updated⟩
      split
      · rename_i finishes
        have active : node.group.node.key ∈ next.rootGroups := by
          have flags := Bool.and_eq_true_iff.mp finishes
          simpa only [State.groupNode?_key found, List.contains_iff_mem]
            using (Bool.and_eq_true_iff.mp flags.1).1
        have updatedMember : updated ∈ next.groupNodes :=
          List.mem_map.mpr ⟨node, member, by simp [updated]⟩
        have registered := next.finishGroupSuccess_registration nextFacts.2.2.1
          nextFacts.2.2.2.1 updated
        exact ⟨nextFacts.1.finishGroupSuccess updated,
          nextFacts.2.1.finishGroupSuccess updated, registered.1, registered.2.1,
          nextFacts.2.2.2.2.1.mono (next.finishGroupSuccess_rootsSubset updated)
            (fun _ retired => retired.finishGroupSuccess updated),
          nextFacts.2.2.2.2.2.finishGroupSuccess generated nextFacts.1 nextFacts.2.1
            canonical nextFacts.2.2.1 updatedMember (nextFacts.2.2.2.2.1 _ active)⟩
      · exact nextFacts
  have loop (more : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent × NewWork)
      (invariant : property acc.1) : property (more.foldl successGroupStep acc).1 := by
    induction more generalizing acc with
    | nil => exact invariant
    | cons group rest ih => exact ih _ (step acc group invariant)
  exact loop groups (queue, [], {}) ⟨matching, links, live, tasks, roots, prior⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
