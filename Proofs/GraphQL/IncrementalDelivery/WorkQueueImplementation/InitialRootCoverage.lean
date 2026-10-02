import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CandidateRootCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PruningBudget

/-! Generated initialization places every surviving live group below an announced root. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Integration's permanent registry contains only earlier or explicitly supplied keys
-----------------------------------------------------------------------------------------

/-- Complete work integration registers only earlier keys or supplied group candidates.
Witness: task and stream installation leave the group registration pass's registry unchanged.
-/
theorem State.maybeIntegrateWork_registeredGroups_subset (queue : State) (work : Work)
    (parentTask : Option Occurrence := none)
    : (queue.maybeIntegrateWork work parentTask).1.registeredGroups.Subset
        (queue.registeredGroups ++ work.groups.map (fun group => group.node.key)) := by
  have loop (more : List Task) (current : State)
      : (more.foldl State.addTask current).registeredGroups
        = current.registeredGroups := by
    induction more generalizing current with
    | nil => rfl
    | cons task rest ih => rw [List.foldl_cons, ih, State.addTask_registeredGroups]
  have same : (queue.maybeIntegrateWork work parentTask).1.registeredGroups
      = (queue.addGroups work.groups).1.registeredGroups := by
    change ((work.tasks.foldl State.addTask (queue.addGroups work.groups).1).addStreams
      work.streams parentTask).1.registeredGroups = _
    unfold State.addStreams
    split
    · exact loop _ _
    · dsimp only
      split <;> exact loop _ _
  rw [same]
  exact queue.addGroups_registeredGroups_subset work.groups

-----------------------------------------------------------------------------------------
-- Empty-state lowering has complete live chains before taskless pruning
-----------------------------------------------------------------------------------------

/-- Every generated initial candidate is below a parentless candidate before pruning.
Witness: empty registration cannot cancel work, lowering supplies complete parent chains,
and generated metadata gives the strictly increasing concrete parent forest.
-/
theorem ExecutedWork.initial_candidate_root_coverage {work : Execution.Work}
    (generated : ExecutedWork work)
    : let integrated := ({} : State).maybeIntegrateWork (Work.fromExecution work)
      ∀ group ∈ (Work.fromExecution work).groups,
        ∃ root ∈ integrated.2.newGroups.map Execution.DeliveryNode.key,
          integrated.1.LiveDescendant root group.node.key := by
  intro integrated
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have groupCanonical : ∀ group ∈ (Work.fromExecution work).groups,
      group.parent = (parents group.node.key).head? :=
    fun _ member => workFromSpec_groups_parentCanonical Located.root canonical member
  have emptyLinks : ({} : State).ParentLinksComplete parents := by
    intro node member
    cases member
  have complete := emptyLinks.maybeIntegrateWork (by simp [State.GroupKeysUnique])
    (by intro node member; cases member) (by intro key member; cases member)
    (Work.fromExecution work) groupCanonical
  have children : integrated.1.ChildGroupsUnique :=
    State.ChildGroupsUnique.maybeIntegrateWork (by intro node member; cases member) _
  have links : integrated.1.ChildLinksCanonical parents :=
    State.ChildLinksCanonical.maybeIntegrateWork (by intro node member; cases member)
      _ groupCanonical
  have records : integrated.1.GroupNodesMatchWork work :=
    State.GroupNodesMatchWork.maybeIntegrateWork (by intro node member; cases member) _
      (by
        intro group member
        obtain ⟨dependencies, known, _⟩ := workFromSpec_groups_recordAt Located.root member
        exact ⟨dependencies, known⟩)
  have forest := State.RemovalForest.of_generated generated children links records canonical
  have unique : integrated.1.GroupKeysUnique :=
    State.GroupKeysUnique.maybeIntegrateWork (by simp [State.GroupKeysUnique]) _
  have live : ∀ group ∈ (Work.fromExecution work).groups,
      ∃ node, integrated.1.groupNode? group.node.key = some node := by
    intro group member
    have present := ({} : State).maybeIntegrateWork_registersKeys (Work.fromExecution work) none
      group member (.inr (by simp)) (by rw [State.addGroups_cancelledGroups_empty rfl]; simp)
    obtain ⟨node, nodeMember, same⟩ := List.mem_map.mp present
    exact ⟨node, same ▸ unique.groupNode?_of_mem nodeMember⟩
  intro group member
  apply complete.candidates_root_coverage forest (Work.fromExecution work).groups
    (integrated.2.newGroups.map Execution.DeliveryNode.key) groupCanonical
    (workFromSpec_parentsCovered work) live
  · intro candidate included parentless
    exact ({} : State).addGroups_parentless_candidate _ included parentless (by simp) rfl
  · exact member

-----------------------------------------------------------------------------------------
-- Complete pruning transfers candidate coverage to actual initial announced roots
-----------------------------------------------------------------------------------------

/-- Every surviving live initial group lies below an actual initialized root.
Witness: the permanent registry identifies its lowered candidate, complete parent-chain
coverage reaches it before pruning, and the budget-complete pruning theorem transfers
coverage through taskless shells. Activation then installs the covering root.
-/
theorem ExecutedWork.initial_live_group_root_coverage {work : Execution.Work}
    (generated : ExecutedWork work)
    : let initial := State.initialize (Work.fromExecution work)
      ∀ target,
        (∃ node, initial.groupNode? target = some node)
        → ∃ root ∈ initial.rootGroups, initial.LiveDescendant root target := by
  intro initial target survives
  let integrated := ({} : State).maybeIntegrateWork (Work.fromExecution work)
  let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
  let released := { integrated.2 with newGroups := pruned.2 }
  let started := pruned.1.startNewWork released
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have groupCanonical : ∀ group ∈ (Work.fromExecution work).groups,
      group.parent = (parents group.node.key).head? :=
    fun _ member => workFromSpec_groups_parentCanonical Located.root canonical member
  have children : integrated.1.ChildGroupsUnique :=
    State.ChildGroupsUnique.maybeIntegrateWork (by intro node member; cases member) _
  have links : integrated.1.ChildLinksCanonical parents :=
    State.ChildLinksCanonical.maybeIntegrateWork (by intro node member; cases member)
      _ groupCanonical
  have unique : integrated.1.GroupKeysUnique :=
    State.GroupKeysUnique.maybeIntegrateWork (by simp [State.GroupKeysUnique]) _
  have registered := ({} : State).maybeIntegrateWork_registration
    (by intro node member; cases member) (by intro task member; cases member)
    (Work.fromExecution work) (workFromSpec_immediateGroupsCoverTasks work [])
  have origin := ({} : State).maybeIntegrateWork_registeredGroups_subset (Work.fromExecution work)
  have candidateLive : ∀ group ∈ integrated.2.newGroups,
      ∃ node, integrated.1.groupNode? group.key = some node := by
    intro group member
    obtain ⟨candidate, included, same, _⟩ :=
      ({} : State).addGroups_newGroup_candidate (Work.fromExecution work).groups member
    have present := ({} : State).maybeIntegrateWork_registersKeys (Work.fromExecution work) none
      candidate included (.inr (by simp))
      (by rw [State.addGroups_cancelledGroups_empty rfl]; simp)
    obtain ⟨node, nodeMember, nodeKey⟩ := List.mem_map.mp present
    exact ⟨node, same ▸ nodeKey ▸ unique.groupNode?_of_mem nodeMember⟩
  have frontier : integrated.1.GroupFrontier integrated.2.newGroups := by
    intro child member node nodeMember incoming
    obtain ⟨candidate, included, same, parentless, _⟩ :=
      ({} : State).addGroups_newGroup_candidate (Work.fromExecution work).groups member
    have head := links node nodeMember child.key incoming
    rw [← same, ← groupCanonical candidate included, parentless] at head
    cases head
  have beforeStart : ∃ node, pruned.1.groupNode? target = some node := by
    change ∃ node, started.groupNode? target = some node at survives
    simpa only [started, State.groupNode?, (State.startNewWork_groupCore _ _).1] using survives
  obtain ⟨node, found⟩ := beforeStart
  have originalMember := (integrated.1.pruneEmptyGroups_groupNodes_sublist
    integrated.2.newGroups).subset (List.mem_of_find?_eq_some found)
  have registeredKey := origin (registered.1 node originalMember)
  obtain ⟨candidate, candidateMember, sameKey⟩ := List.mem_map.mp registeredKey
  obtain ⟨root, candidateRoot, below⟩ := generated.initial_candidate_root_coverage
    candidate candidateMember
  obtain ⟨descriptor, included, descriptorKey⟩ := List.mem_map.mp candidateRoot
  have covered : ∃ root ∈ integrated.2.newGroups, integrated.1.LiveDescendant root.key target :=
    ⟨descriptor, included, descriptorKey.symm ▸
      (sameKey.trans (State.groupNode?_key found)) ▸ below⟩
  obtain ⟨root, retained, path⟩ := State.pruneEmptyGroups_surviving_descendant links children
    frontier (distinctDeliveryNodes_keys_nodup _) candidateLive covered ⟨node, found⟩
  refine ⟨root.key, ?_, ?_⟩
  · change root.key ∈ started.rootGroups
    rw [(pruned.1.startNewWork_groupCore released).2.2]
    exact List.mem_append_right _ (List.mem_map_of_mem retained)
  · apply State.LiveDescendant.of_groupNodes_eq (queue := pruned.1) (path := path)
    exact (pruned.1.startNewWork_groupCore released).1

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
