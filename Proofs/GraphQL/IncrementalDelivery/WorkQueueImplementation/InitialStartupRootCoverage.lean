import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialRootCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialStartupAccounting

/-! Synchronous startup cleanup preserves complete live-group root coverage. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

private theorem rootCoverage_withNotices {queue : State}
    (coverage
      : ∀ target,
          (∃ node, queue.groupNode? target = some node)
          → ∃ root ∈ queue.rootGroups, queue.LiveDescendant root target)
    (groupFailureEvents : List GroupFailureEvent)
    (initialGroups initialStreams : List Execution.DeliveryNode)
    : let next : State := { queue with groupFailureEvents, initialGroups, initialStreams }
      ∀ target,
        (∃ node, next.groupNode? target = some node)
        → ∃ root ∈ next.rootGroups, next.LiveDescendant root target := by
  intro next target survives
  obtain ⟨root, active, covered⟩ := coverage target survives
  exact ⟨root, active, State.LiveDescendant.of_groupNodes_eq (queue := queue) (next := next) rfl covered⟩

/-- Every surviving live initial group lies below an actual initialized root.
Witness: the permanent registry identifies its lowered candidate, complete parent-chain
coverage reaches it before pruning, and the budget-complete pruning theorem transfers
coverage through taskless shells. Activation then installs the covering root.
-/
theorem ExecutedWork.initialStartup_live_group_root_coverage {work : Execution.Work}
    (generated : ExecutedWork work) (startup : InitialStartup)
    : let initial := (State.initialize (Work.fromExecution work) startup)
      ∀ target,
        (∃ node, initial.groupNode? target = some node)
        → ∃ root ∈ initial.rootGroups, initial.LiveDescendant root target := by
  rw [State.initializeWithStartup_eq_preparation]
  dsimp only
  apply rootCoverage_withNotices
    (queue :=
      ((initialPreparation work).1.startNewWork (initialPreparation work).2
        startup.failures).1)
  intro target survives
  let integrated := ({} : State).maybeIntegrateWork (Work.fromExecution work)
  let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
  let released := { integrated.2 with newGroups := pruned.2 }
  let started := (pruned.1.startNewWork released startup.failures).1
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have groupCanonical : ∀ group ∈ (Work.fromExecution work).groups,
      group.parent = (parents group.node.ref).head? :=
    fun _ member => workFromSpec_groups_parentCanonical_root canonical member
  have children : integrated.1.ChildGroupsUnique :=
    State.ChildGroupsUnique.maybeIntegrateWork (by intro node member; cases member) _
  have links : integrated.1.ChildLinksCanonical parents :=
    State.ChildLinksCanonical.maybeIntegrateWork (by intro node member; cases member)
      _ groupCanonical
  have unique : integrated.1.GroupRefsUnique :=
    State.GroupRefsUnique.maybeIntegrateWork (by simp [State.GroupRefsUnique]) _
  have registered := ({} : State).maybeIntegrateWork_registration
    (by intro node member; cases member) (by intro task member; cases member)
    (Work.fromExecution work) (generated.declarations.lower (Located.root (root := work))).contributors
  have origin := ({} : State).maybeIntegrateWork_registeredGroups_subset (Work.fromExecution work)
  have certificate := generated.declarations.lower (Located.root (root := work))
  have descriptors : ∀ candidate ∈ (Work.fromExecution work).groups, ∃ dependencies,
      GroupRecordAt work candidate.node dependencies ∧ candidate.parent = dependencies.head? :=
    fun _ member => workFromSpec_groups_recordAt_root member
  have candidateLive : ∀ group ∈ integrated.2.newGroups,
      ∃ node, integrated.1.groupNode? group.ref = some node := by
    intro group member
    obtain ⟨candidate, included, same, _⟩ :=
      ({} : State).addGroups_newGroup_candidate (Work.fromExecution work).groups member
    have present := ({} : State).maybeIntegrateWork_registersRefs (Work.fromExecution work) none
      generated (by intro node member; cases member) descriptors certificate.parentRefs
      candidate included (generated.empty_registrationSupported _)
    obtain ⟨node, nodeMember, nodeRef⟩ := List.mem_map.mp present
    exact ⟨node, same ▸ nodeRef ▸ unique.groupNode?_of_mem nodeMember⟩
  have frontier : integrated.1.GroupFrontier integrated.2.newGroups := by
    intro child member node nodeMember incoming
    obtain ⟨candidate, included, same, parentless, _⟩ :=
      ({} : State).addGroups_newGroup_candidate (Work.fromExecution work).groups member
    have head := links node nodeMember child.ref incoming
    rw [← same, ← groupCanonical candidate included, parentless] at head
    cases head
  have beforeStart : ∃ node, pruned.1.groupNode? target = some node := by
    change ∃ node, started.groupNode? target = some node at survives
    exact State.groupNode?_exists_before_subset
      (pruned.1.startNewWork_groupNodes_sublist released startup.failures).subset survives
  obtain ⟨node, found⟩ := beforeStart
  have originalMember := (integrated.1.pruneEmptyGroups_groupNodes_sublist
    integrated.2.newGroups).subset (List.mem_of_find?_eq_some found)
  have registeredRef := origin (registered.1 node originalMember)
  obtain ⟨candidate, candidateMember, sameRef⟩ := List.mem_map.mp registeredRef
  obtain ⟨root, candidateRoot, below⟩ := generated.initial_candidate_root_coverage
    candidate candidateMember
  obtain ⟨descriptor, included, descriptorRef⟩ := List.mem_map.mp candidateRoot
  have covered : ∃ root ∈ integrated.2.newGroups, integrated.1.LiveDescendant root.ref target :=
    ⟨descriptor, included, descriptorRef.symm ▸
      (sameRef.trans (State.groupNode?_ref found)) ▸ below⟩
  obtain ⟨root, retained, path⟩ := State.pruneEmptyGroups_surviving_descendant links children
    frontier (State.addGroups_newGroups_unique _ _) candidateLive covered ⟨node, found⟩
  have records : integrated.1.GroupNodesMatchWork work :=
    State.GroupNodesMatchWork.maybeIntegrateWork (by intro node member; cases member) _
      (by
        intro group member
        obtain ⟨dependencies, known, _⟩ := workFromSpec_groups_recordAt_root member
        exact ⟨dependencies, known⟩)
  have forest := State.RemovalForest.of_generated generated children links records canonical
  have prunedForest := forest.of_subset
    (integrated.1.pruneEmptyGroups_groupNodes_sublist integrated.2.newGroups).subset
  obtain ⟨cover, active, covered⟩ := State.startNewWork_root_coverage prunedForest released
    ⟨root.ref, List.mem_append_right _ (List.mem_map_of_mem retained), path⟩ startup.failures
      survives
  exact ⟨cover, active, covered⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
