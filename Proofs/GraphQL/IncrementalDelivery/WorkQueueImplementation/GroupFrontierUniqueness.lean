import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PrunedFrontierUniqueness
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.IntegrationCandidates
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupPublication

/-! Actual integration and successful-release frontiers have unique group refs. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (ExecutionGroupValue)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Integration begins with distinct parentless candidates, even through taskless shells
-----------------------------------------------------------------------------------------

/-- First-encounter descriptor deduplication produces unique delivery refs.
Witness: the fold appends a ref only when no selected descriptor already has that ref.
-/
theorem distinctDeliveryNodes_refs_nodup (nodes : List Execution.DeliveryNode)
    : ((distinctDeliveryNodes nodes).map Execution.DeliveryNode.ref).Nodup := by
  let step (selected : List Execution.DeliveryNode) (node : Execution.DeliveryNode) :=
    if selected.any (fun known => known.ref == node.ref) then selected else selected ++ [node]
  have loop (more selected : List Execution.DeliveryNode)
      (unique : (selected.map Execution.DeliveryNode.ref).Nodup)
      : ((more.foldl step selected).map Execution.DeliveryNode.ref).Nodup := by
    induction more generalizing selected with
    | nil => exact unique
    | cons node rest ih =>
        apply ih
        dsimp only [step]
        split
        · exact unique
        · rename_i fresh
          rw [List.map_append, List.map_singleton, List.nodup_append]
          refine ⟨unique, by simp, ?_⟩
          intro ref member other included same
          obtain rfl := List.mem_singleton.mp included
          obtain ⟨prior, priorMember, priorRef⟩ := List.mem_map.mp member
          exact fresh (List.any_eq_true.mpr
            ⟨prior, priorMember, beq_iff_eq.mpr (priorRef.trans same)⟩)
  exact loop nodes [] (by simp)

/-- Recursive registration emits each parentless root ref at most once.
Witness: every emitted root is permanently registered, and a later installation can
append a root only while its ref is absent from that growing registry.
-/
theorem State.addGroups_newGroups_unique (queue : State) (groups : List Group)
    : ((queue.addGroups groups).2.map Execution.DeliveryNode.ref).Nodup := by
  let property (acc : State × List Execution.DeliveryNode × NodeRefs) :=
    (acc.2.1.map Execution.DeliveryNode.ref).Nodup
      ∧ acc.2.1.map Execution.DeliveryNode.ref ⊆ acc.1.registeredGroups
  have visit (fuel : Nat) (acc : State × List Execution.DeliveryNode × NodeRefs)
      (group : Group) (prior : property acc)
      : property (State.addGroups.go groups fuel acc group) := by
    induction fuel generalizing acc group with
    | zero => exact prior
    | succ fuel ih =>
        obtain ⟨current, roots, visited⟩ := acc
        simp only [State.addGroups.go]
        split
        · exact prior
        · split
          · exact prior
          · rename_i fresh
            have absent : group.node.ref ∉ current.registeredGroups
                ∧ current.groupNode? group.node.ref = none := by simpa using fresh
            split
            · split
              · have parentless : group.parent = none := by
                  simpa using ‹group.parent.isNone = true›
                have missing : group.node.ref ∉ roots.map Execution.DeliveryNode.ref :=
                  fun member => absent.1 (prior.2 member)
                have registered : (current.addGroup group).registeredGroups
                    = current.registeredGroups ++ [group.node.ref] := by
                  simp [State.addGroup, absent.1, absent.2, parentless]
                refine ⟨?_, ?_⟩
                · simpa [List.map_append, missing] using List.nodup_append.mpr
                    ⟨prior.1, by simp, by
                      intro ref member other included same
                      obtain rfl := List.mem_singleton.mp included
                      exact missing (same ▸ member)⟩
                · rw [registered]
                  intro ref member
                  rw [List.map_append, List.map_singleton] at member
                  exact (List.mem_append.mp member).elim
                    (fun old => List.mem_append_left _ (prior.2 old))
                    (List.mem_append_right _)
              · exact ⟨prior.1,
                  prior.2.trans (current.addGroup_registeredGroups_subset_old group)⟩
            · rename_i parent found
              have reached := ih (current, roots, visited ++ [group.node.ref]) parent prior
              split
              · have parentless : group.parent = none := by
                  simpa using ‹group.parent.isNone = true›
                simp [parentless] at found
              · exact ⟨reached.1, reached.2.trans
                  (State.addGroup_registeredGroups_subset_old _ group)⟩
  have loop (more : List Group) (acc : State × List Execution.DeliveryNode × NodeRefs)
      (prior : property acc)
      : property
          (more.foldl
            (fun acc group => State.addGroups.go groups (groups.length + 1) acc group)
            acc) := by
    induction more generalizing acc with
    | nil => exact prior
    | cons group rest ih => exact ih _ (visit _ acc group prior)
  exact (loop groups (queue, [], []) ⟨by simp, by simp⟩).1

/-- Pruning fresh integrated work produces unique group notice refs.
Witness: recursive installation emits distinct parentless candidates. Canonical links exclude incoming
edges to those candidates, and generic frontier pruning preserves uniqueness while
promoting descendants through taskless shells.
-/
theorem State.maybeIntegrateWork_pruned_unique {queue : State} {parents}
    (links : queue.ChildLinksCanonical parents) (children : queue.ChildGroupsUnique)
    (work : Work)
    (canonical : ∀ group ∈ work.groups, group.parent = (parents group.node.ref).head?)
    (parentTask : Option Occurrence := none)
    : let integrated := queue.maybeIntegrateWork work parentTask
      (((integrated.1.pruneEmptyGroups integrated.2.newGroups).2).map
        Execution.DeliveryNode.ref).Nodup := by
  intro integrated
  have integratedLinks := links.maybeIntegrateWork work canonical parentTask
  apply State.pruneEmptyGroups_unique_frontier integratedLinks
    (children.maybeIntegrateWork work parentTask)
  · intro child candidate parent live incoming
    obtain ⟨group, member, same, parentless, _, _⟩ :=
      queue.addGroups_newGroup_candidate work.groups candidate
    have root : (parents child.ref).head? = none := by
      rw [← same, ← canonical group member, parentless]
    have impossible := integratedLinks parent live child.ref incoming
    rw [root] at impossible
    cases impossible
  · exact State.addGroups_newGroups_unique _ _

-----------------------------------------------------------------------------------------
-- A successful closure removes the only possible parent of its immediate children
-----------------------------------------------------------------------------------------

/-- One successful group release has a duplicate-free group notice list.
Witness: flushing tasks preserves canonical links and unique child lists. Removing the
closing parent makes its looked-up children an incoming-free unique frontier, so pruning
cannot duplicate any promoted descendant, even when several empty shells are traversed.
-/
theorem State.finishGroupSuccess_newGroups_unique {queue : State} {parents}
    (links : queue.ChildLinksCanonical parents) (children : queue.ChildGroupsUnique)
    {group : GroupNode} (present : group ∈ queue.groupNodes)
    : (((queue.finishGroupSuccess group).2.2.newGroups).map
        Execution.DeliveryNode.ref).Nodup := by
  have loop (tasks : List Occurrence) (acc : State × List ExecutionGroupValue × NodeRefs)
      (links : acc.1.ChildLinksCanonical parents) (children : acc.1.ChildGroupsUnique)
      : (tasks.foldl flushGroupTask acc).1.ChildLinksCanonical parents
        ∧ (tasks.foldl flushGroupTask acc).1.ChildGroupsUnique := by
    induction tasks generalizing acc with
    | nil => exact ⟨links, children⟩
    | cons occurrence rest ih =>
        simp only [List.foldl_cons, flushGroupTask]
        split
        · exact ih acc links children
        · exact ih _ (links.removeTask occurrence) (children.removeTask occurrence)
  let flushed := group.tasks.foldl flushGroupTask (queue, [], [])
  obtain ⟨flushedLinks, flushedChildren⟩ := loop group.tasks (queue, [], []) links children
  let current : State := { flushed.1 with
    groupNodes := flushed.1.groupNodes.filter
      (fun node => node.group.node.ref != group.group.node.ref)
    rootGroups := flushed.1.rootGroups.filter (· != group.group.node.ref) }
  let candidates := group.childGroups.filterMap (fun ref =>
    (current.groupNode? ref).map (fun node => node.group.node))
  have currentLinks : current.ChildLinksCanonical parents :=
    fun node member => flushedLinks node (List.mem_filter.mp member).1
  have currentChildren : current.ChildGroupsUnique :=
    fun node member => flushedChildren node (List.mem_filter.mp member).1
  change (((current.pruneEmptyGroups candidates).2).map Execution.DeliveryNode.ref).Nodup
  apply current.pruneEmptyGroups_unique_frontier currentLinks currentChildren
  · intro child candidate parent live incoming
    have parentKnown := links group present child.ref (State.childDescriptors_member candidate).1
    have actual := currentLinks parent live child.ref incoming
    have same : parent.group.node.ref = group.group.node.ref :=
      Option.some.inj (actual.symm.trans parentKnown)
    have different : parent.group.node.ref ≠ group.group.node.ref := by
      simpa only [bne_iff_ne] using (List.mem_filter.mp live).2
    exact different same
  · exact (current.childDescriptors_refs_sublist group.childGroups).nodup (children group present)

-----------------------------------------------------------------------------------------
-- Generated initialization uses the same fresh-integration frontier
-----------------------------------------------------------------------------------------

/-- Generated initialization announces each initial group ref at most once.
Witness: canonical registration parents instantiate fresh-integration pruning from the
empty queue; activation preserves the exact pruned notice list, including empty wrappers.
-/
theorem ExecutedWork.initialGroups_unique {work : Execution.Work}
    (generated : ExecutedWork work)
    : ((State.initialize (Work.fromExecution work)).initialGroups.map
        Execution.DeliveryNode.ref).Nodup := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have links : ({} : State).ChildLinksCanonical parents := by intro node member; cases member
  have children : ({} : State).ChildGroupsUnique := by intro node member; cases member
  exact State.maybeIntegrateWork_pruned_unique links children (Work.fromExecution work)
    (fun _ member => workFromSpec_groups_parentCanonical_root canonical member)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
