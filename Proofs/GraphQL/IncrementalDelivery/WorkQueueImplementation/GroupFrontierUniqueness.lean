import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PrunedFrontierUniqueness
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.IntegrationCandidates
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupPublication

/-! Actual integration and successful-release frontiers have unique group keys. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (ExecutionGroupValue)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Integration begins with distinct parentless candidates, even through taskless shells
-----------------------------------------------------------------------------------------

/-- First-encounter descriptor deduplication produces unique delivery keys.
Witness: the fold appends a key only when no selected descriptor already has that key.
-/
theorem distinctDeliveryNodes_keys_nodup (nodes : List Execution.DeliveryNode)
    : ((distinctDeliveryNodes nodes).map Execution.DeliveryNode.key).Nodup := by
  let step (selected : List Execution.DeliveryNode) (node : Execution.DeliveryNode) :=
    if selected.any (fun known => known.key == node.key) then selected else selected ++ [node]
  have loop (more selected : List Execution.DeliveryNode)
      (unique : (selected.map Execution.DeliveryNode.key).Nodup)
      : ((more.foldl step selected).map Execution.DeliveryNode.key).Nodup := by
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
          intro key member other included same
          obtain rfl := List.mem_singleton.mp included
          obtain ⟨prior, priorMember, priorKey⟩ := List.mem_map.mp member
          exact fresh (List.any_eq_true.mpr
            ⟨prior, priorMember, beq_iff_eq.mpr (priorKey.trans same)⟩)
  exact loop nodes [] (by simp)

/-- Pruning fresh integrated work produces unique group notice keys.
Witness: integration deduplicates parentless candidates. Canonical links exclude incoming
edges to those candidates, and generic frontier pruning preserves uniqueness while
promoting descendants through taskless shells.
-/
theorem State.maybeIntegrateWork_pruned_unique {queue : State} {parents}
    (links : queue.ChildLinksCanonical parents) (children : queue.ChildGroupsUnique)
    (work : Work)
    (canonical : ∀ group ∈ work.groups, group.parent = (parents group.node.key).head?)
    (parentTask : Option Occurrence := none)
    : let integrated := queue.maybeIntegrateWork work parentTask
      (((integrated.1.pruneEmptyGroups integrated.2.newGroups).2).map
        Execution.DeliveryNode.key).Nodup := by
  intro integrated
  have integratedLinks := links.maybeIntegrateWork work canonical parentTask
  apply State.pruneEmptyGroups_unique_frontier integratedLinks
    (children.maybeIntegrateWork work parentTask)
  · intro child candidate parent live incoming
    obtain ⟨group, member, same, parentless, _, _⟩ :=
      queue.addGroups_newGroup_candidate work.groups candidate
    have root : (parents child.key).head? = none := by
      rw [← same, ← canonical group member, parentless]
    have impossible := integratedLinks parent live child.key incoming
    rw [root] at impossible
    cases impossible
  · exact distinctDeliveryNodes_keys_nodup _

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
        Execution.DeliveryNode.key).Nodup := by
  have loop (tasks : List Occurrence) (acc : State × List ExecutionGroupValue × Keys)
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
      (fun node => node.group.node.key != group.group.node.key)
    rootGroups := flushed.1.rootGroups.filter (· != group.group.node.key) }
  let candidates := group.childGroups.filterMap (fun key =>
    (current.groupNode? key).map (fun node => node.group.node))
  have currentLinks : current.ChildLinksCanonical parents :=
    fun node member => flushedLinks node (List.mem_filter.mp member).1
  have currentChildren : current.ChildGroupsUnique :=
    fun node member => flushedChildren node (List.mem_filter.mp member).1
  change (((current.pruneEmptyGroups candidates).2).map Execution.DeliveryNode.key).Nodup
  apply current.pruneEmptyGroups_unique_frontier currentLinks currentChildren
  · intro child candidate parent live incoming
    have parentKnown := links group present child.key (State.childDescriptors_member candidate).1
    have actual := currentLinks parent live child.key incoming
    have same : parent.group.node.key = group.group.node.key :=
      Option.some.inj (actual.symm.trans parentKnown)
    have different : parent.group.node.key ≠ group.group.node.key := by
      simpa only [bne_iff_ne] using (List.mem_filter.mp live).2
    exact different same
  · exact (current.childDescriptors_keys_sublist group.childGroups).nodup (children group present)

-----------------------------------------------------------------------------------------
-- Generated initialization uses the same fresh-integration frontier
-----------------------------------------------------------------------------------------

/-- Generated initialization announces each initial group key at most once.
Witness: canonical registration parents instantiate fresh-integration pruning from the
empty queue; activation preserves the exact pruned notice list, including empty wrappers.
-/
theorem ExecutedWork.initialGroups_unique {work : Execution.Work}
    (generated : ExecutedWork work)
    : ((State.initialize (Work.fromExecution work)).initialGroups.map
        Execution.DeliveryNode.key).Nodup := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have links : ({} : State).ChildLinksCanonical parents := by intro node member; cases member
  have children : ({} : State).ChildGroupsUnique := by intro node member; cases member
  exact State.maybeIntegrateWork_pruned_unique links children (Work.fromExecution work)
    (fun _ member => workFromSpec_groups_parentCanonical Located.root canonical member)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
