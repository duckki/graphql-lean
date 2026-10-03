import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupPruningNotices
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GeneratedAncestry

/-! Notice dependency readiness propagates through the actual taskless-shell traversal. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- A promoted child's full ancestry is the removed parent followed by its ready ancestry
-----------------------------------------------------------------------------------------

/-- Pruning preserves dependency readiness when each traversed empty shell is accounted for.
Witness: generated registration metadata identifies every live child edge's full ancestor
chain. Initial candidates have ready ancestors; crossing an empty, error-free shell adds
only that shell's own readiness. Taskless ancestor records need no fabricated `NodeAt`.
The empty-shell accounting premise is a local proof obligation, not a new scheduler law.
-/
theorem State.pruneEmptyGroups_dependenciesReady
    {queue : State} {work initial matching events failures parents}
    (generated : ExecutedWork work) (records : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (emptyReady
      : ∀ node ∈ queue.groupNodes,
          (∀ ref ∈ parents node.group.node.ref,
            DependencySatisfied work initial matching events failures ref)
          → node.tasks = []
          → node.failure = none
          → DependencySatisfied work initial matching events failures node.group.node.ref)
    (groups : List Execution.DeliveryNode)
    (candidates
      : ∀ group ∈ groups,
        ∀ ref ∈ parents group.ref,
          DependencySatisfied work initial matching events failures ref)
    {child dependencies producer}
    (noticed : child ∈ (queue.pruneEmptyGroups groups).2)
    (known : NodeAt work child .group dependencies producer)
    : ∀ ref ∈ dependencies,
        DependencySatisfied work initial matching events failures ref := by
  have ready := queue.pruneEmptyGroups_inheritedNoticeProperty
    (property := fun ref => ∀ ancestor ∈ parents ref,
      DependencySatisfied work initial matching events failures ancestor)
    (groups := groups) (candidates := candidates) (inherited := by
      intro node member ancestors noTasks noFailure child childMember childLink
      obtain ⟨nodeDependencies, nodeKnown⟩ := records node member
      obtain ⟨childDependencies, childKnown⟩ := records child childMember
      have head : childDependencies.head? = some node.group.node.ref := by
        rw [canonical _ _ childKnown]
        exact links node member child.group.node.ref childLink
      have chain := generated.groupRecordAncestryChain childKnown nodeKnown head
      rw [canonical _ _ childKnown, canonical _ _ nodeKnown] at chain
      rw [chain]
      intro ref included
      rcases List.mem_cons.mp included with same | earlier
      · exact same ▸ emptyReady node member ancestors noTasks noFailure
      · exact ancestors ref earlier)
    child noticed
  rw [canonical _ _ (groupRecordAt_of_nodeAt known)]
  exact ready

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
