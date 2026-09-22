import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.HealthyContributors

/-! Structural group metadata, independent of failure-removal accounting. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Registered group records retain the primary parent assigned during pure
execution. This says nothing about whether a group is active or connected. -/
def State.GroupParentsCanonical (queue : State) (parents : Nat → Keys) : Prop :=
  ∀ node ∈ queue.groupNodes, node.group.parent = (parents node.group.node.key).head?

/-- A stored child edge points only to a group whose assigned primary parent
is the storing node. The child need not still be live. -/
def State.ChildLinksCanonical (queue : State) (parents : Nat → Keys) : Prop :=
  ∀ node ∈ queue.groupNodes,
  ∀ child ∈ node.childGroups, (parents child).head? = some node.group.node.key

/-- Every registered group is a contributor or ancestor descriptor in the fixed work.
Ancestor-only records need not own any task or have their own `NodeAt` occurrence.
-/
def State.GroupNodesMatchWork (queue : State) (work : Execution.Work) : Prop :=
  ∀ node ∈ queue.groupNodes,
    ∃ dependencies, GroupRecordAt work node.group.node dependencies

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
