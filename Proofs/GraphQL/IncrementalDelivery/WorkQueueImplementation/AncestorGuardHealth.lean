import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.AcceptedFailureHealth
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GeneratedAncestry
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RecordInvalidation

/-! Historical health at an absent, uncancelled parent boundary. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Missing parents require historical evidence, including on rejected child records
-----------------------------------------------------------------------------------------

/-- A live record with an absent, uncancelled parent has healthy defer ancestry.
`failed` is the received object-failure inventory. This proof certificate concerns the
parent's successful retirement, independently of the child's own retained rejections.
Registration descriptors include taskless ancestors; they do not assert task ownership.
-/
def State.MissingParentAncestorsHealthy (queue : State) (work : Execution.Work)
    (failed : List Occurrence)
    : Prop :=
  ∀ node ∈ queue.groupNodes,
    ∀ dependencies,
      GroupRecordAt work node.group.node dependencies
      → ∀ parent,
          node.group.parent = some parent
          → queue.groupNode? parent = none
          → parent ∉ queue.cancelledGroups
          → ∀ ancestor ∈ dependencies, ¬GroupRecordInvalidated work failed ancestor

/-- Before the first accepted failure, every missing-parent boundary is healthy.
Witness: record invalidation always has a failed contributing task at its origin.
-/
theorem State.MissingParentAncestorsHealthy.of_empty (queue : State)
    (work : Execution.Work)
    : queue.MissingParentAncestorsHealthy work [] := by
  intro node member dependencies known parent parentEq missing uncancelled
  intro ancestor inAncestors invalid
  exact invalid.nonempty rfl

/-- Present or recorded-cancelled parents require no absent-parent health proof.
Witness: a successful lookup excludes absence; a cancellation marker excludes the
uncancelled premise. This also covers child-first registration order.
-/
theorem State.MissingParentAncestorsHealthy.of_presentOrCancelledParents {queue : State}
    (work : Execution.Work) (failed : List Occurrence)
    (covered
      : ∀ node ∈ queue.groupNodes,
          ∀ parent,
            node.group.parent = some parent
            → (queue.groupNode? parent).isSome = true ∨ parent ∈ queue.cancelledGroups)
    : queue.MissingParentAncestorsHealthy work failed := by
  intro node member dependencies known parent parentEq missing notCancelled
  rcases covered node member parent parentEq with available | cancelled
  · simp [missing] at available
  · exact False.elim (notCancelled cancelled)

/-- If no live parent link is missing, the stopping-boundary obligation is vacuous.
Witness: specialize the present-or-cancelled parent criterion to existing lookups.
-/
theorem State.MissingParentAncestorsHealthy.of_presentParents {queue : State}
    (work : Execution.Work) (failed : List Occurrence)
    (present
      : ∀ node ∈ queue.groupNodes,
          ∀ parent,
            node.group.parent = some parent → (queue.groupNode? parent).isSome = true)
    : queue.MissingParentAncestorsHealthy work failed := by
  exact .of_presentOrCancelledParents work failed
    (fun node member parent parentEq => Or.inl (present node member parent parentEq))

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
