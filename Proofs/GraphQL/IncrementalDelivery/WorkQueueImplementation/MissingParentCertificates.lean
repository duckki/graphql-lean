import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.AncestorCertificates

/-! Structural missing-parent retirement, independently of failure-cut licensing. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Each live record with an absent, uncancelled parent retains its ancestor-retirement
certificate. `queue` is the actual state; `work` supplies full registration ancestry.
This is an internal replay invariant to prove, not a host-input or scheduler premise.
-/
def State.MissingParentAncestorsRetired (queue : State) (work : Execution.Work) : Prop :=
  ∀ node ∈ queue.groupNodes,
    ∀ parent,
      node.group.parent = some parent
      → queue.groupNode? parent = none
      → parent ∉ queue.cancelledGroups
      → queue.AncestorsRetired work node.group.node.ref

/-- An absent uncancelled ref after failure removal was already absent and uncancelled.
Witness: every filtered-out ref is recorded as cancelled by the same operation. This
needs no generated-work, subtree-coverage, or traversal-budget premise.
-/
theorem State.removeGroup_missing_uncancelled (queue : State) (root parent : Nat)
    (missing : (queue.removeGroup root).groupNode? parent = none)
    (uncancelled : parent ∉ (queue.removeGroup root).cancelledGroups)
    : queue.groupNode? parent = none ∧ parent ∉ queue.cancelledGroups := by
  let removed := State.removeGroup.collect (queue.groupNodes.length + 1) queue [root] []
  have noCancellation : parent ∉ queue.cancelledGroups ++ removed := uncancelled
  have oldUncancelled : parent ∉ queue.cancelledGroups :=
    fun member => noCancellation (List.mem_append_left _ member)
  refine ⟨?_, oldUncancelled⟩
  cases found : queue.groupNode? parent with
  | none => rfl
  | some node =>
      have same := State.groupNode?_ref found
      have notRemoved : parent ∉ removed :=
        fun member => noCancellation (List.mem_append_right _ member)
      have retained : node ∈ (queue.removeGroup root).groupNodes :=
        List.mem_filter.mpr ⟨List.mem_of_find?_eq_some found, by
          change (!removed.contains node.group.node.ref) = true
          simp [same, notRemoved]⟩
      have absent := List.find?_eq_none.mp missing node retained
      exact False.elim (absent (beq_iff_eq.mpr same))

/-- Failure cleanup preserves missing-parent retirement certificates.
Witness: surviving records retain their parents, newly absent refs are cancelled, and
permanent ancestor retirement survives removal.
-/
theorem State.MissingParentAncestorsRetired.removeGroup {queue : State} {work}
    (retired : queue.MissingParentAncestorsRetired work) (root : Nat)
    : (queue.removeGroup root).MissingParentAncestorsRetired work := by
  intro node member parent parentEq missing uncancelled
  have prior := queue.removeGroup_missing_uncancelled root parent missing uncancelled
  exact (retired node (List.mem_filter.mp member).1 parent parentEq prior.1 prior.2).mono
    (fun _ ancestorRetired => ancestorRetired.removeGroup root)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
