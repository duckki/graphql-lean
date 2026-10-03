import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ExecutedWork

/-! Causal health of generated groups with a root structural occurrence. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- A root-produced group stays healthy if its contributors and defer ancestors do.
Witness: generated dependency agreement handles ancestor failure, role separation excludes
stream rules, and the root descriptor blocks producer cancellation. No already-admitted
history or publication-support assumption is needed for this fixed causal snapshot.
-/
theorem ExecutedWork.rootProducedGroup_healthy {work : Execution.Work}
    (generated : ExecutedWork work) {node dependencies failed published}
    (known : NodeAt work node .group dependencies none)
    (contributors
      : ∀ occurrence ∈ failed,
          ∀ owners, TaskHasOwners work occurrence owners → node.ref ∉ owners)
    (ancestors : ∀ ref ∈ dependencies, ¬Causality.NodeFailed work failed published ref)
    : ¬Causality.NodeFailed work failed published node.ref := by
  intro failure
  cases failure with
  | task task owner member => exact contributors _ member _ task owner
  | groupDependency descriptor member cause =>
      obtain ⟨other, producer, otherKnown, refEq⟩ := descriptor
      obtain ⟨parents, canonical⟩ := generated.groupDependenciesCanonical
      have same := canonical _ _ _ otherKnown
      rw [refEq, ← canonical _ _ _ known] at same
      exact ancestors _ (same ▸ member) cause
  | streamDependencies descriptor _ _ =>
      obtain ⟨stream, producer, streamKnown, refEq⟩ := descriptor
      exact generated.groupStreamRefsDisjoint known streamKnown refEq.symm
  | producers _ noRoot _ _ =>
      exact noRoot ⟨node, .group, dependencies, known, rfl⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
