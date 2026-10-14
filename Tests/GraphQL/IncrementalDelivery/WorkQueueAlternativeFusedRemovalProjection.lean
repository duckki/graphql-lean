import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedRemovalProjection

/-! Full actual-state removal projection, trusted-axiom audits, and the raw-state boundary.
The projection's local record frame remains an obligation at generated handler points.
-/

namespace AlternativeFusedRemovalProjectionChecks
open GraphQL.IncrementalDelivery
open AlternativeWorkQueue

example : FusedRemovalProjection := FusedRemovalProjection_holds

private def ownerlessState : State :=
  {
    queue :=
      {
        taskNodes :=
          [{
            task :=
              { occurrence := .executionGroup [9], groups := [{ ref := 1, path := [] }] }
          }]
      }
  }

/-- A pre-existing ownerless task is a malformed-state counterexample to universal raw
equality: the reference global filter drops it even when the requested root is absent,
while actual affected-subtree removal does not visit it. No generated-work claim is refuted.
-/
theorem missing_root_raw_projection_differs
    : (ownerlessState.removeGroup 1).1.queue ≠ ownerlessState.queue.removeGroup 1 := by
  intro same
  have count := congrArg (fun queue : ReferenceWorkQueue.State => queue.taskNodes.length) same
  have actual : (ownerlessState.removeGroup 1).1.queue.taskNodes.length = 1 := by
    simp [ownerlessState, State.removeGroup, State.removeGroup.walk,
      ReferenceWorkQueue.State.groupNode?]
  have reference : (ownerlessState.queue.removeGroup 1).taskNodes.length = 0 := by decide
  rw [actual, reference] at count
  cases count

#print axioms fusedRemovalTaskFold_taskNodes
#print axioms eraseRemovalGroup_taskCoverage
#print axioms fusedRemovalVisit_taskRecords
#print axioms removeGroup_walk_taskRecords
#print axioms FusedRemovalProjection_holds
#print axioms missing_root_raw_projection_differs

end AlternativeFusedRemovalProjectionChecks
