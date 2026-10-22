import GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskEligibility

/-! Structural parent-cut safety and the target task-presence settlement check.
Owner health is a semantic replay invariant, not an additional runtime guard.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement

/-- The target settlement handlers ignore callbacks whose started task node is absent. -/
def TaskPresenceChecked (queue : ReferenceWorkQueue.State) : Prop :=
  ∀ occurrence,
    queue.taskNode? occurrence = none
    → (∀ result, queue.taskSuccess occurrence result = (queue, []))
      ∧ ∀ errors, queue.taskFailure occurrence errors = (queue, [])

theorem taskPresenceChecked_holds (queue : ReferenceWorkQueue.State)
    : TaskPresenceChecked queue := by
  intro occurrence absent
  exact ⟨queue.taskSuccess_of_taskNode_none absent, queue.taskFailure_of_taskNode_none absent⟩

/-- A structural cut invariant, not an assumption added to EventSource.ValidFor.
Each live record's absent immediate parent was not removed by failure.
-/
def SafeParentCuts (queue : ReferenceWorkQueue.State) : Prop :=
  ∀ node ∈ queue.groupNodes,
    ∀ parent,
      node.group.parent = some parent
      → queue.groupNode? parent = none
      → parent ∉ queue.cancelledGroups

/-- Raw counterexample: a live child has a missing parent removed by failure. -/
def orphanedChild : ReferenceWorkQueue.State :=
  {
    cancelledGroups := [0],
    groupNodes := [{ group := { node := { ref := 1, path := [] }, parent := some 0 } }]
  }

theorem orphanedChild_cuts_unsafe : ¬SafeParentCuts orphanedChild := by
  intro cuts
  have absent := cuts
    { group := { node := { ref := 1, path := [] }, parent := some 0 } }
    (by simp [orphanedChild]) 0 rfl (by decide)
  exact absent (by simp [orphanedChild])

/-- Construction target for safe cuts at actual generated replay boundaries.
`GeneratedParentCuts_holds` in GeneratedParentCuts supplies its unconditional witness.
-/
def GeneratedParentCuts : Prop :=
  ∀ work inputs,
    ReferenceWorkQueue.ExecutedWork work
    → ReferenceWorkQueue.ValidGraphEvents work inputs.flatten
    → ReferenceWorkQueue.inputsStarted work inputs = true
    → SafeParentCuts ((State.initialize work).runNormalized inputs).1.queue

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
