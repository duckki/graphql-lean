import GraphQL.IncrementalDelivery.WorkQueueImplementation
import Proofs.GraphQL.IncrementalDelivery.Correctness.BoundaryErrorCounts
import Proofs.GraphQL.IncrementalDelivery.Correctness.TaskErrors

/-! Primitive execution failures give positive task-boundary reporting causes. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Every failed task in generated work contributes a positive execution-error count.
Witness: root execution's positive-failure certificate and structural task lookup.
-/
theorem ExecutedWork.taskFailure_positive {work : Execution.Work}
    (generated : ExecutedWork work) {occurrence owners producer payload}
    (known : TaskAt work occurrence owners producer payload)
    (failed : payload.failure.isSome = true)
    : 0 < payload.failure.getD 0 := by
  obtain ⟨ObjectRef, schema, resolvers, variables, fuel, parentType, source, selections,
    generated⟩ := generated
  have positive := (Correctness.ExecutionErrors.executeRootSelectionSetCore_positive
    schema resolvers variables fuel parentType source selections 0).2.1
  rw [generated] at positive
  exact positive.task known failed

/-- A generated failed task selects one primitive error, independently of its diagnostics. -/
theorem ExecutedWork.taskFailure_count {work : Execution.Work}
    (generated : ExecutedWork work) {occurrence owners producer payload}
    (known : TaskAt work occurrence owners producer payload)
    (failed : payload.failure.isSome = true)
    : payload.failure.getD 0 = 1 := by
  obtain ⟨ObjectRef, schema, resolvers, variables, fuel, parentType, source, selections,
    generated⟩ := generated
  have counted := (Correctness.BoundaryErrorCounts.executeRootSelectionSetCore_counted
    schema resolvers variables fuel parentType source selections 0).2.1
  rw [generated] at counted
  exact counted.task known failed

/-- Any supported completion cause in generated work has the same primitive count. -/
theorem ExecutedWork.nodeFailureCause_count {work : Execution.Work}
    (generated : ExecutedWork work) {failed ref errors}
    (cause : NodeFailureCause work failed ref errors)
    : errors = 1 := by
  obtain ⟨_, _, _, _, payload, known, _, selected, _⟩ := cause
  have counted := generated.taskFailure_count known (by rw [selected]; rfl)
  simpa only [selected, Option.getD_some] using counted

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
