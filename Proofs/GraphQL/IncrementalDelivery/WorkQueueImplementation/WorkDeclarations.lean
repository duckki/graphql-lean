import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskLookup
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.StructuralEquivalence

/-! Ordered declarations are independent of contributor references and creation refs. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue

/-- A declaration annotation contributes its descriptors in their supplied order. -/
theorem Work.fromExecution_declarations (groups : List Execution.DeferredFragment)
    (tasks : Execution.Work) (address : WorkQueueSemantics.Address)
    : (Work.fromExecution (.declareGroups groups tasks) address).groups
      = groups.map Work.fromExecution.lowerGroup
        ++ (Work.fromExecution tasks address).groups :=
  rfl

/-- Lowering an annotation retains the same task occurrences at the same address. -/
theorem Work.fromExecution_declaration_tasks (groups : List Execution.DeferredFragment)
    (tasks : Execution.Work) (address : WorkQueueSemantics.Address)
    : (Work.fromExecution (.declareGroups groups tasks) address).tasks
      = (Work.fromExecution tasks address).tasks :=
  rfl

/-- Declarations do not change the stream descriptor inventory. -/
theorem Work.fromExecution_declaration_streams (groups : List Execution.DeferredFragment)
    (tasks : Execution.Work) (address : WorkQueueSemantics.Address)
    : (Work.fromExecution (.declareGroups groups tasks) address).streams
      = (Work.fromExecution tasks address).streams :=
  rfl

/-- Normalized address views retain exactly the lowered task descriptors. -/
@[simp]
theorem Work.fromExecution_tasks_withoutDeclarations (work : Execution.Work)
    (address : WorkQueueSemantics.Address)
    : (Work.fromExecution work.withoutDeclarations address).tasks
      = (Work.fromExecution work address).tasks := by
  cases work with
  | declareGroups groups tasks =>
      change (Work.fromExecution tasks.withoutDeclarations address).tasks
        = (Work.fromExecution tasks address).tasks
      exact Work.fromExecution_tasks_withoutDeclarations tasks address
  | _ => rfl
termination_by work

/-- Normalized address views retain exactly the lowered stream descriptors. -/
@[simp]
theorem Work.fromExecution_streams_withoutDeclarations (work : Execution.Work)
    (address : WorkQueueSemantics.Address)
    : (Work.fromExecution work.withoutDeclarations address).streams
      = (Work.fromExecution work address).streams := by
  cases work with
  | declareGroups groups tasks =>
      change (Work.fromExecution tasks.withoutDeclarations address).streams
        = (Work.fromExecution tasks address).streams
      exact Work.fromExecution_streams_withoutDeclarations tasks address
  | _ => rfl
termination_by work

attribute [simp] Work.fromExecution

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
