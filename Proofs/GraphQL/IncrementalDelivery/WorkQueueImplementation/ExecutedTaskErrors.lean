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

/-- Distinct available unit causes cannot exceed a complete contributor candidate list.
This bounds reporting counts independently of the selected causal failure inventory.
-/
theorem ExecutedWork.nodeFailureCauses_count_le {work : Execution.Work}
    (generated : ExecutedWork work) {available ref errors} (candidates : List Occurrence)
    (complete
      : ∀ occurrence owners producer payload,
          TaskAt work occurrence owners producer payload
          → ref ∈ owners
          → payload.failure.isSome = true
          → occurrence ∈ candidates)
    (cause : NodeFailureCauses work available ref errors)
    : errors ≤ candidates.length := by
  obtain ⟨causes, _, unique, supported, counted⟩ := cause
  have units (entry : Occurrence × Nat) (member : entry ∈ causes) : entry.2 = 1 := by
    obtain ⟨seen, owners, producer, payload, known, owner, failure, positive⟩ :=
      supported entry.1 entry.2 member
    exact generated.nodeFailureCause_count
      ⟨entry.1, seen, owners, producer, payload, known, owner, failure, positive⟩
  have sumUnits (more : List (Occurrence × Nat))
      (unit : ∀ entry ∈ more, entry.2 = 1) : (more.map Prod.snd).sum = more.length := by
    induction more with
    | nil => rfl
    | cons entry rest ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons,
          unit entry List.mem_cons_self, ih (fun pair member =>
            unit pair (List.mem_cons_of_mem _ member)), Nat.add_comm]
  have included : (causes.map Prod.fst).Subset candidates := by
    intro occurrence member
    obtain ⟨entry, supplied, rfl⟩ := List.mem_map.mp member
    obtain ⟨_, owners, producer, payload, known, owner, failure, _⟩ :=
      supported entry.1 entry.2 supplied
    exact complete entry.1 owners producer payload known owner (by rw [failure]; rfl)
  have bound := unique.length_le_of_subset included
  rw [List.length_map] at bound
  rw [counted, sumUnits causes units]
  exact bound

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
