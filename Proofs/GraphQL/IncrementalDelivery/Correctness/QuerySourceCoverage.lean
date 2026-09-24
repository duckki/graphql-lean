import Proofs.GraphQL.IncrementalDelivery.Correctness.SourcePublicationCoverage
import Proofs.GraphQL.IncrementalDelivery.Correctness.QueryDisjointness

/-! Successful terminal query observations cover their entire prepared source work. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open Semantics.MixedPaths

/-- Complete zero-error work observations deliver the entire initial/source inventory,
up to response-position order. Witness: terminal publication coverage, exact absolute
decoding, and actual wire replay. QueryCoverage connects this source inventory to basic
execution; this theorem isolates source coverage.
-/
theorem WorkObservation.source_coverage
    {paths bound response work result sourceSlices}
    (observed : WorkObservation response work true result)
    (coherent : Semantics.MixedOwnerPaths.WorkAt paths bound work)
    (positive : ExecutionErrors.WorkPositive work)
    (seeded
      : WorkCursorSeed (ResponsePositions.listCursors [] response.data) work sourceSlices)
    (source
      : (ResponsePositions.value true [] response.data ++ sourceSlices.flatten).Nodup)
    (zero : result.totalErrors = 0) (containers : Bool)
    : ∃ slices,
        result.DeliversSlices containers slices
        ∧ slices.flatten.Perm
            (ResponsePositions.value containers [] response.data
              ++ (sourceTasks [] none (ResponsePositions.listCursors [] response.data)
                    work).flatMap
                  (SourceTask.positions containers)) := by
  have safe := observed.idUsageValid
  have initialHistory : CursorHistory (ResponsePositions.listCursors [] response.data)
      (ResponsePositions.value true [] response.data) := by
    simpa only [source_value_eq_positions] using listCursors_positions [] response.data
  have sourceUnique : (ResponsePositions.value true [] response.data
      ++ List.flatMap (SourceTask.positions true)
        (sourceTasks [] none (ResponsePositions.listCursors [] response.data) work)).Nodup := by
    simpa only [List.flatMap, sourceTasks_positions seeded] using source
  cases observed with
  | single empty =>
      have noTasks : sourceTasks [] none (ResponsePositions.listCursors [] response.data)
          work = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro task member
        obtain ⟨owners, known⟩ := sourceTasks_known .root _ member
        exact no_tasks_of_size_zero empty known
      exact ⟨
        [ResponsePositions.value containers [] response.data],
        rfl,
        by simp [noTasks]
      ⟩
  | incremental groups streams batches nonempty batchNonempty admitted finished =>
      obtain ⟨produced, final, decoded, covered⟩ := replayResponse_absolute_coverage
        coherent positive seeded initialHistory sourceUnique (finished rfl) zero containers
      obtain ⟨slices, delivered, flattened⟩ :=
        replayResponse_positions coherent admitted safe decoded
      exact ⟨slices, delivered, flattened ▸ covered.append_left _⟩

/-- Every successful complete query covers its prepared root source positions, including
mixed nested defer/stream work. Witness: actual-root reduction and execution certificates;
the invalid-root branch contradicts the zero-error premise.
-/
theorem queryOutcome_source_coverage
    {schema : Schema} {resolvers : Resolvers ObjectRef} {variables : VariableValues}
    {operation : Operation} {fuel : Nat} {source : ResolverValue ObjectRef}
    {result : ExecutionObservation}
    (observed : queryOutcome schema resolvers variables operation fuel source result)
    (zero : result.totalErrors = 0) (containers : Bool)
    : let completed :=
        ((executeRootSelectionSetCore schema resolvers
            (coerceVariableValues operation variables) fuel (operation.rootType schema)
            source operation.selectionSet).run
          0).1
      let response := selectionSetResultToResponse completed.result
      ∃ slices,
        result.DeliversSlices containers slices
        ∧ slices.flatten.Perm
            (ResponsePositions.value containers [] response.data
              ++ (sourceTasks [] none (ResponsePositions.listCursors [] response.data)
                    completed.work).flatMap
                  (SourceTask.positions containers)) := by
  have witnessed := queryObservation_workHistory observed
  split at witnessed
  · obtain ⟨paths, coherent⟩ := Semantics.MixedOwnerPaths.executeRoot_owners schema resolvers
      (coerceVariableValues operation variables) fuel (operation.rootType schema) source
      operation.selectionSet 0
    obtain ⟨sourceSlices, seeded, sourcePositions⟩ := executeRoot_source_positions schema resolvers
      (coerceVariableValues operation variables) fuel (operation.rootType schema) source
      operation.selectionSet 0
    exact witnessed.source_coverage coherent
      (ExecutionErrors.executeRootSelectionSetCore_positive schema resolvers
        (coerceVariableValues operation variables) fuel (operation.rootType schema) source
        operation.selectionSet 0).2 seeded sourcePositions zero containers
  · subst result
    simp [ExecutionObservation.totalErrors] at zero

end GraphQL.IncrementalDelivery.Correctness
