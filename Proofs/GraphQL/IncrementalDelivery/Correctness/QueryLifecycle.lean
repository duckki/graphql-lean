import Proofs.GraphQL.IncrementalDelivery.Correctness.QueryIDUsage
import Proofs.GraphQL.IncrementalDelivery.Correctness.ResponseControl
import Proofs.GraphQL.IncrementalDelivery.Correctness.LifecycleControl

/-! Full public lifecycle validity, including termination-only final responses. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open MapperIdentity

/-- Complete work observations have nonempty initial notices, causal closure, and
accurate continuation flags. Witness: independent terminal-event accounting, replay,
and nonempty response grouping; closure need not coincide with the final response.
-/
theorem WorkObservation.control {response work result}
    (observed : WorkObservation response work true result)
    : QueryControl result := by
  have live := observed.idsEventuallyComplete
  cases observed with
  | single empty => trivial
  | incremental groups streams batches nonempty batchNonempty admitted finished =>
      have run := finished rfl
      have initialNonempty : groups ++ streams ≠ [] := by
        obtain ⟨_, _, _, explained, _, _⟩ := run
        exact explained.1.2
      cases allocated
            : (getPendingEntry (m := StateM IDState) groups streams ensureID).run {} with
      | mk pending ids =>
          have rawControl := mappedTrace_control run.terminalBatches ids
          have flatten : (replayGroups batches ids).1.flatten
              = mappedTrace batches.flatten ids := congrArg Prod.fst
            ((replayGroups_flatten batches ids).trans (mapM_workEvents _ _))
          have output : replayResponse response groups streams batches =
              .incremental { toResponse := response, pending, hasNext := true }
                ((replayGroups batches ids).1.map combineIncrementalResults) := by
            simp only [replayResponse, allocated, replayGroups_combined]
          rw [output] at live ⊢
          refine ⟨?_, live, ?_, ?_⟩
          · intro empty
            change pending = [] at empty
            obtain ⟨node, member⟩ := List.exists_mem_of_ne_nil _ initialNonempty
            obtain ⟨id, present, _⟩ := (getPendingEntry_of_eq allocated).2.fromKey node.key
              (List.mem_map.mpr ⟨node, member, rfl⟩)
            simp [empty] at present
          · have outputsNonempty :
                ((replayGroups batches ids).1.map combineIncrementalResults) ≠ [] := by
              intro empty
              have none := List.map_eq_nil_iff.mp empty
              rw [none] at flatten
              exact rawControl.1 flatten.symm
            have notEmpty :
                ((replayGroups batches ids).1.map combineIncrementalResults).isEmpty
                  = false := by simpa using outputsNonempty
            simp [notEmpty]
          · apply batched_hasNextValid (replayGroups_nonempty batchNonempty ids)
            rw [flatten]
            exact rawControl.2

/-- Complete work observations satisfy the full wire checker, combining independently
derived ID safety with causal closure and continuation control.
-/
theorem WorkObservation.deliveryComplete {response work result}
    (observed : WorkObservation response work true result)
    : result.deliveryComplete = true :=
  (deliveryComplete_iff_idUsageValid_control result).mpr
    ⟨observed.idUsageValid, observed.control⟩

/-- Every complete query outcome satisfies the public lifecycle statement, by
query-to-work observation soundness and the complete work-observation witness.
-/
theorem deliveryLifecycleValid_holds (schema : Schema) (operation : Operation)
    : deliveryLifecycleValid schema operation := by
  intro ObjectRef resolvers variables fuel source result observed
  exact queryObservation_property (fun result => result.deliveryComplete = true)
    (fun _ _ _ h => h.deliveryComplete) observed

/-- On complete query outcomes, zero errors is the only remaining execution-completeness
condition. Witness: lifecycle validity is already a consequence of the observation.
-/
theorem queryOutcome_executionComplete_iff
    {schema : Schema} {resolvers : Resolvers ObjectRef} {variables : VariableValues}
    {operation : Operation} {fuel : Nat} {source : ResolverValue ObjectRef}
    {result : QueryResult}
    (observed : queryOutcome schema resolvers variables operation fuel source result)
    : result.executionComplete ↔ result.totalErrors = 0 := by
  constructor
  · exact And.right
  · intro zero
    exact ⟨deliveryLifecycleValid_holds schema operation
      resolvers variables fuel source result observed, zero⟩

end GraphQL.IncrementalDelivery.Correctness
