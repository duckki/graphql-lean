import Proofs.GraphQL.IncrementalDelivery.Correctness.HistoryAbsolutePositions
import Proofs.GraphQL.IncrementalDelivery.Correctness.WirePositionReplay
import Proofs.GraphQL.IncrementalDelivery.Semantics.WireLeafPositions

/-! Public wire-slice disjointness for every query observation and permitted batching. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open MapperIdentity
open Semantics.MixedPaths

/-- Actual work observations decode to globally unique positions when their independently
proved source-work certificates hold. Witness: source/history disjointness, stable mapper
encoding, causal announcements, and arbitrary response-coalescing preservation.
-/
theorem WorkObservation.disjoint_positions
    {paths bound response work complete result sourceSlices}
    (observed : WorkObservation response work complete result)
    (coherent : Semantics.MixedOwnerPaths.WorkAt paths bound work)
    (seeded
      : WorkCursorSeed (ResponsePositions.listCursors [] response.data) work sourceSlices)
    (source
      : (ResponsePositions.value true [] response.data ++ sourceSlices.flatten).Nodup)
    : ∃ slices, result.DeliversSlices true slices ∧ slices.flatten.Nodup := by
  have safe := observed.idUsageValid
  have initialHistory : CursorHistory (ResponsePositions.listCursors [] response.data)
      (ResponsePositions.value true [] response.data) := by
    simpa only [source_value_eq_positions] using listCursors_positions [] response.data
  have sourceUnique : (ResponsePositions.value true [] response.data
      ++ List.flatMap (SourceTask.positions true)
        (sourceTasks [] none (ResponsePositions.listCursors [] response.data) work)).Nodup := by
    simpa only [List.flatMap, sourceTasks_positions seeded] using source
  cases observed with
  | single _ =>
      exact ⟨
        [ResponsePositions.value true [] response.data],
        rfl,
        by
          simpa using (List.nodup_append.mp source).1
      ⟩
  | incremental groups streams batches nonempty batchNonempty admitted finished =>
      obtain ⟨produced, final, decoded, disjoint⟩ := admitted_absolute_positions
        coherent seeded initialHistory sourceUnique admitted
      obtain ⟨slices, delivered, flattened⟩ :=
        replayResponse_positions coherent admitted safe decoded
      exact ⟨slices, delivered, flattened.symm ▸ disjoint⟩

/-- Every actual query observation has a container-inclusive, globally unique wire
position sequence. Witness: root execution's source ownership and cursor certificates,
or the ordinary singleton null position for an inapplicable root.
-/
theorem queryObservation_disjoint_positions
    {schema : Schema} {resolvers : Resolvers ObjectRef} {variables : VariableValues}
    {operation : Operation} {fuel : Nat} {source : ResolverValue ObjectRef}
    {result : ExecutionObservation} {complete : Bool}
    (observed
      : queryObservation schema resolvers variables operation fuel source result complete)
    : ∃ slices, result.DeliversSlices true slices ∧ slices.flatten.Nodup := by
  have witnessed := queryObservation_workHistory observed
  split at witnessed
  · obtain ⟨paths, coherent⟩ := Semantics.MixedOwnerPaths.executeRoot_owners schema resolvers
      (coerceVariableValues operation variables) fuel (operation.rootType schema) source
      operation.selectionSet 0
    obtain ⟨sourceSlices, seeded, sourcePositions⟩ := executeRoot_source_positions schema resolvers
      (coerceVariableValues operation variables) fuel (operation.rootType schema) source
      operation.selectionSet 0
    exact witnessed.disjoint_positions coherent seeded sourcePositions
  · subst result
    exact ⟨[[[]]], rfl, by simp⟩

/-- All public query delivery slices are internally unique and pairwise disjoint, even
with overlapping defer owners, streams, failures, stalled prefixes, and arbitrary
batching. Witness: global container-inclusive wire uniqueness, then leaf projection
when containers are omitted.
-/
theorem deliverySlicesDisjoint_holds (schema : Schema) (operation : Operation)
    : deliverySlicesDisjoint schema operation := by
  intro ObjectRef resolvers variables fuel source result containers observed
  obtain ⟨slices, delivered, disjoint⟩ := queryObservation_disjoint_positions observed
  cases containers with
  | true => exact ⟨slices, delivered, disjoint⟩
  | false => exact Semantics.deliversSlices_leaves_nodup delivered disjoint

end GraphQL.IncrementalDelivery.Correctness
