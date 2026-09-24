import Proofs.GraphQL.IncrementalDelivery.Correctness.ResponsePositionDecoding
import Proofs.GraphQL.IncrementalDelivery.Correctness.QueryIDUsage

/-! Exact absolute-position decoding survives ID encoding and response coalescing. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open MapperIdentity

/-- An admitted response replay delivers exactly its decoded absolute positions, after
the initial slice. Witness: stable allocated IDs, causal notices, and entry-preserving
response coalescing. The decoder may include containers or retain only leaves.
-/
theorem replayResponse_positions
    {paths bound response work groups streams batches containers produced final}
    (coherent : Semantics.MixedOwnerPaths.WorkAt paths bound work)
    (admitted
      : WorkScheduler.AdmissiblePrefix work ⟨groups, streams, batches.flatten⟩
        ∨ WorkScheduler.AdmissibleRun work ⟨groups, streams, batches.flatten⟩)
    (safe : (replayResponse response groups streams batches).idUsageValid)
    (decoded
      : decodeAtoms containers (ResponsePositions.listCursors [] response.data)
          (batches.flatten.flatten.flatMap eventPositionAtoms)
        = some (produced, final))
    : ∃ slices,
        (replayResponse response groups streams batches).DeliversSlices containers slices
        ∧ slices.flatten
          = ResponsePositions.value containers [] response.data ++ produced := by
  have announced := patchesAnnounced_of_idUsageValid _ safe
  have shapes := admitted_patchShapes coherent admitted
  obtain ⟨initialPaths, eventPaths⟩ := history_node_paths coherent admitted
  cases allocated
        : (getPendingEntry (m := StateM IDState) groups streams ensureID).run {} with
  | mk pending ids =>
      have valid := (getPendingEntry_metadata_of_eq allocated).paths initialPaths
      have well : Allocated ids := by
        simpa only [allocated] using getPendingEntry_allocated groups streams {} .empty
      have finalWell := finalIDs_allocated batches.flatten ids well
      have initial := valid.mono (mappedTrace_spec batches.flatten ids).1
      have subsequent := mappedTrace_noticePaths batches.flatten ids eventPaths
      have entries := mappedTrace_positionAtoms batches.flatten ids shapes
      have grouped := replayResponse_groups response groups streams batches
      rw [allocated] at grouped
      obtain ⟨updates, flat, replay⟩ := grouped
      rw [replay] at announced ⊢
      have metadata : NoticePaths paths (finalIDs batches.flatten ids)
          (pending ++ (updates.map combineIncrementalResults).flatMap
            IncrementalStreamUpdateResult.pending) := by
        rw [batched_pending, flat]
        exact initial.append subsequent
      have encoded : EntriesPositionAtoms paths (finalIDs batches.flatten ids)
          ((updates.map combineIncrementalResults).flatMap
            IncrementalStreamUpdateResult.incremental)
          (batches.flatten.flatten.flatMap eventPositionAtoms) := by
        rw [batched_incremental, flat]
        exact entries
      obtain ⟨tail, wireFinal, positions, flattened, _⟩ :=
        positionUpdates_of_atoms encoded finalWell metadata announced decoded
      exact ⟨
        ResponsePositions.value containers [] response.data :: tail,
        ExecutionObservation.deliversSlices_incremental_iff.mpr
          ⟨tail, wireFinal, positions, rfl⟩,
        by simp only [List.flatten_cons, flattened]
      ⟩

end GraphQL.IncrementalDelivery.Correctness
