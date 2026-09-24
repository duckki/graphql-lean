import Proofs.GraphQL.IncrementalDelivery.Correctness.AtomMerging
import Proofs.GraphQL.IncrementalDelivery.Correctness.WirePositionReplay

/-! The actual ID-based client merger has exactly the absolute atoms' data effects. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open MapperIdentity

/-- An announced wire entry applies the same data effect as its encoded absolute atoms.
Witness: stable notice paths and nonempty stream-item coalescing at one list path.
-/
theorem EntryPositionAtoms.apply {paths ids entry atoms notices}
    (encoded : EntryPositionAtoms paths ids entry atoms) (allocated : Allocated ids)
    (metadata : NoticePaths paths ids notices)
    (announced : entry.id ∈ notices.map IncrementalPendingNotice.id)
    (data : ResponseValue)
    : ResponseMerging.applyPatch notices data entry = applyAtoms atoms data := by
  obtain ⟨notice, found⟩ := notice_exists announced
  cases encoded with
  | @object key id incoming errors subPath known =>
      have path := metadata.lookup (node := {key, path := paths key}) allocated known rfl found
      simp only [IncrementalResult.id] at found
      simp only [ResponseMerging.applyPatch, IncrementalResult.id, found,
        Option.bind_eq_bind, Option.bind_some, path, applyAtoms, List.foldlM_cons,
        List.foldlM_nil, Option.pure_def, Option.bind_fun_some]
      rfl
  | @list key id incoming errors known nonempty =>
      have path := metadata.lookup (node := {key, path := paths key}) allocated known rfl found
      simp only [IncrementalResult.id] at found
      rw [applyAtoms_items _ _ nonempty]
      simp only [ResponseMerging.applyPatch, IncrementalResult.id, found,
        Option.bind_eq_bind, Option.bind_some, path]
      rfl

/-- A wire entry sequence and its absolute atom sequence have identical data effects.
Witness: entry induction and compositional atom replay.
-/
theorem EntriesPositionAtoms.apply {paths ids entries atoms notices}
    (encoded : EntriesPositionAtoms paths ids entries atoms) (allocated : Allocated ids)
    (metadata : NoticePaths paths ids notices)
    (announced : ∀ entry ∈ entries, entry.id ∈ notices.map IncrementalPendingNotice.id)
    (data : ResponseValue)
    : entries.foldlM (ResponseMerging.applyPatch notices) data
      = applyAtoms atoms data := by
  induction encoded generalizing data with
  | nil => rfl
  | @cons entry entries first rest head tail ih =>
      simp only [List.foldlM_cons, Option.bind_eq_bind, applyAtoms_append]
      rw [head.apply allocated metadata (announced entry (by simp))]
      apply congrArg
      funext current
      exact ih (fun entry member => announced entry (by simp [member])) current

/-- Update boundaries add notices but do not alter data effects. Witness: split the
encoded atoms at each actual update and use only its causally available announcements.
-/
theorem updates_applyAtoms {paths ids updates atoms notices}
    (encoded
      : EntriesPositionAtoms paths ids
          (updates.flatMap IncrementalStreamUpdateResult.incremental) atoms)
    (allocated : Allocated ids)
    (metadata
      : NoticePaths paths ids
          (notices ++ updates.flatMap IncrementalStreamUpdateResult.pending))
    (announced
      : DeliveryTrace.patchesAnnounced (notices.map IncrementalPendingNotice.id) updates)
    (data : ResponseValue)
    : updates.foldlM ResponseMerging.applyUpdate (data, notices)
      = (applyAtoms atoms data).map
          (fun data =>
            (
              data,
              notices ++ updates.flatMap IncrementalStreamUpdateResult.pending
            )) := by
  induction updates generalizing atoms notices data with
  | nil =>
      cases encoded
      simp [applyAtoms]
  | cons update rest ih =>
      obtain ⟨headAtoms, tailAtoms, rfl, head, tail⟩ := encoded.split
      have currentMetadata : NoticePaths paths ids (notices ++ update.pending) :=
        metadata.subset
          (fun notice member => by
            simpa only [List.flatMap_cons, List.append_assoc]
              using List.mem_append_left
                (rest.flatMap IncrementalStreamUpdateResult.pending) member)
      have laterMetadata : NoticePaths paths ids
          ((notices ++ update.pending) ++ rest.flatMap IncrementalStreamUpdateResult.pending) := by
        simpa only [List.flatMap_cons, List.append_assoc] using metadata
      have currentAnnounced : ∀ entry ∈ update.incremental,
          entry.id ∈ (notices ++ update.pending).map IncrementalPendingNotice.id := by
        simpa only [List.map_append] using announced.1
      have laterAnnounced : DeliveryTrace.patchesAnnounced
          ((notices ++ update.pending).map IncrementalPendingNotice.id) rest := by
        simpa only [List.map_append] using announced.2
      have first := head.apply allocated currentMetadata currentAnnounced data
      have later := fun current => ih tail laterMetadata laterAnnounced current
      simp only [List.foldlM_cons, ResponseMerging.applyUpdate, first,
        Option.bind_eq_bind, Option.pure_def, applyAtoms_append]
      cases hd : applyAtoms headAtoms data with
      | none => simp
      | some current =>
          simpa [hd, List.flatMap_cons, List.append_assoc] using later current

/-- Actual response replay and reconstruction agree exactly with absolute data replay.
Witness: initial allocation, mapper encoding, update coalescing, and the lifecycle guard.
-/
theorem replayResponse_merge_atoms {paths bound response work groups streams batches}
    (coherent : Semantics.MixedOwnerPaths.WorkAt paths bound work)
    (admitted
      : WorkScheduler.AdmissiblePrefix work ⟨groups, streams, batches.flatten⟩
        ∨ WorkScheduler.AdmissibleRun work ⟨groups, streams, batches.flatten⟩)
    (safe : (replayResponse response groups streams batches).idUsageValid)
    (complete : (replayResponse response groups streams batches).deliveryComplete = true)
    : mergeExecutionObservation (replayResponse response groups streams batches)
      = (applyAtoms (batches.flatten.flatten.flatMap eventPositionAtoms)
          response.data).map
          (fun data =>
            ({
                data,
                errors := (replayResponse response groups streams batches).totalErrors
              }
              : Response)) := by
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
      rw [replay] at announced complete ⊢
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
      have merged := updates_applyAtoms encoded finalWell metadata announced response.data
      simp only [mergeExecutionObservation, complete, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        merged, Option.bind_eq_bind, Option.pure_def]
      cases applyAtoms (batches.flatten.flatten.flatMap eventPositionAtoms) response.data <;> rfl

end GraphQL.IncrementalDelivery.Correctness
