import Proofs.GraphQL.IncrementalDelivery.Correctness.MapperPositionAtoms

/-! Causal response boundaries preserve the absolute-position decoder and its slices. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open MapperIdentity

/-- Restricting available notices retains their stable source-path metadata. -/
theorem NoticePaths.subset {paths ids all someNotices}
    (metadata : NoticePaths paths ids all) (included : someNotices.Subset all)
    : NoticePaths paths ids someNotices :=
  fun notice member => metadata notice (included member)

/-- Response coalescing concatenates actual patch entries, by accumulator induction. -/
theorem combineFrom_incremental (updates : List IncrementalStreamUpdateResult)
    (initial : IncrementalStreamUpdateResult)
    : (combineFrom updates initial).incremental
      = initial.incremental
        ++ updates.flatMap IncrementalStreamUpdateResult.incremental := by
  induction updates generalizing initial with
  | nil => simp [combineFrom]
  | cons update rest ih =>
      simpa [combineFrom, List.append_assoc] using ih
        { hasNext := update.hasNext, pending := initial.pending ++ update.pending,
          incremental := initial.incremental ++ update.incremental,
          completed := initial.completed ++ update.completed }

/-- Arbitrary response grouping preserves the complete ordered patch list. -/
theorem batched_incremental (groups : List (List IncrementalStreamUpdateResult))
    : (groups.map combineIncrementalResults).flatMap
        IncrementalStreamUpdateResult.incremental
      = groups.flatten.flatMap IncrementalStreamUpdateResult.incremental := by
  have one (updates : List IncrementalStreamUpdateResult)
      : (combineIncrementalResults updates).incremental
        = updates.flatMap IncrementalStreamUpdateResult.incremental := by
    simpa only [combineFrom, combineIncrementalResults, List.nil_append]
      using combineFrom_incremental updates { hasNext := false }
  induction groups with
  | nil => rfl
  | cons group rest ih =>
      simp only [List.map_cons, List.flatMap_cons, List.flatten_cons, List.flatMap_append,
        one, ih]

/-- Encoded response updates decode using only currently announced IDs, with exactly
the absolute decoder's flattened positions. Witness: split atoms at each response
boundary and transport tail decoding across equivalent cursor histories.
-/
theorem positionUpdates_of_atoms
    {paths ids updates atoms notices containers cursors produced final}
    (encoded
      : EntriesPositionAtoms paths ids
          (updates.flatMap IncrementalStreamUpdateResult.incremental) atoms)
    (allocated : Allocated ids)
    (metadata
      : NoticePaths paths ids
          (notices ++ updates.flatMap IncrementalStreamUpdateResult.pending))
    (announced
      : DeliveryTrace.patchesAnnounced (notices.map IncrementalPendingNotice.id) updates)
    (decoded : decodeAtoms containers cursors atoms = some (produced, final))
    : ∃ slices next,
        DeliveryTrace.decodeUpdates containers notices cursors updates
          = some (slices, next)
        ∧ slices.flatten = produced
        ∧ CursorEquivalent final next := by
  induction updates generalizing notices cursors atoms produced final with
  | nil =>
      cases encoded
      simp only [decodeAtoms, Option.some.injEq, Prod.mk.injEq] at decoded
      obtain ⟨rfl, rfl⟩ := decoded
      exact ⟨[], cursors, rfl, rfl, fun _ => rfl⟩
  | cons update rest ih =>
      obtain ⟨headAtoms, tailAtoms, rfl, headEncoded, tailEncoded⟩ := encoded.split
      have currentMetadata : NoticePaths paths ids (notices ++ update.pending) := by
        apply metadata.subset
        intro notice member
        simpa only [List.flatMap_cons, List.append_assoc]
          using (List.mem_append_left (rest.flatMap IncrementalStreamUpdateResult.pending)
                  member)
      have laterMetadata : NoticePaths paths ids
          ((notices ++ update.pending) ++ rest.flatMap IncrementalStreamUpdateResult.pending) := by
        simpa only [List.flatMap_cons, List.append_assoc] using metadata
      have currentAnnounced : ∀ entry ∈ update.incremental,
          entry.id ∈ (notices ++ update.pending).map IncrementalPendingNotice.id := by
        simpa only [List.map_append] using announced.1
      have laterAnnounced : DeliveryTrace.patchesAnnounced
          ((notices ++ update.pending).map IncrementalPendingNotice.id) rest := by
        simpa only [List.map_append] using announced.2
      rw [decodeAtoms_append] at decoded
      cases hd : decodeAtoms containers cursors headAtoms with
      | none => simp [hd] at decoded
      | some pair =>
          rcases pair with ⟨firstPositions, middle⟩
          cases td : decodeAtoms containers middle tailAtoms with
          | none => simp [hd, td] at decoded
          | some pair =>
              rcases pair with ⟨laterPositions, last⟩
              simp [hd, td] at decoded
              obtain ⟨rfl, rfl⟩ := decoded
              obtain ⟨head, wireMiddle, hp, headPositions, middleEq⟩ :=
                headEncoded.decode allocated currentMetadata currentAnnounced hd
              obtain ⟨tailFinal, tailDecoded, tailEq⟩ := decodeAtoms_equivalent middleEq td
              obtain ⟨tail, wireFinal, ht, tailPositions, finalEq⟩ :=
                ih tailEncoded laterMetadata laterAnnounced tailDecoded
              refine ⟨head ++ tail, wireFinal,
                ?_, ?_, tailEq.trans finalEq⟩
              · simp [DeliveryTrace.decodeUpdates, hp, ht]
              · simp only [List.flatten_append, headPositions, tailPositions]

end GraphQL.IncrementalDelivery.Correctness
