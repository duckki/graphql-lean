import Proofs.GraphQL.IncrementalDelivery.Correctness.HistoryAttachments
import Proofs.GraphQL.IncrementalDelivery.Correctness.AtomMerging

/-! Arbitrary admitted publication histories merge without losing typed response entries. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open WorkScheduler
open Semantics.MixedPaths
open SourceReconstruction SourceAttachments

/-- A supplied value publication merges successfully into the current response. Witness:
its parent is already published, its entries are disjoint, and its stream cursor equals
the actual list length. The resulting cursor history still represents the merged data.
-/
theorem merge_history_value
    {work groups streams events matching failures initial slices positions cut event task
      current}
    (explained : Explains work groups streams events matching failures)
    (seeded : WorkCursorSeed (ResponsePositions.listCursors [] initial) work slices)
    (success : WorkSuccess work)
    (attached
      : WorkAttached (TypedResponse.value [] initial) work
          (entryPaths
            ((sourceTasks [] none (ResponsePositions.listCursors [] initial) work).map
              SourceTask.entries)))
    (initialHistory : CursorHistory (ResponsePositions.listCursors [] initial) positions)
    (initialPositions : (TypedResponse.value [] initial).map Prod.fst = positions)
    (unique
      : (positions
          ++ (sourceTasks [] none (ResponsePositions.listCursors [] initial) work).flatMap
              (SourceTask.positions true)).Nodup)
    (member : task ∈ sourceTasks [] none (ResponsePositions.listCursors [] initial) work)
    (selected : events[cut]? = some event) (value : IsValue event)
    (same : task.occurrence = matching cut)
    (entries
      : (TypedResponse.value [] current).Perm
          (TypedResponse.value [] initial
            ++ (sourcePrefixTasks
                  (sourceTasks [] none (ResponsePositions.listCursors [] initial) work)
                  matching events cut).flatMap
                SourceTask.entries))
    (represents
      : TypedResponse.CursorRepresents
          (sourceHistoryCursors
            (sourceTasks [] none (ResponsePositions.listCursors [] initial) work) matching
            events (ResponsePositions.listCursors [] initial) cut) current)
    : ∃ updated,
        applyAtoms (eventPositionAtoms event) current = some updated
        ∧ (TypedResponse.value [] updated).Perm
            (TypedResponse.value [] current ++ task.entries)
        ∧ TypedResponse.CursorRepresents
            (sourceHistoryCursors
              (sourceTasks [] none (ResponsePositions.listCursors [] initial) work)
              matching events (ResponsePositions.listCursors [] initial) (cut + 1))
            updated := by
  have parent := entries.mem_iff.mpr
    (history_publication_attachment explained success attached member selected value same)
  have selectedTask := sourceEventTask_value value member same
  have nextUnique := sourcePrefix_positions_unique explained unique (cut + 1)
  have typedUnique : ((TypedResponse.value [] current ++ task.entries).map Prod.fst).Nodup := by
    apply ((entries.append_right task.entries).map Prod.fst).nodup_iff.mpr
    simpa only [sourcePrefixTasks, selected, Option.bind_some, selectedTask,
      Option.toList_some, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.map_append, List.map_flatMap, SourceTask.entries_paths,
      initialPositions, List.append_assoc] using nextUnique
  obtain ⟨owners, known⟩ := sourceTasks_known .root (ResponsePositions.listCursors [] initial) member
  have allowed := explained.2.2 cut event selected
  have bound := (List.getElem?_eq_some_iff.mp selected).choose
  have length : (events.take cut).length = cut := by
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt bound)]
  rw [same] at known
  rw [sourceHistoryCursors_step selected, sourceEventCursors_value value member same]
  cases event <;> try contradiction
  case groupValues node values =>
    obtain ⟨_, _, path, data, errors, rfl, actual, _⟩ := allowed
    rw [length] at actual
    have payload := (known.unique actual).2.2
    obtain ⟨updated, merged, exactEntries, represented⟩ :=
      TypedResponse.merge_object_cursorRepresents path current data _ represents
        (by simpa only [SourceTask.attachment, payload] using parent)
        (by simpa only [SourceTask.entries, payload, TypedResponse.result] using typedUnique)
    refine ⟨updated, ?_, ?_, ?_⟩
    · simp only [eventPositionAtoms, List.map_cons, List.map_nil, applyAtoms,
        List.foldlM_cons, List.foldlM_nil, Option.bind_eq_bind, Option.pure_def,
        Option.bind_fun_some]
      exact merged
    · simpa only [SourceTask.entries, payload, TypedResponse.result] using exactEntries
    · simpa only [SourceTask.cursorUpdates, SourceTask.cursors, payload, resultCursors]
        using represented
  case streamValues node values groups streams =>
    obtain ⟨_, _, item, errors, rfl, actual, _⟩ := allowed
    rw [length] at actual
    have payload := (known.unique actual).2.2
    obtain ⟨address, ordinal, occurrence⟩ := sourceTask_item_occurrence member payload
    have cursor := sourceHistoryCursors_item explained seeded initialHistory unique
      member occurrence payload selected value same
    obtain ⟨updated, merged, exactEntries, represented⟩ :=
      TypedResponse.merge_stream_cursorRepresents node.path task.index current item _ represents
        (by simpa only [SourceTask.attachment, payload] using parent) cursor
        (by simpa only [SourceTask.entries, payload, TypedResponse.result] using typedUnique)
    refine ⟨updated, ?_, ?_, ?_⟩
    · simp only [eventPositionAtoms, List.map_cons, List.map_nil, applyAtoms,
        List.foldlM_cons, List.foldlM_nil, Option.bind_eq_bind, Option.pure_def,
        Option.bind_fun_some]
      exact merged
    · simpa only [SourceTask.entries, payload, TypedResponse.result] using exactEntries
    · simpa only [SourceTask.cursorUpdates, SourceTask.cursors, payload, resultCursors]
        using represented

/-- Every supplied history prefix merges to exactly its initial and published typed
entries. Witness: prefix induction, applying the value theorem or ignoring controls.
No completion order is selected and no successful-merge premise is assumed.
-/
theorem merge_history
    {work groups streams events matching failures initial slices positions}
    (explained : Explains work groups streams events matching failures)
    (seeded : WorkCursorSeed (ResponsePositions.listCursors [] initial) work slices)
    (success : WorkSuccess work)
    (attached
      : WorkAttached (TypedResponse.value [] initial) work
          (entryPaths
            ((sourceTasks [] none (ResponsePositions.listCursors [] initial) work).map
              SourceTask.entries)))
    (initialHistory : CursorHistory (ResponsePositions.listCursors [] initial) positions)
    (initialPositions : (TypedResponse.value [] initial).map Prod.fst = positions)
    (unique
      : (positions
          ++ (sourceTasks [] none (ResponsePositions.listCursors [] initial) work).flatMap
              (SourceTask.positions true)).Nodup)
    (cut : Nat) (bound : cut ≤ events.length)
    : ∃ updated,
        applyAtoms ((events.take cut).flatMap eventPositionAtoms) initial = some updated
        ∧ (TypedResponse.value [] updated).Perm
            (TypedResponse.value [] initial
              ++ (sourcePrefixTasks
                    (sourceTasks [] none (ResponsePositions.listCursors [] initial) work)
                    matching events cut).flatMap
                  SourceTask.entries)
        ∧ TypedResponse.CursorRepresents
            (sourceHistoryCursors
              (sourceTasks [] none (ResponsePositions.listCursors [] initial) work)
              matching events (ResponsePositions.listCursors [] initial) cut)
            updated := by
  induction cut with
  | zero => exact ⟨initial, rfl, by simp [sourcePrefixTasks], fun _ => rfl⟩
  | succ cut ih =>
      have earlier : cut < events.length := by omega
      have selected : events[cut]? = some events[cut] := List.getElem?_eq_getElem earlier
      obtain ⟨current, replay, entries, represented⟩ := ih (by omega)
      rw [List.take_succ_eq_append_getElem earlier, List.flatMap_append,
        List.flatMap_cons, List.flatMap_nil, List.append_nil, applyAtoms_append, replay]
      have classified : IsValue events[cut] ∨ ¬IsValue events[cut] := Classical.em _
      rcases classified with value | control
      · obtain ⟨task, member, same⟩ := publication_sourceTask explained selected value
        obtain ⟨updated, merged, exactEntries, nextRep⟩ := merge_history_value
          explained seeded success attached initialHistory initialPositions unique member selected
          value same entries represented
        refine ⟨updated, by simpa using merged, ?_, nextRep⟩
        simpa only [sourcePrefixTasks, selected, Option.bind_some,
          sourceEventTask_value value member same, Option.toList_some,
          List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
          List.append_assoc]
          using exactEntries.trans (entries.append_right task.entries)
      · have noAtoms : eventPositionAtoms events[cut] = [] := by
          cases equal : events[cut] <;> simp_all [IsValue, eventPositionAtoms]
        refine ⟨current, by simp [noAtoms, applyAtoms], ?_, ?_⟩
        · simpa only [sourcePrefixTasks, selected, Option.bind_some,
            sourceEventTask_control control, Option.toList_none, List.append_nil] using entries
        · simpa only [sourceHistoryCursors_step selected, sourceEventCursors_control control,
            List.nil_append] using represented

end GraphQL.IncrementalDelivery.Correctness
