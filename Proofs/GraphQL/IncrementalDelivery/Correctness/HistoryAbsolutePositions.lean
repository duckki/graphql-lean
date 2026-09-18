import Proofs.GraphQL.IncrementalDelivery.Correctness.PublicationPositions

/-! Absolute atom decoding agrees with admitted histories' disjoint source publications. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open WorkScheduler
open Semantics.MixedPaths

/-- A value atom decodes to its exact source positions and cursor writes. Witness:
payload uniqueness for object values and the proved prefix cursor for streamed items.
-/
theorem decode_eventPositionAtoms_value
    {containers : Bool}
    {work groups streams events matching failures initial slices positions}
    (explained : Explains work groups streams events matching failures)
    (seeded : WorkCursorSeed initial work slices)
    (initialHistory : CursorHistory initial positions)
    (disjoint
      : (positions
          ++ (sourceTasks [] none initial work).flatMap
              (SourceTask.positions true)).Nodup)
    {task cut event}
    (member : task ∈ sourceTasks [] none initial work)
    (selected : events[cut]? = some event) (value : IsValue event)
    (matched : task.occurrence = matching cut)
    : decodeAtoms containers
        (sourceHistoryCursors (sourceTasks [] none initial work) matching events initial
          cut)
        (eventPositionAtoms event)
      = some
          (
            task.positions containers,
            task.cursorUpdates
            ++ sourceHistoryCursors (sourceTasks [] none initial work) matching events
                initial cut
          ) := by
  obtain ⟨owners, known⟩ := sourceTasks_known .root initial member
  have allowed := explained.2.2 cut event selected
  have bound := (List.getElem?_eq_some_iff.mp selected).choose
  have length : (events.take cut).length = cut := by
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt bound)]
  rw [matched] at known
  cases event <;> try contradiction
  case groupValues node values =>
    obtain ⟨_, _, path, data, errors, rfl, actual, _⟩ := allowed
    rw [length] at actual
    have payload := (known.unique actual).2.2
    simp [eventPositionAtoms, decodeAtoms, PositionAtom.decode, SourceTask.positions,
      SourceTask.cursorUpdates, SourceTask.cursors, payload, resultCursors,
      DeliveryPaths.result]
  case streamValues node values groups streams =>
    obtain ⟨_, _, item, errors, rfl, actual, _⟩ := allowed
    rw [length] at actual
    have payload := (known.unique actual).2.2
    obtain ⟨address, ordinal, occurrence⟩ := sourceTask_item_occurrence member payload
    have cursor := sourceHistoryCursors_item explained seeded initialHistory disjoint
      member occurrence payload selected value matched
    simp [eventPositionAtoms, decodeAtoms, PositionAtom.decode, cursor, SourceTask.positions,
      SourceTask.cursorUpdates, SourceTask.cursors, payload, resultCursors,
      DeliveryPaths.result]

/-- Controls have no source label, by inspection of their event constructor. -/
theorem sourceEventTask_control {tasks matching index event} (control : ¬IsValue event)
    : sourceEventTask tasks matching index event = none := by
  cases event <;> simp_all [IsValue, sourceEventTask]

/-- One arbitrary admitted output decodes to its optional source contribution. Witness:
the value theorem or empty data effects for control output.
-/
theorem decode_eventPositionAtoms
    {containers : Bool}
    {work groups streams events matching failures initial slices positions}
    (explained : Explains work groups streams events matching failures)
    (seeded : WorkCursorSeed initial work slices)
    (initialHistory : CursorHistory initial positions)
    (disjoint
      : (positions
          ++ (sourceTasks [] none initial work).flatMap
              (SourceTask.positions true)).Nodup)
    {cut event} (selected : events[cut]? = some event)
    : decodeAtoms containers
        (sourceHistoryCursors (sourceTasks [] none initial work) matching events initial
          cut)
        (eventPositionAtoms event)
      = some
          (
            List.flatMap (SourceTask.positions containers)
              (sourceEventTask (sourceTasks [] none initial work) matching cut
                event).toList,
            sourceHistoryCursors (sourceTasks [] none initial work) matching events
              initial (cut + 1)
          ) := by
  have classified : IsValue event ∨ ¬IsValue event := by cases event <;> simp [IsValue]
  rcases classified with value | control
  · obtain ⟨task, member, same⟩ := publication_sourceTask explained selected value
    rw [sourceEventTask_value value member same, sourceHistoryCursors_step selected,
      sourceEventCursors_value value member same]
    simpa using decode_eventPositionAtoms_value explained seeded initialHistory disjoint
      member selected value same
  · rw [sourceEventTask_control control, sourceHistoryCursors_step selected,
      sourceEventCursors_control control]
    cases event <;> simp_all [IsValue, eventPositionAtoms, decodeAtoms]

/-- Every supplied history prefix decodes to exactly the selected source positions.
Witness: prefix induction and the atomic decoder theorem, retaining the exact residual
source cursor history. No terminal or error-freedom premise is needed.
-/
theorem decode_historyPositionAtoms
    {containers : Bool}
    {work groups streams events matching failures initial slices positions}
    (explained : Explains work groups streams events matching failures)
    (seeded : WorkCursorSeed initial work slices)
    (initialHistory : CursorHistory initial positions)
    (disjoint
      : (positions
          ++ (sourceTasks [] none initial work).flatMap
              (SourceTask.positions true)).Nodup)
    (cut : Nat) (bound : cut ≤ events.length)
    : decodeAtoms containers initial ((events.take cut).flatMap eventPositionAtoms)
      = some
          (
            List.flatMap (SourceTask.positions containers)
              (sourcePrefixTasks (sourceTasks [] none initial work) matching events cut),
            sourceHistoryCursors (sourceTasks [] none initial work) matching events
              initial cut
          ) := by
  induction cut with
  | zero => rfl
  | succ cut ih =>
      have earlier : cut < events.length := by omega
      have selected : events[cut]? = some events[cut] := List.getElem?_eq_getElem earlier
      have previous := ih (by omega)
      have current := decode_eventPositionAtoms (containers := containers)
        explained seeded initialHistory disjoint selected
      rw [List.take_succ_eq_append_getElem earlier, List.flatMap_append,
        List.flatMap_cons, List.flatMap_nil, List.append_nil, decodeAtoms_append,
        previous]
      simp only [sourcePrefixTasks, selected, Option.bind_some, Option.pure_def,
        List.flatMap_append]
      simp [current]

/-- Every admitted work history has a total absolute decoder with disjoint introduced
positions, before numeric-ID encoding and response batching. Witness: the exact prefix
decoder and source-label uniqueness; the full-history cut is its finite length.
-/
theorem explained_absolute_positions
    {work groups streams events matching failures initial slices positions}
    (explained : Explains work groups streams events matching failures)
    (seeded : WorkCursorSeed initial work slices)
    (initialHistory : CursorHistory initial positions)
    (disjoint
      : (positions
          ++ (sourceTasks [] none initial work).flatMap
              (SourceTask.positions true)).Nodup)
    : ∃ produced final,
        decodeAtoms true initial (events.flatMap eventPositionAtoms)
          = some (produced, final)
        ∧ (positions ++ produced).Nodup := by
  refine ⟨_, sourceHistoryCursors (sourceTasks [] none initial work) matching events initial
    events.length, ?_, sourcePrefix_positions_unique explained disjoint events.length⟩
  simpa only [List.take_length] using decode_historyPositionAtoms explained seeded
    initialHistory disjoint events.length (Nat.le_refl _)

/-- All admitted value/work groupings retain total, disjoint absolute position decoding.
Witness: their atoms equal an explained unbatched history's atoms, whose exact source
decoder is already proved. The remaining boundary is actual ID-based wire decoding.
-/
theorem admitted_absolute_positions
    {paths bound work history initial slices positions}
    (coherent : Semantics.MixedOwnerPaths.WorkAt paths bound work)
    (seeded : WorkCursorSeed initial work slices)
    (initialHistory : CursorHistory initial positions)
    (disjoint
      : (positions
          ++ (sourceTasks [] none initial work).flatMap
              (SourceTask.positions true)).Nodup)
    (admitted : AdmissiblePrefix work history ∨ AdmissibleRun work history)
    : ∃ produced final,
        decodeAtoms true initial (history.batches.flatten.flatMap eventPositionAtoms)
          = some (produced, final)
        ∧ (positions ++ produced).Nodup := by
  obtain ⟨events, matching, failures, explained, atoms⟩ :=
    admitted_positionAtoms coherent admitted
  rw [atoms]
  exact explained_absolute_positions explained seeded initialHistory disjoint

end GraphQL.IncrementalDelivery.Correctness
