import Proofs.GraphQL.IncrementalDelivery.Correctness.SourceReconstructionAlgebra
import Proofs.GraphQL.IncrementalDelivery.Correctness.SourceTasks
import Proofs.GraphQL.IncrementalDelivery.Correctness.TypedPositions

/-! Typed source slices and occurrence-labelled inventory share the same exact contents. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open SourceReconstruction

/-- A source label retains both its absolute positions and scalar/container tags. -/
def SourceTask.entries (task : SourceTask) : List TypedResponse.Entry :=
  match task.payload with
  | .object path result => TypedResponse.result (TypedResponse.fields path) result
  | .item node result =>
      TypedResponse.result (TypedResponse.value (node.path ++ [.index task.index])) result

/-- Typed entry projection is exactly the label's public position contribution.
Witness: payload case analysis and the typed-value position identities.
-/
theorem SourceTask.entries_positions (task : SourceTask) (containers : Bool)
    : task.entries.filterMap (TypedResponse.entryPath containers)
      = task.positions containers := by
  cases payload : task.payload <;> simp only [SourceTask.entries, SourceTask.positions, payload]
  all_goals
    unfold TypedResponse.result
    split <;> simp [DeliveryPaths.result,
      TypedResponse.fields_entryPaths, TypedResponse.value_entryPaths,
      source_fields_eq_positions, source_value_eq_positions]

/-- Forgetting all entry tags yields exactly the container-inclusive source positions. -/
theorem SourceTask.entries_paths (task : SourceTask)
    : task.entries.map Prod.fst = task.positions true := by
  have projection : TypedResponse.entryPath true = fun entry => some entry.1 := by
    funext entry
    rcases entry with ⟨path, atom⟩
    cases atom <;> rfl
  simpa only [projection, List.filterMap_eq_map'] using task.entries_positions true

mutual
  /-- Labelling work preserves an exact typed-slice witness, by structural recursion. -/
  theorem sourceTasks_entries (address producer cursors work)
      : WorkEntries work
          ((sourceTasks address producer cursors work).map SourceTask.entries) := by
    cases work with
    | empty => exact .empty
    | combine left right =>
        simpa [sourceTasks] using WorkEntries.combine
          (sourceTasks_entries (address ++ [0]) producer cursors left)
          (sourceTasks_entries (address ++ [1]) producer cursors right)
    | executionGroup groups path result children =>
        exact .executionGroup (sourceTasks_entries _ _ _ children)
    | stream node items => exact .stream (sourceItemTasks_entries _ _ _ _ _ _)
  termination_by sizeOf work

  /-- Item labels preserve typed slices at their stored absolute index, by item
  descent.
  -/
  theorem sourceItemTasks_entries (address producer node index ordinal items)
      : ItemEntries node.path index items
          ((sourceItemTasks address producer node index ordinal items).map
            SourceTask.entries) := by
    cases items with
    | nil => exact .nil
    | cons entry rest =>
        cases entry with
        | mk result children =>
            simpa [sourceItemTasks, SourceTask.entries] using ItemEntries.cons
              (sourceTasks_entries _ _ _ children)
              (sourceItemTasks_entries address producer node (index + 1) (ordinal + 1) rest)
  termination_by sizeOf items
end

namespace SourceReconstruction
open TypedResponse

mutual
  /-- Slice counts depend only on work shape, not ghost offsets or typed payloads. -/
  theorem WorkEntries.length_eq {work left right}
      (hl : WorkEntries work left) (hr : WorkEntries work right)
      : left.length = right.length := by
    cases hl with
    | empty =>
        cases hr; rfl
    | combine hla hlb =>
        cases hr with
        | combine hra hrb =>
            simp only [List.length_append, hla.length_eq hra, hlb.length_eq hrb]
    | executionGroup hlc =>
        cases hr with
        | executionGroup hrc => simp only [List.length_cons, hlc.length_eq hrc]
    | stream hli =>
        cases hr with
        | stream hri => exact hli.length_eq hri

  /-- Item slice counts ignore the starting offset, by simultaneous structural descent. -/
  theorem ItemEntries.length_eq {path otherPath index otherIndex items left right}
      (hl : ItemEntries path index items left)
      (hr : ItemEntries otherPath otherIndex items right)
      : left.length = right.length := by
    cases hl with
    | nil =>
        cases hr; rfl
    | cons hlc hlt =>
        cases hr with
        | cons hrc hrt =>
            simp only [List.length_cons, List.length_append, hlc.length_eq hrc, hlt.length_eq hrt]
end

/-- The same payload at two positions has identical typed entries if its paths agree.
Witness: successful values expose their root path; failed results contribute no entries.
-/
theorem result_value_of_paths {left right : ResponsePath} (outcome : Result ResponseValue)
    (same
      : (result (value left) outcome).map Prod.fst
        = (result (value right) outcome).map Prod.fst)
    : result (value left) outcome = result (value right) outcome := by
  cases outcome with
  | error _ => rfl
  | ok pair =>
      rcases pair with ⟨data, errors⟩
      have paths : left = right := by
        cases data <;> simp [result, value] at same
        all_goals first | exact same | exact same.1
      rw [paths]

mutual
  /-- Typed slices of fixed work are determined by their path slices. Witness: structural
  descent, splitting combine witnesses using their work-determined slice counts.
  -/
  theorem WorkEntries.of_paths {work left right}
      (hl : WorkEntries work left) (hr : WorkEntries work right)
      (same : entryPaths left = entryPaths right)
      : left = right := by
    cases hl with
    | empty =>
        cases hr; rfl
    | combine hla hlb =>
        cases hr with
        | combine hra hrb =>
            simp only [entryPaths, List.map_append] at same
            obtain ⟨first, rest⟩ := List.append_inj same (by
              simpa only [List.length_map] using hla.length_eq hra)
            rw [hla.of_paths hra first, hlb.of_paths hrb rest]
    | executionGroup hlc =>
        cases hr with
        | executionGroup hrc =>
            have rest := (List.cons.inj same).2
            rw [hlc.of_paths hrc rest]
    | stream hli =>
        cases hr with
        | stream hri => exact hli.of_paths hri same

  /-- The same item payloads and path slices determine typed slices even with different
  existential offset witnesses. Failed items need not determine an offset.
  -/
  theorem ItemEntries.of_paths {path index otherIndex items left right}
      (hl : ItemEntries path index items left)
      (hr : ItemEntries path otherIndex items right)
      (same : entryPaths left = entryPaths right)
      : left = right := by
    cases hl with
    | nil =>
        cases hr; rfl
    | cons hlc hlt =>
        cases hr with
        | cons hrc hrt =>
            obtain ⟨head, rest⟩ := List.cons.inj same
            obtain ⟨children, tail⟩ := List.append_inj
              (by simpa only [List.map_append] using rest) (by
                simpa only [List.length_map] using hlc.length_eq hrc)
            rw [result_value_of_paths _ head, hlc.of_paths hrc children, hlt.of_paths hrt tail]
end

end SourceReconstruction

/-- A typed source reconstruction and its cursor seed identify exactly the labelled
inventory, not just its positions. Witness: unique seeded paths and typed path
injectivity.
-/
theorem sourceTasks_typed {cursors work slices}
    (typed : WorkEntries work slices)
    (seeded : Semantics.MixedPaths.WorkCursorSeed cursors work (entryPaths slices))
    : (sourceTasks [] none cursors work).map SourceTask.entries = slices := by
  apply (sourceTasks_entries [] none cursors work).of_paths typed
  simpa only [entryPaths, List.map_map, Function.comp_def, SourceTask.entries_paths]
    using sourceTasks_positions seeded [] none

end GraphQL.IncrementalDelivery.Correctness
