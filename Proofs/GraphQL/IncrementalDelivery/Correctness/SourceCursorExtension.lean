import Proofs.GraphQL.IncrementalDelivery.Correctness.FailureCoverageAlgebra
import Proofs.GraphQL.IncrementalDelivery.Correctness.SourceListReconstruction

/-! Local source inventories survive assembly of enclosing response cursors. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open WorkQueueSemantics
open Semantics.MixedPaths

-----------------------------------------------------------------------------------------
-- Cursor extension preserves labels, payloads, indices, and all projected positions
-----------------------------------------------------------------------------------------

/-- Work descent keeps the ambient cursor environments generalized under seed inversion.
Witness: only sibling components recurse; payload children reseed independently.
-/
private theorem sourceTasks_cursorExtension_aux (work : Work)
    : ∀ before after slices,
        WorkCursorSeed before work slices
        → CursorExtends before after
        → ∀ address producer,
            sourceTasks address producer before work
            = sourceTasks address producer after work := by
  intro before after slices seeded extended address producer
  cases work with
  | empty => rfl
  | declareGroups groups tasks =>
      cases seeded with
      | declareGroups nested =>
          exact sourceTasks_cursorExtension_aux tasks before after slices nested extended address producer
  | combine left right =>
      cases seeded with
      | combine leftSeed rightSeed =>
          simp only [sourceTasks]
          rw [sourceTasks_cursorExtension_aux left _ _ _ leftSeed extended
              (address ++ [0]) producer,
            sourceTasks_cursorExtension_aux right _ _ _ rightSeed extended
              (address ++ [1]) producer]
  | executionGroup groups path result children => rfl
  | stream node items =>
      cases seeded with
      | stream cursor itemSeed =>
          simp only [sourceTasks, cursor, extended _ _ cursor]
termination_by sizeOf work

/-- Extending a valid cursor environment preserves the entire labelled source inventory.
Witness: work-seed descent. Siblings use the extended environment; deferred children
use their own payload seeds, and a stream's established starting index is unchanged.
No completion-success or error-count hypothesis is needed.
-/
theorem sourceTasks_cursorExtension {before after work slices}
    (seeded : WorkCursorSeed before work slices) (extended : CursorExtends before after)
    (address : Address) (producer : Option Occurrence)
    : sourceTasks address producer before work
      = sourceTasks address producer after work :=
  sourceTasks_cursorExtension_aux work before after slices seeded extended address
    producer

/-- Cursor extension also preserves any requested source-position projection.
Witness: equality of labelled source tasks, including their absolute item indices.
This includes leaf-only positions, not only the container-inclusive seed slices.
-/
theorem sourceTasks_positions_cursorExtension {before after work slices}
    (seeded : WorkCursorSeed before work slices) (extended : CursorExtends before after)
    (containers : Bool) (address : Address) (producer : Option Occurrence)
    : (sourceTasks address producer before work).flatMap (SourceTask.positions containers)
      = (sourceTasks address producer after work).flatMap
          (SourceTask.positions containers) := by
  rw [sourceTasks_cursorExtension seeded extended address producer]

-----------------------------------------------------------------------------------------
-- Initial object/list assembly does not move existing future work
-----------------------------------------------------------------------------------------

/-- Adding later object fields leaves earlier fields' seeded source tasks unchanged.
Witness: field-cursor concatenation and right extension; the earlier cursor lookups keep
their first matches even without a disjointness hypothesis.
-/
theorem sourceTasks_appendFields_left {path work slices}
    (left right : List (Name × ResponseValue))
    (seeded : WorkCursorSeed (ResponsePositions.fieldCursors path left) work slices)
    (address : Address) (producer : Option Occurrence)
    : sourceTasks address producer (ResponsePositions.fieldCursors path left) work
      = sourceTasks address producer (ResponsePositions.fieldCursors path (left ++ right))
          work := by
  rw [SourceReconstruction.fieldCursors_append]
  exact sourceTasks_cursorExtension seeded (.append_right _ _) address producer

/-- Adding earlier disjoint object fields leaves later fields' source tasks unchanged.
Witness: unique initial positions forbid the added cursors from shadowing later list
paths. Cursor provenance then supplies extension of each successful lookup.
This uniqueness is an initial-response property, not zero-error reconstruction.
-/
theorem sourceTasks_appendFields_right {path work slices}
    (left right : List (Name × ResponseValue))
    (seeded : WorkCursorSeed (ResponsePositions.fieldCursors path right) work slices)
    (unique : (ResponsePositions.fields true path (left ++ right)).Nodup)
    (address : Address) (producer : Option Occurrence)
    : sourceTasks address producer (ResponsePositions.fieldCursors path right) work
      = sourceTasks address producer (ResponsePositions.fieldCursors path (left ++ right))
          work := by
  have positions : (DeliveryPaths.fields true path right
      ++ DeliveryPaths.fields true path left).Nodup := by
    rw [responsePositions_fields_append] at unique
    rw [← source_fields_eq_positions, ← source_fields_eq_positions] at unique
    exact List.perm_append_comm.nodup_iff.mp unique
  have extended := CursorExtends.of_disjoint_history
    (fieldCursors_positions path right) (fieldCursors_positions path left) positions
  rw [SourceReconstruction.fieldCursors_append]
  exact sourceTasks_cursorExtension seeded extended address producer

/-- Adding an enclosing list cursor leaves its items' nested source tasks unchanged.
Witness: all item cursors are strictly below the list attachment, so the new list cursor
does not shadow any nested stream's starting index.
-/
theorem sourceTasks_enclosingList {path work slices} (data : List ResponseValue)
    (seeded : WorkCursorSeed (ResponsePositions.itemCursors path 0 data) work slices)
    (address : Address) (producer : Option Occurrence)
    : sourceTasks address producer (ResponsePositions.itemCursors path 0 data) work
      = sourceTasks address producer (ResponsePositions.listCursors path (.list data))
          work :=
  sourceTasks_cursorExtension seeded (SourceReconstruction.list_cursors_extend path data)
    address producer

end GraphQL.IncrementalDelivery.Correctness
