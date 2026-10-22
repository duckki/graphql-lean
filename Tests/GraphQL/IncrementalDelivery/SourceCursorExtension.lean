import Proofs.GraphQL.IncrementalDelivery.Correctness.SourceCursorExtension

/-! Enclosing initial fields preserve future stream offsets without zero-error premises. -/

namespace GraphQL.IncrementalDelivery.Tests.SourceCursorExtension
open GraphQL.IncrementalDelivery.Execution
open Correctness
open WorkQueueSemantics
open Semantics.MixedPaths

private def node : DeliveryNode := { ref := 0, path := [.field "values"] }

private def work : Work :=
  .stream node [({ result := .ok (.scalar "later", 3) }, .empty)]

private def fields : List (Name × ResponseValue) :=
  [("values", .list [.null])]

private def earlier : List (Name × ResponseValue) :=
  [("other", .list [.scalar "a", .scalar "b"])]

/-- The future value's coordinate is seeded by its actual one-item initial list.
Witness: the stream seed certificate, allowing counted errors in its retained payload.
-/
private theorem seeded
    : WorkCursorSeed (ResponsePositions.fieldCursors [] fields) work
        [[[.field "values", .index 1]]] := by exact .stream (by cbv) (.cons .empty .nil)

/-- Earlier disjoint list fields do not move the retained item from index one.
Witness: full source-inventory equality under field-cursor assembly, not just path count.
-/
example
    : sourceTasks [] none (ResponsePositions.fieldCursors [] fields) work
      = sourceTasks [] none (ResponsePositions.fieldCursors [] (earlier ++ fields))
          work := by
  apply sourceTasks_appendFields_right earlier fields seeded
  decide

/-- The retained scalar has its original absolute coordinate after object assembly.
Witness: reduction of the assembled cursor/source projection with three counted errors.
-/
example
    : List.flatMap (SourceTask.positions false)
        (sourceTasks [] none (ResponsePositions.fieldCursors [] (earlier ++ fields)) work)
      = [[.field "values", .index 1]] := by cbv

/-- Both leaf-only and container-inclusive source positions survive this assembly.
Witness: equality of entire source task lists, retaining payloads and absolute indices.
-/
example (containers : Bool)
    : List.flatMap (SourceTask.positions containers)
        (sourceTasks [] none (ResponsePositions.fieldCursors [] fields) work)
      = List.flatMap (SourceTask.positions containers)
          (sourceTasks [] none (ResponsePositions.fieldCursors [] (earlier ++ fields))
            work) := by
  rw [sourceTasks_appendFields_right earlier fields seeded (by decide) [] none]

/-- Duplicate earlier fields can shadow a cursor, so the prepend condition is necessary.
Witness: the earlier duplicate introduces index zero, changing the retained coordinate.
The left-append theorem has no such condition because existing first matches win.
-/
example
    : List.flatMap (SourceTask.positions false)
        (sourceTasks [] none
          (ResponsePositions.fieldCursors [] ([("values", .list [])] ++ fields)) work)
      = [[.field "values", .index 0]] := by cbv

#print axioms sourceTasks_cursorExtension
#print axioms sourceTasks_appendFields_right

end GraphQL.IncrementalDelivery.Tests.SourceCursorExtension
