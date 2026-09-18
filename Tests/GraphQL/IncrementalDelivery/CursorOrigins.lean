import Proofs.GraphQL.IncrementalDelivery.Correctness.StreamCoordinates
import Proofs.GraphQL.IncrementalDelivery.Correctness.HistoryStreamCursors

/-! Deferred producers seed nested streams; equal payloads retain different occurrences. -/

namespace GraphQL.IncrementalDelivery.Tests.CursorOrigins
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.WorkScheduler
open GraphQL.IncrementalDelivery.Semantics.MixedPaths

def parent : DeliveryNode := { key := 0, path := [] }
def child : DeliveryNode := { key := 1, path := [.field "items"] }

def nested : Work :=
  .deferred [{ node := parent }] []
    (.ok ([("items", .list [.null, .null])], 0))
    (.stream child [(.ok (.null, 0), .empty)])

/-- A nested stream's cursor is absent initially; its deferred producer supplies index 2.
-/
example : ResponsePositions.cursorAt ([] : ResponsePositions.Cursors) child.path = none :=
  rfl

example
    : (sourceTasks [] none [] nested).map (fun task => (task.occurrence, task.index))
      = [(.deferred [], 0), (.item [0] 0, 2)] :=
  rfl

/-- The actual cursor-seed certificate agrees with the labelled deferred/item slices. -/
theorem nested_seed
    : WorkCursorSeed [] nested
        [
          [child.path, child.path ++ [.index 0], child.path ++ [.index 1]],
          [child.path ++ [.index 2]]
        ] :=
  .deferred (.stream rfl (.cons .empty .nil))

/-- Task lookup supplies a producer-origin witness without assuming publication order. -/
example
    : ∃ task ∈ sourceTasks [] none [] nested,
        task.occurrence = .item [0] 0
        ∧ task.producer = some (.deferred [])
        ∧ task.payload = .item child (.ok (.null, 0))
        ∧ task.Seeded [] (sourceTasks [] none [] nested) :=
  sourceTasks_task_seeded nested_seed (TaskAt.item (.deferred .root) rfl)

/-- Nested source labels preserve unique structural occurrences independently of cursors.
-/
example
    : (sourceTasks [] none [] nested).Pairwise
        (fun left right => left.occurrence ≠ right.occurrence) :=
  sourceTasks_unique _ _ _ _

/-- Two separate stream tasks cannot both own the same first source position. Raw Work
remains permissive; it is the generated execution's position certificate that excludes it.
-/
example
    : ¬((sourceTasks [] none [(child.path, 2)]
          (.append (.stream child [(.ok (.null, 0), .empty)])
            (.stream child [(.ok (.null, 0), .empty)]))).flatMap
          (SourceTask.positions true)).Nodup := by
  decide

/-- Replaying a deferred parent establishes its nested list cursor before any item arrives.
-/
example
    : ResponsePositions.cursorAt
        (sourceHistoryCursors (sourceTasks [] none [] nested)
          (fun index => if index = 0 then .deferred [] else .item [0] 0)
          [
            .groupValues parent
              [{ path := [], data := [("items", .list [.null, .null])] }],
            .streamValues child [{ item := .null }] [] []
          ] [] 1) child.path
      = some 2 :=
  rfl

/-- A subsequent item advances that cursor, retaining the producer-established offset. -/
example
    : ResponsePositions.cursorAt
        (sourceHistoryCursors (sourceTasks [] none [] nested)
          (fun index => if index = 0 then .deferred [] else .item [0] 0)
          [
            .groupValues parent
              [{ path := [], data := [("items", .list [.null, .null])] }],
            .streamValues child [{ item := .null }] [] []
          ] [] 2) child.path
      = some 3 :=
  rfl

end GraphQL.IncrementalDelivery.Tests.CursorOrigins
