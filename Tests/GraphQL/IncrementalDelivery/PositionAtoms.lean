import Proofs.GraphQL.IncrementalDelivery.Correctness.HistoryAbsolutePositions

/-! Coalesced streamed values preserve indexed positions and nested list cursors. -/

namespace GraphQL.IncrementalDelivery.Tests.PositionAtoms
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Correctness

def path : ResponsePath := [.field "items"]
def node : DeliveryNode := { key := 0, path }
def values : List ResponseValue := [.list [.null], .list [.null, .null]]

/-- Coalescing keeps one absolute atom per item, even when the values are themselves lists.
-/
example
    : eventPositionAtoms (.streamValues node (values.map (fun item => { item })) [] [])
      = values.map (PositionAtom.item path) := by rfl

/-- Separate item decoding and one list patch have equal positions and cursor lookups.
This checks the general theorem at a nonzero start with nested list cursors.
-/
example
    : ∃ final,
        decodeAtoms true [(path, 3)] (values.map (PositionAtom.item path))
          = some (ResponsePositions.items true path 3 values, final)
        ∧ CursorEquivalent final
            ((path, 5) :: ResponsePositions.itemCursors path 3 values ++ [(path, 3)]) :=
  decodeAtoms_items true path values [(path, 3)] 3 rfl

/-- The outer cursor advances twice; each nested list retains its own observed length. -/
example
    : ∃ positions final,
        decodeAtoms true [(path, 3)] (values.map (PositionAtom.item path))
          = some (positions, final)
        ∧ ResponsePositions.cursorAt final path = some 5
        ∧ ResponsePositions.cursorAt final (path ++ [.index 3]) = some 1
        ∧ ResponsePositions.cursorAt final (path ++ [.index 4]) = some 2 := by
  refine ⟨_, _, rfl, rfl, rfl, rfl⟩

/-- Absolute decoding rejects an unseeded streamed list rather than inventing index zero.
-/
example : decodeAtoms true [] [.item path .null] = none := rfl

end GraphQL.IncrementalDelivery.Tests.PositionAtoms
