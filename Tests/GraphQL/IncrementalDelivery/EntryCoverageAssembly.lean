import Proofs.GraphQL.IncrementalDelivery.Correctness.EntryCoverageAssembly

/-! Seeded assembly retains streamed data and nullable failure evidence simultaneously. -/

namespace GraphQL.IncrementalDelivery.Tests.EntryCoverageAssembly
open GraphQL.IncrementalDelivery.Execution
open Correctness WorkQueueSemantics Semantics.MixedPaths

private def xs : ResponsePath := [.field "xs"]
private def missing : ResponsePath := [.field "missing"]
private def streamNode : DeliveryNode := { ref := 7, path := xs }

private def leftInitial : List (Name × ResponseValue) :=
  [("xs", .list [.scalar "a"])]

private def rightInitial : List (Name × ResponseValue) := [("missing", .object [])]

private def leftWork : Work :=
  .stream streamNode [({ result := .ok (.scalar "b", 2) }, .empty)]

private def rightWork : Work :=
  .executionGroup [] (missing ++ [.field "child"]) ({ result := .error 1 }) .empty

private def leftReference : List (Name × ResponseValue) :=
  [("xs", .list [.scalar "a", .scalar "b"])]

private def rightReference : List (Name × ResponseValue) := [("missing", .null)]

/-- The stream begins after the one initial item; its successful counted errors are kept. -/
private theorem leftSeed
    : WorkCursorSeed (ResponsePositions.fieldCursors [] leftInitial) leftWork
        [[xs ++ [.index 1]]] := by
  apply WorkCursorSeed.stream (index := 1)
  · rfl
  · exact .cons .empty .nil

/-- Failed object payloads need no initial cursor; their child work is empty. -/
private theorem rightSeed
    : WorkCursorSeed (ResponsePositions.fieldCursors [] rightInitial) rightWork [[]] :=
  .executionGroup .empty

/-- All reference list positions are initially present or in the actual stream payload. -/
private theorem leftCovered (containers : Bool)
    : EntriesCovered containers (TypedResponse.fields [] leftReference)
        (preparedFieldPositions containers [] leftInitial leftWork) leftWork := by
  apply EntriesCovered.of_visiblePaths_subset
  rw [visibleEntryPaths_fields]
  cases containers <;> intro path member
  all_goals
    cbv at member ⊢
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using member

/-- The ordinary nullable field is explained by the failed task below its partial object. -/
private theorem rightCovered (containers : Bool)
    : EntriesCovered containers (TypedResponse.fields [] rightReference)
        (preparedFieldPositions containers [] rightInitial rightWork) rightWork := by
  intro entry member _
  have same : entry = (missing, .null) := by
    simpa [TypedResponse.fields, TypedResponse.value, rightReference, missing]
      using member
  subst entry
  unfold rightWork
  exact Or.inr ⟨_, _, _, .object (missing ++ [.field "child"]) (.error 1),
    (StructuralEquivalence.TaskAt.executionGroup .root).toCurrent,
    rfl, Or.inr ⟨rfl, ⟨[.field "child"], rfl⟩⟩⟩

/-- Object assembly retains successful stream data and the tagged null failure together. -/
example (containers : Bool)
    : EntriesCovered containers
        (TypedResponse.value [] (.object (leftReference ++ rightReference)))
        (preparedValuePositions containers [] (.object (leftInitial ++ rightInitial))
          (.combine leftWork rightWork)) (.combine leftWork rightWork) := by
  apply EntriesCovered.object
  rw [TypedResponse.fields_append]
  exact EntriesCovered.append_fields leftInitial rightInitial
    (leftCovered containers) (rightCovered containers) leftSeed rightSeed (by decide)

/-- The assembled typed witness also discharges the existing public prepared comparison. -/
example (containers : Bool)
    : PreparedResponseCovers (.object (leftReference ++ rightReference))
        { data := .object (leftInitial ++ rightInitial) }
        (.combine leftWork rightWork) containers := by
  apply EntriesCovered.to_prepared
  · apply EntriesCovered.object
    rw [TypedResponse.fields_append]
    exact EntriesCovered.append_fields leftInitial rightInitial
      (leftCovered containers) (rightCovered containers) leftSeed rightSeed (by decide)
  · decide

/-- List wrapping retains a null failure beneath item zero and item one's empty container. -/
example (containers : Bool)
    : EntriesCovered containers
        (TypedResponse.value [] (.list [.null, .list []]))
        (preparedValuePositions containers [] (.list [.object [], .list []])
          (.executionGroup [] [.index 0, .field "child"] ({ result := .error 1 }) .empty))
        (.executionGroup [] [.index 0, .field "child"] ({ result := .error 1 })
          .empty) := by
  apply EntriesCovered.list
  · intro entry member visible
    change entry ∈ [([.index 0], .null), ([.index 1], .list)] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact Or.inr ⟨_, _, _, .object [.index 0, .field "child"] (.error 1),
        (StructuralEquivalence.TaskAt.executionGroup .root).toCurrent,
        rfl, Or.inr ⟨rfl, ⟨[.field "child"], rfl⟩⟩⟩
    · have flag : containers = true := visible
      exact Or.inl (by simp [preparedItemPositions, ResponsePositions.items,
        ResponsePositions.value, flag])
  · exact .executionGroup .empty

/-- Item concatenation keeps the nested stream at item zero and a failure under item one.
The streamed scalar has a counted error; the second initial object has no leaf positions.
-/
example (containers : Bool)
    : let first : Work :=
        .stream { ref := 8, path := [.index 0] }
          [({ result := .ok (.scalar "b", 2) }, .empty)]
      let second : Work :=
        .executionGroup [] [.index 1, .field "child"] ({ result := .error 1 }) .empty
      EntriesCovered containers
        [([.index 0, .index 1], .scalar "b"), ([.index 1], .null)]
        (preparedItemPositions containers [] 0 [.list [.scalar "a"], .object []]
          (.combine first second)) (.combine first second) := by
  dsimp only
  apply EntriesCovered.append_items
    (leftReference := [([.index 0, .index 1], .scalar "b")])
    (rightReference := [([.index 1], .null)]) [.list [.scalar "a"]] [.object []]
  · intro entry member _
    obtain rfl := List.mem_singleton.mp member
    exact Or.inl (by cases containers <;> decide)
  · intro entry member _
    obtain rfl := List.mem_singleton.mp member
    exact Or.inr ⟨_, _, _, .object [.index 1, .field "child"] (.error 1),
      (StructuralEquivalence.TaskAt.executionGroup .root).toCurrent,
      rfl, Or.inr ⟨rfl, ⟨[.field "child"], rfl⟩⟩⟩
  · apply WorkCursorSeed.stream (index := 1)
    · rfl
    · exact .cons .empty .nil
  · exact .executionGroup .empty
  · decide

#print axioms EntriesCovered.append_fields
#print axioms EntriesCovered.append_items
#print axioms EntriesCovered.list

end GraphQL.IncrementalDelivery.Tests.EntryCoverageAssembly
