import Proofs.GraphQL.IncrementalDelivery.Correctness.EntryCoverageRetention

/-! Deferred and streamed retention preserves real nullable-failure evidence. -/

namespace GraphQL.IncrementalDelivery.Tests.EntryCoverageRetention
open GraphQL.IncrementalDelivery.Execution
open Correctness WorkQueueSemantics

private def userPath : ResponsePath := [.field "user"]
private def userInitial : List (Name × ResponseValue) := [("user", .object [])]

private def userChildren : Work :=
  .executionGroup [] (userPath ++ [.field "required"]) ({ result := .error 1 }) .empty

/-- A nullable ordinary user has a real failed task below the initial partial user. -/
private theorem userCovered (containers : Bool)
    : EntriesCovered containers [(userPath, .null)]
        (preparedFieldPositions containers [] userInitial userChildren) userChildren := by
  intro entry member _
  obtain rfl := List.mem_singleton.mp member
  unfold userChildren
  exact Or.inr ⟨_, _, _, .object (userPath ++ [.field "required"]) (.error 1),
    (StructuralEquivalence.TaskAt.executionGroup .root).toCurrent,
    rfl, Or.inr ⟨rfl, ⟨[.field "required"], rfl⟩⟩⟩

/-- A successful deferred payload can preserve a failed child and nullable ordinary root.
Its counted errors and external cursor table do not affect this pure comparison.
-/
example (containers : Bool) (cursors : ResponsePositions.Cursors) (errors : Nat)
    : EntriesCovered containers [(userPath, .null)]
        ((sourceTasks [] none cursors
            (.executionGroup [] [] ({ result := .ok (userInitial, errors) })
              userChildren)).flatMap
          (SourceTask.positions containers))
        (.executionGroup [] [] ({ result := .ok (userInitial, errors) }) userChildren) :=
  (userCovered containers).executionGroup userInitial errors [] cursors

private def node : DeliveryNode := { ref := 9, path := [.field "xs"] }
private def itemPath : ResponsePath := node.path ++ [.index 4]

private def itemInitial : ResponseValue :=
  .object [("ok", .scalar "x"), ("child", .object [])]

private def itemChildren : Work :=
  .executionGroup [] (itemPath ++ [.field "child", .field "required"])
    ({ result := .error 1 }) .empty

private def items : List (TaskOutcome ResponseValue × Work) :=
  [
    ({ result := .ok (.scalar "a", 2) }, .empty),
    ({ result := .ok (itemInitial, 3) }, itemChildren)
  ]

private def itemReference : List TypedResponse.Entry :=
  [(itemPath ++ [.field "ok"], .scalar "x"), (itemPath ++ [.field "child"], .null)]

/-- One actual item supplies a scalar and a failed nullable child, without zero errors. -/
private theorem itemCovered (containers : Bool)
    : EntriesCovered containers itemReference
        (preparedValuePositions containers itemPath itemInitial itemChildren)
        itemChildren := by
  intro entry member _
  change entry ∈ [(itemPath ++ [.field "ok"], .scalar "x"),
    (itemPath ++ [.field "child"], .null)] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact Or.inl (by cases containers <;> decide)
  · unfold itemChildren
    exact Or.inr ⟨_, _, _,
      .object (itemPath ++ [.field "child", .field "required"]) (.error 1),
      (StructuralEquivalence.TaskAt.executionGroup .root).toCurrent,
      rfl, Or.inr ⟨rfl, ⟨[.field "required"], by simp [Payload.path, List.append_assoc]⟩⟩⟩

/-- Retention uses absolute index four: initial count three plus item ordinal one.
The successful scalar and failed child both survive retention inside the outer stream.
-/
example (containers : Bool)
    : EntriesCovered containers itemReference
        ((sourceTasks [] none [(node.path, 3)] (.stream node items)).flatMap
          (SourceTask.positions containers)) (.stream node items) := by
  exact EntriesCovered.streamItem (index := 3) (offset := 1) (initial := itemInitial)
    (errors := 3) (children := itemChildren) (itemCovered containers) rfl rfl

/-- A missing cursor defaults to zero in the total projection and changes delivered paths.
The retention theorem requires the real successful cursor, not this fallback projection.
-/
example
    : itemPath ++ [.field "ok"]
      ∉ (sourceTasks [] none [] (.stream node items)).flatMap
          (SourceTask.positions false) := by
  decide

/-- Separate retained partitions combine scalar data and null failure explanations. -/
example (containers : Bool)
    : let left := .executionGroup [] [] ({ result := .ok (userInitial, 0) }) userChildren
      let right := .stream node items
      EntriesCovered containers ([(userPath, .null)] ++ itemReference)
        ((sourceTasks [] none [(node.path, 3)] (.combine left right)).flatMap
          (SourceTask.positions containers)) (.combine left right) := by
  exact EntriesCovered.combine_sources
    ((userCovered containers).executionGroup userInitial 0 [] [(node.path, 3)])
    (EntriesCovered.streamItem (index := 3) (offset := 1) (initial := itemInitial)
      (errors := 3) (children := itemChildren) (itemCovered containers) rfl rfl)

#print axioms EntriesCovered.executionGroup
#print axioms EntriesCovered.streamItem
#print axioms EntriesCovered.combine_sources

end GraphQL.IncrementalDelivery.Tests.EntryCoverageRetention
