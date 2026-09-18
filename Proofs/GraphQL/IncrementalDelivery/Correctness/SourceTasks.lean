import Proofs.GraphQL.IncrementalDelivery.Correctness.SourcePositions
import Proofs.GraphQL.IncrementalDelivery.WorkScheduler.PublicationOrder

/-! Proof-only labels connect scheduler occurrences to the execution's source slices.
The labels are derived from finite prepared work, not from a chosen output order.
-/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open WorkScheduler
open Semantics.MixedPaths

/-- A task's fixed source payload and producer, with its absolute streamed-item index.
The index is ignored for object tasks; it is not a runtime scheduler field.
-/
structure SourceTask where
  occurrence : Occurrence
  producer : Option Occurrence
  payload : Payload
  index : Nat

/-- The source positions introduced by this task, retaining containers when requested.
-/
def SourceTask.positions (containers : Bool) (task : SourceTask) : List ResponsePath :=
  match task.payload with
  | .object path result =>
      DeliveryPaths.result (ResponsePositions.fields containers path) result
  | .item node result =>
      DeliveryPaths.result
        (ResponsePositions.value containers (node.path ++ [.index task.index])) result

/-- List cursors introduced by the task's payload, excluding its enclosing stream cursor.
-/
def SourceTask.cursors (task : SourceTask) : ResponsePositions.Cursors :=
  match task.payload with
  | .object path result => resultCursors (ResponsePositions.fieldCursors path) result
  | .item node result =>
      resultCursors
        (ResponsePositions.listCursors (node.path ++ [.index task.index])) result

mutual
  /-- Label all source tasks with structural addresses and payload-seeded stream offsets.
  Missing seed lookups default to zero only to make this proof projection total; the
  execution certificate below requires every actual stream lookup to succeed.
  -/
  def sourceTasks (address : Address) (producer : Option Occurrence)
      (cursors : ResponsePositions.Cursors)
      : Work → List SourceTask
    | .empty => []
    | .append left right =>
        sourceTasks (address ++ [0]) producer cursors left
        ++ sourceTasks (address ++ [1]) producer cursors right
    | .deferred _ path result children =>
        let task : SourceTask := ⟨.deferred address, producer, .object path result, 0⟩
        task :: sourceTasks (address ++ [0]) (some task.occurrence) task.cursors children
    | .stream node items =>
        sourceItemTasks address producer node
          ((ResponsePositions.cursorAt cursors node.path).getD 0) 0 items

  /-- Label remaining stream items with both their task ordinal and absolute response index.
  -/
  def sourceItemTasks (address : Address) (producer : Option Occurrence)
      (node : DeliveryNode) (index ordinal : Nat)
      : List (Result ResponseValue × Work) → List SourceTask
    | [] => []
    | (result, children) :: rest =>
        let task : SourceTask :=
          ⟨.item address ordinal, producer, .item node result, index⟩
        task
        :: (sourceTasks (address ++ [ordinal]) (some task.occurrence)
              task.cursors children
            ++ sourceItemTasks address producer node (index + 1) (ordinal + 1) rest)
end

mutual
  /-- Labelled work positions are exactly the execution's seeded slices. Witness:
  structural descent through the shared cursor certificate, with no schedule choice.
  -/
  theorem sourceTasks_positions {cursors work slices}
      (seeded : WorkCursorSeed cursors work slices) (address : Address)
      (producer : Option Occurrence)
      : (sourceTasks address producer cursors work).map (SourceTask.positions true)
        = slices := by
    cases seeded with
    | empty => rfl
    | append left right =>
        simp only [sourceTasks, List.map_append, sourceTasks_positions left,
          sourceTasks_positions right]
    | deferred children =>
        simp only [sourceTasks, List.map_cons, SourceTask.cursors, SourceTask.positions,
          sourceTasks_positions children, ← funext (source_fields_eq_positions true _)]
    | stream cursor items =>
        simp only [sourceTasks, cursor, Option.getD_some]
        exact sourceItemTasks_positions items address producer _ 0
  termination_by sizeOf work

  /-- Labelled stream-item positions retain the certificate's successive absolute indices.
  Witness: simultaneous induction through each payload's child work and the item tail.
  -/
  theorem sourceItemTasks_positions {path index items slices}
      (seeded : ItemCursorSeed path index items slices) (address : Address)
      (producer : Option Occurrence) (node : DeliveryNode) (ordinal : Nat)
      (path_eq : node.path = path := by rfl)
      : (sourceItemTasks address producer node index ordinal items).map
          (SourceTask.positions true)
        = slices := by
    cases seeded with
    | nil => rfl
    | cons children rest =>
        simp only [sourceItemTasks, List.map_cons, List.map_append, SourceTask.cursors,
          SourceTask.positions, path_eq, sourceTasks_positions children,
          sourceItemTasks_positions rest address producer node (ordinal + 1) path_eq,
          ← funext (source_value_eq_positions true _)]
  termination_by sizeOf items
end

/-- Actual prepared root work has a labelled, globally disjoint source-position inventory.
Witness: the existing execution ownership certificate and its exact labelled projection.
-/
theorem executeRoot_sourceTasks (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (parentType : Name)
    (source : ResolverValue ObjectRef) (selections : List Selection) (state : Nat)
    : let completed :=
        ((executeRootSelectionSetCore schema resolvers variables fuel parentType source
            selections).run
          state).1
      let response := selectionSetResultToResponse completed.result
      let tasks :=
        sourceTasks [] none (ResponsePositions.listCursors [] response.data)
          completed.work
      (ResponsePositions.value true [] response.data
        ++ tasks.flatMap (SourceTask.positions true)).Nodup := by
  obtain ⟨slices, seeded, disjoint⟩ := executeRoot_source_positions schema resolvers
    variables fuel parentType source selections state
  simpa only [List.flatMap, sourceTasks_positions seeded] using disjoint

end GraphQL.IncrementalDelivery.Correctness
