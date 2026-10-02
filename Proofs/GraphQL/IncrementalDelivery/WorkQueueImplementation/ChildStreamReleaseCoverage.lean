import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ChildStreamInventory
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamRegistry

/-! Successful group flushing releases every registered stream attached to a selected task. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Complete selection covers streams, not only the selected producer values
-----------------------------------------------------------------------------------------

/-- A group's flush releases each registered child stream of every findable membership.
Witness: complete occurrence selection retains all linked keys; cleanup preserves the
registry, so the final stream lookup cannot discard this key. Duplicate memberships are
permitted, and no source, health, or output-admission premise is needed.
-/
theorem State.finishGroupSuccess_childStream_covered {queue : State} (group : GroupNode)
    {occurrence node key stream} (member : occurrence ∈ group.tasks)
    (found : queue.taskNode? occurrence = some node) (linked : key ∈ node.childStreams)
    (registered : queue.stream? key = some stream)
    : stream.node ∈ (queue.finishGroupSuccess group).2.2.newStreams := by
  obtain ⟨selected, _, _, _, streams, _, _, covered, _⟩ :=
    flushGroupTask_completeWitness queue group.tasks [] []
  let flushed := group.tasks.foldl flushGroupTask (queue, [], [])
  have exactStreams : flushed.2.2 = selected.flatMap TaskNode.childStreams := streams
  change stream.node ∈ flushed.2.2.filterMap
    (fun key => ((queue.finishGroupSuccess group).1.stream? key).map Stream.node)
  rw [exactStreams]
  apply List.mem_filterMap.mpr
  refine ⟨
    key,
    List.mem_flatMap.mpr ⟨node, covered occurrence member node found, linked⟩,
    ?_
  ⟩
  have retained : (queue.finishGroupSuccess group).1.stream? key = some stream := by
    simpa only [State.stream?, State.finishGroupSuccess_streams] using registered
  simp only [retained, Option.map_some]

/-- Registered child-link inventory turns each selected link into an actual notice key.
Witness: registry membership yields a successful lookup; complete flush coverage releases
its descriptor even if raw registry entries repeat a key.
-/
theorem State.ChildStreamInventory.finishGroupSuccess_childKey_covered {queue : State}
    (inventory : queue.ChildStreamInventory) (group : GroupNode) {occurrence node key}
    (member : occurrence ∈ group.tasks) (found : queue.taskNode? occurrence = some node)
    (linked : key ∈ node.childStreams)
    : key
      ∈ (queue.finishGroupSuccess group).2.2.newStreams.map
          Execution.DeliveryNode.key := by
  have registered := (inventory node (State.taskNode?_some found).1).2 linked
  obtain ⟨stream, included, same⟩ := List.mem_map.mp registered
  have existsLookup : ∃ selected, queue.stream? key = some selected := by
    apply Option.isSome_iff_exists.mp
    change (queue.streams.find? (fun candidate => candidate.node.key == key)).isSome = true
    rw [List.isSome_find?]
    exact List.any_eq_true.mpr ⟨stream, included, beq_iff_eq.mpr same⟩
  obtain ⟨selected, lookup⟩ := existsLookup
  exact List.mem_map.mpr ⟨selected.node,
    State.finishGroupSuccess_childStream_covered group member found linked lookup,
    (State.stream?_some lookup).2⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
