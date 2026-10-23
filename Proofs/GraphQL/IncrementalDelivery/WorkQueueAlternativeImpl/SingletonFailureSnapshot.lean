import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ResourceHandoff
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskLookupUpdates

/-! A singleton failure exposes precisely the rejection its handler immediately records.
This local equality does not flatten multi-input host batches or their cache snapshots.
-/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue

private theorem putTaskNode_idempotent (queue : State) (node : TaskNode)
    : (queue.putTaskNode node).putTaskNode node = queue.putTaskNode node := by
  unfold State.putTaskNode
  simp only [List.map_map]
  congr 1
  apply List.map_congr_left
  intro old member
  dsimp only [Function.comp_apply]
  by_cases same : old.task.occurrence = node.task.occurrence
  · simp only [occurrence_beq_iff_eq, same, ↓reduceIte]
  · simp only [occurrence_beq_iff_eq, same, ↓reduceIte]

/-- Exposing a failure immediately before consuming that same failure is redundant. -/
theorem State.taskFailure_cacheSelf (queue : State) (occurrence errors)
    : (queue.cacheTaskFailures [(occurrence, errors)]).taskFailure occurrence errors
      = queue.taskFailure occurrence errors := by
  cases found : queue.taskNode? occurrence with
  | none => simp only [State.cacheTaskFailures, List.foldl_cons, List.foldl_nil, found]
  | some node =>
      have identity := (State.taskNode?_some found).2
      have lookup := State.putTaskNode_lookup_same found
        { node with rejection := some errors } identity
      simp only [State.cacheTaskFailures, List.foldl_cons, List.foldl_nil, found,
        State.taskFailure, lookup, putTaskNode_idempotent]

/-- Singleton host availability changes no reference dispatch result. -/
theorem State.handleGraphEvent_singletonSnapshot (queue : State) (event : GraphEvent)
    : queue.handleGraphEvent event (GraphEvent.availableFailures [event])
      = queue.handleGraphEvent event := by
  cases event <;> simp only [GraphEvent.availableFailures, List.filterMap_cons,
    List.filterMap_nil, State.handleGraphEvent, State.cacheTaskFailures, List.foldl_nil,
    ]
  exact congrArg (fun result => (result.1, result.2, []))
    (queue.taskFailure_cacheSelf _ _)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement

/-- Native failed-task disposal also sees the same already-recorded singleton rejection. -/
theorem State.taskFailure_cacheSelf (state : State) (occurrence errors)
    : ({ state with queue := state.queue.cacheTaskFailures [(occurrence, errors)] }
        : State).taskFailure
        occurrence errors
      = state.taskFailure occurrence errors := by
  cases found : state.queue.taskNode? occurrence with
  | none =>
      simp only [ReferenceWorkQueue.State.cacheTaskFailures, List.foldl_cons,
        List.foldl_nil, found]
  | some node =>
      have identity := (ReferenceWorkQueue.State.taskNode?_some found).2
      have lookup := ReferenceWorkQueue.State.putTaskNode_lookup_same found
        { node with rejection := some errors } identity
      simp only [ReferenceWorkQueue.State.cacheTaskFailures, List.foldl_cons,
        List.foldl_nil, found, State.taskFailure, lookup,
        ReferenceWorkQueue.putTaskNode_idempotent]

/-- A singleton batch's failure snapshot leaves native state, notices and effects unchanged. -/
theorem State.handleGraphEvent_singletonSnapshot (state : State) (event : GraphEvent)
    : state.handleGraphEvent event
        (ReferenceWorkQueue.GraphEvent.availableFailures [event])
      = state.handleGraphEvent event := by
  cases event <;> simp only [ReferenceWorkQueue.GraphEvent.availableFailures,
    List.filterMap_cons, List.filterMap_nil, State.handleGraphEvent,
    ReferenceWorkQueue.State.cacheTaskFailures, List.foldl_nil,
    ]
  exact congrArg (fun result =>
    (result.1, result.2.1, result.2.2.flatMap CleanupTarget.effects, []))
    (State.taskFailure_cacheSelf state _ _)
  all_goals rfl

/-- Batch accumulation preserves the native singleton dispatch equality. -/
theorem GraphBatchResult.handleGraphEvent_singletonSnapshot
    (result : GraphBatchResult) (event : GraphEvent)
    : result.handleGraphEvent event
        (ReferenceWorkQueue.GraphEvent.availableFailures [event])
      = result.handleGraphEvent event := by
  simp only [GraphBatchResult.handleGraphEvent, State.handleGraphEvent_singletonSnapshot]

/-- Resource observation requests exactly the same singleton cleanup effects. -/
theorem ResourceState.observeDispatch_singletonSnapshot (resources : ResourceState)
    (inventories : ProducerInventories) (state : State) (event : GraphEvent)
    : resources.observeDispatch inventories state event
        (ReferenceWorkQueue.GraphEvent.availableFailures [event])
      = resources.observeDispatch inventories state event := by
  simp only [ResourceState.observeDispatch, GraphBatchResult.handleGraphEvent_singletonSnapshot]

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
