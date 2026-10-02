import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.BufferedOwnerHandlers

/-! Actual source replay never forgets a group cancellation marker. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Successful handling may integrate cancelled children but never erases old markers
-----------------------------------------------------------------------------------------

/-- The successful-owner fold leaves cancellation history unchanged.
Witness: each absent/counter-only case keeps the list; successful cleanup prunes without
recording failure. This remains true for arbitrary raw states and contributor lists.
-/
theorem successGroupFold_cancelledGroups (groups : List Execution.DeliveryNode)
    (acc : State × List WorkQueueEvent × NewWork)
    : (groups.foldl successGroupStep acc).1.cancelledGroups = acc.1.cancelledGroups := by
  induction groups generalizing acc with
  | nil => rfl
  | cons group rest ih =>
      rw [List.foldl_cons, ih]
      obtain ⟨queue, events, released⟩ := acc
      unfold successGroupStep
      dsimp only
      split
      · rfl
      · split
        · rw [State.finishGroupSuccess_cancelledGroups]; rfl
        · rfl

/-- Successful settlement preserves every earlier cancellation key.
Witness: integration only appends refused-child markers, the owner fold preserves them,
and activation plus mixed draining never remove them. Ignored inputs keep them unchanged.
-/
theorem State.taskSuccess_cancelledGroups_subset (queue : State) (occurrence : Occurrence)
    (result : TaskResult)
    : queue.cancelledGroups.Subset
        (queue.taskSuccess occurrence result).1.cancelledGroups := by
  cases found : queue.taskNode? occurrence with
  | none =>
      simp only [State.taskSuccess, found]
      exact fun _ member => member
  | some node =>
      rw [queue.taskSuccess_eq occurrence result node found]
      split
      · exact List.Subset.refl _
      · intro key member
        apply State.drainReadyGroups_go_cancelledGroups_subset
        rw [State.startNewWork_cancelledGroups, successGroupFold_cancelledGroups]
        dsimp only
        rw [State.maybeIntegrateWork_cancelledGroups _ result.work (some occurrence)]
        exact State.addGroups_cancelledGroups_subset _ result.work.groups member

/-- Failed settlement preserves all earlier cancellation keys.
Witness: task removal leaves them unchanged and each active failed-owner cleanup appends.
-/
theorem State.taskFailure_cancelledGroups_subset (queue : State) (occurrence : Occurrence)
    (errors : Nat)
    : queue.cancelledGroups.Subset
        (queue.taskFailure occurrence errors).1.cancelledGroups := by
  cases found : queue.taskNode? occurrence with
  | none =>
      simp only [State.taskFailure, found]
      exact fun _ member => member
  | some node =>
      rw [queue.taskFailure_eq occurrence errors node found]
      split
      · exact List.Subset.refl _
      · exact failureGroupFold_cancelledGroups_subset errors node.task.groups
          (queue.removeTask occurrence, [])

/-- Item child integration and its final drain preserve all existing cancellation keys.
Witness: each item's integration appends markers, while pruning/activation preserve them;
compose the fold and the actual mixed drain. Inactive stream inputs do nothing.
-/
theorem State.streamItems_cancelledGroups_subset (queue : State)
    (stream : Execution.DeliveryNode) (items : List StreamItem)
    : queue.cancelledGroups.Subset
        (queue.streamItems stream items).1.cancelledGroups := by
  let step (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue) (item : StreamItem) :=
    let (current, groups, streams, values) := acc
    let (integrated, newWork) := current.maybeIntegrateWork item.work
    let (pruned, nonempty) := integrated.pruneEmptyGroups newWork.newGroups
    (pruned.startNewWork { newWork with newGroups := nonempty },
      groups ++ nonempty, streams ++ newWork.newStreams, values ++ [item.value])
  have one (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue) (item : StreamItem)
      : acc.1.cancelledGroups.Subset (step acc item).1.cancelledGroups := by
    obtain ⟨current, groups, streams, values⟩ := acc
    dsimp only [step]
    rw [State.startNewWork_cancelledGroups, State.pruneEmptyGroups_cancelledGroups,
      State.maybeIntegrateWork_cancelledGroups]
    exact current.addGroups_cancelledGroups_subset item.work.groups
  have loop (more : List StreamItem) (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue)
      : acc.1.cancelledGroups.Subset (more.foldl step acc).1.cancelledGroups := by
    induction more generalizing acc with
    | nil => exact List.Subset.refl _
    | cons item rest ih => exact (one acc item).trans (ih _)
  unfold State.streamItems
  split
  · exact List.Subset.refl _
  · exact (loop items (queue, [], [], [])).trans
      (State.drainReadyGroups_go_cancelledGroups_subset _ _)

-----------------------------------------------------------------------------------------
-- The event source can change order and batching, but cannot undo recorded cancellation
-----------------------------------------------------------------------------------------

/-- Every graph-event handler retains its queue's cancellation markers.
Witness: the three modifying handler proofs; stream closures change only root membership.
-/
theorem State.handleGraphEvent_cancelledGroups_subset (queue : State) (event : GraphEvent)
    : queue.cancelledGroups.Subset (queue.handleGraphEvent event).1.cancelledGroups := by
  cases event with
  | taskSuccess occurrence result => exact queue.taskSuccess_cancelledGroups_subset _ _
  | taskFailure occurrence errors => exact queue.taskFailure_cancelledGroups_subset _ _
  | streamItems stream items => exact queue.streamItems_cancelledGroups_subset _ _
  | streamSuccess stream =>
      change queue.cancelledGroups.Subset (queue.streamSuccess stream).1.cancelledGroups
      unfold State.streamSuccess
      split <;> exact fun _ member => member
  | streamFailure stream errors =>
      change queue.cancelledGroups.Subset
        (queue.streamFailure stream errors).1.cancelledGroups
      unfold State.streamFailure
      split <;> exact fun _ member => member

/-- Sequential source replay retains every cancellation key from each earlier prefix.
Witness: transitivity of the actual handlers' key subsets. No source-admission premise.
-/
theorem State.replayGraphEvents_cancelledGroups_subset (queue : State)
    (events : List GraphEvent)
    : queue.cancelledGroups.Subset (queue.replayGraphEvents events).cancelledGroups := by
  induction events generalizing queue with
  | nil => exact List.Subset.refl _
  | cons event rest ih =>
      exact (queue.handleGraphEvent_cancelledGroups_subset event).trans (ih _)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
