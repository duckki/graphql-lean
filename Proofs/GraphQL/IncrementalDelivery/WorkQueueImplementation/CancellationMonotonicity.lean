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

/-- Successful settlement preserves every earlier cancellation ref.
Witness: integration only appends refused-child markers, the owner fold preserves them,
and activation plus draining never remove them. Ignored inputs keep them unchanged.
-/
theorem State.taskSuccess_cancelledGroups_subset (queue : State) (occurrence : Occurrence)
    (result : TaskResult) (available : List (Occurrence × Nat) := [])
    : queue.cancelledGroups.Subset
        (queue.taskSuccess occurrence result available).1.cancelledGroups := by
  cases found : queue.taskNode? occurrence with
  | none =>
      simp only [State.taskSuccess, found]
      exact fun _ member => member
  | some node =>
      rw [queue.taskSuccess_eq occurrence result node found available]
      intro ref member
      apply State.drainReadyGroups_go_cancelledGroups_subset (available := available)
      apply State.startNewWork_cancelledGroups_subset _ _ available
      rw [successGroupFold_cancelledGroups]
      dsimp only
      rw [State.maybeIntegrateWork_cancelledGroups _ result.work (some occurrence)]
      exact State.addGroups_cancelledGroups_subset _ result.work.groups member

/-- Failed settlement preserves all earlier cancellation refs.
Witness: task removal leaves them unchanged and each active failed-owner cleanup appends.
-/
theorem State.taskFailure_cancelledGroups_subset (queue : State) (occurrence : Occurrence)
    (errors : Nat)
    : queue.cancelledGroups.Subset
        (queue.taskFailure occurrence errors).1.cancelledGroups := by
  exact queue.taskFailure_cancelledGroups_mono occurrence errors

/-- Item child integration and its final drain preserve all existing cancellation refs.
Witness: item integration and startup can append markers; pruning preserves them.
compose the fold and the actual drain. Inactive stream inputs do nothing.
-/
theorem State.streamItems_cancelledGroups_subset (queue : State)
    (stream : Execution.DeliveryNode) (items : List StreamItem)
    (available : List (Occurrence × Nat) := [])
    : queue.cancelledGroups.Subset
        (queue.streamItems stream items available).1.cancelledGroups := by
  let step (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue × List GroupFailureEvent)
      (item : StreamItem) :=
    let (current, groups, streams, values, failures) := acc
    let (integrated, newWork) := current.maybeIntegrateWork item.work
    let (pruned, nonempty) := integrated.pruneEmptyGroups newWork.newGroups
    let (started, queued) := pruned.startNewWork { newWork with newGroups := nonempty } available
    (started, groups ++ nonempty, streams ++ newWork.newStreams,
      values ++ [item.value], failures ++ queued)
  have one (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue × List GroupFailureEvent)
      (item : StreamItem)
      : acc.1.cancelledGroups.Subset (step acc item).1.cancelledGroups := by
    obtain ⟨current, groups, streams, values, failures⟩ := acc
    dsimp only [step]
    apply List.Subset.trans _ (State.startNewWork_cancelledGroups_subset _ _ available)
    rw [State.pruneEmptyGroups_cancelledGroups, State.maybeIntegrateWork_cancelledGroups]
    exact current.addGroups_cancelledGroups_subset item.work.groups
  have loop (more : List StreamItem) (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue × List GroupFailureEvent)
      : acc.1.cancelledGroups.Subset (more.foldl step acc).1.cancelledGroups := by
    induction more generalizing acc with
    | nil => exact List.Subset.refl _
    | cons item rest ih => exact (one acc item).trans (ih _)
  unfold State.streamItems
  split
  · exact List.Subset.refl _
  · exact (loop items (queue, [], [], [], [])).trans
      (State.drainReadyGroups_go_cancelledGroups_subset _ _ available)

-----------------------------------------------------------------------------------------
-- The event source can change order and batching, but cannot undo recorded cancellation
-----------------------------------------------------------------------------------------

/-- Every graph-event handler retains its queue's cancellation markers.
Witness: the three modifying handler proofs; stream closures change only root membership.
-/
theorem State.handleGraphEvent_cancelledGroups_subset (queue : State) (event : GraphEvent)
    (available : List (Occurrence × Nat) := [])
    : queue.cancelledGroups.Subset
        (queue.handleGraphEvent event available).1.cancelledGroups := by
  have same := queue.cacheTaskFailures_cancelledGroups available
  cases event with
  | taskSuccess occurrence result =>
      simpa only [State.handleGraphEvent, same]
        using (queue.cacheTaskFailures available).taskSuccess_cancelledGroups_subset
          occurrence result available
  | taskFailure occurrence errors =>
      simpa only [State.handleGraphEvent, same]
        using (queue.cacheTaskFailures available).taskFailure_cancelledGroups_subset
          occurrence errors
  | streamItems stream items =>
      simpa only [State.handleGraphEvent, same]
        using (queue.cacheTaskFailures available).streamItems_cancelledGroups_subset
          stream items available
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess]
      split <;> intro ref member <;> simpa only [same] using member
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> intro ref member <;> simpa only [same] using member

  | groupFailure notice =>
      simp only [State.handleGraphEvent, State.groupFailure]
      split
      · intro ref member; simpa only [same] using member
      · split <;> intro ref member <;> simpa only [same] using member

/-- Realizing startup enqueue effects retains all cancellation markers. -/
theorem State.dispatchGraphEvent_cancelledGroups_subset (queue : State)
    (event : GraphEvent) (available : List (Occurrence × Nat) := [])
    : queue.cancelledGroups.Subset
        (queue.dispatchGraphEvent event available).1.cancelledGroups :=
  queue.handleGraphEvent_cancelledGroups_subset event available

/-- Sequential source replay retains every cancellation ref from each earlier prefix.
Witness: transitivity of the actual handlers' ref subsets. No source-admission premise.
-/
theorem State.replayGraphEvents_cancelledGroups_subset (queue : State)
    (events : List GraphEvent) (available : List (Occurrence × Nat) := [])
    : queue.cancelledGroups.Subset
        (queue.replayGraphEvents events available).cancelledGroups := by
  induction events generalizing queue with
  | nil => exact List.Subset.refl _
  | cons event rest ih =>
      exact (queue.dispatchGraphEvent_cancelledGroups_subset event available).trans (ih _)

/-- Batch forwarding and termination preserve every previously recorded cancellation. -/
theorem State.handleGraphEvents_cancelledGroups_subset (queue : State)
    (events : List GraphEvent)
    : queue.cancelledGroups.Subset
        (queue.handleGraphEvents events).1.cancelledGroups := by
  cases running : queue.terminated with
  | true =>
      simp only [State.handleGraphEvents, running, ↓reduceIte]
      exact fun _ member => member
  | false =>
      obtain ⟨terminal, same⟩ := queue.handleGraphEvents_stateCore events running
      rw [same]
      exact queue.replayGraphEvents_cancelledGroups_subset events
        (GraphEvent.availableFailures events)

/-- Cancellation history grows through the actual normalized batch state fold. -/
theorem State.runNormalized_cancelledGroups_subset (queue : State)
    (batches : List (List GraphEvent))
    : queue.cancelledGroups.Subset (queue.runNormalized batches).1.cancelledGroups := by
  rw [State.runNormalized_replayBatches]
  induction batches generalizing queue with
  | nil => exact List.Subset.refl _
  | cons batch rest ih =>
      exact (queue.handleGraphEvents_cancelledGroups_subset batch).trans (ih _)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
