import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.SuccessfulStreamTransfer

namespace AlternativeStreamTransferChecks
open GraphQL.IncrementalDelivery
open AlternativeWorkQueue
open AlternativeWorkQueue.NativeRefinement
open ReferenceWorkQueue (rawStreamNoticeRefs)

example : GeneratedFlushStreamCoverage := GeneratedFlushStreamCoverage_holds

-----------------------------------------------------------------------------------------
-- A successful handler removes the buffered producer and activates its held source
-----------------------------------------------------------------------------------------

private def group0 : Execution.DeliveryNode := { ref := 0, path := [] }
private def stream7 : Execution.DeliveryNode := { ref := 7, path := [] }
private def producer : WorkQueueSemantics.Occurrence := .executionGroup [0]
private def incoming : WorkQueueSemantics.Occurrence := .executionGroup [1]

private def value : Execution.ExecutionGroupValue :=
  { deliveryGroups := [group0], path := [], data := [] }

private def queue : ReferenceWorkQueue.State :=
  {
    rootGroups := [0],
    groupNodes :=
      [{ group := ⟨group0, none⟩, tasks := [producer, incoming], pending := 1 }],
    tasks :=
      [
        { occurrence := producer, groups := [group0] },
        { occurrence := incoming, groups := [group0] }
      ],
    taskNodes :=
      [
        {
          task := { occurrence := producer, groups := [group0] },
          value := some value,
          childStreams := [7]
        },
        { task := { occurrence := incoming, groups := [group0] } }
      ],
    streams := [⟨stream7⟩]
  }

private def event : GraphEvent := .taskSuccess incoming { value }
private def before : GraphBatchResult := { state := { queue } }
private abbrev released := before.handleGraphEvent event

private theorem projection
    : (
        (before.state.handleGraphEvent event).1.queue,
        (before.state.handleGraphEvent event).2.1
      )
      = queue.handleGraphEvent event := by cbv

private theorem noticed
    : 7 ∈ (queue.handleGraphEvent event).2.flatMap rawStreamNoticeRefs := by
  cbv
  exact List.mem_cons_self

example : released.state.queue.taskNode? producer = none := by cbv
example : released.state.queue.rootStreams = [7] := by cbv

-- The stop target and emitted cancellation come from general actual-dispatch coverage.
example : .stream 7 ∈ released.state.cleanupTargets :=
  GraphBatchResult.releasedStream_cleanupTarget before event projection noticed

example : .cancelSource 7 ∈ released.state.cancel.2 :=
  GraphBatchResult.releasedStream_stopRequest before event rfl projection noticed

private def acquired : ResourceState :=
  ResourceState.empty.set (.stream 7) (.owned (.producer producer))

private def leases : ResourceState :=
  (acquired.adopt producer [.stream 7]).set (.task incoming) (.owned .queue)

private abbrev completed := leases.observeCompletionAndCleanup before.state event
private abbrev stopped := completed.1.observeStop released.state

private theorem acquisition
    : ResourceReplay ResourceState.empty
        [
          .acquire (.stream 7) (.producer producer),
          .adopt producer [.stream 7],
          .acquire (.task incoming) .queue
        ]
        leases :=
  .cons (.acquire _ _ _ rfl)
    (.cons (.adopt _ _ _) (.cons (.acquire _ _ .queue (by cbv)) (.nil _)))

-- Successful transfer does not dispose the held source; stopping its new root does.
example : completed.2 = [.finishNormally (.task incoming)] := by cbv
example : completed.1 (.stream 7) = .owned .queue := by cbv

example : stopped.1 (.stream 7) = .cleanupRequested .queue := by
  apply ResourceState.requestQueueCleanup_owned
  · exact List.mem_filterMap.mpr ⟨.cancelSource 7,
      GraphBatchResult.releasedStream_stopRequest before event rfl projection noticed, rfl⟩
  · cbv

example
    : ResourceReplay ResourceState.empty
        ([
            .acquire (.stream 7) (.producer producer),
            .adopt producer [.stream 7],
            .acquire (.task incoming) .queue
          ]
          ++ completed.2
          ++ stopped.2) stopped.1 :=
  (acquisition.append (leases.observeCompletionAndCleanup_replay _ _)).append
    (completed.1.observeStop_replay _)

-----------------------------------------------------------------------------------------
-- A later input may finish an earlier notice retained in the batch accumulator
-----------------------------------------------------------------------------------------

private abbrev exhausted := released.handleGraphEvent (.streamSuccess stream7)

example : 7 ∈ exhausted.workQueueEvents.flatMap rawStreamNoticeRefs := by
  cbv
  exact List.mem_cons_self

example : exhausted.state.queue.rootStreams = [] := by cbv
example : exhausted.state.cleanupTargets = [] := by cbv

-- Coverage intentionally uses newly emitted notices, not every historical batch notice.
example
    : (completed.1.observeCompletionAndCleanup released.state (.streamSuccess stream7)).1
        (.stream 7)
      = .released :=
  completed.1.observeCompletionAndCleanup_finishedTarget released.state
    (.streamSuccess stream7) (.stream 7) (by cbv) (by cbv)

#print axioms GeneratedFlushStreamCoverage_holds
#print axioms successfulFlush_heldSource
#print axioms graphEvent_newStream_active
#print axioms GraphBatchResult.releasedStream_cleanupTarget
#print axioms GraphBatchResult.releasedStream_stopRequest

end AlternativeStreamTransferChecks
