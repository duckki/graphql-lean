import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationHandlerDispatch

/-! The actual FIFO dispatch bridge retains internal failure controls in queue state. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue

/-- Exposing task rejections commutes with appending internal group notices. -/
theorem reference_cacheTaskFailures_enqueueGroupFailures
    (queue : ReferenceWorkQueue.State)
    (notices : List ReferenceWorkQueue.GroupFailureEvent)
    (available : List (WorkQueueSemantics.Occurrence × Nat))
    : (queue.enqueueGroupFailures notices).cacheTaskFailures available
      = (queue.cacheTaskFailures available).enqueueGroupFailures notices := by
  induction available generalizing queue with
  | nil => rfl
  | cons entry rest ih =>
      have lookup : (queue.enqueueGroupFailures notices).taskNode? entry.1
          = queue.taskNode? entry.1 := rfl
      cases found : queue.taskNode? entry.1 with
      | none =>
          simpa only [ReferenceWorkQueue.State.cacheTaskFailures, List.foldl_cons,
            lookup, found] using ih queue
      | some node =>
          have put : (queue.enqueueGroupFailures notices).putTaskNode
              { node with rejection := some entry.2 }
              = (queue.putTaskNode { node with rejection := some entry.2 }).enqueueGroupFailures
                notices := rfl
          simpa only [ReferenceWorkQueue.State.cacheTaskFailures, List.foldl_cons,
            lookup, found, put] using ih (queue.putTaskNode { node with rejection := some entry.2 })

/-- The reference batch accumulator consists of the real queue and emitted work events. -/
abbrev ReferenceDispatchAcc := ReferenceWorkQueue.State × List Execution.WorkQueueEvent

/-- Realize enqueue effects before the next supplied FIFO entry. -/
def referenceDispatchStep (available : List (WorkQueueSemantics.Occurrence × Nat))
    (acc : ReferenceDispatchAcc) (event : GraphEvent)
    : ReferenceDispatchAcc :=
  let handled := acc.1.dispatchGraphEvent event available
  (handled.1, acc.2 ++ handled.2)

private theorem graphDispatchStep_cacheProjection (actual : GraphBatchResult)
    (reference : ReferenceDispatchAcc) (event : GraphEvent)
    (available : List (WorkQueueSemantics.Occurrence × Nat))
    (outputs : actual.workQueueEvents = reference.2)
    (step
      : (
          (actual.state.handleGraphEvent event available).1.queue.cacheTaskFailures
            available,
          (actual.state.handleGraphEvent event available).2.1,
          (actual.state.handleGraphEvent event available).2.2.2
        )
        = (
          (reference.1.handleGraphEvent event available).1.cacheTaskFailures available,
          (reference.1.handleGraphEvent event available).2
        ))
    : (
        (actual.handleGraphEvent event available).state.queue.cacheTaskFailures available,
        (actual.handleGraphEvent event available).workQueueEvents
      )
      = (
        (referenceDispatchStep available reference event).1.cacheTaskFailures available,
        (referenceDispatchStep available reference event).2
      ) := by
  have combined := congrArg
    (fun value : ReferenceWorkQueue.State × List Execution.WorkQueueEvent
        × List ReferenceWorkQueue.GroupFailureEvent =>
      (value.1.enqueueGroupFailures value.2.2, actual.workQueueEvents ++ value.2.1)) step
  simpa only [GraphBatchResult.handleGraphEvent, referenceDispatchStep,
    ReferenceWorkQueue.State.dispatchGraphEvent, reference_cacheTaskFailures_enqueueGroupFailures,
    outputs] using combined

/-- The actual FIFO prefix has the same exposed queue and ordered output as reference dispatch. -/
theorem referenceBatch_graphPrefix_cacheProjection {work : Work}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (earlier : List (List GraphEvent)) (batch : List GraphEvent)
    (later : List (List GraphEvent))
    (valid : ReferenceWorkQueue.ValidGraphEvents work (earlier ++ batch :: later).flatten)
    (started : ReferenceWorkQueue.inputsStarted work (earlier ++ batch :: later) = true)
    (fifoPrefix tail : List GraphEvent) (partition : batch = fifoPrefix ++ tail)
    : let available := ReferenceWorkQueue.GraphEvent.availableFailures batch
      let queue :=
        (ReferenceWorkQueue.State.initialize
          (ReferenceWorkQueue.Work.fromExecution work)).replayBatches
          earlier
      let actual :=
        fifoPrefix.foldl (fun acc event => acc.handleGraphEvent event available)
          ({ state := { queue } } : GraphBatchResult)
      let reference := fifoPrefix.foldl (referenceDispatchStep available) (queue, [])
      (actual.state.queue.cacheTaskFailures available, actual.workQueueEvents)
      = (reference.1.cacheTaskFailures available, reference.2) := by
  let available := ReferenceWorkQueue.GraphEvent.availableFailures batch
  let queue := (ReferenceWorkQueue.State.initialize
    (ReferenceWorkQueue.Work.fromExecution work)).replayBatches earlier
  have loop (remaining fifo : List GraphEvent) (cut : batch = fifo ++ remaining ++ tail)
      (actual : GraphBatchResult) (reference : ReferenceDispatchAcc)
      (referenceQueue : reference.1 = queue.replayGraphEvents fifo available)
      (same : (actual.state.queue.cacheTaskFailures available, actual.workQueueEvents)
        = (reference.1.cacheTaskFailures available, reference.2))
      (running : actual.state.stopped = false)
      : let first := remaining.foldl (fun acc event => acc.handleGraphEvent event available) actual
        let second := remaining.foldl (referenceDispatchStep available) reference
        (first.state.queue.cacheTaskFailures available, first.workQueueEvents)
          = (second.1.cacheTaskFailures available, second.2) := by
    induction remaining generalizing fifo actual reference with
    | nil => exact same
    | cons event rest ih =>
        let nextReference := referenceDispatchStep available reference event
        let nextActual := actual.handleGraphEvent event available
        have queueEq := congrArg Prod.fst same
        rw [referenceQueue] at queueEq
        have actualStep := actual.state.handleGraphEvent_of_cache_eq
          ({ queue := queue.replayGraphEvents fifo available } : State) running rfl
          available queueEq event
        have step := referenceBatchPrefix_handleGraphEvent_cacheProjection generated earlier batch
          later fifo event (rest ++ tail)
          (by simpa only [List.append_assoc, List.cons_append] using cut) valid started
        change ((({ queue := queue.replayGraphEvents fifo available } : State
            ).handleGraphEvent event available).1.queue.cacheTaskFailures available,
            (({ queue := queue.replayGraphEvents fifo available } : State
              ).handleGraphEvent event available).2.1,
            (({ queue := queue.replayGraphEvents fifo available } : State
              ).handleGraphEvent event available).2.2.2)
          = (((queue.replayGraphEvents fifo available).handleGraphEvent event available
              ).1.cacheTaskFailures available,
            ((queue.replayGraphEvents fifo available).handleGraphEvent event available).2) at step
        rw [← actualStep, ← referenceQueue] at step
        have nextSame := graphDispatchStep_cacheProjection actual reference event available
          (congrArg Prod.snd same) step
        have nextQueue : nextReference.1
            = queue.replayGraphEvents (fifo ++ [event]) available := by
          rw [ReferenceWorkQueue.State.replayGraphEvents_append queue fifo [event] available]
          change (reference.1.dispatchGraphEvent event available).1
            = ((queue.replayGraphEvents fifo available).dispatchGraphEvent event available).1
          rw [referenceQueue]
        have nextPartition : batch = (fifo ++ [event]) ++ rest ++ tail := by
          simpa only [List.append_assoc, List.singleton_append] using cut
        have nextRunning : nextActual.state.stopped = false :=
          (actual.state.handleGraphEvent_stopped event available).trans running
        exact ih (fifo ++ [event]) nextPartition nextActual nextReference nextQueue
          nextSame nextRunning
  exact loop fifoPrefix [] (by simpa only [List.nil_append] using partition)
    ({ state := { queue } } : GraphBatchResult) (queue, []) rfl rfl rfl

/-- The complete FIFO fold has equal exposed queues and emitted work-event lists. -/
theorem referenceBatch_graphFold_cacheProjection {work : Work}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (earlier : List (List GraphEvent)) (batch : List GraphEvent)
    (later : List (List GraphEvent))
    (valid : ReferenceWorkQueue.ValidGraphEvents work (earlier ++ batch :: later).flatten)
    (started : ReferenceWorkQueue.inputsStarted work (earlier ++ batch :: later) = true)
    : let available := ReferenceWorkQueue.GraphEvent.availableFailures batch
      let queue :=
        (ReferenceWorkQueue.State.initialize
          (ReferenceWorkQueue.Work.fromExecution work)).replayBatches
          earlier
      let actual :=
        batch.foldl (fun acc event => acc.handleGraphEvent event available)
          ({ state := { queue } } : GraphBatchResult)
      let reference := batch.foldl (referenceDispatchStep available) (queue, [])
      (actual.state.queue.cacheTaskFailures available, actual.workQueueEvents)
      = (reference.1.cacheTaskFailures available, reference.2) :=
  referenceBatch_graphPrefix_cacheProjection generated earlier batch later valid started
    batch [] (by simp)

/-- The reference accumulator follows exact snapshot-aware FIFO replay. -/
theorem referenceDispatchFold_state (events : List GraphEvent)
    (acc : ReferenceDispatchAcc) (available : List (WorkQueueSemantics.Occurrence × Nat))
    : (events.foldl (referenceDispatchStep available) acc).1
      = acc.1.replayGraphEvents events available := by
  induction events generalizing acc with
  | nil => rfl
  | cons event rest ih => exact ih (referenceDispatchStep available acc event)

/-- Actual FIFO dispatch leaves the reader's stopped guard unchanged. -/
theorem graphDispatchFold_stopped (events : List GraphEvent) (acc : GraphBatchResult)
    (available : List (WorkQueueSemantics.Occurrence × Nat))
    : (events.foldl (fun acc event => acc.handleGraphEvent event available)
        acc).state.stopped
      = acc.state.stopped := by
  induction events generalizing acc with
  | nil => rfl
  | cons event rest ih =>
      exact (ih (acc.handleGraphEvent event available)).trans
        (acc.state.handleGraphEvent_stopped event available)

/-- Complete FIFO folds agree in residual queue, including pending controls, and real output. -/
theorem referenceBatch_graphFold_projection {work : Work}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (earlier : List (List GraphEvent)) (batch : List GraphEvent)
    (later : List (List GraphEvent))
    (valid : ReferenceWorkQueue.ValidGraphEvents work (earlier ++ batch :: later).flatten)
    (started : ReferenceWorkQueue.inputsStarted work (earlier ++ batch :: later) = true)
    : let available := ReferenceWorkQueue.GraphEvent.availableFailures batch
      let queue :=
        (ReferenceWorkQueue.State.initialize
          (ReferenceWorkQueue.Work.fromExecution work)).replayBatches
          earlier
      let actual :=
        batch.foldl (fun acc event => acc.handleGraphEvent event available)
          ({ state := { queue } } : GraphBatchResult)
      let reference := batch.foldl (referenceDispatchStep available) (queue, [])
      (actual.state.queue, actual.workQueueEvents) = reference := by
  let available := ReferenceWorkQueue.GraphEvent.availableFailures batch
  let queue := (ReferenceWorkQueue.State.initialize
    (ReferenceWorkQueue.Work.fromExecution work)).replayBatches earlier
  cases reversed : batch.reverse with
  | nil =>
      have empty := congrArg List.reverse reversed
      simp only [List.reverse_reverse, List.reverse_nil] at empty
      subst batch
      rfl
  | cons event rest =>
      let fifo := rest.reverse
      have partition : batch = fifo ++ [event] := by
        have same := congrArg List.reverse reversed
        simpa only [List.reverse_reverse, List.reverse_cons] using same
      let actual := fifo.foldl (fun acc event => acc.handleGraphEvent event available)
        ({ state := { queue } } : GraphBatchResult)
      let reference := fifo.foldl (referenceDispatchStep available) (queue, [])
      have exposed := referenceBatch_graphPrefix_cacheProjection generated earlier batch later
        valid started fifo [event] partition
      have referenceQueue : reference.1 = queue.replayGraphEvents fifo available :=
        referenceDispatchFold_state fifo (queue, []) available
      have queueEq := congrArg Prod.fst exposed
      change actual.state.queue.cacheTaskFailures available
        = reference.1.cacheTaskFailures available at queueEq
      rw [referenceQueue] at queueEq
      have running : actual.state.stopped = false :=
        graphDispatchFold_stopped fifo ({ state := { queue } } : GraphBatchResult) available
      have actualStep := actual.state.handleGraphEvent_of_cache_eq
        ({ queue := queue.replayGraphEvents fifo available } : State) running rfl
        available queueEq event
      have bridge := referenceBatchLast_handleGraphEvent_projection generated earlier batch later
        fifo event partition valid started
      change ((({ queue := queue.replayGraphEvents fifo available } : State
          ).handleGraphEvent event available).1.queue,
          (({ queue := queue.replayGraphEvents fifo available } : State
            ).handleGraphEvent event available).2.1,
          (({ queue := queue.replayGraphEvents fifo available } : State
            ).handleGraphEvent event available).2.2.2)
        = (queue.replayGraphEvents fifo available).handleGraphEvent event available at bridge
      rw [← actualStep, ← referenceQueue] at bridge
      have combined := congrArg
        (fun value : ReferenceWorkQueue.State × List Execution.WorkQueueEvent
            × List ReferenceWorkQueue.GroupFailureEvent =>
          (value.1.enqueueGroupFailures value.2.2, actual.workQueueEvents ++ value.2.1)) bridge
      have wire := congrArg Prod.snd exposed
      change actual.workQueueEvents = reference.2 at wire
      have final : ((actual.handleGraphEvent event available).state.queue,
          (actual.handleGraphEvent event available).workQueueEvents)
          = referenceDispatchStep available reference event := by
        simpa only [GraphBatchResult.handleGraphEvent, referenceDispatchStep,
          ReferenceWorkQueue.State.dispatchGraphEvent, wire]
          using combined
      change ((batch.foldl (fun acc event => acc.handleGraphEvent event available)
          ({ state := { queue } } : GraphBatchResult)).state.queue,
          (batch.foldl (fun acc event => acc.handleGraphEvent event available)
            ({ state := { queue } } : GraphBatchResult)).workQueueEvents)
        = batch.foldl (referenceDispatchStep available) (queue, [])
      rw [partition, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact final

end GraphQL.IncrementalDelivery.AlternativeWorkQueue
