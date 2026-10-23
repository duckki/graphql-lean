import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.GeneratedDispatchBoundary
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ResourceBatchReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ResourceCacheExposure

/-! Resource observations at actual FIFO cuts retain the complete host failure snapshot.
The source ledger refers to consumed notifications; rejection availability can be earlier.
-/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue

/-- Child-source inventories follow the same supplied-snapshot FIFO replay. -/
theorem State.ChildStreamInventory.replayGraphEvents {queue : State}
    (prior : queue.ChildStreamInventory) (events : List GraphEvent)
    (available : List (WorkQueueSemantics.Occurrence × Nat) := [])
    : (queue.replayGraphEvents events available).ChildStreamInventory := by
  induction events generalizing queue with
  | nil => exact prior
  | cons event rest ih => exact ih (prior.handleGraphEvent event available)

/-- Supplied snapshots and consumed callbacks preserve any independently licensed
rejection-origin predicate throughout the actual FIFO replay.
-/
theorem State.TaskRejectionsSatisfy.replayGraphEvents_available {queue : State} {property}
    (prior : queue.TaskRejectionsSatisfy property) (events : List GraphEvent)
    (incoming
      : ∀ occurrence errors,
          GraphEvent.taskFailure occurrence errors ∈ events → property occurrence errors)
    (available : List (WorkQueueSemantics.Occurrence × Nat))
    (licensed
      : ∀ occurrence errors,
          (occurrence, errors) ∈ available → property occurrence errors)
    : (queue.replayGraphEvents events available).TaskRejectionsSatisfy property := by
  induction events generalizing queue with
  | nil => exact prior
  | cons event rest ih =>
      exact ih (prior.handleGraphEvent event
        (fun occurrence errors same => incoming occurrence errors
          (same ▸ List.mem_cons_self)) available licensed)
        (fun occurrence errors member => incoming occurrence errors
          (List.mem_cons_of_mem _ member))

/-- Exposing source-matched rejections preserves all source-cut structural certificates.
The consumed history stays fixed; the cache may include later task notifications.
-/
theorem UncancelledReplayFrame.cacheTaskFailures {queue work parents before}
    (frame : UncancelledReplayFrame queue work parents before)
    (available : List (WorkQueueSemantics.Occurrence × Nat))
    (licensed
      : ∀ occurrence errors,
          (occurrence, errors) ∈ available
          → (GraphEvent.taskFailure occurrence errors).MatchesWork work)
    : UncancelledReplayFrame (queue.cacheTaskFailures available) work parents before := by
  refine ⟨
    frame.markers.cacheTaskFailures available,
    frame.owners.cacheTaskFailures available,
    frame.parent.cacheTaskFailures available,
    frame.roots.cacheTaskFailures available,
    frame.tasks.cacheTaskFailures available,
    frame.pending.cacheTaskFailures available,
    frame.regions.cacheTaskFailures available,
    frame.rejected.cacheTaskFailures available licensed,
    ?_,
    frame.cancellations.cacheTaskFailures available,
    ?_,
    ?_,
    ?_
  ⟩
  · simpa only [State.cacheTaskFailures_tasks] using frame.failures
  · simpa only [State.ProducerRegistrationAccounting, State.ObjectProducerCancelled,
      State.cacheTaskFailures_tasks, State.cacheTaskFailures_cancelledGroups]
      using frame.producerRegistrations
  · simpa only [State.cacheTaskFailures_tasks] using frame.producers
  · simpa only [State.cacheTaskFailures_tasks] using frame.producerOrder

end GraphQL.IncrementalDelivery.ReferenceWorkQueue

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement

private abbrev initial (work : Work) :=
  ReferenceWorkQueue.State.initialize (ReferenceWorkQueue.Work.fromExecution work)

/-- A started next batch exposes the exact running native state after earlier batches. -/
theorem generatedResource_beforeBatch {work inputs batch}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (valid : ReferenceWorkQueue.ValidGraphEvents work inputs.flatten)
    (started : ReferenceWorkQueue.inputsStarted work (inputs ++ [batch]) = true)
    : ((State.initialize work).runNormalized inputs).1
        = { queue := (initial work).replayBatches inputs }
      ∧ ((initial work).replayBatches inputs).terminated = false := by
  obtain ⟨_, priorStarted, _⟩ := generatedReplay_beforeBatch generated valid started
  have recursive : (initial work).batchesStarted (inputs ++ [batch]) = true := by
    rwa [ReferenceWorkQueue.inputsStarted_eq_batchesStarted] at started
  rw [ReferenceWorkQueue.State.batchesStarted_append, Bool.and_eq_true] at recursive
  have running := ((initial work).replayBatches inputs).batchesStarted_cons batch []
    recursive.2
  refine ⟨?_, running.1⟩
  rw [State.runNormalized_initialize work inputs generated valid priorStarted]
  dsimp only
  rw [ReferenceWorkQueue.State.runNormalized_replayBatches]
  simp only [State.fromReference, running.1, Bool.false_eq_true, ↓reduceIte]

/-- Name the actual resource FIFO prefix, using availability from its entire host batch.
This is proof notation for the existing observer fold, not another queue implementation.
-/
def resourceFifoPrefix (work : Work) (inputs : List (List GraphEvent))
    (batch fifo : List GraphEvent) (resources : ResourceState)
    (inventories : ProducerInventories)
    : ResourceBatchObservation :=
  fifo.foldl
    (fun acc event =>
      acc.handleGraphEvent inventories event
        (ReferenceWorkQueue.GraphEvent.availableFailures batch))
    {
      dispatch := { state := ((State.initialize work).runNormalized inputs).1 }, resources
    }

/-- Common exposure relates the actual resource prefix to its reference source cut.
No flattened replay or empty-snapshot state bridge is required at intermediate cuts.
-/
theorem resourceFifoPrefix_cacheProjection
    {work inputs batch fifo tail resources inventories}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (valid : ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ batch))
    (started : ReferenceWorkQueue.inputsStarted work (inputs ++ [batch]) = true)
    (partition : batch = fifo ++ tail)
    : let available := ReferenceWorkQueue.GraphEvent.availableFailures batch
      let actual := resourceFifoPrefix work inputs batch fifo resources inventories
      actual.dispatch.state.queue.cacheTaskFailures available
        = (((initial work).replayBatches inputs).replayGraphEvents fifo
            available).cacheTaskFailures
            available
      ∧ actual.dispatch.state.stopped = false := by
  have before := (generatedResource_beforeBatch generated
    (valid.prefix ⟨batch, rfl⟩) started).1
  have allValid : ReferenceWorkQueue.ValidGraphEvents work (inputs ++ batch :: []).flatten := by
    simpa only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil]
      using valid
  have bridge := referenceBatch_graphPrefix_cacheProjection generated inputs batch []
    allValid started fifo tail partition
  have queue := congrArg Prod.fst bridge
  rw [referenceDispatchFold_state] at queue
  dsimp only [resourceFifoPrefix]
  rw [ResourceBatchObservation.fold_dispatch _ inventories fifo
    (ReferenceWorkQueue.GraphEvent.availableFailures batch), before]
  exact ⟨queue, graphDispatchFold_stopped fifo
    ({ state := { queue := (initial work).replayBatches inputs } } : GraphBatchResult)
    (ReferenceWorkQueue.GraphEvent.availableFailures batch)⟩

/-- The independently derived source ledger holds at the same exposed resource cut.
Its settlement history contains only FIFO notifications already consumed.
-/
theorem resourceFifoPrefix_pendingAccounting
    {work inputs batch fifo tail resources inventories}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (valid : ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ batch))
    (started : ReferenceWorkQueue.inputsStarted work (inputs ++ [batch]) = true)
    (partition : batch = fifo ++ tail)
    : let available := ReferenceWorkQueue.GraphEvent.availableFailures batch
      let actual := resourceFifoPrefix work inputs batch fifo resources inventories
      (actual.dispatch.state.queue.cacheTaskFailures available).PendingAccounting work
        (ReferenceWorkQueue.GraphEvent.taskSettlements (inputs.flatten ++ fifo)) := by
  have allValid : ReferenceWorkQueue.ValidGraphEvents work (inputs ++ batch :: []).flatten := by
    simpa only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil]
      using valid
  have ledger := generated.pendingLedger_atBatchPrefix inputs batch [] fifo allValid started
    ⟨tail, partition.symm⟩
  dsimp only
  rw [(resourceFifoPrefix_cacheProjection generated valid started partition).1]
  exact ledger.cacheTaskFailures _

/-- Structural source evidence holds at the actual exposed resource FIFO prefix.
The complete batch licenses availability; settlement evidence retains the consumed prefix.
-/
theorem resourceFifoPrefix_sourceFrame
    {work inputs batch fifo tail resources inventories parents}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          ReferenceWorkQueue.GroupRecordAt work node dependencies
          → dependencies = parents node.ref)
    (valid : ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ batch))
    (started : ReferenceWorkQueue.inputsStarted work (inputs ++ [batch]) = true)
    (partition : batch = fifo ++ tail)
    : let available := ReferenceWorkQueue.GraphEvent.availableFailures batch
      let actual := resourceFifoPrefix work inputs batch fifo resources inventories
      ReferenceWorkQueue.UncancelledReplayFrame
        (actual.dispatch.state.queue.cacheTaskFailures available) work parents
        (inputs.flatten ++ fifo) := by
  have allValid : ReferenceWorkQueue.ValidGraphEvents work (inputs ++ batch :: []).flatten := by
    simpa only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil]
      using valid
  have source := generated.uncancelledFrame_atBatchPrefix canonical inputs batch [] fifo
    allValid started ⟨tail, partition.symm⟩
  dsimp only
  rw [(resourceFifoPrefix_cacheProjection generated valid started partition).1]
  apply source.cacheTaskFailures
  intro occurrence errors member
  obtain ⟨event, supplied, failure⟩ := List.mem_filterMap.mp member
  cases event <;> simp only [Option.some.injEq, reduceCtorEq, Prod.mk.injEq] at failure
  obtain ⟨rfl, rfl⟩ := failure
  exact valid.eachMatches (List.mem_append_right _ supplied)

/-- Every rejection at the actual exposed cut is licensed by a task outcome in the full
supplied source. This bound includes later notifications from the current host batch.
-/
theorem resourceFifoPrefix_taskRejections
    {work inputs batch fifo tail resources inventories}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (valid : ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ batch))
    (started : ReferenceWorkQueue.inputsStarted work (inputs ++ [batch]) = true)
    (partition : batch = fifo ++ tail)
    : let available := ReferenceWorkQueue.GraphEvent.availableFailures batch
      let actual := resourceFifoPrefix work inputs batch fifo resources inventories
      (actual.dispatch.state.queue.cacheTaskFailures available).TaskRejectionsSatisfy
        (fun occurrence _ =>
          occurrence
          ∈ ReferenceWorkQueue.GraphEvent.taskSettlements (inputs.flatten ++ batch)) := by
  have licensedFailure (occurrence errors)
      (member : ReferenceWorkQueue.GraphEvent.taskFailure occurrence errors
        ∈ inputs.flatten ++ batch)
      : occurrence ∈ ReferenceWorkQueue.GraphEvent.taskSettlements (inputs.flatten ++ batch) := by
    apply List.mem_reverse.mpr
    exact List.mem_flatMap.mpr ⟨.taskFailure occurrence errors, member, List.mem_cons_self⟩
  have licensed (occurrence errors)
      (member : (occurrence, errors) ∈ ReferenceWorkQueue.GraphEvent.availableFailures batch)
      : occurrence ∈ ReferenceWorkQueue.GraphEvent.taskSettlements (inputs.flatten ++ batch) := by
    obtain ⟨event, supplied, failure⟩ := List.mem_filterMap.mp member
    cases event <;> simp only [Option.some.injEq, reduceCtorEq, Prod.mk.injEq] at failure
    obtain ⟨rfl, rfl⟩ := failure
    exact licensedFailure _ _ (List.mem_append_right _ supplied)
  have prior := ReferenceWorkQueue.createWorkQueue_runNormalized_taskRejections
    (ReferenceWorkQueue.Work.fromExecution work) inputs
  rw [ReferenceWorkQueue.State.runNormalized_replayBatches] at prior
  have supported := prior.mono (fun occurrence errors member =>
    licensedFailure occurrence errors (List.mem_append_left _ member))
  have exposed := supported.replayGraphEvents_available fifo (fun occurrence errors member => by
    apply licensedFailure occurrence errors
    apply List.mem_append_right
    rw [partition]
    exact List.mem_append_left _ member)
    (ReferenceWorkQueue.GraphEvent.availableFailures batch) licensed
  dsimp only
  rw [(resourceFifoPrefix_cacheProjection generated valid started partition).1]
  exact exposed.cacheTaskFailures _ licensed

/-- Actual native computation keys remain unique at every resource FIFO cut. -/
theorem resourceFifoPrefix_taskKeys
    {work inputs batch fifo tail resources inventories}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (valid : ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ batch))
    (started : ReferenceWorkQueue.inputsStarted work (inputs ++ [batch]) = true)
    (partition : batch = fifo ++ tail)
    : (resourceFifoPrefix work inputs batch fifo resources
        inventories).dispatch.state.queue.TaskNodeKeysUnique := by
  have prior := (ReferenceWorkQueue.createWorkQueue_taskNodeKeysUnique
    (ReferenceWorkQueue.Work.fromExecution work)).runNormalized inputs
  rw [ReferenceWorkQueue.State.runNormalized_replayBatches] at prior
  have exposed := (prior.replayGraphEvents fifo
    (ReferenceWorkQueue.GraphEvent.availableFailures batch)).cacheTaskFailures
      (ReferenceWorkQueue.GraphEvent.availableFailures batch)
  rw [← (resourceFifoPrefix_cacheProjection generated valid started partition).1] at exposed
  simpa only [ReferenceWorkQueue.State.TaskNodeKeysUnique,
    ReferenceWorkQueue.State.cacheTaskFailures_taskOccurrences] using exposed

/-- The source inventory belongs to the actual exposed observer cut, not a flattened queue. -/
theorem resourceFifoPrefix_childStreamInventory
    {work inputs batch fifo tail resources inventories}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (valid : ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ batch))
    (started : ReferenceWorkQueue.inputsStarted work (inputs ++ [batch]) = true)
    (partition : batch = fifo ++ tail)
    : let available := ReferenceWorkQueue.GraphEvent.availableFailures batch
      let actual := resourceFifoPrefix work inputs batch fifo resources inventories
      (actual.dispatch.state.queue.cacheTaskFailures available).ChildStreamInventory := by
  have prior := ReferenceWorkQueue.createWorkQueue_runNormalized_childStreamInventory
    (ReferenceWorkQueue.Work.fromExecution work) inputs
  rw [ReferenceWorkQueue.State.runNormalized_replayBatches] at prior
  have after := prior.replayGraphEvents fifo (ReferenceWorkQueue.GraphEvent.availableFailures batch)
  dsimp only
  rw [(resourceFifoPrefix_cacheProjection generated valid started partition).1]
  exact after.cacheTaskFailures _

/-- Resource handoffs and ordered cleanup actions can be checked at the source cut.
Actual dispatch and its observer both retain the complete batch's available failures.
-/
theorem resourceFifoPrefix_observeDispatch
    {work inputs batch fifo tail resources inventories}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (valid : ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ batch))
    (started : ReferenceWorkQueue.inputsStarted work (inputs ++ [batch]) = true)
    (partition : batch = fifo ++ tail) (event : GraphEvent)
    : let available := ReferenceWorkQueue.GraphEvent.availableFailures batch
      let actual := resourceFifoPrefix work inputs batch fifo resources inventories
      actual.resources.observeDispatch inventories actual.dispatch.state event available
      = actual.resources.observeDispatch inventories
          {
            queue :=
              ((initial work).replayBatches inputs).replayGraphEvents fifo available
          }
          event available := by
  obtain ⟨same, running⟩ := resourceFifoPrefix_cacheProjection generated valid started partition
  exact ResourceState.observeDispatch_of_cache_eq _ _ _ _ running rfl _ same event

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
