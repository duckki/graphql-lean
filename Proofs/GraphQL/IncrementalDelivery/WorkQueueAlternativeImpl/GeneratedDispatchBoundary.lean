import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.UncancelledReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskRejections
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ReferenceReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InputReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PublicationReplay

/-! Original next-batch start discipline identifies the actual normalized pre-handler state.
These boundary facts are independent of publication-transfer and resource-coverage proofs.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement

private abbrev Kernel := ReferenceWorkQueue.State

-----------------------------------------------------------------------------------------
-- A later started batch proves that the current accounting state has not been retired
-----------------------------------------------------------------------------------------

private theorem batchesStarted_append (queue : Kernel)
    (before after : List (List GraphEvent))
    (started : queue.batchesStarted (before ++ after) = true)
    : queue.batchesStarted before = true
      ∧ (queue.runNormalized before).1.batchesStarted after = true := by
  induction before generalizing queue with
  | nil =>
      refine ⟨rfl, ?_⟩
      simpa only [ReferenceWorkQueue.State.runNormalized_stateFold, List.foldl_nil,
        List.nil_append] using started
  | cons batch rest ih =>
      let next := (queue.handleGraphEvents batch).1
      have step : (!queue.terminated && !batch.isEmpty && queue.acceptsBatch batch) = true
          ∧ next.batchesStarted (rest ++ after) = true := by
        simpa only [ReferenceWorkQueue.State.batchesStarted, List.cons_append,
          Bool.and_eq_true]
          using started
      obtain ⟨earlier, later⟩ := ih next step.2
      refine ⟨?_, ?_⟩
      · change ((!queue.terminated && !batch.isEmpty && queue.acceptsBatch batch)
          && next.batchesStarted rest) = true
        simpa only [Bool.and_eq_true] using And.intro step.1 earlier
      simpa only [ReferenceWorkQueue.State.runNormalized_stateFold, List.foldl_cons]
        using later

/-- A next started batch derives exact raw pre-handler accounting, not merely agreement
up to a termination flag. Terminal clearing cannot occur before this admitted next batch.
-/
theorem generatedReplay_beforeBatch {work inputs batch}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (valid : ReferenceWorkQueue.ValidGraphEvents work inputs.flatten)
    (started : ReferenceWorkQueue.inputsStarted work (inputs ++ [batch]) = true)
    : ((State.initialize work).runNormalized inputs).1.queue
        = (ReferenceWorkQueue.State.initialize
            (ReferenceWorkQueue.Work.fromExecution work)).replayBatches
            inputs
      ∧ ReferenceWorkQueue.inputsStarted work inputs = true
      ∧ ((ReferenceWorkQueue.State.initialize
            (ReferenceWorkQueue.Work.fromExecution work)).replayBatches
          inputs).acceptsBatch
          batch
        = true := by
  let initial := ReferenceWorkQueue.State.initialize (ReferenceWorkQueue.Work.fromExecution work)
  have recursive : initial.batchesStarted (inputs ++ [batch]) = true := by
    rwa [ReferenceWorkQueue.inputsStarted_eq_batchesStarted] at started
  rw [ReferenceWorkQueue.State.batchesStarted_append, Bool.and_eq_true] at recursive
  have next := (initial.replayBatches inputs).batchesStarted_cons batch [] recursive.2
  have priorStarted : ReferenceWorkQueue.inputsStarted work inputs = true := by
    rw [ReferenceWorkQueue.inputsStarted_eq_batchesStarted]
    exact recursive.1
  refine ⟨?_, priorStarted, next.2.1⟩
  rw [State.runNormalized_initialize work inputs generated valid priorStarted]
  dsimp only
  rw [ReferenceWorkQueue.State.runNormalized_replayBatches]
  change (State.fromReference (initial.replayBatches inputs)).queue = initial.replayBatches inputs
  simp only [State.fromReference, next.1, Bool.false_eq_true, ↓reduceIte]

/-- The singleton dispatch boundary specializes the same actual next-batch projection. -/
theorem generatedReplay_beforeNext {work inputs event}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (valid : ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ [event]))
    (started : ReferenceWorkQueue.inputsStarted work (inputs ++ [[event]]) = true)
    : ((State.initialize work).runNormalized inputs).1.queue
        = (ReferenceWorkQueue.State.initialize
            (ReferenceWorkQueue.Work.fromExecution work)).replayBatches
            inputs
      ∧ ReferenceWorkQueue.inputsStarted work inputs = true
      ∧ ((ReferenceWorkQueue.State.initialize
            (ReferenceWorkQueue.Work.fromExecution work)).replayBatches
          inputs).acceptsBatch
          [event]
        = true :=
  generatedReplay_beforeBatch generated (valid.prefix ⟨[event], rfl⟩) started

/-- Actual cached batches derive the complete all-outcomes task ledger before a next input. -/
theorem generatedReplay_pendingAccounting {work inputs event}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (valid : ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ [event]))
    (started : ReferenceWorkQueue.inputsStarted work (inputs ++ [[event]]) = true)
    : ((State.initialize work).runNormalized inputs).1.queue.PendingAccounting work
        (ReferenceWorkQueue.GraphEvent.taskSettlements inputs.flatten) := by
  obtain ⟨raw, _, _⟩ := generatedReplay_beforeNext generated valid started
  have allValid : ReferenceWorkQueue.ValidGraphEvents work (inputs ++ [[event]]).flatten := by
    simpa only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil]
      using valid
  have ledger := generated.pendingLedger_atBatchPrefix inputs [event] [] [] allValid started
    ⟨[event], rfl⟩
  rw [raw]
  simpa only [List.append_nil, ReferenceWorkQueue.State.replayGraphEvents, List.foldl_nil]
    using ledger

/-- Actual batch-prefix source accounting is available at the same next-input queue. -/
theorem generatedReplay_sourceFrame {work inputs event}
    {parents : Nat → WorkQueueSemantics.NodeRefs}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          ReferenceWorkQueue.GroupRecordAt work node dependencies
          → dependencies = parents node.ref)
    (valid : ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ [event]))
    (started : ReferenceWorkQueue.inputsStarted work (inputs ++ [[event]]) = true)
    : ReferenceWorkQueue.UncancelledReplayFrame
        ((State.initialize work).runNormalized inputs).1.queue work parents
        inputs.flatten := by
  obtain ⟨raw, _, _⟩ := generatedReplay_beforeNext generated valid started
  have allValid : ReferenceWorkQueue.ValidGraphEvents work (inputs ++ [[event]]).flatten := by
    simpa only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil]
      using valid
  have source := generated.uncancelledFrame_atBatchPrefix canonical inputs [event] [] []
    allValid started ⟨[event], rfl⟩
  rw [raw]
  simpa only [List.append_nil, ReferenceWorkQueue.State.replayGraphEvents, List.foldl_nil]
    using source

/-- Retained rejections at the real next-input cut come from earlier source task outcomes. -/
theorem generatedReplay_taskRejections {work inputs event}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (valid : ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ [event]))
    (started : ReferenceWorkQueue.inputsStarted work (inputs ++ [[event]]) = true)
    : ((State.initialize work).runNormalized inputs).1.queue.TaskRejectionsSatisfy
        (fun occurrence _ =>
          occurrence ∈ ReferenceWorkQueue.GraphEvent.taskSettlements inputs.flatten) := by
  obtain ⟨raw, _, _⟩ := generatedReplay_beforeNext generated valid started
  rw [raw, ← ReferenceWorkQueue.State.runNormalized_replayBatches]
  refine (ReferenceWorkQueue.createWorkQueue_runNormalized_taskRejections
    (ReferenceWorkQueue.Work.fromExecution work) inputs).mono
    (after := fun occurrence _ => occurrence ∈
      ReferenceWorkQueue.GraphEvent.taskSettlements inputs.flatten) ?_
  intro occurrence errors received
  apply List.mem_reverse.mpr
  exact List.mem_flatMap.mpr ⟨.taskFailure occurrence errors, received, List.mem_cons_self⟩

/-- A next started input cannot follow terminal retirement or an interrupted reader. -/
theorem generatedReplay_beforeNextState {work inputs event}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (valid : ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ [event]))
    (started : ReferenceWorkQueue.inputsStarted work (inputs ++ [[event]]) = true)
    : let before := ((State.initialize work).runNormalized inputs).1
      before = { queue := before.queue } := by
  obtain ⟨_, earlierStarted, _⟩ := generatedReplay_beforeNext generated valid started
  obtain ⟨earlier, _, _⟩ := ReferenceWorkQueue.validGraphEvents_last valid
  have running : ((ReferenceWorkQueue.State.initialize
      (ReferenceWorkQueue.Work.fromExecution work)).runNormalized inputs).1.terminated = false := by
    have all := started
    rw [ReferenceWorkQueue.inputsStarted_eq_batchesStarted] at all
    have later := (batchesStarted_append _ inputs [[event]] all).2
    exact (ReferenceWorkQueue.State.batchesStarted_cons _ [event] [] later).1
  have reader : ((State.initialize work).runNormalized inputs).1.stopped = false := by
    rw [State.runNormalized_initialize work inputs generated earlier earlierStarted]
    simp only [State.fromReference, running, Bool.false_eq_true, ↓reduceIte]
  let before := ((State.initialize work).runNormalized inputs).1
  change before = { queue := before.queue }
  have state : before = { queue := before.queue } := by
    change before.stopped = false at reader
    cases shape : before with
    | mk queue stopped =>
        have flag : stopped = false := by simpa only [shape] using reader
        rw [flag]
  exact state

/-- Exact accounting and wire events at the actual generated next-input boundary. -/
theorem generatedReplay_dispatchProjection {work inputs event}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (valid : ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ [event]))
    (started : ReferenceWorkQueue.inputsStarted work (inputs ++ [[event]]) = true)
    : let before := ((State.initialize work).runNormalized inputs).1
      (
        (before.handleGraphEvent event).1.queue,
        (before.handleGraphEvent event).2.1,
        (before.handleGraphEvent event).2.2.2
      )
      = before.queue.handleGraphEvent event := by
  obtain ⟨raw, _, _⟩ := generatedReplay_beforeNext generated valid started
  obtain ⟨prior, matched, _⟩ := ReferenceWorkQueue.validGraphEvents_last valid
  rw [generatedReplay_beforeNextState generated valid started, raw]
  obtain ⟨parents, canonical, owners, roots, retired⟩ :=
    generated.batchPrefix_structuralFrames inputs [] (fun _ member => prior.eachMatches member)
      (by simp) []
  have allValid : ReferenceWorkQueue.ValidGraphEvents work (inputs ++ [[event]]).flatten := by
    simpa only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil]
      using valid
  have accounting := generated.pendingLedger_atBatchPrefix inputs [event] [] [] allValid started
    ⟨[event], rfl⟩
  simp only [List.append_nil] at accounting
  have children := (ReferenceWorkQueue.createWorkQueue_childGroupsUnique
    (ReferenceWorkQueue.Work.fromExecution work)).runNormalized inputs
  have keys := (ReferenceWorkQueue.createWorkQueue_taskNodeKeysUnique
    (ReferenceWorkQueue.Work.fromExecution work)).runNormalized inputs
  rw [ReferenceWorkQueue.State.runNormalized_replayBatches] at children keys
  apply State.handleGraphEvent_projection_of_consumedAvailability generated canonical
    roots retired owners children keys inputs.flatten event accounting valid rfl []
  intro occurrence errors member
  cases member

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
