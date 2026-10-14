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
            (ReferenceWorkQueue.Work.fromExecution work)).replayGraphEvents
            inputs.flatten
      ∧ ReferenceWorkQueue.inputsStarted work inputs = true
      ∧ (ReferenceWorkQueue.State.initialize
          (ReferenceWorkQueue.Work.fromExecution work)).acceptsBatch
          inputs.flatten
        = true := by
  let initial := ReferenceWorkQueue.State.initialize (ReferenceWorkQueue.Work.fromExecution work)
  have recursive : initial.batchesStarted (inputs ++ [batch]) = true := by
    rwa [ReferenceWorkQueue.inputsStarted_eq_batchesStarted] at started
  obtain ⟨earlier, later⟩ := batchesStarted_append initial inputs [batch] recursive
  have running := ((initial.runNormalized inputs).1.batchesStarted_cons batch [] later).1
  obtain ⟨terminal, same⟩ := initial.runNormalized_stateCore inputs earlier
  have flag : terminal = false := by simpa [same] using running
  have rawFlag : (initial.replayGraphEvents inputs.flatten).terminated = false := by
    rw [← ReferenceWorkQueue.State.rawEventReplay_state,
      ReferenceWorkQueue.State.rawEventReplay_terminated]
    exact ReferenceWorkQueue.createWorkQueue_terminated _
  have unchanged : { initial.replayGraphEvents inputs.flatten with
      terminated := (initial.replayGraphEvents inputs.flatten).terminated }
      = initial.replayGraphEvents inputs.flatten := by
    cases initial.replayGraphEvents inputs.flatten
    rfl
  have exactState : (initial.runNormalized inputs).1 = initial.replayGraphEvents inputs.flatten := by
    rw [same, flag]
    simpa only [rawFlag] using unchanged
  refine ⟨?_, ?_, initial.batchesStarted_acceptsBatch inputs earlier⟩
  · rw [State.runNormalized_initialize work inputs generated valid
      (by rwa [ReferenceWorkQueue.inputsStarted_eq_batchesStarted])]
    change (State.fromReference (initial.runNormalized inputs).1).queue
      = initial.replayGraphEvents inputs.flatten
    rw [exactState]
    simp only [State.fromReference, rawFlag, Bool.false_eq_true, ↓reduceIte]
  · rwa [ReferenceWorkQueue.inputsStarted_eq_batchesStarted]

/-- The singleton dispatch boundary specializes the same actual next-batch projection. -/
theorem generatedReplay_beforeNext {work inputs event}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (valid : ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ [event]))
    (started : ReferenceWorkQueue.inputsStarted work (inputs ++ [[event]]) = true)
    : ((State.initialize work).runNormalized inputs).1.queue
        = (ReferenceWorkQueue.State.initialize
            (ReferenceWorkQueue.Work.fromExecution work)).replayGraphEvents
            inputs.flatten
      ∧ ReferenceWorkQueue.inputsStarted work inputs = true
      ∧ (ReferenceWorkQueue.State.initialize
          (ReferenceWorkQueue.Work.fromExecution work)).acceptsBatch
          inputs.flatten
        = true :=
  generatedReplay_beforeBatch generated (valid.prefix ⟨[event], rfl⟩) started

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
      ((before.handleGraphEvent event).1.queue, (before.handleGraphEvent event).2.1)
      = before.queue.handleGraphEvent event := by
  obtain ⟨raw, _, accepted⟩ := generatedReplay_beforeNext generated valid started
  rw [generatedReplay_beforeNextState generated valid started, raw]
  exact referencePrefix_handleGraphEvent generated inputs.flatten event valid accepted

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
