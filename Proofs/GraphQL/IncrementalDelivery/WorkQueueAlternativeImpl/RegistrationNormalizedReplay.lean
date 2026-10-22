import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationBatchReplay
import Proofs.GraphQL.IncrementalDelivery.Semantics.WorkSize

/-! Exact generated replay and factory equivalence under the original source contract. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)

-----------------------------------------------------------------------------------------
-- Terminal projection retains the public observations
-----------------------------------------------------------------------------------------

@[simp]
theorem State.fromReference_initialGroups (queue : ReferenceWorkQueue.State)
    : (State.fromReference queue).queue.initialGroups = queue.initialGroups := by
  simp only [State.fromReference]
  split <;> rfl

@[simp]
theorem State.fromReference_initialStreams (queue : ReferenceWorkQueue.State)
    : (State.fromReference queue).queue.initialStreams = queue.initialStreams := by
  simp only [State.fromReference]
  split <;> rfl

@[simp]
theorem State.fromReference_terminated (queue : ReferenceWorkQueue.State)
    : (State.fromReference queue).queue.terminated = queue.terminated := by
  simp only [State.fromReference]
  split <;> rfl

/-- Reference termination retires the graph reader; live projections are not interrupted. -/
theorem State.fromReference_stopped (queue : ReferenceWorkQueue.State)
    : (State.fromReference queue).stopped = queue.terminated := by
  cases ended : queue.terminated <;> simp [State.fromReference, ended, State.clearRecords]

private theorem fromReference_terminated (queue : ReferenceWorkQueue.State)
    : (State.fromReference queue).queue.terminated = queue.terminated := by
  unfold State.fromReference
  split <;> rfl

/-- Checked factory reduction using only admitted inputs of the original valid source.
Witness: the replay target supplies both emitted batches and projected termination;
propositional/function extensionality then identifies the two opaque output sources.
This deliberately does not assume replay equality on arbitrary malformed graph inputs.
-/
theorem createWorkQueueForScheduleMatchesReference_of_replay
    (replay : replayMatchesReference)
    : createWorkQueueForScheduleMatchesReference := by
  intro work schedule generated _ valid
  let alternative := State.initialize work
  let reference := ReferenceWorkQueue.State.initialize (ReferenceWorkQueue.Work.fromExecution work)
  have emitted (inputs : List (List GraphEvent)) (admitted : schedule.admissible inputs)
      : (alternative.runNormalized inputs).2 = (reference.runNormalized inputs).2
        ∧ (alternative.runNormalized inputs).1.queue.terminated
          = (reference.runNormalized inputs).1.terminated := by
    obtain ⟨matching, started, _⟩ := valid.2.2.2.2 inputs admitted
    obtain ⟨state, outputs⟩ := replay work inputs generated matching started
    exact ⟨outputs, (congrArg (fun state : State => state.queue.terminated) state).trans
      (fromReference_terminated _)⟩
  have admissible : (fun outputs => ∃ inputs, schedule.admissible inputs
        ∧ (alternative.runNormalized inputs).2 = outputs)
      = (fun outputs => ∃ inputs, schedule.admissible inputs
        ∧ (reference.runNormalized inputs).2 = outputs) := by
    funext outputs
    apply propext
    constructor
    · rintro ⟨inputs, admitted, same⟩
      exact ⟨inputs, admitted, (emitted inputs admitted).1.symm.trans same⟩
    · rintro ⟨inputs, admitted, same⟩
      exact ⟨inputs, admitted, (emitted inputs admitted).1.trans same⟩
  have finished : (fun outputs => ∃ inputs, schedule.admissible inputs
        ∧ (alternative.runNormalized inputs).2 = outputs
        ∧ (alternative.runNormalized inputs).1.queue.terminated = true)
      = (fun outputs => ∃ inputs, schedule.admissible inputs
        ∧ (reference.runNormalized inputs).2 = outputs
        ∧ (reference.runNormalized inputs).1.terminated = true) := by
    funext outputs
    apply propext
    constructor
    · rintro ⟨inputs, admitted, same, ended⟩
      obtain ⟨batches, terminal⟩ := emitted inputs admitted
      exact ⟨inputs, admitted, batches.symm.trans same, terminal.symm.trans ended⟩
    · rintro ⟨inputs, admitted, same, ended⟩
      obtain ⟨batches, terminal⟩ := emitted inputs admitted
      exact ⟨inputs, admitted, batches.trans same, terminal.trans ended⟩
  unfold createWorkQueueForSchedule ReferenceWorkQueue.createWorkQueueForSchedule
  dsimp only
  rw [admissible, finished, State.initialize_queue]

private abbrev ReferenceAcc :=
  ReferenceWorkQueue.State
  × ReferenceWorkQueue.IncrementalPublisher
  × List (List WorkQueueEvent)

private abbrev AlternativeAcc :=
  State × ReferenceWorkQueue.IncrementalPublisher × List (List WorkQueueEvent)

private abbrev referenceStep (acc : ReferenceAcc) (batch : List GraphEvent)
    : ReferenceAcc :=
  let handled := acc.1.handleGraphEvents batch
  if handled.2.isEmpty then
    (handled.1, acc.2.1, acc.2.2)
  else
    let normalized := acc.2.1.normalizeBatch handled.2
    (handled.1, normalized.1, acc.2.2 ++ [normalized.2])

private abbrev alternativeStep (acc : AlternativeAcc) (batch : List GraphEvent)
    : AlternativeAcc :=
  let handled := acc.1.handleGraphEvents batch
  if handled.workQueueEvents.isEmpty then
    (handled.state, acc.2.1, acc.2.2)
  else
    let normalized := acc.2.1.normalizeBatch handled.workQueueEvents
    (handled.state, normalized.1, acc.2.2 ++ [normalized.2])

-----------------------------------------------------------------------------------------
-- Normalization threads the shared publisher over generated batches
-----------------------------------------------------------------------------------------

private theorem normalizedFold {work : Work}
    (generated : ReferenceWorkQueue.ExecutedWork work) (earlier : List (List GraphEvent))
    (inputs : List (List GraphEvent))
    (valid : ReferenceWorkQueue.ValidGraphEvents work (earlier ++ inputs).flatten)
    (started : ReferenceWorkQueue.inputsStarted work (earlier ++ inputs) = true)
    (publisher : ReferenceWorkQueue.IncrementalPublisher)
    (outputs : List (List WorkQueueEvent))
    : let queue :=
        (ReferenceWorkQueue.State.initialize
          (ReferenceWorkQueue.Work.fromExecution work)).replayBatches
          earlier
      inputs.foldl alternativeStep (State.fromReference queue, publisher, outputs)
      = let reference := inputs.foldl referenceStep (queue, publisher, outputs)
        (State.fromReference reference.1, reference.2.1, reference.2.2) := by
  let initial := ReferenceWorkQueue.State.initialize (ReferenceWorkQueue.Work.fromExecution work)
  induction inputs generalizing earlier publisher outputs with
  | nil => rfl
  | cons batch rest ih =>
      let queue := initial.replayBatches earlier
      have bridge := referencePrefix_handleGraphEvents generated earlier batch rest valid started
      change ((State.fromReference queue).handleGraphEvents batch).state
          = State.fromReference (queue.handleGraphEvents batch).1
        ∧ ((State.fromReference queue).handleGraphEvents batch).workQueueEvents
          = (queue.handleGraphEvents batch).2 at bridge
      have validNext : ReferenceWorkQueue.ValidGraphEvents work
          ((earlier ++ [batch]) ++ rest).flatten := by
        simpa only [List.append_assoc, List.singleton_append] using valid
      have startedNext : ReferenceWorkQueue.inputsStarted work ((earlier ++ [batch]) ++ rest)
          = true := by
        simpa only [List.append_assoc, List.singleton_append] using started
      have queueNext : initial.replayBatches (earlier ++ [batch])
          = (queue.handleGraphEvents batch).1 := by
        rw [ReferenceWorkQueue.State.replayBatches_append]
        rfl
      change (batch :: rest).foldl alternativeStep (State.fromReference queue, publisher, outputs)
        = let reference := (batch :: rest).foldl referenceStep (queue, publisher, outputs)
          (State.fromReference reference.1, reference.2.1, reference.2.2)
      simp only [List.foldl_cons, alternativeStep, referenceStep, bridge.1, bridge.2]
      split
      · have next := ih (earlier ++ [batch]) validNext startedNext publisher outputs
        rw [queueNext] at next
        exact next
      · have next := ih (earlier ++ [batch]) validNext startedNext
          (publisher.normalizeBatch (queue.handleGraphEvents batch).2).1
          (outputs ++ [(publisher.normalizeBatch (queue.handleGraphEvents batch).2).2])
        rw [queueNext] at next
        exact next

/-- Generated normalized replay has exactly the reference output and terminal projection.
Witness: the public start checker supplies actual host batches; the queue follows their
cache snapshots, and terminal retirement uses the existing reference projection.
The generated-work domain excludes malformed task catalogues with conflicting owners.
-/
theorem State.runNormalized_initialize (work : Work) (inputs : List (List GraphEvent))
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (valid : ReferenceWorkQueue.ValidGraphEvents work inputs.flatten)
    (started : ReferenceWorkQueue.inputsStarted work inputs = true)
    : (State.initialize work).runNormalized inputs
      = let reference :=
          (ReferenceWorkQueue.State.initialize
            (ReferenceWorkQueue.Work.fromExecution work)).runNormalized
            inputs
        (State.fromReference reference.1, reference.2) := by
  let queue := ReferenceWorkQueue.State.initialize (ReferenceWorkQueue.Work.fromExecution work)
  have same := normalizedFold generated [] inputs (by simpa using valid) (by simpa using started)
    ({ active := queue.initialGroups ++ queue.initialStreams } :
      ReferenceWorkQueue.IncrementalPublisher) []
  rw [State.initialize_fromReference]
  simp only [State.runNormalized, ReferenceWorkQueue.State.runNormalized,
    State.fromReference_initialGroups,
    State.fromReference_initialStreams]
  exact congrArg (fun result : AlternativeAcc => (result.1, result.2.2)) same

/-- Witness of the exact public replay target, with no new caller or host assumption. -/
theorem replayMatchesReference_holds : replayMatchesReference := by
  intro work inputs generated valid started
  rw [State.runNormalized_initialize work inputs generated valid started]
  exact ⟨rfl, rfl⟩

/-- Witness of the original factory-equivalence target on valid generated sources. -/
theorem createWorkQueueForScheduleMatchesReference_holds
    : createWorkQueueForScheduleMatchesReference :=
  createWorkQueueForScheduleMatchesReference_of_replay replayMatchesReference_holds

/-- The observable source factory equals the reference factory under its original premises. -/
theorem createWorkQueueForSchedule_eq_reference (work : Work)
    (schedule : EventSource (List GraphEvent))
    (generated : ReferenceWorkQueue.ExecutedWork work) (nonempty : work.size ≠ 0)
    (valid : schedule.ValidFor work)
    : createWorkQueueForSchedule work schedule
      = ReferenceWorkQueue.createWorkQueueForSchedule work schedule :=
  createWorkQueueForScheduleMatchesReference_holds work schedule generated
    ((Execution.Work.isEmpty_eq_false work).mpr nonempty) valid

end GraphQL.IncrementalDelivery.AlternativeWorkQueue
