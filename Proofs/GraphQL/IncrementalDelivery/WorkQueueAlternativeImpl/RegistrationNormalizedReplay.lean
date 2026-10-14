import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationBatchReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationRefinement

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
    (generated : ReferenceWorkQueue.ExecutedWork work) (before : List GraphEvent)
    (inputs : List (List GraphEvent))
    (valid : ReferenceWorkQueue.ValidGraphEvents work (before ++ inputs.flatten))
    (accepted
      : (ReferenceWorkQueue.State.initialize
          (ReferenceWorkQueue.Work.fromExecution work)).acceptsBatch
          before
        = true)
    (queue : ReferenceWorkQueue.State)
    (provenance
      : queue.terminated = false
        → queue
          = (ReferenceWorkQueue.State.initialize
              (ReferenceWorkQueue.Work.fromExecution work)).replayGraphEvents
              before)
    (started : queue.batchesStarted inputs = true)
    (publisher : ReferenceWorkQueue.IncrementalPublisher)
    (outputs : List (List WorkQueueEvent))
    : inputs.foldl alternativeStep (State.fromReference queue, publisher, outputs)
      = let reference := inputs.foldl referenceStep (queue, publisher, outputs)
        (State.fromReference reference.1, reference.2.1, reference.2.2) := by
  induction inputs generalizing before queue publisher outputs with
  | nil => rfl
  | cons batch rest ih =>
      obtain ⟨startOpen, batchAccepted, restStarted⟩ := queue.batchesStarted_cons batch rest started
      have same := provenance startOpen
      have acceptedNext : (ReferenceWorkQueue.State.initialize
          (ReferenceWorkQueue.Work.fromExecution work)).acceptsBatch (before ++ batch) = true := by
        rw [reference_acceptsBatch_append]
        simp only [accepted, Bool.true_and, ← same]
        exact batchAccepted
      have initialPart : (before ++ batch).IsPrefix (before ++ (batch :: rest).flatten) :=
        ⟨rest.flatten, by simp [List.append_assoc]⟩
      have bridge : ((State.fromReference queue).handleGraphEvents batch).state
            = State.fromReference (queue.handleGraphEvents batch).1
          ∧ ((State.fromReference queue).handleGraphEvents batch).workQueueEvents
            = (queue.handleGraphEvents batch).2 := by
        rw [same]
        exact referencePrefix_handleGraphEvents generated before batch
          (valid.prefix initialPart) acceptedNext
      have validNext : ReferenceWorkQueue.ValidGraphEvents work
          ((before ++ batch) ++ rest.flatten) := by
        simpa [List.append_assoc] using valid
      have provenanceNext : (queue.handleGraphEvents batch).1.terminated = false
          → (queue.handleGraphEvents batch).1 = (ReferenceWorkQueue.State.initialize
            (ReferenceWorkQueue.Work.fromExecution work)).replayGraphEvents (before ++ batch) := by
        intro nextOpen
        rw [queue.handleGraphEvents_nonterminalState batch startOpen nextOpen, same]
        simp [ReferenceWorkQueue.State.replayGraphEvents, List.foldl_append]
      simp only [List.foldl_cons, alternativeStep, referenceStep, bridge.1, bridge.2]
      split
      · exact ih (before ++ batch) validNext acceptedNext (queue.handleGraphEvents batch).1
          provenanceNext restStarted publisher outputs
      · exact ih (before ++ batch) validNext acceptedNext (queue.handleGraphEvents batch).1
          provenanceNext restStarted
          (publisher.normalizeBatch (queue.handleGraphEvents batch).2).1
          (outputs ++ [(publisher.normalizeBatch (queue.handleGraphEvents batch).2).2])

/-- Generated normalized replay has exactly the reference output and terminal projection.
Witness: the public start checker supplies accepted prefixes; live batch states equal sequential
replay, and terminal retirement is observed only through the existing reference projection.
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
  have same := normalizedFold generated [] inputs (by simpa using valid) rfl queue
    (fun _ => rfl) (by simpa only [ReferenceWorkQueue.inputsStarted_eq_batchesStarted] using started)
    ({ active := queue.initialGroups ++ queue.initialStreams } :
      ReferenceWorkQueue.IncrementalPublisher) []
  rw [State.initialize_fromReference]
  simp only [State.runNormalized, ReferenceWorkQueue.State.runNormalized,
    ReferenceWorkQueue.State.runWithPublisher, State.fromReference_initialGroups,
    State.fromReference_initialStreams]
  rw [same]

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
  createWorkQueueForScheduleMatchesReference_holds work schedule generated nonempty valid

end GraphQL.IncrementalDelivery.AlternativeWorkQueue
