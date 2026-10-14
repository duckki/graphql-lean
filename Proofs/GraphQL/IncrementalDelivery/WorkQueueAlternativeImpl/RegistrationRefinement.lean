import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationInitialization
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.Conformance

/-! Checked reductions from the unchanged generated replay target to factory conformance.

These are conditional proof reductions, not closed replay or conformance witnesses.
RegistrationNormalizedReplay supplies the generated replay witness used by these reductions.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue

-----------------------------------------------------------------------------------------
-- Public roots retain their original source and generated-work domains
-----------------------------------------------------------------------------------------

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
    obtain ⟨matching, started⟩ := valid.2.2.2 inputs admitted
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

/-- Checked conformance reduction reuses the complete reference witness and exact premises.
Witness: factory equality transports all four independent WorkQueue contract clauses.
-/
theorem createWorkQueueForScheduleConforms_of_factory
    (factory : createWorkQueueForScheduleMatchesReference)
    : createWorkQueueForScheduleConforms := by
  intro work schedule generated nonempty valid
  rw [factory work schedule generated nonempty valid]
  exact ReferenceWorkQueue.createWorkQueueForScheduleConforms_holds
    work schedule generated nonempty valid

/-- The only semantic leaf needed by these factory/conformance reductions is public replay.
This is a checked dependency edge, not an assertion that the replay leaf is proved.
-/
theorem createWorkQueueForScheduleConforms_of_replay (replay : replayMatchesReference)
    : createWorkQueueForScheduleConforms :=
  createWorkQueueForScheduleConforms_of_factory
    (createWorkQueueForScheduleMatchesReference_of_replay replay)

end GraphQL.IncrementalDelivery.AlternativeWorkQueue
