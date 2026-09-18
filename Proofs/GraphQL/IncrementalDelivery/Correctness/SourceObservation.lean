import Proofs.GraphQL.IncrementalDelivery.Correctness.InputObservation

/-! Work-accounting witnesses behind actual source observations.
Source conformance supplies histories, not wire safety or response-equivalence assumptions.
-/

namespace GraphQL.IncrementalDelivery.Execution

/-- Initialized, prefix-closed sources admit inputs exactly when they admit the full
history. Witness: inspect the full prefix in one direction and use prefix closure in the
other.
-/
theorem WorkQueueResult.allows_iff_admissible (source : WorkQueueResult)
    (initialized : source.Initialized) (closed : source.PrefixClosed)
    (batches : List (List WorkEvent))
    : source.workEventStream.Allows batches
      ↔ source.workEventStream.admissible batches := by
  constructor
  · intro allowed
    simpa [initialized.1] using allowed batches (List.prefix_refl _)
  · intro admitted prior before
    simpa [initialized.1] using closed prior batches before admitted

/-- A conforming source has an actual nonempty initialization witness, not vacuous
admission. Witness: account for its admitted empty history and retain the run's
initialization.
-/
theorem WorkQueueResult.Conforms.initializes {source : WorkQueueResult} {work : Work}
    (conforms : source.Conforms work)
    : WorkScheduler.Initializes work source.initialGroups source.initialStreams := by
  rcases conforms.2.2.1 [] conforms.1.2 with prefixRun | run
  · obtain ⟨_, _, _, explained, _⟩ := prefixRun
    exact explained.1
  · obtain ⟨_, _, _, explained, _⟩ := run
    exact explained.1

/-- Actual batched mapper observations have independently admitted work histories.
Witness: replay exposes ordered nonempty response groups; conformance accounts for their
flattened work batches and characterizes termination, without inspecting wire IDs.
-/
theorem WorkQueueResult.observes_workHistory (source : WorkQueueResult) (work : Work)
    (ids : IDState) (conforms : source.Conforms work)
    {updates : List IncrementalStreamUpdateResult} {final : ResponseEventStream}
    (observed
      : (batchIncrementalResults
          (mapIncrementalWorkEventsToResponseEvent source.workEventStream ids)).Observes
          updates final)
    : ∃ groups : List (List (List WorkEvent)),
        (∀ group ∈ groups, group ≠ [])
        ∧ source.workEventStream.Allows groups.flatten
        ∧ (WorkScheduler.AdmissiblePrefix work (source.toHistory groups.flatten)
            ∨ WorkScheduler.AdmissibleRun work (source.toHistory groups.flatten))
        ∧ updates
          = ((batchIncrementalResults
                (mapIncrementalWorkEventsToResponseEvent source.workEventStream
                  ids)).mapInputs
              groups).1
        ∧ (final.source.IsFinished
            ↔ WorkScheduler.AdmissibleRun work (source.toHistory groups.flatten)) := by
  have initial : source.workEventStream.admissible source.workEventStream.history := by
    simpa [conforms.1.1] using conforms.1.2
  obtain ⟨groups, nonempty, allowed, outputs, residual⟩ :=
    (ResponseEventStream.batch_observes_iff_inputs _ _ _ initial).mp observed
  change List (List (List WorkEvent)) at groups
  have admitted := (source.allows_iff_admissible conforms.1 conforms.2.1 _).mp allowed
  refine ⟨groups, nonempty, allowed, conforms.2.2.1 _ admitted, outputs, ?_⟩
  rw [residual]
  change ((∀ group ∈ groups, group ≠ []) ∧ source.workEventStream.Allows groups.flatten)
    ∧ source.workEventStream.finished (source.workEventStream.history ++ groups.flatten) ↔ _
  rw [conforms.1.1, List.nil_append, conforms.2.2.2]
  exact ⟨fun h => h.2.2, fun run => ⟨⟨nonempty, allowed⟩, admitted, run⟩⟩

/-- A finished observation exposes a terminal work run, by the source's termination
equivalence.
-/
theorem WorkQueueResult.observes_complete_workHistory (source : WorkQueueResult)
    (work : Work) (ids : IDState) (conforms : source.Conforms work)
    {updates : List IncrementalStreamUpdateResult} {final : ResponseEventStream}
    (observed
      : (batchIncrementalResults
          (mapIncrementalWorkEventsToResponseEvent source.workEventStream ids)).Observes
          updates final)
    (finished : final.source.IsFinished)
    : ∃ groups : List (List (List WorkEvent)),
        (∀ group ∈ groups, group ≠ [])
        ∧ WorkScheduler.AdmissibleRun work (source.toHistory groups.flatten)
        ∧ updates
          = ((batchIncrementalResults
                (mapIncrementalWorkEventsToResponseEvent source.workEventStream
                  ids)).mapInputs
              groups).1 := by
  obtain ⟨groups, nonempty, _, _, outputs, terminal⟩ :=
    source.observes_workHistory work ids conforms observed
  exact ⟨groups, nonempty, terminal.mp finished, outputs⟩

end GraphQL.IncrementalDelivery.Execution
