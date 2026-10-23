import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FiniteGraphEvents
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CursorReplay

/-! Finite nonblocking of the concrete queue for nonstalling host input languages. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- A finite fresh-event budget converts local continuation into a terminal continuation
-----------------------------------------------------------------------------------------

/-- Every admitted input prefix can finish if each unfinished prefix admits another
nonempty batch. Witness: strong induction on the remaining finite settlement budget.
The continuation extends the actual supplied inputs, not an alternative realization of
the same output. Source `finished` and elapsed host time are deliberately irrelevant.
-/
theorem admittedInputs_canFinish {work : Execution.Work}
    {schedule : EventSource (List GraphEvent)} (valid : schedule.ValidFor work)
    (next
      : ∀ inputs,
          schedule.admissible inputs
          → ((State.initialize (Work.fromExecution work)).runNormalized
              inputs).1.terminated
            ≠ true
          → ∃ batch, batch ≠ [] ∧ schedule.admissible (inputs ++ [batch]))
    {inputs : List (List GraphEvent)} (admitted : schedule.admissible inputs)
    : ∃ suffix,
        schedule.admissible (inputs ++ suffix)
        ∧ ((State.initialize (Work.fromExecution work)).runNormalized
            (inputs ++ suffix)).1.terminated
          = true := by
  let budget := 2 * (observationTokens [] work).length
  have bounded : ∀ history, schedule.admissible history → history.flatten.length ≤ budget :=
    fun history accepted => (valid.2.2.2.2 history accepted).1.length_le_budget
  have finish (remaining : Nat) : ∀ history, schedule.admissible history →
      budget - history.flatten.length = remaining →
      ∃ suffix, schedule.admissible (history ++ suffix) ∧
        ((State.initialize (Work.fromExecution work)).runNormalized
          (history ++ suffix)).1.terminated = true := by
    induction remaining using Nat.strongRecOn with
    | ind remaining ih =>
        intro history accepted same
        by_cases ended :
          ((State.initialize (Work.fromExecution work)).runNormalized
            history).1.terminated
          = true
        · exact ⟨[], by simpa using accepted, by simpa using ended⟩
        obtain ⟨batch, nonempty, extended⟩ := next history accepted ended
        have positive := List.length_pos_iff.mpr nonempty
        have longer : (history ++ [batch]).flatten.length =
            history.flatten.length + batch.length := by simp
        have within := bounded (history ++ [batch]) extended
        have smaller : budget - (history ++ [batch]).flatten.length < remaining := by omega
        obtain ⟨suffix, allowed, terminal⟩ :=
          ih _ smaller (history ++ [batch]) extended rfl
        exact ⟨
          batch :: suffix,
          by simpa [List.append_assoc] using allowed,
          by simpa [List.append_assoc] using terminal
        ⟩
  exact finish _ inputs admitted rfl

-----------------------------------------------------------------------------------------
-- Normalization retains the observed output prefix when input replay resumes
-----------------------------------------------------------------------------------------

/-- Appending inputs appends normalized output batches without changing earlier ones.
Witness: shared queue/publisher replay composition, including silent input batches.
-/
theorem State.runNormalized_outputs_prefix (queue : State)
    (before after : List (List GraphEvent))
    : (queue.runNormalized before).2.IsPrefix
        (queue.runNormalized (before ++ after)).2 := by
  change (queue.runWithPublisher _ before).2.2.IsPrefix
    (queue.runWithPublisher _ (before ++ after)).2.2
  rw [State.runWithPublisher_append]
  exact ⟨_, rfl⟩

/-- Terminal input continuations yield finite nonblocking at the exposed queue boundary.
Witness: preserve the caller's input prefix, then use replay composition to extract its
output suffix. Publisher normalization and omitted silent batches do not break the prefix.
-/
theorem createWorkQueueForSchedule_nonblocking_of_inputsCanFinish
    {work : Execution.Work} {schedule : EventSource (List GraphEvent)}
    (finish
      : ∀ inputs,
          schedule.admissible inputs
          → ∃ suffix,
              schedule.admissible (inputs ++ suffix)
              ∧ ((State.initialize (Work.fromExecution work)).runNormalized
                  (inputs ++ suffix)).1.terminated
                = true)
    : (createWorkQueueForSchedule work schedule).Nonblocking := by
  intro batches admitted
  obtain ⟨inputs, accepted, same⟩ := admitted
  change ((State.initialize (Work.fromExecution work)).runNormalized inputs).2 = batches at same
  obtain ⟨more, extended, terminal⟩ := finish inputs accepted
  obtain ⟨suffix, outputs⟩ :=
    (State.initialize (Work.fromExecution work)).runNormalized_outputs_prefix inputs more
  refine ⟨suffix, inputs ++ more, extended, ?_, terminal⟩
  change ((State.initialize (Work.fromExecution work)).runNormalized
    (inputs ++ more)).2 = batches ++ suffix
  simpa only [same] using outputs.symm

/-- A valid nonstalling input language makes the concrete queue finitely nonblocking.
Witness: finite fresh-event induction and exact input/output-prefix replay composition.
This helper's local premise applies at every unfinished queue prefix; reducing it to
only healthy unsettled tasks and live streams requires a separate readiness theorem.
-/
theorem createWorkQueueForSchedule_nonblocking
    {work : Execution.Work} {schedule : EventSource (List GraphEvent)}
    (valid : schedule.ValidFor work)
    (nonblocking : schedule.NonblockingFor work)
    : (createWorkQueueForSchedule work schedule).Nonblocking :=
  createWorkQueueForSchedule_nonblocking_of_inputsCanFinish
    (fun _ admitted => admittedInputs_canFinish valid nonblocking admitted)

/-- The reference implementation satisfies the optional public nonblocking statement.
Witness: `createWorkQueueForSchedule_nonblocking` proves the transfer for arbitrary work;
executed-work and nonemptiness premises restrict its public execution scope.
-/
theorem implementationNonblocking_holds : ImplementationNonblocking := by
  intro work schedule _generated _nonempty valid nonblocking
  exact createWorkQueueForSchedule_nonblocking valid nonblocking

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
