import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupConformanceCertificates
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialStartupSourceFrames
import Proofs.GraphQL.IncrementalDelivery.Semantics.WorkSize

/-! Full queue conformance for arbitrary source-valid synchronous startup observations. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Proof projection of actual normalized startup replay, retaining its initial notices. -/
def State.normalizedStartupHistory (queue : State) (inputs : List (List GraphEvent))
    : History :=
  {
    initialGroups := queue.initialGroups
    initialStreams := queue.initialStreams
    batches := (queue.runNormalized inputs).2
  }

namespace ConformancePlan

/-- A complete abstract run is equivalent to the actual startup replay's terminal flag.
The forward direction reflects the real final marker through batching. The reverse uses
all three constructed terminal leaves on the very same witness and history.
-/
theorem startup_run_iff_terminated {work} {queue : State} {inputs}
    {w : Witness}
    (explained
      : Explains work queue.initialGroups queue.initialStreams
          w.events w.matching w.failures)
    (batching
      : WorkBatching
          (w.events
            ++ if (queue.runNormalized inputs).1.terminated then
                  [.workQueueTermination]
                else
                  [])
          (queue.runNormalized inputs).2)
    (accounted
      : (queue.runNormalized inputs).1.terminated = true
        → Terminal work
            ((queue.initialGroups ++ queue.initialStreams).map Execution.DeliveryNode.ref)
            w.matching w.events w.failures)
    : AdmissibleRun work (queue.normalizedStartupHistory inputs)
      ↔ (queue.runNormalized inputs).1.terminated = true := by
  constructor
  · rintro ⟨events, matching, failures, _, _, grouped⟩
    have marker := grouped.termination_mem.mpr
      (by simp : WorkQueueEvent.workQueueTermination ∈ events ++ [.workQueueTermination])
    have actual := batching.termination_mem.mp marker
    cases done : (queue.runNormalized inputs).1.terminated with
    | false =>
        simp only [done, Bool.false_eq_true, ↓reduceIte, List.append_nil] at actual
        exact False.elim (explained.noTermination actual)
    | true => rfl
  · intro done
    refine ⟨w.events, w.matching, w.failures, explained, accounted done, ?_⟩
    simpa only [State.normalizedStartupHistory, done, ↓reduceIte] using batching

/-- Every actual startup replay is an explained prefix or a complete accounted run.
Only the concrete final flag chooses the case; no fairness or source completion is assumed.
-/
theorem startup_validHistory {work} {queue : State} {inputs} {w : Witness}
    (explained
      : Explains work queue.initialGroups queue.initialStreams
          w.events w.matching w.failures)
    (batching
      : WorkBatching
          (w.events
            ++ if (queue.runNormalized inputs).1.terminated then
                  [.workQueueTermination]
                else
                  [])
          (queue.runNormalized inputs).2)
    (accounted
      : (queue.runNormalized inputs).1.terminated = true
        → Terminal work
            ((queue.initialGroups ++ queue.initialStreams).map Execution.DeliveryNode.ref)
            w.matching w.events w.failures)
    : ValidHistory work (queue.normalizedStartupHistory inputs) := by
  cases done : (queue.runNormalized inputs).1.terminated with
  | false =>
      left
      refine ⟨w.events, w.matching, w.failures, explained, ?_⟩
      simpa only [State.normalizedStartupHistory, done, Bool.false_eq_true, ↓reduceIte,
        List.append_nil] using batching
  | true =>
      right
      exact (startup_run_iff_terminated explained batching accounted).mpr done

end ConformancePlan

/-- Actual startup source replay satisfies all four unchanged public queue clauses.
Source-language initialization and prefix closure are independent of output accounting.
For each admitted input, one constructed witness proves both accounting and the exact
finished/run equivalence, including initial failures retained until their observed FIFO dispatch.
-/
theorem createWorkQueueForSchedule_startup_conforms {work startup}
    {source : EventSource (List GraphEvent)} (generated : ExecutedWork work)
    (nonempty : work.size ≠ 0) (valid : source.ValidFor work startup)
    : (createWorkQueueForSchedule work source startup).Conforms work := by
  have sourceClauses := createWorkQueueForSchedule_startup_sourceClauses valid
  let initial := State.initialize (Work.fromExecution work) startup
  have certificates inputs (accepted : source.admissible inputs) :=
    ConformancePlan.startup_replayCertificates generated nonempty startup valid.cachedMatches
      (valid.admittedProperties accepted).1 (valid.admittedProperties accepted).2
  refine ⟨sourceClauses.1, sourceClauses.2, ?_, ?_⟩
  · intro outputs admitted
    obtain ⟨inputs, accepted, same⟩ := admitted
    obtain ⟨w, batching, explained, accounted⟩ := certificates inputs accepted
    have history := ConformancePlan.startup_validHistory explained batching accounted
    change ValidHistory work
      { initialGroups := initial.initialGroups
        initialStreams := initial.initialStreams
        batches := outputs }
    cases same
    exact history
  · intro outputs
    constructor
    · rintro ⟨inputs, accepted, same, done⟩
      obtain ⟨w, batching, explained, accounted⟩ := certificates inputs accepted
      refine ⟨⟨inputs, accepted, same⟩, ?_⟩
      have run := (ConformancePlan.startup_run_iff_terminated explained batching accounted).mpr done
      cases same
      exact run
    · rintro ⟨⟨inputs, accepted, same⟩, run⟩
      obtain ⟨w, batching, explained, accounted⟩ := certificates inputs accepted
      refine ⟨inputs, accepted, same, ?_⟩
      apply (ConformancePlan.startup_run_iff_terminated explained batching accounted).mp
      cases same
      exact run

/-- The reference queue conforms for every source-valid startup observation.
All failures, publications, carried notices, terminal work and covering reports use the
same actual replay witness. The established empty-startup theorem remains available.
-/
theorem createWorkQueueForScheduleConformsWithStartup_holds (startup : InitialStartup)
    : createWorkQueueForScheduleConforms startup := by
  intro work schedule generated nonempty valid
  have nonempty := (Execution.Work.isEmpty_eq_false work).mp nonempty
  exact createWorkQueueForSchedule_startup_conforms generated nonempty valid

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
