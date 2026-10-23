import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CursorReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InputReplay

/-! Startup notices remain in state; ordinary replay supplies initialization and prefixes. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue

/-- Startup source admission uses the actual initialized state and ordinary batch checker. -/
theorem inputsStartedWithStartup_eq_batchesStarted (work : Execution.Work)
    (inputs : List (List GraphEvent)) (startup : InitialStartup)
    : inputsStarted work inputs startup
      = (State.initialize (Work.fromExecution work) startup).batchesStarted inputs := by
  unfold inputsStarted
  rw [State.fold_started_eq]
  rfl

/-- Source initialization holds with pending notices and no supplied input. -/
theorem createWorkQueueForSchedule_startup_initialized (work : Execution.Work)
    (source : EventSource (List GraphEvent)) (startup : InitialStartup)
    (empty : source.admissible [])
    : (createWorkQueueForSchedule work source startup).Initialized := by
  exact ⟨rfl, [], empty, rfl⟩

/-- Prefix closure uses the ordinary runner, whose state retains all pending notices. -/
theorem createWorkQueueForSchedule_startup_prefixClosed (work : Execution.Work)
    (source : EventSource (List GraphEvent)) (startup : InitialStartup)
    (closed
      : ∀ before after,
          before.IsPrefix after → source.admissible after → source.admissible before)
    : (createWorkQueueForSchedule work source startup).PrefixClosed := by
  let initial := State.initialize (Work.fromExecution work) startup
  intro before after earlier admitted
  change ∃ inputs, source.admissible inputs ∧ (initial.runNormalized inputs).2 = after at admitted
  obtain ⟨inputs, accepted, same⟩ := admitted
  have prefixOfOutput : before.IsPrefix (initial.runNormalized inputs).2 := by
    rw [same]
    exact earlier
  obtain ⟨prior, prefixOfInputs, output⟩ := initial.runNormalized_prefix_reachable inputs before prefixOfOutput
  exact ⟨prior, closed prior inputs prefixOfInputs accepted, output⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue

namespace GraphQL.IncrementalDelivery.EventSource
open ReferenceWorkQueue

/-- Startup-aware sources retain the ordinary empty-history and prefix language laws. -/
theorem ValidFor.sourceLaws {work startup} {source : EventSource (List GraphEvent)}
    (valid : source.ValidFor work startup)
    : source.history = []
      ∧ source.admissible []
      ∧ ∀ before after,
          before.IsPrefix after → source.admissible after → source.admissible before :=
  ⟨valid.2.1, valid.2.2.1, valid.2.2.2.1⟩

end GraphQL.IncrementalDelivery.EventSource

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue

/-- Every startup-valid source satisfies both source-language clauses of queue conformance.
Work accounting and terminal reporting remain independent proof obligations.
-/
theorem createWorkQueueForSchedule_startup_sourceClauses {work startup}
    {source : EventSource (List GraphEvent)} (valid : source.ValidFor work startup)
    : (createWorkQueueForSchedule work source startup).Initialized
      ∧ (createWorkQueueForSchedule work source startup).PrefixClosed := by
  have laws := valid.sourceLaws
  exact ⟨createWorkQueueForSchedule_startup_initialized work source startup laws.2.1,
    createWorkQueueForSchedule_startup_prefixClosed work source startup laws.2.2⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
