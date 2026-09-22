import GraphQL.IncrementalDelivery.WorkQueueImplementation
import GraphQL.IncrementalDelivery.Observation

/-! Definition-only checks of the shared source and observable work-queue interfaces. -/

namespace GraphQL.IncrementalDelivery.Tests.WorkQueueInterfaces

open ReferenceWorkQueue

/-- The full constructor exposes the state initializer's notices without changing them. -/
example (work : Execution.Work) (schedule : EventSource (List GraphEvent))
    : (createWorkQueueForSchedule work schedule).initialGroups
        = (State.initialize (Work.fromExecution work)).initialGroups
      ∧ (createWorkQueueForSchedule work schedule).initialStreams
        = (State.initialize (Work.fromExecution work)).initialStreams :=
  ⟨rfl, rfl⟩

/-- The single source predicate contains exactly the former event and start laws. -/
example (work : Execution.Work) (schedule : EventSource (List GraphEvent))
    : schedule.ValidFor work
      ↔ schedule.history = []
        ∧ schedule.admissible []
        ∧ (∀ before after,
            before.IsPrefix after
            → schedule.admissible after
            → schedule.admissible before)
        ∧ (∀ batches, schedule.admissible batches → ValidGraphEvents work batches.flatten)
        ∧ (∀ batches,
            schedule.admissible batches → inputsStarted work batches = true) := by
  constructor
  · rintro ⟨history, empty, prefixes, batches⟩
    exact ⟨history, empty, prefixes, fun xs allowed => (batches xs allowed).1,
      fun xs allowed => (batches xs allowed).2⟩
  · rintro ⟨history, empty, prefixes, events, starts⟩
    exact ⟨history, empty, prefixes, fun xs allowed => ⟨events xs allowed, starts xs allowed⟩⟩

/-- A source admitting only the empty input satisfies the host contract for arbitrary
work. Initial-notice correctness and progress are not hidden source assumptions.
-/
example (work : Execution.Work)
    : EventSource.ValidFor (EventSource.ofList ([] : List (List GraphEvent))) work := by
  refine ⟨rfl, List.prefix_refl _, ?_, ?_⟩
  · intro before after prior accepted
    exact prior.trans accepted
  · intro batches accepted
    change batches.IsPrefix [] at accepted
    obtain rfl := List.prefix_nil.mp accepted
    exact ⟨.nil, rfl⟩

/-- Conformance requires only nonempty executed work and a valid source.
This exact definition-level check rules out an extra caller initialization premise.
-/
example
    : createWorkQueueForScheduleConforms
      ↔ ∀ work (schedule : EventSource (List GraphEvent)),
          let queue := createWorkQueueForSchedule work schedule
          ExecutedWork work
          → work.size ≠ 0
          → schedule.ValidFor work
          → queue.Conforms work :=
  Iff.rfl

/-- Per-work sources and source families express the same conformance requirement.
Witness: specialize a family forward and use a constant family backward.
-/
example
    : createWorkQueueForScheduleConforms
      ↔ ∀ (sources : Execution.Work → EventSource (List GraphEvent)) work,
          ExecutedWork work
          → (sources work).ValidFor work
          → work.size ≠ 0
          → (createWorkQueueForSchedule work (sources work)).Conforms work := by
  constructor
  · intro conforms sources work
    intro executed valid nonempty
    exact conforms work (sources work) executed nonempty valid
  · intro conforms work schedule
    intro executed nonempty valid
    exact conforms (fun _ => schedule) work executed valid nonempty

/-- Query inputs precede the schedule and observed result. The definition retains source
validity and finite replay, without assuming the conformance it is used to prove.
-/
example (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variables : Execution.VariableValues) (operation : Operation) (fuel : Nat)
    (root : Execution.ResolverValue ObjectRef) (schedule : EventSource (List GraphEvent))
    (result : Execution.ExecutionObservation) (complete : Bool)
    : queryScheduleMatches schema resolvers variables operation fuel root schedule result
        complete
      ↔ let completed := queryCompletion schema resolvers variables operation fuel root
        Execution.rootSourceAppliesBool schema operation root = true
        ∧ completed.work.size ≠ 0
        ∧ schedule.ValidFor completed.work
        ∧ ∃ inputs,
            schedule.admissible inputs
            ∧ let (initial, updates, terminated) :=
                replayIncrementalResponse completed inputs
              (complete = true → terminated = true)
              ∧ result = .incremental initial updates :=
  Iff.rfl

end GraphQL.IncrementalDelivery.Tests.WorkQueueInterfaces
