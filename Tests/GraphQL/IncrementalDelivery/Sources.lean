import Tests.GraphQL.IncrementalDelivery.SpecInterfaces

/-! Definition-level regressions for partial source state and sequential observation.
These fixtures do not assert universal scheduler conformance or migrate query proofs.
-/

namespace GraphQL.IncrementalDelivery.Tests.Sources

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Tests

def branching : EventSource Nat :=
  {
    admissible := fun values => values.IsPrefix [1, 2] ∨ values.IsPrefix [2, 1],
    finished := fun values => values = [1, 2] ∨ values = [2, 1]
  }

/-- The same partial state admits two distinct next observations, not a chosen trace. -/
example : branching.Allows [1] := by
  intro initial h
  exact Or.inl (h.trans ⟨[2], rfl⟩)

example : branching.Allows [2] := by
  intro initial h
  exact Or.inr (h.trans ⟨[1], rfl⟩)

/-- A chosen observation constrains later choices. Incompatible suffixes cannot be spliced
together by forgetting the observed prefix.
-/
example : branching.admissible ((branching.advance [1]).history ++ [2]) := by
  simp [branching, EventSource.advance]

example : ¬branching.admissible ((branching.advance [1]).history ++ [1]) := by
  simp [branching, EventSource.advance]

example : ¬(branching.advance [1]).IsFinished := by
  simp [branching, EventSource.advance, EventSource.IsFinished]

example : ((branching.advance [1]).advance [2]).IsFinished := by
  simp [branching, EventSource.advance, EventSource.IsFinished]

def stalled : EventSource Nat :=
  { admissible := fun values => values = [], finished := fun _ => False }

/-- Having no admitted next value is different from having a finished source. -/
example : stalled.admissible [] := rfl

example : ¬stalled.admissible [1] := by simp [stalled]
example : ¬stalled.IsFinished := by simp [stalled, EventSource.IsFinished]
example : (EventSource.ofList ([] : List Nat)).IsFinished := rfl

/-- Aggregation must not hide an inadmissible intermediate source observation. -/
def skipsPrefix : EventSource Nat :=
  {
    admissible := fun values => values = [] ∨ values = [1, 2],
    finished := fun values => values = [1, 2]
  }

example : ¬skipsPrefix.Allows [1, 2] := by
  intro h
  have firstAllowed := h [1] ⟨[2], rfl⟩
  simp [skipsPrefix] at firstAllowed

def node : DeliveryNode := { key := 7, path := [] }

def events : List WorkEvent :=
  [
    .groupValues node [{ path := [], data := [("a", .scalar "a")] }],
    .groupSuccess node [] [],
    .workQueueTermination
  ]

def responseStream : ResponseEventStream :=
  batchIncrementalResults
    (mapIncrementalWorkEventsToResponseEvent (.ofList [events])
      { ids := [(7, "0")], nextID := 1 })

theorem allowed : responseStream.Accepts [events] :=
  SpecInterfaces.batchAccepts _ _ (by simp) (fun _ h => h)

example : ¬responseStream.Accepts [] := by
  intro h
  have admitted := h [[]] ⟨[], rfl⟩
  change (∀ group ∈ ([[]] : List (List (List WorkEvent))), group ≠ []) ∧ _ at admitted
  have nonempty := admitted.1 [] (by simp)
  exact nonempty rfl

/-! The actual mapper runs only on acceptance, reuses the initial ID, and advances both
the history and the mapper state without exposing the source's task state.
-/

#guard
  let (update, rest) := responseStream.next [events] allowed
  same update
    {
      hasNext := false,
      incremental := [.object "0" [("a", .scalar "a")]],
      completed := [{ id := "0" }]
    }
  && rest.source.history.length == 1
  && rest.ids.nextID == 1

theorem finished : (responseStream.next [events] allowed).2.source.IsFinished :=
  ⟨allowed [[events]] ⟨[], rfl⟩, rfl⟩

def initial : InitialIncrementalStreamResult :=
  { data := .object [], pending := [{ id := "0", path := [] }], hasNext := true }

/-- Observing no updates is a valid prefix, but not a complete execution here. -/
example
    : (ExecutionResult.incremental initial responseStream).Observes
        (.incremental initial []) :=
  ⟨rfl, responseStream, .nil _, by simp⟩

example
    : ¬(ExecutionResult.incremental initial responseStream).Observes
        (.incremental initial []) true := by
  rintro ⟨_, final, observed, finished⟩
  cases observed
  have h := finished rfl
  simp [responseStream, batchIncrementalResults, mapIncrementalWorkEventsToResponseEvent,
    EventSource.IsFinished, EventSource.ofList, EventSource.batch, EventSource.advance] at h

example
    : (ExecutionResult.incremental initial responseStream).Observes
        (.incremental initial [(responseStream.next [events] allowed).1]) true :=
  ⟨rfl, _, .cons responseStream [events] allowed (.nil _), fun _ => finished⟩

/-! Invalid roots still take the inherited ordinary counted-error branch. -/

#guard
  match executeQuery unavailable schema resolvers [] { selectionSet := [field "a"] }
          (.scalar "invalid") with
  | .single response => same response { data := .null, errors := 1 }
  | _ => false

/-- Ordinary queries have outcomes even when their unused source admits nothing. -/
example
    : Correctness.queryOutcome schema resolvers [] { selectionSet := [] } 5
        (.object "Query" 0) (.single { data := .object [] }) := by
  refine ⟨unavailable, ?_, ?_⟩
  all_goals
    simp [Execution.WorkScheduler.Conforms, executeQueryWithFuel, executeRootSelectionSet,
      executeRootSelectionSetCore, executeExecutionPlan, executeCollectedFields,
      collectExecutionGroups, collectFields, buildExecutionPlan, getNewDeferMap,
      Completion.pure, StateT.run, ExecutionResult.Observes,
      show rootSourceAppliesBool schema { selectionSet := [] }
        (.object "Query" 0) = true from rfl]
  · exact fun nonempty => False.elim (nonempty rfl)
  · rfl

example
    : Correctness.queryOutcome schema resolvers [] { selectionSet := [field "a"] } 5
        (.scalar "invalid") (.single { data := .null, errors := 1 }) := by
  refine ⟨unavailable, ?_, rfl⟩
  intro applies
  change false = true at applies
  cases applies

/-! Reconstruct the actual observed mapper output, without a candidate enumerator. -/

#guard
  let result :=
    ExecutionObservation.incremental initial [(responseStream.next [events] allowed).1]
  result.deliveryComplete
  && (mergeExecutionObservation result).any
      (fun response => same response { data := .object [("a", .scalar "a")] })

end GraphQL.IncrementalDelivery.Tests.Sources
