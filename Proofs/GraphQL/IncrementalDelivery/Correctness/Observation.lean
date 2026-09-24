import Proofs.GraphQL.IncrementalDelivery.Correctness.RootExecution
import Init.Data.List.Sublist

/-! Finite observations of partial sources. These witnesses compose observations,
forget termination, and preserve initial data/errors without fixing a future schedule.
-/

namespace GraphQL.IncrementalDelivery.Execution

/-- Appending two observed input lists is one history update, by list associativity. -/
theorem EventSource.advance_append (source : EventSource α) (left right : List α)
    : (source.advance left).advance right = source.advance (left ++ right) := by
  simp [advance, List.append_assoc]

/-- Accepting a longer group accepts all its prefixes, by transitivity of list prefixes.
-/
theorem EventSource.Allows.prefix {source : EventSource α} {values prior : List α}
    (allowed : source.Allows values) (h : prior.IsPrefix values)
    : source.Allows prior :=
  fun initial before => allowed initial (before.trans h)

/-- Admission composes exactly across a history update; witness: split a prefix at the
boundary.
-/
theorem EventSource.allows_append_iff (source : EventSource α) (left right : List α)
    : source.Allows (left ++ right)
      ↔ source.Allows left ∧ (source.advance left).Allows right := by
  constructor
  · intro allowed
    refine ⟨allowed.prefix (List.prefix_append left right), ?_⟩
    intro initial before
    have h := allowed (left ++ initial) ((List.prefix_append_right_inj left).mpr before)
    simpa [advance, List.append_assoc] using h
  · rintro ⟨first, rest⟩ initial before
    rcases List.prefix_or_prefix_of_prefix before (List.prefix_append left right) with h | h
    · exact first initial h
    · obtain ⟨suffix, rfl⟩ := h
      have tail := (List.prefix_append_right_inj left).mp before
      simpa [advance, List.append_assoc] using rest suffix tail

/-- Sources with the same history and extensional languages are equal, by funext/propext.
-/
theorem EventSource.extensionality (left right : EventSource α)
    (history : left.history = right.history)
    (admissible : ∀ values, left.admissible values ↔ right.admissible values)
    (finished : ∀ values, left.finished values ↔ right.finished values)
    : left = right := by
  have ha := funext (fun values => propext (admissible values))
  have hf := funext (fun values => propext (finished values))
  cases left
  cases right
  simp_all

/-- A newly installed batcher accepts exactly nonempty admitted upstream groups. Witness:
the singleton group's full prefix in one direction, its two prefixes in the other.
-/
theorem ResponseEventStream.batch_accepts_iff (stream : ResponseEventStream)
    (available : List stream.Input)
    : (batchIncrementalResults stream).Accepts available
      ↔ available ≠ [] ∧ stream.source.Allows available := by
  change (∀ initial : List (List stream.Input), initial.IsPrefix [available] →
    (∀ group ∈ initial, group ≠ []) ∧ stream.source.Allows initial.flatten) ↔ _
  constructor
  · intro allowed
    simpa using allowed [available] (List.prefix_refl _)
  · rintro ⟨nonempty, admitted⟩ initial before
    cases initial with
    | nil =>
        refine ⟨by simp, ?_⟩
        exact admitted.prefix List.nil_prefix
    | cons first rest =>
        obtain ⟨rfl, tail⟩ := List.cons_prefix_cons.mp before
        have empty := List.prefix_nil.mp tail
        subst rest
        simpa using And.intro nonempty admitted

/-- Observations concatenate without choosing more inputs; witness: induction on the first
run.
-/
theorem ResponseEventStream.Observes.append {start middle final : ResponseEventStream}
    {left right : List IncrementalStreamUpdateResult} (first : start.Observes left middle)
    (rest : middle.Observes right final)
    : start.Observes (left ++ right) final := by
  induction first with
  | nil => exact rest
  | cons stream input allowed tail ih => exact .cons stream input allowed (ih rest)

/-- Every observed prefix has an intermediate stream witness, obtained by splitting the
run.
-/
theorem ResponseEventStream.Observes.split
    {start final : ResponseEventStream} (left right : List IncrementalStreamUpdateResult)
    (observed : start.Observes (left ++ right) final)
    : ∃ middle, start.Observes left middle ∧ middle.Observes right final := by
  induction left generalizing start with
  | nil => exact ⟨start, .nil _, observed⟩
  | cons update rest ih =>
      cases observed with
      | cons stream input allowed tail =>
          obtain ⟨middle, first, last⟩ := ih tail
          exact ⟨middle, .cons _ input allowed first, last⟩

/-- Complete observations are finite observations too; witness: drop only the termination
proof.
-/
theorem ExecutionResult.Observes.forgetComplete
    {execution : ExecutionResult} {result : ExecutionObservation} {complete : Bool}
    (observed : execution.Observes result complete)
    : execution.Observes result := by
  cases execution <;> cases result <;> simp_all [Observes]
  obtain ⟨final, run, _⟩ := observed.2
  exact ⟨final, run⟩

end GraphQL.IncrementalDelivery.Execution

namespace GraphQL.IncrementalDelivery.Correctness

open GraphQL.IncrementalDelivery.Execution

/-- Data/errors from a finite response observation, excluding notices and later payloads.
-/
def observedInitialResponse : ExecutionObservation → Response
  | .single response => response
  | .incremental initial _ => initial.toResponse

/-- Observations keep the execution's initial envelope; witness: the equality in Observes.
-/
theorem observes_initialResponse {execution : ExecutionResult}
    {result : ExecutionObservation} {complete : Bool}
    (observed : execution.Observes result complete)
    : initialResponse execution = observedInitialResponse result := by
  cases execution <;> cases result <;>
    simp_all [ExecutionResult.Observes, initialResponse, observedInitialResponse]

/-- Every complete query outcome is a prefix observation, with the same conforming
factory.
-/
theorem queryOutcome_observation {schema : Schema} {resolvers : Resolvers ObjectRef}
    {variables : VariableValues} {operation : Operation} {fuel : Nat}
    {source : ResolverValue ObjectRef} {result : ExecutionObservation}
    (h : queryOutcome schema resolvers variables operation fuel source result)
    : queryObservation schema resolvers variables operation fuel source result := by
  obtain ⟨scheduler, conforms, observed⟩ := h
  exact ⟨scheduler, conforms, observed.forgetComplete⟩

/-- Admitted observations agree on initial data/errors across factories and stopping
points. Witness: observed envelopes equal their executions', whose pure initial responses
agree.
-/
theorem queryObservation_initialResponse_independent
    {schema : Schema} {resolvers : Resolvers ObjectRef} {variables : VariableValues}
    {operation : Operation} {fuel : Nat} {source : ResolverValue ObjectRef}
    {first second : ExecutionObservation} {firstComplete secondComplete : Bool}
    (left
      : queryObservation schema resolvers variables operation fuel source first
          firstComplete)
    (right
      : queryObservation schema resolvers variables operation fuel source second
          secondComplete)
    : observedInitialResponse first = observedInitialResponse second := by
  obtain ⟨leftScheduler, _, leftObserved⟩ := left
  obtain ⟨rightScheduler, _, rightObserved⟩ := right
  exact (observes_initialResponse leftObserved).symm.trans
    ((executeQueryWithFuel_initialResponse_independent leftScheduler rightScheduler
      schema resolvers variables operation fuel source).trans
      (observes_initialResponse rightObserved))

end GraphQL.IncrementalDelivery.Correctness
