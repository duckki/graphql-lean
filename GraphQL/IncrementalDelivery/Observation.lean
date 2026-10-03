import GraphQL.IncrementalDelivery.WorkQueueSemantics

/-! Shared finite execution observations and query-local queue conformance.
Both correctness statements and the reference implementation use these definitions;
this module does not depend on response-correctness properties or implementation details.
-/

namespace GraphQL.IncrementalDelivery
open GraphQL.IncrementalDelivery.Execution

-----------------------------------------------------------------------------------------
-- Query completion and work-queue conformance
-----------------------------------------------------------------------------------------

/-- Prepared pure root completion, shared by query-observation and implementation statements.
This model-only helper applies variable defaults and starts work-ref allocation at zero;
it neither checks root applicability nor constructs a queue or response stream.
-/
def queryCompletion (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (operation : Operation) (fuel : Nat)
    (source : ResolverValue ObjectRef)
    : Execution.Completion (List (Name × Execution.ResponseValue)) :=
  let coercedVariables := Execution.coerceVariableValues operation variables
  ((Execution.executeRootSelectionSetCore schema resolvers coercedVariables fuel
      (operation.rootType schema) source operation.selectionSet).run
    0).1

/-- The supplied `createWorkQueue` constructs a conforming queue for this query's work.
Work is derived from execution; unrelated work imposes no law. Invalid roots and ordinary
responses do not use a queue. Correctness requires this separately from observing output.
-/
def queryWorkQueueConforms (createWorkQueue : Execution.Work → Execution.WorkQueue)
    (schema : Schema) (resolvers : Resolvers ObjectRef) (variables : VariableValues)
    (operation : Operation) (fuel : Nat) (source : ResolverValue ObjectRef)
    : Prop :=
  let work := (queryCompletion schema resolvers variables operation fuel source).work
  Execution.rootSourceAppliesBool schema operation source = true
  → work.size ≠ 0
  → (createWorkQueue work).Conforms work

namespace Execution

-----------------------------------------------------------------------------------------
-- Finite response observations
-----------------------------------------------------------------------------------------

/-- An observation supplies one input to this stage. For a batched stream, that input is
itself a nonempty available group. Admission belongs to the upstream source.
-/
def ResponseEventStream.Accepts (stream : ResponseEventStream) (input : stream.Input)
    : Prop :=
  stream.source.Allows [input]

/-- Deterministic state update after an admissible observation. This does not choose what
becomes available next; several inputs may satisfy Accepts at the same state.
-/
def ResponseEventStream.next (stream : ResponseEventStream) (input : stream.Input)
    (_allowed : stream.Accepts input)
    : IncrementalStreamUpdateResult × ResponseEventStream :=
  let result := (stream.mapEvent input).run stream.ids
  (result.1, { stream with source := stream.source.advance [input], ids := result.2 })

/-- Single-threaded observation: accept an available batch, update the partial source
history and mapper IDs, then repeat. Stopping observation does not assert termination.
-/
inductive ResponseEventStream.Observes
    : ResponseEventStream → List IncrementalStreamUpdateResult → ResponseEventStream
      → Prop where
  | nil (stream) : Observes stream [] stream
  | cons (stream batches) (allowed : stream.Accepts batches)
    {updates final}
    (rest : Observes (stream.next batches allowed).2 updates final)
    : Observes stream ((stream.next batches allowed).1 :: updates) final

/-- A finite observation of query execution. Unlike `ExecutionResult`, which retains a
resumable response-event stream, this type materializes only the updates observed so far.
-/
inductive ExecutionObservation where
  | single (response : Response)
  | incremental (initial : InitialIncrementalStreamResult)
    (subsequent : List IncrementalStreamUpdateResult)
deriving Repr

/-- complete=false includes stalled/interrupted observations; complete=true additionally
requires source termination, independently of response lifecycle or merge predicates.
-/
def ExecutionResult.Observes (execution : ExecutionResult) (result : ExecutionObservation)
    (complete : Bool := false)
    : Prop :=
  match execution, result with
  | .single response, .single observed => response = observed
  | .incremental initial stream, .incremental observed updates =>
      initial = observed
      ∧ ∃ final,
          stream.Observes updates final ∧ (complete = true → final.source.IsFinished)
  | _, _ => False

end Execution

-----------------------------------------------------------------------------------------
-- Query observations
-----------------------------------------------------------------------------------------

/-- A finite observation of the public query entry point with an explicit `createWorkQueue`.
This describes actual output, not queue conformance. Correctness requires the separate
`queryWorkQueueConforms` premise; observation alone allows arbitrary queue behavior.
-/
def queryObservation (createWorkQueue : Execution.Work → Execution.WorkQueue)
    (schema : Schema) (resolvers : Resolvers ObjectRef) (variables : VariableValues)
    (operation : Operation) (fuel : Nat)
    (source : ResolverValue ObjectRef) (result : ExecutionObservation)
    (complete : Bool := false)
    : Prop :=
  (Execution.executeQueryWithFuel createWorkQueue schema resolvers variables operation
    fuel source).Observes
    result complete

/-- Complete queryObservation, additionally requiring termination. -/
def queryOutcome (createWorkQueue : Execution.Work → Execution.WorkQueue)
    (schema : Schema) (resolvers : Resolvers ObjectRef) (variables : VariableValues)
    (operation : Operation) (fuel : Nat)
    (source : ResolverValue ObjectRef) (result : ExecutionObservation)
    : Prop :=
  queryObservation createWorkQueue schema resolvers variables operation fuel source result
    true

end GraphQL.IncrementalDelivery
