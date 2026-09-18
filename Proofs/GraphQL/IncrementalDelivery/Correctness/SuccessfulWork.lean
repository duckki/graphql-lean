import Proofs.GraphQL.IncrementalDelivery.Correctness.TaskErrors
import Proofs.GraphQL.IncrementalDelivery.Correctness.FailureCounts

/-! Error-free complete observations retain no hidden failure or cancellation witness. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open WorkScheduler

/-- A zero-error terminal history has an explanation with no failures. Every task is
published, rather than cancelled. Witness: positive execution failures contradict the
failure-accounting bound; terminal accounting then forces publication.
-/
theorem successful_history {work history}
    (positive : ExecutionErrors.WorkPositive work) (run : AdmissibleRun work history)
    (zero : (history.batches.flatten.map failureErrors).sum = 0)
    : ∃ events matching,
        Explains work history.initialGroups history.initialStreams events matching []
        ∧ Terminal work
            ((history.initialGroups ++ history.initialStreams).map DeliveryNode.key)
            matching events []
        ∧ WorkBatching (events ++ [.workQueueTermination]) history.batches
        ∧ ∀ occurrence owners producer payload,
            TaskAt work occurrence owners producer payload
            → Published matching events occurrence ∧ payload.failure = none := by
  obtain ⟨events, matching, failures, explained, done, batching, counts⟩ :=
    run.failure_accounting
  have empty : failures = [] := by
    cases failures with
    | nil => rfl
    | cons entry rest =>
        rcases entry with ⟨cut, task⟩
        obtain ⟨owners, producer, payload, known, fails, _⟩ :=
          (explained.2.1 [] cut task rest rfl).2.2.1
        have nonzero := positive.task known fails
        have bound := counts cut task owners producer payload (by simp) known
        omega
  subst failures
  simp only [failedBefore, List.filter_nil, List.map_nil] at done
  refine ⟨events, matching, explained, done, batching, ?_⟩
  intro occurrence owners producer payload known
  rcases done.1 occurrence owners producer payload known with cancelled | published
  · exact False.elim (cancelled.nonempty rfl)
  · exact ⟨published, explained.published_succeeds known published⟩

/-- A concrete supplied response replay with zero errors has no hidden failed tasks;
witness: the actual mapper's count bound and the independent terminal history.
-/
theorem replayResponse_successful_history {response : Response} {work : Work}
    {groups streams : List DeliveryNode} {batches : List (List (List WorkEvent))}
    (positive : ExecutionErrors.WorkPositive work)
    (run : AdmissibleRun work ⟨groups, streams, batches.flatten⟩)
    (zero : (replayResponse response groups streams batches).totalErrors = 0)
    : ∃ events matching,
        Explains work groups streams events matching []
        ∧ Terminal work ((groups ++ streams).map DeliveryNode.key) matching events []
        ∧ WorkBatching (events ++ [.workQueueTermination]) batches.flatten
        ∧ ∀ occurrence owners producer payload,
            TaskAt work occurrence owners producer payload
            → Published matching events occurrence ∧ payload.failure = none := by
  apply successful_history positive run
  have bound := replayResponse_failureErrors_le response groups streams batches
  dsimp only
  omega

/-- Zero-size work has no deferred or streamed tasks; witness: navigation cannot reach
a positive-size node from a zero-size root.
-/
theorem no_tasks_of_size_zero {work : Work} (empty : work.size = 0)
    {occurrence owners producer payload}
    (known : TaskAt work occurrence owners producer payload)
    : False := by
  have locatedZero {address current producer owners}
      (located : Located work address current producer owners) : current.size = 0 := by
    have navigation := StructuralEquivalence.located_of_current located
    clear located
    induction navigation with
    | root => exact empty
    | left _ ih | right _ ih =>
        simp only [Work.size] at ih; omega
    | deferred _ ih | item _ _ ih =>
        simp only [Work.size] at ih; omega
  cases StructuralEquivalence.taskAt_of_current known with
  | deferred located =>
      have := locatedZero located.toCurrent; simp [Work.size] at this
  | item located _ =>
      have := locatedZero located.toCurrent; simp [Work.size] at this

/-- Error-free complete work observations contain only successful task outcomes.
Witness: empty work has no tasks; incremental work admits a failure-free explanation.
-/
theorem WorkObservation.tasks_succeed {response : Response} {work : Work}
    {result : QueryResult} (observed : WorkObservation response work true result)
    (positive : ExecutionErrors.WorkPositive work) (zero : result.totalErrors = 0)
    {occurrence owners producer payload}
    (known : TaskAt work occurrence owners producer payload)
    : payload.failure = none := by
  cases observed with
  | single empty => exact False.elim (no_tasks_of_size_zero empty known)
  | incremental groups streams batches _ _ _ finished =>
      obtain ⟨events, matching, _, _, _, success⟩ :=
        replayResponse_successful_history positive (finished rfl) zero
      exact (success occurrence owners producer payload known).2

/-- Zero errors at query level exclude every failed task in the actual prepared work.
Witness: query-to-work soundness, positive finite execution, and preserved failure counts.
-/
theorem queryOutcome_tasks_succeed {schema : Schema} {resolvers : Resolvers ObjectRef}
    {variables : VariableValues} {operation : Operation} {fuel : Nat}
    {source : ResolverValue ObjectRef} {result : QueryResult}
    (observed : queryOutcome schema resolvers variables operation fuel source result)
    (zero : result.totalErrors = 0)
    (applies : rootSourceAppliesBool schema operation source = true)
    {occurrence owners producer payload}
    (known
      : TaskAt
          ((executeRootSelectionSetCore schema resolvers
              (coerceVariableValues operation variables) fuel (operation.rootType schema)
              source operation.selectionSet).run
            0).1.work
          occurrence owners producer payload)
    : payload.failure = none := by
  have witnessed := queryObservation_workHistory observed
  simp only [applies, ↓reduceIte] at witnessed
  exact witnessed.tasks_succeed
    (ExecutionErrors.executeRootSelectionSetCore_positive schema resolvers _ fuel
      (operation.rootType schema) source operation.selectionSet 0).2 zero known

end GraphQL.IncrementalDelivery.Correctness
