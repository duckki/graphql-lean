import Proofs.GraphQL.IncrementalDelivery.Correctness.QueryRealization
import Proofs.GraphQL.IncrementalDelivery.Correctness.Initialization
import Proofs.GraphQL.IncrementalDelivery.WorkScheduler.CompletionExistence

/-! Query-prefix existence without assuming scheduler conformance or an admitted history.
This establishes initialization independently of the complete-run construction in
QueryOutcomeExistence.
-/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution

-----------------------------------------------------------------------------------------
-- A factory exists before any history is assumed
-----------------------------------------------------------------------------------------

/-- Choose valid initial notices when they exist, retaining every later history allowed
by that choice. This proof-only factory chooses no task order or future response stream.
The fallback applies to arbitrary malformed raw work, not nonempty generated work.
-/
noncomputable def initializedScheduler : Execution.WorkScheduler :=
  open Classical in
  WorkScheduler.specificationScheduler
    (fun work =>
      if possible
          : ∃ notices : List DeliveryNode × List DeliveryNode,
              WorkScheduler.Initializes work notices.1 notices.2 then
        Classical.choose possible
      else
        ([], []))

/-- The proof-only factory conforms whenever initialization is possible. Witness: the
chosen notice witness and maximal-source conformance; no future run is selected.
-/
theorem initializedScheduler_conforms {work}
    (possible
      : work.size ≠ 0 → ∃ groups streams, WorkScheduler.Initializes work groups streams)
    : initializedScheduler.Conforms work := by
  apply WorkScheduler.specificationScheduler_conforms
  intro nonempty
  obtain ⟨groups, streams, initialized⟩ := possible nonempty
  have existsNotices : ∃ notices : List DeliveryNode × List DeliveryNode,
      WorkScheduler.Initializes work notices.1 notices.2 :=
    ⟨(groups, streams), initialized⟩
  simpa only [dite_eq_left existsNotices] using Classical.choose_spec existsNotices

/-- One factory conforms to every prepared root work. Witness: unconditional generated
work initialization, with no law needed in the empty-work branch.
-/
theorem executeRoot_initializedScheduler_conforms (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (parentType : Name) (source : ResolverValue ObjectRef) (selections : List Selection)
    : initializedScheduler.Conforms
        ((executeRootSelectionSetCore schema resolvers variables fuel parentType source
            selections).run
          0).1.work :=
  initializedScheduler_conforms
    (WorkScheduler.executeRoot_initialization_exists schema resolvers variables fuel
      parentType source selections)

-----------------------------------------------------------------------------------------
-- Observable query initialization
-----------------------------------------------------------------------------------------

/-- Generated root work has an ordinary or initialized incremental observation. Witness:
empty-work packaging, or the independently proved initial frontier with no updates.
-/
theorem executeRoot_workObservation_exists (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (parentType : Name) (source : ResolverValue ObjectRef) (selections : List Selection)
    : let completed :=
        ((executeRootSelectionSetCore schema resolvers variables fuel
            parentType source selections).run
          0).1
      ∃ result,
        WorkObservation (selectionSetResultToResponse completed.result)
          completed.work false result := by
  intro completed
  by_cases empty : completed.work.size = 0
  · exact ⟨_, .single empty⟩
  · obtain ⟨groups, streams, initialized⟩ :=
      WorkScheduler.executeRoot_initialization_exists schema resolvers variables fuel
        parentType source selections empty
    exact ⟨_, .incremental groups streams [] empty (by simp)
      (Or.inl initialized.emptyHistory) (by simp)⟩

/-- Every query has a conforming observable prefix, including errors and exhausted fuel.
Witness: generated initialization plus realization, or the ordinary invalid-root branch.
This does not assert that a complete outcome exists.
-/
theorem queryObservation_exists (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (operation : Operation) (fuel : Nat)
    (source : ResolverValue ObjectRef)
    : ∃ result,
        queryObservation schema resolvers variables operation fuel source result
          false := by
  by_cases applies : rootSourceAppliesBool schema operation source = true
  · obtain ⟨result, observed⟩ := executeRoot_workObservation_exists schema resolvers
      (coerceVariableValues operation variables) fuel (operation.rootType schema) source
      operation.selectionSet
    refine ⟨result, queryObservation_iff_workHistory.mpr ?_⟩
    simpa only [applies, ↓reduceIte] using observed
  · refine ⟨.single { data := .null, errors := 1 },
      queryObservation_iff_workHistory.mpr ?_⟩
    simp [applies]

-----------------------------------------------------------------------------------------
-- Complete raw-work observations are equivalent to task-accounted histories
-----------------------------------------------------------------------------------------

/-- A complete observation exists exactly when work is empty or an explained history
accounts for all tasks. Witness: terminal-history realization and constructive completion
of every remaining open node. Closing IDs is a conclusion, not a premise on this history.
-/
theorem completeObservation_exists_iff_accounted_history (response : Response)
    (work : Work)
    : (∃ scheduler : Execution.WorkScheduler,
        ∃ result : QueryResult,
          scheduler.Conforms work
          ∧ (executionFromWork scheduler response work).Observes result true)
      ↔ work.size = 0
        ∨ ∃ groups streams events matching failures,
            WorkScheduler.Explains work groups streams events matching failures
            ∧ ∀ occurrence owners producer payload,
                WorkScheduler.TaskAt work occurrence owners producer payload
                → WorkScheduler.Accounted work matching events
                    (WorkScheduler.failedBefore failures events.length) occurrence := by
  rw [completeObservation_exists_iff,
    WorkScheduler.admissibleRun_exists_iff_accounted_history]

end GraphQL.IncrementalDelivery.Correctness
