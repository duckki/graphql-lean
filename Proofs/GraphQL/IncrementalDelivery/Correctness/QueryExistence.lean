import Proofs.GraphQL.IncrementalDelivery.Correctness.QueryRealization
import Proofs.GraphQL.IncrementalDelivery.Correctness.Initialization
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.CompletionExistence

/-! Query-prefix existence without assuming scheduler conformance or an admitted history.
This establishes initialization independently of the complete-run construction in
QueryOutcomeExistence.
-/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution

-----------------------------------------------------------------------------------------
-- A queue constructor exists before any history is assumed
-----------------------------------------------------------------------------------------

/-- Choose valid initial notices when they exist, retaining every later history allowed
by that choice. This proof-only queue constructor chooses no task order or future response stream.
The fallback applies to arbitrary malformed raw work, not nonempty generated work.
-/
noncomputable def initializedWorkQueue : (Execution.Work → Execution.WorkQueue) :=
  open Classical in
  fun work =>
    let notices :=
      if possible
          : ∃ notices : List DeliveryNode × List DeliveryNode,
              WorkQueueSemantics.Initializes work notices.1 notices.2 then
        Classical.choose possible
      else
        ([], [])
    WorkQueueSemantics.specificationSource work notices.1 notices.2

/-- The proof-only queue constructor conforms whenever initialization is possible. Witness: the
chosen notice witness and maximal-source conformance; no future run is selected.
-/
theorem initializedWorkQueue_conforms {work}
    (possible
      : work.size ≠ 0
        → ∃ groups streams, WorkQueueSemantics.Initializes work groups streams)
    : (work.size ≠ 0 → (initializedWorkQueue work).Conforms work) := by
  intro nonempty
  apply WorkQueueSemantics.specificationSource_conforms
  obtain ⟨groups, streams, initialized⟩ := possible nonempty
  have existsNotices : ∃ notices : List DeliveryNode × List DeliveryNode,
      WorkQueueSemantics.Initializes work notices.1 notices.2 :=
    ⟨(groups, streams), initialized⟩
  simpa only [dite_eq_left existsNotices] using Classical.choose_spec existsNotices

/-- One queue constructor conforms to every prepared root work. Witness: unconditional generated
work initialization, with no law needed in the empty-work branch.
-/
theorem executeRoot_initializedWorkQueue_conforms (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (parentType : Name) (source : ResolverValue ObjectRef) (selections : List Selection)
    : let work :=
        ((executeRootSelectionSetCore schema resolvers variables fuel
            parentType source selections).run
          0).1.work
      work.size ≠ 0 → (initializedWorkQueue work).Conforms work :=
  initializedWorkQueue_conforms
    (WorkQueueSemantics.executeRoot_initialization_exists schema resolvers variables fuel
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
      WorkQueueSemantics.executeRoot_initialization_exists schema resolvers variables fuel
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
    : ∃ result createWorkQueue,
        queryWorkQueueConforms createWorkQueue schema resolvers variables operation fuel
          source
        ∧ queryObservation createWorkQueue schema resolvers variables operation fuel
            source result false := by
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
of every remaining open node, retaining the failure cuts and publication matching.
Closing IDs is a conclusion, not a premise on this history.
-/
theorem completeObservation_exists_iff_accounted_history (response : Response)
    (work : Work)
    : (∃ scheduler : (Execution.Work → Execution.WorkQueue),
        ∃ result : ExecutionObservation,
          (work.size ≠ 0 → (scheduler work).Conforms work)
          ∧ (executionFromWork scheduler response work).Observes result true)
      ↔ work.size = 0
        ∨ ∃ groups streams events matching failures,
            WorkQueueSemantics.Explains work groups streams events matching failures
            ∧ ∀ occurrence owners producer payload,
                WorkQueueSemantics.TaskAt work occurrence owners producer payload
                → WorkQueueSemantics.TaskAccounted work matching events failures
                    occurrence := by
  rw [completeObservation_exists_iff,
    WorkQueueSemantics.admissibleRun_exists_iff_accounted_history]

end GraphQL.IncrementalDelivery.Correctness
