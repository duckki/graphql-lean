import Proofs.GraphQL.IncrementalDelivery.Correctness.QueryObservation
import Proofs.GraphQL.IncrementalDelivery.Correctness.SourceRealization

/-! Independent work-history witnesses can be realized by an opaque conforming source. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution

/-- Response replay is observable through the supplied conforming queue constructor itself.
Witness: actual source replay and the root's existing nonempty-work packaging equation.
-/
theorem executionFromWork_observes_replay (createWorkQueue : Work → WorkQueue)
    (response : Response) (work : Work) (groups : List (List (List WorkQueueEvent)))
    (complete : Bool) (nonempty : work.size ≠ 0)
    (conforms : (createWorkQueue work).Conforms work)
    (nonemptyGroups : ∀ group ∈ groups, group ≠ [])
    (admitted : (createWorkQueue work).workEventStream.admissible groups.flatten)
    (finished
      : complete = true → (createWorkQueue work).workEventStream.finished groups.flatten)
    : (executionFromWork createWorkQueue response work).Observes
        (replayResponse response (createWorkQueue work).initialGroups
          (createWorkQueue work).initialStreams groups) complete := by
  cases allocated
        : (getPendingEntry (m := StateM IDState)
            (createWorkQueue work).initialGroups (createWorkQueue work).initialStreams
            ensureID).run
            {} with
  | mk pending ids =>
      have replay := (createWorkQueue work).observes_inputs work ids groups conforms
        nonemptyGroups admitted
      simp only [executionFromWork, nonempty, beq_iff_eq, ↓reduceIte,
        yieldIncrementalResults, initializeIncrementalResponse, replayResponse, allocated]
      exact ⟨rfl, _, replay.1, fun done => replay.2.mpr (finished done)⟩

/-- Every independent work observation is an actual observation for a conforming
queue constructor. Witness: the maximal source with the supplied initialization and batching.
This realizes a given history; it does not assert that a terminal history exists.
-/
theorem WorkObservation.realizes {response work complete result}
    (observed : WorkObservation response work complete result)
    : ∃ scheduler : (Execution.Work → Execution.WorkQueue),
        (work.size ≠ 0 → (scheduler work).Conforms work)
        ∧ (executionFromWork scheduler response work).Observes result complete := by
  cases observed with
  | single empty =>
      let scheduler := fun work => WorkQueueSemantics.specificationSource work [] []
      refine ⟨scheduler, fun nonempty => False.elim (nonempty empty), ?_⟩
      rw [executionFromWork_silent scheduler response work empty]
      rfl
  | incremental initialGroups initialStreams groups nonempty batches admitted finished =>
      let scheduler := fun work =>
        WorkQueueSemantics.specificationSource work initialGroups initialStreams
      have initialized := WorkQueueSemantics.ValidHistory.initializes admitted
      refine ⟨scheduler,
        (fun _ => WorkQueueSemantics.specificationSource_conforms initialized), ?_⟩
      cases allocated
            : (getPendingEntry (m := StateM IDState)
                initialGroups initialStreams ensureID).run
                {} with
      | mk pending ids =>
          have realized := WorkQueueSemantics.specificationSource_observes ids groups batches admitted
          simp only [executionFromWork, nonempty, beq_iff_eq, ↓reduceIte,
            yieldIncrementalResults, initializeIncrementalResponse, scheduler,
            WorkQueueSemantics.specificationSource, replayResponse, allocated]
          exact ⟨rfl, _, realized.1, fun done => realized.2.mpr (finished done)⟩

/-- Packaging observations and independent work witnesses coincide. Witness: source
accounting in one direction and the maximal conforming source in the other.
-/
theorem workObservation_iff_realizable (response work complete result)
    : WorkObservation response work complete result
      ↔ ∃ scheduler : (Execution.Work → Execution.WorkQueue),
          (work.size ≠ 0 → (scheduler work).Conforms work)
          ∧ (executionFromWork scheduler response work).Observes result complete :=
  ⟨
    WorkObservation.realizes,
    fun ⟨scheduler, conforms, observed⟩ =>
      executionFromWork_observes_workHistory scheduler response work conforms observed
  ⟩

/-- Existence of a conforming queue constructor with the given query observation is exactly an
independent history witness for prepared root work, or the inherited invalid-root response.
Witness: the packaging equivalence; conformance is separate from the observation itself.
-/
theorem queryObservation_iff_workHistory {schema : Schema}
    {resolvers : Resolvers ObjectRef} {variables : VariableValues} {operation : Operation}
    {fuel : Nat} {source : ResolverValue ObjectRef} {result : ExecutionObservation}
    {complete : Bool}
    : (∃ createWorkQueue,
        queryWorkQueueConforms createWorkQueue schema resolvers variables operation fuel
          source
        ∧ queryObservation createWorkQueue schema resolvers variables operation fuel
            source result complete)
      ↔ if rootSourceAppliesBool schema operation source then
          let completed :=
            ((executeRootSelectionSetCore schema resolvers
                (coerceVariableValues operation variables) fuel
                (operation.rootType schema) source operation.selectionSet).run
              0).1
          WorkObservation (selectionSetResultToResponse completed.result) completed.work
            complete result
        else
          result = .single { data := .null, errors := 1 } := by
  constructor
  · rintro ⟨createWorkQueue, conforms, observed⟩
    exact queryObservation_workHistory conforms observed
  · intro observed
    split at observed
    · rename_i applies
      obtain ⟨scheduler, conforms, run⟩ := observed.realizes
      refine ⟨scheduler, fun _ => conforms, ?_⟩
      simpa only [queryObservation, executeQueryWithFuel, applies, ↓reduceIte,
        executeRootSelectionSet_fromWork] using run
    · rename_i invalid
      subst result
      refine ⟨(fun work => WorkQueueSemantics.specificationSource work [] []),
        fun applies => False.elim (invalid applies), ?_⟩
      simp [queryObservation, executeQueryWithFuel, invalid, ExecutionResult.Observes]

/-- Complete observation exists exactly when work is empty or has an admitted terminal
history. Witness: observation soundness, or singleton response grouping of the supplied
run. MixedExistence supplies the terminal history for coherent generated work.
-/
theorem completeObservation_exists_iff (response : Response) (work : Work)
    : (∃ scheduler : (Execution.Work → Execution.WorkQueue),
        ∃ result : ExecutionObservation,
          (work.size ≠ 0 → (scheduler work).Conforms work)
          ∧ (executionFromWork scheduler response work).Observes result true)
      ↔ work.size = 0 ∨ ∃ history, WorkQueueSemantics.AdmissibleRun work history := by
  constructor
  · rintro ⟨scheduler, result, conforms, observed⟩
    have witness := executionFromWork_observes_workHistory scheduler response work
      conforms observed
    cases witness with
    | single empty => exact Or.inl empty
    | incremental groups streams batches _ _ _ finished =>
        exact Or.inr ⟨_, finished rfl⟩
  · intro possible
    by_cases empty : work.size = 0
    · obtain ⟨scheduler, conforms, observed⟩ :=
        (WorkObservation.single (response := response) (complete := true) empty).realizes
      exact ⟨scheduler, .single response, conforms, observed⟩
    · obtain ⟨history, run⟩ := possible.resolve_left empty
      let groups := history.batches.map (fun batch => [batch])
      have flattened : groups.flatten = history.batches := by
        dsimp [groups]
        induction history.batches with
        | nil => rfl
        | cons batch rest ih => simpa using congrArg (List.cons batch) ih
      have nonempty : ∀ group ∈ groups, group ≠ [] := by
        intro group member
        obtain ⟨batch, _, rfl⟩ := List.mem_map.mp member
        simp
      have terminal : WorkQueueSemantics.AdmissibleRun work
          ⟨history.initialGroups, history.initialStreams, groups.flatten⟩ := by
        simpa only [flattened] using run
      have witness := WorkObservation.incremental (response := response)
        (complete := true) history.initialGroups history.initialStreams groups empty
        nonempty (Or.inr terminal) (fun _ => terminal)
      obtain ⟨scheduler, conforms, observed⟩ := witness.realizes
      exact ⟨scheduler, _, conforms, observed⟩

end GraphQL.IncrementalDelivery.Correctness
