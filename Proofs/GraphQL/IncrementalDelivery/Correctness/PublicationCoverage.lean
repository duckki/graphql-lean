import Proofs.GraphQL.IncrementalDelivery.Correctness.SuccessfulWork
import Proofs.GraphQL.IncrementalDelivery.Correctness.ErrorCounts
import Proofs.GraphQL.IncrementalDelivery.WorkScheduler.Publication

/-! Exact task coverage and payload error-freedom in complete successful observations. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open WorkScheduler

/-- The counted errors in a task's outcome, including successful null-catching results. -/
def payloadErrors : Payload → Nat
  | .object _ (.error errors)
  | .object _ (.ok (_, errors))
  | .item _ (.error errors)
  | .item _ (.ok (_, errors)) => errors

/-- Compatible value coalescing adds both error counts, by its two constructor cases. -/
theorem combineValues_errors {left right combined}
    (h : combineValues left right = some combined)
    : workEventErrors combined = workEventErrors left + workEventErrors right := by
  cases left <;> cases right <;> simp only [combineValues] at h <;> try contradiction
  all_goals split at h <;> cases h <;> simp [workEventErrors]

/-- Value grouping preserves all error counts, by induction on grouping. -/
theorem valueGrouping_errors {events grouped} (h : ValueGrouping events grouped)
    : (grouped.map workEventErrors).sum = (events.map workEventErrors).sum := by
  induction h with
  | nil => rfl
  | separate head _ ih => simpa using congrArg (workEventErrors head + ·) ih
  | combine head _ compatible ih =>
      simpa [combineValues_errors compatible, Nat.add_assoc]
        using congrArg (workEventErrors head + ·) ih

/-- Work batching preserves all errors, by concatenation and value-group preservation. -/
theorem workBatching_errors {events batches} (h : WorkBatching events batches)
    : (batches.flatten.map workEventErrors).sum = (events.map workEventErrors).sum := by
  induction h with
  | nil => rfl
  | cons _ grouped _ ih =>
      simp only [List.flatten_cons, List.map_append, List.sum_append,
        valueGrouping_errors grouped, ih]

/-- A value atom carries exactly its matched task's error count; witness: task uniqueness
identifies the payload from the event's provenance premise.
-/
theorem event_publication_errors {work initial matching before failed event}
    (allowed : EventAllowed work initial matching before failed event)
    (value : IsValue event) {owners producer payload}
    (known : TaskAt work (matching before.length) owners producer payload)
    : payloadErrors payload = workEventErrors event := by
  cases event <;> try contradiction
  case groupValues node values =>
    obtain ⟨_, _, _, _, _, rfl, task, _⟩ := allowed
    rw [(known.unique task).2.2]
    simp [payloadErrors, workEventErrors]
  case streamValues node values groups streams =>
    obtain ⟨_, _, _, _, rfl, task, _⟩ := allowed
    rw [(known.unique task).2.2]
    simp [payloadErrors, workEventErrors]

/-- Any published task's errors are bounded by the event-history sum; witness: its
unique payload count is one nonnegative summand.
-/
theorem published_errors_le {work groups streams events matching failures}
    (explained : Explains work groups streams events matching failures)
    {occurrence owners producer payload}
    (known : TaskAt work occurrence owners producer payload)
    (published : Published matching events occurrence)
    : payloadErrors payload ≤ (events.map workEventErrors).sum := by
  obtain ⟨index, event, selected, value, same⟩ := published
  have bound := (List.getElem?_eq_some_iff.mp selected).choose
  have task : TaskAt work (matching (events.take index).length) owners producer payload := by
    simpa [List.length_take, Nat.min_eq_left (Nat.le_of_lt bound), same] using known
  rw [event_publication_errors (explained.2.2 index event selected) value task]
  exact le_sum (List.mem_map.mpr
    ⟨event, List.mem_iff_getElem?.mpr ⟨index, selected⟩, rfl⟩)

/-- Error-free terminal replay publishes each real task exactly once, with zero payload
errors. Witness: failure-free coverage, one-shot matching, and conserved error totals.
Distinct equal-valued tasks remain distinct occurrences; overlapping owners do not
multiply publication.
-/
theorem replayResponse_task_coverage {response : Response} {work : Work}
    {groups streams : List DeliveryNode} {batches : List (List (List WorkEvent))}
    (positive : ExecutionErrors.WorkPositive work)
    (run : AdmissibleRun work ⟨groups, streams, batches.flatten⟩)
    (zero : (replayResponse response groups streams batches).totalErrors = 0)
    : ∃ events matching,
        Explains work groups streams events matching []
        ∧ WorkBatching (events ++ [.workQueueTermination]) batches.flatten
        ∧ ∀ occurrence owners producer payload,
            TaskAt work occurrence owners producer payload
            → payload.failure = none
              ∧ payloadErrors payload = 0
              ∧ ∃ index,
                  (∃ event,
                    events[index]? = some event
                    ∧ IsValue event
                    ∧ matching index = occurrence)
                  ∧ ∀ other event,
                      events[other]? = some event
                      → IsValue event
                      → matching other = occurrence
                      → other = index := by
  obtain ⟨events, matching, explained, _, batched, success⟩ :=
    replayResponse_successful_history positive run zero
  have count := workBatching_errors batched
  rw [List.map_append, List.sum_append] at count
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    workEventErrors, Nat.add_zero] at count
  rw [replayResponse_errors] at zero
  have allZero : (events.map workEventErrors).sum = 0 := by
    omega
  refine ⟨events, matching, explained, batched, ?_⟩
  intro occurrence owners producer payload known
  obtain ⟨published, succeeds⟩ := success occurrence owners producer payload known
  have bound := published_errors_le explained known published
  exact ⟨succeeds, by omega, explained.published_once published⟩

/-- The initial envelope's errors remain part of every observation's total, by the
ordinary branch or the exact replay sum. Prefix observations need not terminate.
-/
theorem WorkObservation.initial_errors_le {response : Response} {work : Work}
    {complete : Bool} {result : ExecutionObservation}
    (observed : WorkObservation response work complete result)
    : response.errors ≤ result.totalErrors := by
  cases observed with
  | single _ => exact Nat.le_refl _
  | incremental groups streams batches _ _ _ _ =>
      rw [replayResponse_errors]
      omega

/-- Every retained task in zero-error complete work has zero payload errors, including
successful null-catching results; witness: the complete publication-coverage certificate.
-/
theorem WorkObservation.payload_errors_zero {response : Response} {work : Work}
    {result : ExecutionObservation} (observed : WorkObservation response work true result)
    (positive : ExecutionErrors.WorkPositive work) (zero : result.totalErrors = 0)
    {occurrence owners producer payload}
    (known : TaskAt work occurrence owners producer payload)
    : payloadErrors payload = 0 := by
  cases observed with
  | single empty => exact False.elim (no_tasks_of_size_zero empty known)
  | incremental groups streams batches _ _ _ finished =>
      obtain ⟨events, matching, _, _, coverage⟩ :=
        replayResponse_task_coverage positive (finished rfl) zero
      exact (coverage occurrence owners producer payload known).2.1

/-- A zero-error complete query has zero errors in every retained task. Witness:
actual-work reduction, execution positivity, and exact publication coverage.
-/
theorem queryOutcome_payload_errors_zero {schema : Schema}
    {resolvers : Resolvers ObjectRef} {variables : VariableValues} {operation : Operation}
    {fuel : Nat} {source : ResolverValue ObjectRef} {result : ExecutionObservation}
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
    : payloadErrors payload = 0 := by
  have witnessed := queryObservation_workHistory observed
  simp only [applies, ↓reduceIte] at witnessed
  exact witnessed.payload_errors_zero
    (ExecutionErrors.executeRootSelectionSetCore_positive schema resolvers _ fuel
      (operation.rootType schema) source operation.selectionSet 0).2 zero known

end GraphQL.IncrementalDelivery.Correctness
