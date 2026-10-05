import Proofs.GraphQL.IncrementalDelivery.Correctness.QueryIDUsage
import Proofs.GraphQL.IncrementalDelivery.Correctness.PatchPositions
import Proofs.GraphQL.IncrementalDelivery.Correctness.QueryCoverage

/-! Observable failure-scope decoding and the established zero-error coverage branch.
Failure scopes are resolved from wire notices, never assumed from internal cancellation.
-/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution

/-- A finite Option traversal succeeds when every supplied element has an output.
Witness: list induction threads the successful head and tail computations.
-/
private theorem option_mapM_exists {α β : Type} (values : List α) (f : α → Option β)
    (total : ∀ value ∈ values, ∃ output, f value = some output)
    : ∃ outputs, values.mapM f = some outputs := by
  induction values with
  | nil => exact ⟨[], rfl⟩
  | cons head tail ih =>
      obtain ⟨output, found⟩ := total head (by simp)
      obtain ⟨outputs, rest⟩ := ih (fun value member => total value (by simp [member]))
      exact ⟨output :: outputs, by simp [found, rest]⟩

/-- ID safety makes every failure completion resolvable using only available notices.
Witness: completion IDs belong to the live frontier, which is included in the cumulative
announcement list; update induction preserves that inclusion.
-/
theorem collectFailureScopes_exists_of_idUsageValid
    (notices : List IncrementalPendingNotice) (active : List String)
    (updates : List IncrementalStreamUpdateResult)
    (safe
      : DeliveryTrace.idUsageValid (notices.map IncrementalPendingNotice.id)
          active updates
        = true)
    (supported : active.Subset (notices.map IncrementalPendingNotice.id))
    : ∃ scopes, DeliveryTrace.collectFailureScopes notices updates = some scopes := by
  induction updates generalizing notices active with
  | nil => exact ⟨[], rfl⟩
  | cons update rest ih =>
      obtain ⟨_, _, _, completed, _, next⟩ :=
        (idUsageValid_cons_iff _ _ _ _).mp safe
      let available := notices ++ update.pending
      have supportedNow : (active ++ update.pending.map IncrementalPendingNotice.id).Subset
          (available.map IncrementalPendingNotice.id) := by
        intro id member
        simp only [available, List.map_append]
        rcases List.mem_append.mp member with old | fresh
        · exact List.mem_append_left _ (supported old)
        · exact List.mem_append_right _ fresh
      obtain ⟨scopes, decoded⟩ := option_mapM_exists
        (update.completed.filter (fun completion => completion.errors > 0))
        (fun completion => do
          let notice ← available.find? (fun notice => notice.id == completion.id)
          return notice.path) (by
          intro completion member
          have known := (List.mem_filter.mp member).1
          have announced := supportedNow (completed completion.id
            (List.mem_map.mpr ⟨completion, known, rfl⟩))
          obtain ⟨notice, found⟩ := notice_exists announced
          exact ⟨notice.path, by simp [found]⟩)
      have nextSafe : DeliveryTrace.idUsageValid
          (available.map IncrementalPendingNotice.id)
          ((active ++ update.pending.map IncrementalPendingNotice.id).filter
            (fun id => !(update.completed.map IncrementalCompletionNotice.id).contains id))
          rest = true := by
        simpa only [available, List.map_append] using next
      obtain ⟨subsequent, decodedRest⟩ := ih available _ nextSafe
        (fun _ member => supportedNow (List.mem_filter.mp member).1)
      refine ⟨scopes ++ subsequent, ?_⟩
      simp only [available] at decoded decodedRest
      simp only [DeliveryTrace.collectFailureScopes, decoded, decodedRest]
      rfl

/-- Any ID-safe observation has a successfully decoded finite failure-scope list.
Witness: ordinary responses have none; incremental responses start with their initial
notices and apply the cumulative wire-decoding theorem.
-/
theorem ExecutionObservation.failureScopes_exist {result : ExecutionObservation}
    (safe : result.idUsageValid)
    : ∃ scopes, result.collectFailureScopes = some scopes := by
  cases result with
  | single response => exact ⟨[], rfl⟩
  | incremental initial updates =>
      exact collectFailureScopes_exists_of_idUsageValid initial.pending _ updates safe.2
        (List.Subset.refl _)

/-- Conforming query observations decode failure scopes even when execution has errors.
Witness: public ID safety and the finite wire decoder; completeness is not required.
-/
theorem queryObservation_failureScopes_exist {createWorkQueue : Work → WorkQueue}
    {schema : Schema} {resolvers : Resolvers ObjectRef} {variables : VariableValues}
    {operation : Operation} {fuel : Nat} {source : ResolverValue ObjectRef}
    {result : ExecutionObservation}
    (conforms
      : queryWorkQueueConforms createWorkQueue schema resolvers variables operation
          fuel source)
    (observed
      : queryObservation createWorkQueue schema resolvers variables operation fuel
          source result)
    : ∃ scopes, result.collectFailureScopes = some scopes :=
  ExecutionObservation.failureScopes_exist
    (deliveryIDUsageValid_holds schema operation resolvers variables fuel source
      createWorkQueue result conforms observed)

/-- No error-bearing completion means the decoder produces no failure scopes.
Witness: the positive-error filter is empty at every response update.
-/
theorem collectFailureScopes_eq_nil_of_zero_completions
    (notices : List IncrementalPendingNotice)
    (updates : List IncrementalStreamUpdateResult)
    (zero : ∀ update ∈ updates, ∀ completion ∈ update.completed, completion.errors = 0)
    : DeliveryTrace.collectFailureScopes notices updates = some [] := by
  induction updates generalizing notices with
  | nil => rfl
  | cons update rest ih =>
      have empty : update.completed.filter (fun completion => completion.errors > 0) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro completion member
        simp [zero update (by simp) completion member]
      have tail := ih (notices ++ update.pending)
        (fun later member => zero later (by simp [member]))
      simp [DeliveryTrace.collectFailureScopes, empty, tail]

/-- Zero total errors excludes every positive-count completion, hence every failure scope.
Witness: each completion count is bounded by its response sum and the total error sum.
-/
theorem ExecutionObservation.failureScopes_eq_nil {result : ExecutionObservation}
    (zero : result.totalErrors = 0)
    : result.collectFailureScopes = some [] := by
  cases result with
  | single response => rfl
  | incremental initial updates =>
      apply collectFailureScopes_eq_nil_of_zero_completions
      intro update member completion present
      have inner : completion.errors ≤
          (update.completed.map IncrementalCompletionNotice.errors).sum :=
        WorkQueueSemantics.le_sum
        (List.mem_map.mpr ⟨completion, present, rfl⟩)
      have outer : (update.incremental.map IncrementalResult.errors).sum
          + (update.completed.map IncrementalCompletionNotice.errors).sum ≤
          (updates.map (fun update =>
            (update.incremental.map IncrementalResult.errors).sum
              + (update.completed.map IncrementalCompletionNotice.errors).sum)).sum :=
        WorkQueueSemantics.le_sum (List.mem_map.mpr ⟨update, member, rfl⟩)
      simp only [ExecutionObservation.totalErrors] at zero
      omega

/-- The proposed error-aware statement's zero-error branch follows from full coverage.
Witness: the existing position-permutation theorem and the empty failure-scope decoder.
This is not a proof of the unrestricted failure-aware public statement.
-/
theorem ResponsePositionsDeliveredOrFailed_of_zeroErrors
    {createWorkQueue : Work → WorkQueue} {schema : Schema}
    {resolvers : Resolvers ObjectRef} {variables : VariableValues} {operation : Operation}
    {fuel : Nat} {source : ResolverValue ObjectRef} {result : ExecutionObservation}
    (conforms
      : queryWorkQueueConforms createWorkQueue schema resolvers variables operation
          fuel source)
    (observed
      : queryOutcome createWorkQueue schema resolvers variables operation fuel
          source result)
    (zero : result.totalErrors = 0) (containers : Bool)
    : result.AddressesResponsePositions containers
        (GraphQL.Execution.executeQueryWithFuel schema resolvers variables
          operation.eraseIncrementalDirectives fuel source).data := by
  obtain ⟨slices, delivered, covered⟩ := deliveredResponsePositionsEquivalentToBasic_holds
    schema operation resolvers variables fuel source createWorkQueue result conforms observed
    zero containers
  refine ⟨slices, [], delivered, ExecutionObservation.failureScopes_eq_nil zero, ?_⟩
  intro path member
  exact Or.inl (covered.mem_iff.mpr member)

end GraphQL.IncrementalDelivery.Correctness
