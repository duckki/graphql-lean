import Proofs.GraphQL.IncrementalDelivery.Correctness.BasicFieldErrors

/-! Ordinary execution cannot repair a bubbling or null initial incremental outcome. -/

namespace GraphQL.IncrementalDelivery.Correctness.InitialFailures
open GraphQL.IncrementalDelivery.Execution

-----------------------------------------------------------------------------------------
-- Failure comparison, independent of counted-error equality and future work
-----------------------------------------------------------------------------------------

/-- Every bubbling `initial` outcome also bubbles in `ordinary` execution.
The counts may differ because ordinary execution also evaluates deferred selections.
-/
def BubblesPreserved (ordinary initial : Result α) : Prop :=
  ∀ errors, initial = .error errors → ∃ count, ordinary = .error count

/-- Initial bubbling and initial null remain bubbling or null in ordinary execution.
This includes nullable catches and supplies the extra case needed by non-null wrappers.
-/
def ValueFailuresPreserved (ordinary initial : Result ResponseValue) : Prop :=
  BubblesPreserved ordinary initial
  ∧ ∀ errors,
      initial = .ok (.null, errors)
      → (∃ count, ordinary = .error count) ∨ ∃ count, ordinary = .ok (.null, count)

/-- Identical results preserve bubbling, without requiring positive or zero errors. -/
theorem BubblesPreserved.refl (result : Result α) : BubblesPreserved result result :=
  fun errors failed => ⟨errors, failed⟩

/-- A successful initial result has no bubbling outcome to preserve. -/
theorem BubblesPreserved.ok (ordinary : Result α) (data : α) (errors : Nat)
    : BubblesPreserved ordinary (.ok (data, errors)) := by
  intro count failed
  cases failed

/-- Identical value outcomes also preserve null, including nullable counted errors. -/
theorem ValueFailuresPreserved.refl (result : Result ResponseValue)
    : ValueFailuresPreserved result result :=
  ⟨BubblesPreserved.refl result, fun errors isNull => Or.inr ⟨errors, isNull⟩⟩

/-- A non-null successful initial value imposes no initial-failure restriction.
Witness: that result is neither bubbling nor null; ordinary execution may still fail.
-/
theorem ValueFailuresPreserved.nonNullOk (ordinary : Result ResponseValue)
    (data : ResponseValue) (errors : Nat) (notNull : data ≠ .null)
    : ValueFailuresPreserved ordinary (.ok (data, errors)) := by
  refine ⟨BubblesPreserved.ok ordinary data errors, ?_⟩
  intro count isNull
  exact False.elim (notNull (congrArg Prod.fst (Except.ok.inj isNull)))

/-- An ordinary nonbubbling result has a nonbubbling initial counterpart.
Witness: an initial bubble would force ordinary bubbling, contradicting success.
The initial data and counted errors need not equal the ordinary ones.
-/
theorem BubblesPreserved.initial_success {ordinary : Result α} {initial : Result α}
    (preserved : BubblesPreserved ordinary initial) (data : α) (errors : Nat)
    (success : ordinary = .ok (data, errors))
    : ∃ value count, initial = .ok (value, count) := by
  cases outcome : initial with
  | error count =>
      obtain ⟨count, failed⟩ := preserved _ outcome
      simp [success] at failed
  | ok pair => exact ⟨pair.1, pair.2, rfl⟩

/-- An ordinary successful non-null value has a successful non-null initial counterpart.
Witness: forward bubble/null preservation rules out both unwanted initial outcomes.
This is only an outer-value guard; equality of nested data is not claimed.
-/
theorem ValueFailuresPreserved.initial_nonNull {ordinary initial : Result ResponseValue}
    (preserved : ValueFailuresPreserved ordinary initial) (data : ResponseValue)
    (errors : Nat) (success : ordinary = .ok (data, errors)) (notNull : data ≠ .null)
    : ∃ value count, initial = .ok (value, count) ∧ value ≠ .null := by
  obtain ⟨value, count, initialSuccess⟩ := preserved.1.initial_success data errors success
  refine ⟨value, count, initialSuccess, ?_⟩
  intro isNull
  rw [isNull] at initialSuccess
  rcases preserved.2 count initialSuccess with failed | ordinaryNull
  · obtain ⟨count, failed⟩ := failed
    simp [success] at failed
  · obtain ⟨count, ordinaryNull⟩ := ordinaryNull
    rw [success] at ordinaryNull
    exact notNull (congrArg Prod.fst (Except.ok.inj ordinaryNull))

/-- Combining field/list outcomes preserves bubbling if each part does.
Witness: inspect result combinations; one bubbling initial part forces its ordinary part
to bubble, independently of the other ordinary outcome and its counted errors.
-/
theorem BubblesPreserved.combine (combine : α → β → γ)
    {ordinaryLeft initialLeft : Result α} {ordinaryRight initialRight : Result β}
    (left : BubblesPreserved ordinaryLeft initialLeft)
    (right : BubblesPreserved ordinaryRight initialRight)
    : BubblesPreserved (Result.combine combine ordinaryLeft ordinaryRight)
        (Result.combine combine initialLeft initialRight) := by
  intro errors failed
  cases initialLeft with
  | error count =>
      obtain ⟨ordinaryCount, ordinaryFailed⟩ := left count rfl
      cases ordinaryRight <;> simp [Result.combine, ordinaryFailed]
  | ok value =>
      cases initialRight with
      | ok other => simp [Result.combine] at failed
      | error count =>
          obtain ⟨ordinaryCount, ordinaryFailed⟩ := right count rfl
          cases ordinaryLeft <;> simp [Result.combine, ordinaryFailed]

/-- Completion combination has the same result-level bubbling comparison.
Witness: combination's work cancellation changes only work, not the combined result.
-/
theorem BubblesPreserved.combineCompletions (combine : α → β → γ)
    {ordinaryLeft : Result α} {ordinaryRight : Result β}
    {initialLeft : Completion α} {initialRight : Completion β}
    (left : BubblesPreserved ordinaryLeft initialLeft.result)
    (right : BubblesPreserved ordinaryRight initialRight.result)
    : BubblesPreserved (Result.combine combine ordinaryLeft ordinaryRight)
        (Completion.combine combine initialLeft initialRight).result := by
  have preserved := BubblesPreserved.combine combine left right
  cases first : initialLeft.result <;> cases last : initialRight.result <;>
    simpa [Completion.combine, Completion.error, Result.combine, first, last] using preserved

/-- Extra ordinary fields cannot repair an already bubbling initial field partition.
Witness: the preserved ordinary failure bubbles under either right-hand result.
-/
theorem BubblesPreserved.appendOrdinary (combine : α → β → α)
    {ordinary initial : Result α} (preserved : BubblesPreserved ordinary initial)
    (right : Result β)
    : BubblesPreserved (Result.combine combine ordinary right) initial := by
  intro errors failed
  obtain ⟨count, bubbles⟩ := preserved errors failed
  cases right <;> simp [Result.combine, bubbles]

/-- Mapping a completed field value does not change whether it bubbles.
Witness: successful mapping remains successful; an error retains its ordinary failure.
-/
theorem BubblesPreserved.map (transform : α → β) {ordinary : Result α}
    {initial : Completion α} (preserved : BubblesPreserved ordinary initial.result)
    : BubblesPreserved
        (match ordinary with
          | .error errors => .error errors
          | .ok (data, errors) => .ok (transform data, errors))
        (initial.map transform).result := by
  intro errors failed
  cases outcome : initial.result with
  | error count =>
      obtain ⟨count, ordinaryFailed⟩ := preserved _ outcome
      simp [ordinaryFailed]
  | ok value => simp [Completion.map, outcome] at failed

/-- Nullable catching preserves initial null as ordinary null.
Witness: preserved bubbling is caught by both executions; a wrapped successful result
cannot become null when `wrap` is non-null. Caught results themselves never bubble.
-/
theorem BubblesPreserved.catchNull (wrap : α → ResponseValue)
    (notNull : ∀ data, wrap data ≠ .null) {ordinary : Result α} {initial : Completion α}
    (preserved : BubblesPreserved ordinary initial.result)
    : ValueFailuresPreserved (GraphQL.Execution.catchBubbleAsNull wrap ordinary)
        (initial.catchNull wrap).result := by
  constructor
  · intro errors failed
    cases outcome : initial.result <;> simp [Completion.catchNull, outcome] at failed
  · intro errors isNull
    cases outcome : initial.result with
    | error count =>
        obtain ⟨count, failed⟩ := preserved _ outcome
        exact Or.inr ⟨count, by simp [GraphQL.Execution.catchBubbleAsNull, failed]⟩
    | ok result =>
        obtain ⟨data, count⟩ := result
        simp only [Completion.catchNull, outcome, Except.ok.injEq, Prod.mk.injEq] at isNull
        exact False.elim (notNull data isNull.1)

/-- Non-null completion preserves initial failure, including initial nullable null.
Witness: a bubbling input stays bubbling; an initial null has an ordinary null or
bubbling counterpart, and either becomes a non-null failure. Counts need not agree.
-/
theorem ValueFailuresPreserved.nonNull {ordinary : Result ResponseValue}
    {initial : Completion ResponseValue}
    (preserved : ValueFailuresPreserved ordinary initial.result)
    : ValueFailuresPreserved (GraphQL.Execution.nonNullCompletion ordinary)
        initial.nonNull.result := by
  constructor
  · intro errors failed
    cases outcome : initial.result with
    | error count =>
        obtain ⟨count, ordinaryFailed⟩ := preserved.1 _ outcome
        exact ⟨count, by simp [GraphQL.Execution.nonNullCompletion, ordinaryFailed]⟩
    | ok result =>
        obtain ⟨data, count⟩ := result
        cases data with
        | null =>
            rcases preserved.2 count outcome with bubbles | isNull
            · obtain ⟨count, ordinaryFailed⟩ := bubbles
              exact ⟨count, by simp [GraphQL.Execution.nonNullCompletion, ordinaryFailed]⟩
            · obtain ⟨count, ordinaryNull⟩ := isNull
              cases count <;> simp [GraphQL.Execution.nonNullCompletion, ordinaryNull]
        | scalar _ | object _ | list _ =>
            simp [Completion.nonNull, outcome, GraphQL.Execution.nonNullCompletion] at failed
  · intro errors isNull
    cases outcome : initial.result with
    | error count => simp [Completion.nonNull, Completion.error, outcome,
        GraphQL.Execution.nonNullCompletion] at isNull
    | ok result =>
        obtain ⟨data, count⟩ := result
        cases data <;> cases count <;>
          simp [Completion.nonNull, Completion.error, outcome,
            GraphQL.Execution.nonNullCompletion] at isNull

/-- Field-result permutation preserves the bubbling comparison with initial completion.
Witness: equivalent field results have the same success/failure constructor, including
nonzero nullable errors. This is independent of successful data order.
-/
theorem BubblesPreserved.of_fieldEquivalent {ordinary other initial}
    (equivalent : TypedResponse.FieldResultsEquivalent ordinary other)
    (preserved : BubblesPreserved other initial)
    : BubblesPreserved ordinary initial := by
  intro errors failed
  obtain ⟨count, bubbles⟩ := preserved errors failed
  rw [bubbles] at equivalent
  cases ordinary with
  | error count => exact ⟨count, rfl⟩
  | ok value => simp [TypedResponse.FieldResultsEquivalent] at equivalent

end GraphQL.IncrementalDelivery.Correctness.InitialFailures
