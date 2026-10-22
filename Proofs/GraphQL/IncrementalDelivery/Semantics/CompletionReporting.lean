import Proofs.GraphQL.IncrementalDelivery.Semantics.Completion

/-! Collected diagnostics and selected explanations at a payload boundary. These results
concern the completion algebra; queue admission and wire reporting are separate layers.
-/

namespace GraphQL.IncrementalDelivery.Semantics.CompletionReporting

open GraphQL.IncrementalDelivery.Execution

/-- A raw outcome without a selected cause preserves the supplied result. -/
@[simp]
theorem deliveryResult_no_cause (result : Result α)
    : ({ result } : TaskOutcome α).deliveryResult = result := by
  cases result <;> rfl

/-- A successful delivery preserves its collected result unchanged. -/
theorem result_eq_ok_of_deliveryResult_eq_ok {outcome : TaskOutcome α}
    {data : α} {errors : Nat} (same : outcome.deliveryResult = .ok (data, errors))
    : outcome.result = .ok (data, errors) := by
  cases outcome with
  | mk result cause => cases result <;> simp_all [TaskOutcome.deliveryResult]

/-- The ordinary projection still uses the shared additive result algebra. -/
theorem combine_result (f : α → β → γ) (left : Completion α) (right : Completion β)
    : (Completion.combine f left right).result
      = Result.combine f left.result right.result := by
  cases h : Result.combine f left.result right.result <;>
    simp [Completion.combine, h, Completion.error]

/-- A failing left sibling supplies the cause, independently of sibling diagnostics. -/
theorem combine_left_cause (f : α → β → γ) (left : Completion α) (right : Completion β)
    (failed : left.result = .error errors)
    : (Completion.combine f left right).cause = left.cause := by
  cases hr : right.result <;>
    simp [Completion.combine, failed, hr, GraphQL.Execution.Result.combine]

/-- A successful left sibling cannot supply the escaping cause of a failed right sibling.
-/
theorem combine_right_cause (f : α → β → γ) (left : Completion α) (right : Completion β)
    (succeeded : left.result = .ok value) (failed : right.result = .error errors)
    : (Completion.combine f left right).cause = right.cause := by
  simp [Completion.combine, succeeded, failed, GraphQL.Execution.Result.combine]

/-- Delivered data keeps its entire diagnostic count. -/
theorem deliveryResult_ok (completed : Completion α)
    (succeeded : completed.result = .ok value)
    : completed.deliveryResult = .ok value := by
  simp [Completion.deliveryResult, Completion.outcome, TaskOutcome.deliveryResult, succeeded]

/-- A failed boundary reports the selected cause, without replacing it by a constant. -/
theorem deliveryResult_error (completed : Completion α)
    (failed : completed.result = .error errors) (selected : completed.cause = some cause)
    : completed.deliveryResult = .error cause := by
  simp [Completion.deliveryResult, Completion.outcome, TaskOutcome.deliveryResult, failed, selected]

/-- Catching a failure retains every diagnostic and the cause of the resulting null. -/
theorem catchNull_error (wrap : α → ResponseValue) (completed : Completion α)
    (failed : completed.result = .error errors)
    : (completed.catchNull wrap).result = .ok (.null, errors)
      ∧ (completed.catchNull wrap).cause = completed.cause := by
  simp [Completion.catchNull, failed]

/-- An enclosing non-null wrapper rethrows the caught cause, including its full count. -/
theorem nonNull_catchNull (wrap : α → ResponseValue) (completed : Completion α)
    (failed : completed.result = .error errors) (selected : completed.cause = some cause)
    : ((completed.catchNull wrap).nonNull).deliveryResult = .error cause := by
  cases errors <;>
    simp [Completion.catchNull, Completion.nonNull, Completion.deliveryResult, Completion.outcome, TaskOutcome.deliveryResult,
      Completion.error, nonNullCompletion, failed, selected]

/-- Mapping delivered data clears a caught-null cause while retaining its diagnostics. -/
theorem map_ok (f : α → β) (completed : Completion α)
    (succeeded : completed.result = .ok (value, errors))
    : (completed.map f).result = .ok (f value, errors)
      ∧ (completed.map f).cause = none := by
  simp [Completion.map, succeeded]

def diagnostics : Result α → Nat
  | .error errors => errors
  | .ok (_, errors) => errors

/-- A retained explanation is positive and bounded by collected diagnostics; a bubble
has an explanation. This invariant makes the reporting projection reflect failure.
-/
def CauseValid (completed : Completion α) : Prop :=
  (∀ cause,
    completed.cause = some cause → 0 < cause ∧ cause ≤ diagnostics completed.result)
  ∧ (∀ errors, completed.result = .error errors → completed.cause.isSome)

theorem pure_valid (value : α) : CauseValid (Completion.pure value) := by
  simp [CauseValid, Completion.pure]

theorem error_valid (errors : Nat) (positive : 0 < errors)
    : CauseValid (Completion.error errors : Completion α) := by
  simp [CauseValid, Completion.error, diagnostics, positive]

theorem combine_valid (f : α → β → γ) (left : Completion α) (right : Completion β)
    (hl : CauseValid left) (hr : CauseValid right)
    : CauseValid (Completion.combine f left right) := by
  rcases hl with ⟨hl, hlf⟩
  rcases hr with ⟨hr, hrf⟩
  cases he : left.result <;> cases hf : right.result <;>
    simp only [Completion.combine, he, hf, GraphQL.Execution.Result.combine]
  · constructor
    · intro cause hc
      have h := hl cause hc
      simp only [he, diagnostics] at h
      exact ⟨h.1, Nat.le_add_right_of_le h.2⟩
    · simpa [Completion.error] using hlf _ he
  · constructor
    · intro cause hc
      have h := hl cause hc
      simp only [he, diagnostics] at h
      exact ⟨h.1, Nat.le_add_right_of_le h.2⟩
    · simpa [Completion.error] using hlf _ he
  · constructor
    · intro cause hc
      have h := hr cause hc
      simp only [hf, diagnostics] at h
      exact ⟨h.1, Nat.le_add_left_of_le h.2⟩
    · simpa [Completion.error] using hrf _ hf
  · simp [CauseValid]

theorem map_valid (f : α → β) (completed : Completion α) (valid : CauseValid completed)
    : CauseValid (completed.map f) := by
  cases hr : completed.result with
  | error errors =>
      simpa [CauseValid, Completion.map, hr, Completion.error, diagnostics] using valid
  | ok result => simp [CauseValid, Completion.map, hr]

theorem catchNull_valid (f : α → ResponseValue) (completed : Completion α)
    (valid : CauseValid completed)
    : CauseValid (completed.catchNull f) := by
  cases hr : completed.result with
  | error errors =>
      simpa [CauseValid, Completion.catchNull, hr, diagnostics] using valid.1
  | ok result => simp [CauseValid, Completion.catchNull, hr]

theorem nonNull_valid (completed : Completion ResponseValue)
    (valid : CauseValid completed)
    : CauseValid completed.nonNull := by
  cases hr : completed.result with
  | error errors =>
      simpa [CauseValid, Completion.nonNull, hr, nonNullCompletion, Completion.error,
        diagnostics] using valid
  | ok result =>
      rcases result with ⟨value, errors⟩
      cases value with
      | null =>
          cases hc : completed.cause with
          | none =>
              cases errors <;>
                simp [CauseValid, Completion.nonNull, hr, hc, nonNullCompletion,
                  Completion.error, diagnostics]
          | some cause =>
              have h := valid.1 cause hc
              simp only [hr, diagnostics] at h
              have positive : 0 < errors := Nat.lt_of_lt_of_le h.1 h.2
              cases errors with
              | zero => omega
              | succ errors =>
                  simp [CauseValid, Completion.nonNull, hr, hc, nonNullCompletion,
                    Completion.error, diagnostics, h]
      | scalar value | object value | list value =>
          simpa [CauseValid, Completion.nonNull, hr, nonNullCompletion, diagnostics] using valid.1

/-- Selected positive causes cannot turn a failing boundary into zero reported errors. -/
theorem deliveryResult_positive (completed : Completion α) (valid : CauseValid completed)
    (failed : completed.deliveryResult = .error errors)
    : 0 < errors := by
  cases hr : completed.result with
  | ok result =>
      simp [Completion.deliveryResult, Completion.outcome, TaskOutcome.deliveryResult, hr] at failed
  | error collected =>
      obtain ⟨cause, hc⟩ := Option.isSome_iff_exists.mp (valid.2 collected hr)
      have positive := (valid.1 cause hc).1
      have equal : cause = errors := by
        simpa [Completion.deliveryResult, Completion.outcome, TaskOutcome.deliveryResult,
          hr, hc]
          using failed
      simpa [← equal] using positive

end GraphQL.IncrementalDelivery.Semantics.CompletionReporting
