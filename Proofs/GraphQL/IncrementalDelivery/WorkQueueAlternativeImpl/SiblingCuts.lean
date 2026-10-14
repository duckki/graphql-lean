import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ExecutionSiblingPlans

/-! A proof-only sequential sibling cut, running unchanged public actions until the
first fatal outcome. This constructs an actual prefix observation and key supply;
it is neither a replacement public executor nor a model of asynchronous settlement.
Recursive cuts inside those actions and native error occurrences remain separate.
-/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.ScheduledErrors

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics (
  id_pure_eq id_bind_eq id_map_eq run_bind run_map)

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

-----------------------------------------------------------------------------------------
-- Observe only the executed prefix, retaining the unexecuted action suffix
-----------------------------------------------------------------------------------------

def observeUntilFatal
    : List (StateM Nat (Completion α))
      → StateM Nat (List (Completion α) × List (StateM Nat (Completion α)))
  | [] => pure ([], [])
  | action :: rest => do
      let completed ← action
      match completed.result with
      | .error _ => return ([completed], rest)
      | .ok _ =>
          let later ← observeUntilFatal rest
          return (completed :: later.1, later.2)

/-- Fold just the observed prefix; a proof observer, not a public execution policy. -/
def cutActions (combine : α → β → β) (base : β)
    (actions : List (StateM Nat (Completion α)))
    : StateM Nat (Completion β) := do
  let cut ← observeUntilFatal actions
  return foldCompletions combine base cut.1

/-- Every executed action uses its actual input/output supply. Skipped actions are
retained but not run. No data, work, count or supply agreement is assumed here.
-/
inductive ActionCut
    : List (StateM Nat (Completion α)) → Nat
      → List (Completion α) → List (StateM Nat (Completion α)) → Nat → Prop where
  | empty : ActionCut [] supply [] [] supply
  | fatal (action rest supply completed next errors)
    (ran : action.run supply = (completed, next))
    (failed : completed.result = .error errors)
    : ActionCut (action :: rest) supply [completed] rest next
  | success (action rest supply completed next observed remaining finish value errors)
    (ran : action.run supply = (completed, next))
    (succeeded : completed.result = .ok (value, errors))
    (later : ActionCut rest next observed remaining finish)
    : ActionCut (action :: rest) supply (completed :: observed) remaining finish

/-- The observer constructs the same prefix witness used by all following conclusions. -/
theorem observeUntilFatal_cut (actions : List (StateM Nat (Completion α))) (supply : Nat)
    : let cut := (observeUntilFatal actions).run supply
      ActionCut actions supply cut.1.1 cut.1.2 cut.2 := by
  induction actions generalizing supply with
  | nil => exact .empty
  | cons action rest ih =>
      cases outcome : action.run supply with
      | mk completed next =>
          cases result : completed.result with
          | error errors =>
              simpa only [observeUntilFatal, run_bind, outcome, result, StateT.run_pure,
                id_pure_eq] using ActionCut.fatal action rest supply completed next errors
                  outcome result
          | ok resultValue =>
              obtain ⟨value, errors⟩ := resultValue
              simpa only [observeUntilFatal, run_bind, outcome, result, StateT.run_pure,
                id_pure_eq]
                using ActionCut.success action rest supply completed next _ _ _ value
                  errors outcome result (ih next)

-----------------------------------------------------------------------------------------
-- Checked decomposition: the eager executor continues from the cut's actual supply
-----------------------------------------------------------------------------------------

/-- This hypothetical eager suffix is used only for comparison; the cut never runs it. -/
theorem ActionCut.observed {actions : List (StateM Nat (Completion α))}
    {supply completed remaining next}
    (cut : ActionCut actions supply completed remaining next)
    : (observeActions actions).run supply
      = let omitted := (observeActions remaining).run next
        (completed ++ omitted.1, omitted.2) := by
  induction cut with
  | empty => rfl
  | fatal action rest supply completed next errors ran failed =>
      simp only [observeActions, run_bind, ran, StateT.run_pure, id_pure_eq,
        List.singleton_append]
  | success action rest supply completed next observed remaining finish value errors
      ran succeeded later ih =>
      simp only [observeActions, run_bind, ran, StateT.run_pure, id_pure_eq]
      rw [ih]
      rfl

theorem completion_combine_result (combine : α → β → γ)
    (left : Completion α) (right : Completion β)
    : (Completion.combine combine left right).result
      = Result.combine combine left.result right.result := by
  unfold Completion.combine
  cases Result.combine combine left.result right.result <;> rfl

theorem foldCompletions_result (combine : α → β → β) (base : β)
    (completed : Completion α) (rest : List (Completion α))
    : (foldCompletions combine base (completed :: rest)).result
      = Result.combine combine completed.result
          (foldCompletions combine base rest).result :=
  completion_combine_result ..

theorem foldCompletions_errors_append (combine : α → β → β) (base : β)
    (left right : List (Completion α))
    : countedErrors (foldCompletions combine base (left ++ right)).result
      = countedErrors (foldCompletions combine base left).result
        + countedErrors (foldCompletions combine base right).result := by
  induction left with
  | nil => simp [foldCompletions, Completion.pure, countedErrors]
  | cons completed rest ih =>
      simp only [List.cons_append, foldCompletions_result, countedErrors_combine, ih]
      exact (Nat.add_assoc ..).symm

/-- No error count is chosen independently: the difference is exactly the untouched
suffix's eager count, evaluated from this same cut boundary.
-/
theorem ActionCut.error_accounting {actions : List (StateM Nat (Completion α))}
    {supply completed remaining next}
    (cut : ActionCut actions supply completed remaining next)
    (combine : α → β → β) (base : β)
    : countedErrors (foldCompletions combine base completed).result
        + countedErrors
            (foldCompletions combine base ((observeActions remaining).run next).1).result
      = countedErrors ((executeActions combine base actions).run supply).1.result := by
  rw [executeActions_observed, cut.observed]
  dsimp only
  exact (foldCompletions_errors_append ..).symm

/-- The unchanged atomic actions yield the same data/fatal status. This is not an
agreement theorem for actions whose inner recursion itself has been cancelled.
-/
theorem ActionCut.sameData {actions : List (StateM Nat (Completion α))}
    {supply completed remaining next}
    (cut : ActionCut actions supply completed remaining next)
    (combine : α → β → β) (base : β)
    : SameData (foldCompletions combine base completed).result
        ((executeActions combine base actions).run supply).1.result := by
  induction cut with
  | empty => rfl
  | fatal action rest supply completed next errors ran failed =>
      simp only [executeActions, run_bind, ran, StateT.run_pure, id_pure_eq,
        failed, foldCompletions, Completion.pure,
        Completion.combine, Result.combine, Completion.error, SameData]
      cases ((executeActions combine base rest).run next).1.result <;> trivial
  | success action rest supply completed next observed remaining finish value errors
      ran succeeded later ih =>
      simp only [executeActions, run_bind, ran, StateT.run_pure, id_pure_eq,
        foldCompletions_result, succeeded]
      rw [completion_combine_result, succeeded]
      cases left : (foldCompletions combine base observed).result
      <;> cases right : ((executeActions combine base rest).run next).1.result
      <;> simp only [left, right, SameData] at ih
      <;> simp [Result.combine, SameData, ih]

/-- A nonfatal cut exhausted the entire action list, hence preserves the full original
completion (including work) and final supply, not merely data and counted errors.
-/
theorem ActionCut.nonfatal_exact {actions : List (StateM Nat (Completion α))}
    {supply completed remaining next}
    (cut : ActionCut actions supply completed remaining next)
    (combine : α → β → β) (base : β)
    (healthy : isFatal (foldCompletions combine base completed).result = false)
    : remaining = []
      ∧ (executeActions combine base actions).run supply
        = (foldCompletions combine base completed, next) := by
  have exhausted : remaining = [] := by
    induction cut with
    | empty => rfl
    | fatal action rest supply completed next errors ran failed =>
        rw [foldCompletions_result, isFatal_combine, failed] at healthy
        simp [isFatal] at healthy
    | success action rest supply completed next observed remaining finish value errors
        ran succeeded later ih =>
        rw [foldCompletions_result, isFatal_combine, succeeded] at healthy
        exact ih healthy
  refine ⟨exhausted, ?_⟩
  rw [executeActions_observed, cut.observed, exhausted]
  simp only [observeActions, StateT.run_pure, id_pure_eq, List.append_nil]

/-- Failed semantic completions expose no child work, even if the observed prefix
constructed some. This statement does not release already acquired native resources.
-/
theorem foldCompletions_fatal_work (combine : α → β → β) (base : β)
    (completed : List (Completion α))
    (failed : isFatal (foldCompletions combine base completed).result = true)
    : (foldCompletions combine base completed).work = .empty := by
  cases completed with
  | nil => simp [foldCompletions, Completion.pure, isFatal] at failed
  | cons head rest =>
      exact fatal_combine_work combine head (foldCompletions combine base rest)
        (by rwa [foldCompletions_result] at failed)

theorem ActionCut.fatal_no_children {actions : List (StateM Nat (Completion α))}
    {supply completed remaining next}
    (cut : ActionCut actions supply completed remaining next)
    (combine : α → β → β) (base : β)
    (failed : isFatal (foldCompletions combine base completed).result = true)
    : (foldCompletions combine base completed).work = .empty
      ∧ ((executeActions combine base actions).run supply).1.work = .empty := by
  refine ⟨foldCompletions_fatal_work _ _ _ failed, ?_⟩
  have agreement := cut.sameData combine base
  have eagerFailed
      : isFatal ((executeActions combine base actions).run supply).1.result = true := by
    cases left : (foldCompletions combine base completed).result
    <;> cases right : ((executeActions combine base actions).run supply).1.result
    <;> simp_all [SameData, isFatal]
  rw [executeActions_observed] at eagerFailed ⊢
  exact foldCompletions_fatal_work _ _ _ eagerFailed

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.ScheduledErrors
