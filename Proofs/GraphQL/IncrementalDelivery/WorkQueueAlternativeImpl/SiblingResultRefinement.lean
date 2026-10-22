import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.SiblingCuts
import Proofs.GraphQL.IncrementalDelivery.Semantics.BasicErrors

/-! Conditional sibling-composition edge for recursively changed child outcomes.
Unlike an atomic cut, paired actions need not have identical outcomes or key supplies.
The actual paired child runs must establish result refinement and carry the same supply
relation forward. Those recursive premises are explicit and are not proved here.

Counts remain observable: the relation preserves data/fatal status and error presence,
and permits only a decrease in counted errors. It neither rewrites public/native payloads
nor proves which originating errors were skipped. Work, compatible keys, recording
histories and native async correspondence remain separate obligations. -/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.ScheduledErrors

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
  (id_pure_eq id_bind_eq id_map_eq run_bind run_map)

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

-----------------------------------------------------------------------------------------
-- Result relation: counts can decrease, but completed data and error presence cannot
-----------------------------------------------------------------------------------------

/-- Data/status agreement, bounded error counts and the same presence of errors.
This is a proof relation, not an error-count adapter or a native-reporting license. -/
def ResultRefines (scheduled eager : Result α) : Prop :=
  SameData scheduled eager
  ∧ countedErrors scheduled ≤ countedErrors eager
  ∧ (countedErrors scheduled = 0 ↔ countedErrors eager = 0)

theorem ResultRefines.refl (result : Result α) : ResultRefines result result := by
  cases result <;> simp [ResultRefines, SameData]

theorem ResultRefines.combine (combine : α → β → γ)
    {left leftEager : Result α} {right rightEager : Result β}
    (head : ResultRefines left leftEager) (tail : ResultRefines right rightEager)
    : ResultRefines (Result.combine combine left right)
        (Result.combine combine leftEager rightEager) := by
  rcases left with errors | ⟨value, errors⟩
  <;> rcases leftEager with eagerErrors | ⟨eagerValue, eagerErrors⟩
  <;> rcases right with laterErrors | ⟨laterValue, laterErrors⟩
  <;> rcases rightEager with laterEagerErrors | ⟨laterEagerValue, laterEagerErrors⟩
  <;> simp_all [ResultRefines, SameData, Result.combine, countedErrors]
  <;> omega

/-- A cut is sound only with a positive actual fatal count. This excludes dropping a
later error merely because a raw, impossible zero-count failure cut the scope. -/
theorem ResultRefines.fatal_cut (combine : α → β → γ)
    {errors : Nat} {eagerHead : Result α} (eagerTail : Result β)
    (head : ResultRefines (.error errors) eagerHead) (positive : 0 < errors)
    : ResultRefines (.error errors) (Result.combine combine eagerHead eagerTail) := by
  rcases eagerHead with eagerErrors | ⟨eagerValue, eagerErrors⟩
  <;> rcases eagerTail with laterErrors | ⟨laterValue, laterErrors⟩
  <;> simp_all [ResultRefines, SameData, Result.combine, countedErrors]
  <;> omega

theorem ResultRefines.completion_map (wrap : α → β)
    {left right : Completion α} (known : ResultRefines left.result right.result)
    : ResultRefines (left.map wrap).result (right.map wrap).result := by
  rcases left with ⟨left, leftWork⟩
  rcases right with ⟨right, rightWork⟩
  rcases left with errors | ⟨value, errors⟩
  <;> rcases right with eagerErrors | ⟨eagerValue, eagerErrors⟩
  <;> simp_all [ResultRefines, SameData, Completion.map, Completion.error, countedErrors]

theorem ResultRefines.catchNull (wrap : α → ResponseValue)
    {left right : Completion α} (known : ResultRefines left.result right.result)
    : ResultRefines (left.catchNull wrap).result (right.catchNull wrap).result := by
  rcases left with ⟨left, leftWork⟩
  rcases right with ⟨right, rightWork⟩
  rcases left with errors | ⟨value, errors⟩
  <;> rcases right with eagerErrors | ⟨eagerValue, eagerErrors⟩
  <;> simp_all [ResultRefines, SameData, Completion.catchNull, countedErrors]

theorem ResultRefines.nonNull {left right : Completion ResponseValue}
    (known : ResultRefines left.result right.result)
    : ResultRefines left.nonNull.result right.nonNull.result := by
  rcases left with ⟨left, leftWork⟩
  rcases right with ⟨right, rightWork⟩
  rcases left with errors | ⟨value, errors⟩
  <;> rcases right with eagerErrors | ⟨eagerValue, eagerErrors⟩
  <;> simp_all only [ResultRefines, SameData, countedErrors, false_and]
  · simpa [Completion.nonNull, nonNullCompletion, Completion.error, ResultRefines,
      SameData, countedErrors] using known
  · obtain ⟨rfl, bounded, zero⟩ := known
    cases value <;> cases errors <;> cases eagerErrors <;>
      simp_all [Completion.nonNull, nonNullCompletion, Completion.error]

-----------------------------------------------------------------------------------------
-- Coupled child actions: carry one actual input/output supply relation through siblings
-----------------------------------------------------------------------------------------

/-- Recursive leaf premise at paired actual supplies. The chosen relation can include
key-map/context invariants; True is useful only for result-only finite regressions. -/
def ActionRefines (supplies : Nat → Nat → Prop)
    (scheduled eager : StateM Nat (Completion α))
    : Prop :=
  ∀ left right,
    supplies left right
    → ResultRefines (scheduled.run left).1.result (eager.run right).1.result
      ∧ supplies (scheduled.run left).2 (eager.run right).2
      ∧ Semantics.BasicErrors.PositiveFailure (scheduled.run left).1.result

/-- Same ordered response positions, with related recursive actions at each position. -/
inductive PairedActions (supplies : Nat → Nat → Prop)
    : List (StateM Nat (Completion α)) → List (StateM Nat (Completion α)) → Prop where
  | nil : PairedActions supplies [] []
  | cons {scheduled eager scheduledRest eagerRest}
    (head : ActionRefines supplies scheduled eager)
    (rest : PairedActions supplies scheduledRest eagerRest)
    : PairedActions supplies (scheduled :: scheduledRest) (eager :: eagerRest)

/-- Operational decomposition of the cut fold, including exact Work and final supply. -/
theorem cutActions_cons (combine : α → β → β) (base : β)
    (action : StateM Nat (Completion α)) (rest : List (StateM Nat (Completion α)))
    : cutActions combine base (action :: rest)
      = (do
          let head ← action
          match head.result with
          | .error errors => return { Completion.error errors with cause := head.cause }
          | .ok _ =>
              let tail ← cutActions combine base rest
              return Completion.combine combine head tail) := by
  funext supply
  change (cutActions combine base (action :: rest)).run supply =
    ((do
      let head ← action
      match head.result with
      | .error errors => return { Completion.error errors with cause := head.cause }
      | .ok _ =>
          let tail ← cutActions combine base rest
          return Completion.combine combine head tail) : StateM Nat (Completion β)).run
      supply
  cases ran : action.run supply with
  | mk head next =>
      cases result : head.result with
      | error errors =>
          simp [cutActions, observeUntilFatal, ran, result, foldCompletions,
            Completion.combine, Result.combine, Completion.pure]
      | ok value =>
          simp [cutActions, observeUntilFatal, ran, result, foldCompletions]

/-- Paired child actions imply the parent's result refinement. The supply relation is
retained when no parent cut occurs; after a fatal cut the eager suffix may allocate a
gap, which requires the separate compatible-map construction. -/
def SiblingResultRefinement : Prop :=
  ∀ (α β : Type) (supplies : Nat → Nat → Prop) (combine : α → β → β) (base : β)
    (scheduled eager : List (StateM Nat (Completion α))) left right,
    PairedActions supplies scheduled eager
    → supplies left right
    → ResultRefines ((cutActions combine base scheduled).run left).1.result
        ((executeActions combine base eager).run right).1.result
      ∧ (isFatal ((cutActions combine base scheduled).run left).1.result = false
          → supplies ((cutActions combine base scheduled).run left).2
              ((executeActions combine base eager).run right).2)

theorem siblingResultRefinement_holds : SiblingResultRefinement := by
  intro α β supplies combine base scheduled eager left right paired initial
  induction paired generalizing left right with
  | nil => exact ⟨ResultRefines.refl _, fun _ => initial⟩
  | @cons scheduledHead eagerHead scheduledTail eagerTail head rest ih =>
      obtain ⟨refined, next, positive⟩ := head left right initial
      rw [cutActions_cons]
      simp only [executeActions, run_bind]
      cases result : (scheduledHead.run left).1.result with
      | error errors =>
          rw [result] at refined
          simp only [StateT.run_pure, id_pure_eq, Completion.error, isFatal,
            Bool.true_eq_false, false_implies, and_true, completion_combine_result]
          exact refined.fatal_cut combine _ (positive errors result)
      | ok value =>
          rw [result] at refined
          obtain ⟨tail, later⟩ := ih _ _ next
          simp only [result, run_bind, StateT.run_pure, id_pure_eq,
            completion_combine_result]
          refine ⟨refined.combine combine tail, ?_⟩
          intro healthy
          rw [isFatal_combine] at healthy
          exact later (by simpa only [isFatal, Bool.false_or] using healthy)

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.ScheduledErrors
