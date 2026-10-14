import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ReaderLifecycle

/-! Finite, non-reentrant cached-computation call boundaries. Evaluation and cleanup
labels identify invocation sites, not resource inventories or settled effects. A pending
promise's once-only continuation survives abort and may replace the rejection cache later.
The native callback-to-trace construction remains separate from this checked model.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement

-----------------------------------------------------------------------------------------
-- Cached computation and the still-live promise continuation
-----------------------------------------------------------------------------------------

inductive ComputationResult (value error : Type) where
  | pending
  | fulfilled (result : value)
  | rejected (reason : error)
deriving Repr

def ComputationResult.isPending : ComputationResult value error → Bool
  | .pending => true
  | _ => false

/-- Optional outcome cache, abort callback availability, and independent promise continuation.
continuation is proof evidence for the promise's single settlement, not another native flag.
-/
structure CachedComputation (value error : Type) where
  cache : Option (ComputationResult value error) := none
  abortAvailable : Bool := true
  continuation : Bool := false
deriving Repr

inductive ComputationEffect where
  | evaluate
  | abortCallback
deriving Repr, DecidableEq

def ComputationEffect.isEvaluation : ComputationEffect → Bool
  | .evaluate => true
  | _ => false

def ComputationEffect.isAbortCallback : ComputationEffect → Bool
  | .abortCallback => true
  | _ => false

inductive ComputationAction (value error : Type) where
  /-- The supplied outcome matters only when _fn is actually invoked. -/
  | prime (started : ComputationResult value error)
  | settle (outcome : Except error value)
  | abort (reason : error)
deriving Repr

/-- prime and result share the same cached evaluation. No eager executor is allocated here. -/
def CachedComputation.prime (state : CachedComputation value error)
    (started : ComputationResult value error)
    : CachedComputation value error × List ComputationEffect :=
  if state.cache.isSome then
    (state, [])
  else
    ({ state with cache := some started, continuation := started.isPending }, [.evaluate])

/-- abort clears onAbort before invoking it, even for fulfilled unpublished work. An abort
before evaluation caches rejection but invokes neither _fn nor the executor cleanup callback.
-/
def CachedComputation.abort (state : CachedComputation value error) (reason : error)
    : CachedComputation value error × List ComputationEffect :=
  match state.cache with
  | none => ({ state with cache := some (.rejected reason) }, [])
  | some .pending =>
      (
        { state with cache := some (.rejected reason), abortAvailable := false },
        if state.abortAvailable then [.abortCallback] else []
      )
  | some (.fulfilled _) =>
      (
        { state with abortAvailable := false },
        if state.abortAvailable then [.abortCallback] else []
      )
  | some (.rejected _) => (state, [])

/-- A once-only promise continuation can overwrite abort's cached rejection. It does not
invoke _fn, onAbort, or queue publication. Extra settlement observations are ignored.
-/
def CachedComputation.settle (state : CachedComputation value error)
    (outcome : Except error value)
    : CachedComputation value error × List ComputationEffect :=
  if state.continuation then
    let result :=
      match outcome with
      | .ok value => .fulfilled value
      | .error reason => .rejected reason
    ({ state with cache := some result, continuation := false }, [])
  else
    (state, [])

def CachedComputation.step (state : CachedComputation value error)
    : ComputationAction value error
      → CachedComputation value error × List ComputationEffect
  | .prime started => state.prime started
  | .settle outcome => state.settle outcome
  | .abort reason => state.abort reason

/-- One actual state and ordered invocation trace, without predicting callback timing. -/
def CachedComputation.run (state : CachedComputation value error)
    : List (ComputationAction value error)
      → CachedComputation value error × List ComputationEffect
  | [] => (state, [])
  | action :: rest =>
      let next := state.step action
      let last := next.1.run rest
      (last.1, next.2 ++ last.2)

/-- The exact local optimization target. This is not a resource-coverage or native
reentrancy theorem; those obligations cannot be inferred from these invocation bounds.
-/
def LazyComputationOptimization : Prop :=
  ∀ (value error : Type) (hasAbort : Bool)
    (actions : List (ComputationAction value error)),
    let observed := (⟨none, hasAbort, false⟩ : CachedComputation value error).run actions
    observed.2.countP ComputationEffect.isEvaluation ≤ 1
    ∧ observed.2.countP ComputationEffect.isAbortCallback ≤ 1

-----------------------------------------------------------------------------------------
-- Potential accounting derives once-only invocation over the whole compatible trace
-----------------------------------------------------------------------------------------

private def CachedComputation.evaluationCredit (state : CachedComputation value error)
    : Nat :=
  if state.cache.isSome then 0 else 1

private def CachedComputation.abortCredit (state : CachedComputation value error) : Nat :=
  if state.abortAvailable then 1 else 0

private theorem CachedComputation.step_evaluationCredit
    (state : CachedComputation value error) (action : ComputationAction value error)
    : (state.step action).2.countP ComputationEffect.isEvaluation
        + (state.step action).1.evaluationCredit
      ≤ state.evaluationCredit := by
  cases action with
  | prime started =>
      simp only [CachedComputation.step, CachedComputation.prime]
      split <;> simp_all [CachedComputation.evaluationCredit, ComputationEffect.isEvaluation]
  | abort reason =>
      cases cached : state.cache with
      | none =>
          simp [CachedComputation.step, CachedComputation.abort, cached, CachedComputation.evaluationCredit]
      | some result =>
          cases result <;> cases available : state.abortAvailable <;>
            simp [CachedComputation.step, CachedComputation.abort, cached, available,
              CachedComputation.evaluationCredit, ComputationEffect.isEvaluation]
  | settle outcome =>
      cases outcome <;> cases pending : state.continuation <;>
        simp [CachedComputation.step, CachedComputation.settle, pending, CachedComputation.evaluationCredit]

private theorem CachedComputation.step_abortCredit (state : CachedComputation value error)
    (action : ComputationAction value error)
    : (state.step action).2.countP ComputationEffect.isAbortCallback
        + (state.step action).1.abortCredit
      = state.abortCredit := by
  cases action with
  | prime started =>
      simp only [CachedComputation.step, CachedComputation.prime]
      split <;> simp [CachedComputation.abortCredit, ComputationEffect.isAbortCallback]
  | abort reason =>
      cases cached : state.cache with
      | none =>
          simp [CachedComputation.step, CachedComputation.abort, cached, CachedComputation.abortCredit]
      | some result =>
          cases result <;> cases available : state.abortAvailable <;>
            simp [CachedComputation.step, CachedComputation.abort, cached, available,
              CachedComputation.abortCredit, ComputationEffect.isAbortCallback]
  | settle outcome =>
      cases outcome <;> cases pending : state.continuation <;>
        simp [CachedComputation.step, CachedComputation.settle, pending, CachedComputation.abortCredit]

/-- Any finite call/continuation history has at most one evaluation and one cleanup start.
Late fulfilment does not replenish either invocation credit.
-/
theorem CachedComputation.run_invocationBounds (state : CachedComputation value error)
    (actions : List (ComputationAction value error))
    : (state.run actions).2.countP ComputationEffect.isEvaluation ≤ state.evaluationCredit
      ∧ (state.run actions).2.countP ComputationEffect.isAbortCallback
        ≤ state.abortCredit := by
  have accounting : ∀ (state : CachedComputation value error),
      (state.run actions).2.countP ComputationEffect.isEvaluation + (state.run actions).1.evaluationCredit
        ≤ state.evaluationCredit
      ∧ (state.run actions).2.countP ComputationEffect.isAbortCallback + (state.run actions).1.abortCredit
        = state.abortCredit := by
    intro state
    induction actions generalizing state with
    | nil => simp [CachedComputation.run]
    | cons action rest ih =>
        obtain ⟨evalRest, abortRest⟩ := ih (state.step action).1
        have evalStep := state.step_evaluationCredit action
        have abortStep := state.step_abortCredit action
        simp only [CachedComputation.run, List.countP_append]
        constructor <;> omega
  obtain ⟨evaluations, cleanups⟩ := accounting state
  constructor <;> omega

theorem LazyComputationOptimization_holds : LazyComputationOptimization := by
  intro value error hasAbort actions
  obtain ⟨evaluations, cleanups⟩ := (⟨none, hasAbort, false⟩ : CachedComputation value error).run_invocationBounds actions
  refine ⟨evaluations, Nat.le_trans cleanups ?_⟩
  cases hasAbort <;> simp [CachedComputation.abortCredit]

-----------------------------------------------------------------------------------------
-- Lazy allocation and cached results, including abort/late-settlement boundaries
-----------------------------------------------------------------------------------------

/-- A cached prime/result read cannot evaluate again, regardless of the unused supplied outcome. -/
theorem CachedComputation.prime_cached (state : CachedComputation value error)
    (result : ComputationResult value error) (cached : state.cache = some result)
    (unused : ComputationResult value error)
    : state.prime unused = (state, []) := by
  simp [CachedComputation.prime, cached]

/-- Early priming and a later result read use the same cached computation, not a second executor. -/
theorem CachedComputation.prime_twice (state : CachedComputation value error)
    (first later : ComputationResult value error)
    : (state.prime first).1.prime later = ((state.prime first).1, []) := by
  unfold CachedComputation.prime
  split
  · simp_all
  · simp

/-- Cancelling an unevaluated computation suppresses later priming and all invocation sites.
The actual lazy factory must perform acquisition only inside _fn to infer zero acquisition.
-/
theorem CachedComputation.abort_before_prime (hasAbort : Bool) (reason : error)
    (started : ComputationResult value error)
    : let initial : CachedComputation value error := ⟨none, hasAbort, false⟩
      initial.run [.abort reason, .prime started]
      = (⟨some (.rejected reason), hasAbort, false⟩, []) := by
  simp [CachedComputation.run, CachedComputation.step, CachedComputation.abort, CachedComputation.prime]

/-- Cleanup of fulfilled unpublished work does not erase or replace its cached result. -/
theorem CachedComputation.abort_fulfilled (state : CachedComputation value error)
    (result : value) (cached : state.cache = some (.fulfilled result)) (reason : error)
    : (state.abort reason).1.cache = some (.fulfilled result) := by
  simp [CachedComputation.abort, cached]

/-- The callback is already disabled at its invocation label. A reentrant abort of this
updated local state therefore cannot invoke that callback again.
-/
theorem CachedComputation.abort_callback_disabled (state : CachedComputation value error)
    (reason : error) (invoked : .abortCallback ∈ (state.abort reason).2)
    : (state.abort reason).1.abortAvailable = false
      ∧ ∀ later, ((state.abort reason).1.abort later).2 = [] := by
  cases cached : state.cache with
  | none => simp [CachedComputation.abort, cached] at invoked
  | some result =>
      cases result with
      | rejected rejected => simp [CachedComputation.abort, cached] at invoked
      | pending => simp [CachedComputation.abort, cached]
      | fulfilled value => simp [CachedComputation.abort, cached]

/-- A late callback may replace abort's rejection cache, but cannot repeat evaluation or cleanup. -/
theorem CachedComputation.pending_abort_late_fulfilment (reason : error) (result : value)
    : let initial : CachedComputation value error := {}
      let observed :=
        initial.run [.prime .pending, .abort reason, .settle (.ok result), .abort reason]
      observed.1.cache = some (.fulfilled result)
      ∧ observed.2 = [.evaluate, .abortCallback] := by
  simp [CachedComputation.run, CachedComputation.step, CachedComputation.prime, CachedComputation.abort,
    CachedComputation.settle, ComputationResult.isPending]

/-- Even a fulfilled late result cannot map a batch through the actual closed reader.
The callback-to-batch function is arbitrary; admission and disposing its resources remain
separate native obligations, not consequences of this reader guard.
-/
theorem CachedComputation.late_fulfilment_closed_reader (reason : error) (result : value)
    (cursor : ResponseStreamCursor) (toBatch : value → List GraphEvent)
    : let initial : CachedComputation value error := {}
      let observed :=
        initial.run [.prime .pending, .abort reason, .settle (.ok result), .abort reason]
      observed.1.cache = some (.fulfilled result)
      ∧ observed.2 = [.evaluate, .abortCallback]
      ∧ cursor.close.1.handleBatch (toBatch result) = (none, cursor.close.1, []) := by
  obtain ⟨cached, effects⟩ := CachedComputation.pending_abort_late_fulfilment reason result
  exact ⟨cached, effects, ResponseStreamCursor.handleBatch_finished _ _
    (ResponseStreamCursor.close_finished cursor)⟩

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
