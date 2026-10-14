import GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl

/-! Finite audit observations of the cleanup tracker and its two completion boundaries.
An empty tracked set does not prove absence of untracked work. Constructing a complete
tracking witness from native callbacks is an open obligation, not a source assumption.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement

structure CleanupTracker where
  pending : List Nat := []
  responseFinished : Bool := false
  asyncWorkFinished : Bool := false
deriving Repr

def CleanupTracker.Valid (tracker : CleanupTracker) : Prop :=
  tracker.pending.Nodup
  ∧ (tracker.asyncWorkFinished = true
      → tracker.responseFinished = true ∧ tracker.pending = [])

inductive CleanupAction where
  | register (token : Nat)
  | settle (token : Nat)
  | responseFinished
  | asyncWorkFinished
deriving Repr

def CleanupAction.isResponseFinished : CleanupAction → Bool
  | .responseFinished => true
  | _ => false

def CleanupAction.isAsyncWorkFinished : CleanupAction → Bool
  | .asyncWorkFinished => true
  | _ => false

/-- Late registrations may follow response closure, but not completed async notification.
This audit protocol is not implied by an empty pending-effect tracker.
-/
inductive CleanupStep : CleanupTracker → CleanupAction → CleanupTracker → Prop where
  | register (tracker token) (fresh : token ∉ tracker.pending)
    (tracking : tracker.asyncWorkFinished = false)
    : CleanupStep tracker (.register token)
        { tracker with pending := token :: tracker.pending }
  | settle (tracker token) (pending : token ∈ tracker.pending)
    : CleanupStep tracker (.settle token)
        { tracker with pending := tracker.pending.filter (· != token) }
  | responseFinished (tracker) (fresh : tracker.responseFinished = false)
    : CleanupStep tracker .responseFinished { tracker with responseFinished := true }
  | asyncWorkFinished (tracker) (response : tracker.responseFinished = true)
    (settled : tracker.pending = []) (fresh : tracker.asyncWorkFinished = false)
    : CleanupStep tracker .asyncWorkFinished { tracker with asyncWorkFinished := true }

inductive CleanupReplay
    : CleanupTracker → List CleanupAction → CleanupTracker → Prop where
  | nil (tracker) : CleanupReplay tracker [] tracker
  | cons (step : CleanupStep before action middle)
    (rest : CleanupReplay middle actions after)
    : CleanupReplay before (action :: actions) after

theorem CleanupTracker.empty_valid : ({} : CleanupTracker).Valid := by
  simp [CleanupTracker.Valid]

theorem CleanupStep.preserves_valid {before action after}
    (step : CleanupStep before action after) (valid : before.Valid)
    : after.Valid := by
  cases step with
  | register token fresh tracking =>
      refine ⟨List.nodup_cons.mpr ⟨fresh, valid.1⟩, ?_⟩
      simp [tracking]
  | settle token pending =>
      refine ⟨List.Pairwise.filter _ valid.1, ?_⟩
      intro notified
      obtain ⟨response, settled⟩ := valid.2 notified
      exact ⟨response, by simp [settled]⟩
  | responseFinished fresh =>
      exact ⟨valid.1, fun notified => ⟨rfl, (valid.2 notified).2⟩⟩
  | asyncWorkFinished response settled fresh =>
      exact ⟨valid.1, fun _ => ⟨response, settled⟩⟩

theorem CleanupReplay.preserves_valid {before actions after}
    (replay : CleanupReplay before actions after) (valid : before.Valid)
    : after.Valid := by
  induction replay with
  | nil => exact valid
  | cons step rest ih => exact ih (step.preserves_valid valid)

theorem CleanupStep.responseFinishCount {before action after}
    (step : CleanupStep before action after)
    : (if action.isResponseFinished then 1 else 0)
        + (if before.responseFinished then 1 else 0)
      = if after.responseFinished then 1 else 0 := by
  cases step <;> simp_all [CleanupAction.isResponseFinished]

theorem CleanupStep.asyncFinishCount {before action after}
    (step : CleanupStep before action after)
    : (if action.isAsyncWorkFinished then 1 else 0)
        + (if before.asyncWorkFinished then 1 else 0)
      = if after.asyncWorkFinished then 1 else 0 := by
  cases step <;> simp_all [CleanupAction.isAsyncWorkFinished]

theorem CleanupReplay.responseFinishCount {before actions after}
    (replay : CleanupReplay before actions after)
    : actions.countP CleanupAction.isResponseFinished
        + (if before.responseFinished then 1 else 0)
      = if after.responseFinished then 1 else 0 := by
  induction replay with
  | nil => exact Nat.zero_add _
  | cons step rest ih =>
      have one := step.responseFinishCount
      rw [List.countP_cons]
      omega

theorem CleanupReplay.asyncFinishCount {before actions after}
    (replay : CleanupReplay before actions after)
    : actions.countP CleanupAction.isAsyncWorkFinished
        + (if before.asyncWorkFinished then 1 else 0)
      = if after.asyncWorkFinished then 1 else 0 := by
  induction replay with
  | nil => exact Nat.zero_add _
  | cons step rest ih =>
      have one := step.asyncFinishCount
      rw [List.countP_cons]
      omega

theorem CleanupReplay.responseFinishCount_le_one {before actions after}
    (replay : CleanupReplay before actions after)
    : actions.countP CleanupAction.isResponseFinished ≤ 1 := by
  have count := replay.responseFinishCount
  split at count <;> split at count <;> omega

theorem CleanupReplay.asyncFinishCount_le_one {before actions after}
    (replay : CleanupReplay before actions after)
    : actions.countP CleanupAction.isAsyncWorkFinished ≤ 1 := by
  have count := replay.asyncFinishCount
  split at count <;> split at count <;> omega

theorem CleanupStep.asyncFinish_requires_settlement {before after}
    (step : CleanupStep before .asyncWorkFinished after)
    : before.responseFinished = true ∧ before.pending = [] := by
  cases step
  exact ⟨by assumption, by assumption⟩

/-- Response completion can be prompt even with cleanup pending; it is not quiescence. -/
theorem CleanupStep.responseFinish_keeps_pending {before after}
    (step : CleanupStep before .responseFinished after)
    : after.pending = before.pending := by
  cases step
  rfl

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
