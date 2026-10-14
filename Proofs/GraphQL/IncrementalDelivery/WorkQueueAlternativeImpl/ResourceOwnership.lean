import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.GraphEffectProjection

/-! Ghost ownership for acquired task/source cleanup obligations. Cleanup requested is
not cleanup settled. No production resource ledger or stronger source law is introduced.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open GraphQL.IncrementalDelivery.WorkQueueSemantics (Occurrence)

inductive ResourceOwner where
  | producer (occurrence : Occurrence)
  | queue
deriving DecidableEq, Repr

inductive ResourceLease where
  | unacquired
  | owned (owner : ResourceOwner)
  | cleanupRequested (owner : ResourceOwner)
  | released
deriving DecidableEq, Repr

/-- One ghost lease per cleanup identity; this map is evidence, not a runtime container. -/
abbrev ResourceState := CleanupTarget → ResourceLease

def ResourceState.empty : ResourceState := fun _ => .unacquired

def ResourceState.set (state : ResourceState) (target : CleanupTarget)
    (lease : ResourceLease)
    : ResourceState :=
  fun other => if other = target then lease else state other

/-- Whole-work handoff transfers only that producer's existing leases. It neither acquires
resources nor transfers foreign ownership. Registration/reachability is a separate leaf.
-/
def ResourceState.adopt (state : ResourceState) (producer : Occurrence)
    (inventory : List CleanupTarget)
    : ResourceState :=
  fun target =>
    if target ∈ inventory ∧ state target = .owned (.producer producer) then
      .owned .queue
    else
      state target

inductive ResourceAction where
  | acquire (target : CleanupTarget) (owner : ResourceOwner)
  | adopt (producer : Occurrence) (inventory : List CleanupTarget)
  | requestCleanup (target : CleanupTarget)
  | settleCleanup (target : CleanupTarget)
  | finishNormally (target : CleanupTarget)
deriving Repr

/-- Legal ownership observations. A native audit must construct these transitions from
the actual acquisition, adoption, cleanup and completion sites; they are not host axioms.
-/
inductive ResourceStep : ResourceState → ResourceAction → ResourceState → Prop where
  | acquire (state target owner) (fresh : state target = .unacquired)
    : ResourceStep state (.acquire target owner) (state.set target (.owned owner))
  | adopt (state producer inventory)
    : ResourceStep state (.adopt producer inventory) (state.adopt producer inventory)
  | request (state target owner) (owned : state target = .owned owner)
    : ResourceStep state (.requestCleanup target)
        (state.set target (.cleanupRequested owner))
  | settle (state target owner) (requested : state target = .cleanupRequested owner)
    : ResourceStep state (.settleCleanup target) (state.set target .released)
  | finish (state target owner) (owned : state target = .owned owner)
    : ResourceStep state (.finishNormally target) (state.set target .released)

inductive ResourceReplay
    : ResourceState → List ResourceAction → ResourceState → Prop where
  | nil (state) : ResourceReplay state [] state
  | cons (step : ResourceStep before action middle)
    (rest : ResourceReplay middle actions after)
    : ResourceReplay before (action :: actions) after

/-- No legal transition forgets an acquired obligation, including cleanup awaiting settlement. -/
theorem ResourceStep.never_forgets {before action after}
    (step : ResourceStep before action after) (target : CleanupTarget)
    (acquired : before target ≠ .unacquired)
    : after target ≠ .unacquired := by
  cases step <;> simp only [ResourceState.set, ResourceState.adopt]
  all_goals split
  all_goals first | exact acquired | simp

theorem ResourceReplay.never_forgets {before actions after}
    (replay : ResourceReplay before actions after) (target : CleanupTarget)
    (acquired : before target ≠ .unacquired)
    : after target ≠ .unacquired := by
  induction replay with
  | nil => exact acquired
  | cons step rest ih => exact ih (step.never_forgets target acquired)

/-- An acquisition anywhere in this same history remains accounted for at its endpoint.
Unlike preservation from the initial state, this is nonvacuous for histories starting empty.
Requested, producer-owned and released leases all remain distinct acquired identities.
-/
theorem ResourceReplay.acquisition_accounted {before actions after target owner}
    (replay : ResourceReplay before actions after)
    (acquired : ResourceAction.acquire target owner ∈ actions)
    : after target ≠ .unacquired := by
  induction replay with
  | nil => cases acquired
  | cons step rest ih =>
      rcases List.mem_cons.mp acquired with same | later
      · subst same
        cases step
        apply rest.never_forgets target
        simp [ResourceState.set]
      · exact ih later

/-- Complete adoption preserves the identity and leaves one queue-owned lease. -/
theorem ResourceState.adopt_owned (state : ResourceState) (producer : Occurrence)
    (inventory : List CleanupTarget) (target : CleanupTarget)
    (listed : target ∈ inventory) (owned : state target = .owned (.producer producer))
    : state.adopt producer inventory target = .owned .queue := by
  simp [ResourceState.adopt, listed, owned]

/-- Handoff cannot steal another producer's lease or hide requested cleanup. -/
theorem ResourceState.adopt_unchanged (state : ResourceState) (producer : Occurrence)
    (inventory : List CleanupTarget) (target : CleanupTarget)
    (foreign : state target ≠ .owned (.producer producer))
    : state.adopt producer inventory target = state target := by
  simp [ResourceState.adopt, foreign]

/-- Already requested/released cleanup cannot be requested again by a legal transition. -/
theorem ResourceStep.request_requires_owned {before after target}
    (step : ResourceStep before (.requestCleanup target) after)
    : ∃ owner, before target = .owned owner := by
  cases step
  exact ⟨_, by assumption⟩

/-- Settlement is possible only after a request, and does not turn into semantic work success. -/
theorem ResourceStep.settle_requires_request {before after target}
    (step : ResourceStep before (.settleCleanup target) after)
    : ∃ owner, before target = .cleanupRequested owner := by
  cases step
  exact ⟨_, by assumption⟩

/-- A queue-owned unfinished resource must be represented at the actual stop traversal.
This is an audit obligation to derive, never a WorkQueue source assumption.
-/
def StopCoverage (queue : State) (resources : ResourceState) : Prop :=
  ∀ target, resources target = .owned .queue → target ∈ queue.cleanupTargets

/-- Once coverage is established, the existing stop protocol requests every owned target.
This checked reduction alone does not establish coverage at any runtime boundary.
-/
theorem cancel_requests_owned (queue : State) (resources : ResourceState)
    (running : queue.stopped = false) (coverage : StopCoverage queue resources)
    (target : CleanupTarget) (owned : resources target = .owned .queue)
    : target ∈ queue.cancel.2.filterMap HostEffect.cleanupStart? := by
  have member := coverage target owned
  rw [State.cancel_effects]
  simp only [running, Bool.false_eq_true, ↓reduceIte]
  apply List.mem_filterMap.mpr
  cases target with
  | task occurrence =>
      refine ⟨.abortTask occurrence, ?_, rfl⟩
      exact List.mem_flatMap.mpr ⟨.task occurrence, member, by simp⟩
  | stream key =>
      refine ⟨.cancelSource key, ?_, rfl⟩
      exact List.mem_flatMap.mpr ⟨.stream key, member, by simp⟩

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
