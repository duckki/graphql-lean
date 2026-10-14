import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ResourceOwnership

/-! Construct queue-owned cleanup observations from an actual ordered target list.
Producer-owned suffixes and asynchronous settlement remain separate obligations.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement

/-- One compatible ownership history connects acquisition/adoption and subsequent disposal. -/
theorem ResourceReplay.append {before first middle last after}
    (earlier : ResourceReplay before first middle)
    (suffix : ResourceReplay middle last after)
    : ResourceReplay before (first ++ last) after := by
  induction earlier with
  | nil => exact suffix
  | cons step rest ih => exact .cons step (ih suffix)

-----------------------------------------------------------------------------------------
-- Cleanup observations preserve the independently supplied acquired-resource inventory
-----------------------------------------------------------------------------------------

/-- Observe requests only for leases currently owned by the queue. Previously requested,
released, unacquired, and producer-owned identities do not acquire another ghost request.
The targets must come from the actual transition; this does not manufacture acquisitions.
-/
def ResourceState.requestQueueCleanup (resources : ResourceState)
    : List CleanupTarget → ResourceState × List ResourceAction
  | [] => (resources, [])
  | target :: rest =>
      if resources target = .owned .queue then
        let next := resources.set target (.cleanupRequested .queue)
        let (final, actions) := next.requestQueueCleanup rest
        (final, .requestCleanup target :: actions)
      else
        resources.requestQueueCleanup rest

/-- The observation constructs one legal history rather than assuming a resource replay. -/
theorem ResourceState.requestQueueCleanup_replay (resources : ResourceState)
    (targets : List CleanupTarget)
    : ResourceReplay resources (resources.requestQueueCleanup targets).2
        (resources.requestQueueCleanup targets).1 := by
  induction targets generalizing resources with
  | nil => exact .nil _
  | cons target rest ih =>
      simp only [ResourceState.requestQueueCleanup]
      split
      · exact .cons (.request _ _ .queue (by assumption)) (ih _)
      · exact ih _

/-- Every constructed request is licensed by one of the supplied cleanup identities. -/
theorem ResourceState.requestQueueCleanup_actions (resources : ResourceState)
    (targets : List CleanupTarget)
    : ∀ action ∈ (resources.requestQueueCleanup targets).2,
        ∃ target ∈ targets, action = .requestCleanup target := by
  induction targets generalizing resources with
  | nil => simp [ResourceState.requestQueueCleanup]
  | cons target rest ih =>
      simp only [ResourceState.requestQueueCleanup]
      split
      · intro action member
        rcases List.mem_cons.mp member with same | later
        · exact ⟨target, List.mem_cons_self, same⟩
        · obtain ⟨other, listed, same⟩ := ih _ action later
          exact ⟨other, List.mem_cons_of_mem _ listed, same⟩
      · intro action member
        obtain ⟨other, listed, same⟩ := ih _ action member
        exact ⟨other, List.mem_cons_of_mem _ listed, same⟩

/-- No operation changes a lease outside queue ownership, including producer-owned suffixes. -/
theorem ResourceState.requestQueueCleanup_foreign (resources : ResourceState)
    (targets : List CleanupTarget) (target : CleanupTarget)
    (foreign : resources target ≠ .owned .queue)
    : (resources.requestQueueCleanup targets).1 target = resources target := by
  induction targets generalizing resources with
  | nil => rfl
  | cons head rest ih =>
      simp only [ResourceState.requestQueueCleanup]
      split
      · rename_i owned
        have different : target ≠ head := fun same => foreign (same ▸ owned)
        have unchanged : resources.set head (.cleanupRequested .queue) target
            = resources target := by simp [ResourceState.set, different]
        rw [ih _ (by rwa [unchanged]), unchanged]
      · exact ih _ foreign

/-- Unlisted targets retain their original lease, not just their acquisition status. -/
theorem ResourceState.requestQueueCleanup_unlisted (resources : ResourceState)
    (targets : List CleanupTarget) (target : CleanupTarget) (absent : target ∉ targets)
    : (resources.requestQueueCleanup targets).1 target = resources target := by
  induction targets generalizing resources with
  | nil => rfl
  | cons head rest ih =>
      have different : target ≠ head := fun same => absent (by simp [same])
      have missing : target ∉ rest := fun member => absent (List.mem_cons_of_mem _ member)
      simp only [ResourceState.requestQueueCleanup]
      split
      · rw [ih _ missing]
        simp [ResourceState.set, different]
      · exact ih _ missing

/-- Every listed queue-owned lease becomes requested, never falsely released. -/
theorem ResourceState.requestQueueCleanup_owned (resources : ResourceState)
    (targets : List CleanupTarget) (target : CleanupTarget) (listed : target ∈ targets)
    (owned : resources target = .owned .queue)
    : (resources.requestQueueCleanup targets).1 target = .cleanupRequested .queue := by
  induction targets generalizing resources with
  | nil => cases listed
  | cons head rest ih =>
      simp only [ResourceState.requestQueueCleanup]
      split
      · rename_i headOwned
        by_cases same : target = head
        · subst target
          rw [ResourceState.requestQueueCleanup_foreign]
          · simp [ResourceState.set]
          · simp [ResourceState.set]
        · apply ih _ ((List.mem_cons.mp listed).resolve_left same)
          simpa [ResourceState.set, same] using owned
      · rename_i headForeign
        have different : target ≠ head := fun same => headForeign (same ▸ owned)
        exact ih _ ((List.mem_cons.mp listed).resolve_left different) owned

/-- A still-owned lease was neither changed nor among the cleanup targets. -/
theorem ResourceState.requestQueueCleanup_still_owned (resources : ResourceState)
    (targets : List CleanupTarget) (target : CleanupTarget)
    (owned : (resources.requestQueueCleanup targets).1 target = .owned .queue)
    : resources target = .owned .queue ∧ target ∉ targets := by
  have before : resources target = .owned .queue := by
    by_cases initial : resources target = .owned .queue
    · exact initial
    · rw [resources.requestQueueCleanup_foreign targets target initial] at owned
      exact False.elim (initial owned)
  refine ⟨before, ?_⟩
  intro listed
  rw [resources.requestQueueCleanup_owned targets target listed before] at owned
  contradiction

-----------------------------------------------------------------------------------------
-- Explicit stop constructs disposal evidence and leaves no covered queue-owned lease
-----------------------------------------------------------------------------------------

/-- Use the actual stop targets; leases are independent evidence, not inferred from records. -/
def ResourceState.observeStop (resources : ResourceState) (queue : State)
    : ResourceState × List ResourceAction :=
  resources.requestQueueCleanup (queue.cancel.2.filterMap HostEffect.cleanupStart?)

/-- Stop requests construct a legal ownership trace and preserve every acquired obligation. -/
theorem ResourceState.observeStop_replay (resources : ResourceState) (queue : State)
    : ResourceReplay resources (resources.observeStop queue).2
        (resources.observeStop queue).1 :=
  resources.requestQueueCleanup_replay _

/-- Covered stop has no queue-owned remainder. Coverage itself is still a replay obligation;
this theorem supplies the previously implicit legal disposal history, not that invariant.
-/
theorem ResourceState.observeStop_no_owned (resources : ResourceState) (queue : State)
    (running : queue.stopped = false) (coverage : StopCoverage queue resources)
    (target : CleanupTarget)
    : (resources.observeStop queue).1 target ≠ .owned .queue := by
  intro owned
  obtain ⟨before, absent⟩ := resources.requestQueueCleanup_still_owned _ target owned
  exact absent (cancel_requests_owned queue resources running coverage target before)

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
