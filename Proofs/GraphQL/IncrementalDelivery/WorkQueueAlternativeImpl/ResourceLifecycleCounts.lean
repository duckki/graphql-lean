import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ResourcePrefixConstruction

/-! Per-identity lifecycle bounds for one legal acquired-resource history. These count
independently observed acquisitions, cleanup requests and actual releases, not public host
labels, native callbacks or runtime operations. They assume no inventory completeness.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement

-----------------------------------------------------------------------------------------
-- Each acquired identity can cross each lifecycle milestone only once
-----------------------------------------------------------------------------------------

/-- Proof-side milestones of one cleanup identity; adoption is an ownership transfer,
not another acquisition or release. Normal completion and settled cleanup both release it.
-/
inductive ResourceMilestone where
  | acquisition
  | cleanupRequest
  | release

/-- Count only the specified identity's independently observed lifecycle actions. -/
def ResourceMilestone.matches (milestone : ResourceMilestone) (target : CleanupTarget)
    : ResourceAction → Bool
  | .acquire other _ =>
      match milestone with
      | .acquisition => other == target
      | _ => false
  | .requestCleanup other =>
      match milestone with
      | .cleanupRequest => other == target
      | _ => false
  | .settleCleanup other | .finishNormally other =>
      match milestone with
      | .release => other == target
      | _ => false
  | .adopt _ _ => false

private def ResourceMilestone.remaining (milestone : ResourceMilestone)
    : ResourceLease → Nat
  | .unacquired => 1
  | .owned _ =>
      match milestone with
      | .acquisition => 0
      | _ => 1
  | .cleanupRequested _ =>
      match milestone with
      | .release => 1
      | _ => 0
  | .released => 0

private theorem ResourceMilestone.remaining_le_one (milestone : ResourceMilestone)
    (lease : ResourceLease)
    : milestone.remaining lease ≤ 1 := by
  cases lease <;> cases milestone <;> simp [ResourceMilestone.remaining]

private theorem ResourceStep.milestoneAccounting {before action after}
    (step : ResourceStep before action after) (milestone : ResourceMilestone)
    (target : CleanupTarget)
    : (if milestone.matches target action then 1 else 0)
        + milestone.remaining (after target)
      ≤ milestone.remaining (before target) := by
  cases step with
  | acquire other owner fresh =>
      by_cases same : other = target
      · subst target
        cases milestone <;> simp [ResourceMilestone.matches, ResourceMilestone.remaining,
          ResourceState.set, fresh]
      · have different := Ne.symm same
        cases milestone <;> simp [ResourceMilestone.matches, ResourceMilestone.remaining,
          ResourceState.set, same, different]
  | adopt producer inventory =>
      simp only [ResourceMilestone.matches, Bool.false_eq_true, ↓reduceIte, Nat.zero_add,
        ResourceState.adopt]
      split
      · rename_i transferred
        rw [transferred.2]
        cases milestone <;> simp [ResourceMilestone.remaining]
      · exact Nat.le_refl _
  | request other owner owned =>
      by_cases same : other = target
      · subst target
        cases milestone <;> simp [ResourceMilestone.matches, ResourceMilestone.remaining,
          ResourceState.set, owned]
      · have different := Ne.symm same
        cases milestone <;> simp [ResourceMilestone.matches, ResourceMilestone.remaining,
          ResourceState.set, same, different]
  | settle other owner requested =>
      by_cases same : other = target
      · subst target
        cases milestone <;> simp [ResourceMilestone.matches, ResourceMilestone.remaining,
          ResourceState.set, requested]
      · have different := Ne.symm same
        cases milestone <;> simp [ResourceMilestone.matches, ResourceMilestone.remaining,
          ResourceState.set, same, different]
  | finish other owner owned =>
      by_cases same : other = target
      · subst target
        cases milestone <;> simp [ResourceMilestone.matches, ResourceMilestone.remaining,
          ResourceState.set, owned]
      · have different := Ne.symm same
        cases milestone <;> simp [ResourceMilestone.matches, ResourceMilestone.remaining,
          ResourceState.set, same, different]

private theorem ResourceReplay.milestoneAccounting {before actions after}
    (replay : ResourceReplay before actions after) (milestone : ResourceMilestone)
    (target : CleanupTarget)
    : actions.countP (milestone.matches target) + milestone.remaining (after target)
      ≤ milestone.remaining (before target) := by
  induction replay with
  | nil => simp
  | cons step rest ih =>
      have one := step.milestoneAccounting milestone target
      rw [List.countP_cons]
      omega

/-- Each identity is acquired at most once, requested at most once, and released at
most once across a whole legal history. A request need not settle in any finite prefix.
-/
theorem ResourceReplay.milestoneCount_le_one {before actions after}
    (replay : ResourceReplay before actions after) (milestone : ResourceMilestone)
    (target : CleanupTarget)
    : actions.countP (milestone.matches target) ≤ 1 := by
  have bound := replay.milestoneAccounting milestone target
  have capacity := milestone.remaining_le_one (before target)
  omega

-----------------------------------------------------------------------------------------
-- Counts concern the same constructed dispatch, FIFO and explicit-stop histories
-----------------------------------------------------------------------------------------

/-- Independent acquisition and inter-input callbacks are included in the same history. -/
theorem ResourcePrefixConstruction.milestoneCount_le_one {work inputs resources actions}
    (built : ResourcePrefixConstruction work inputs resources actions)
    (generated : ReferenceWorkQueue.ExecutedWork work) (milestone : ResourceMilestone)
    (target : CleanupTarget)
    : actions.countP (milestone.matches target) ≤ 1 :=
  (built.invariants generated).1.milestoneCount_le_one milestone target

/-- Appending the actual stop observations cannot duplicate a prior lifecycle milestone.
This is not an assertion that every producer-owned suffix is disposed or every callback
is observed completely by a native bridge.
-/
theorem ResourcePrefixConstruction.stop_milestoneCount_le_one
    {work inputs resources actions}
    (built : ResourcePrefixConstruction work inputs resources actions)
    (generated : ReferenceWorkQueue.ExecutedWork work) (milestone : ResourceMilestone)
    (target : CleanupTarget)
    : (actions
        ++ (resources.observeStop
              ((State.initialize work).runNormalized inputs).1).2).countP
        (milestone.matches target)
      ≤ 1 :=
  ((built.invariants generated).1.append
    (resources.observeStop_replay _)).milestoneCount_le_one
    milestone target

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
