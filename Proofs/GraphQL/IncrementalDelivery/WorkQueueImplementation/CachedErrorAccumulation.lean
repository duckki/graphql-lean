import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureDebt
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CachedFailureOutput

/-! Exact once-per-contributor accumulation in the retained-failure owner fold. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- The actual failure fold updates each surviving owner's cache exactly once
-----------------------------------------------------------------------------------------

/-- Every surviving cache is unchanged or incremented once by the failed task's count.
Witness: induction through distinct contributor keys. Removal only filters nodes; a
latent update adds the count once, and the remaining keys cannot update that key again.
No claim is made that a group survives ancestor cancellation.
-/
theorem failureGroupFold_cachedErrors (errors : Nat)
    (groups : List Execution.DeliveryNode)
    (unique : (groups.map Execution.DeliveryNode.key).Nodup)
    (acc : State × List WorkQueueEvent) {node : GroupNode}
    (member : node ∈ (groups.foldl (failureGroupStep errors) acc).1.groupNodes)
    : ∃ old ∈ acc.1.groupNodes,
        old.group.node.key = node.group.node.key
        ∧ node.failure
          = if node.group.node.key ∈ groups.map Execution.DeliveryNode.key then
              some (old.failure.getD 0 + errors)
            else
              old.failure := by
  induction groups generalizing acc with
  | nil => exact ⟨node, member, rfl, by simp⟩
  | cons group rest ih =>
      obtain ⟨fresh, uniqueTail⟩ := List.nodup_cons.mp unique
      obtain ⟨mid, live, key, count⟩ := ih uniqueTail (failureGroupStep errors acc group) member
      obtain ⟨current, events⟩ := acc
      dsimp only [failureGroupStep] at live
      cases found : current.groupNode? group.key with
      | none =>
          rw [found] at live
          have different : mid.group.node.key ≠ group.key := by
            have missing := List.find?_eq_none.mp found mid live
            simpa using missing
          refine ⟨mid, live, key, ?_⟩
          simpa [List.map_cons, List.mem_cons, ← key, different] using count
      | some owner =>
          rw [found] at live
          dsimp only at live
          have ownerKey := current.groupNode?_key found
          split at live
          · have missing := current.removeGroup_ownGroupAbsent group.key
            have different : mid.group.node.key ≠ group.key := by
              have live' : mid ∈ (current.removeGroup group.key).groupNodes := by
                simpa only [State.finishGroupFailure, ownerKey] using live
              have noKey := List.find?_eq_none.mp missing mid live'
              simpa using noKey
            refine ⟨mid, (List.mem_filter.mp live).1, key, ?_⟩
            simpa [List.map_cons, List.mem_cons, ← key, different] using count
          · obtain ⟨old, oldMember, mapped⟩ := List.mem_map.mp live
            split at mapped
            · subst mid
              have nodeKey : node.group.node.key = group.key := key.symm.trans ownerKey
              have notLater : node.group.node.key ∉ rest.map Execution.DeliveryNode.key := by
                simpa only [nodeKey] using fresh
              refine ⟨owner, List.mem_of_find?_eq_some found, key, ?_⟩
              simp only [notLater, ↓reduceIte] at count
              simpa [nodeKey] using count
            · rename_i different
              subst mid
              have notHead : old.group.node.key ≠ group.key := by
                simpa [ownerKey] using different
              refine ⟨old, oldMember, key, ?_⟩
              simpa [List.map_cons, List.mem_cons, ← key, notHead] using count

/-- A failure increments surviving contributor caches only if a healthy owner survives.
Witness: cancelled-task removal retains caches; the active distinct-key fold adds once.
The source's contributor uniqueness is sufficient; no output-admission premise is used.
-/
theorem State.taskFailure_cachedErrors (queue : State) (occurrence : Occurrence)
    (errors : Nat) (task : TaskNode) (found : queue.taskNode? occurrence = some task)
    (unique : (task.task.groups.map Execution.DeliveryNode.key).Nodup) {node : GroupNode}
    (member : node ∈ (queue.taskFailure occurrence errors).1.groupNodes)
    : ∃ old ∈ queue.groupNodes,
        old.group.node.key = node.group.node.key
        ∧ node.failure
          = if queue.taskHasHealthyOwner task.task = true
                ∧ node.group.node.key
                  ∈ task.task.groups.map Execution.DeliveryNode.key then
              some (old.failure.getD 0 + errors)
            else
              old.failure := by
  rw [queue.taskFailure_eq occurrence errors task found] at member
  split at member
  · rename_i inactive
    have cancelled : queue.taskHasHealthyOwner task.task = false := by simpa using inactive
    obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
    exact ⟨old, oldMember, rfl, by simp [cancelled]⟩
  · rename_i active
    have healthy : queue.taskHasHealthyOwner task.task = true := by simpa using active
    obtain ⟨mid, live, key, count⟩ := failureGroupFold_cachedErrors errors task.task.groups
      unique (queue.removeTask occurrence, []) member
    obtain ⟨old, oldMember, same⟩ := List.mem_map.mp live
    subst mid
    exact ⟨old, oldMember, key, by simpa only [healthy, true_and] using count⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
