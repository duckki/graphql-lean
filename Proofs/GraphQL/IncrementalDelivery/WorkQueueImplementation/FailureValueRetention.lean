import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.BufferedLookupPreservation

/-! Failed settlements retain earlier values with any surviving contributing group. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Endpoint conservation names the surviving-owner qualification explicitly
-----------------------------------------------------------------------------------------

/-- Buffered values in `queue` publish in `published` or remain in `next` when protected.
Protection means at least one contributing group is still live in the endpoint state.
No claim about cancellation follows merely from the absence of a surviving group.
-/
def State.StoredValuesConserved (queue : State) (published : List ObjectPublication)
    (next : State)
    : Prop :=
  ∀ occurrence node value,
    queue.taskNode? occurrence = some node
    → node.value = some value
    → (∃ contributor ∈ node.task.groups,
        ∃ owner, next.groupNode? contributor.key = some owner)
    → (occurrence, value) ∈ published ∨ next.taskNode? occurrence = some node

/-- Conservation transfers from a prepared state that retains every earlier stored lookup.
Witness: apply its certificate to exactly the original node and value, without relabelling.
-/
theorem State.StoredValuesConserved.of_lookups {queue prepared next : State} {published}
    (conserved : prepared.StoredValuesConserved published next)
    (retained
      : ∀ occurrence node value,
          queue.taskNode? occurrence = some node
          → node.value = some value
          → prepared.taskNode? occurrence = some node)
    : queue.StoredValuesConserved published next := by
  intro occurrence node value found stored live
  exact conserved occurrence node value (retained occurrence node value found stored) stored live

-----------------------------------------------------------------------------------------
-- Failure folds only remove live group keys or update their existing records
-----------------------------------------------------------------------------------------

/-- A failed-owner step cannot introduce a new live group key.
Witness: absent owners do nothing, active removal filters records, and latent cache
updates preserve the exact key list. No source or queue well-formedness premise is used.
-/
theorem failureGroupStep_groupKeys_subset (errors : Nat)
    (acc : State × List WorkQueueEvent) (group : Execution.DeliveryNode)
    : ((failureGroupStep errors acc group).1.groupNodes.map
        (fun node => node.group.node.key)).Subset
        (acc.1.groupNodes.map (fun node => node.group.node.key)) := by
  obtain ⟨queue, events⟩ := acc
  unfold failureGroupStep
  dsimp only
  split
  · exact List.Subset.refl _
  · split
    · intro key member
      obtain ⟨node, retained, same⟩ := List.mem_map.mp member
      exact List.mem_map.mpr ⟨node, (List.mem_filter.mp retained).1, same⟩
    · rw [State.putGroupNode_keys]
      exact List.Subset.refl _

/-- The complete failed-owner fold introduces no live group key.
Witness: compose the per-step key subsets in actual contributor order.
-/
theorem failureGroupFold_groupKeys_subset (errors : Nat)
    (groups : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent)
    : ((groups.foldl (failureGroupStep errors) acc).1.groupNodes.map
        (fun node => node.group.node.key)).Subset
        (acc.1.groupNodes.map (fun node => node.group.node.key)) := by
  induction groups generalizing acc with
  | nil => exact List.Subset.refl _
  | cons group rest ih =>
      exact (ih _).trans (failureGroupStep_groupKeys_subset errors acc group)

-----------------------------------------------------------------------------------------
-- An endpoint live contributor protects the exact earlier task lookup
-----------------------------------------------------------------------------------------

/-- A failure fold preserves each task with a contributor still live at its endpoint.
Witness: propagate endpoint liveness backward through key subsets; each active removal
then keeps the task's exact first lookup. Latent error caching does not touch task nodes.
-/
theorem failureGroupFold_lookup_survivingOwner (errors : Nat)
    (groups : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent)
    {occurrence node} (found : acc.1.taskNode? occurrence = some node)
    {contributor : Execution.DeliveryNode} (contributes : contributor ∈ node.task.groups)
    {owner : GroupNode}
    (live : owner ∈ (groups.foldl (failureGroupStep errors) acc).1.groupNodes)
    (same : owner.group.node.key = contributor.key)
    : (groups.foldl (failureGroupStep errors) acc).1.taskNode? occurrence
      = some node := by
  induction groups generalizing acc with
  | nil => exact found
  | cons group rest ih =>
      apply ih _ ?_ live
      have atStep := failureGroupFold_groupKeys_subset errors rest
        (failureGroupStep errors acc group) (List.mem_map.mpr ⟨owner, live, same⟩)
      obtain ⟨survivor, survives, key⟩ := List.mem_map.mp atStep
      obtain ⟨queue, events⟩ := acc
      unfold failureGroupStep at survives ⊢
      dsimp only at survives ⊢
      cases lookup : queue.groupNode? group.key with
      | none => simpa only [lookup] using found
      | some closing =>
          simp only [lookup] at survives ⊢
          cases active : queue.rootGroups.contains group.key with
          | false =>
              simpa only [active, Bool.false_eq_true, ↓reduceIte, State.putGroupNode,
                State.taskNode?]
                using found
          | true =>
              simp only [active, ↓reduceIte] at survives ⊢
              exact State.removeGroup_lookup_survivingOwner found _ contributes survives key

/-- A failed task cannot discard another task while one of its contributors survives.
Witness: distinct-occurrence removal preserves the lookup before the failed-owner fold;
the fold's endpoint liveness protects it through every subsequent group removal.
-/
theorem State.taskFailure_lookup_survivingOwner {queue : State} {occurrence node}
    (found : queue.taskNode? occurrence = some node) (failed : Occurrence) (errors : Nat)
    (different : occurrence ≠ failed)
    {contributor : Execution.DeliveryNode} (contributes : contributor ∈ node.task.groups)
    {owner : GroupNode} (live : owner ∈ (queue.taskFailure failed errors).1.groupNodes)
    (same : owner.group.node.key = contributor.key)
    : (queue.taskFailure failed errors).1.taskNode? occurrence = some node := by
  have retained := (queue.removeTask_lookup_other different).trans found
  unfold State.taskFailure at live ⊢
  cases lookup : queue.taskNode? failed with
  | none => simpa only [lookup] using found
  | some failing =>
      simp only [lookup] at live ⊢
      cases healthy : queue.taskHasHealthyOwner failing.task with
      | false =>
          simpa only [healthy, Bool.not_false, ↓reduceIte] using retained
      | true =>
          simp only [healthy, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at live ⊢
          exact failureGroupFold_lookup_survivingOwner errors _ _ retained contributes live same

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
