import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureValueRetention

/-! Preparing new work and failed settlements preserve uncancelled buffered owners. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Reuse the same publication labels across lookup-preserving preparation
-----------------------------------------------------------------------------------------

/-- Preparation that retains old buffered lookups and refs preserves owner conservation.
Witness: apply the prepared certificate to the same task node, value, and contributor.
-/
theorem State.StoredOwnersConserved.of_lookups {queue prepared next : State} {published}
    (conserved : prepared.StoredOwnersConserved published next)
    (retained
      : ∀ occurrence node value,
          queue.taskNode? occurrence = some node
          → node.value = some value
          → prepared.taskNode? occurrence = some node)
    (refs : queue.GroupRefsIncluded prepared)
    : queue.StoredOwnersConserved published next := by
  intro occurrence node value found stored ref contributes present uncancelled
  exact conserved occurrence node value (retained occurrence node value found stored) stored
    ref contributes (refs ref present) uncancelled

/-- Empty-output conservation can use any supplied publication ledger unchanged.
Witness: no label can be in the empty list, so every case uses exact retained state.
-/
theorem State.StoredOwnersConserved.of_empty {queue next : State}
    (conserved : queue.StoredOwnersConserved [] next) (published : List ObjectPublication)
    : queue.StoredOwnersConserved published next := by
  intro occurrence node value found stored ref contributes present uncancelled
  exact Or.inr
    ((conserved occurrence node value found stored ref contributes present
        uncancelled).resolve_left
      (by simp))

/-- Root child-work integration keeps every earlier buffered lookup and owner.
Witness: no producer attachment can replace the old node, and integration only adds refs.
-/
theorem State.maybeIntegrateWork_storedOwnersConserved (queue : State) (work : Work)
    : queue.StoredOwnersConserved [] (queue.maybeIntegrateWork work).1 := by
  intro occurrence node value found stored ref contributes present uncancelled
  exact Or.inr ⟨State.maybeIntegrateWork_lookup_other found work,
    queue.maybeIntegrateWork_includesRefs work none ref present⟩

-----------------------------------------------------------------------------------------
-- Failure processing cannot erase a group without retaining its cancellation ref
-----------------------------------------------------------------------------------------

/-- A removal retains each previously live group not in its final cancellation history.
Witness: every filtered-out ref is appended to that history by the same removal.
-/
theorem State.removeGroup_uncancelled_present (queue : State) (root : Nat) {ref : NodeRef}
    (present : ref ∈ queue.groupNodes.map (fun owner => owner.group.node.ref))
    (uncancelled : ref ∉ (queue.removeGroup root).cancelledGroups)
    : ref
      ∈ (queue.removeGroup root).groupNodes.map (fun owner => owner.group.node.ref) := by
  obtain ⟨node, live, same⟩ := List.mem_map.mp present
  refine List.mem_map.mpr ⟨node, List.mem_filter.mpr ⟨live, ?_⟩, same⟩
  have absent : ref ∉ State.removeGroup.collect (queue.groupNodes.length + 1)
      queue [root] [] := fun member => uncancelled (List.mem_append_right _ member)
  simpa [same] using absent

/-- One failed-owner step never forgets cancellation refs.
Witness: active cleanup appends refs; absent owners and latent error caching keep them.
-/
theorem failureGroupStep_cancelledGroups_subset (errors : Nat)
    (acc : State × List WorkQueueEvent) (group : Execution.DeliveryNode)
    : acc.1.cancelledGroups.Subset
        (failureGroupStep errors acc group).1.cancelledGroups := by
  obtain ⟨current, events⟩ := acc
  unfold failureGroupStep
  dsimp only
  split
  · exact List.Subset.refl _
  · split
    · exact List.subset_append_left _ _
    · exact List.Subset.refl _

/-- Cancellation history grows across the sequential failed-owner fold.
Witness: compose the per-owner subset through actual fold order.
-/
theorem failureGroupFold_cancelledGroups_subset (errors : Nat)
    (groups : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent)
    : acc.1.cancelledGroups.Subset
        (groups.foldl (failureGroupStep errors) acc).1.cancelledGroups := by
  induction groups generalizing acc with
  | nil => exact List.Subset.refl _
  | cons group rest ih =>
      exact (failureGroupStep_cancelledGroups_subset errors acc group).trans (ih _)

/-- A failed-owner fold retains each initially live uncancelled group ref.
Witness: propagate endpoint noncancellation backward using retained history, then keep the
ref through active removal or the ref-preserving latent error-cache update.
-/
theorem failureGroupFold_uncancelled_present (errors : Nat)
    (groups : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent)
    {ref : NodeRef}
    (present : ref ∈ acc.1.groupNodes.map (fun owner => owner.group.node.ref))
    (uncancelled : ref ∉ (groups.foldl (failureGroupStep errors) acc).1.cancelledGroups)
    : ref
      ∈ (groups.foldl (failureGroupStep errors) acc).1.groupNodes.map
          (fun owner => owner.group.node.ref) := by
  induction groups generalizing acc with
  | nil => exact present
  | cons group rest ih =>
      have after : ref ∉ (failureGroupStep errors acc group).1.cancelledGroups :=
        fun member => uncancelled (failureGroupFold_cancelledGroups_subset errors rest _ member)
      apply ih _ ?_ uncancelled
      obtain ⟨current, events⟩ := acc
      unfold failureGroupStep at after ⊢
      dsimp only at after ⊢
      cases found : current.groupNode? group.ref with
      | none => simpa only [found] using present
      | some node =>
          simp only [found] at after ⊢
          cases active : current.rootGroups.contains group.ref with
          | false =>
              simp only [Bool.false_eq_true, ↓reduceIte, State.putGroupNode_refs]
              exact present
          | true =>
              simp only [active, ↓reduceIte] at after ⊢
              exact State.removeGroup_uncancelled_present _ _ present after

/-- A failed task retains each initially live group not recorded as cancelled.
Witness: ignored failures remove only the failed task; accepted failures use the fold's
uncancelled-ref theorem. Neither branch treats mere absence as cancellation.
-/
theorem State.taskFailure_uncancelled_present (queue : State) (occurrence : Occurrence)
    (errors : Nat) {ref : NodeRef}
    (present : ref ∈ queue.groupNodes.map (fun owner => owner.group.node.ref))
    (uncancelled : ref ∉ (queue.taskFailure occurrence errors).1.cancelledGroups)
    : ref
      ∈ (queue.taskFailure occurrence errors).1.groupNodes.map
          (fun owner => owner.group.node.ref) := by
  unfold State.taskFailure at uncancelled ⊢
  cases found : queue.taskNode? occurrence with
  | none => simpa only [found] using present
  | some node =>
      simp only [found] at uncancelled ⊢
      cases healthy : queue.taskHasHealthyOwner node.task with
      | false =>
          simpa only [healthy, Bool.not_false, ↓reduceIte, State.removeTask, List.map_map,
            Function.comp_def]
            using present
      | true =>
          simp only [healthy, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at uncancelled ⊢
          apply failureGroupFold_uncancelled_present _ _ _ ?_ uncancelled
          simpa only [State.removeTask, List.map_map, Function.comp_def] using present

/-- Fresh failed input conserves every older successful buffered value and live owner.
Witness: source provenance excludes the failed identity. Noncancellation retains the
owner record, so the existing surviving-owner lookup theorem preserves the exact value.
-/
theorem State.PublicationInventory.taskFailure_storedOwnersConserved {queue : State}
    {before published}
    (inventory : queue.PublicationInventory (ObjectValueFrom before) published)
    (occurrence : Occurrence) (errors : Nat)
    (fresh : (GraphEvent.taskFailure occurrence errors).Fresh before)
    : queue.StoredOwnersConserved [] (queue.taskFailure occurrence errors).1 := by
  intro task node value found stored ref contributes present uncancelled
  have live := queue.taskFailure_uncancelled_present occurrence errors present uncancelled
  have known := State.taskNode?_some found
  have source := (inventory.stored node known.1 value stored).1
  have different : task ≠ occurrence := by
    intro same
    exact fresh.2.2.1 occurrence List.mem_cons_self (same ▸ known.2 ▸ source.identity)
  obtain ⟨contributor, member, refEq⟩ := List.mem_map.mp contributes
  obtain ⟨owner, retained, ownerEq⟩ := List.mem_map.mp live
  exact Or.inr ⟨State.taskFailure_lookup_survivingOwner found occurrence errors different
      member retained (ownerEq.trans refEq.symm),
    List.mem_map.mpr ⟨owner, retained, ownerEq⟩⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
