import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamRegistrationFreshness
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ItemStreamRelease

/-! A multi-item carrier announces each new stream once and excludes the old registry. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (StreamItemValue)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Freshness survives every item in the carrier's actual preparation fold
-----------------------------------------------------------------------------------------

/-- The item fold retains a fresh, unique notice inventory against any old registered keys.
Witness: each integration appends only keys absent from the current registry, which already
contains both excluded old keys and all earlier item notices. Pruning and activation leave
that registry unchanged. No generated-work or source-validity premise is required.
-/
theorem streamItemFold_streamNoticeInventory (items : List StreamItem) (excluded : Keys)
    (acc
      : State
        × List Execution.DeliveryNode
        × List Execution.DeliveryNode
        × List StreamItemValue)
    (old : excluded.Subset (acc.1.streams.map (fun stream => stream.node.key)))
    (covered
      : (acc.2.2.1.map Execution.DeliveryNode.key).Subset
          (acc.1.streams.map (fun stream => stream.node.key)))
    (unique : (acc.2.2.1.map Execution.DeliveryNode.key).Nodup)
    (fresh : ∀ key ∈ acc.2.2.1.map Execution.DeliveryNode.key, key ∉ excluded)
    : let final := items.foldl streamItemStep acc
      excluded.Subset (final.1.streams.map (fun stream => stream.node.key))
      ∧ (final.2.2.1.map Execution.DeliveryNode.key).Subset
          (final.1.streams.map (fun stream => stream.node.key))
      ∧ (final.2.2.1.map Execution.DeliveryNode.key).Nodup
      ∧ ∀ key ∈ final.2.2.1.map Execution.DeliveryNode.key, key ∉ excluded := by
  induction items generalizing acc with
  | nil => exact ⟨old, covered, unique, fresh⟩
  | cons item rest ih =>
      let integrated := acc.1.maybeIntegrateWork item.work
      let next := streamItemStep acc item
      have registry : next.1.streams = integrated.1.streams := by
        dsimp only [next, streamItemStep]
        rw [State.startNewWork_streams, State.pruneEmptyGroups_streams]
      have notices : next.2.2.1 = acc.2.2.1 ++ integrated.2.newStreams := rfl
      have stored := acc.1.maybeIntegrateWork_streams_registered item.work
      have added := acc.1.maybeIntegrateWork_streamNotices_fresh item.work
      have retains : (acc.1.streams.map (fun stream => stream.node.key)).Subset
          (next.1.streams.map (fun stream => stream.node.key)) := by
        rw [registry]
        exact List.map_subset _ stored.1
      have newStored : (integrated.2.newStreams.map Execution.DeliveryNode.key).Subset
          (next.1.streams.map (fun stream => stream.node.key)) := by
        rw [registry]
        intro key member
        obtain ⟨node, included, same⟩ := List.mem_map.mp member
        obtain ⟨stream, registered, descriptor⟩ := List.mem_map.mp (stored.2 included)
        exact List.mem_map.mpr ⟨stream, registered,
          (congrArg Execution.DeliveryNode.key descriptor).trans same⟩
      have newFresh : ∀ key ∈ integrated.2.newStreams.map Execution.DeliveryNode.key,
          key ∉ acc.1.streams.map (fun stream => stream.node.key) := by
        intro key member
        obtain ⟨node, included, same⟩ := List.mem_map.mp member
        exact same ▸ added.2 node included
      refine ih next (old.trans retains) ?_ ?_ ?_
      · rw [notices, List.map_append]
        exact List.append_subset.mpr ⟨covered.trans retains, newStored⟩
      · rw [notices, List.map_append]
        refine List.nodup_append.mpr ⟨unique, added.1, ?_⟩
        intro first earlier second later same
        exact newFresh second later (same ▸ covered earlier)
      · rw [notices, List.map_append]
        intro key member
        rcases List.mem_append.mp member with earlier | later
        · exact fresh key earlier
        · exact fun previous => newFresh key later (old previous)

/-- All streams on an actual item carrier are unique and absent from its entry registry.
Witness: initialize the preparation inventory with no carried notices; the handler emits
the resulting list once before draining, and the drain never emits another item carrier.
-/
theorem State.streamItems_notices_fresh (queue : State) (stream : Execution.DeliveryNode)
    (items : List StreamItem) {position : Nat} {owner : Execution.DeliveryNode}
    {values : List StreamItemValue} {groups streams : List Execution.DeliveryNode}
    (selected
      : (queue.streamItems stream items).2[position]?
        = some (.streamValues owner values groups streams))
    : (streams.map Execution.DeliveryNode.key).Nodup
      ∧ ∀ node ∈ streams,
          node.key ∉ queue.streams.map (fun stream => stream.node.key) := by
  have zero := queue.streamItems_carrier_index stream items selected
  rw [zero, queue.streamItems_eq] at selected
  split at selected
  · cases selected
  · have same := Execution.WorkQueueEvent.streamValues.inj (Option.some.inj selected)
    obtain ⟨_, _, _, rfl⟩ := same
    have inventory := streamItemFold_streamNoticeInventory items
      (queue.streams.map (fun stream => stream.node.key)) (queue, [], [], [])
      (List.Subset.refl _) (by intro key impossible; cases impossible) (by simp) (by simp)
    refine ⟨inventory.2.2.1, ?_⟩
    intro node member
    exact inventory.2.2.2 node.key (List.mem_map_of_mem member)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
