import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ReceiptLifecycle

/-! A partially consumed receipt erases to its consumed item prefix, not its original
batch. Nonempty prefixes retain the existing work/source admission laws. This does not
model native exceptions, reentrant stop or disposal of unconsumed producer-owned work.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement

-----------------------------------------------------------------------------------------
-- Partial consumption licenses only the accepted FIFO prefix
-----------------------------------------------------------------------------------------

/-- The same initialized receipt licenses adoption of exactly its consumed prefix.
Acknowledgement does not adopt the unconsumed suffix, even when it follows partial unwind.
-/
theorem ReceiptReplay.prefix_graphEffects {queue : ReferenceWorkQueue.State}
    {stream : Execution.DeliveryNode} {items : List ReferenceWorkQueue.StreamItem}
    {id actions after}
    (replay
      : ReceiptReplay (Receipt.initialize id stream.ref (items.map (·.occurrence)))
          actions after)
    (active : queue.rootStreams.contains stream.ref = true)
    (acknowledged : after.acknowledged = true)
    : graphEffects queue (.streamItems stream (items.take after.consumed))
        = (actions.filterMap ReceiptAction.consumed?).map HostEffect.adopt
          ++ [.acknowledge stream.ref]
      ∧ actions.countP ReceiptAction.isAcknowledgement = 1 := by
  have fifo := replay.initialized_prefix
  have consumed : actions.filterMap ReceiptAction.consumed?
      = (items.take after.consumed).map (·.occurrence) := by
    rw [← fifo.2.2.2.1, fifo.2.2.1, List.map_take]
  refine ⟨?_, ?_⟩
  · simp only [graphEffects, active, ↓reduceIte, consumed, List.map_map]
    rfl
  · simpa [Receipt.initialize, acknowledged] using replay.acknowledgementCount

-----------------------------------------------------------------------------------------
-- Trimming a ready source batch preserves its original admission requirements
-----------------------------------------------------------------------------------------

private theorem streamItems_take_matchesWork {work : Work} {stream items}
    (matching
      : ReferenceWorkQueue.GraphEvent.MatchesWork work
          (.streamItems stream items)) (count : Nat)
    : ReferenceWorkQueue.GraphEvent.MatchesWork work
        (.streamItems stream (items.take count)) := by
  intro item selected
  exact matching item (List.mem_of_mem_take selected)

private theorem streamItems_take_fresh {before : List GraphEvent} {stream items}
    (fresh : ReferenceWorkQueue.GraphEvent.Fresh before (.streamItems stream items))
    (count : Nat)
    : ReferenceWorkQueue.GraphEvent.Fresh before
        (.streamItems stream (items.take count)) := by
  dsimp only [ReferenceWorkQueue.GraphEvent.Fresh, ReferenceWorkQueue.GraphEvent.identities] at fresh ⊢
  rw [List.map_take]
  exact ⟨List.Nodup.sublist (List.take_sublist _ _) fresh.1, fresh.2.1,
    fun occurrence selected => fresh.2.2.1 occurrence (List.mem_of_mem_take selected), fresh.2.2.2⟩

private theorem streamItems_take_ready {work : Work} {before : List GraphEvent}
    {stream items}
    (ready : ReferenceWorkQueue.GraphEvent.Ready work before (.streamItems stream items))
    (count : Nat) (positive : 0 < count)
    : ReferenceWorkQueue.GraphEvent.Ready work before
        (.streamItems stream (items.take count)) := by
  obtain ⟨address, results, producer, dependencies, located, nonempty, openSource, settled, ordered⟩ := ready
  refine ⟨address, results, producer, dependencies, located, ?_, openSource, settled, ?_⟩
  · intro empty
    rcases List.take_eq_nil_iff.mp empty with zero | absent
    · omega
    · exact nonempty absent
  · rw [List.map_take, ordered, ← List.map_take, List.take_range, List.length_take]

/-- The original source contract admits every nonempty initial slice of a matching,
fresh, ready batch. No endpoint queue safety or new source premise is introduced.
-/
theorem validGraphEvents_append_streamPrefix {work : Work} {before : List GraphEvent}
    {stream items} (valid : ReferenceWorkQueue.ValidGraphEvents work before)
    (matching
      : ReferenceWorkQueue.GraphEvent.MatchesWork work (.streamItems stream items))
    (fresh : ReferenceWorkQueue.GraphEvent.Fresh before (.streamItems stream items))
    (ready : ReferenceWorkQueue.GraphEvent.Ready work before (.streamItems stream items))
    (count : Nat) (positive : 0 < count)
    : ReferenceWorkQueue.ValidGraphEvents work
        (before ++ [.streamItems stream (items.take count)]) :=
  .append valid (streamItems_take_matchesWork matching count)
    (streamItems_take_fresh fresh count) (streamItems_take_ready ready count positive)

/-- A nonempty consumed receipt prefix preserves source legality without adopting its suffix.
This is a work/source abstraction, not a claim that every opaque schedule admits trimming.
-/
theorem ReceiptReplay.prefix_sourceAdmission {work : Work} {before : List GraphEvent}
    {stream : Execution.DeliveryNode} {items : List ReferenceWorkQueue.StreamItem}
    {id actions after}
    (replay
      : ReceiptReplay (Receipt.initialize id stream.ref (items.map (·.occurrence)))
          actions after)
    (valid : ReferenceWorkQueue.ValidGraphEvents work before)
    (matching
      : ReferenceWorkQueue.GraphEvent.MatchesWork work (.streamItems stream items))
    (fresh : ReferenceWorkQueue.GraphEvent.Fresh before (.streamItems stream items))
    (ready : ReferenceWorkQueue.GraphEvent.Ready work before (.streamItems stream items))
    (positive : 0 < after.consumed)
    : ReferenceWorkQueue.ValidGraphEvents work
        (before ++ [.streamItems stream (items.take after.consumed)])
      ∧ (items.take after.consumed).map (·.occurrence)
        = actions.filterMap ReceiptAction.consumed? := by
  refine ⟨validGraphEvents_append_streamPrefix valid matching fresh ready _ positive, ?_⟩
  rw [List.map_take, ← replay.initialized_prefix.2.2.1]
  exact replay.initialized_prefix.2.2.2.1

/-- A zero-consumption finally callback contributes no ready item event. The existing source
contract requires nonempty stream-item input; do not manufacture an empty admitted event.
-/
theorem streamItems_empty_not_ready (work : Work) (before : List GraphEvent)
    (stream : Execution.DeliveryNode)
    : ¬ReferenceWorkQueue.GraphEvent.Ready work before (.streamItems stream []) := by
  rintro ⟨_, _, _, _, _, nonempty, _⟩
  exact nonempty rfl

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
