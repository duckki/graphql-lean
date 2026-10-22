import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.GraphEffectProjection

/-! One source-generator receipt, including partial consumption and finally acknowledgement.
Receipt identity is distinct from stream identity. This is ghost evidence, not a buffer.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open GraphQL.IncrementalDelivery.WorkQueueSemantics (Occurrence)

structure Receipt where
  id : Nat
  stream : Nat
  items : List Occurrence
  consumed : Nat := 0
  unwound : Bool := false
  acknowledged : Bool := false
deriving Repr

def Receipt.initialize (id stream : Nat) (items : List Occurrence) : Receipt :=
  { id, stream, items }

def Receipt.Valid (receipt : Receipt) : Prop :=
  receipt.consumed ≤ receipt.items.length
  ∧ (receipt.acknowledged = true → receipt.unwound = true)

/-- Accepted items are exactly a prefix; unwinding/acknowledging cannot adopt the suffix. -/
def Receipt.accepted (receipt : Receipt) : List Occurrence :=
  receipt.items.take receipt.consumed

inductive ReceiptAction where
  | consume (occurrence : Occurrence)
  | unwind
  | acknowledge
deriving Repr

def ReceiptAction.consumed? : ReceiptAction → Option Occurrence
  | .consume occurrence => some occurrence
  | _ => none

def ReceiptAction.isAcknowledgement : ReceiptAction → Bool
  | .acknowledge => true
  | _ => false

/-- Consume means the item's integration/ownership handoff has completed. A bridge must
justify that observation at the actual item boundary, not at receipt acknowledgement.
-/
inductive ReceiptStep : Receipt → ReceiptAction → Receipt → Prop where
  | consume (receipt occurrence) (live : receipt.unwound = false)
    (next : receipt.items[receipt.consumed]? = some occurrence)
    : ReceiptStep receipt (.consume occurrence)
        { receipt with consumed := receipt.consumed + 1 }
  | unwind (receipt) : ReceiptStep receipt .unwind { receipt with unwound := true }
  | acknowledge (receipt) (unwound : receipt.unwound = true)
    (fresh : receipt.acknowledged = false)
    : ReceiptStep receipt .acknowledge { receipt with acknowledged := true }

inductive ReceiptReplay : Receipt → List ReceiptAction → Receipt → Prop where
  | nil (receipt) : ReceiptReplay receipt [] receipt
  | cons (step : ReceiptStep before action middle)
    (rest : ReceiptReplay middle actions after)
    : ReceiptReplay before (action :: actions) after

theorem Receipt.initialize_valid (id stream : Nat) (items : List Occurrence)
    : (Receipt.initialize id stream items).Valid := by
  simp [Receipt.initialize, Receipt.Valid]

theorem ReceiptStep.preserves_valid {before action after}
    (step : ReceiptStep before action after) (valid : before.Valid)
    : after.Valid := by
  cases step with
  | consume occurrence live next =>
      obtain ⟨room, _⟩ := List.getElem?_eq_some_iff.mp next
      refine ⟨by dsimp only; omega, ?_⟩
      intro acknowledged
      exact valid.2 acknowledged
  | unwind => exact ⟨valid.1, fun _ => rfl⟩
  | acknowledge unwound fresh => exact ⟨valid.1, fun _ => unwound⟩

theorem ReceiptReplay.preserves_valid {before actions after}
    (replay : ReceiptReplay before actions after) (valid : before.Valid)
    : after.Valid := by
  induction replay with
  | nil => exact valid
  | cons step rest ih => exact ih (step.preserves_valid valid)

theorem ReceiptStep.metadata {before action after}
    (step : ReceiptStep before action after)
    : (after.id, after.stream, after.items)
      = (before.id, before.stream, before.items) := by
  cases step <;> rfl

theorem ReceiptReplay.metadata {before actions after}
    (replay : ReceiptReplay before actions after)
    : (after.id, after.stream, after.items)
      = (before.id, before.stream, before.items) := by
  induction replay with
  | nil => rfl
  | cons step rest ih => exact ih.trans step.metadata

/-- Each consume advances by the actual next occurrence; other transitions advance nothing. -/
theorem ReceiptStep.accepted {before action after}
    (step : ReceiptStep before action after)
    : after.accepted = before.accepted ++ action.consumed?.toList := by
  cases step with
  | consume occurrence live next =>
      simp only [Receipt.accepted, ReceiptAction.consumed?, List.take_add_one, next,
        Option.toList_some]
  | unwind => simp [Receipt.accepted, ReceiptAction.consumed?]
  | acknowledge => simp [Receipt.accepted, ReceiptAction.consumed?]

/-- The same receipt witness ties FIFO consumption to the exact accepted prefix. -/
theorem ReceiptReplay.accepted {before actions after}
    (replay : ReceiptReplay before actions after)
    : after.accepted = before.accepted ++ actions.filterMap ReceiptAction.consumed? := by
  induction replay with
  | nil => simp
  | cons step rest ih =>
      rw [ih, step.accepted, List.append_assoc]
      cases step <;> rfl

/-- FIFO identity and the consumed prefix come from one initialized receipt trace. -/
theorem ReceiptReplay.initialized_prefix {id stream items actions after}
    (replay : ReceiptReplay (Receipt.initialize id stream items) actions after)
    : after.id = id
      ∧ after.stream = stream
      ∧ after.accepted = items.take after.consumed
      ∧ after.accepted = actions.filterMap ReceiptAction.consumed?
      ∧ after.consumed ≤ items.length := by
  have metadata := replay.metadata
  have sameItems : after.items = items := congrArg (fun p => p.2.2) metadata
  refine ⟨congrArg Prod.fst metadata,
    congrArg (fun p => p.2.1) metadata, ?_, ?_, ?_⟩
  · simp only [Receipt.accepted, sameItems]
  · simpa [Receipt.initialize, Receipt.accepted] using replay.accepted
  · simpa [sameItems] using (replay.preserves_valid (Receipt.initialize_valid _ _ _)).1

theorem ReceiptStep.acknowledgementCount {before action after}
    (step : ReceiptStep before action after)
    : (if action.isAcknowledgement then 1 else 0) + (if before.acknowledged then 1 else 0)
      = if after.acknowledged then 1 else 0 := by
  cases step <;> simp_all [ReceiptAction.isAcknowledgement]

theorem ReceiptReplay.acknowledgementCount {before actions after}
    (replay : ReceiptReplay before actions after)
    : actions.countP ReceiptAction.isAcknowledgement
        + (if before.acknowledged then 1 else 0)
      = if after.acknowledged then 1 else 0 := by
  induction replay with
  | nil => exact Nat.zero_add _
  | cons step rest ih =>
      have one := step.acknowledgementCount
      rw [List.countP_cons]
      omega

theorem ReceiptReplay.acknowledgementCount_le_one {before actions after}
    (replay : ReceiptReplay before actions after)
    : actions.countP ReceiptAction.isAcknowledgement ≤ 1 := by
  have count := replay.acknowledgementCount
  split at count <;> split at count <;> omega

/-- A finally acknowledgement is licensed by unwinding, not by fully consuming the receipt. -/
theorem ReceiptStep.acknowledge_requires_unwind {before after}
    (step : ReceiptStep before .acknowledge after)
    : before.unwound = true ∧ after.consumed = before.consumed := by
  cases step
  exact ⟨by assumption, rfl⟩

/-- The public label forgets receipt identity; a native trace must retain callback identity. -/
def Receipt.acknowledgementEffect (receipt : Receipt) : HostEffect :=
  .acknowledge receipt.stream

theorem Receipt.same_stream_effect (left right : Receipt)
    (same : left.stream = right.stream)
    : left.acknowledgementEffect = right.acknowledgementEffect :=
  congrArg HostEffect.acknowledge same

/-- A fully consumed, acknowledged receipt erases to the existing atomic batch labels.
Partial unwinding is governed by the prefix theorem, not by this full-batch correspondence.
-/
theorem ReceiptReplay.full_graphEffects {queue : ReferenceWorkQueue.State}
    {stream : Execution.DeliveryNode} {items : List ReferenceWorkQueue.StreamItem}
    {id actions after}
    (replay
      : ReceiptReplay
          (Receipt.initialize id stream.ref (items.map (·.occurrence))) actions after)
    (active : queue.rootStreams.contains stream.ref = true)
    (full : after.consumed = items.length) (acknowledged : after.acknowledged = true)
    : graphEffects queue (.streamItems stream items)
        = (actions.filterMap ReceiptAction.consumed?).map HostEffect.adopt
          ++ [.acknowledge stream.ref]
      ∧ actions.countP ReceiptAction.isAcknowledgement = 1 := by
  have fifo := replay.initialized_prefix
  have consumed : actions.filterMap ReceiptAction.consumed? = items.map (·.occurrence) := by
    rw [← fifo.2.2.2.1, fifo.2.2.1, full]
    exact List.take_of_length_le (by simp)
  refine ⟨?_, ?_⟩
  · simp only [graphEffects, active, ↓reduceIte, consumed, List.map_map]
    rfl
  · simpa [Receipt.initialize, acknowledged] using replay.acknowledgementCount

/-- A fully consumed native receipt agrees with the current handler's actual handoff and
acknowledgement views. Cleanup stays interleaved during consumption, and ready-drain cleanup
may follow the acknowledgement at the consumption boundary.
This does not reconstruct acquired resources from those handoff identities.
-/
theorem ReceiptReplay.full_streamItems {state : State}
    {stream : Execution.DeliveryNode} {items : List ReferenceWorkQueue.StreamItem}
    {id actions after}
    (replay
      : ReceiptReplay
          (Receipt.initialize id stream.ref (items.map (·.occurrence))) actions after)
    (active : state.queue.rootStreams.contains stream.ref = true)
    (full : after.consumed = items.length) (acknowledged : after.acknowledged = true)
    : (state.streamItems stream items).2.2.1.filterMap HostEffect.adoptedProducer?
        = actions.filterMap ReceiptAction.consumed?
      ∧ (state.streamItems stream items).2.2.1.filterMap HostEffect.acknowledgedStream?
        = [stream.ref]
      ∧ (∃ (earlier : List HostEffect) (targets : List CleanupTarget),
          (state.streamItems stream items).2.2.1
          = earlier ++ [.acknowledge stream.ref] ++ targets.flatMap CleanupTarget.effects)
      ∧ actions.countP ReceiptAction.isAcknowledgement = 1 := by
  have fifo := replay.initialized_prefix
  have consumed : actions.filterMap ReceiptAction.consumed? = items.map (·.occurrence) := by
    rw [← fifo.2.2.2.1, fifo.2.2.1, full]
    exact List.take_of_length_le (by simp)
  refine ⟨?_, state.streamItems_acknowledges_once stream items,
    state.streamItems_consumptionBoundary stream items, ?_⟩
  · rw [State.streamItems_adoptedProducers, active, consumed]
    rfl
  · simpa [Receipt.initialize, acknowledged] using replay.acknowledgementCount

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
