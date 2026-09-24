import Proofs.GraphQL.IncrementalDelivery.Correctness.MapperLiveness
import Proofs.GraphQL.IncrementalDelivery.Correctness.StateInvariant
import Std.Data.String.ToNat

/-! Wire IDs are globally fresh, including IDs whose nodes have already completed.
The numerical supply is internal to mapping and is independent of scheduling order.
-/

namespace GraphQL.IncrementalDelivery.Correctness.MapperIdentity

open GraphQL.IncrementalDelivery.Execution
open WorkScheduler

/-- Distinct projected values identify distinct list members, by list induction. -/
private theorem eq_of_map_nodup {values : List α} {key : α → β} {left right : α}
    (h : (values.map key).Nodup) (hl : left ∈ values) (hr : right ∈ values)
    (he : key left = key right)
    : left = right := by
  induction values with
  | nil => simp at hl
  | cons head tail ih =>
      obtain ⟨fresh, unique⟩ := List.nodup_cons.mp h
      rcases List.mem_cons.mp hl with rfl | leftTail
      · rcases List.mem_cons.mp hr with rfl | rightTail
        · rfl
        · exact False.elim (fresh (List.mem_map.mpr ⟨right, rightTail, he.symm⟩))
      · rcases List.mem_cons.mp hr with rfl | rightTail
        · exact False.elim (fresh (List.mem_map.mpr ⟨left, leftTail, he⟩))
        · exact ih unique leftTail rightTail

/-- Allocated IDs are distinct decimal numbers below the next supply value. -/
structure Allocated (state : IDState) : Prop where
  unique : (state.ids.map Prod.snd).Nodup
  bounded : ∀ entry ∈ state.ids, ∃ n < state.nextID, entry.2 = toString n

/-- The empty allocation state is injective and bounded, by empty membership. -/
theorem Allocated.empty : Allocated {} := ⟨by simp, by simp⟩

/-- The next numerical ID is unused, by boundedness and decimal injectivity. -/
theorem Allocated.fresh {state : IDState} (h : Allocated state)
    : toString state.nextID ∉ state.ids.map Prod.snd := by
  intro hm
  obtain ⟨entry, member, same⟩ := List.mem_map.mp hm
  obtain ⟨n, bound, encoded⟩ := h.bounded entry member
  have equal : n = state.nextID := Nat.repr_injective (encoded.symm.trans same)
  omega

/-- Allocation preserves fresh, bounded IDs, by lookup cases. -/
theorem ensureID_allocated (node : DeliveryNode)
    : StateInvariant Allocated (ensureID node) := by
  intro state well
  change Allocated (ensureID node state).2
  cases h : state.ids.find? (fun entry => entry.1 == node.key) with
  | some entry => simpa [ensureID, h] using well
  | none =>
      simp only [ensureID, h]
      constructor
      · simp only [List.map_append, List.map_cons, List.map_nil]
        exact List.nodup_append.mpr ⟨well.unique, by simp, fun a ha b hb he => by
          cases List.mem_singleton.mp hb
          exact well.fresh (he ▸ ha)⟩
      · intro entry member
        rcases List.mem_append.mp member with old | new
        · obtain ⟨n, bound, encoded⟩ := well.bounded entry old
          exact ⟨n, Nat.lt_trans bound (Nat.lt_succ_self _), encoded⟩
        · cases List.mem_singleton.mp new
          exact ⟨state.nextID, Nat.lt_succ_self _, rfl⟩

/-- Equal known IDs identify equal keys, by injectivity of the stored ID list. -/
theorem Known.injective {state : IDState} (well : Allocated state) {left right : Nat}
    {id : String} (hl : Known state left id) (hr : Known state right id)
    : left = right := by
  have pairs := eq_of_map_nodup well.unique (List.mem_of_find?_eq_some hl)
    (List.mem_of_find?_eq_some hr) rfl
  exact congrArg Prod.fst pairs

/-- Distinct encoded keys yield distinct IDs, by allocation injectivity. -/
theorem Encodes.nodup {state : IDState} {keys : List Nat} {ids : List String}
    (h : Encodes state keys ids) (well : Allocated state) (unique : keys.Nodup)
    : ids.Nodup := by
  induction h with
  | nil => simp
  | @cons key id keys ids known tail ih =>
      obtain ⟨fresh, unique⟩ := List.nodup_cons.mp unique
      refine List.nodup_cons.mpr ⟨?_, ih unique⟩
      intro hm
      obtain ⟨other, member, encoded⟩ := tail.fromID id hm
      exact fresh ((known.injective well encoded).symm ▸ member)

/-- Pending allocation preserves freshness, by the state-invariant combinators. -/
theorem getPendingEntry_allocated (groups streams : List DeliveryNode)
    : StateInvariant Allocated (getPendingEntry groups streams ensureID) :=
  StateInvariant.mapM (fun node => (ensureID_allocated node).bind fun _ => .pure _ _) _

/-- Completion allocation preserves freshness, by one ID allocation. -/
theorem getCompletedEntry_allocated (node : DeliveryNode) (errors : Nat)
    : StateInvariant Allocated (getCompletedEntry node errors ensureID) :=
  (ensureID_allocated node).bind fun _ => .pure _ _

/-- Patch allocation preserves freshness, by one ID allocation. -/
theorem getIncrementalEntry_allocated (node : DeliveryNode) (value : GroupValue)
    : StateInvariant Allocated (getIncrementalEntry node value ensureID) :=
  (ensureID_allocated node).bind fun _ => .pure _ _

/-- Every mapper event preserves allocation freshness, by event case analysis. -/
theorem eventLoop_allocated (event : WorkEvent) (update : IncrementalStreamUpdateResult)
    : StateInvariant Allocated (eventLoop event update) := by
  cases event with
  | groupValues group values =>
      exact (StateInvariant.mapM (getIncrementalEntry_allocated group) values).bind
        fun _ => .pure _ _
  | groupSuccess group groups streams =>
      exact (getCompletedEntry_allocated group 0).bind fun _ =>
        (getPendingEntry_allocated groups streams).bind fun _ => .pure _ _
  | groupFailure group errors | streamFailure group errors =>
      exact (getCompletedEntry_allocated group errors).bind fun _ => .pure _ _
  | streamValues stream values groups streams =>
      exact (ensureID_allocated stream).bind fun _ =>
        (getPendingEntry_allocated groups streams).bind fun _ => .pure _ _
  | streamSuccess stream =>
      exact (getCompletedEntry_allocated stream 0).bind fun _ => .pure _ _
  | workQueueTermination => exact .pure _ _

/-- Batch mapping preserves allocation freshness, by loop induction. -/
theorem mapWorkEventBatch_allocated (events : List WorkEvent)
    : StateInvariant Allocated (mapWorkEventBatch events) := by
  intro state well
  rw [mapWorkEventBatch_loop]
  exact StateInvariant.forIn eventLoop_allocated events _ state well

/-- Finite replay preserves allocation freshness, by batch induction. -/
theorem finalIDs_allocated (batches : List (List WorkEvent)) (state : IDState)
    (well : Allocated state)
    : Allocated (finalIDs batches state) := by
  induction batches generalizing state with
  | nil => exact well
  | cons batch rest ih => exact ih _ (mapWorkEventBatch_allocated batch state well)

/-- Finite replay encodes every pending occurrence in order, by batch induction. -/
theorem mappedTrace_pending (batches : List (List WorkEvent)) (state : IDState)
    : Encodes (finalIDs batches state) (pendingKeys batches.flatten)
        (DeliveryTrace.pendingIDs (mappedTrace batches state)) := by
  induction batches generalizing state with
  | nil => exact .nil
  | cons batch rest ih =>
      cases h : (mapWorkEventBatch batch).run state with
      | mk update next =>
          have head := (mapWorkEventBatch_of_eq h).2.1
          have preserved := (mappedTrace_spec rest next).1
          simpa only [finalIDs, mappedTrace, h, List.flatten_cons, pendingKeys,
            List.flatMap_append, DeliveryTrace.pendingIDs, List.flatMap_cons]
            using (head.mono preserved).append (ih next)

end GraphQL.IncrementalDelivery.Correctness.MapperIdentity
