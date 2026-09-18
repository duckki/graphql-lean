import Proofs.GraphQL.IncrementalDelivery.Correctness.MapperEvents

/-! Stable identities transport node liveness to the actual lazy response mapper.
Materialization here is a proof observation, never an execution step.
-/

namespace GraphQL.IncrementalDelivery.Correctness.MapperIdentity

open GraphQL.IncrementalDelivery.Execution
open WorkScheduler

/-- Replay supplied observed batches; this helper never selects a source's future. -/
def mappedTrace : List (List WorkEvent) → IDState → List IncrementalStreamUpdateResult
  | [], _ => []
  | events :: tail, ids =>
      let (update, nextIDs) := (mapWorkEventBatch events).run ids
      update :: mappedTrace tail nextIDs

/-- The allocation state remaining after the supplied observed batches. -/
def finalIDs : List (List WorkEvent) → IDState → IDState
  | [], state => state
  | batch :: rest, state => finalIDs rest ((mapWorkEventBatch batch).run state).2

/-- Finite input replay preserves IDs and encodes completions, by batch induction. -/
theorem mappedTrace_spec (batches : List (List WorkEvent)) (state : IDState)
    : Preserves state (finalIDs batches state)
      ∧ Encodes (finalIDs batches state) (completedKeys batches.flatten)
          (DeliveryTrace.completedIDs (mappedTrace batches state)) := by
  induction batches generalizing state with
  | nil => exact ⟨.refl _, .nil⟩
  | cons batch rest ih =>
      cases h : (mapWorkEventBatch batch).run state with
      | mk update next =>
          obtain ⟨hp, _, hc⟩ := mapWorkEventBatch_of_eq h
          obtain ⟨tp, tc⟩ := ih next
          refine ⟨?_, ?_⟩
          · simpa [finalIDs, h] using hp.trans tp
          · simpa only [finalIDs, mappedTrace, h, List.flatten_cons, completedKeys,
              List.flatMap_append, DeliveryTrace.completedIDs, List.flatMap_cons]
              using (hc.mono tp).append tc

/-- A completed key yields its previously known ID, by stable lookup uniqueness. -/
theorem mappedTrace_completion {batches : List (List WorkEvent)} {state : IDState}
    {key : Nat} {id : String} (known : Known state key id)
    (closed : key ∈ completedKeys batches.flatten)
    : id ∈ DeliveryTrace.completedIDs (mappedTrace batches state) := by
  obtain ⟨preserves, encodes⟩ := mappedTrace_spec batches state
  obtain ⟨other, ho, hk⟩ := encodes.fromKey key closed
  have same := (preserves _ _ known).unique hk
  simpa [same] using ho

/-- Causal key liveness yields causal ID liveness, by replay induction. -/
theorem mappedTrace_live {batches : List (List WorkEvent)} (state : IDState)
    (live : liveBatches batches)
    : DeliveryTrace.announcementsEventuallyComplete (mappedTrace batches state) := by
  induction batches generalizing state with
  | nil => trivial
  | cons batch rest ih =>
      cases h : (mapWorkEventBatch batch).run state with
      | mk update next =>
          obtain ⟨_, pending, _⟩ := mapWorkEventBatch_of_eq h
          obtain ⟨preserves, _⟩ := mappedTrace_spec rest next
          have whole := (mappedTrace_spec (batch :: rest) state).2
          simp only [finalIDs, h, List.flatten_cons, mappedTrace] at whole
          simp only [mappedTrace, h]
          refine ⟨?_, ih next live.2⟩
          intro id hi
          obtain ⟨key, hk, known⟩ := pending.fromID id hi
          obtain ⟨other, ho, hc⟩ := whole.fromKey key (live.1 key hk)
          have same := (preserves _ _ known).unique hc
          simpa [same] using ho

end GraphQL.IncrementalDelivery.Correctness.MapperIdentity
