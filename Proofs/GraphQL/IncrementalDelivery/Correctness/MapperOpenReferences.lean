import Proofs.GraphQL.IncrementalDelivery.Correctness.MapperReferences
import Proofs.GraphQL.IncrementalDelivery.Correctness.MapperAllocation

/-! Transport causal source references to actual wire IDs. Closed IDs remain tracked
in the stable allocation map; freshness never relies on forgetting past completions.
-/

namespace GraphQL.IncrementalDelivery.Correctness

open GraphQL.IncrementalDelivery.Execution

namespace WireReferences

def pending (update : IncrementalStreamUpdateResult) : List String :=
  update.pending.map IncrementalPendingNotice.id

def completed (update : IncrementalStreamUpdateResult) : List String :=
  update.completed.map IncrementalCompletionNotice.id

def used (update : IncrementalStreamUpdateResult) : List String :=
  completed update ++ update.incremental.map IncrementalResult.id

def Valid (seen closed : List String) (updates : List IncrementalStreamUpdateResult)
    : Prop :=
  ReferenceHistory pending completed used seen closed updates

end WireReferences

namespace MapperIdentity

open WorkScheduler

/-- Injective stable allocation transports an open key reference to an open ID. -/
theorem Encodes.reference {state : IDState} (well : Allocated state)
    {seen closed : List Nat} {seenIDs closedIDs : List String}
    (announced : Encodes state seen seenIDs) (finished : Encodes state closed closedIDs)
    {key : Nat} {id : String} (known : Known state key id)
    (refs : key ∈ seen ∧ key ∉ closed)
    : id ∈ seenIDs ∧ id ∉ closedIDs := by
  obtain ⟨other, member, encoded⟩ := announced.fromKey key refs.1
  refine ⟨by simpa [known.unique encoded] using member, ?_⟩
  intro member
  obtain ⟨other, source, encoded⟩ := finished.fromID id member
  exact refs.2 ((known.injective well encoded).symm ▸ source)

/-- Replay preserves open references, by batch induction and allocation injectivity. -/
theorem mappedTrace_references {batches : List (List WorkEvent)} {state : IDState}
    {seen closed : List Nat} {seenIDs closedIDs : List String}
    (well : Allocated state) (announced : Encodes state seen seenIDs)
    (finished : Encodes state closed closedIDs)
    (refs : ReferenceHistory pendingKeys completedKeys usedKeys seen closed batches)
    : WireReferences.Valid seenIDs closedIDs (mappedTrace batches state) := by
  induction batches generalizing state seen closed seenIDs closedIDs with
  | nil => trivial
  | cons batch rest ih =>
      cases h : (mapWorkEventBatch batch).run state with
      | mk update next =>
          obtain ⟨preserved, pending, completed⟩ := mapWorkEventBatch_of_eq h
          have patches := mapWorkEventBatch_references batch state
          rw [h] at patches
          have allocated : Allocated next := by
            simpa only [h] using mapWorkEventBatch_allocated batch state well
          have newSeen := (announced.mono preserved).append pending
          have oldClosed := finished.mono preserved
          have newClosed := oldClosed.append completed
          simp only [mappedTrace, h]
          refine ⟨?_, ih allocated newSeen newClosed refs.2⟩
          intro id member
          have source : ∃ key ∈ usedKeys batch, Known next key id := by
            rcases List.mem_append.mp member with completion | patch
            · obtain ⟨key, source, known⟩ := completed.fromID id completion
              exact ⟨key, completedKeys_used source, known⟩
            · obtain ⟨entry, member, eq⟩ := List.mem_map.mp patch
              obtain ⟨key, source, known⟩ := patches entry member
              exact ⟨key, source, eq ▸ known⟩
          obtain ⟨key, source, known⟩ := source
          exact newSeen.reference allocated oldClosed known (refs.1 key source)

end MapperIdentity
end GraphQL.IncrementalDelivery.Correctness
