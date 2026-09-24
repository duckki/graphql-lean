import Proofs.GraphQL.IncrementalDelivery.Correctness.MapperEvents
import Proofs.GraphQL.IncrementalDelivery.WorkScheduler.References

/-! Each actual object/list patch carries the stable wire ID of a source-event node.
The proof follows the mapper, including all ID allocations made by new notices.
-/

namespace GraphQL.IncrementalDelivery.Correctness.MapperIdentity

open GraphQL.IncrementalDelivery.Execution
open WorkScheduler

def PatchReferences (state : IDState) (keys : List Nat) (patches : List IncrementalResult)
    : Prop :=
  ∀ patch ∈ patches, ∃ key ∈ keys, Known state key patch.id

/-- Preserved lookups transport patch provenance to the later allocation state. -/
theorem PatchReferences.mono {state next : IDState} {keys : List Nat}
    {patches : List IncrementalResult} (h : PatchReferences state keys patches)
    (preserved : Preserves state next)
    : PatchReferences next keys patches := by
  intro patch member
  obtain ⟨key, source, known⟩ := h patch member
  exact ⟨key, source, preserved _ _ known⟩

/-- Concatenating patch lists preserves provenance in the union of source keys. -/
theorem PatchReferences.append {state : IDState} {keys more : List Nat}
    {patches rest : List IncrementalResult} (h : PatchReferences state keys patches)
    (t : PatchReferences state more rest)
    : PatchReferences state (keys ++ more) (patches ++ rest) := by
  intro patch member
  rcases List.mem_append.mp member with member | member
  · obtain ⟨key, source, known⟩ := h patch member
    exact ⟨key, List.mem_append_left _ source, known⟩
  · obtain ⟨key, source, known⟩ := t patch member
    exact ⟨key, List.mem_append_right _ source, known⟩

structure MappedPatches (state : IDState) (initial : IncrementalStreamUpdateResult)
    (events : List WorkEvent) (update : IncrementalStreamUpdateResult) (next : IDState)
    : Prop where
  preserves : Preserves state next
  patches
    : ∃ entries,
        update.incremental = initial.incremental ++ entries
        ∧ PatchReferences next (usedKeys events) entries

/-- Every mapped patch names its source owner, by event case analysis. -/
theorem eventLoop_patches (event : WorkEvent) (initial : IncrementalStreamUpdateResult)
    (state : IDState)
    : ∃ update next,
        (eventLoop event initial).run state = (.yield update, next)
        ∧ MappedPatches state initial [event] update next := by
  cases event with
  | groupValues group values =>
      let action := fun value => getIncrementalEntry (m := StateM IDState) group value ensureID
      have fact := mapM_encodes action (fun _ => group.key) IncrementalResult.id
        (fun _ _ => ensureID_spec _ _) values state
      cases h : (values.mapM action).run state with
      | mk entries next =>
          rw [h] at fact
          refine ⟨
            { initial with incremental := initial.incremental ++ entries },
            next,
            ?_,
            ⟨fact.1, entries, rfl, ?_⟩
          ⟩
          · simp [eventLoop, action, StateT.run, StateT.bind, StateT.pure, bind, pure] at h ⊢
            rw [h]
          · intro patch member
            obtain ⟨key, source, known⟩ :=
              fact.2.fromID patch.id (List.mem_map.mpr ⟨patch, member, rfl⟩)
            obtain ⟨value, _, eq⟩ := List.mem_map.mp source
            exact ⟨key, by simp [usedKeys, eventUsed, eq], known⟩
  | groupSuccess group groups streams =>
      cases hc : (getCompletedEntry (m := StateM IDState) group 0 ensureID).run state with
      | mk completed middle =>
          cases hp
                : (getPendingEntry (m := StateM IDState) groups streams ensureID).run
                    middle with
          | mk pending next =>
              refine ⟨
                {
                  initial with
                    pending := initial.pending ++ pending
                    completed := initial.completed ++ [completed]
                },
                next,
                ?_,
                ⟨
                  (getCompletedEntry_of_eq hc).1.trans (getPendingEntry_of_eq hp).1,
                  [],
                  by simp,
                  by simp [PatchReferences]
                ⟩
              ⟩
              simp [eventLoop, StateT.run, StateT.bind, StateT.pure, bind, pure] at hc hp ⊢
              simp only [hc, hp]
  | groupFailure group errors | streamFailure group errors =>
      cases hc
            : (getCompletedEntry (m := StateM IDState) group errors ensureID).run
                state with
      | mk completed next =>
          refine ⟨
            { initial with completed := initial.completed ++ [completed] },
            next,
            ?_,
            ⟨(getCompletedEntry_of_eq hc).1, [], by simp, by simp [PatchReferences]⟩
          ⟩
          simp [eventLoop, StateT.run, StateT.bind, StateT.pure, bind, pure] at hc ⊢
          rw [hc]
  | streamValues stream values groups streams =>
      have fact := ensureID_spec stream state
      cases hi : ensureID stream state with
      | mk id middle =>
          rw [hi] at fact
          cases hp
                : (getPendingEntry (m := StateM IDState) groups streams ensureID).run
                    middle with
          | mk pending next =>
              have preserved := (getPendingEntry_of_eq hp).1
              let patch : IncrementalResult :=
                .list id (values.map StreamValue.item) ((values.map StreamValue.errors).sum)
              refine ⟨{ initial with
                  pending := initial.pending ++ pending
                  incremental := initial.incremental ++ [patch] }, next, ?_,
                ⟨fact.1.trans preserved, [patch], rfl, ?_⟩⟩
              · simp [eventLoop, patch, StateT.run, StateT.bind, StateT.pure,
                  bind, pure, hi] at hp ⊢
                rw [hp]
              · intro entry member
                cases List.mem_singleton.mp member
                exact ⟨stream.key, by simp [usedKeys, eventUsed], preserved _ _ fact.2⟩
  | streamSuccess stream =>
      cases hc
            : (getCompletedEntry (m := StateM IDState) stream 0 ensureID).run state with
      | mk completed next =>
          refine ⟨
            { initial with completed := initial.completed ++ [completed] },
            next,
            ?_,
            ⟨(getCompletedEntry_of_eq hc).1, [], by simp, by simp [PatchReferences]⟩
          ⟩
          simp [eventLoop, StateT.run, StateT.bind, StateT.pure, bind, pure] at hc ⊢
          rw [hc]
  | workQueueTermination =>
      exact ⟨
        { initial with hasNext := false },
        state,
        rfl,
        ⟨.refl _, [], by simp, by simp [PatchReferences]⟩
      ⟩

/-- Sequential mapper loops preserve combined patch provenance. -/
theorem MappedPatches.append {state middle final : IDState}
    {initial update last : IncrementalStreamUpdateResult} {head tail : List WorkEvent}
    (h : MappedPatches state initial head update middle)
    (t : MappedPatches middle update tail last final)
    : MappedPatches state initial (head ++ tail) last final := by
  obtain ⟨preserved, entries, he, refs⟩ := h
  obtain ⟨tailPreserved, more, hm, tailRefs⟩ := t
  exact ⟨
    preserved.trans tailPreserved,
    entries ++ more,
    by simp [hm, he, List.append_assoc],
    by
      simpa only [usedKeys, List.flatMap_append]
        using (refs.mono tailPreserved).append tailRefs
  ⟩

/-- All mapped patches have source-owner witnesses, by event-list induction. -/
theorem loop_patches (events : List WorkEvent) (initial : IncrementalStreamUpdateResult)
    (state : IDState)
    : ∃ update next,
        (forIn events initial eventLoop).run state = (update, next)
        ∧ MappedPatches state initial events update next := by
  induction events generalizing initial state with
  | nil => exact ⟨initial, state, rfl, .refl _, [], by simp, by simp [PatchReferences]⟩
  | cons event rest ih =>
      obtain ⟨middle, ids, he, hs⟩ := eventLoop_patches event initial state
      obtain ⟨update, next, ht, hm⟩ := ih middle ids
      refine ⟨update, next, ?_, hs.append hm⟩
      simp only [List.forIn_cons]
      simp [StateT.run, StateT.bind, bind] at he ht ⊢
      simp only [he, ht]

/-- Public batch mapping preserves patch provenance, by the loop equation. -/
theorem mapWorkEventBatch_references (events : List WorkEvent) (state : IDState)
    : let (update, next) := (mapWorkEventBatch events).run state
      PatchReferences next (usedKeys events) update.incremental := by
  obtain ⟨update, next, he, _, entries, hp, refs⟩ := loop_patches events { hasNext := true } state
  rw [mapWorkEventBatch_loop, he]
  simpa [hp] using refs

end GraphQL.IncrementalDelivery.Correctness.MapperIdentity
