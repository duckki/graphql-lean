import Proofs.GraphQL.IncrementalDelivery.Correctness.MapperIdentity

/-! Generalize the mapper's accumulator for induction, without changing execution.
The proof-only loop below is definitionally the body of mapWorkEventBatch.
-/

namespace GraphQL.IncrementalDelivery.Correctness.MapperIdentity

open GraphQL.IncrementalDelivery.Execution
open WorkScheduler

def eventLoop (event : WorkEvent) (update : IncrementalStreamUpdateResult)
    : StateM IDState (ForInStep IncrementalStreamUpdateResult) := do
  match event with
  | .groupValues group values =>
      let entries ← values.mapM (fun value => getIncrementalEntry group value ensureID)
      return .yield { update with incremental := update.incremental ++ entries }
  | .groupSuccess group groups streams =>
      let completed ← getCompletedEntry group 0 ensureID
      let pending ← getPendingEntry groups streams ensureID
      return .yield
        {
          update with
            completed := update.completed ++ [completed],
            pending := update.pending ++ pending
        }
  | .groupFailure group errors =>
      let completed ← getCompletedEntry group errors ensureID
      return .yield { update with completed := update.completed ++ [completed] }
  | .streamValues stream values groups streams =>
      let id ← ensureID stream
      let pending ← getPendingEntry groups streams ensureID
      return .yield
        {
          update with
            incremental :=
              update.incremental
              ++ [.list id (values.map StreamValue.item)
                    ((values.map StreamValue.errors).sum)],
            pending := update.pending ++ pending
        }
  | .streamSuccess stream =>
      let completed ← getCompletedEntry stream 0 ensureID
      return .yield { update with completed := update.completed ++ [completed] }
  | .streamFailure stream errors =>
      let completed ← getCompletedEntry stream errors ensureID
      return .yield { update with completed := update.completed ++ [completed] }
  | .workQueueTermination => return .yield { update with hasNext := false }

/-- The induction loop is definitionally the public event mapper. -/
theorem mapWorkEventBatch_loop (events : List WorkEvent) (state : IDState)
    : (mapWorkEventBatch events).run state
      = (forIn events { hasNext := true } eventLoop).run state := by
  rfl

structure Mapped (state : IDState) (initial : IncrementalStreamUpdateResult)
    (events : List WorkEvent) (update : IncrementalStreamUpdateResult) (next : IDState)
    : Prop where
  preserves : Preserves state next
  pending
    : ∃ entries,
        update.pending = initial.pending ++ entries
        ∧ Encodes next (pendingKeys events) (entries.map IncrementalPendingNotice.id)
  completed
    : ∃ entries,
        update.completed = initial.completed ++ entries
        ∧ Encodes next (completedKeys events) (entries.map IncrementalCompletionNotice.id)

/-- One mapped event preserves IDs and encodes notices, by event case analysis. -/
theorem eventLoop_spec (event : WorkEvent) (initial : IncrementalStreamUpdateResult)
    (state : IDState)
    : ∃ update next,
        (eventLoop event initial).run state = (.yield update, next)
        ∧ Mapped state initial [event] update next := by
  cases event with
  | groupValues group values =>
      let action := fun value => getIncrementalEntry (m := StateM IDState) group value ensureID
      have preserves := mapM_preserves action (getIncrementalEntry_preserves group) values state
      cases h : (values.mapM action).run state with
      | mk entries next =>
          refine ⟨
            { initial with incremental := initial.incremental ++ entries },
            next,
            ?_,
            ?_
          ⟩
          · simp [eventLoop, action, StateT.run, StateT.bind, StateT.pure, bind, pure] at h ⊢
            rw [h]
          · refine ⟨?_, ⟨[], by simp, .nil⟩, ⟨[], by simp, .nil⟩⟩
            simpa [h] using preserves
  | groupSuccess group groups streams =>
      cases hc : (getCompletedEntry (m := StateM IDState) group 0 ensureID).run state with
      | mk completed middle =>
          obtain ⟨preserves, known⟩ := getCompletedEntry_of_eq hc
          cases hp
                : (getPendingEntry (m := StateM IDState) groups streams ensureID).run
                    middle with
          | mk pending next =>
              obtain ⟨tailPreserves, keys⟩ := getPendingEntry_of_eq hp
              refine ⟨{ initial with
                  pending := initial.pending ++ pending
                  completed := initial.completed ++ [completed] }, next, ?_, ?_⟩
              · simp [eventLoop, StateT.run, StateT.bind, StateT.pure, bind, pure] at hc hp ⊢
                simp only [hc, hp]
              · exact ⟨preserves.trans tailPreserves,
                  ⟨pending, rfl, by simpa [pendingKeys, eventPending] using keys⟩,
                  ⟨[completed], rfl, .singleton (tailPreserves _ _ known)⟩⟩
  | groupFailure group errors | streamFailure group errors =>
      cases hc
            : (getCompletedEntry (m := StateM IDState) group errors ensureID).run
                state with
      | mk completed next =>
          obtain ⟨preserves, known⟩ := getCompletedEntry_of_eq hc
          refine ⟨
            { initial with completed := initial.completed ++ [completed] },
            next,
            ?_,
            ?_
          ⟩
          · simp [eventLoop, StateT.run, StateT.bind, StateT.pure, bind, pure] at hc ⊢
            rw [hc]
          · exact ⟨preserves, ⟨[], by simp, .nil⟩, ⟨[completed], rfl, .singleton known⟩⟩
  | streamValues stream values groups streams =>
      obtain ⟨preserves, _⟩ := ensureID_spec stream state
      cases hi : ensureID stream state with
      | mk id middle =>
          cases hp
                : (getPendingEntry (m := StateM IDState) groups streams ensureID).run
                    middle with
          | mk pending next =>
              simp only [hi] at preserves
              obtain ⟨tailPreserves, keys⟩ := getPendingEntry_of_eq hp
              refine ⟨
                {
                  initial with
                    pending := initial.pending ++ pending
                    incremental :=
                      initial.incremental
                      ++ [.list id (values.map StreamValue.item)
                            ((values.map StreamValue.errors).sum)]
                },
                next,
                ?_,
                ?_
              ⟩
              · simp [eventLoop, StateT.run, StateT.bind, StateT.pure, bind, pure, hi] at hp ⊢
                rw [hp]
              · exact ⟨preserves.trans tailPreserves,
                  ⟨pending, rfl, by simpa [pendingKeys, eventPending] using keys⟩,
                  ⟨[], by simp, .nil⟩⟩
  | streamSuccess stream =>
      cases hc
            : (getCompletedEntry (m := StateM IDState) stream 0 ensureID).run state with
      | mk completed next =>
          obtain ⟨preserves, known⟩ := getCompletedEntry_of_eq hc
          refine ⟨
            { initial with completed := initial.completed ++ [completed] },
            next,
            ?_,
            ?_
          ⟩
          · simp [eventLoop, StateT.run, StateT.bind, StateT.pure, bind, pure] at hc ⊢
            rw [hc]
          · exact ⟨preserves, ⟨[], by simp, .nil⟩, ⟨[completed], rfl, .singleton known⟩⟩
  | workQueueTermination =>
      exact ⟨
        { initial with hasNext := false },
        state,
        rfl,
        ⟨.refl _, ⟨[], by simp, .nil⟩, ⟨[], by simp, .nil⟩⟩
      ⟩

/-- Sequential mapper witnesses compose their ordered notice encodings. -/
theorem Mapped.append {state middle final : IDState}
    {initial update last : IncrementalStreamUpdateResult} {head tail : List WorkEvent}
    (h : Mapped state initial head update middle)
    (t : Mapped middle update tail last final)
    : Mapped state initial (head ++ tail) last final := by
  obtain ⟨hp, ⟨pending, ep, kp⟩, ⟨completed, ec, kc⟩⟩ := h
  obtain ⟨tp, ⟨more, em, km⟩, ⟨rest, er, kr⟩⟩ := t
  refine ⟨hp.trans tp, ⟨pending ++ more, ?_, ?_⟩, ⟨completed ++ rest, ?_, ?_⟩⟩
  · simp [em, ep, List.append_assoc]
  · simpa only [pendingKeys, List.flatMap_append, List.map_append]
      using (kp.mono tp).append km
  · simp [er, ec, List.append_assoc]
  · simpa only [completedKeys, List.flatMap_append, List.map_append]
      using (kc.mono tp).append kr

/-- The entire mapper loop preserves IDs and notice encodings, by list induction. -/
theorem loop_spec (events : List WorkEvent) (initial : IncrementalStreamUpdateResult)
    (state : IDState)
    : ∃ update next,
        (forIn events initial eventLoop).run state = (update, next)
        ∧ Mapped state initial events update next := by
  induction events generalizing initial state with
  | nil =>
      exact ⟨initial, state, rfl, ⟨.refl _, ⟨[], by simp, .nil⟩, ⟨[], by simp, .nil⟩⟩⟩
  | cons event rest ih =>
      obtain ⟨middle, ids, he, hs⟩ := eventLoop_spec event initial state
      obtain ⟨update, next, ht, hm⟩ := ih middle ids
      refine ⟨update, next, ?_, hs.append hm⟩
      simp only [List.forIn_cons]
      simp [StateT.run, StateT.bind, bind] at he ht ⊢
      simp only [he, ht]

/-- A work batch maps its ordered key occurrences to stable IDs, by the loop witness. -/
theorem mapWorkEventBatch_spec (events : List WorkEvent) (state : IDState)
    : let (update, next) := (mapWorkEventBatch events).run state
      Preserves state next
      ∧ Encodes next (pendingKeys events) (update.pending.map IncrementalPendingNotice.id)
      ∧ Encodes next (completedKeys events)
          (update.completed.map IncrementalCompletionNotice.id) := by
  obtain ⟨update, next, he, hp, ⟨pending, ep, kp⟩, ⟨completed, ec, kc⟩⟩ :=
    loop_spec events { hasNext := true } state
  rw [mapWorkEventBatch_loop, he]
  simpa [ep, ec] using And.intro hp (And.intro kp kc)

/-- An explicit batch-mapping result inherits the ordered encoding witness. -/
theorem mapWorkEventBatch_of_eq {events : List WorkEvent} {state next : IDState}
    {update : IncrementalStreamUpdateResult}
    (h : (mapWorkEventBatch events).run state = (update, next))
    : Preserves state next
      ∧ Encodes next (pendingKeys events) (update.pending.map IncrementalPendingNotice.id)
      ∧ Encodes next (completedKeys events)
          (update.completed.map IncrementalCompletionNotice.id) := by
  have fact := mapWorkEventBatch_spec events state
  rw [h] at fact
  exact fact

end GraphQL.IncrementalDelivery.Correctness.MapperIdentity
