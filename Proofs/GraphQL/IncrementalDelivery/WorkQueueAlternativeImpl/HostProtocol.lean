import GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PendingCounts

/-! Local host-protocol safety. Reachable cleanup is not acquired-resource coverage. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics (Occurrence)

private instance : LawfulBEq Occurrence where
  rfl := (ReferenceWorkQueue.occurrence_beq_iff_eq _ _).mpr rfl
  eq_of_beq := (ReferenceWorkQueue.occurrence_beq_iff_eq _ _).mp

private instance : LawfulBEq CleanupTarget where
  rfl := by
    intro target
    cases target with
    | task occurrence => exact beq_self_eq_true occurrence
    | stream key => exact beq_self_eq_true key
  eq_of_beq := by
    intro left right same
    cases left with
    | task left =>
        cases right with
        | task right => exact congrArg CleanupTarget.task (eq_of_beq same)
        | stream right => contradiction
    | stream left =>
        cases right with
        | task right => contradiction
        | stream right => exact congrArg CleanupTarget.stream (eq_of_beq same)

private abbrev insertTarget (targets : List CleanupTarget) (target : CleanupTarget) :=
  if targets.contains target then targets else targets ++ [target]

private theorem insertTarget_nodup (targets : List CleanupTarget) (target : CleanupTarget)
    (unique : targets.Nodup)
    : (insertTarget targets target).Nodup := by
  unfold insertTarget
  split
  · exact unique
  · rename_i fresh
    have absent : target ∉ targets := by simpa only [List.contains_iff_mem] using fresh
    rw [List.nodup_append]
    refine ⟨unique, by simp, ?_⟩
    intro left member right single
    simp only [List.mem_singleton] at single
    subst right
    exact fun same => absent (same ▸ member)

private theorem targetFold_nodup (pending targets : List CleanupTarget)
    (unique : targets.Nodup)
    : (pending.foldl insertTarget targets).Nodup := by
  induction pending generalizing targets with
  | nil => exact unique
  | cons target rest ih =>
      exact ih _ (insertTarget_nodup _ _ unique)

/-- Temporary identity deduplication loses no cancellation target. -/
theorem mem_uniqueCleanupTargets (target : CleanupTarget) (targets : List CleanupTarget)
    : target ∈ uniqueCleanupTargets targets ↔ target ∈ targets := by
  have loop (pending initial : List CleanupTarget)
      : target ∈ pending.foldl insertTarget initial ↔ target ∈ initial ++ pending := by
    induction pending generalizing initial with
    | nil => simp
    | cons head rest ih =>
        rw [List.foldl_cons, ih]
        unfold insertTarget
        split
        · rename_i present
          have listed : head ∈ initial := List.contains_iff_mem.mp present
          simp only [List.mem_append, List.mem_cons]
          constructor
          · exact fun member => member.imp_right Or.inr
          · rintro (earlier | same | later)
            · exact Or.inl earlier
            · exact Or.inl (same ▸ listed)
            · exact Or.inr later
        · simp [List.mem_append, List.mem_cons]
  exact (loop targets []).trans (by simp)

/-- Deduplication is valid even for raw cyclic/shared graphs; coverage is a separate question. -/
theorem State.cleanupTargets_nodup (state : State) : state.cleanupTargets.Nodup := by
  unfold State.cleanupTargets
  exact targetFold_nodup _ [] (by simp)

/-- One cleanup block per target, with source cancellation immediately before queue abort. -/
theorem State.cancel_effects (state : State)
    : state.cancel.2
      = if state.stopped then
          []
        else
          state.cleanupTargets.flatMap
            (fun target =>
              match target with
              | .task occurrence => [HostEffect.abortTask occurrence]
              | .stream key => [.cancelSource key, .abortStreamQueue key]) := by
  unfold State.cancel
  split <;> rfl

/-- The first operation of each cleanup block identifies the task or source being cleaned. -/
def HostEffect.cleanupStart? : HostEffect → Option CleanupTarget
  | .abortTask occurrence => some (.task occurrence)
  | .cancelSource key => some (.stream key)
  | _ => none

private theorem cleanupStarts_blocks (targets : List CleanupTarget)
    : (targets.flatMap
        (fun target =>
          match target with
          | .task occurrence => [HostEffect.abortTask occurrence]
          | .stream key => [.cancelSource key, .abortStreamQueue key])).filterMap
        HostEffect.cleanupStart?
      = targets := by
  induction targets with
  | nil => rfl
  | cons target rest ih =>
      cases target <;> simp [List.flatMap_cons, List.filterMap_cons,
        HostEffect.cleanupStart?, ih]

/-- The ordered cleanup blocks erase to exactly their task/source identity list. -/
theorem cleanupEffects_starts (targets : List CleanupTarget)
    : (targets.flatMap CleanupTarget.effects).filterMap HostEffect.cleanupStart?
      = targets :=
  cleanupStarts_blocks targets

/-- No task-abort or source-cancel request repeats within one stop transition. -/
theorem State.cancel_cleanupStarts_nodup (state : State)
    : (state.cancel.2.filterMap HostEffect.cleanupStart?).Nodup := by
  rw [State.cancel_effects]
  split
  · simp
  · rw [cleanupStarts_blocks]
    exact state.cleanupTargets_nodup

/-- Temporary identity deduplication always produces a unique ordered target list. -/
theorem uniqueCleanupTargets_nodup (targets : List CleanupTarget)
    : (uniqueCleanupTargets targets).Nodup :=
  targetFold_nodup _ [] List.nodup_nil

/-- Rejected registration's actual returned target projection is duplicate-free. -/
theorem State.disposeRejectedTasks_nodup (state : State) (integrated : IntegratedWork)
    (targets : List CleanupTarget)
    : (state.disposeRejectedTasks integrated targets).Nodup := by
  unfold State.disposeRejectedTasks uniqueCleanupTargets
  exact targetFold_nodup _ [] (by simp)

/-- Re-deduplicating an already unique target prefix leaves its order unchanged. -/
theorem uniqueCleanupTargets_eq_self (targets : List CleanupTarget)
    (unique : targets.Nodup)
    : uniqueCleanupTargets targets = targets := by
  have fold (remaining initial : List CleanupTarget) (unique : (initial ++ remaining).Nodup)
      : remaining.foldl insertTarget initial = initial ++ remaining := by
    induction remaining generalizing initial with
    | nil => simp
    | cons target rest ih =>
        have fresh : target ∉ initial := by
          intro member
          exact (List.nodup_append.mp unique).2.2 target member target (by simp) rfl
        have absent : initial.contains target = false := by simpa using fresh
        have nextUnique : ((initial ++ [target]) ++ rest).Nodup := by
          simpa [List.append_assoc] using unique
        simp only [List.foldl_cons, insertTarget, absent, Bool.false_eq_true, ↓reduceIte]
        rw [ih _ nextUnique]
        simp [List.append_assoc]
  exact (fold targets [] (by simpa using unique)).trans (by simp)

private theorem targetFold_prefix (pending initial : List CleanupTarget)
    : initial.IsPrefix (pending.foldl insertTarget initial) := by
  induction pending generalizing initial with
  | nil => exact List.prefix_refl _
  | cons target rest ih =>
      apply List.IsPrefix.trans (l₂ := insertTarget initial target) _ (ih _)
      unfold insertTarget
      split
      · exact List.prefix_refl _
      · exact ⟨[target], rfl⟩

/-- Reusing the deduplicated prefix preserves first-encounter order on an appended suffix. -/
theorem uniqueCleanupTargets_unique_append (initial pending : List CleanupTarget)
    : uniqueCleanupTargets (uniqueCleanupTargets initial ++ pending)
      = uniqueCleanupTargets (initial ++ pending) := by
  unfold uniqueCleanupTargets
  rw [List.foldl_append, List.foldl_append]
  change pending.foldl insertTarget (uniqueCleanupTargets (uniqueCleanupTargets initial))
    = pending.foldl insertTarget (uniqueCleanupTargets initial)
  rw [uniqueCleanupTargets_eq_self _ (uniqueCleanupTargets_nodup _)]

/-- Identity deduplication extends an already unique prefix without changing its order. -/
theorem uniqueCleanupTargets_append_prefix (initial pending : List CleanupTarget)
    (unique : initial.Nodup)
    : initial.IsPrefix (uniqueCleanupTargets (initial ++ pending)) := by
  unfold uniqueCleanupTargets
  rw [List.foldl_append]
  change initial.IsPrefix (pending.foldl insertTarget (uniqueCleanupTargets initial))
  rw [uniqueCleanupTargets_eq_self initial unique]
  exact targetFold_prefix _ _

/-- Actual rejected-task disposal extends the existing unique receipt target prefix. -/
theorem State.disposeRejectedTasks_prefix (state : State) (integrated : IntegratedWork)
    (targets : List CleanupTarget) (unique : targets.Nodup)
    : targets.IsPrefix (state.disposeRejectedTasks integrated targets) := by
  unfold State.disposeRejectedTasks uniqueCleanupTargets
  rw [List.foldl_append]
  change targets.IsPrefix ((integrated.rejectedTasks.flatMap
    (fun task => state.cancelTask task.occurrence)).foldl insertTarget (uniqueCleanupTargets targets))
  rw [uniqueCleanupTargets_eq_self targets unique]
  exact targetFold_prefix _ _

/-- Activation consumes the actual rejection projection without duplicating cleanup identities. -/
theorem State.startNewWork_targets_nodup (state : State)
    (newWork : ReferenceWorkQueue.NewWork) (integrated : IntegratedWork)
    (targets : List CleanupTarget) (unique : targets.Nodup)
    : (state.startNewWork newWork integrated targets).2.Nodup := by
  unfold State.startNewWork
  split
  · exact unique
  · exact State.disposeRejectedTasks_nodup _ _ _

/-- Activation only extends a receipt's already accumulated target identities. -/
theorem State.startNewWork_targets_prefix (state : State)
    (newWork : ReferenceWorkQueue.NewWork) (integrated : IntegratedWork)
    (targets : List CleanupTarget) (unique : targets.Nodup)
    : targets.IsPrefix (state.startNewWork newWork integrated targets).2 := by
  unfold State.startNewWork
  split
  · exact List.prefix_refl _
  · exact State.disposeRejectedTasks_prefix _ _ _ unique

@[simp]
theorem State.clearRecords_terminated (state : State)
    : state.clearRecords.queue.terminated = state.queue.terminated :=
  rfl

@[simp]
theorem State.cancel_terminated (state : State)
    : state.cancel.1.queue.terminated = state.queue.terminated := by
  unfold State.cancel
  split <;> rfl

@[simp]
theorem State.cancel_stopped (state : State) : state.cancel.1.stopped = true := by
  unfold State.cancel
  split
  · assumption
  · rfl

/-- An early stop cannot turn unfinished accounting into semantic work completion. -/
theorem State.cancel_unfinished (state : State)
    (unfinished : state.queue.terminated = false)
    : state.cancel.1.queue.terminated = false := by
  rw [State.cancel_terminated, unfinished]

/-- Cleanup cannot repeat after accounting is retired. -/
theorem State.cancel_idempotent (state : State)
    : state.cancel.1.cancel = (state.cancel.1, []) := by
  rw [State.cancel, State.cancel_stopped]
  rfl

/-- Source failure requests producer cancellation only, never an admitted queue abort. -/
theorem State.handleGraphEvent_streamFailure_effects (state : State)
    (stream : Execution.DeliveryNode) (errors : Nat)
    : (state.handleGraphEvent (.streamFailure stream errors)).2.2
      = if state.queue.rootStreams.contains stream.ref then
          [.cancelSource stream.ref]
        else
          [] :=
  rfl

@[simp]
theorem ResponseStreamCursor.onWorkQueueFinished_nextID (cursor : ResponseStreamCursor)
    : cursor.onWorkQueueFinished.publisher.ids.nextID = cursor.publisher.ids.nextID :=
  rfl

@[simp]
theorem ResponseStreamCursor.onWorkQueueFinished_ids (cursor : ResponseStreamCursor)
    : cursor.onWorkQueueFinished.publisher.ids.ids = [] :=
  rfl

@[simp]
theorem ResponseStreamCursor.onWorkQueueFinished_active (cursor : ResponseStreamCursor)
    : cursor.onWorkQueueFinished.publisher.active = [] :=
  rfl

@[simp]
theorem ResponseStreamCursor.close_terminated (cursor : ResponseStreamCursor)
    : cursor.close.1.queue.queue.terminated = cursor.queue.queue.terminated := by
  unfold ResponseStreamCursor.close
  split
  · rfl
  · exact cursor.queue.cancel_terminated

@[simp]
theorem ResponseStreamCursor.close_finished (cursor : ResponseStreamCursor)
    : cursor.close.1.finished = true := by
  unfold ResponseStreamCursor.close
  split
  · assumption
  · rfl

/-- Explicit close starts the finish hook after cleanup; it does not assert effect settlement. -/
theorem ResponseStreamCursor.close_effects (cursor : ResponseStreamCursor)
    (running : cursor.finished = false)
    : cursor.close.2 = cursor.queue.cancel.2 ++ [.responseFinished] := by
  simp only [ResponseStreamCursor.close, running, Bool.false_eq_true, ↓reduceIte]

@[simp]
theorem ResponseStreamCursor.close_nextID (cursor : ResponseStreamCursor)
    : cursor.close.1.publisher.ids.nextID = cursor.publisher.ids.nextID := by
  unfold ResponseStreamCursor.close
  split <;> rfl

theorem ResponseStreamCursor.close_ids (cursor : ResponseStreamCursor)
    (running : cursor.finished = false)
    : cursor.close.1.publisher.ids.ids = [] := by
  simp only [ResponseStreamCursor.close, running, Bool.false_eq_true, ↓reduceIte,
    ResponseStreamCursor.onWorkQueueFinished_ids]

theorem ResponseStreamCursor.close_active (cursor : ResponseStreamCursor)
    (running : cursor.finished = false)
    : cursor.close.1.publisher.active = [] := by
  simp only [ResponseStreamCursor.close, running, Bool.false_eq_true, ↓reduceIte,
    ResponseStreamCursor.onWorkQueueFinished_active]

theorem ResponseStreamCursor.close_idempotent (cursor : ResponseStreamCursor)
    : cursor.close.1.close = (cursor.close.1, []) := by
  rw [ResponseStreamCursor.close, ResponseStreamCursor.close_finished]
  rfl

/-- Closed readers do not reduce, map, acknowledge, allocate IDs, or start another finish hook. -/
theorem ResponseStreamCursor.handleBatch_finished (cursor : ResponseStreamCursor)
    (batch : List GraphEvent) (closed : cursor.finished = true)
    : cursor.handleBatch batch = (none, cursor, []) := by
  simp only [ResponseStreamCursor.handleBatch, closed, ↓reduceIte]

theorem ResponseStreamCursor.run_finished (cursor : ResponseStreamCursor)
    (inputs : List (List GraphEvent)) (closed : cursor.finished = true)
    : cursor.run inputs = ([], cursor, []) := by
  unfold ResponseStreamCursor.run
  induction inputs with
  | nil => rfl
  | cons batch rest ih =>
      simp only [List.foldl_cons, ResponseStreamCursor.handleBatch_finished _ _ closed,
        Option.toList_none, List.append_nil]
      exact ih

end GraphQL.IncrementalDelivery.AlternativeWorkQueue
