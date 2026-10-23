import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.HostProtocol
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationStreamReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationTaskReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedCleanupTargets

/-! Observations of the actual interleaved registration effects, not a replayed observer. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics (Occurrence)

-----------------------------------------------------------------------------------------
-- Effect projections observe actual inline operations
-----------------------------------------------------------------------------------------

/-- The producer identity of an actual whole-work handoff; cleanup and acknowledgement erase. -/
def HostEffect.adoptedProducer? : HostEffect → Option Occurrence
  | .adopt occurrence => some occurrence
  | _ => none

/-- The source identity of a consumed receipt acknowledgement; handoff and cleanup erase. -/
def HostEffect.acknowledgedStream? : HostEffect → Option Nat
  | .acknowledge key => some key
  | _ => none

/-- Count finish-hook starts, not promises settling or semantic work termination. -/
def HostEffect.isResponseFinished : HostEffect → Bool
  | .responseFinished => true
  | _ => false

/-- Ordered cleanup blocks never adopt newly returned work. -/
theorem cleanupEffects_adoptedProducers (targets : List CleanupTarget)
    : (targets.flatMap CleanupTarget.effects).filterMap HostEffect.adoptedProducer?
      = [] := by
  induction targets with
  | nil => rfl
  | cons target rest ih =>
      rw [List.flatMap_cons, List.filterMap_append, ih]
      cases target <;> rfl

/-- Cleanup requests are not acknowledgements of a consumed input receipt. -/
theorem cleanupEffects_acknowledgedStreams (targets : List CleanupTarget)
    : (targets.flatMap CleanupTarget.effects).filterMap HostEffect.acknowledgedStream?
      = [] := by
  induction targets with
  | nil => rfl
  | cons target rest ih =>
      rw [List.flatMap_cons, List.filterMap_append, ih]
      cases target <;> rfl

/-- Ordered cleanup requests cannot start the response-finished hook. -/
theorem cleanupEffects_noFinish (targets : List CleanupTarget)
    : (targets.flatMap CleanupTarget.effects).countP HostEffect.isResponseFinished
      = 0 := by
  induction targets with
  | nil => rfl
  | cons target rest ih =>
      cases target <;> simp [CleanupTarget.effects, cancelStream, HostEffect.isResponseFinished, ih]

private abbrev streamEffects (acc : StreamRegistrationAcc) := acc.2.2.2.2.2.1
private abbrev streamTargets (acc : StreamRegistrationAcc) := acc.2.2.2.2.1

private abbrev receiptEffects (acc : StreamRegistrationAcc) (key : Nat)
    (available : List (WorkQueueSemantics.Occurrence × Nat) := []) :=
  streamEffects acc
  ++ [.acknowledge key]
  ++ ((acc.1.drainReadyGroups (streamTargets acc) available).2.2.1.drop
        (streamTargets acc).length).flatMap
      CleanupTarget.effects

private theorem streamStep_targets_nodup (acc : StreamRegistrationAcc)
    (item : ReferenceWorkQueue.StreamItem) (unique : (streamTargets acc).Nodup)
    (available : List (Occurrence × Nat) := [])
    : (streamTargets (streamRegistrationStep acc item available)).Nodup :=
  State.startNewWork_targets_nodup _ _ _ _ unique available

private theorem streamStep_targets_prefix (acc : StreamRegistrationAcc)
    (item : ReferenceWorkQueue.StreamItem) (unique : (streamTargets acc).Nodup)
    (available : List (Occurrence × Nat) := [])
    : (streamTargets acc).IsPrefix
        (streamTargets (streamRegistrationStep acc item available)) :=
  State.startNewWork_targets_prefix _ _ _ _ unique available

private theorem streamFold_cleanupTargets (items : List ReferenceWorkQueue.StreamItem)
    (acc : StreamRegistrationAcc) (unique : (streamTargets acc).Nodup)
    (tracked : (streamEffects acc).filterMap HostEffect.cleanupStart? = streamTargets acc)
    (available : List (Occurrence × Nat) := [])
    : (streamTargets
        (items.foldl (fun acc item => streamRegistrationStep acc item available)
          acc)).Nodup
      ∧ (streamEffects
          (items.foldl (fun acc item => streamRegistrationStep acc item available)
            acc)).filterMap
          HostEffect.cleanupStart?
        = streamTargets
            (items.foldl (fun acc item => streamRegistrationStep acc item available)
              acc) := by
  induction items generalizing acc with
  | nil => exact ⟨unique, tracked⟩
  | cons item rest ih =>
      have nextUnique := streamStep_targets_nodup acc item unique available
      have nextTracked : (streamEffects (streamRegistrationStep acc item available)).filterMap
          HostEffect.cleanupStart? = streamTargets (streamRegistrationStep acc item available) := by
        have extending := streamStep_targets_prefix acc item unique available
        obtain ⟨more, joined⟩ := extending
        change (streamEffects acc ++ [HostEffect.adopt item.occurrence]
          ++ ((streamTargets (streamRegistrationStep acc item available)).drop
            (streamTargets acc).length).flatMap CleanupTarget.effects).filterMap
              HostEffect.cleanupStart? = _
        rw [List.filterMap_append, List.filterMap_append, cleanupEffects_starts, tracked,
          ← joined]
        simp [HostEffect.cleanupStart?]
      exact ih _ nextUnique nextTracked

/-- The actual receipt's cumulative unique targets are exactly its cleanup-start projection.
The initial trace must account for its initial target prefix; no acquisition premise is used.
-/
theorem streamRegistrationFold_cleanupTargets (items : List ReferenceWorkQueue.StreamItem)
    (acc : StreamRegistrationAcc) (unique : (streamTargets acc).Nodup)
    (tracked : (streamEffects acc).filterMap HostEffect.cleanupStart? = streamTargets acc)
    (available : List (Occurrence × Nat) := [])
    : (streamTargets
        (items.foldl (fun acc item => streamRegistrationStep acc item available)
          acc)).Nodup
      ∧ (streamEffects
          (items.foldl (fun acc item => streamRegistrationStep acc item available)
            acc)).filterMap
          HostEffect.cleanupStart?
        = streamTargets
            (items.foldl (fun acc item => streamRegistrationStep acc item available)
              acc) :=
  streamFold_cleanupTargets items acc unique tracked available

/-- Inline disposal carries its cumulative cleanup prefix through the entire receipt. -/
theorem streamRegistrationFold_targets_prefix (items : List ReferenceWorkQueue.StreamItem)
    (acc : StreamRegistrationAcc) (unique : (streamTargets acc).Nodup)
    (available : List (Occurrence × Nat) := [])
    : (streamTargets acc).IsPrefix
        (streamTargets
          (items.foldl (fun acc item => streamRegistrationStep acc item available)
            acc)) := by
  induction items generalizing acc with
  | nil => exact List.prefix_refl _
  | cons item rest ih =>
      exact (streamStep_targets_prefix acc item unique available).trans
        (ih _ (streamStep_targets_nodup acc item unique available))

private theorem streamFold_adoptions (items : List ReferenceWorkQueue.StreamItem)
    (acc : StreamRegistrationAcc)
    (available : List (Occurrence × Nat) := [])
    : (streamEffects
        (items.foldl (fun acc item => streamRegistrationStep acc item available)
          acc)).filterMap
        HostEffect.adoptedProducer?
      = (streamEffects acc).filterMap HostEffect.adoptedProducer?
        ++ items.map (·.occurrence) := by
  induction items generalizing acc with
  | nil => simp
  | cons item rest ih =>
      rw [List.foldl_cons, ih]
      simp [streamEffects, streamRegistrationStep, List.filterMap_append,
        cleanupEffects_adoptedProducers, HostEffect.adoptedProducer?, List.append_assoc]

private theorem streamFold_noFinish (items : List ReferenceWorkQueue.StreamItem)
    (acc : StreamRegistrationAcc)
    (available : List (WorkQueueSemantics.Occurrence × Nat) := [])
    : (streamEffects
        (items.foldl (fun acc item => streamRegistrationStep acc item available)
          acc)).countP
        HostEffect.isResponseFinished
      = (streamEffects acc).countP HostEffect.isResponseFinished := by
  induction items generalizing acc with
  | nil => rfl
  | cons item rest ih =>
      rw [List.foldl_cons, ih]
      simp only [streamEffects, streamRegistrationStep, List.countP_append,
        cleanupEffects_noFinish, HostEffect.isResponseFinished, List.countP_cons,
        List.countP_nil, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]

private theorem streamFold_acknowledgements (items : List ReferenceWorkQueue.StreamItem)
    (acc : StreamRegistrationAcc)
    : (streamEffects (items.foldl streamRegistrationStep acc)).filterMap
        HostEffect.acknowledgedStream?
      = (streamEffects acc).filterMap HostEffect.acknowledgedStream? := by
  induction items generalizing acc with
  | nil => rfl
  | cons item rest ih =>
      rw [List.foldl_cons, ih]
      simp only [streamEffects, streamRegistrationStep, List.filterMap_append,
        cleanupEffects_acknowledgedStreams, List.filterMap_cons, List.filterMap_nil,
        HostEffect.acknowledgedStream?, List.append_nil]

-----------------------------------------------------------------------------------------
-- FIFO handoffs and the acknowledgement boundary of actual item consumption
-----------------------------------------------------------------------------------------

/-- A receipt's actual trace adopts exactly its consumed items, in FIFO order.
Rejected-task cleanup may occur between these handoffs; it is not moved after acknowledgement.
-/
theorem State.streamItems_adoptedProducers (state : State)
    (stream : Execution.DeliveryNode) (items : List ReferenceWorkQueue.StreamItem)
    (available : List (Occurrence × Nat) := [])
    : (state.streamItems stream items available).2.2.1.filterMap
        HostEffect.adoptedProducer?
      = if state.queue.rootStreams.contains stream.ref then
          items.map (·.occurrence)
        else
          [] := by
  unfold State.streamItems
  split
  · rename_i inactive
    have absent : state.queue.rootStreams.contains stream.ref = false := by simpa using inactive
    rw [absent]
    rfl
  · rename_i active
    have present : state.queue.rootStreams.contains stream.ref = true := by simpa using active
    change (receiptEffects (items.foldl (fun acc item => streamRegistrationStep acc item available)
      (state, [], [], [], [], [], []))
      stream.ref available).filterMap HostEffect.adoptedProducer? = _
    simp only [receiptEffects, List.filterMap_append, streamFold_adoptions, streamEffects,
      List.filterMap_cons, List.filterMap_nil, HostEffect.adoptedProducer?,
      cleanupEffects_adoptedProducers, present, ↓reduceIte, List.nil_append, List.append_nil]

/-- Acknowledgement ends item consumption; any subsequent inline operations are precisely
cleanup from ready draining. Ignored/stale receipts have empty consumption and cleanup.
-/
theorem State.streamItems_consumptionBoundary (state : State)
    (stream : Execution.DeliveryNode) (items : List ReferenceWorkQueue.StreamItem)
    : ∃ (earlier : List HostEffect) (targets : List CleanupTarget),
        (state.streamItems stream items).2.2.1
        = earlier
          ++ [.acknowledge stream.ref]
          ++ targets.flatMap CleanupTarget.effects := by
  unfold State.streamItems
  split
  · exact ⟨[], [], rfl⟩
  · exact ⟨_, _, rfl⟩

/-- Exactly one acknowledgement belongs to each actual receipt, including inactive/empty input. -/
theorem State.streamItems_acknowledges_once (state : State)
    (stream : Execution.DeliveryNode) (items : List ReferenceWorkQueue.StreamItem)
    : (state.streamItems stream items).2.2.1.filterMap HostEffect.acknowledgedStream?
      = [stream.ref] := by
  unfold State.streamItems
  split
  · rfl
  · change (receiptEffects (items.foldl streamRegistrationStep (state, [], [], [], [], [], []))
      stream.ref).filterMap HostEffect.acknowledgedStream? = _
    simp only [receiptEffects, List.filterMap_append, streamFold_acknowledgements, streamEffects,
      cleanupEffects_acknowledgedStreams, List.filterMap_cons, HostEffect.acknowledgedStream?,
      List.filterMap_nil, List.nil_append, List.append_nil]

/-- Earlier item cleanup and the post-ACK drain suffix telescope to the actual cumulative
target list. This equality licenses any returned target by a real receipt effect, without
assuming that all cleanup happens before the acknowledgement.
-/
theorem State.streamItems_cleanupStarts_eq (state : State)
    (stream : Execution.DeliveryNode) (items : List ReferenceWorkQueue.StreamItem)
    (active : state.queue.rootStreams.contains stream.ref = true)
    (available : List (Occurrence × Nat) := [])
    : let acc :=
        items.foldl (fun acc item => streamRegistrationStep acc item available)
          (state, [], [], [], [], [], [])
      (state.streamItems stream items available).2.2.1.filterMap HostEffect.cleanupStart?
      = (acc.1.drainReadyGroups (streamTargets acc) available).2.2.1 := by
  simp only [State.streamItems, active, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  let acc := items.foldl (fun acc item => streamRegistrationStep acc item available)
    (state, [], [], [], [], [], [])
  have tracked : (streamTargets acc).Nodup
      ∧ (streamEffects acc).filterMap HostEffect.cleanupStart? = streamTargets acc :=
    streamFold_cleanupTargets items (state, [], [], [], [], [], []) List.nodup_nil rfl available
  have later := acc.1.drainReadyGroups_targets (streamTargets acc) tracked.1 available
  change (receiptEffects acc stream.ref available).filterMap HostEffect.cleanupStart? = _
  simp only [receiptEffects, List.filterMap_append, List.filterMap_cons, HostEffect.cleanupStart?,
    List.filterMap_nil, List.append_nil, cleanupEffects_starts, tracked.2]
  obtain ⟨more, joined⟩ := later.2
  rw [← joined]
  simp

/-- The actual multi-item receipt requests each rejected-task/source cleanup identity at most once.
Witness: every activation preserves the unique prefix, so emitting only the new suffix telescopes
to the returned target list. No global source-history ledger or generated-work premise is needed.
-/
theorem State.streamItems_cleanupStarts_nodup (state : State)
    (stream : Execution.DeliveryNode) (items : List ReferenceWorkQueue.StreamItem)
    : ((state.streamItems stream items).2.2.1.filterMap
        HostEffect.cleanupStart?).Nodup := by
  unfold State.streamItems
  split
  · exact List.nodup_nil
  · let acc := items.foldl streamRegistrationStep (state, [], [], [], [], [], [])
    have tracked : (streamTargets acc).Nodup
        ∧ (streamEffects acc).filterMap HostEffect.cleanupStart? = streamTargets acc :=
      streamFold_cleanupTargets items (state, [], [], [], [], [], []) List.nodup_nil rfl
    have later := acc.1.drainReadyGroups_targets (streamTargets acc) tracked.1
    change ((receiptEffects acc stream.ref).filterMap HostEffect.cleanupStart?).Nodup
    simp only [receiptEffects, List.filterMap_append, List.filterMap_cons, HostEffect.cleanupStart?,
      List.filterMap_nil, List.append_nil, cleanupEffects_starts, tracked.2]
    have telescoped : streamTargets acc ++
        ((acc.1.drainReadyGroups (streamTargets acc)).2.2.1.drop (streamTargets acc).length)
        = (acc.1.drainReadyGroups (streamTargets acc)).2.2.1 := by
      obtain ⟨more, joined⟩ := later.2
      rw [← joined]
      simp
    rw [telescoped]
    exact later.1

/-- One task-success registration emits a duplicate-free rejected-task/source cleanup block. -/
theorem State.taskSuccess_cleanupStarts_nodup (state : State) (occurrence : Occurrence)
    (result : ReferenceWorkQueue.TaskResult)
    : ((state.taskSuccess occurrence result).2.2.1.filterMap
        HostEffect.cleanupStart?).Nodup := by
  cases found : state.queue.taskNode? occurrence with
  | none => simp only [State.taskSuccess, found, List.filterMap_nil, List.nodup_nil]
  | some node =>
      rw [state.taskSuccess_eq occurrence result node found]
      simp only [List.filterMap_append, List.filterMap_cons, HostEffect.cleanupStart?,
          List.filterMap_nil, List.nil_append, cleanupEffects_starts]
      apply (State.drainReadyGroups_targets _ _ ?_).1
      exact State.startNewWork_targets_nodup _ _ _ [] (by simp)

/-- Task-success handoff projection observes the accepting producer, not any cleanup target. -/
theorem State.taskSuccess_adoptedProducers (state : State) (occurrence : Occurrence)
    (result : ReferenceWorkQueue.TaskResult)
    (available : List (Occurrence × Nat) := [])
    : (state.taskSuccess occurrence result available).2.2.1.filterMap
        HostEffect.adoptedProducer?
      = match state.queue.taskNode? occurrence with
        | none => []
        | some _ => [occurrence] := by
  cases found : state.queue.taskNode? occurrence with
  | none => simp only [State.taskSuccess, found, List.filterMap_nil]
  | some node =>
      rw [state.taskSuccess_eq occurrence result node found available]
      simp only [List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
        HostEffect.adoptedProducer?, cleanupEffects_adoptedProducers, List.append_nil]

/-- Successful task handoff/disposal cannot acknowledge a stream receipt. -/
theorem State.taskSuccess_acknowledgedStreams (state : State) (occurrence : Occurrence)
    (result : ReferenceWorkQueue.TaskResult)
    : (state.taskSuccess occurrence result).2.2.1.filterMap HostEffect.acknowledgedStream?
      = [] := by
  cases found : state.queue.taskNode? occurrence with
  | none => simp only [State.taskSuccess, found, List.filterMap_nil]
  | some node =>
      rw [state.taskSuccess_eq occurrence result node found]
      simp only [List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
          HostEffect.acknowledgedStream?, cleanupEffects_acknowledgedStreams, List.append_nil]

-----------------------------------------------------------------------------------------
-- Graph dispatch cannot start the response-finished hook
-----------------------------------------------------------------------------------------

/-- Registration/settlement effects contain only handoff and cleanup operations. -/
theorem State.taskSuccess_noFinish (state : State) (occurrence : Occurrence)
    (result : ReferenceWorkQueue.TaskResult)
    (available : List (WorkQueueSemantics.Occurrence × Nat) := [])
    : (state.taskSuccess occurrence result available).2.2.1.countP
        HostEffect.isResponseFinished
      = 0 := by
  cases found : state.queue.taskNode? occurrence with
  | none => simp only [State.taskSuccess, found, List.countP_nil]
  | some node =>
      rw [state.taskSuccess_eq occurrence result node found available]
      simp only [List.countP_append, cleanupEffects_noFinish,
          HostEffect.isResponseFinished, List.countP_cons, List.countP_nil,
          Bool.false_eq_true, ↓reduceIte, Nat.add_zero]

/-- Receipt effects preserve handoff/disposal order but never start reader completion. -/
theorem State.streamItems_noFinish (state : State) (stream : Execution.DeliveryNode)
    (items : List ReferenceWorkQueue.StreamItem)
    (available : List (WorkQueueSemantics.Occurrence × Nat) := [])
    : (state.streamItems stream items available).2.2.1.countP
        HostEffect.isResponseFinished
      = 0 := by
  unfold State.streamItems
  split
  · rfl
  · change (receiptEffects (items.foldl (fun acc item => streamRegistrationStep acc item available)
      (state, [], [], [], [], [], [])) stream.ref available).countP HostEffect.isResponseFinished
        = 0
    simp only [receiptEffects, List.countP_append, streamFold_noFinish _ _ available, streamEffects,
      HostEffect.isResponseFinished, List.countP_cons, List.countP_nil,
      Bool.false_eq_true, ↓reduceIte, cleanupEffects_noFinish, Nat.add_zero]

/-- A failed task produces only actual cleanup blocks, not handoff or reader completion. -/
theorem State.taskFailure_cleanupEffects (state : State) (occurrence : Occurrence)
    (errors : Nat)
    (available : List (WorkQueueSemantics.Occurrence × Nat) := [])
    : ∃ targets : List CleanupTarget,
        (state.handleGraphEvent (.taskFailure occurrence errors) available).2.2.1
        = targets.flatMap CleanupTarget.effects :=
  ⟨_, rfl⟩

/-- Failure dispatch converts cleanup targets without starting reader completion. -/
theorem State.taskFailure_noFinish (state : State) (occurrence : Occurrence)
    (errors : Nat)
    (available : List (WorkQueueSemantics.Occurrence × Nat) := [])
    : (state.handleGraphEvent (.taskFailure occurrence errors) available).2.2.1.countP
        HostEffect.isResponseFinished
      = 0 := by
  obtain ⟨targets, same⟩ := state.taskFailure_cleanupEffects occurrence errors available
  rw [same, cleanupEffects_noFinish]

/-- All actual single-event handlers leave finish-hook starts to the response reader. -/
theorem State.handleGraphEvent_noFinish (state : State) (event : GraphEvent)
    (available : List (WorkQueueSemantics.Occurrence × Nat) := [])
    : (state.handleGraphEvent event available).2.2.1.countP HostEffect.isResponseFinished
      = 0 := by
  let current := { state with queue := state.queue.cacheTaskFailures available }
  cases event with
  | taskSuccess occurrence result =>
      exact current.taskSuccess_noFinish occurrence result available
  | streamItems stream items => exact current.streamItems_noFinish stream items available
  | taskFailure occurrence errors =>
      exact state.taskFailure_noFinish occurrence errors available
  | groupFailure | streamSuccess => rfl
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent]
      split <;> rfl

end GraphQL.IncrementalDelivery.AlternativeWorkQueue
