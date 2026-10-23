import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedDrainSources
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ResourceCacheRecords
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedTaskNodeKeys
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.StartupTaskProgress

/-! Cache-aware source records through concrete task starts and group removal. A changed
task rejection slot does not change the source's stored-value or attachment evidence.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open WorkQueueSemantics (Occurrence)

/-- Starting another computation preserves any existing active or buffered source record. -/
theorem sourceRecord_startTask {queue : ReferenceWorkQueue.State} {key}
    (represented : RecordTargetRepresented queue (.stream key)) (occurrence : Occurrence)
    (available : List (Occurrence × Nat))
    : RecordTargetRepresented (queue.startTask occurrence available) (.stream key) := by
  cases represented with
  | activeStream active =>
      have roots : (queue.startTask occurrence available).rootStreams = queue.rootStreams := by
        unfold ReferenceWorkQueue.State.startTask
        split
        · rfl
        · split <;> rfl
      exact .activeStream (by rw [roots]; exact active)
  | bufferedStream found stored held =>
      exact .bufferedStream
        (ReferenceWorkQueue.State.startTask_lookup_existing found occurrence available) stored held

/-- Active task starts retain source records before any released group can remove them. -/
theorem sourceRecord_startTasks (tasks : List Occurrence)
    (queue : ReferenceWorkQueue.State) (available : List (Occurrence × Nat)) {key}
    (represented : RecordTargetRepresented queue (.stream key))
    : RecordTargetRepresented
        (tasks.foldl (fun queue task => queue.startTask task available) queue)
        (.stream key) := by
  induction tasks generalizing queue with
  | nil => exact represented
  | cons task rest ih => exact ih _ (sourceRecord_startTask represented task available)

/-- Actual last-owner removal retains the source's record or emits its cleanup target. -/
theorem sourceRecord_removeGroup (state : State) (ref : Nat)
    (targets : List CleanupTarget) {key}
    (represented : RecordTargetRepresented state.queue (.stream key))
    : RecordTargetRepresented (state.removeGroup ref targets).1.queue (.stream key)
      ∨ .stream key ∈ (state.removeGroup ref targets).2 := by
  cases represented with
  | activeStream active =>
      exact .inl (.activeStream (by rw [State.removeGroup_rootStreams]; exact active))
  | @bufferedStream occurrence node _ found stored held =>
      rcases (FusedRemovalSafety_holds state ref targets).2.2 occurrence node key found held
          with kept | requested
      · exact .inl (.bufferedStream kept stored held)
      · exact .inr requested

/-- Cached group startup retains an active/buffered source or requests its actual cleanup.
Task rejection slots may change; the represented source identity and value stay explicit.
-/
theorem sourceRecord_startGroup_available (state : State)
    (keys : state.queue.TaskNodeKeysUnique) (ref : Nat) (targets : List CleanupTarget)
    (available : List (Occurrence × Nat)) {key}
    (represented : RecordTargetRepresented state.queue (.stream key))
    : RecordTargetRepresented (state.startGroup ref targets available).1.queue
        (.stream key)
      ∨ .stream key ∈ (state.startGroup ref targets available).2.1 := by
  have exposed := (streamRecord_cacheTaskFailures_iff keys available key).mpr represented
  unfold State.startGroup
  dsimp only
  split
  · exact .inl exposed
  · split
    · exact .inl (sourceRecord_startTasks _ _ available exposed)
    · exact sourceRecord_removeGroup _ _ targets exposed

private theorem sourceRecord_startStream {queue : ReferenceWorkQueue.State} {key}
    (represented : RecordTargetRepresented queue (.stream key)) (ref : Nat)
    : RecordTargetRepresented (queue.startStream ref) (.stream key) := by
  cases represented with
  | activeStream active =>
      exact .activeStream (queue.startStream_rootStreams_mono ref active)
  | bufferedStream found stored held =>
      unfold ReferenceWorkQueue.State.startStream
      split <;> exact .bufferedStream found stored held

/-- The complete concrete startup loop preserves source records or accumulates their
actual cleanup targets. Rejection-slot changes are allowed throughout its supplied snapshot.
-/
theorem sourceRecord_startNewWork_available (state : State)
    (keys : state.queue.TaskNodeKeysUnique) (more : ReferenceWorkQueue.NewWork)
    (integrated : IntegratedWork) (targets : List CleanupTarget)
    (available : List (Occurrence × Nat)) {key}
    (represented : RecordTargetRepresented state.queue (.stream key))
    : RecordTargetRepresented
        (state.startNewWork more integrated targets available).1.queue (.stream key)
      ∨ .stream key ∈ (state.startNewWork more integrated targets available).2.1 := by
  have streams (nodes : List Execution.DeliveryNode) (queue : ReferenceWorkQueue.State)
      (keys : queue.TaskNodeKeysUnique)
      (represented : RecordTargetRepresented queue (.stream key))
      : let final := nodes.foldl (fun current stream => current.startStream stream.ref) queue
        final.TaskNodeKeysUnique ∧ RecordTargetRepresented final (.stream key) := by
    induction nodes generalizing queue with
    | nil => exact ⟨keys, represented⟩
    | cons node rest ih =>
        have nextKeys : (queue.startStream node.ref).TaskNodeKeysUnique := by
          unfold ReferenceWorkQueue.State.startStream
          split <;> exact keys
        exact ih _ nextKeys (sourceRecord_startStream represented node.ref)
  have tasks (nodes : List ReferenceWorkQueue.Task) (queue : ReferenceWorkQueue.State)
      (keys : queue.TaskNodeKeysUnique)
      (represented : RecordTargetRepresented queue (.stream key))
      : let final := nodes.foldl
          (fun current task => current.startTask task.occurrence available) queue
        final.TaskNodeKeysUnique ∧ RecordTargetRepresented final (.stream key) := by
    induction nodes generalizing queue with
    | nil => exact ⟨keys, represented⟩
    | cons task rest ih =>
        exact ih _ (keys.startTask task.occurrence available)
          (sourceRecord_startTask represented task.occurrence available)
  have groups (refs : WorkQueueSemantics.NodeRefs)
      (acc : State × List CleanupTarget × List ReferenceWorkQueue.GroupFailureEvent)
      (keys : acc.1.queue.TaskNodeKeysUnique) (unique : acc.2.1.Nodup)
      (prior : RecordTargetRepresented acc.1.queue (.stream key) ∨ .stream key ∈ acc.2.1)
      : let final := refs.foldl
          (fun (current, targets, failures) ref =>
            let (next, targets, queued) := current.startGroup ref targets available
            (next, targets, failures ++ queued)) acc
        RecordTargetRepresented final.1.queue (.stream key) ∨ .stream key ∈ final.2.1 := by
    induction refs generalizing acc with
    | nil => exact prior
    | cons ref rest ih =>
        rcases acc with ⟨current, targets, failures⟩
        have nextKeys := State.startGroup_taskNodeKeysUnique keys ref targets available
        have extending := startGroup_targets current ref targets unique available
        have progress : RecordTargetRepresented
            (current.startGroup ref targets available).1.queue (.stream key)
            ∨ .stream key ∈ (current.startGroup ref targets available).2.1 := by
          rcases prior with kept | requested
          · exact sourceRecord_startGroup_available current keys ref targets available kept
          · exact .inr (extending.2.sublist.subset requested)
        cases step : current.startGroup ref targets available with
        | mk next output =>
            cases output with
            | mk nextTargets notices =>
                rw [step] at nextKeys extending progress
                simpa only [List.foldl_cons, step]
                  using ih (next, nextTargets, failures ++ notices) nextKeys extending.1
                    progress
  let seeded : ReferenceWorkQueue.State :=
    { state.queue with rootGroups := state.queue.rootGroups
      ++ more.newGroups.map Execution.DeliveryNode.ref }
  have seededRecord : RecordTargetRepresented seeded (.stream key) := by
    cases represented with
    | activeStream active => exact .activeStream active
    | bufferedStream found stored held => exact .bufferedStream found stored held
  have installed := streams more.newStreams seeded keys seededRecord
  have active := tasks integrated.activeTasks _ installed.1 installed.2
  unfold State.startNewWork
  split
  · exact .inl represented
  · exact groups _ _ active.1 (State.disposeRejectedTasks_nodup _ _ _) (.inl active.2)

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
