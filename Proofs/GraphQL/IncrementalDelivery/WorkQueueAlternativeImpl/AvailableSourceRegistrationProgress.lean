import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.SourceRecordRegistration
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.AvailableSourceStartup

/-! Existing source records through actual cache-aware registration and receipt preparation.
Disposal during an earlier item remains in the same cumulative inline effect trace.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open WorkQueueSemantics (Occurrence)

/-- Empty-shell pruning leaves source roots and buffered task records unchanged. -/
theorem sourceRecord_pruneEmptyGroups (queue : ReferenceWorkQueue.State)
    (groups : List Execution.DeliveryNode) {key}
    (represented : RecordTargetRepresented queue (.stream key))
    : RecordTargetRepresented (queue.pruneEmptyGroups groups).1 (.stream key) := by
  cases represented with
  | activeStream active =>
      exact .activeStream
        (by rw [ReferenceWorkQueue.State.pruneEmptyGroups_rootStreams]; exact active)
  | bufferedStream found stored held =>
      exact .bufferedStream
        (by
          simpa only [ReferenceWorkQueue.State.taskNode?,
            ReferenceWorkQueue.State.pruneEmptyGroups_taskNodes]
            using found)
        stored held

/-- One actual receipt item retains an existing source record or requests its cleanup. -/
theorem streamRegistrationStep_sourceRecord_available (acc : StreamRegistrationAcc)
    (keys : acc.1.queue.TaskNodeKeysUnique) (item : ReferenceWorkQueue.StreamItem)
    (available : List (Occurrence × Nat)) {key}
    (represented : RecordTargetRepresented acc.1.queue (.stream key))
    : RecordTargetRepresented (streamRegistrationStep acc item available).1.queue
        (.stream key)
      ∨ .stream key ∈ (streamRegistrationStep acc item available).2.2.2.2.1 := by
  let registered := acc.1.maybeIntegrateWork item.work
  let pruned := registered.1.queue.pruneEmptyGroups registered.2.newGroups
  let preparing : State := { registered.1 with queue := pruned.1 }
  have registeredRecord := State.maybeIntegrateWork_sourceRecord acc.1 item.work none represented
  have preparedRecord := sourceRecord_pruneEmptyGroups registered.1.queue
    registered.2.newGroups registeredRecord
  have registeredKeys := State.maybeIntegrateWork_taskNodeKeysUnique (state := acc.1) keys item.work
  have preparedKeys := registeredKeys.pruneEmptyGroups registered.2.newGroups
  exact sourceRecord_startNewWork_available preparing preparedKeys
    { registered.2.newWork with newGroups := pruned.2 } registered.2 acc.2.2.2.2.1
    available preparedRecord

/-- Actual item preparation preserves the same computation-key invariant. -/
theorem streamRegistrationStep_taskKeys_available (acc : StreamRegistrationAcc)
    (keys : acc.1.queue.TaskNodeKeysUnique) (item : ReferenceWorkQueue.StreamItem)
    (available : List (Occurrence × Nat))
    : (streamRegistrationStep acc item available).1.queue.TaskNodeKeysUnique := by
  let registered := acc.1.maybeIntegrateWork item.work
  let pruned := registered.1.queue.pruneEmptyGroups registered.2.newGroups
  let preparing : State := { registered.1 with queue := pruned.1 }
  have preparedKeys := (State.maybeIntegrateWork_taskNodeKeysUnique (state := acc.1)
    keys item.work).pruneEmptyGroups registered.2.newGroups
  exact State.startNewWork_taskNodeKeysUnique (state := preparing) preparedKeys
    { registered.2.newWork with newGroups := pruned.2 } registered.2 acc.2.2.2.2.1 available

/-- The receipt fold retains a source record or its actual cumulative cleanup target. -/
theorem streamRegistrationFold_sourceRecord_available
    (items : List ReferenceWorkQueue.StreamItem) (acc : StreamRegistrationAcc)
    (keys : acc.1.queue.TaskNodeKeysUnique) (unique : acc.2.2.2.2.1.Nodup)
    (available : List (Occurrence × Nat)) {key}
    (prior
      : RecordTargetRepresented acc.1.queue (.stream key) ∨ .stream key ∈ acc.2.2.2.2.1)
    : let final :=
        items.foldl (fun acc item => streamRegistrationStep acc item available) acc
      RecordTargetRepresented final.1.queue (.stream key)
      ∨ .stream key ∈ final.2.2.2.2.1 := by
  induction items generalizing acc with
  | nil => exact prior
  | cons item rest ih =>
      let next := streamRegistrationStep acc item available
      have nextKeys := streamRegistrationStep_taskKeys_available acc keys item available
      have nextUnique : next.2.2.2.2.1.Nodup :=
        State.startNewWork_targets_nodup _ _ _ _ unique available
      have extending : acc.2.2.2.2.1.IsPrefix next.2.2.2.2.1 :=
        State.startNewWork_targets_prefix _ _ _ _ unique available
      apply ih next nextKeys nextUnique
      rcases prior with represented | requested
      · exact streamRegistrationStep_sourceRecord_available acc keys item available represented
      · exact .inr (extending.sublist.subset requested)

/-- Every cumulative prepared source target appears in the same receipt's real effects. -/
theorem State.streamItems_preparedSourceTarget_cancelled (state : State)
    (stream : Execution.DeliveryNode) (items : List ReferenceWorkQueue.StreamItem)
    (active : state.queue.rootStreams.contains stream.ref = true)
    (available : List (Occurrence × Nat)) {key}
    (target
      : .stream key
        ∈ (items.foldl
            (fun acc item => streamRegistrationStep acc item available)
            (state, [], [], [], [], [], [])).2.2.2.2.1)
    : .cancelSource key ∈ (state.streamItems stream items available).2.2.1 := by
  let initial : StreamRegistrationAcc := (state, [], [], [], [], [], [])
  let final := items.foldl (fun acc item => streamRegistrationStep acc item available) initial
  have tracked := (streamRegistrationFold_cleanupTargets items initial
    List.nodup_nil rfl available).2
  have listed : CleanupTarget.stream key ∈ final.2.2.2.2.2.1.filterMap HostEffect.cleanupStart? :=
    tracked.symm ▸ target
  obtain ⟨effect, emitted, selected⟩ := List.mem_filterMap.mp listed
  have same : effect = .cancelSource key := by
    cases effect <;> simp_all [HostEffect.cleanupStart?]
  rw [same] at emitted
  simp only [State.streamItems, active, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  exact List.mem_append_left _ (List.mem_append_left _ emitted)

/-- Registration preserves an old source record or supplies its actual dispatch cleanup.
The queue is the already exposed source cut; no flattened-prefix state bridge is used.
-/
theorem registrationSnapshot_sourceRecord_progress_available
    (queue : ReferenceWorkQueue.State) (keys : queue.TaskNodeKeysUnique)
    (event : GraphEvent) (available : List (Occurrence × Nat))
    (cached : queue.cacheTaskFailures available = queue) {key}
    (represented : RecordTargetRepresented queue (.stream key))
    : RecordTargetRepresented (registrationSnapshot queue event available) (.stream key)
      ∨ .cancelSource key
        ∈ (({ queue } : State).handleGraphEvent event available).2.2.1 := by
  cases event with
  | taskSuccess incoming result =>
      cases found : queue.taskNode? incoming with
      | none => simpa only [registrationSnapshot, found] using Or.inl represented
      | some input =>
          left
          simp only [registrationSnapshot, found]
          exact State.maybeIntegrateWork_sourceRecord
            { queue := queue.putTaskNode { input with value := some result.value } }
            result.work (some incoming) (sourceRecord_putTaskValue found result.value represented)
  | streamItems stream items =>
      cases active : queue.rootStreams.contains stream.ref with
      | false =>
          simpa only [registrationSnapshot, active, Bool.false_eq_true, ↓reduceIte]
            using Or.inl represented
      | true =>
          have progress := streamRegistrationFold_sourceRecord_available items
            (({ queue } : State), [], [], [], [], [], []) keys List.nodup_nil available
            (.inl represented)
          rcases progress with retained | requested
          · left
            rwa [registrationSnapshot_itemFold queue stream items active available]
          · right
            simp only [State.handleGraphEvent, cached]
            exact State.streamItems_preparedSourceTarget_cancelled { queue } stream items
              active available requested
  | taskFailure | groupFailure | streamSuccess | streamFailure => exact .inl represented

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
