import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.AvailableSourceDrain
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.StreamItemSourceFrames
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.UncancelledReplay

/-! Source-record progress after actual receipt preparation with the complete host snapshot.
Item-prefix and ready certificates are derived separately from resource ownership evidence.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open WorkQueueSemantics (Occurrence)

/-- Common cache projection constructs every actual pre-drain receipt certificate. -/
theorem State.streamItems_readySourceFrames_available {state : State} {work}
    (keys : state.queue.TaskNodeKeysUnique) (inventory : state.queue.ChildStreamInventory)
    (items : List ReferenceWorkQueue.StreamItem)
    (known
      : ∀ item ∈ items,
        ∀ task ∈ item.work.tasks, ReferenceWorkQueue.TaskMatches work task)
    (running : state.stopped = false) (available : List (Occurrence × Nat))
    (frames
      : ∀ earlier item later,
          items = earlier ++ item :: later
          → StreamItemCacheFrame (state.queue.preparedStreamItems earlier available) work
              item)
    (drainFrames
      : ∃ parents,
          (state.queue.preparedStreamItems items available).TaskOwnerFrame work
          ∧ (state.queue.preparedStreamItems items available).RemovalForest parents)
    : ∃ parents,
        let acc :=
          items.foldl (fun acc item => streamRegistrationStep acc item available)
            (state, [], [], [], [], [], [])
        acc.1.queue.TaskOwnerFrame work
        ∧ acc.1.queue.RemovalForest parents
        ∧ acc.1.queue.TaskNodeKeysUnique
        ∧ acc.1.queue.ChildStreamInventory := by
  let initial : StreamRegistrationAcc := (state, [], [], [], [], [], [])
  let acc := items.foldl (fun acc item => streamRegistrationStep acc item available) initial
  have fold := streamRegistrationFold_cacheProjection initial items running known available frames
  have queueEq := congrArg Prod.fst fold
  change acc.1.queue.cacheTaskFailures available
    = (state.queue.preparedStreamItems items available).cacheTaskFailures available at queueEq
  have referenceKeys : (state.queue.preparedStreamItems items available).TaskNodeKeysUnique := by
    apply ReferenceWorkQueue.State.preparedStreamItems_preserves
      (fun queue => queue.TaskNodeKeysUnique) keys items available
    intro queue item _ prior
    exact ((prior.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _ available
  have actualKeys : acc.1.queue.TaskNodeKeysUnique := by
    have cached := referenceKeys.cacheTaskFailures available
    rw [← queueEq] at cached
    simpa only [ReferenceWorkQueue.State.TaskNodeKeysUnique,
      ReferenceWorkQueue.State.cacheTaskFailures_taskOccurrences] using cached
  obtain ⟨parents, owners, forest⟩ := drainFrames
  have actualOwners := ReferenceWorkQueue.State.TaskOwnerFrame.of_cacheTaskFailures_eq
    actualKeys available queueEq owners
  have actualForest : acc.1.queue.RemovalForest parents := by
    have groups := congrArg ReferenceWorkQueue.State.groupNodes queueEq
    simp only [ReferenceWorkQueue.State.cacheTaskFailures_groupNodes] at groups
    apply forest.of_subset
    rw [groups]
    exact List.Subset.refl _
  have referenceInventory :
      (state.queue.preparedStreamItems items available).ChildStreamInventory := by
    apply ReferenceWorkQueue.State.preparedStreamItems_preserves
      (fun queue => queue.ChildStreamInventory) inventory items available
    intro queue item _ prior
    exact ((prior.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _ available
  exact ⟨parents, actualOwners, actualForest, actualKeys,
    childStreamInventory_of_cache_eq actualKeys available queueEq referenceInventory⟩

/-- The actual prepared source record survives ready draining or is cancelled in this
receipt's real effect trace, including cumulative preparation cleanup and the drain suffix.
-/
theorem State.streamItems_phaseSourceRecord_available {state : State} {work}
    (stream : Execution.DeliveryNode) (items : List ReferenceWorkQueue.StreamItem)
    (running : state.stopped = false)
    (active : state.queue.rootStreams.contains stream.ref = true)
    (available : List (Occurrence × Nat))
    (ready
      : ∃ parents,
          let acc :=
            items.foldl (fun acc item => streamRegistrationStep acc item available)
              (state, [], [], [], [], [], [])
          acc.1.queue.TaskOwnerFrame work
          ∧ acc.1.queue.RemovalForest parents
          ∧ acc.1.queue.TaskNodeKeysUnique
          ∧ acc.1.queue.ChildStreamInventory)
    {key}
    (represented
      : RecordTargetRepresented
          (registrationSnapshot state.queue (.streamItems stream items) available)
          (.stream key))
    : RecordTargetRepresented (state.streamItems stream items available).1.queue
        (.stream key)
      ∨ .cancelSource key ∈ (state.streamItems stream items available).2.2.1 := by
  let initial : StreamRegistrationAcc := (state, [], [], [], [], [], [])
  let acc := items.foldl (fun acc item => streamRegistrationStep acc item available) initial
  have prepared : registrationSnapshot state.queue (.streamItems stream items) available
      = acc.1.queue := by
    simp only [registrationSnapshot, active, ↓reduceIte]
    have stateEq : state = ({ queue := state.queue } : State) := by
      cases state with
      | mk queue stopped => simp_all
    dsimp only [acc, initial]
    rw [stateEq]
  rw [prepared] at represented
  obtain ⟨parents, owners, forest, keys, inventory⟩ := ready
  have readyRunning : acc.1.stopped = false :=
    (streamRegistrationFold_stopped items initial available).trans running
  have unique := (streamRegistrationFold_cleanupTargets items initial
    List.nodup_nil rfl available).1
  rcases sourceRecord_drainReadyGroups_available readyRunning owners forest inventory keys
      acc.2.2.2.2.1 unique available represented with retained | requested
  · simp only [State.streamItems, active, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    exact .inl retained
  · apply Or.inr
    have listed : CleanupTarget.stream key ∈ (state.streamItems stream items available
        ).2.2.1.filterMap HostEffect.cleanupStart? := by
      rw [State.streamItems_cleanupStarts_eq state stream items active available]
      exact requested
    obtain ⟨effect, emitted, selected⟩ := List.mem_filterMap.mp listed
    cases effect <;> simp_all [HostEffect.cleanupStart?]

/-- Actual source-cut certificates construct cache-aware receipt source progress. -/
theorem sourceFrame_streamItems_sourceRecord_available {queue : ReferenceWorkQueue.State}
    {work parents before}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          ReferenceWorkQueue.GroupRecordAt work node dependencies
          → dependencies = parents node.ref)
    (source : ReferenceWorkQueue.UncancelledReplayFrame queue work parents before)
    (keys : queue.TaskNodeKeysUnique) (inventory : queue.ChildStreamInventory)
    (stream : Execution.DeliveryNode) (items : List ReferenceWorkQueue.StreamItem)
    (matched : (ReferenceWorkQueue.GraphEvent.streamItems stream items).MatchesWork work)
    (available : List (Occurrence × Nat)) {key}
    (represented
      : RecordTargetRepresented
          (registrationSnapshot queue (.streamItems stream items) available)
          (.stream key))
    : RecordTargetRepresented
        (({ queue } : State).streamItems stream items available).1.queue (.stream key)
      ∨ .cancelSource key
        ∈ (({ queue } : State).streamItems stream items available).2.2.1 := by
  cases active : queue.rootStreams.contains stream.ref with
  | false =>
      simp only [registrationSnapshot, active, Bool.false_eq_true, ↓reduceIte] at represented
      simp only [State.streamItems, active, Bool.not_false, ↓reduceIte]
      exact .inl represented
  | true =>
      have known : ∀ item ∈ items, ∀ task ∈ item.work.tasks,
          ReferenceWorkQueue.TaskMatches work task := by
        intro item member task supplied
        obtain ⟨address, payload, same, located⟩ :=
          matched.streamItem_childTask_producer member supplied
        exact ⟨⟨address, payload, some item.occurrence, same, located⟩,
          matched.streamItem_childTask_groupsExact member supplied⟩
      have frames := streamItems_cacheFrames_of_structural generated canonical source.roots.live
        source.roots.retired source.tasks source.parent.children keys stream items matched available
      have drainFrames := streamItems_drainFrames generated canonical source.roots.live
        source.roots.retired source.tasks source.parent.children stream items matched available
      have ready := State.streamItems_readySourceFrames_available (state := { queue }) keys
        inventory items known rfl available frames ⟨parents, drainFrames⟩
      exact State.streamItems_phaseSourceRecord_available stream items rfl active
        available ready represented

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
