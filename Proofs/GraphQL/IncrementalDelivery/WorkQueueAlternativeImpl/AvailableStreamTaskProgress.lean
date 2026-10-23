import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedUnsettledTaskDrain
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.IncomingTaskOwners
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ReceiptCatalogues
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.StreamItemSourceFrames

/-! Local task-resource progress through a receipt with complete host cache availability. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open WorkQueueSemantics (Occurrence)
open GraphQL.IncrementalDelivery.Execution (DeliveryNode)

/-- An unfinished prepared task has an endpoint record or an abort in the actual receipt.
Both registration and drain use the supplied snapshot. Its other failures are unrestricted.
-/
theorem State.streamItems_preparedTask_progress_available {state : State} {work settled}
    (keys : state.queue.TaskNodeKeysUnique) (stream : DeliveryNode)
    (items : List ReferenceWorkQueue.StreamItem)
    (known
      : ∀ item ∈ items,
        ∀ task ∈ item.work.tasks, ReferenceWorkQueue.TaskMatches work task)
    (accounted : state.queue.PendingAccounting work settled)
    (matched : (ReferenceWorkQueue.GraphEvent.streamItems stream items).MatchesWork work)
    (running : state.stopped = false)
    (active : state.queue.rootStreams.contains stream.ref = true)
    (available : List (Occurrence × Nat))
    (frames
      : ∀ earlier item later,
          items = earlier ++ item :: later
          → StreamItemCacheFrame (state.queue.preparedStreamItems earlier available) work
              item)
    (drainFrames
      : ∃ parents,
          (state.queue.preparedStreamItems items available).TaskOwnerFrame work
          ∧ (state.queue.preparedStreamItems items available).RemovalForest parents)
    (task : ReferenceWorkQueue.Task) (pending : task.occurrence ∉ settled)
    (unrejected
      : state.queue.TaskRejectionsSatisfy (fun rejected _ => rejected ≠ task.occurrence))
    (licensed
      : ∀ occurrence errors,
          (occurrence, errors) ∈ available → occurrence ≠ task.occurrence)
    (catalogue
      : (items.foldl (fun acc item => streamRegistrationStep acc item available)
          (state, [], [], [], [], [], [])).1.queue.task?
          task.occurrence
        = some task)
    (links
      : (items.foldl (fun acc item => streamRegistrationStep acc item available)
          (state, [], [], [], [], [], [])).1.queue.TaskLinkedOn
          task.occurrence (task.groups.map DeliveryNode.ref))
    (owned
      : ∃ owner ∈ task.groups,
          ∃ group,
            (items.foldl (fun acc item => streamRegistrationStep acc item available)
              (state, [], [], [], [], [], [])).1.queue.groupNode?
              owner.ref
            = some group)
    : RecordTargetRepresented (state.streamItems stream items available).1.queue
        (.task task.occurrence)
      ∨ .abortTask task.occurrence
        ∈ (state.streamItems stream items available).2.2.1 := by
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
  obtain ⟨parents, frame, forest⟩ := drainFrames
  have actualFrame := ReferenceWorkQueue.State.TaskOwnerFrame.of_cacheTaskFailures_eq
    actualKeys available queueEq frame
  have topology := congrArg ReferenceWorkQueue.State.groupNodes queueEq
  simp only [ReferenceWorkQueue.State.cacheTaskFailures_groupNodes] at topology
  have actualForest := forest.of_subset (by rw [topology]; exact List.Subset.refl _)
  have bounded : acc.1.queue.PendingBound (fun _ => True) settled := by
    intro node member eligible
    rw [topology] at member
    exact preparedStreamItems_pendingBound accounted matched available node member eligible
  have readyRunning : acc.1.stopped = false :=
    (streamRegistrationFold_stopped items initial available).trans running
  have unique := (streamRegistrationFold_cleanupTargets items initial
    List.nodup_nil rfl available).1
  have readyUnrejected := streamRegistrationFold_taskRejections items initial unrejected
    available licensed
  have classified := fusedUnsettledDrainProgress_available task acc.2.2.2.2.1 readyRunning
    actualFrame actualForest catalogue links bounded pending owned unique readyUnrejected
    available licensed
  rcases classified with retained | aborted
  · simp only [State.streamItems, active, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    exact .inl retained
  · apply Or.inr
    have listed : CleanupTarget.task task.occurrence ∈
        ((acc.1.drainReadyGroups acc.2.2.2.2.1 available).2.2.1.flatMap
          CleanupTarget.effects).filterMap HostEffect.cleanupStart? :=
      List.mem_filterMap.mpr ⟨.abortTask task.occurrence, aborted, rfl⟩
    simp only [cleanupEffects_starts] at listed
    rw [← State.streamItems_cleanupStarts_eq state stream items active available] at listed
    obtain ⟨effect, emitted, selected⟩ := List.mem_filterMap.mp listed
    cases effect <;> simp_all [HostEffect.cleanupStart?]

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
