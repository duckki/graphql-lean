import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.AvailablePreparedSourceProgress
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.AvailableSourceRegistrationProgress
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.SourceRecordFailureProgress
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ResourceCompletion

/-! Existing source records through actual dispatch with the complete host-batch cache. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open WorkQueueSemantics (Occurrence)

/-- Existing source records survive dispatch unless that dispatch completes or cancels
the source. Availability changes diagnostics without erasing held source records.
-/
theorem sourceFrame_existingSource_progress_available {queue : ReferenceWorkQueue.State}
    {work parents before event key} (generated : ReferenceWorkQueue.ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          ReferenceWorkQueue.GroupRecordAt work node dependencies
          → dependencies = parents node.ref)
    (source : ReferenceWorkQueue.UncancelledReplayFrame queue work parents before)
    (keys : queue.TaskNodeKeysUnique) (inventory : queue.ChildStreamInventory)
    (valid : ReferenceWorkQueue.ValidGraphEvents work (before ++ [event]))
    (available : List (Occurrence × Nat))
    (cached : queue.cacheTaskFailures available = queue)
    (represented : RecordTargetRepresented queue (.stream key))
    : let reduced := ({ queue } : State).handleGraphEvent event available
      RecordTargetRepresented reduced.1.queue (.stream key)
      ∨ normalCompletionTarget? queue event = some (.stream key)
      ∨ .cancelSource key ∈ reduced.2.2.1 := by
  dsimp only
  cases event with
  | taskSuccess incoming result =>
      rcases registrationSnapshot_sourceRecord_progress_available queue keys
          (.taskSuccess incoming result) available cached represented with prepared | cancelled
      · rcases sourceFrame_preparedSource_progress_available generated canonical source keys
            inventory valid trivial available cached prepared with retained | cancelled
        · exact .inl retained
        · exact .inr (.inr cancelled)
      · exact .inr (.inr cancelled)
  | streamItems stream items =>
      rcases registrationSnapshot_sourceRecord_progress_available queue keys
          (.streamItems stream items) available cached represented with prepared | cancelled
      · rcases sourceFrame_preparedSource_progress_available generated canonical source keys
            inventory valid trivial available cached prepared with retained | cancelled
        · exact .inl retained
        · exact .inr (.inr cancelled)
      · exact .inr (.inr cancelled)
  | taskFailure failed errors =>
      simp only [State.handleGraphEvent, cached]
      rcases State.taskFailure_sourceRecord ({ queue } : State) failed errors represented with
          retained | cancelled
      · exact .inl retained
      · exact .inr (.inr cancelled)
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, cached]
      simp only [ReferenceWorkQueue.State.handleGraphEvent,
        ReferenceWorkQueue.State.cacheTaskFailures, List.foldl_nil]
      cases represented with
      | activeStream active =>
          by_cases same : key = stream.ref
          · exact .inr (.inl (by simp [normalCompletionTarget?, ← same, active]))
          · apply Or.inl
            apply RecordTargetRepresented.activeStream
            simp only [ReferenceWorkQueue.State.streamSuccess]
            split
            · exact List.mem_filter.mpr ⟨active, by simpa using same⟩
            · exact active
      | @bufferedStream occurrence node key found stored held =>
          apply Or.inl
          apply RecordTargetRepresented.bufferedStream (occurrence := occurrence)
            (node := node) _ stored held
          simp only [ReferenceWorkQueue.State.streamSuccess]
          split <;> exact found
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, cached]
      simp only [ReferenceWorkQueue.State.handleGraphEvent,
        ReferenceWorkQueue.State.cacheTaskFailures, List.foldl_nil]
      cases represented with
      | activeStream active =>
          by_cases same : key = stream.ref
          · subst key
            exact .inr (.inr (by simp [active]))
          · apply Or.inl
            apply RecordTargetRepresented.activeStream
            simp only [ReferenceWorkQueue.State.streamFailure]
            split
            · exact List.mem_filter.mpr ⟨active, by simpa using same⟩
            · exact active
      | @bufferedStream occurrence node key found stored held =>
          apply Or.inl
          apply RecordTargetRepresented.bufferedStream (occurrence := occurrence)
            (node := node) _ stored held
          simp only [ReferenceWorkQueue.State.streamFailure]
          split <;> exact found
  | groupFailure notice =>
      apply Or.inl
      simp only [State.handleGraphEvent, cached]
      simp only [ReferenceWorkQueue.State.handleGraphEvent,
        ReferenceWorkQueue.State.cacheTaskFailures, List.foldl_nil]
      unfold ReferenceWorkQueue.State.groupFailure
      split
      · exact represented
      · split
        · cases represented with
          | activeStream active => exact .activeStream active
          | bufferedStream found stored held => exact .bufferedStream found stored held
        · exact represented

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
