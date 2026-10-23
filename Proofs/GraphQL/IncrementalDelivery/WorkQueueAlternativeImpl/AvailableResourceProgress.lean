import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.AvailableIncomingTaskProgress
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.AvailableIncomingSourceProgress
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.TaskRecordPreservation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.DispatchResourceInvariant

/-! Resource preservation at cache-exposed FIFO cuts. A future notified failure can
already be cached while its independent computation lease awaits normal settlement.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open WorkQueueSemantics (Occurrence)

/-- Every owned task awaits a consumed outcome; tasks outside the full batch's outcomes
also retain concrete records. Sources always retain records. At the complete batch cut,
the two outcome lists coincide and recover the established full representation invariant.
-/
def BatchResourcesRepresented (queue : ReferenceWorkQueue.State)
    (consumed excluded : List Occurrence) (resources : ResourceState)
    : Prop :=
  (∀ occurrence,
    resources (.task occurrence) = .owned .queue
    → occurrence ∉ consumed
      ∧ (occurrence ∉ excluded → RecordTargetRepresented queue (.task occurrence)))
  ∧ SourcesRepresented queue resources

/-- Full representation supplies the weaker intermediate batch invariant. -/
theorem QueueResourcesRepresented.batch {queue consumed excluded resources}
    (represented : QueueResourcesRepresented queue consumed resources)
    : BatchResourcesRepresented queue consumed excluded resources :=
  ⟨
    fun occurrence owned =>
      ⟨(represented.1 occurrence owned).2, fun _ => (represented.1 occurrence owned).1⟩,
    represented.2
  ⟩

/-- Once every supplied outcome has been consumed, all remaining task leases have records. -/
theorem BatchResourcesRepresented.complete {queue consumed resources}
    (represented : BatchResourcesRepresented queue consumed consumed resources)
    : QueueResourcesRepresented queue consumed resources :=
  ⟨
    fun occurrence owned =>
      let pending := represented.1 occurrence owned
      ⟨pending.2 pending.1, pending.1⟩,
    represented.2
  ⟩

/-- Still-owned old leases survive the normal-completion phase with supplied availability. -/
theorem ResourceState.observeDispatch_existingQueueOwned_survivesCompletion_available
    (resources : ResourceState) (inventories : ProducerInventories) (before : State)
    (event : GraphEvent) (target : CleanupTarget) (available : List (Occurrence × Nat))
    (initial : resources target = .owned .queue)
    (owned
      : (resources.observeDispatch inventories before event available).1 target
        = .owned .queue)
    : (resources.observeNormalCompletion before.queue event).1 target
      = .owned .queue := by
  obtain ⟨adopted, _⟩ := ResourceState.requestQueueCleanup_still_owned _ _ target owned
  rcases ResourceState.observeAdoptions_queueOwned_origin _ _ _ target adopted with
      earlier | transferred
  · exact earlier
  · obtain ⟨producer, _, _, lease⟩ := transferred
    have original := resources.observeNormalCompletion_owned_origin _ _ target
      (.producer producer) lease
    rw [initial] at original
    cases original

/-- The actual exposed handler preserves independent leases using structural producer
identities. No resource conclusion, complete acquisition inventory, or endpoint law is assumed.
-/
theorem sourceFrame_resource_progress_available {queue : ReferenceWorkQueue.State}
    {work parents before event excluded resources inventories}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          ReferenceWorkQueue.GroupRecordAt work node dependencies
          → dependencies = parents node.ref)
    (source : ReferenceWorkQueue.UncancelledReplayFrame queue work parents before)
    (accounted
      : queue.PendingAccounting work
          (ReferenceWorkQueue.GraphEvent.taskSettlements before))
    (keys : queue.TaskNodeKeysUnique) (inventory : queue.ChildStreamInventory)
    (origins
      : queue.StreamsSatisfy
          (ReferenceWorkQueue.StreamProducerSeen work
            (before.flatMap (fun event => event.identities.1))))
    (valid : ReferenceWorkQueue.ValidGraphEvents work (before ++ [event]))
    (included
      : (event.recordTaskOutcome
          (ReferenceWorkQueue.GraphEvent.taskSettlements before)).Subset
          excluded)
    (rejections : queue.TaskRejectionsSatisfy (fun rejected _ => rejected ∈ excluded))
    (available : List (Occurrence × Nat))
    (cached : queue.cacheTaskFailures available = queue)
    (licensed
      : ∀ occurrence errors, (occurrence, errors) ∈ available → occurrence ∈ excluded)
    (represented
      : BatchResourcesRepresented queue
          (ReferenceWorkQueue.GraphEvent.taskSettlements before) excluded resources)
    (taskIdentity
      : ProducerTasksMatchWork work resources inventories (graphEffects queue event))
    (sourceIdentity
      : ProducerSourcesMatchWork work resources inventories (graphEffects queue event))
    : BatchResourcesRepresented
        (({ queue } : State).handleGraphEvent event available).1.queue
        (event.recordTaskOutcome (ReferenceWorkQueue.GraphEvent.taskSettlements before))
        excluded (resources.observeDispatch inventories { queue } event available).1 := by
  obtain ⟨prior, matching, fresh⟩ := ReferenceWorkQueue.validGraphEvents_last valid
  constructor
  · intro occurrence owned
    obtain ⟨adopted, absent⟩ := ResourceState.requestQueueCleanup_still_owned _ _ (.task occurrence)
      owned
    rcases ResourceState.observeAdoptions_queueOwned_origin _ _ _ (.task occurrence) adopted with
        earlier | transferred
    · have original := resources.observeNormalCompletion_owned_origin _ _ _ .queue earlier
      obtain ⟨pending, record⟩ := represented.1 occurrence original
      refine ⟨resources.observeNormalCompletion_taskUnsettled queue event occurrence _ pending
        earlier, ?_⟩
      intro outside
      rcases sourceFrame_existingTask_progress_available generated canonical source accounted keys
          valid included rejections available cached licensed (record outside) outside with
          retained | aborted
      · exact retained
      · exact False.elim (absent (List.mem_filterMap.mpr ⟨.abortTask occurrence, aborted, rfl⟩))
    · obtain ⟨producer, emitted, listed, lease⟩ := transferred
      have original := resources.observeNormalCompletion_owned_origin _ _ _ (.producer producer)
        lease
      obtain ⟨address, owners, payload, same, known⟩ := taskIdentity producer occurrence emitted
        listed original
      obtain ⟨task, returned, identity⟩ := adoptedTask_returned matching emitted (same ▸ known)
      have exactOccurrence : task.occurrence = occurrence := identity.trans same.symm
      have pending : task.occurrence ∉ ReferenceWorkQueue.GraphEvent.taskSettlements before := by
        intro processed
        exact acceptedChildTask_unsettled matching prior fresh returned
          (ReferenceWorkQueue.GraphEvent.taskSettlements_subsetIdentities _ processed)
      refine ⟨exactOccurrence ▸ acceptedChildTask_not_recorded matching returned pending, ?_⟩
      intro outside
      rcases sourceFrame_acceptedTask_progress_available generated canonical source accounted keys
          valid included rejections available cached licensed returned
          (exactOccurrence.symm ▸ outside)
          with retained | aborted
      · exact exactOccurrence ▸ retained
      · exact False.elim (absent (List.mem_filterMap.mpr
          ⟨.abortTask occurrence, exactOccurrence ▸ aborted, rfl⟩))
  · intro key owned
    obtain ⟨adopted, absent⟩ := ResourceState.requestQueueCleanup_still_owned _ _
      (.stream key) owned
    rcases ResourceState.observeAdoptions_queueOwned_origin _ _ _ (.stream key) adopted with
        earlier | transferred
    · have original := resources.observeNormalCompletion_owned_origin _ _ _ .queue earlier
      rcases sourceFrame_existingSource_progress_available generated canonical source keys inventory
          valid available cached (represented.2 key original) with retained | completed | cancelled
      · exact retained
      · exact False.elim (resources.observeDispatch_completedSource_not_owned_available inventories
          { queue } event key completed available owned)
      · exact False.elim (absent (List.mem_filterMap.mpr ⟨.cancelSource key, cancelled, rfl⟩))
    · obtain ⟨producer, emitted, listed, lease⟩ := transferred
      have original := resources.observeNormalCompletion_owned_origin _ _ _ (.producer producer)
        lease
      obtain ⟨child, dependencies, same, known⟩ :=
        sourceIdentity producer key emitted listed original
      rcases sourceFrame_adoptedSource_progress_available generated canonical source keys inventory
          origins valid available cached emitted known with retained | cancelled
      · exact same ▸ retained
      · exact False.elim (absent (List.mem_filterMap.mpr
          ⟨.cancelSource key, same ▸ cancelled, rfl⟩))

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
