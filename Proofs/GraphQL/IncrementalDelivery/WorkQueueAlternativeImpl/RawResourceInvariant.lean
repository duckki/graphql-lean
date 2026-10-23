import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ResourceInitialization
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.AvailableResourceProgress
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.GeneratedResourceBoundary

/-! Resource progress at actual FIFO cuts, retaining the complete supplied failure cache.
Consumed settlement history and full-batch exclusions have separate proof roles.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open WorkQueueSemantics (Occurrence)
private abbrev Kernel := ReferenceWorkQueue.State

/-- No actual adoption label is emitted when all graph roots are gone. Immutable task
registration and live-owner existence and contributor coverage exclude every started task.
-/
theorem graphEffects_emptyRoots_noAdopt {queue : Kernel}
    (registered : queue.StartedTasksRegistered) (covered : queue.LiveContributorsCovered)
    (owners : queue.TaskOwnersPresent)
    (empty : (queue.rootGroups.isEmpty && queue.rootStreams.isEmpty) = true)
    (event : GraphEvent) (producer : WorkQueueSemantics.Occurrence)
    : .adopt producer ∉ graphEffects queue event := by
  obtain ⟨groupsEmpty, streamsEmpty⟩ := Bool.and_eq_true_iff.mp empty
  have absent : ∀ occurrence, queue.taskNode? occurrence = none := by
    intro occurrence
    cases found : queue.taskNode? occurrence with
    | none => rfl
    | some node =>
        obtain ⟨key, contributes, live⟩ := owners node (List.mem_of_find?_eq_some found)
        have lookup : ∃ group, queue.groupNode? key = some group := by
          cases tested : queue.groupNode? key with
          | some group => exact ⟨group, rfl⟩
          | none => exact False.elim ((queue.groupNode?_eq_none_iff key).mp tested live)
        obtain ⟨root, active, _⟩ := covered node.task
          (registered node (List.mem_of_find?_eq_some found)) key contributes lookup
        rw [List.isEmpty_iff.mp groupsEmpty] at active
        cases active
  cases event with
  | taskSuccess occurrence result => simp [graphEffects, absent occurrence]
  | streamItems stream items => simp [graphEffects, List.isEmpty_iff.mp streamsEmpty]
  | taskFailure | groupFailure | streamSuccess => simp [graphEffects]
  | streamFailure stream errors => simp [graphEffects, List.isEmpty_iff.mp streamsEmpty]

/-- A dispatch with no adoption cannot create queue ownership from a missing/foreign lease. -/
theorem ResourceState.observeDispatch_noAdopt_noOwned (resources : ResourceState)
    (inventories : ProducerInventories) (before : State) (event : GraphEvent)
    (noOwned : ∀ target, resources target ≠ .owned .queue)
    (noAdopt : ∀ producer, .adopt producer ∉ graphEffects before.queue event)
    : ∀ target,
        (resources.observeDispatch inventories before event).1 target
        ≠ .owned .queue := by
  intro target owned
  obtain ⟨adopted, _⟩ := ResourceState.requestQueueCleanup_still_owned _ _ target owned
  rcases ResourceState.observeAdoptions_queueOwned_origin _ _ _ target adopted with
      earlier | transferred
  · exact noOwned target (resources.observeNormalCompletion_owned_origin _ _ _ .queue earlier)
  · obtain ⟨producer, emitted, _, _⟩ := transferred
    exact noAdopt producer emitted

/-- Cache exposure preserves every source location and each task location outside the
complete batch's outcome set. The ghost consumed-outcome ledger does not change.
-/
theorem BatchResourcesRepresented.cacheTaskFailures {queue consumed excluded resources}
    (represented : BatchResourcesRepresented queue consumed excluded resources)
    (keys : queue.TaskNodeKeysUnique) (available : List (Occurrence × Nat))
    (licensed
      : ∀ occurrence errors, (occurrence, errors) ∈ available → occurrence ∈ excluded)
    : BatchResourcesRepresented (queue.cacheTaskFailures available) consumed excluded
        resources := by
  constructor
  · intro occurrence owned
    obtain ⟨pending, record⟩ := represented.1 occurrence owned
    refine ⟨pending, fun outside => ?_⟩
    exact (taskRecord_cacheTaskFailures_iff keys available occurrence
      (fun errors member => outside (licensed occurrence errors member))).mpr (record outside)
  · intro key owned
    exact (streamRecord_cacheTaskFailures_iff keys available key).mpr (represented.2 key owned)

/-- Realizing internal enqueue effects preserves every batch resource-record witness. -/
theorem BatchResourcesRepresented.withGroupFailures {queue consumed excluded resources}
    (represented : BatchResourcesRepresented queue consumed excluded resources)
    (notices : List ReferenceWorkQueue.GroupFailureEvent)
    : BatchResourcesRepresented ({ queue with groupFailureEvents := notices })
        consumed excluded resources := by
  constructor
  · intro occurrence owned
    obtain ⟨pending, record⟩ := represented.1 occurrence owned
    exact ⟨pending, fun outside => (record outside).withGroupFailures notices⟩
  · intro key owned
    exact (represented.2 key owned).withGroupFailures notices

/-- One actual FIFO step preserves the batch resource invariant. Source certificates and
cache exposure are derived at this exact observer cut, without flattening host batches.
-/
theorem generatedRaw_resourceInvariant
    {work inputs batch fifo event tail resources inventories}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (valid : ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ batch))
    (started : ReferenceWorkQueue.inputsStarted work (inputs ++ [batch]) = true)
    (partition : batch = fifo ++ event :: tail)
    (represented
      : let actual := resourceFifoPrefix work inputs batch fifo resources inventories
        BatchResourcesRepresented actual.dispatch.state.queue
          (ReferenceWorkQueue.GraphEvent.taskSettlements (inputs.flatten ++ fifo))
          (ReferenceWorkQueue.GraphEvent.taskSettlements (inputs.flatten ++ batch))
          actual.resources)
    (taskIdentity
      : let actual := resourceFifoPrefix work inputs batch fifo resources inventories
        ProducerTasksMatchWork work actual.resources inventories
          (graphEffects actual.dispatch.state.queue event))
    (sourceIdentity
      : let actual := resourceFifoPrefix work inputs batch fifo resources inventories
        ProducerSourcesMatchWork work actual.resources inventories
          (graphEffects actual.dispatch.state.queue event))
    : let available := ReferenceWorkQueue.GraphEvent.availableFailures batch
      let actual := resourceFifoPrefix work inputs batch fifo resources inventories
      let after := actual.handleGraphEvent inventories event available
      BatchResourcesRepresented after.dispatch.state.queue
        (ReferenceWorkQueue.GraphEvent.taskSettlements
          ((inputs.flatten ++ fifo) ++ [event]))
        (ReferenceWorkQueue.GraphEvent.taskSettlements (inputs.flatten ++ batch))
        after.resources := by
  let available := ReferenceWorkQueue.GraphEvent.availableFailures batch
  let actual := resourceFifoPrefix work inputs batch fifo resources inventories
  let queue := actual.dispatch.state.queue.cacheTaskFailures available
  obtain ⟨projection, running⟩ := resourceFifoPrefix_cacheProjection
    (resources := resources) (inventories := inventories) generated valid started partition
  have keys := resourceFifoPrefix_taskKeys
    (resources := resources) (inventories := inventories) generated valid started partition
  have cached : queue.cacheTaskFailures available = queue := keys.cacheTaskFailures_idempotent _
  have exposedKeys := keys.cacheTaskFailures available
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have source := resourceFifoPrefix_sourceFrame
    (resources := resources) (inventories := inventories)
    generated canonical valid started partition
  have accounted := resourceFifoPrefix_pendingAccounting
    (resources := resources) (inventories := inventories) generated valid started partition
  have inventory := resourceFifoPrefix_childStreamInventory
    (resources := resources) (inventories := inventories) generated valid started partition
  have rejections := resourceFifoPrefix_taskRejections
    (resources := resources) (inventories := inventories) generated valid started partition
  have localValid : ReferenceWorkQueue.ValidGraphEvents work
      ((inputs.flatten ++ fifo) ++ [event]) := by
    apply valid.prefix ⟨tail, ?_⟩
    simp [partition, List.append_assoc]
  have origins : queue.StreamsSatisfy (ReferenceWorkQueue.StreamProducerSeen work
      ((inputs.flatten ++ fifo).flatMap (fun event => event.identities.1))) := by
    dsimp only [queue]
    rw [projection]
    exact (generated.batchPrefix_streamProducersSeen inputs fifo available
      (localValid.prefix ⟨[event], rfl⟩)).cacheTaskFailures available
  have licensed (occurrence errors) (member : (occurrence, errors) ∈ available)
      : occurrence ∈ ReferenceWorkQueue.GraphEvent.taskSettlements (inputs.flatten ++ batch) := by
    obtain ⟨supplied, included, failure⟩ := List.mem_filterMap.mp member
    cases supplied <;> simp only [Option.some.injEq, reduceCtorEq, Prod.mk.injEq] at failure
    obtain ⟨rfl, rfl⟩ := failure
    apply List.mem_reverse.mpr
    exact List.mem_flatMap.mpr ⟨_,
      List.mem_append_right _ included, List.mem_cons_self⟩
  have included : (event.recordTaskOutcome
      (ReferenceWorkQueue.GraphEvent.taskSettlements (inputs.flatten ++ fifo))).Subset
        (ReferenceWorkQueue.GraphEvent.taskSettlements (inputs.flatten ++ batch)) := by
    rw [← ReferenceWorkQueue.GraphEvent.taskSettlements_append]
    intro occurrence member
    obtain ⟨supplied, seen, outcome⟩ := List.mem_flatMap.mp (List.mem_reverse.mp member)
    apply List.mem_reverse.mpr
    apply List.mem_flatMap.mpr ⟨supplied, ?_, outcome⟩
    rw [partition]
    have earlierCut : ((inputs.flatten ++ fifo) ++ [event]).IsPrefix
        (inputs.flatten ++ (fifo ++ event :: tail)) := ⟨tail, by simp⟩
    exact earlierCut.subset seen
  have same : actual.dispatch.state.queue.cacheTaskFailures available
      = queue.cacheTaskFailures available := cached.symm
  have labels := graphEffects_of_cache_eq actual.dispatch.state.queue queue available same event
  change ProducerTasksMatchWork work actual.resources inventories
    (graphEffects actual.dispatch.state.queue event) at taskIdentity
  change ProducerSourcesMatchWork work actual.resources inventories
    (graphEffects actual.dispatch.state.queue event) at sourceIdentity
  have progress := sourceFrame_resource_progress_available generated canonical source accounted
    exposedKeys inventory origins localValid included rejections available cached licensed
    (represented.cacheTaskFailures keys available licensed) (labels ▸ taskIdentity)
    (labels ▸ sourceIdentity)
  have dispatch := State.handleGraphEvent_of_cache_eq actual.dispatch.state { queue }
    running rfl available same event
  have observer := actual.resources.observeDispatch_of_cache_eq inventories actual.dispatch.state
    { queue } running rfl available same event
  dsimp only [ResourceBatchObservation.handleGraphEvent, GraphBatchResult.handleGraphEvent]
  rw [dispatch, observer, ReferenceWorkQueue.GraphEvent.taskSettlements_append]
  exact progress.withGroupFailures _

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
