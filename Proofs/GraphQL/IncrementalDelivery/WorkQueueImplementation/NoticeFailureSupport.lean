import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.AcceptedFailureHealth
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureContributions
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CachedFailures
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ItemNoticeContents

/-! Retained notice caches are supported by accepted, not merely received, failures. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Positive complete error totals identify an accepted contributing failure
-----------------------------------------------------------------------------------------

/-- A positive exact total contains a failed-inventory task contributing to this key.
Witness: extract a positive summand; a nonowner would have contributed zero. This does
not require a licensed output history or replace the inventory by raw source failures.
-/
theorem nodeErrors_contributor_of_positive {work failed key errors}
    (counts : NodeErrors work failed key errors) (positive : 0 < errors)
    : ∃ occurrence ∈ failed,
        ∃ owners, TaskHasOwners work occurrence owners ∧ key ∈ owners := by
  obtain ⟨contribution, known, total⟩ := counts
  rw [total] at positive
  obtain ⟨count, member, pos⟩ := List.sum_pos_iff_exists_pos_nat.mp positive
  obtain ⟨occurrence, recorded, same⟩ := List.mem_map.mp member
  obtain ⟨owners, producer, payload, task, counted⟩ := known occurrence recorded
  refine ⟨occurrence, recorded, owners, ⟨producer, payload, task⟩, ?_⟩
  by_cases present : key ∈ owners
  · exact present
  · simp [present, same] at counted
    omega

/-- A generated nonempty source-contributor total is strictly positive.
Witness: a listed failing task has a positive fixed error count, hence so does its sum.
-/
theorem GroupFailureTotal.positive {work inputs key errors}
    (total : GroupFailureTotal work inputs key errors) (generated : ExecutedWork work)
    : 0 < errors := by
  obtain ⟨parts, nonempty, _, total, sources⟩ := total
  obtain ⟨entry, member⟩ := List.exists_mem_of_ne_nil parts nonempty
  obtain ⟨_, owners, producer, path, known, _⟩ := sources entry.1 entry.2 member
  have positive : 0 < entry.2 := generated.taskFailure_positive known rfl
  rw [← total]
  exact List.sum_pos_iff_exists_pos_nat.mpr
    ⟨entry.2, List.mem_map.mpr ⟨entry, member, rfl⟩, positive⟩

/-- Positive live caches with complete accounting have accepted contributor support.
Witness: the cache's exact positive total supplies a member of the same full inventory.
-/
theorem State.GroupErrorAccounting.cachedFailuresSupported {queue : State} {work failed}
    (counts : queue.GroupErrorAccounting work failed)
    (positive : queue.CachedErrorsSatisfy (fun _ errors => 0 < errors))
    : queue.CachedFailuresSupported work failed := by
  intro node member present
  cases cached : node.failure with
  | none => simp [cached] at present
  | some errors =>
      have exactCount := counts.live node member
      simp only [cached, Option.getD_some] at exactCount
      exact nodeErrors_contributor_of_positive exactCount (positive node member errors cached)

/-- Every generated replay cache has a contributor accepted by the executable guard.
Witness: source provenance gives positivity; full accepted-inventory accounting identifies
the contributor. Ignored settlements are absent from that inventory, even if received.
-/
theorem ExecutedWork.replayGraphEvents_cachedAcceptedFailures {work events}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work events)
    (accepted : (State.initialize (Work.fromExecution work)).acceptsBatch events = true)
    : ((State.initialize (Work.fromExecution work)).replayGraphEvents
        events).CachedFailuresSupported
        work
        ((State.initialize (Work.fromExecution work)).objectFailureContributions
          events) := by
  have counts := (createWorkQueue_groupErrorAccounting (Work.fromExecution work) work).replayGraphEvents
    (before := []) (createWorkQueue_pendingAccounting work) generated events valid accepted
  simp only [List.append_nil] at counts
  exact counts.cachedFailuresSupported
    ((generated.replayGraphEvents_cachedFailureTotals valid).mono
      (fun _ _ total => total.positive generated))

-----------------------------------------------------------------------------------------
-- Every internal successful-release boundary retains the same accepted inventory
-----------------------------------------------------------------------------------------

/-- Every prefix of the single-pass owner fold preserves accepted cache support.
Witness: counter decrements retain their cache; a successful flush only removes caches.
-/
theorem State.CachedFailuresSupported.successGroupFold {queue : State} {work failed}
    (supported : queue.CachedFailuresSupported work failed)
    (groups : List Execution.DeliveryNode)
    : (groups.foldl successGroupStep (queue, [], {})).1.CachedFailuresSupported work
        failed := by
  have loop (more : List Execution.DeliveryNode)
      (acc : State × List WorkQueueEvent × NewWork)
      (prior : acc.1.CachedFailuresSupported work failed)
      : (more.foldl successGroupStep acc).1.CachedFailuresSupported work failed := by
    induction more generalizing acc with
    | nil => exact prior
    | cons group rest ih =>
        simp only [List.foldl_cons, successGroupStep]
        split
        · exact ih acc prior
        · rename_i node found
          let updated := { node with pending := node.pending - 1 }
          have next := prior.putGroupNode updated (prior node (List.mem_of_find?_eq_some found))
          split
          · exact ih _ (next.finishGroupSuccess updated)
          · exact ih _ next
  exact loop groups (queue, [], {}) supported

/-- Each bounded drain prefix retains accepted cache support after either kind of closure.
Witness: the actual finite-loop induction, including failure cleanup before a later notice.
-/
theorem State.CachedFailuresSupported.drainReadyGroups_go {queue : State} {work failed}
    (supported : queue.CachedFailuresSupported work failed) (fuel : Nat)
    : (State.drainReadyGroups.go fuel queue).1.CachedFailuresSupported work failed := by
  apply State.drainReadyGroups_go_preserves
    (fun current => current.CachedFailuresSupported work failed) (valid := supported)
  · intro current node prior _ _ _ _
    exact (prior.finishGroupSuccess node).startNewWork _
  · intro current node errors prior _ _ _
    exact prior.removeGroup node.group.node.key

/-- Integrating one stream item retains the prior accepted contributor inventory.
Witness: integration, pruning, and activation introduce no failure cache.
-/
theorem State.CachedFailuresSupported.integrateStreamItem {queue : State} {work failed}
    (supported : queue.CachedFailuresSupported work failed) (item : StreamItem)
    : (queue.integrateStreamItem item).CachedFailuresSupported work failed :=
  ((supported.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _

/-- Any prepared item prefix retains the same accepted cache support.
Witness: the projected item-state fold and induction through actual item integration.
-/
theorem State.CachedFailuresSupported.preparedStreamItems {queue : State} {work failed}
    (supported : queue.CachedFailuresSupported work failed) (items : List StreamItem)
    : (queue.preparedStreamItems items).CachedFailuresSupported work failed := by
  induction items generalizing queue with
  | nil => exact supported
  | cons item rest ih =>
      rw [queue.preparedStreamItems_cons]
      exact ih (supported.integrateStreamItem item)

-----------------------------------------------------------------------------------------
-- Actual source prefixes supply support to all three notice-origin boundaries
-----------------------------------------------------------------------------------------

/-- Task-success preparation retains the accepted failures from prior source replay.
Witness: derive prior cache support and preserve it while storing and integrating work.
-/
theorem ExecutedWork.taskSuccess_prepared_cachedAcceptedFailures
    {work before occurrence} {result : TaskResult} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work before)
    (accepted : (State.initialize (Work.fromExecution work)).acceptsBatch before = true)
    (incoming : TaskNode)
    : let initial := State.initialize (Work.fromExecution work)
      let current := initial.replayGraphEvents before
      let stored := current.putTaskNode { incoming with value := some result.value }
      let prepared := (stored.maybeIntegrateWork result.work (some occurrence)).1
      prepared.CachedFailuresSupported work
        (initial.objectFailureContributions before) := by
  intro initial current stored prepared
  have support := generated.replayGraphEvents_cachedAcceptedFailures valid accepted
  have storedSupport : stored.CachedFailuresSupported work
      (initial.objectFailureContributions before) := support
  exact storedSupport.maybeIntegrateWork result.work (some occurrence)

/-- The post-owner-fold drain starts with support from exactly the prior accepted failures.
Witness: task preparation, complete single-pass release, and activation preserve support.
-/
theorem ExecutedWork.taskSuccess_drain_cachedAcceptedFailures
    {work before occurrence} {result : TaskResult} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work before)
    (accepted : (State.initialize (Work.fromExecution work)).acceptsBatch before = true)
    (incoming : TaskNode)
    : let initial := State.initialize (Work.fromExecution work)
      let current := initial.replayGraphEvents before
      let stored := current.putTaskNode { incoming with value := some result.value }
      let prepared := (stored.maybeIntegrateWork result.work (some occurrence)).1
      let released := incoming.task.groups.foldl successGroupStep (prepared, [], {})
      let active := released.1.startNewWork released.2.2
      active.CachedFailuresSupported work
        (initial.objectFailureContributions before) := by
  exact ((generated.taskSuccess_prepared_cachedAcceptedFailures valid accepted incoming
    (occurrence := occurrence) (result := result)).successGroupFold
      incoming.task.groups).startNewWork _

/-- Any item prefix and its following drain retain the prior accepted failure support.
Witness: generated replay followed by arbitrary item preparation; a bounded drain prefix
can then use `CachedFailuresSupported.drainReadyGroups_go` without a new source premise.
-/
theorem ExecutedWork.streamItems_prepared_cachedAcceptedFailures {work before}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work before)
    (accepted : (State.initialize (Work.fromExecution work)).acceptsBatch before = true)
    (items : List StreamItem)
    : let initial := State.initialize (Work.fromExecution work)
      ((initial.replayGraphEvents before).preparedStreamItems
        items).CachedFailuresSupported
        work (initial.objectFailureContributions before) :=
  (generated.replayGraphEvents_cachedAcceptedFailures valid accepted).preparedStreamItems
    items

/-- An accepted cache contributor visible at an output cut licenses the failure alternative.
Witness: transport that contributor into the same cut inventory; no output admission,
open-owner premise, or fresh source-failure choice is introduced here.
-/
theorem State.CachedFailuresSupported.recorded {queue : State} {work failed failures cut}
    (supported : queue.CachedFailuresSupported work failed)
    (visible : failed.Subset (failedBefore failures cut)) {node : GroupNode}
    (member : node ∈ queue.groupNodes) (cached : node.failure.isSome = true)
    : HasRecordedFailure work failures cut node.group.node.key := by
  obtain ⟨occurrence, accepted, owners, known, owner⟩ := supported node member cached
  exact ⟨occurrence, owners, visible accepted, known, owner⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
