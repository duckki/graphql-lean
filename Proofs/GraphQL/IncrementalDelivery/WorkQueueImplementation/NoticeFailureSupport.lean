import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CancellationReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureContributions
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CachedFailures
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ItemNoticeContents

/-! Retained task rejections have presence-selected source contributors. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Selected source causes retain generated positive error counts
-----------------------------------------------------------------------------------------

/-- A selected generated source rejection has a positive delivery count. -/
theorem GroupFailureSourceCause.positive {work inputs ref errors}
    (cause : GroupFailureSourceCause work inputs ref errors)
    (generated : ExecutedWork work)
    : 0 < errors := by
  obtain ⟨occurrence, received, owners, producer, path, known, owner⟩ := cause
  exact generated.taskFailure_positive known rfl

/-- Every replayed rejection has a contributor in the presence-selected source inventory.
Witness: rejected-task provenance advances with actual handlers and registered task
descriptors. Removed tasks contribute no token even when their source input is received.
-/
theorem ExecutedWork.replayGraphEvents_cachedAcceptedFailures {work events}
    (_generated : ExecutedWork work) (valid : ValidGraphEvents work events)
    (_accepted
      : State.eventsStarted [] (State.initialize (Work.fromExecution work)) events = true)
    : ((State.initialize (Work.fromExecution work)).replayGraphEvents
        events).CachedFailuresSupported
        work
        ((State.initialize (Work.fromExecution work)).objectFailureContributions
          events) := by
  have supported := (createWorkQueue_cachedFailuresSupported
    (Work.fromExecution work) work []).replayGraphEvents_contributions
    (createWorkQueue_startedTasksRegistered _) (createWorkQueue_fromSpec_registeredTasksMatch work)
    events (fun _ member => valid.eachMatches member)
  simpa only [List.append_nil] using supported

-----------------------------------------------------------------------------------------
-- Every internal successful-release boundary retains the same accepted inventory
-----------------------------------------------------------------------------------------

/-- Every prefix of the single-pass owner fold preserves accepted cache support.
Witness: counter writes leave task rejections unchanged; successful flushing removes tasks.
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
          have next := prior.putGroupNode updated
          split
          · exact ih _ (next.finishGroupSuccess updated)
          · exact ih _ next
  exact loop groups (queue, [], {}) supported

/-- Each bounded successful drain retains accepted cache support through child startup.
Witness: successful flushes and cached startup preserve retained task-rejection facts
under the empty supplied snapshot.
-/
theorem State.CachedFailuresSupported.drainReadyGroups_go {queue : State} {work failed}
    (supported : queue.CachedFailuresSupported work failed) (fuel : Nat)
    : (State.drainReadyGroups.go [] fuel queue).1.CachedFailuresSupported work
        failed := by
  apply State.drainReadyGroups_go_preserves
    (fun current => current.CachedFailuresSupported work failed) (valid := supported)
  intro current node prior _ _ _
  exact (prior.finishGroupSuccess node).startNewWork _

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
Witness: an actual input lookup identifies the unchanged rejected computation, while
value storage and child integration retain its contributor witnesses.
-/
theorem ExecutedWork.taskSuccess_prepared_cachedAcceptedFailures
    {work before occurrence} {result : TaskResult} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work before)
    (accepted
      : State.eventsStarted [] (State.initialize (Work.fromExecution work)) before = true)
    (incoming : TaskNode)
    (found
      : ((State.initialize (Work.fromExecution work)).replayGraphEvents before).taskNode?
          occurrence
        = some incoming)
    : let initial := State.initialize (Work.fromExecution work)
      let current := initial.replayGraphEvents before
      let stored := current.putTaskNode { incoming with value := some result.value }
      let prepared := (stored.maybeIntegrateWork result.work (some occurrence)).1
      prepared.CachedFailuresSupported work
        (initial.objectFailureContributions before) := by
  intro initial current stored prepared
  have support := generated.replayGraphEvents_cachedAcceptedFailures valid accepted
  have storedSupport : stored.CachedFailuresSupported work
      (initial.objectFailureContributions before) :=
    State.CachedErrorsSatisfy.putTaskNode support _
      (fun errors rejected group member =>
        support incoming (List.mem_of_find?_eq_some found) errors rejected group member)
  exact storedSupport.maybeIntegrateWork result.work (some occurrence)

/-- The post-owner-fold drain starts with support from exactly the prior accepted failures.
Witness: task preparation, complete single-pass release, and activation preserve support.
-/
theorem ExecutedWork.taskSuccess_drain_cachedAcceptedFailures
    {work before occurrence} {result : TaskResult} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work before)
    (accepted
      : State.eventsStarted [] (State.initialize (Work.fromExecution work)) before = true)
    (incoming : TaskNode)
    (found
      : ((State.initialize (Work.fromExecution work)).replayGraphEvents before).taskNode?
          occurrence
        = some incoming)
    : let initial := State.initialize (Work.fromExecution work)
      let current := initial.replayGraphEvents before
      let stored := current.putTaskNode { incoming with value := some result.value }
      let prepared := (stored.maybeIntegrateWork result.work (some occurrence)).1
      let released := incoming.task.groups.foldl successGroupStep (prepared, [], {})
      let active := (released.1.startNewWork released.2.2).1
      active.CachedFailuresSupported work
        (initial.objectFailureContributions before) := by
  exact ((generated.taskSuccess_prepared_cachedAcceptedFailures valid accepted incoming found
    (occurrence := occurrence) (result := result)).successGroupFold
      incoming.task.groups).startNewWork _

/-- Any item prefix and its following drain retain the prior accepted failure support.
Witness: generated replay followed by arbitrary item preparation; a bounded drain prefix
can then use `CachedFailuresSupported.drainReadyGroups_go` without a new source premise.
-/
theorem ExecutedWork.streamItems_prepared_cachedAcceptedFailures {work before}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work before)
    (accepted
      : State.eventsStarted [] (State.initialize (Work.fromExecution work)) before = true)
    (items : List StreamItem)
    : let initial := State.initialize (Work.fromExecution work)
      ((initial.replayGraphEvents before).preparedStreamItems
        items).CachedFailuresSupported
        work (initial.objectFailureContributions before) :=
  (generated.replayGraphEvents_cachedAcceptedFailures valid accepted).preparedStreamItems
    items

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
