import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.InterleavedCallbacks
import Tests.GraphQL.IncrementalDelivery.Fixtures.SharedOwnerFailure
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.Conformance

open GraphQL.IncrementalDelivery.Tests

/-! Generated same-batch failure/late-result regression. Enqueue permission, raw work
legality, semantic projection and source conformance are checked separately.
-/

namespace AlternativeBufferedCallbackChecks

open GraphQL.IncrementalDelivery
open AlternativeWorkQueue
open AlternativeWorkQueue.NativeRefinement
open BufferedCallbacks
open WorkQueueSemantics (TaskAt)

private abbrev initial :=
  ReferenceWorkQueue.State.initialize
    (ReferenceWorkQueue.Work.fromExecution SharedOwnerFailure.work)

private abbrev before :=
  (initial.runNormalized [[SharedOwnerFailure.parentSuccess]]).1

private def raw : List (List GraphEvent) :=
  [
    [SharedOwnerFailure.parentSuccess],
    [SharedOwnerFailure.failureG, SharedOwnerFailure.success],
    [SharedOwnerFailure.failureH]
  ]

private def effective : List (List GraphEvent) :=
  [
    [SharedOwnerFailure.parentSuccess],
    [SharedOwnerFailure.failureG],
    [SharedOwnerFailure.failureH]
  ]

private def failed : BufferedCallback := ⟨10, SharedOwnerFailure.failureG⟩
private def buffered : BufferedCallback := ⟨11, SharedOwnerFailure.success⟩

private theorem first_valid
    : ReferenceWorkQueue.ValidGraphEvents SharedOwnerFailure.work
        [SharedOwnerFailure.parentSuccess] :=
  SharedOwnerFailure.valid_events.prefix
    ⟨
      [
        SharedOwnerFailure.success,
        SharedOwnerFailure.failureG,
        SharedOwnerFailure.failureH
      ],
      rfl
    ⟩

private theorem g_known
    : TaskAt SharedOwnerFailure.work (.executionGroup [1, 1, 0]) [0] none
        (.object [] (.error 1)) := by
  refine ⟨[{ node := SharedOwnerFailure.groupG }], [], { result := .error 1, cause := some 1 }, .empty, [], ?_, rfl, rfl⟩
  rw [SharedOwnerFailure.work_shape]
  rfl

private theorem h_known
    : TaskAt SharedOwnerFailure.work (.executionGroup [1, 1, 1, 0]) [1] none
        (.object [] (.error 1)) := by
  refine ⟨[{ node := SharedOwnerFailure.groupH }], [], { result := .error 1, cause := some 1 }, .empty, [], ?_, rfl, rfl⟩
  rw [SharedOwnerFailure.work_shape]
  rfl

private theorem source_known
    : TaskAt SharedOwnerFailure.work SharedOwnerFailure.heldProducer [0]
        (some (.executionGroup [1, 0]))
        (.object [.field "box"] (.ok ([("values", .list [])], 0))) := by
  refine ⟨[{ node := SharedOwnerFailure.groupG }], [.field "box"],
    { result := .ok ([("values", .list [])], 0) }, SharedOwnerFailure.streamWork, [0, 1], ?_, rfl, rfl⟩
  rw [SharedOwnerFailure.work_shape]
  rfl

private theorem g_ready (earlier : List GraphEvent)
    : SharedOwnerFailure.failureG.Ready SharedOwnerFailure.work earlier :=
  ⟨[0], none, _, g_known, fun _ impossible => by cases impossible⟩

private theorem h_ready (earlier : List GraphEvent)
    : SharedOwnerFailure.failureH.Ready SharedOwnerFailure.work earlier :=
  ⟨[1], none, _, h_known, fun _ impossible => by cases impossible⟩

private theorem buffered_enqueued
    : Enqueued SharedOwnerFailure.work before [SharedOwnerFailure.parentSuccess]
        [failed, buffered] := by
  have first : Enqueued SharedOwnerFailure.work before [SharedOwnerFailure.parentSuccess] [failed] :=
    .append .nil failed (by cbv) (by cbv) (by simp) SharedOwnerFailure.failureG_matches
      (by simp [failed, ReferenceWorkQueue.GraphEvent.Fresh,
        ReferenceWorkQueue.GraphEvent.identities, SharedOwnerFailure.parentSuccess, SharedOwnerFailure.failureG])
      (g_ready _)
  have ready : SharedOwnerFailure.success.Ready SharedOwnerFailure.work
      ([SharedOwnerFailure.parentSuccess] ++ [failed].map BufferedCallback.event) := by
    refine ⟨[0], some (.executionGroup [1, 0]), _, source_known, ?_⟩
    intro producer same
    cases same
    simp [ReferenceWorkQueue.GraphEvent.successes, SharedOwnerFailure.parentSuccess]
  exact .append first buffered (by cbv) (by cbv) (by decide)
    SharedOwnerFailure.success_matches
    (by
      simp [failed, buffered, ReferenceWorkQueue.GraphEvent.Fresh,
        ReferenceWorkQueue.GraphEvent.identities, SharedOwnerFailure.parentSuccess,
        SharedOwnerFailure.failureG, SharedOwnerFailure.success, SharedOwnerFailure.heldProducer])
    ready

private theorem raw_valid
    : ReferenceWorkQueue.ValidGraphEvents SharedOwnerFailure.work raw.flatten := by
  have bufferedValid := buffered_enqueued.work_valid first_valid
  have all := ReferenceWorkQueue.ValidGraphEvents.append bufferedValid
    SharedOwnerFailure.failureH_matches
    (by simp [failed, buffered, ReferenceWorkQueue.GraphEvent.Fresh,
      ReferenceWorkQueue.GraphEvent.identities, SharedOwnerFailure.parentSuccess,
      SharedOwnerFailure.failureG, SharedOwnerFailure.success, SharedOwnerFailure.failureH, SharedOwnerFailure.heldProducer])
    (h_ready _)
  exact all

private theorem raw_buffers : BoundaryBuffers SharedOwnerFailure.work initial [] raw := by
  refine ⟨⟨[⟨0, SharedOwnerFailure.parentSuccess⟩], ?_, rfl⟩,
    ⟨⟨[failed, buffered], ?_, rfl⟩,
      ⟨⟨[⟨12, SharedOwnerFailure.failureH⟩], ?_, rfl⟩, trivial⟩⟩⟩
  · have laws := first_valid.atPrefix (before := []) (event := SharedOwnerFailure.parentSuccess)
      ⟨[], rfl⟩
    exact .append .nil ⟨0, SharedOwnerFailure.parentSuccess⟩ (by cbv) (by cbv) (by simp)
      laws.1 laws.2.1 laws.2.2
  · have sameBoundary : (initial.handleGraphEvents [SharedOwnerFailure.parentSuccess]).1 = before := by
      cbv
    simpa only [sameBoundary, List.nil_append] using buffered_enqueued
  · exact .append .nil ⟨12, SharedOwnerFailure.failureH⟩ (by cbv) (by cbv) (by simp)
      SharedOwnerFailure.failureH_matches
      (by simp [ReferenceWorkQueue.GraphEvent.Fresh,
        ReferenceWorkQueue.GraphEvent.identities, SharedOwnerFailure.parentSuccess,
        SharedOwnerFailure.failureG, SharedOwnerFailure.success, SharedOwnerFailure.failureH, SharedOwnerFailure.heldProducer])
      (h_ready _)

private theorem projected : projectHistory initial raw = effective := by cbv

-----------------------------------------------------------------------------------------
-- A callback carried across reduction boundaries can be legal but stale when consumed
-----------------------------------------------------------------------------------------

private def parentCallback : BufferedCallback := ⟨0, SharedOwnerFailure.parentSuccess⟩
private def lastCallback : BufferedCallback := ⟨12, SharedOwnerFailure.failureH⟩

private def withParent : CallbackBuffer :=
  ({ queue := initial } : CallbackBuffer).enqueue parentCallback

private def firstBoundary := withParent.reduce [parentCallback] []
private def withFailure := firstBoundary.enqueue failed
private def withBoth := withFailure.enqueue buffered
private def withStalePending := withBoth.reduce [failed] [buffered]
private def afterStale := withStalePending.reduce [buffered] []
private def withLast := afterStale.enqueue lastCallback
private def completed := withLast.reduce [lastCallback] []

private theorem cross_boundary_history
    : CallbackHistory SharedOwnerFailure.work initial completed := by
  have parentLaws := raw_valid.atPrefix (before := [])
    (event := SharedOwnerFailure.parentSuccess)
    ⟨[SharedOwnerFailure.failureG, SharedOwnerFailure.success, SharedOwnerFailure.failureH], rfl⟩
  have parent : CallbackHistory SharedOwnerFailure.work initial withParent :=
    .enqueue .initial parentCallback (by cbv) (by cbv) (by simp)
      parentLaws.1 parentLaws.2.1 parentLaws.2.2
  have first : CallbackHistory SharedOwnerFailure.work initial firstBoundary :=
    .reduce parent [parentCallback] [] rfl
  have failureLaws := raw_valid.atPrefix (before := [SharedOwnerFailure.parentSuccess])
    (event := SharedOwnerFailure.failureG)
    ⟨[SharedOwnerFailure.success, SharedOwnerFailure.failureH], rfl⟩
  have failure : CallbackHistory SharedOwnerFailure.work initial withFailure :=
    .enqueue first failed (by cbv) (by cbv) (by decide)
      failureLaws.1 failureLaws.2.1 failureLaws.2.2
  have successLaws := raw_valid.atPrefix
    (before := [SharedOwnerFailure.parentSuccess, SharedOwnerFailure.failureG])
    (event := SharedOwnerFailure.success) ⟨[SharedOwnerFailure.failureH], rfl⟩
  have both : CallbackHistory SharedOwnerFailure.work initial withBoth :=
    .enqueue failure buffered (by cbv) (by cbv) (by decide)
      successLaws.1 successLaws.2.1 successLaws.2.2
  have pending : CallbackHistory SharedOwnerFailure.work initial withStalePending :=
    .reduce both [failed] [buffered] rfl
  have stale : CallbackHistory SharedOwnerFailure.work initial afterStale :=
    .reduce pending [buffered] [] rfl
  have lastLaws := raw_valid.atPrefix
    (before := [SharedOwnerFailure.parentSuccess, SharedOwnerFailure.failureG, SharedOwnerFailure.success])
    (event := SharedOwnerFailure.failureH) ⟨[], rfl⟩
  have last : CallbackHistory SharedOwnerFailure.work initial withLast :=
    .enqueue stale lastCallback (by cbv) (by cbv) (by decide)
      lastLaws.1 lastLaws.2.1 lastLaws.2.2
  exact .reduce last [lastCallback] [] rfl

-- Reduction does not demand current liveness of an already legally enqueued task.
example : withStalePending.pending = [buffered] := rfl
example : withStalePending.queue.acceptsGraphEvent buffered.event = false := by cbv

example : CallbackHistory SharedOwnerFailure.work initial completed :=
  cross_boundary_history

private theorem cross_boundary_not_boundary_buffers
    : ¬BoundaryBuffers SharedOwnerFailure.work initial [] completed.rawBatches := by
  intro buffers
  obtain ⟨_, _, ⟨callbacks, queued, same⟩, _⟩ := buffers
  have member : SharedOwnerFailure.success ∈ callbacks.map BufferedCallback.event := by
    rw [same]
    exact List.mem_singleton_self _
  obtain ⟨callback, present, equals⟩ := List.mem_map.mp member
  have started := queued.started callback present
  rw [equals] at started
  have absent : ((initial.handleGraphEvents [SharedOwnerFailure.parentSuccess]).1
      |>.handleGraphEvents [SharedOwnerFailure.failureG]).1.acceptsGraphEvent
        SharedOwnerFailure.success = false := by cbv
  change ((initial.handleGraphEvents [SharedOwnerFailure.parentSuccess]).1
      |>.handleGraphEvents [SharedOwnerFailure.failureG]).1.acceptsGraphEvent
        SharedOwnerFailure.success = true at started
  rw [absent] at started
  cases started

example : ¬BoundaryBuffers SharedOwnerFailure.work initial [] completed.rawBatches :=
  cross_boundary_not_boundary_buffers

private theorem cross_boundary_projection
    : projectHistory initial completed.rawBatches = effective := by cbv

example : (EventSource.ofList effective).ValidFor SharedOwnerFailure.work := by
  rw [← cross_boundary_projection]
  exact cross_boundary_history.projected_source_valid
    SharedOwnerFailure.executed SharedOwnerFailure.nonempty

example
    : (createWorkQueueForSchedule SharedOwnerFailure.work
        (EventSource.ofList effective)).Conforms
        SharedOwnerFailure.work := by
  rw [← cross_boundary_projection]
  exact cross_boundary_history.projected_conforms SharedOwnerFailure.executed SharedOwnerFailure.nonempty

example
    : initial.runNormalized (projectHistory initial completed.rawBatches)
      = initial.runNormalized completed.rawBatches :=
  cross_boundary_history.projected_runNormalized SharedOwnerFailure.executed
    SharedOwnerFailure.nonempty

-- The filtered success still has one consumed receipt in the same host inventory.
example : completed.batches.flatten.map BufferedCallback.receipt = [0, 10, 11, 12] := rfl
example : completed.pending = [] := rfl

example : (completed.batches.flatten.map BufferedCallback.receipt).Nodup :=
  cross_boundary_history.receipts_partition.2.1

-- The result was legally enqueued before failure; sequential raw admission rejects it.
example
    : Enqueued SharedOwnerFailure.work before [SharedOwnerFailure.parentSuccess]
        [failed, buffered] :=
  buffered_enqueued

example : ReferenceWorkQueue.ExecutedWork SharedOwnerFailure.work :=
  SharedOwnerFailure.executed

example : ReferenceWorkQueue.ValidGraphEvents SharedOwnerFailure.work raw.flatten :=
  raw_valid

example : ReferenceWorkQueue.inputsStarted SharedOwnerFailure.work raw = false := by cbv
example : projectHistory initial raw = effective := projected
example : BoundaryBuffers SharedOwnerFailure.work initial [] raw := raw_buffers

-- The generic work-law and full source proofs replace a regression-only legality argument.
example
    : ReferenceWorkQueue.ValidGraphEvents SharedOwnerFailure.work
        (projectHistory initial raw).flatten :=
  bufferedWorkProjection_holds _ raw SharedOwnerFailure.executed
    SharedOwnerFailure.nonempty raw_buffers

example : (EventSource.ofList effective).ValidFor SharedOwnerFailure.work := by
  rw [← projected]
  exact projected_source_valid SharedOwnerFailure.executed SharedOwnerFailure.nonempty raw raw_buffers

example
    : (createWorkQueueForSchedule SharedOwnerFailure.work
        (EventSource.ofList effective)).Conforms
        SharedOwnerFailure.work := by
  rw [← projected]
  exact projected_conforms SharedOwnerFailure.executed SharedOwnerFailure.nonempty raw raw_buffers

-- No child stream is adopted or started by the already-buffered, now-stale success.
example : before.acceptsGraphEvent SharedOwnerFailure.success = true := by cbv

example
    : (before.handleGraphEvent SharedOwnerFailure.failureG).1.acceptsGraphEvent
        SharedOwnerFailure.success
      = false := by cbv

example
    : (({ queue := before } : State).handleGraphEvents
        [SharedOwnerFailure.failureG, SharedOwnerFailure.success]).effects
      = [.abortTask SharedOwnerFailure.heldProducer] := by cbv

example
    : (({ queue := before } : State).handleGraphEvents
        [SharedOwnerFailure.failureG, SharedOwnerFailure.success]).state.queue.rootStreams
      = [] := by cbv

-- Filtering derives source start discipline while preserving the entire normalized replay.
example : ReferenceWorkQueue.inputsStarted SharedOwnerFailure.work effective = true := by
  rw [← projected]
  exact projected_inputsStarted SharedOwnerFailure.executed SharedOwnerFailure.nonempty raw

example : initial.runNormalized raw = initial.runNormalized effective := by
  rw [← projected]
  exact (projectHistory_runNormalized initial raw
    (initialized_boundary SharedOwnerFailure.executed SharedOwnerFailure.nonempty)).symm

private theorem source_valid
    : (EventSource.ofList effective).ValidFor SharedOwnerFailure.work := by
  rw [← projected]
  exact projected_source_valid SharedOwnerFailure.executed SharedOwnerFailure.nonempty raw raw_buffers

example
    : (createWorkQueueForSchedule SharedOwnerFailure.work
        (EventSource.ofList effective)).Conforms
        SharedOwnerFailure.work :=
  createWorkQueueForScheduleConforms_holds _ _ SharedOwnerFailure.executed
    SharedOwnerFailure.nonempty source_valid

-- Acknowledgement is not publication or adoption; stale receipts are not deduplicated by source.
private def source : Execution.DeliveryNode := ⟨77, [], none⟩

example
    : graphEffects ({} : ReferenceWorkQueue.State) (.streamItems source [])
      = [.acknowledge 77] :=
  stale_graphEffects _ _ rfl

example
    : (({ state := { queue := {} } } : GraphBatchResult).handleGraphEvent
          (.streamItems source [])
        |>.handleGraphEvent (.streamItems source [])).effects
      = [.acknowledge 77, .acknowledge 77] := by cbv

-- Silent/late batches disappear, but raw empty-root nonterminal states require the boundary guard.
example : projectHistory initial (raw ++ [[SharedOwnerFailure.success]]) = effective := by
  cbv

example : ¬Boundary ({} : ReferenceWorkQueue.State) := by unfold Boundary; decide

example
    : (({} : ReferenceWorkQueue.State).handleGraphEvents []).2
      = [.workQueueTermination] :=
  rfl

#print axioms projectBatch_handleGraphEvents
#print axioms projectHistory_runWithPublisher
#print axioms projected_inputsStarted
#print axioms Enqueued.work_valid
#print axioms BoundaryBuffers.work_valid
#print axioms stale_dispatch
#print axioms projected_conforms_of_workProjection
#print axioms SourceSupport.initialize
#print axioms SourceSupport.handleGraphEvent
#print axioms SourceSupport.ready
#print axioms bufferedWorkProjection_holds
#print axioms projected_source_valid
#print axioms projected_conforms
#print axioms raw_buffers
#print axioms buffered_enqueued
#print axioms source_valid
#print axioms CallbackHistory.invariant
#print axioms CallbackHistory.receipts_partition
#print axioms CallbackHistory.projected_source_valid
#print axioms CallbackHistory.projected_conforms
#print axioms cross_boundary_history
#print axioms cross_boundary_not_boundary_buffers

end AlternativeBufferedCallbackChecks
