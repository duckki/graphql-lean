import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ResourceBatchReplay
import Tests.GraphQL.IncrementalDelivery.Fixtures.SharedOwnerFailure

open GraphQL.IncrementalDelivery.Tests

/-! Actual FIFO batches and normalized replay share one acquired-resource history.
The independently supplied inventory is intentionally selective, not claimed native-complete.
-/

namespace AlternativeResourceBatchReplayChecks
open GraphQL.IncrementalDelivery
open AlternativeWorkQueue
open AlternativeWorkQueue.NativeRefinement

private abbrev producer := SharedOwnerFailure.heldProducer
private def inventories : ProducerInventories := fun _ => [.stream 2]

private def acquired : ResourceState :=
  (ResourceState.empty.set (.task producer) (.owned .queue)).set
    (.stream 2) (.owned (.producer producer))

private abbrev before :=
  (State.initialize SharedOwnerFailure.work).handleGraphEvents
    [SharedOwnerFailure.parentSuccess]

private def batch : List GraphEvent :=
  [SharedOwnerFailure.success, SharedOwnerFailure.failureG, SharedOwnerFailure.failureH]

private abbrev observed :=
  State.observeResourceBatch before.state acquired inventories batch

private abbrev splitRun :=
  State.observeResourceBatches before.state acquired inventories
    [
      [SharedOwnerFailure.success],
      [SharedOwnerFailure.failureG],
      [SharedOwnerFailure.failureH]
    ]

private theorem acquisition
    : ResourceReplay ResourceState.empty
        [.acquire (.task producer) .queue, .acquire (.stream 2) (.producer producer)]
        acquired :=
  .cons (.acquire _ _ _ rfl) (.cons (.acquire _ _ _ (by cbv)) (.nil _))

-----------------------------------------------------------------------------------------
-- Same batch: completion, handoff, last-owner disposal, then terminal record clearing
-----------------------------------------------------------------------------------------

example : observed.dispatch = before.state.handleGraphEvents batch :=
  State.observeResourceBatch_dispatch _ _ _ _

example
    : observed.actions
      = [
        .finishNormally (.task producer),
        .adopt producer [.stream 2],
        .requestCleanup (.stream 2)
      ] := by
  dsimp only [observed, before]
  rw [SharedOwnerFailure.work_shape]
  cbv

example
    : observed.dispatch.state.stopped = true
      ∧ observed.dispatch.state.queue.terminated = true := by
  dsimp only [observed, before]
  rw [SharedOwnerFailure.work_shape]
  cbv

example : observed.dispatch.state.queue.taskNodes = [] := by
  dsimp only [observed, before]
  rw [SharedOwnerFailure.work_shape]
  cbv

example : observed.resources (.stream 2) = .cleanupRequested .queue := by
  dsimp only [observed, before]
  rw [SharedOwnerFailure.work_shape]
  cbv

example : observed.resources (.task producer) = .released := by
  dsimp only [observed, before]
  rw [SharedOwnerFailure.work_shape]
  cbv

private theorem actualBatch
    : ResourceReplay ResourceState.empty
        ([.acquire (.task producer) .queue, .acquire (.stream 2) (.producer producer)]
          ++ observed.actions) observed.resources :=
  acquisition.append (State.observeResourceBatch_replay _ _ _ _)

-----------------------------------------------------------------------------------------
-- Separate available batches retain the same obligations and actual normalized state
-----------------------------------------------------------------------------------------

example
    : splitRun.state
      = (before.state.runNormalized
          [
            [SharedOwnerFailure.success],
            [SharedOwnerFailure.failureG],
            [SharedOwnerFailure.failureH]
          ]).1 :=
  State.observeResourceBatches_state _ _ _ _

example : splitRun.actions = observed.actions := by
  dsimp only [splitRun, observed, before]
  rw [SharedOwnerFailure.work_shape]
  cbv

example : splitRun.resources (.stream 2) = .cleanupRequested .queue := by
  dsimp only [splitRun, before]
  rw [SharedOwnerFailure.work_shape]
  cbv

private theorem actualSplitRun
    : ResourceReplay ResourceState.empty
        ([.acquire (.task producer) .queue, .acquire (.stream 2) (.producer producer)]
          ++ splitRun.actions) splitRun.resources :=
  acquisition.append (State.observeResourceBatches_replay _ _ _ _)

-----------------------------------------------------------------------------------------
-- Closed wrappers ignore all late input; requested cleanup still requires settlement
-----------------------------------------------------------------------------------------

example
    : (State.observeResourceBatch observed.dispatch.state observed.resources inventories
        [SharedOwnerFailure.success]).actions
      = [] := by
  rw [State.observeResourceBatch_closed _ _ _ _ (Or.inl (by
    dsimp only [observed, before]; rw [SharedOwnerFailure.work_shape]; cbv))]

example
    : State.observeResourceBatch { queue := { terminated := true } } acquired inventories
        [SharedOwnerFailure.success]
      = {
        dispatch := { state := { queue := { terminated := true } } },
        resources := acquired
      } :=
  State.observeResourceBatch_closed _ _ _ _ (Or.inr rfl)

example
    : (State.observeResourceBatch { queue := {} } ResourceState.empty inventories
        []).dispatch.workQueueEvents
      = [.workQueueTermination] := by cbv

example
    : (State.observeResourceBatch { queue := {} } ResourceState.empty inventories
        []).actions
      = [] := by cbv

private def settled : ResourceState := observed.resources.set (.stream 2) .released

private theorem settlement
    : ResourceReplay observed.resources [.settleCleanup (.stream 2)] settled :=
  .cons
    (.settle _ _ .queue
      (by dsimp only [observed, before]; rw [SharedOwnerFailure.work_shape]; cbv))
    (.nil _)

example
    : ResourceReplay ResourceState.empty
        (([.acquire (.task producer) .queue, .acquire (.stream 2) (.producer producer)]
            ++ observed.actions)
          ++ [.settleCleanup (.stream 2)]) settled :=
  actualBatch.append settlement

-- This result covers arbitrary legal suffixes, not just an ignored late Lean batch.
example (actions : List ResourceAction) (after : ResourceState)
    (later : ResourceReplay settled actions after)
    : after (.stream 2) = .released :=
  later.released_persists (.stream 2) (by simp [settled, ResourceState.set])

#print axioms State.observeResourceBatch_dispatch
#print axioms State.observeResourceBatch_replay
#print axioms State.observeResourceBatches_state
#print axioms State.observeResourceBatches_replay
#print axioms ResourceReplay.released_persists
#print axioms actualBatch
#print axioms actualSplitRun

end AlternativeResourceBatchReplayChecks
