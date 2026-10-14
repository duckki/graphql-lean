import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ResourceCompletion
import Tests.GraphQL.IncrementalDelivery.Fixtures.SharedOwnerFailure

open GraphQL.IncrementalDelivery.Tests

namespace AlternativeResourceCompletionChecks
open GraphQL.IncrementalDelivery
open AlternativeWorkQueue
open AlternativeWorkQueue.NativeRefinement

example : GeneratedTaskFailureResourceCompletion :=
  GeneratedTaskFailureResourceCompletion_holds

private def stream7 : Execution.DeliveryNode := { ref := 7, path := [] }

private def sourceState : State :=
  { queue := { rootStreams := [7], streams := [⟨stream7⟩] } }

private def sourceLease : ResourceState :=
  ResourceState.empty.set (.stream 7) (.owned .queue)

-- Exhaustion finishes the active source without manufacturing a cancellation request.
example
    : (sourceLease.observeCompletionAndCleanup sourceState (.streamSuccess stream7)).2
      = [.finishNormally (.stream 7)] := by cbv

example
    : (sourceLease.observeCompletionAndCleanup sourceState (.streamSuccess stream7)).1
        (.stream 7)
      = .released :=
  sourceLease.observeCompletionAndCleanup_finishedTarget sourceState
    (.streamSuccess stream7) (.stream 7) (by cbv) (by cbv)

-- Source failure closes semantic work, but its cleanup lease still awaits settlement.
example
    : (sourceLease.observeCompletionAndCleanup sourceState (.streamFailure stream7 1)).2
      = [.requestCleanup (.stream 7)] := by cbv

example
    : (sourceLease.observeCompletionAndCleanup sourceState (.streamFailure stream7 1)).1
        (.stream 7)
      = .cleanupRequested .queue := by cbv

example
    : (({ state := sourceState } : GraphBatchResult).handleGraphEvent
        (.streamFailure stream7 1)).state.queue.rootStreams
      = [] := by cbv

-- Rejected/late inputs cannot finish requested cleanup or steal producer-owned resources.
private def requested : ResourceState :=
  ResourceState.empty.set (.stream 7) (.cleanupRequested .queue)

private def foreign : ResourceState :=
  ResourceState.empty.set (.stream 7) (.owned (.producer (.executionGroup [0])))

example
    : (requested.observeCompletionAndCleanup sourceState (.streamSuccess stream7)).1
        (.stream 7)
      = .cleanupRequested .queue := by cbv

example
    : (requested.observeCompletionAndCleanup sourceState (.streamSuccess stream7)).2
      = [] := by cbv

example
    : (foreign.observeCompletionAndCleanup sourceState (.streamSuccess stream7)).1
        (.stream 7)
      = .owned (.producer (.executionGroup [0])) := by cbv

example
    : (ResourceState.empty.observeCompletionAndCleanup sourceState
        (.streamSuccess stream7)).1
        (.stream 7)
      = .unacquired := by cbv

-----------------------------------------------------------------------------------------
-- One generated task-failure dispatch finishes its settler and disposes its held sources
-----------------------------------------------------------------------------------------

private def failed : WorkQueueSemantics.Occurrence := .executionGroup [1, 1, 0]

private def leases : ResourceState :=
  SharedOwnerFailure.leases.set (.task failed) (.owned .queue)

private abbrev observed :=
  leases.observeCompletionAndCleanup SharedOwnerFailure.staged.state
    SharedOwnerFailure.failureG

private theorem acquisition
    : ResourceReplay ResourceState.empty
        [
          .acquire (.stream 2) (.producer SharedOwnerFailure.heldProducer),
          .adopt SharedOwnerFailure.heldProducer [.stream 2],
          .acquire (.task failed) .queue
        ] leases := by
  exact SharedOwnerFailure.handoff.append (.cons (.acquire _ _ .queue (by cbv)) (.nil _))

-- Operational completion releases the failed task; it does not make GraphQL work successful.
example : observed.2 = [.finishNormally (.task failed), .requestCleanup (.stream 2)] := by
  cbv

example : observed.1 (.task failed) = .released :=
  leases.observeCompletionAndCleanup_finishedTask _ _ _ (by cbv)

example : observed.1 (.stream 2) = .cleanupRequested .queue := by cbv

example
    : ResourceReplay ResourceState.empty
        ([
            .acquire (.stream 2) (.producer SharedOwnerFailure.heldProducer),
            .adopt SharedOwnerFailure.heldProducer [.stream 2],
            .acquire (.task failed) .queue
          ]
          ++ observed.2) observed.1 :=
  acquisition.append (leases.observeCompletionAndCleanup_replay _ _)

-- Any resource observation here comes from the same input or the same dispatch effects.
example (resources : ResourceState) (before : State) (event : GraphEvent)
    : ∀ action ∈ (resources.observeCompletionAndCleanup before event).2,
        (∃ target,
          normalCompletionTarget? before.queue event = some target
          ∧ action = .finishNormally target)
        ∨ (∃ effect ∈
            (({ state := before } : GraphBatchResult).handleGraphEvent event).effects,
            ∃ target,
              effect.cleanupStart? = some target ∧ action = .requestCleanup target) :=
  resources.observeCompletionAndCleanup_actions before event

#print axioms GeneratedTaskFailureResourceCompletion_holds
#print axioms ResourceState.observeCompletionAndCleanup_replay
#print axioms ResourceState.observeCompletionAndCleanup_actions
#print axioms ResourceState.observeCompletionAndCleanup_finishedTarget
#print axioms ResourceState.finishQueueTarget_replay

end AlternativeResourceCompletionChecks
