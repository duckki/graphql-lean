import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FailurePruning
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedFailureResources
import Tests.GraphQL.IncrementalDelivery.Fixtures.SharedOwnerFailure
import Tests.GraphQL.IncrementalDelivery.Fixtures.HeldSourceCleanup

open GraphQL.IncrementalDelivery.Tests

namespace AlternativeResourceRequestChecks
open GraphQL.IncrementalDelivery
open AlternativeWorkQueue
open AlternativeWorkQueue.NativeRefinement
open WorkQueueSemantics (Occurrence)

private def producer : Occurrence := .executionGroup [0]
private def group0 : Execution.DeliveryNode := { ref := 0, path := [] }
private def group1 : Execution.DeliveryNode := { ref := 1, path := [] }

private def sharedTask : ReferenceWorkQueue.Task :=
  { occurrence := producer, groups := [group0, group1] }

private def sharedQueue : ReferenceWorkQueue.State :=
  {
    groupNodes :=
      [
        { group := ⟨group0, none⟩, tasks := [producer] },
        { group := ⟨group1, none⟩, tasks := [producer] }
      ],
    tasks := [sharedTask],
    taskNodes := [{ task := sharedTask, childStreams := [7] }]
  }

private def afterFirstOwner : ReferenceWorkQueue.State :=
  { sharedQueue with groupNodes := [{ group := ⟨group1, none⟩, tasks := [producer] }] }

private def acquired : ResourceState :=
  ResourceState.empty.set (.stream 7) (.owned (.producer producer))

private def adopted : ResourceState := acquired.adopt producer [.stream 7]

private theorem handoff
    : ResourceReplay ResourceState.empty
        [.acquire (.stream 7) (.producer producer), .adopt producer [.stream 7]]
        adopted :=
  .cons (.acquire _ _ _ rfl) (.cons (.adopt _ _ _) (.nil _))

-- Raw local-site tests: a surviving co-owner prevents disposal; the last owner requests it.
example : (({ queue := sharedQueue } : State).removeGroup 0).2 = [] := by cbv

example
    : (({ queue := afterFirstOwner } : State).removeGroup 1).2
      = [.task producer, .stream 7] := by cbv

example : (adopted.observeFusedRemoval { queue := sharedQueue } 0).2 = [] := by
  cbv

example
    : (adopted.observeFusedRemoval { queue := sharedQueue } 0).1 (.stream 7)
      = .owned .queue := by cbv

example
    : (adopted.observeFusedRemoval { queue := afterFirstOwner } 1).2
      = [.requestCleanup (.stream 7)] := by cbv

example
    : (adopted.observeFusedRemoval { queue := afterFirstOwner } 1).1 (.stream 7)
      = .cleanupRequested .queue := by cbv

-- Cancellation observations preserve independently acquired producer-owned suffix work.
private def suffix : ResourceState :=
  adopted.set (.stream 9) (.owned (.producer producer))

example
    : (suffix.observeFusedRemoval { queue := afterFirstOwner } 1).1 (.stream 9)
      = .owned (.producer producer) := by
  exact suffix.requestQueueCleanup_foreign _ _ (by simp [suffix, ResourceState.set])

example
    : (adopted.requestQueueCleanup [.stream 7, .stream 7]).2
      = [.requestCleanup (.stream 7)] := by cbv

example
    : (adopted.requestQueueCleanup [.stream 7, .stream 7]).1 (.stream 7)
      = .cleanupRequested .queue := by cbv

-- Successful release transfers the task before a later owner failure: no failure cleanup.
private def transferred : ReferenceWorkQueue.State :=
  (sharedQueue.finishGroupSuccess { group := ⟨group0, none⟩, tasks := [producer] }).1

example : (({ queue := transferred } : State).removeGroup 1).2 = [] := by cbv

-- The dynamic effect walk visits live records once despite cycles, shared and stale links.
private def tangledQueue : ReferenceWorkQueue.State :=
  {
    sharedQueue with
      groupNodes :=
        [
          { group := ⟨group0, none⟩, tasks := [producer], childGroups := [99, 0, 1, 1] },
          { group := ⟨group1, none⟩, tasks := [producer], childGroups := [0, 99] }
        ]
  }

example
    : (({ queue := tangledQueue } : State).removeGroup 0).2
      = [.task producer, .stream 7] := by cbv

example (state : State) (keys : List Nat)
    : ∃ current retired targets,
        State.removeGroup.walk (state.queue.groupNodes.length + 1) state keys [] []
          = (current, retired, uniqueCleanupTargets targets)
        ∧ PruningGroups state.queue keys current.queue targets := by
  simpa using pruningGroups_witness (state.queue.groupNodes.length + 1) state keys [] []
    List.nodup_nil (by omega)

-----------------------------------------------------------------------------------------
-- Generated work uses one acquisition/adoption/request history at actual dispatch
-----------------------------------------------------------------------------------------

private abbrev generatedObserved :=
  SharedOwnerFailure.leases.observeHandlerCleanup SharedOwnerFailure.staged.state
    SharedOwnerFailure.failureG

private theorem generated_history
    : ResourceReplay ResourceState.empty
        ([
            .acquire (.stream 2) (.producer SharedOwnerFailure.heldProducer),
            .adopt SharedOwnerFailure.heldProducer [.stream 2]
          ]
          ++ generatedObserved.2)
        generatedObserved.1 :=
  SharedOwnerFailure.handoff.append
    (SharedOwnerFailure.leases.observeHandlerCleanup_replay _ _)

example : generatedObserved.2 = [.requestCleanup (.stream 2)] := by cbv
example : generatedObserved.1 (.stream 2) = .cleanupRequested .queue := by cbv

example : generatedObserved.1 (.stream 2) ≠ .unacquired :=
  (SharedOwnerFailure.leases.observeHandlerCleanup_replay _ _).never_forgets _
    (by rw [SharedOwnerFailure.source_owned]; simp)

private theorem generated_request_observed
    : HostEffect.cancelSource 2 ∈ SharedOwnerFailure.firstFailure.effects := by
  have listed : SharedOwnerFailure.firstFailure.effects =
      [.abortTask SharedOwnerFailure.heldProducer, .cancelSource 2, .abortStreamQueue 2] := by cbv
  rw [listed]
  exact List.mem_cons_of_mem _ List.mem_cons_self

example : ReferenceWorkQueue.ExecutedWork SharedOwnerFailure.work :=
  SharedOwnerFailure.executed

example : SharedOwnerFailure.schedule.ValidFor SharedOwnerFailure.work :=
  SharedOwnerFailure.source_valid

example
    : StopCoverage HeldSourceCleanup.staged.state
        (HeldSourceCleanup.leases.observeStop HeldSourceCleanup.staged.state).1 := by
  intro target owned
  exact False.elim
    ((HeldSourceCleanup.leases.observeStop_no_owned HeldSourceCleanup.staged.state
        (by cbv) HeldSourceCleanup.staged_coverage target)
      owned)

-- The independent acquired inventory uses one actual removal endpoint and history.
example : FusedRemovalResourceSafety := FusedRemovalResourceSafety_holds

example (resources : ResourceState) (before : State) (event : GraphEvent)
    : ResourceReplay resources (resources.observeHandlerCleanup before event).2
        (resources.observeHandlerCleanup before event).1 :=
  resources.observeHandlerCleanup_replay _ _

#print axioms FusedRemovalResourceSafety_holds
#print axioms pruningGroups_witness
#print axioms pruningRemoval_witness
#print axioms ResourceState.observeHandlerCleanup_actions
#print axioms ResourceState.observeStop_no_owned
#print axioms generated_history
#print axioms generated_request_observed

end AlternativeResourceRequestChecks
