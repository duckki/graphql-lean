import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ResourceOwnership
import Tests.GraphQL.IncrementalDelivery.Fixtures.WorkDeclarations

open GraphQL.IncrementalDelivery.Tests (declaredTask)

/-! Raw held-source cleanup fixture: last-owner failure requests disposal before unlinking.
Acquisition is ghost evidence; this module alone does not assert execution generates work.
-/

namespace GraphQL.IncrementalDelivery.Tests.HeldSourceCleanup
open AlternativeWorkQueue AlternativeWorkQueue.NativeRefinement
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.WorkQueueSemantics (Occurrence)

private def owner : DeliveryNode := { ref := 0, path := [] }
private def heldSource : DeliveryNode := { ref := 3, path := [] }

def work : Execution.Work :=
  .combine
    (declaredTask [{ node := owner }] [] ({ result := .ok ([], 0) })
      (.stream heldSource []))
    (declaredTask [{ node := owner }] [] ({ result := .error 1 }) .empty)

def success : GraphEvent :=
  .taskSuccess (.executionGroup [0])
    {
      value := { deliveryGroups := [owner], path := [], data := [] },
      work := ReferenceWorkQueue.Work.fromExecution (.stream heldSource []) [0, 0]
    }

def staged : GraphBatchResult :=
  (State.initialize work).handleGraphEvents [success]

def failed : GraphBatchResult :=
  staged.state.handleGraphEvents [.taskFailure (.executionGroup [1]) 1]

def leases : ResourceState :=
  ResourceState.adopt
    (ResourceState.empty.set (.stream 3) (.owned (.producer (.executionGroup [0]))))
    (.executionGroup [0]) [.stream 3]

/-- One shared ghost trace witnesses acquisition followed by the actual adoption identity.
It does not supply the missing native acquisition/registration bridge.
-/
theorem handoff
    : ResourceReplay ResourceState.empty
        [
          .acquire (.stream 3) (.producer (.executionGroup [0])),
          .adopt (.executionGroup [0]) [.stream 3]
        ] leases := by
  exact .cons (.acquire _ _ _ rfl) (.cons (.adopt _ _ _) (.nil _))

theorem adoption_observed : staged.effects = [.adopt (.executionGroup [0])] := by cbv

theorem owned : leases (.stream 3) = .owned .queue := by
  simp [leases, ResourceState.adopt, ResourceState.set]

theorem staged_coverage : StopCoverage staged.state leases := by
  intro target owned
  by_cases same : target = .stream 3
  · subst target
    cbv
    exact .tail _ (.head _)
  · simp [leases, ResourceState.adopt, ResourceState.set,
      ResourceState.empty, same] at owned

/-- Accounting can disappear only after the corresponding disposal request is observed. -/
theorem failure_loses_reachability
    : (.stream 3 : CleanupTarget) ∉ failed.state.cleanupTargets := by
  cbv
  exact List.not_mem_nil

theorem failure_effects
    : failed.effects
      = [.abortTask (.executionGroup [0]), .cancelSource 3, .abortStreamQueue 3] := by
  cbv

def requested : ResourceState :=
  leases.set (.stream 3) (.cleanupRequested .queue)

/-- The observed cancel operation licenses the ghost request, not asynchronous settlement. -/
theorem disposal
    : .cancelSource 3 ∈ failed.effects
      ∧ ResourceReplay leases [.requestCleanup (.stream 3)] requested := by
  refine ⟨?_, .cons (.request _ _ .queue owned) (.nil _)⟩
  rw [failure_effects]
  exact .tail _ (.head _)

theorem final_coverage : StopCoverage failed.state requested := by
  intro target owned
  by_cases same : target = .stream 3
  all_goals simp [requested, leases, ResourceState.adopt,
    ResourceState.set, ResourceState.empty, same] at owned

end GraphQL.IncrementalDelivery.Tests.HeldSourceCleanup
