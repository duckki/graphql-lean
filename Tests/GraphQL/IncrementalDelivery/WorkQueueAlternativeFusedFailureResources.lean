import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedFailureResources

/-! Check the actual failed-task fold and its compatible resource-request witness. -/

namespace AlternativeFusedFailureResourceChecks
open GraphQL.IncrementalDelivery
open GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open GraphQL.IncrementalDelivery.AlternativeWorkQueue

example : FusedTaskFailureResourceSafety := FusedTaskFailureResourceSafety_holds

private def first : Execution.DeliveryNode := { ref := 0, path := [] }
private def second : Execution.DeliveryNode := { ref := 1, path := [] }
private def failed : WorkQueueSemantics.Occurrence := .executionGroup [0]
private def held : WorkQueueSemantics.Occurrence := .executionGroup [1]

private def shared : State :=
  {
    queue :=
      {
        rootGroups := [0, 1]
        groupNodes :=
          [
            { group := ⟨first, none⟩, tasks := [failed, held] },
            { group := ⟨second, none⟩, tasks := [failed, held] }
          ]
        tasks :=
          [
            { occurrence := failed, groups := [first, second] },
            { occurrence := held, groups := [first, second] }
          ]
        taskNodes :=
          [
            { task := { occurrence := failed, groups := [first, second] } },
            {
              task := { occurrence := held, groups := [first, second] },
              childStreams := [7]
            }
          ]
      }
  }

-- Either owner alone protects the held task; the full handler removes both in sequence.
example : (shared.removeGroup 0).2 = [] := by cbv
example : (shared.removeGroup 1).2 = [] := by cbv

example
    : (shared.taskFailure failed 1).2.1
      = [.groupFailure first 1, .groupFailure second 1] := by cbv

example
    : (shared.handleGraphEvent (.taskFailure failed 1)).2.2.1
      = [.abortTask held, .cancelSource 7, .abortStreamQueue 7] := by cbv

example : (shared.taskFailure failed 1).1.queue.taskNode? held = none := by cbv

example
    : .abortTask failed ∉ (shared.handleGraphEvent (.taskFailure failed 1)).2.2.1 := by
  have effects : (shared.handleGraphEvent (.taskFailure failed 1)).2.2.1
      = [.abortTask held, .cancelSource 7, .abortStreamQueue 7] := by cbv
  rw [effects]
  intro member
  rcases List.mem_cons.mp member with same | later
  · have indices := WorkQueueSemantics.Occurrence.executionGroup.inj
      (HostEffect.abortTask.inj same)
    cases indices
  · rcases List.mem_cons.mp later with same | last
    · cases same
    · cases List.mem_singleton.mp last

private def leases : ResourceState :=
  fun target => if target = .stream 7 then .owned .queue else .unacquired

example
    : (leases.observeHandlerCleanup shared (.taskFailure failed 1)).1 (.stream 7)
      = .cleanupRequested .queue := by cbv

example
    : (leases.observeHandlerCleanup shared (.taskFailure failed 1)).2
      = [.requestCleanup (.stream 7)] := by cbv

-- A stale input creates no requests; dormant failures do not dispose before activation.
example : (shared.taskFailure (.executionGroup [9]) 1).2.2 = [] := by cbv

example
    : (State.taskFailure
        { shared with queue := { shared.queue with rootGroups := [] } } failed 1).2.2
      = [] := by cbv

#print axioms FusedTaskFailureResourceSafety_holds
#print axioms State.taskFailure_heldSource
#print axioms ResourceState.observeHandlerCleanup_replay
#print axioms ResourceState.observeHandlerCleanup_actions

end AlternativeFusedFailureResourceChecks
