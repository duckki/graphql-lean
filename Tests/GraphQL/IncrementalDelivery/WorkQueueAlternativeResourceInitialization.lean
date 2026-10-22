import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ResourceInitialization
import Tests.GraphQL.IncrementalDelivery.Fixtures.RejectedTaskCleanup

open GraphQL.IncrementalDelivery.Tests

/-! Initial structural acquisition mapping and independent producer acquisition between inputs. -/

namespace AlternativeResourceInitializationChecks
open GraphQL.IncrementalDelivery
open AlternativeWorkQueue
open AlternativeWorkQueue.NativeRefinement

example : GeneratedInitialResourcesRepresented :=
  GeneratedInitialResourcesRepresented_holds

private def resources :=
  ResourceState.empty.set (.task RejectedTaskCleanup.producer) (.owned .queue)

private theorem producerKnown
    : WorkQueueSemantics.TaskAt SharedOwnerFailure.work RejectedTaskCleanup.producer
        [0, 1] none (.object [] (.ok (SharedOwnerFailure.data, 0))) := by
  refine ⟨[{ node := SharedOwnerFailure.groupG }, { node := SharedOwnerFailure.groupH }], [],
    { result := .ok (SharedOwnerFailure.data, 0) }, SharedOwnerFailure.childWork, [], ?_, rfl, rfl⟩
  rw [SharedOwnerFailure.work_shape]
  rfl

private theorem identity
    : InitialResourcesMatchWork SharedOwnerFailure.work resources := by
  constructor
  · intro occurrence owned
    by_cases same : occurrence = RejectedTaskCleanup.producer
    · subst occurrence
      exact ⟨[1, 0], [0, 1], _, rfl, producerKnown⟩
    · simp [resources, ResourceState.set, ResourceState.empty, same] at owned
  · intro key owned
    simp [resources, ResourceState.set, ResourceState.empty] at owned

private theorem initial
    : QueueResourcesRepresented (State.initialize SharedOwnerFailure.work).queue []
        resources :=
  GeneratedInitialResourcesRepresented_holds _ SharedOwnerFailure.executed resources
    identity

-- Real early child acquisition does not require child queue registration yet.
example
    : QueueResourcesRepresented (State.initialize SharedOwnerFailure.work).queue []
        (resources.set (.task RejectedTaskCleanup.child)
          (.owned (.producer RejectedTaskCleanup.producer))) := by
  apply initial.interInputReplay (actions := [.acquire (.task RejectedTaskCleanup.child)
    (.producer RejectedTaskCleanup.producer)])
  · exact .cons (.acquire _ _ _ (by
      simp [resources, ResourceState.set, ResourceState.empty, RejectedTaskCleanup.child,
        RejectedTaskCleanup.producer, SharedOwnerFailure.heldProducer])) (.nil _)
  · intro action member
    cases List.mem_singleton.mp member
    trivial

-- Arbitrary queue-owned acquisition is not silently licensed as an inter-input callback.
example : ¬InterInputResourceAction (.acquire (.stream 999) .queue) := by
  simp [InterInputResourceAction]

example
    : ¬InterInputResourceAction (.adopt RejectedTaskCleanup.producer [.stream 999]) := by
  simp [InterInputResourceAction]

#print axioms generatedInitial_taskRepresented
#print axioms GeneratedInitialResourcesRepresented_holds
#print axioms ResourceStep.interInput_owned_origin
#print axioms QueueResourcesRepresented.interInputReplay

end AlternativeResourceInitializationChecks
