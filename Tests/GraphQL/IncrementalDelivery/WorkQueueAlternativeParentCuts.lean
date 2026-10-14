import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.GeneratedParentCuts
import Tests.GraphQL.IncrementalDelivery.Fixtures.SharedOwnerFailure

open GraphQL.IncrementalDelivery.Tests

namespace AlternativeParentCutChecks
open GraphQL.IncrementalDelivery
open AlternativeWorkQueue
open AlternativeWorkQueue.NativeRefinement

-- Pin the exact original target, without an extra safe-cut or inventory hypothesis.
example : GeneratedParentCuts := GeneratedParentCuts_holds

example {work : Work} (generated : ReferenceWorkQueue.ExecutedWork work)
    (inputs : List (List GraphEvent))
    (valid : ReferenceWorkQueue.ValidGraphEvents work inputs.flatten)
    (started : ReferenceWorkQueue.inputsStarted work inputs = true) (key : Nat)
    : groupIsHealthy ((State.initialize work).runNormalized inputs).1.queue key
      = ((State.initialize work).runNormalized inputs).1.queue.groupIsHealthy key :=
  generatedReplay_groupIsHealthy_eq_reference generated inputs valid started key

example
    : SafeParentCuts
        ((State.initialize SharedOwnerFailure.work).runNormalized
          SharedOwnerFailure.inputs).1.queue :=
  generatedReplay_safeParentCuts SharedOwnerFailure.executed SharedOwnerFailure.inputs
    SharedOwnerFailure.valid_events SharedOwnerFailure.started

-- Exercise an actual nonterminal failure prefix, before terminal record clearing.
private def activePrefix : List (List GraphEvent) :=
  [
    [SharedOwnerFailure.parentSuccess],
    [SharedOwnerFailure.success],
    [SharedOwnerFailure.failureG]
  ]

private theorem activePrefix_valid
    : ReferenceWorkQueue.ValidGraphEvents SharedOwnerFailure.work activePrefix.flatten :=
  SharedOwnerFailure.valid_events.prefix ⟨[SharedOwnerFailure.failureH], rfl⟩

example
    : SafeParentCuts
        ((State.initialize SharedOwnerFailure.work).runNormalized activePrefix).1.queue :=
  generatedReplay_safeParentCuts SharedOwnerFailure.executed activePrefix
    activePrefix_valid (by rw [SharedOwnerFailure.work_shape]; cbv)

#guard
  !((State.initialize SharedOwnerFailure.work).runNormalized
      activePrefix).1.queue.terminated
#guard
  !((State.initialize SharedOwnerFailure.work).runNormalized
      activePrefix).1.queue.groupNodes.isEmpty
#guard
  ((State.initialize SharedOwnerFailure.work).runNormalized
    activePrefix).1.queue.cancelledGroups
  |>.contains 0

-- An arbitrary child-first batch can create the raw orphan; it is not generated lowering.
private def retiredParent : ReferenceWorkQueue.State :=
  { registeredGroups := [0], cancelledGroups := [0] }

private def child : ReferenceWorkQueue.Group :=
  { node := { ref := 2, path := [] }, parent := some 1 }

private def parent : ReferenceWorkQueue.Group :=
  { node := { ref := 1, path := [] }, parent := some 0 }

private def childFirst : ReferenceWorkQueue.State :=
  (retiredParent.addGroups [child, parent]).1

#guard groupIsHealthy childFirst 2
#guard !childFirst.groupIsHealthy 2

example : ¬SafeParentCuts childFirst := by
  intro cuts
  have notCancelled := cuts ({ group := child } : ReferenceWorkQueue.GroupNode)
    (by
      change ({ group := child } : ReferenceWorkQueue.GroupNode) ∈ [{ group := child }]
      exact List.mem_cons_self) 1 rfl (by decide)
  exact notCancelled (by decide)

-- The exact parent-first chain refuses both descendants of the failed retired parent.
private def chain : List Execution.DeliveryNode :=
  [child.node, parent.node, { ref := 0, path := [] }]

private def parentFirst : ReferenceWorkQueue.State :=
  (retiredParent.addGroups (ReferenceWorkQueue.Work.fromExecution.groupChain chain)).1

example
    : ReferenceWorkQueue.ParentsBefore []
        (ReferenceWorkQueue.Work.fromExecution.groupChain chain) :=
  ReferenceWorkQueue.groupChain_parentsBefore chain

#guard parentFirst.groupNodes.isEmpty
#guard parentFirst.cancelledGroups == [0, 1, 2]
#guard !groupIsHealthy parentFirst 2
#guard !parentFirst.groupIsHealthy 2

#print axioms GeneratedParentCuts_holds
#print axioms generatedReplay_safeParentCuts
#print axioms generatedReplay_groupIsHealthy_eq_reference
#print axioms ReferenceWorkQueue.ExecutedWork.runNormalized_liveParentsUncancelled

end AlternativeParentCutChecks
