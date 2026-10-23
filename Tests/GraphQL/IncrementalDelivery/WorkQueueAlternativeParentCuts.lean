import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.GeneratedParentCuts
import Tests.GraphQL.IncrementalDelivery.Fixtures.SharedOwnerFailure

open GraphQL.IncrementalDelivery.Tests

namespace AlternativeParentCutChecks
open GraphQL.IncrementalDelivery
open AlternativeWorkQueue
open AlternativeWorkQueue.NativeRefinement

-- Pin the exact original target, without an extra safe-cut or inventory hypothesis.
example : GeneratedParentCuts := GeneratedParentCuts_holds

example (work : Work) (inputs : List (List GraphEvent))
    : TaskPresenceChecked ((State.initialize work).runNormalized inputs).1.queue :=
  generatedReplay_taskPresenceChecked work inputs

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

-- Recursive installation refuses descendants of an absent failed parent in either order.
private def retiredParent : ReferenceWorkQueue.State :=
  { registeredGroups := [0], cancelledGroups := [0] }

private def child : ReferenceWorkQueue.Group :=
  { node := { ref := 2, path := [] }, parent := some 1 }

private def parent : ReferenceWorkQueue.Group :=
  { node := { ref := 1, path := [] }, parent := some 0 }

private def childFirst : ReferenceWorkQueue.State :=
  (retiredParent.addGroups [child, parent]).1

#guard (childFirst.groupNode? 2).isNone
#guard childFirst.groupNodes.isEmpty
#guard childFirst.cancelledGroups == [0, 1, 2]

example : SafeParentCuts childFirst := by
  intro group member
  change group ∈ [] at member
  cases member

-- The exact parent-first chain refuses both descendants of the failed retired parent.
private def chain : List ReferenceWorkQueue.Group :=
  [⟨{ ref := 0, path := [] }, none⟩, parent, child]

private def parentFirst : ReferenceWorkQueue.State :=
  (retiredParent.addGroups chain).1

example : ReferenceWorkQueue.ParentsBefore [] chain := by
  simp [ReferenceWorkQueue.ParentsBefore, chain, parent, child]

example : childFirst = parentFirst := by cbv

#guard parentFirst.groupNodes.isEmpty
#guard parentFirst.cancelledGroups == [0, 1, 2]
#guard (parentFirst.groupNode? 2).isNone

#print axioms GeneratedParentCuts_holds
#print axioms generatedReplay_safeParentCuts
#print axioms generatedReplay_taskPresenceChecked
#print axioms ReferenceWorkQueue.ExecutedWork.runNormalized_liveParentsUncancelled

end AlternativeParentCutChecks
