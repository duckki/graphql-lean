import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.PruningProjection
import Tests.GraphQL.IncrementalDelivery.Fixtures.SharedOwnerFailure

open GraphQL.IncrementalDelivery.Tests

namespace AlternativePruningProjectionChecks
open GraphQL.IncrementalDelivery
open AlternativeWorkQueue
open AlternativeWorkQueue.NativeRefinement

-- Exact construction target: no caller-supplied forest, accounting, or source strengthening.
example : GeneratedPruningGroupProjection := GeneratedPruningGroupProjection_holds

private def activePrefix : List (List GraphEvent) :=
  [[SharedOwnerFailure.parentSuccess], [SharedOwnerFailure.success]]

private theorem valid
    : ReferenceWorkQueue.ValidGraphEvents SharedOwnerFailure.work activePrefix.flatten :=
  SharedOwnerFailure.valid_events.prefix
    ⟨[SharedOwnerFailure.failureG, SharedOwnerFailure.failureH], rfl⟩

example
    : ∃ parents,
        ((State.initialize SharedOwnerFailure.work).runNormalized
          activePrefix).1.queue.RemovalForest
          parents :=
  generatedReplay_removalForest SharedOwnerFailure.executed activePrefix valid
    (by rw [SharedOwnerFailure.work_shape]; cbv)

example
    : ∃ parents,
        ((State.initialize SharedOwnerFailure.work).runNormalized
          SharedOwnerFailure.inputs).1.queue.RemovalForest
          parents :=
  generatedReplay_removalForest SharedOwnerFailure.executed SharedOwnerFailure.inputs
    SharedOwnerFailure.valid_events SharedOwnerFailure.started

#guard
  !((State.initialize SharedOwnerFailure.work).runNormalized
      activePrefix).1.queue.terminated
#guard
  ((State.initialize SharedOwnerFailure.work).runNormalized
    SharedOwnerFailure.inputs).1.queue.terminated

example (root : Nat)
    : let queue :=
        ((State.initialize SharedOwnerFailure.work).runNormalized activePrefix).1.queue
      ∃ final targets,
        PruningGroups queue [root] final targets
        ∧ (({ queue := queue } : State).removeGroup root).2 = uniqueCleanupTargets targets
        ∧ ∀ key,
            (∃ node, final.groupNode? key = some node)
            ↔ ∃ node, (queue.removeGroup root).groupNode? key = some node :=
  GeneratedPruningGroupProjection_holds _ _ SharedOwnerFailure.executed valid
    (by rw [SharedOwnerFailure.work_shape]; cbv) root

-----------------------------------------------------------------------------------------
-- Raw cyclic input demonstrates why projection needs the derived generated forest
-----------------------------------------------------------------------------------------

private def group0 : Execution.DeliveryNode := { ref := 0, path := [] }
private def group1 : Execution.DeliveryNode := { ref := 1, path := [] }

private def task : ReferenceWorkQueue.Task :=
  { occurrence := .executionGroup [0], groups := [group0, group1] }

private def loopNode : ReferenceWorkQueue.GroupNode :=
  { group := ⟨group0, none⟩, childGroups := [0, 1], tasks := [task.occurrence] }

private def rawCycle : ReferenceWorkQueue.State :=
  {
    groupNodes := [loopNode, { group := ⟨group1, some 0⟩, tasks := [task.occurrence] }],
    tasks := [task],
    taskNodes := [{ task, childStreams := [7] }]
  }

-- Fixed-state collection revisits the loop and exhausts its budget before key 1.
example : ((rawCycle.removeGroup 0).groupNode? 1).isSome = true := by cbv

-- Dynamic disposal instead removes each live record before visiting its child frontier.
example
    : (({ queue := rawCycle } : State).removeGroup 0).2
      = [.task task.occurrence, .stream 7] := by cbv

example : ¬∃ parents, rawCycle.RemovalForest parents := by
  rintro ⟨parents, forest⟩
  have impossible := forest.increasing (parent := loopNode) (child := loopNode)
    List.mem_cons_self List.mem_cons_self (by decide)
  exact Nat.lt_irrefl _ impossible

#print axioms GeneratedPruningGroupProjection_holds
#print axioms generatedReplay_removalForest
#print axioms PruningGroups.groupPresent_iff_removeGroup
#print axioms PruningGroups.coversDescendants

end AlternativePruningProjectionChecks
