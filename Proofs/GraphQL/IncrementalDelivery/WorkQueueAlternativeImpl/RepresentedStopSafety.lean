import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.BufferedStopCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ResourceRecords

/-! Separate acquired-lease representation from generated graph reachability. The native
bridge must construct representation for the actual same-run independent resource inventory.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open GraphQL.IncrementalDelivery.WorkQueueSemantics (Occurrence)
open GraphQL.IncrementalDelivery.ReferenceWorkQueue (TaskNode GroupNode)

private theorem generatedReplay_membershipEvidence {work inputs}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (valid : ReferenceWorkQueue.ValidGraphEvents work inputs.flatten)
    (started : ReferenceWorkQueue.inputsStarted work inputs = true)
    : let queue := ((State.initialize work).runNormalized inputs).1.queue
      queue.GroupMembershipSound := by
  rw [State.runNormalized_initialize work inputs generated valid started]
  simp only [State.fromReference]
  split
  · intro group impossible; cases impossible
  · obtain ⟨settled, _, accounted⟩ := generated.runNormalized_pendingAccounting inputs valid started
    exact accounted.sound

-----------------------------------------------------------------------------------------
-- The generated proof supplies coverage, rather than asking a native audit to assume it
-----------------------------------------------------------------------------------------

/-- Every represented target is reached by the actual generated stop walk.
Witness: live group membership supplies its permanent contributing task and rooted path;
buffered sources use generated buffered coverage, and active sources are explicit stop roots.
-/
theorem generatedReplay_representedTarget_covered {work inputs}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (valid : ReferenceWorkQueue.ValidGraphEvents work inputs.flatten)
    (started : ReferenceWorkQueue.inputsStarted work inputs = true)
    {target}
    (represented
      : RecordTargetRepresented ((State.initialize work).runNormalized inputs).1.queue
          target)
    : target ∈ ((State.initialize work).runNormalized inputs).1.cleanupTargets := by
  cases represented with
  | @task key occurrence group found linked =>
      have evidence := generatedReplay_membershipEvidence generated valid started
      have member := List.mem_of_find?_eq_some found
      obtain ⟨task, registered, _, contributes⟩ := evidence group member occurrence linked
      obtain ⟨root, active, path⟩ := GeneratedLiveContributorCoverage_holds work inputs generated
        valid started task registered group.group.node.ref contributes
        ⟨group, (ReferenceWorkQueue.State.groupNode?_ref found).symm ▸ found⟩
      have covered := GeneratedRootedStopCoverage_holds work inputs generated valid started root
        group.group.node.ref group occurrence active path
        ((ReferenceWorkQueue.State.groupNode?_ref found).symm ▸ found) linked
      exact covered (List.mem_append_left _ List.mem_cons_self)
  | activeStream active =>
      apply (mem_uniqueCleanupTargets _ _).mpr
      exact List.mem_append_right _ (List.mem_map_of_mem active)
  | @bufferedStream occurrence node key found stored held =>
      apply GeneratedBufferedStopCoverage_holds work inputs generated valid started occurrence node found stored
      simp only [State.cancelTask, found, Option.toList_some, List.flatMap_singleton]
      exact List.mem_append_right _ (List.mem_map_of_mem held)

/-- Concrete record representation suffices for generated acquired-lease stop coverage.
The complete independent resource inventory is still supplied, not inferred from targets.
-/
theorem generatedReplay_stopCoverage_of_representation {work inputs}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (valid : ReferenceWorkQueue.ValidGraphEvents work inputs.flatten)
    (started : ReferenceWorkQueue.inputsStarted work inputs = true)
    (resources : ResourceState)
    (represented
      : ResourcesRepresented ((State.initialize work).runNormalized inputs).1.queue
          resources)
    : StopCoverage ((State.initialize work).runNormalized inputs).1 resources := by
  intro target owned
  exact generatedReplay_representedTarget_covered generated valid started (represented target owned)

/-- Same-run stop reduction with record representation as the remaining native leaf.
It constructs one legal cleanup-request history and eliminates every queue-owned remainder;
it does not prove native acquisition completeness, settlement, or global quiescence.
-/
def GeneratedRepresentedStopSafety : Prop :=
  ∀ work inputs,
    ReferenceWorkQueue.ExecutedWork work
    → ReferenceWorkQueue.ValidGraphEvents work inputs.flatten
    → ReferenceWorkQueue.inputsStarted work inputs = true
    → ∀ resources,
        let state := ((State.initialize work).runNormalized inputs).1
        ResourcesRepresented state.queue resources
        → state.stopped = false
        → ResourceReplay resources (resources.observeStop state).2
            (resources.observeStop state).1
          ∧ ∀ target, (resources.observeStop state).1 target ≠ .owned .queue

/-- Generated topology and record coverage discharge every edge except native representation. -/
theorem GeneratedRepresentedStopSafety_holds : GeneratedRepresentedStopSafety := by
  intro work inputs generated valid started resources
  dsimp only
  intro represented running
  exact ⟨resources.observeStop_replay _, resources.observeStop_no_owned _ running
    (generatedReplay_stopCoverage_of_representation generated valid started resources represented)⟩

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
