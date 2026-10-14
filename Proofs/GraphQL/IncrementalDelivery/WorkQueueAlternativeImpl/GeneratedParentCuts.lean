import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.NativeHealth
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ParentCutsHandlers
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ReferenceReplay

/-! Generated replay discharges the live-ancestor guard's missing-parent boundary. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement

-----------------------------------------------------------------------------------------
-- Derived cuts in the actual alternative replay
-----------------------------------------------------------------------------------------

/-- Parent safety transfers through exact reference replay and terminal record clearing. -/
theorem generatedReplay_liveParentsUncancelled {work : Work}
    (generated : ReferenceWorkQueue.ExecutedWork work) (inputs : List (List GraphEvent))
    (valid : ReferenceWorkQueue.ValidGraphEvents work inputs.flatten)
    (started : ReferenceWorkQueue.inputsStarted work inputs = true)
    : ((State.initialize work).runNormalized inputs).1.queue.LiveParentsUncancelled := by
  rw [State.runNormalized_initialize work inputs generated valid started]
  simp only [State.fromReference]
  split
  · intro node member
    simp [State.clearRecords] at member
  · exact generated.runNormalized_liveParentsUncancelled inputs valid

/-- Every generated replay boundary has safe missing-parent cuts, including terminal ones. -/
theorem generatedReplay_safeParentCuts {work : Work}
    (generated : ReferenceWorkQueue.ExecutedWork work) (inputs : List (List GraphEvent))
    (valid : ReferenceWorkQueue.ValidGraphEvents work inputs.flatten)
    (started : ReferenceWorkQueue.inputsStarted work inputs = true)
    : SafeParentCuts ((State.initialize work).runNormalized inputs).1.queue := by
  intro node member parent same _missing
  exact generatedReplay_liveParentsUncancelled generated inputs valid started node member parent same

/-- Generated parent safety with no new source or reachability premises. -/
theorem GeneratedParentCuts_holds : GeneratedParentCuts := by
  intro work inputs generated valid started
  exact generatedReplay_safeParentCuts generated inputs valid started

/-- The live-ancestor and reference health guards agree on every key after generated replay.
This is model guard equivalence, not a projection of the actual native record map.
-/
theorem generatedReplay_groupIsHealthy_eq_reference {work : Work}
    (generated : ReferenceWorkQueue.ExecutedWork work) (inputs : List (List GraphEvent))
    (valid : ReferenceWorkQueue.ValidGraphEvents work inputs.flatten)
    (started : ReferenceWorkQueue.inputsStarted work inputs = true) (key : Nat)
    : groupIsHealthy ((State.initialize work).runNormalized inputs).1.queue key
      = ((State.initialize work).runNormalized inputs).1.queue.groupIsHealthy key :=
  groupIsHealthy_eq_reference _
    (generatedReplay_safeParentCuts generated inputs valid started) key

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
