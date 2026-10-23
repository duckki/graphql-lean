import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.NativeHealth
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ParentCutsHandlers
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ReferenceReplay

/-! Generated replay has safe missing-parent cuts and uses the task-presence check. -/

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

/-- Task-presence settlement checking holds at every replay boundary, including raw ones. -/
theorem generatedReplay_taskPresenceChecked (work : Work)
    (inputs : List (List GraphEvent))
    : TaskPresenceChecked ((State.initialize work).runNormalized inputs).1.queue :=
  taskPresenceChecked_holds _

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
