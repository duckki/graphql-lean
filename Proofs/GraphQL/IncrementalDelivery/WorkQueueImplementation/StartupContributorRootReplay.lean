import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialStartupBatchShape
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialStartupRootCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialStartupSourceFrames
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ContributorRootReplay

/-! Actual startup terminal replay retires every registered contributor through root coverage. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Initial startup root paths and source-valid replay cover every surviving contributor. -/
theorem ExecutedWork.startup_runNormalized_contributorsCovered {work inputs}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (matched : startup.MatchesWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    : let initial := State.initialize (Work.fromExecution work) startup
      (initial.runNormalized inputs).1.ContributorsCovered := by
  let initial := State.initialize (Work.fromExecution work) startup
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have frame : ContributorRootFrame initial work parents [] :=
    ⟨generated.initialStartup_uncancelledReplayFrame canonical startup matched,
      fun _ _ ref _ live => generated.initialStartup_live_group_root_coverage startup ref live⟩
  have final := (frame.runNormalized generated canonical inputs valid
    (by rwa [← inputsStartedWithStartup_eq_batchesStarted])).covered
  rw [State.runNormalized_replayBatches] at final
  dsimp only
  rwa [State.runNormalized_replayBatches]

/-- Empty terminal roots retire every registered contributor after actual startup replay.
No healthy-owner, consumed-failure or already-reported premise is needed for retirement.
-/
theorem ExecutedWork.startup_terminal_registeredContributor_retired
    {work inputs task ref} (generated : ExecutedWork work) (startup : InitialStartup)
    (matched : startup.MatchesWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (ended
      : let initial := State.initialize (Work.fromExecution work) startup
        (initial.runNormalized inputs).1.terminated = true)
    (registered
      : let initial := State.initialize (Work.fromExecution work) startup
        task ∈ (initial.runNormalized inputs).1.tasks)
    (contributes : ref ∈ task.groups.map Execution.DeliveryNode.ref)
    : let initial := State.initialize (Work.fromExecution work) startup
      (initial.runNormalized inputs).1.RetiredGroup ref := by
  let initial := State.initialize (Work.fromExecution work) startup
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have frame := generated.startup_runNormalized_frame canonical startup matched inputs valid started
  apply State.RetiredGroup.of_lookup_none
    (frame.pending.taskGroups task registered ref contributes)
  cases found : (initial.runNormalized inputs).1.groupNode? ref with
  | none => rfl
  | some node =>
      obtain ⟨root, active, _⟩ := generated.startup_runNormalized_contributorsCovered startup
        matched valid started task registered ref contributes ⟨node, found⟩
      have roots := initial.runNormalized_terminalRoots (by
        rw [State.initializeWithStartup_terminated]
        intro impossible; cases impossible) inputs ended
      rw [roots.1] at active
      cases active

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
