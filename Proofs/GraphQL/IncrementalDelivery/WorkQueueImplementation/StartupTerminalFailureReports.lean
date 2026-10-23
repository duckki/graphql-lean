import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupFailureReportReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.Causality

/-! Actual startup terminal markers have observed reports and therefore semantic failures. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Startup initialization does not terminate before at least one supplied host batch. -/
theorem State.startup_terminal_inputs_nonempty {work inputs}
    (startup : InitialStartup)
    (ended
      : let initial := State.initialize (Work.fromExecution work) startup
        (initial.runNormalized inputs).1.terminated = true)
    : inputs ≠ [] := by
  intro empty
  subst inputs
  dsimp only at ended
  rw [State.runNormalized_replayBatches] at ended
  change (State.initialize (Work.fromExecution work)
    startup).terminated = true at ended
  rw [State.initializeWithStartup_terminated] at ended
  cases ended

/-- Every terminal startup cancellation marker has its positive report in actual atoms.
The exact raw diagnostic control survives the real publisher and removal of termination.
-/
theorem ExecutedWork.startup_runNormalized_cancelledRecordsReported {work inputs}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (matched : startup.MatchesWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (ended
      : ((State.initialize (Work.fromExecution work) startup).runNormalized
          inputs).1.terminated
        = true)
    : let initial := State.initialize (Work.fromExecution work) startup
      (initial.runNormalized inputs).1.CancelledRecordsReported work
        (initial.nonterminalAtoms inputs) := by
  let initial := State.initialize (Work.fromExecution work) startup
  have raw := generated.startup_rawBatches_cancelledRecordsReported startup matched valid started
  dsimp only at raw ⊢
  rw [State.rawBatches_state, ← State.runNormalized_replayBatches] at raw
  have completed := raw.completed (State.runNormalized_terminalPending
    (by rw [State.initializeWithStartup_terminated]; intro impossible; cases impossible)
    inputs ended)
  intro node dependencies known cancelled
  have reported := (completed node dependencies known cancelled).normalized
    ({ active := initial.initialGroups ++ initial.initialStreams } : IncrementalPublisher)
  obtain ⟨reporter, errors, positive, emitted, ancestor⟩ := reported
  rw [← initial.runNormalized_rawBatches inputs] at emitted
  exact ⟨reporter, errors, positive, List.mem_filter.mpr ⟨emitted, rfl⟩, ancestor⟩

/-- An observed report for a group or full ancestor establishes its semantic failure.
This uses the same explanation's licensed cuts, independently of hidden cancellation state.
-/
theorem GroupFailureReported.nodeFailed
    {work groups streams events matching failures node dependencies producer}
    (reported : GroupFailureReported events node dependencies)
    (explained : Explains work groups streams events matching failures)
    (known : NodeAt work node .group dependencies producer)
    : NodeFailed work matching events failures node.ref := by
  obtain ⟨reporter, errors, _, emitted, ancestry⟩ := reported
  obtain ⟨index, selected⟩ := List.mem_iff_getElem?.mp emitted
  obtain ⟨_, _, available, _, _, allowed⟩ := explained
  have atEvent := allowed index _ selected
  simp only [EventAllowed] at atEvent
  have failed : NodeFailed work matching (events.take index) failures reporter.ref := by
    rw [nodeFailed_filter (Nat.le_refl _)] at atEvent
    exact atEvent.2.2.1
  have final : NodeFailed work matching events failures reporter.ref := by
    simpa only [List.take_append_drop] using failed.append (events.drop index)
  rcases ancestry with same | above
  · exact same ▸ final
  · exact NodeFailed.groupDependency known above final

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
