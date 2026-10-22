import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RootPathContinuation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TerminalRoots

/-! Previously root-covered groups cannot remain live after actual terminal batch replay. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- A ref covered at an actual FIFO boundary is absent after concrete termination.
Witness: continuation preserves its old root path or permanently retires it. The first
alternative contradicts empty terminal roots, including when the ref later becomes failed.
Every batch retains its own rejection snapshot and actual queue state. -/
theorem ExecutedWork.terminal_oldRootCovered_absent {work : Execution.Work}
    {inputs earlier batch later fifo tail target} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (splitInputs : inputs = earlier ++ batch :: later) (batchEq : batch = fifo ++ tail)
    (ended
      : ((State.initialize (Work.fromExecution work)).runNormalized inputs).1.terminated
        = true)
    (covered
      : let initial := State.initialize (Work.fromExecution work)
        let current :=
          (initial.replayBatches earlier).replayGraphEvents fifo
            (GraphEvent.availableFailures batch)
        ∃ root ∈ current.rootGroups, current.LiveDescendant root target)
    : ((State.initialize (Work.fromExecution work)).runNormalized inputs).1.groupNode?
        target
      = none := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  let initial := State.initialize (Work.fromExecution work)
  let boundary := initial.replayBatches earlier
  let available := GraphEvent.availableFailures batch
  have firstFrame := generated.uncancelledFrame_atBatchPrefix canonical earlier batch later []
    (splitInputs ▸ valid) (splitInputs ▸ started) List.nil_prefix
  simp only [State.replayGraphEvents, List.foldl_nil, List.append_nil] at firstFrame
  have currentFrame := generated.uncancelledFrame_atBatchPrefix canonical earlier batch later fifo
    (splitInputs ▸ valid) (splitInputs ▸ started) ⟨tail, batchEq.symm⟩
  have matching : ∀ event ∈ batch, event.MatchesWork work := by
    intro event member
    apply valid.eachMatches
    rw [splitInputs, List.flatten_append, List.flatten_cons]
    exact List.mem_append_right _ (List.mem_append_left _ member)
  have continuation := currentFrame.parent.replayGraphEvents_rootCoveredOrRetired generated
    canonical tail
    (fun event member => matching event (batchEq ▸ List.mem_append_right fifo member))
    (.inl covered) available
  have starts := splitInputs ▸ started
  rw [inputsStarted_eq_batchesStarted, State.batchesStarted_append, Bool.and_eq_true] at starts
  obtain ⟨running, _, _⟩ := boundary.batchesStarted_cons batch later starts.2
  have atBatch : (boundary.handleGraphEvents batch).1.RootCoveredOrRetired target := by
    obtain ⟨terminal, same⟩ := boundary.handleGraphEvents_stateCore batch running
    rw [same]
    change ({ boundary.replayGraphEvents batch available with terminated := terminal } : State)
      |>.RootCoveredOrRetired target
    have composed : boundary.replayGraphEvents batch available
        = (boundary.replayGraphEvents fifo available).replayGraphEvents tail available := by
      calc
        _ = boundary.replayGraphEvents (fifo ++ tail) available :=
          congrArg (fun events => boundary.replayGraphEvents events available) batchEq
        _ = _ := boundary.replayGraphEvents_append fifo tail available
    rw [composed]
    exact continuation.2.withTerminated terminal
  have batchFrame := firstFrame.parent.handleGraphEvents generated canonical batch matching
  have final := batchFrame.rawBatches_rootCoveredOrRetired generated canonical later
    (fun event member => valid.eachMatches (by
      rw [splitInputs, List.flatten_append, List.flatten_cons]
      exact List.mem_append_right _ (List.mem_append_right _ member))) atBatch
  rw [State.rawBatches_state] at final
  have same : (initial.runNormalized inputs).1
      = (boundary.handleGraphEvents batch).1.replayBatches later := by
    rw [State.runNormalized_replayBatches, splitInputs, State.replayBatches_append]
    rfl
  rw [← same] at final
  rcases final.2 with ⟨root, active, _⟩ | retired
  · have empty := (createWorkQueue_terminalRoots (Work.fromExecution work) inputs ended).1
    rw [empty] at active
    cases active
  · exact retired.lookup_none

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
