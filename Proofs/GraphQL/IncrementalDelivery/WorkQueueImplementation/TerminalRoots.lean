import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TerminationShape
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupNoticeTracking

/-! Concrete termination exhausts active roots; this alone does not account for latent work. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Only the batch boundary can set the terminal flag
-----------------------------------------------------------------------------------------

/-- A batch preserves the invariant that termination implies two empty root lists.
Witness: an already terminated queue is unchanged; a running queue sets the flag only
after the empty-root test. Individual handlers cannot set it.
-/
theorem State.handleGraphEvents_terminalRoots {queue : State}
    (prior : queue.terminated = true → queue.rootGroups = [] ∧ queue.rootStreams = [])
    (events : List GraphEvent)
    : (queue.handleGraphEvents events).1.terminated = true
      → (queue.handleGraphEvents events).1.rootGroups = []
        ∧ (queue.handleGraphEvents events).1.rootStreams = [] := by
  rw [State.handleGraphEvents_eq_rawEventReplay]
  cases ended : queue.terminated with
  | true => simpa only [ended, ↓reduceIte] using prior
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      split
      · rename_i empty
        intro _
        simpa using empty
      · intro impossible
        rw [State.rawEventReplay_terminated, ended] at impossible
        cases impossible

/-- Publisher replay preserves the same terminal-root invariant across arbitrary batches.
Witness: its state projection is the actual queue batch fold; no source validity or start
assumption is needed for this concrete invariant.
-/
theorem State.runNormalized_terminalRoots {queue : State}
    (prior : queue.terminated = true → queue.rootGroups = [] ∧ queue.rootStreams = [])
    (inputs : List (List GraphEvent))
    : (queue.runNormalized inputs).1.terminated = true
      → (queue.runNormalized inputs).1.rootGroups = []
        ∧ (queue.runNormalized inputs).1.rootStreams = [] := by
  rw [State.runNormalized_stateFold]
  induction inputs generalizing queue with
  | nil => exact prior
  | cons batch rest ih =>
      exact ih (State.handleGraphEvents_terminalRoots prior batch)

/-- Every terminated initialized queue has exhausted its concrete active roots.
Witness: initialization starts with a false terminal flag, then batch replay preserves
the conditional empty-root invariant, even for arbitrary raw input.
-/
theorem createWorkQueue_terminalRoots (work : Work) (inputs : List (List GraphEvent))
    (ended : ((State.initialize work).runNormalized inputs).1.terminated = true)
    : ((State.initialize work).runNormalized inputs).1.rootGroups = []
      ∧ ((State.initialize work).runNormalized inputs).1.rootStreams = [] :=
  State.runNormalized_terminalRoots
    (by rw [createWorkQueue_terminated]; intro impossible; cases impossible) inputs ended

-----------------------------------------------------------------------------------------
-- Started eventwise replay shares the final root lists
-----------------------------------------------------------------------------------------

/-- A terminated started replay also has empty roots before publisher normalization.
Witness: accepted batches and flattened eventwise replay differ only in the terminal flag.
This transports concrete emptiness, not abstract task or latent-node coverage.
-/
theorem createWorkQueue_replayGraphEvents_terminalRoots {work inputs}
    (started : inputsStarted work inputs = true)
    (ended
      : ((State.initialize (Work.fromExecution work)).runNormalized inputs).1.terminated
        = true)
    : ((State.initialize (Work.fromExecution work)).replayGraphEvents
          inputs.flatten).rootGroups
        = []
      ∧ ((State.initialize (Work.fromExecution work)).replayGraphEvents
          inputs.flatten).rootStreams
        = [] := by
  have empty := createWorkQueue_terminalRoots (Work.fromExecution work) inputs ended
  obtain ⟨flag, same⟩ := State.runNormalized_stateCore _ inputs
    ((inputsStarted_eq_batchesStarted work inputs) ▸ started)
  simpa only [same] using empty

/-- At termination, every announced group has a completion or a concrete cancellation mark.
Witness: eventwise notice tracking excludes the active-root alternative. The stronger
generated-work result in `GroupCompletionReplay` eliminates silent cancellation as well.
-/
theorem createWorkQueue_terminalGroupTracking {work inputs ref}
    (started : inputsStarted work inputs = true)
    (ended
      : ((State.initialize (Work.fromExecution work)).runNormalized inputs).1.terminated
        = true)
    (announced
      : ref
        ∈ (State.initialize (Work.fromExecution work)).rootGroups
          ++ ((State.initialize (Work.fromExecution work)).rawEventReplay
                inputs.flatten).2.flatMap
              rawGroupNoticeRefs)
    : ref
        ∈ ((State.initialize (Work.fromExecution work)).replayGraphEvents
            inputs.flatten).cancelledGroups
      ∨ ref
        ∈ ((State.initialize (Work.fromExecution work)).rawEventReplay
            inputs.flatten).2.flatMap
            rawGroupClosureRefs := by
  have tracked := State.rawEventReplay_groupNoticeTracking
    (State.initialize (Work.fromExecution work)) inputs.flatten ref announced
  have empty := (createWorkQueue_replayGraphEvents_terminalRoots started ended).1
  rw [State.rawEventReplay_state] at tracked
  exact tracked.resolve_left (by rw [empty]; simp)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
