import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TerminationShape
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupNoticeTracking
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.BatchOutputReplay

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
        have both := Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp empty).1
        exact ⟨List.isEmpty_iff.mp both.1, List.isEmpty_iff.mp both.2⟩
      · intro impossible
        rw [State.rawEventReplay_terminated _ _ (GraphEvent.availableFailures events), ended]
          at impossible
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

/-- A running batch terminates only after consuming all pending internal notices. -/
theorem State.handleGraphEvents_terminalPending {queue : State}
    (prior : queue.terminated = true → queue.groupFailureEvents = [])
    (events : List GraphEvent)
    : (queue.handleGraphEvents events).1.terminated = true
      → (queue.handleGraphEvents events).1.groupFailureEvents = [] := by
  rw [State.handleGraphEvents_eq_rawEventReplay]
  cases ended : queue.terminated with
  | true => simpa only [ended, ↓reduceIte] using prior
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      split
      · rename_i empty
        intro _
        exact List.isEmpty_iff.mp (Bool.and_eq_true_iff.mp empty).2
      · intro impossible
        rw [State.rawEventReplay_terminated _ _ (GraphEvent.availableFailures events), ended]
          at impossible
        cases impossible

/-- Normalized batch replay retains the pending-FIFO termination condition. -/
theorem State.runNormalized_terminalPending {queue : State}
    (prior : queue.terminated = true → queue.groupFailureEvents = [])
    (inputs : List (List GraphEvent))
    : (queue.runNormalized inputs).1.terminated = true
      → (queue.runNormalized inputs).1.groupFailureEvents = [] := by
  rw [State.runNormalized_stateFold]
  induction inputs generalizing queue with
  | nil => exact prior
  | cons batch rest ih => exact ih (State.handleGraphEvents_terminalPending prior batch)

/-- Every terminated initialized queue has consumed all its internal group notices. -/
theorem createWorkQueue_terminalPending (work : Work) (inputs : List (List GraphEvent))
    (ended : ((State.initialize work).runNormalized inputs).1.terminated = true)
    : ((State.initialize work).runNormalized inputs).1.groupFailureEvents = [] :=
  State.runNormalized_terminalPending
    (by rw [createWorkQueue_terminated]; intro impossible; cases impossible) inputs ended

-----------------------------------------------------------------------------------------
-- Actual batch state and output retain the final root and notice evidence
-----------------------------------------------------------------------------------------

/-- A terminated actual batch replay has empty group and stream root lists.
Witness: publisher normalization projects to the same batch state without changing cache
visibility or flattening source input boundaries.
-/
theorem createWorkQueue_replayBatches_terminalRoots {work inputs}
    (ended
      : ((State.initialize (Work.fromExecution work)).runNormalized inputs).1.terminated
        = true)
    : ((State.initialize (Work.fromExecution work)).replayBatches inputs).rootGroups = []
      ∧ ((State.initialize (Work.fromExecution work)).replayBatches inputs).rootStreams
        = [] := by
  have empty := createWorkQueue_terminalRoots (Work.fromExecution work) inputs ended
  rwa [State.runNormalized_replayBatches] at empty

/-- Actual raw batch replay retains every prior cancellation marker. -/
theorem State.rawBatches_cancelledGroups_subset (queue : State)
    (batches : List (List GraphEvent))
    : queue.cancelledGroups.Subset (queue.rawBatches batches).1.cancelledGroups := by
  induction batches generalizing queue with
  | nil => exact List.Subset.refl _
  | cons batch rest ih =>
      exact (queue.handleGraphEvents_cancelledGroups_subset batch).trans (ih _)

/-- Actual batches retain an active, cancelled or completed explanation for every notice.
Witness: compose the per-batch tracking theorem over the same raw-output and queue fold.
-/
theorem State.rawBatches_groupNoticeTracking (queue : State)
    (batches : List (List GraphEvent))
    : GroupNoticeTracking queue.rootGroups (queue.rawBatches batches) := by
  induction batches generalizing queue with
  | nil => exact .silent (List.Subset.refl _)
  | cons batch rest ih =>
      exact (queue.handleGraphEvents_groupNoticeTracking batch).append (ih _)
        (State.rawBatches_cancelledGroups_subset _ rest)

/-- At termination, each announced group has a completion or concrete cancellation mark.
Witness: actual-batch notice tracking excludes the empty active-root alternative. The
stronger generated-work completion bridge must separately rule out silent cancellation.
-/
theorem createWorkQueue_terminalGroupTracking {work inputs ref}
    (_started : inputsStarted work inputs = true)
    (ended
      : ((State.initialize (Work.fromExecution work)).runNormalized inputs).1.terminated
        = true)
    (announced
      : ref
        ∈ (State.initialize (Work.fromExecution work)).rootGroups
          ++ ((State.initialize (Work.fromExecution work)).rawBatches inputs).2.flatMap
              rawGroupNoticeRefs)
    : ref
        ∈ ((State.initialize (Work.fromExecution work)).rawBatches
            inputs).1.cancelledGroups
      ∨ ref
        ∈ ((State.initialize (Work.fromExecution work)).rawBatches inputs).2.flatMap
            rawGroupClosureRefs := by
  have tracked := State.rawBatches_groupNoticeTracking
    (State.initialize (Work.fromExecution work)) inputs ref announced
  have empty := (createWorkQueue_replayBatches_terminalRoots ended).1
  exact tracked.resolve_left (by rw [State.rawBatches_state, empty]; simp)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
