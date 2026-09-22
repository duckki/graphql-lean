import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TerminationShape
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ConformancePlan

/-! Exact nonterminal history and the checked conformance batching leaf. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Source blocks have exactly one optional terminal suffix
-----------------------------------------------------------------------------------------

/-- Annotated handler replay preserves the flag and contains no terminal atom.
Witness: exact raw replay agreement, handler exclusion, and publisher/atom reflection.
-/
theorem State.sourceOutputBlocks_terminalShape (queue : State)
    (publisher : IncrementalPublisher) (events : List GraphEvent)
    : (queue.sourceOutputBlocks publisher events).1.terminated = queue.terminated
      ∧ Execution.WorkQueueEvent.workQueueTermination
        ∉ (queue.sourceOutputBlocks publisher events).2.2.flatMap Prod.snd := by
  obtain ⟨state, _, output⟩ := queue.sourceOutputBlocks_agrees publisher events
  rw [state, output, State.rawEventReplay_terminated,
    publicationAtoms_list_termination_mem, IncrementalPublisher.normalizeBatch_termination_mem]
  exact ⟨rfl, queue.rawEventReplay_noTermination events⟩

/-- A terminated queue contributes no later source blocks and leaves both machines alone.
Witness: each batch takes the absorbing branch before processing any host input.
-/
theorem State.sourceRunBlocks_after_termination (queue : State)
    (publisher : IncrementalPublisher) (batches : List (List GraphEvent))
    (ended : queue.terminated = true)
    : queue.sourceRunBlocks publisher batches = (queue, publisher, []) := by
  induction batches with
  | nil => rfl
  | cons batch rest ih =>
      simpa only [State.sourceRunBlocks, State.sourceBatchBlocks, ended, ↓reduceIte,
        List.nil_append] using ih

/-- One open batch appends its only possible terminal marker after all handler atoms.
Witness: handlers retain false and emit no marker; the empty-root test determines both
the flag and the optional final atom.
-/
theorem State.sourceBatchBlocks_terminalShape (queue : State)
    (publisher : IncrementalPublisher) (events : List GraphEvent)
    (running : queue.terminated = false)
    : ∃ before : List Execution.WorkQueueEvent,
        Execution.WorkQueueEvent.workQueueTermination ∉ before
        ∧ (queue.sourceBatchBlocks publisher events).2.2.flatMap Prod.snd
          = before
            ++ if (queue.sourceBatchBlocks publisher events).1.terminated then
                  [.workQueueTermination]
                else
                  [] := by
  obtain ⟨flag, absent⟩ := queue.sourceOutputBlocks_terminalShape publisher events
  refine ⟨(queue.sourceOutputBlocks publisher events).2.2.flatMap Prod.snd, absent, ?_⟩
  simp only [State.sourceBatchBlocks, running, Bool.false_eq_true, ↓reduceIte]
  split
  · simp
  · simp [flag, running]

/-- Actual multi-batch atoms end in one terminal marker exactly when the flag is true.
Witness: concatenate nonterminal handler blocks until the first ending batch, after which
the absorbing branch contributes no further atoms. No input-validity premise is needed.
-/
theorem State.sourceRunBlocks_terminalShape (queue : State)
    (publisher : IncrementalPublisher) (batches : List (List GraphEvent))
    (running : queue.terminated = false)
    : ∃ before : List Execution.WorkQueueEvent,
        Execution.WorkQueueEvent.workQueueTermination ∉ before
        ∧ (queue.sourceRunBlocks publisher batches).2.2.flatMap Prod.snd
          = before
            ++ if (queue.sourceRunBlocks publisher batches).1.terminated then
                  [.workQueueTermination]
                else
                  [] := by
  induction batches generalizing queue publisher with
  | nil => exact ⟨[], by simp, by simp [State.sourceRunBlocks, running]⟩
  | cons batch rest ih =>
      obtain ⟨first, noFirst, firstShape⟩ :=
        queue.sourceBatchBlocks_terminalShape publisher batch running
      let next := queue.sourceBatchBlocks publisher batch
      change next.2.2.flatMap Prod.snd = first ++
        (if next.1.terminated then [.workQueueTermination] else []) at firstShape
      cases ended : next.1.terminated with
      | true =>
          have later := next.1.sourceRunBlocks_after_termination next.2.1 rest ended
          refine ⟨first, noFirst, ?_⟩
          change (next.2.2 ++ (next.1.sourceRunBlocks next.2.1 rest).2.2).flatMap Prod.snd
            = first ++ if (next.1.sourceRunBlocks next.2.1 rest).1.terminated then
                [.workQueueTermination] else []
          rw [later]
          simpa only [List.append_nil] using firstShape
      | false =>
          obtain ⟨last, noLast, lastShape⟩ := ih next.1 next.2.1 ended
          refine ⟨first ++ last, ?_, ?_⟩
          · simpa only [List.mem_append, not_or] using And.intro noFirst noLast
          · change (next.2.2 ++ (next.1.sourceRunBlocks next.2.1 rest).2.2).flatMap Prod.snd
              = (first ++ last) ++
                if (next.1.sourceRunBlocks next.2.1 rest).1.terminated then
                  [.workQueueTermination] else []
            have firstEq : next.2.2.flatMap Prod.snd = first := by
              simpa only [ended, Bool.false_eq_true, ↓reduceIte, List.append_nil]
                using firstShape
            rw [List.flatMap_append, firstEq, lastShape, List.append_assoc]

-----------------------------------------------------------------------------------------
-- One canonical nonterminal history for the shared conformance witness
-----------------------------------------------------------------------------------------

/-- The actual atomic history with the terminal constructor filtered out.
The shape theorem below proves that this removes only the optional final marker, not
arbitrary outputs. It is a proof projection, not an admission filter or runtime behavior.
-/
def State.nonterminalAtoms (queue : State) (inputs : List (List GraphEvent))
    : List Execution.WorkQueueEvent :=
  (queue.runNormalized inputs).2.flatten.flatMap publicationAtoms
  |>.filter
      (fun
        | .workQueueTermination => false
        | _ => true)

/-- The canonical nonterminal history contains no termination atom.
Witness: the filter excludes exactly that constructor.
-/
theorem State.nonterminalAtoms_noTermination (queue : State)
    (inputs : List (List GraphEvent))
    : Execution.WorkQueueEvent.workQueueTermination ∉ queue.nonterminalAtoms inputs := by
  simp [State.nonterminalAtoms]

/-- The actual atomic history is its nonterminal projection plus its final marker.
Witness: source-block agreement and the proved unique terminal suffix; no actual value,
notice, error, or completion is discarded by the projection.
-/
theorem State.runNormalized_terminalShape (queue : State)
    (inputs : List (List GraphEvent)) (running : queue.terminated = false)
    : (queue.runNormalized inputs).2.flatten.flatMap publicationAtoms
      = queue.nonterminalAtoms inputs
        ++ if (queue.runNormalized inputs).1.terminated then
              [.workQueueTermination]
            else
              [] := by
  let publisher : IncrementalPublisher :=
    { active := queue.initialGroups ++ queue.initialStreams }
  obtain ⟨before, absent, shape⟩ :=
    queue.sourceRunBlocks_terminalShape publisher inputs running
  obtain ⟨state, output⟩ := queue.sourceRunBlocks_agrees inputs
  change (queue.sourceRunBlocks publisher inputs).1 = _ at state
  change (queue.sourceRunBlocks publisher inputs).2.2.flatMap Prod.snd = _ at output
  rw [state, output] at shape
  have retained : before.filter (fun | .workQueueTermination => false | _ => true) = before := by
    apply List.filter_eq_self.mpr
    intro event member
    cases event <;> try rfl
    exact False.elim (absent member)
  unfold State.nonterminalAtoms
  rw [shape, List.filter_append, retained]
  cases (queue.runNormalized inputs).1.terminated <;> simp

/-- A real replay contains a terminal marker exactly when its final queue has terminated.
Witness: the exact terminal-suffix equation and exclusion from the nonterminal projection.
This is concrete output shape, not yet abstract terminal work accounting.
-/
theorem State.runNormalized_termination_mem (queue : State)
    (inputs : List (List GraphEvent)) (running : queue.terminated = false)
    : Execution.WorkQueueEvent.workQueueTermination
        ∈ (queue.runNormalized inputs).2.flatten
      ↔ (queue.runNormalized inputs).1.terminated = true := by
  rw [← publicationAtoms_list_termination_mem, queue.runNormalized_terminalShape inputs running]
  simp only [List.mem_append, queue.nonterminalAtoms_noTermination inputs, false_or]
  cases (queue.runNormalized inputs).1.terminated <;> simp

namespace ConformancePlan

/-- The batching leaf holds for the canonical actual history, with any matching and cuts.
Witness: exact atomic batching plus the terminal-suffix theorem. Only the existing valid
input premise is used, to exclude empty value events; no output admission is assumed.
-/
theorem batchShape_holds {work : Execution.Work} {inputs : List (List GraphEvent)}
    (valid : ValidGraphEvents work inputs.flatten)
    (matching : PublicationMatching) (failures : FailureCuts)
    : BatchShape work inputs
        {
          events := (initialQueue work).nonterminalAtoms inputs, matching, failures
        } := by
  have grouped := createWorkQueue_runNormalized_atomicBatching valid
  dsimp only at grouped
  rw [State.runNormalized_terminalShape _ inputs
    (createWorkQueue_terminated (Work.fromExecution work))] at grouped
  exact grouped

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
