import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SourceOutputBlocks

/-! Aggregate report provenance across actual FIFO blocks and retained host batches. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Every report is explained by distinct actual source rejections retained in this run.
This is source provenance, not notification-prefix availability: a host batch can expose a
rejection before its FIFO callback, and a queued report can precede that callback. Exact
reporting cuts are established separately from this complete source inventory. -/
def SourceBlocksHaveFailureTotals (work : Execution.Work) (before : List GraphEvent)
    (blocks : List SourceOutputBlock)
    : Prop :=
  ∀ group errors,
    WorkQueueEvent.groupFailure group errors ∈ blocks.flatMap Prod.snd
    → GroupFailureSources work (before ++ blocks.filterMap Prod.fst) group.ref errors

/-- Consecutive block lists retain exact provenance without asserting callback consumption. -/
theorem SourceBlocksHaveFailureTotals.append {work before left right}
    (first : SourceBlocksHaveFailureTotals work before left)
    (last : SourceBlocksHaveFailureTotals work (before ++ left.filterMap Prod.fst) right)
    : SourceBlocksHaveFailureTotals work before (left ++ right) := by
  intro group errors emitted
  rw [List.flatMap_append] at emitted
  simp only [List.filterMap_append]
  rcases List.mem_append.mp emitted with earlier | later
  · exact (first group errors earlier).weaken (by
      intro event member
      rw [← List.append_assoc]
      exact List.mem_append_left _ member)
  · simpa only [List.append_assoc] using last group errors later

/-- A report's exact causes belong to the retained source inventory of the whole trace.
Their availability at the report is not inferred from its consumed notification prefix. -/
theorem SourceBlocksHaveFailureTotals.atBlock {work initial before block after}
    (totals : SourceBlocksHaveFailureTotals work initial (before ++ block :: after))
    {group errors}
    (emitted : WorkQueueEvent.groupFailure group errors ∈ block.2)
    : GroupFailureSources work
        (initial ++ (before ++ block :: after).filterMap Prod.fst) group.ref errors :=
  totals group errors
    (List.mem_flatMap.mpr ⟨block, List.mem_append_right _ List.mem_cons_self, emitted⟩)

/-- Atomic normalization copies group failures and their exact counts. -/
theorem IncrementalPublisher.normalizeBatch_atomicGroupFailure_mem
    (publisher : IncrementalPublisher) (events : List WorkQueueEvent) {group errors}
    : WorkQueueEvent.groupFailure group errors
        ∈ (publisher.normalizeBatch events).2.flatMap publicationAtoms
      ↔ WorkQueueEvent.groupFailure group errors ∈ events := by
  rw [List.mem_flatMap]
  simp only [publicationAtoms_groupFailure_mem, exists_eq_right]
  exact publisher.normalizeBatch_groupFailure_mem events

/-- An open batch retains every FIFO label, including handlers with empty output. -/
theorem State.sourceBatchBlocks_inputs_of_open (queue : State)
    (publisher : IncrementalPublisher) (events : List GraphEvent)
    (running : queue.terminated = false)
    : (queue.sourceBatchBlocks publisher events).2.2.filterMap Prod.fst = events := by
  simp only [State.sourceBatchBlocks, running, Bool.false_eq_true, ↓reduceIte]
  split <;> simp [State.sourceOutputBlocks_inputs]

/-- A terminated runner ignores later source batches in the annotated view too. -/
theorem State.sourceRunBlocks_of_terminated (queue : State)
    (publisher : IncrementalPublisher) (batches : List (List GraphEvent))
    (finished : queue.terminated = true)
    : queue.sourceRunBlocks publisher batches = (queue, publisher, []) := by
  induction batches with
  | nil => rfl
  | cons batch rest ih =>
      simp [State.sourceRunBlocks, State.sourceBatchBlocks, finished, ih]

/-- Actual batch blocks preserve queued causes and emitted aggregate provenance.
The entire supplied batch licenses cache exposure before individual callback consumption. -/
theorem State.FailureSourceFrame.sourceBatchBlocks_totals {queue : State} {work before}
    (frame : queue.FailureSourceFrame work before)
    (queued : queue.QueuedFailureSources work before) (publisher : IncrementalPublisher)
    (events : List GraphEvent) (valid : ValidGraphEvents work (before ++ events))
    (running : queue.terminated = false)
    : (queue.sourceBatchBlocks publisher events).1.FailureSourceFrame work
        (before ++ events)
      ∧ (queue.sourceBatchBlocks publisher events).1.QueuedFailureSources work
          (before ++ events)
      ∧ SourceBlocksHaveFailureTotals work before
          (queue.sourceBatchBlocks publisher events).2.2 := by
  have extended : queue.FailureSourceFrame work (before ++ events) :=
    ⟨frame.rejections.mono (fun _ _ member => List.mem_append_left events member),
      frame.unique, frame.sound, frame.matching, frame.started⟩
  have waiting := queued.weaken (List.subset_append_left before events)
  have sources := extended.handleGraphEvents_sources waiting events
    (List.subset_append_right _ _) (fun _ member => valid.eachMatches member)
  refine ⟨?_, ?_, ?_⟩
  · rw [(queue.sourceBatchBlocks_agrees publisher events).1]
    exact extended.handleGraphEvents events (List.subset_append_right _ _)
      (fun _ member => valid.eachMatches member)
  · rw [(queue.sourceBatchBlocks_agrees publisher events).1]
    exact sources.1
  · intro group errors emitted
    rw [queue.sourceBatchBlocks_inputs_of_open publisher events running]
    rw [(queue.sourceBatchBlocks_agrees publisher events).2.2] at emitted
    exact sources.2 group errors
      ((publisher.normalizeBatch_atomicGroupFailure_mem _).mp emitted)

/-- Multi-batch provenance follows actual cache snapshots and pending FIFO state. -/
theorem State.FailureSourceFrame.sourceRunBlocks_totals {queue : State} {work before}
    (frame : queue.FailureSourceFrame work before)
    (queued : queue.QueuedFailureSources work before) (publisher : IncrementalPublisher)
    (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work (before ++ batches.flatten))
    : SourceBlocksHaveFailureTotals work before
        (queue.sourceRunBlocks publisher batches).2.2 := by
  induction batches generalizing queue publisher before with
  | nil => intro group errors emitted; cases emitted
  | cons batch rest ih =>
      cases running : queue.terminated with
      | true =>
          rw [queue.sourceRunBlocks_of_terminated publisher _ running]
          intro group errors emitted
          cases emitted
      | false =>
          have firstValid : ValidGraphEvents work (before ++ batch) :=
            valid.prefix ⟨rest.flatten, by simp [List.append_assoc]⟩
          obtain ⟨next, waiting, certified⟩ := frame.sourceBatchBlocks_totals queued publisher
            batch firstValid running
          have tailTotals := ih next waiting (queue.sourceBatchBlocks publisher batch).2.1
            (by simpa only [List.flatten_cons, List.append_assoc] using valid)
          apply certified.append
          rw [queue.sourceBatchBlocks_inputs_of_open publisher batch running]
          exact tailTotals

/-- Every actual group report has exact distinct causes from retained source rejections.
Reporting availability and licensed causal cuts remain separate proof obligations. -/
theorem createWorkQueue_sourceRunBlocks_groupFailureTotals {work : Execution.Work}
    (_generated : ExecutedWork work) {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten)
    : let queue := State.initialize (Work.fromExecution work)
      let publisher : IncrementalPublisher :=
        { active := queue.initialGroups ++ queue.initialStreams }
      SourceBlocksHaveFailureTotals work []
        (queue.sourceRunBlocks publisher batches).2.2 := by
  have initial : (State.initialize (Work.fromExecution work)).FailureSourceFrame work [] :=
    ⟨createWorkQueue_taskRejections _ _, createWorkQueue_taskMembershipsUnique _,
      createWorkQueue_groupMembershipSound _, createWorkQueue_fromSpec_registeredTasksMatch work,
      createWorkQueue_startedTasksRegistered _⟩
  have queued : (State.initialize (Work.fromExecution work)).QueuedFailureSources work [] := by
    intro failure member
    rw [State.initialize_groupFailureEvents] at member
    cases member
  exact initial.sourceRunBlocks_totals queued _ batches valid

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
