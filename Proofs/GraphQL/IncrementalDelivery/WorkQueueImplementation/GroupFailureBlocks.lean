import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SourceOutputBlocks

/-! Failed group closures retain exact totals from their actual source-handler prefix. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Each block's failed-group totals use only `before` and labels through that block.
Earlier silent handlers count; later handlers do not. This proof annotation allows a
successful handler to release several cached failures without inventing a current failure.
-/
def SourceBlocksHaveFailureTotals (work : Execution.Work)
    : List GraphEvent → List SourceOutputBlock → Prop
  | _, [] => True
  | before, block :: rest =>
      (∀ group errors,
        Execution.WorkQueueEvent.groupFailure group errors ∈ block.2
        → GroupFailureTotal work (before ++ block.1.toList) group.key errors)
      ∧ SourceBlocksHaveFailureTotals work (before ++ block.1.toList) rest

/-- Consecutive certified block lists retain the exact intervening source prefix.
Witness: recursion over the first list and concatenation of its optional source labels.
-/
theorem SourceBlocksHaveFailureTotals.append {work before left right}
    (first : SourceBlocksHaveFailureTotals work before left)
    (last : SourceBlocksHaveFailureTotals work (before ++ left.filterMap Prod.fst) right)
    : SourceBlocksHaveFailureTotals work before (left ++ right) := by
  induction left generalizing before with
  | nil => simpa using last
  | cons block rest ih =>
      refine ⟨first.1, ih first.2 ?_⟩
      cases source : block.1 <;>
        simpa [List.filterMap_cons, source, List.append_assoc] using last

/-- A selected block's totals use precisely its preceding labels and its own optional input.
Witness: peel off earlier blocks, preserving their order even when they emit no output.
-/
theorem SourceBlocksHaveFailureTotals.atBlock {work initial before block after}
    (totals : SourceBlocksHaveFailureTotals work initial (before ++ block :: after))
    {group errors}
    (emitted : Execution.WorkQueueEvent.groupFailure group errors ∈ block.2)
    : GroupFailureTotal work
        (initial ++ before.filterMap Prod.fst ++ block.1.toList) group.key errors := by
  induction before generalizing initial with
  | nil => simpa using totals.1 group errors emitted
  | cons head rest ih =>
      have result := ih totals.2
      cases source : head.1 <;>
        simpa [List.filterMap_cons, source, List.append_assoc] using result

-----------------------------------------------------------------------------------------
-- Each handler preserves totals and records their source boundary
-----------------------------------------------------------------------------------------

/-- Atomic normalized failure membership is exactly raw failure membership in the batch.
Witness: publisher failure copying and the control-preserving atomic expansion.
-/
theorem IncrementalPublisher.normalizeBatch_atomicGroupFailure_mem
    (publisher : IncrementalPublisher) (events : List WorkQueueEvent) {group errors}
    : Execution.WorkQueueEvent.groupFailure group errors
        ∈ (publisher.normalizeBatch events).2.flatMap publicationAtoms
      ↔ Execution.WorkQueueEvent.groupFailure group errors ∈ events := by
  rw [List.mem_flatMap]
  simp only [publicationAtoms_groupFailure_mem, exists_eq_right]
  exact publisher.normalizeBatch_groupFailure_mem events

/-- Handler annotation preserves cached totals and certifies each exact source prefix.
Witness: joint cache/registration induction and publisher copying. Delayed completions
may draw on earlier failures but never on a later handler, even in the same host batch.
-/
theorem State.CachedErrorsSatisfy.sourceOutputBlocks_totals {queue : State} {work before}
    (totals : queue.CachedErrorsSatisfy (GroupFailureTotal work before))
    (generated : ExecutedWork work) (registered : queue.StartedTasksRegistered)
    (tasks : queue.RegisteredTasksMatch work) (publisher : IncrementalPublisher)
    (events : List GraphEvent) (valid : ValidGraphEvents work (before ++ events))
    : (queue.sourceOutputBlocks publisher events).1.CachedErrorsSatisfy
        (GroupFailureTotal work (before ++ events))
      ∧ SourceBlocksHaveFailureTotals work before
          (queue.sourceOutputBlocks publisher events).2.2 := by
  induction events generalizing queue publisher before with
  | nil => exact ⟨by simpa [State.sourceOutputBlocks] using totals, trivial⟩
  | cons event rest ih =>
      have initialPart : (before ++ [event]).IsPrefix (before ++ event :: rest) :=
        ⟨rest, by simp [List.append_assoc]⟩
      have localLaws := valid.atPrefix initialPart
      have next := totals.handleGraphEvent_totals generated registered tasks event
        localLaws.1 localLaws.2.1
      obtain ⟨cached, certified⟩ := ih next (registered.handleGraphEvent event)
        (tasks.handleGraphEvent event localLaws.1)
        (publisher.normalizeBatch (queue.handleGraphEvent event).2).1
        (by simpa [List.append_assoc] using valid)
      refine ⟨by simpa [State.sourceOutputBlocks, List.append_assoc] using cached, ?_⟩
      refine ⟨?_, certified⟩
      intro group errors emitted
      exact totals.handleGraphEvent_outputTotal registered tasks event localLaws.1
        ((publisher.normalizeBatch_atomicGroupFailure_mem _).mp emitted)

-----------------------------------------------------------------------------------------
-- Termination adds no source identity and ignored batches supply no contributors
-----------------------------------------------------------------------------------------

/-- An open batch retains every source label, including handlers with empty output.
Witness: the optional termination marker carries no label and changes no handler input.
-/
theorem State.sourceBatchBlocks_inputs_of_open (queue : State)
    (publisher : IncrementalPublisher) (events : List GraphEvent)
    (running : queue.terminated = false)
    : (queue.sourceBatchBlocks publisher events).2.2.filterMap Prod.fst = events := by
  simp only [State.sourceBatchBlocks, running, Bool.false_eq_true, ↓reduceIte]
  split <;> simp [State.sourceOutputBlocks_inputs]

/-- A terminated runner ignores all later source batches in the annotated view too.
Witness: induction over batch wrapping, which never invokes a handler after termination.
-/
theorem State.sourceRunBlocks_of_terminated (queue : State)
    (publisher : IncrementalPublisher) (batches : List (List GraphEvent))
    (finished : queue.terminated = true)
    : queue.sourceRunBlocks publisher batches = (queue, publisher, []) := by
  induction batches with
  | nil => rfl
  | cons batch rest ih =>
      simp [State.sourceRunBlocks, State.sourceBatchBlocks, finished, ih]

/-- An open batch preserves exact prefix totals through its optional terminal block.
Witness: handler totals and the absence of group failures in the unlabelled terminal block.
-/
theorem State.CachedErrorsSatisfy.sourceBatchBlocks_totals {queue : State} {work before}
    (totals : queue.CachedErrorsSatisfy (GroupFailureTotal work before))
    (generated : ExecutedWork work) (registered : queue.StartedTasksRegistered)
    (tasks : queue.RegisteredTasksMatch work) (publisher : IncrementalPublisher)
    (events : List GraphEvent) (valid : ValidGraphEvents work (before ++ events))
    (running : queue.terminated = false)
    : (queue.sourceBatchBlocks publisher events).1.CachedErrorsSatisfy
        (GroupFailureTotal work (before ++ events))
      ∧ SourceBlocksHaveFailureTotals work before
          (queue.sourceBatchBlocks publisher events).2.2 := by
  obtain ⟨cached, certified⟩ := totals.sourceOutputBlocks_totals generated registered tasks
    publisher events valid
  simp only [State.sourceBatchBlocks, running, Bool.false_eq_true, ↓reduceIte]
  split
  · exact ⟨cached, certified.append (by simp [SourceBlocksHaveFailureTotals])⟩
  · exact ⟨cached, certified⟩

/-- Actual multi-batch annotations certify totals against retained source prefixes only.
Witness: open batches retain every input; terminated tails are empty. Registry and cache
preservation follow the same queue state as the executable batch runner.
-/
theorem State.CachedErrorsSatisfy.sourceRunBlocks_totals {queue : State} {work before}
    (totals : queue.CachedErrorsSatisfy (GroupFailureTotal work before))
    (generated : ExecutedWork work) (registered : queue.StartedTasksRegistered)
    (tasks : queue.RegisteredTasksMatch work) (publisher : IncrementalPublisher)
    (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work (before ++ batches.flatten))
    : SourceBlocksHaveFailureTotals work before
        (queue.sourceRunBlocks publisher batches).2.2 := by
  induction batches generalizing queue publisher before with
  | nil => trivial
  | cons batch rest ih =>
      cases running : queue.terminated with
      | true => rw [queue.sourceRunBlocks_of_terminated publisher _ running]; trivial
      | false =>
          have firstValid : ValidGraphEvents work (before ++ batch) :=
            valid.prefix ⟨rest.flatten, by simp [List.append_assoc]⟩
          have batchMatch : ∀ event ∈ batch, event.MatchesWork work := fun event member =>
            firstValid.eachMatches (List.mem_append_right before member)
          obtain ⟨cached, certified⟩ := totals.sourceBatchBlocks_totals generated registered
            tasks publisher batch firstValid running
          have agreement := (queue.sourceBatchBlocks_agrees publisher batch).1
          have nextRegistered := registered.handleGraphEvents batch
          have nextTasks := tasks.handleGraphEvents batch batchMatch
          rw [← agreement] at nextRegistered nextTasks
          have tailTotals := ih cached nextRegistered nextTasks
            (queue.sourceBatchBlocks publisher batch).2.1
            (by simpa [List.append_assoc] using valid)
          apply certified.append
          rw [queue.sourceBatchBlocks_inputs_of_open publisher batch running]
          exact tailTotals

/-- Actual normalized output blocks have exact distinct-source totals at their boundaries.
Witness: initially empty caches, generated task metadata, valid inputs, and prefix replay.
No accepted-start, output-admission, or failure-cut-licensing premise is assumed.
-/
theorem createWorkQueue_sourceRunBlocks_groupFailureTotals {work : Execution.Work}
    (generated : ExecutedWork work) {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten)
    : let queue := State.initialize (Work.fromExecution work)
      let publisher : IncrementalPublisher :=
        { active := queue.initialGroups ++ queue.initialStreams }
      SourceBlocksHaveFailureTotals work []
        (queue.sourceRunBlocks publisher batches).2.2 :=
  State.CachedErrorsSatisfy.sourceRunBlocks_totals (createWorkQueue_cachedErrors _ _)
    generated (createWorkQueue_startedTasksRegistered _)
    (createWorkQueue_fromSpec_registeredTasksMatch work) _ batches valid

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
