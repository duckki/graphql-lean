import GraphQL.IncrementalDelivery.WorkQueueImplementation

/-! Batch-preserving state replay. Each supplied batch has its own cache-availability
snapshot; flattening batches is not an equivalent state or reporting observation.
-/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue

/-- Replay complete host batches, retaining their cache-availability boundaries. -/
def State.replayBatches (queue : State) (batches : List (List GraphEvent)) : State :=
  batches.foldl (fun current batch => (current.handleGraphEvents batch).1) queue

/-- Concatenating histories composes replay while retaining every batch boundary. -/
theorem State.replayBatches_append (queue : State) (before after : List (List GraphEvent))
    : queue.replayBatches (before ++ after)
      = (queue.replayBatches before).replayBatches after := by
  simp only [State.replayBatches, List.foldl_append]

private abbrev BatchAcc :=
  State × IncrementalPublisher × List (List Execution.WorkQueueEvent)

private def batchStep (acc : BatchAcc) (batch : List GraphEvent) : BatchAcc :=
  let (queue, publisher, outputs) := acc
  let (next, raw) := queue.handleGraphEvents batch
  if raw.isEmpty then
    (next, publisher, outputs)
  else
    let (publisher, events) := publisher.normalizeBatch raw
    (next, publisher, outputs ++ [events])

private theorem batchStep_state (acc : BatchAcc) (batch : List GraphEvent)
    : (batchStep acc batch).1 = (acc.1.handleGraphEvents batch).1 := by
  obtain ⟨queue, publisher, outputs⟩ := acc
  simp only [batchStep]
  split <;> rfl

private theorem fold_batchStep_state (batches : List (List GraphEvent)) (acc : BatchAcc)
    : (batches.foldl batchStep acc).1 = acc.1.replayBatches batches := by
  induction batches generalizing acc with
  | nil => rfl
  | cons batch rest ih =>
      simp only [List.foldl_cons, State.replayBatches] at *
      rw [ih, batchStep_state]

/-- Publisher normalization preserves the actual batch-aware queue replay.
This replaces a flatten-only replay boundary; no source or conformance law is assumed.
-/
theorem State.runNormalized_replayBatches (queue : State)
    (batches : List (List GraphEvent))
    : (queue.runNormalized batches).1 = queue.replayBatches batches := by
  let publisher : IncrementalPublisher :=
    { active := queue.initialGroups ++ queue.initialStreams }
  change (batches.foldl batchStep (queue, publisher, [])).1 = _
  exact fold_batchStep_state batches (queue, publisher, [])

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
