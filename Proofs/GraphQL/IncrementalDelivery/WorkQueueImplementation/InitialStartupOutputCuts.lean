import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialStartupOutputBlocks
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.BatchImmediateBoundaries

/-! Startup source cuts use ordinary replay with persistent queued controls. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue

/-- Ordinary source-cut evidence also applies to queues with pending startup controls. -/
theorem State.sourceRunBlocks_startup_append (queue : State)
    (publisher : IncrementalPublisher) (before after : List (List GraphEvent))
    : queue.sourceRunBlocks publisher (before ++ after)
      = let first := queue.sourceRunBlocks publisher before
        let last := first.1.sourceRunBlocks first.2.1 after
        (last.1, last.2.1, first.2.2 ++ last.2.2) :=
  queue.sourceRunBlocks_append publisher before after

/-- Ordinary source-cut evidence also applies to queues with pending startup controls. -/
theorem State.sourceRunBlocks_startup_state (queue : State)
    (publisher : IncrementalPublisher) (batches : List (List GraphEvent))
    : (queue.sourceRunBlocks publisher batches).1 = queue.replayBatches batches :=
  queue.sourceRunBlocks_state publisher batches

/-- Ordinary source-cut evidence also applies to queues with pending startup controls. -/
theorem State.sourceBatchBlocks_startup_inputs (queue : State)
    (publisher : IncrementalPublisher) (events : List GraphEvent)
    (running : queue.terminated = false)
    : (queue.sourceBatchBlocks publisher events).2.2.filterMap Prod.fst = events :=
  queue.sourceBatchBlocks_inputs_of_open publisher events running

/-- Ordinary source-cut evidence also applies to queues with pending startup controls. -/
theorem State.sourceRunBlocks_startup_inputs_of_started {queue : State}
    (publisher : IncrementalPublisher) {batches : List (List GraphEvent)}
    (started : queue.batchesStarted batches = true)
    : ((queue.sourceRunBlocks publisher batches).2.2.filterMap Prod.fst)
      = batches.flatten :=
  State.sourceRunBlocks_inputs_of_started publisher started

/-- Ordinary source-cut evidence also applies to queues with pending startup controls. -/
theorem State.sourceBatchBlocks_startup_labeledPrefix (queue : State)
    (publisher : IncrementalPublisher) (batch : List GraphEvent)
    {index : Nat} {block : SourceOutputBlock} {source : GraphEvent}
    (selected : (queue.sourceBatchBlocks publisher batch).2.2[index]? = some block)
    (labeled : block.1 = some source)
    : let traced :=
        queue.sourceOutputBlocks publisher batch (GraphEvent.availableFailures batch)
      traced.2.2[index]? = some block
      ∧ (queue.sourceBatchBlocks publisher batch).2.2.take index
        = traced.2.2.take index :=
  queue.sourceBatchBlocks_labeledPrefix publisher batch selected labeled

/-- Ordinary source-cut evidence also applies to queues with pending startup controls. -/
theorem State.sourceRunBlocks_startup_blockCut (queue : State)
    (publisher : IncrementalPublisher) (batches : List (List GraphEvent))
    {index : Nat} {block : SourceOutputBlock}
    (selected : (queue.sourceRunBlocks publisher batches).2.2[index]? = some block)
    : ∃ earlier batch later localIndex,
        batches = earlier ++ batch :: later
        ∧ let first := queue.sourceRunBlocks publisher earlier
          let current := first.1.sourceBatchBlocks first.2.1 batch
          current.2.2[localIndex]? = some block
          ∧ (queue.sourceRunBlocks publisher batches).2.2.take index
            = first.2.2 ++ current.2.2.take localIndex :=
  queue.sourceRunBlocks_blockCut publisher batches selected

/-- Ordinary source-cut evidence also applies to queues with pending startup controls. -/
theorem State.sourceRunBlocks_startup_labeledInputCut (queue : State)
    (publisher : IncrementalPublisher) (batches : List (List GraphEvent))
    (started : queue.batchesStarted batches = true)
    {index : Nat} {block : SourceOutputBlock} {source : GraphEvent}
    (selected : (queue.sourceRunBlocks publisher batches).2.2[index]? = some block)
    (labeled : block.1 = some source)
    : ∃ earlier batch later fifo tail,
        batches = earlier ++ batch :: later
        ∧ batch = fifo ++ source :: tail
        ∧ ((queue.sourceRunBlocks publisher batches).2.2.take index).filterMap Prod.fst
          = earlier.flatten ++ fifo :=
  queue.sourceRunBlocks_labeledInputCut publisher batches started selected labeled

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
