import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialStartupReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SourceOutputBlocks

/-! Source-output traces share the ordinary publisher runner with pending-startup queues. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue

/-- The exact trace agrees with the actual publisher runner from any queue state.
Startup controls are represented by that queue's pending FIFO and their supplied dispatch
entries; no separately forwarded failure tail is needed. -/
theorem State.sourceRunBlocks_withPublisher_agrees (queue : State)
    (publisher : IncrementalPublisher) (batches : List (List GraphEvent))
    : let traced := queue.sourceRunBlocks publisher batches
      let actual := queue.runWithPublisher publisher batches
      traced.1 = actual.1
      ∧ traced.2.1 = actual.2.1
      ∧ traced.2.2.flatMap Prod.snd = actual.2.2.flatten.flatMap publicationAtoms := by
  have runner : queue.runWithPublisher publisher batches
      = batches.foldl normalizedStep (queue, publisher, []) := rfl
  rw [runner]
  exact queue.sourceRunBlocks_fold publisher batches []

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
