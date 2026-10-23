import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.BufferedCallbackDefinitions

/-! Finite FIFO enqueue/reduction histories, including notifications held across batches.
This proof inventory records the host history without adding runtime callback storage. -/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.BufferedCallbacks

/-- Proof-only observations of one host run. `received` retains consumed and pending
callbacks; none of these histories or ghost receipt identities are production storage.
-/
structure CallbackBuffer where
  queue : ReferenceWorkQueue.State
  batches : List (List BufferedCallback) := []
  pending : List BufferedCallback := []
  received : List BufferedCallback := []

def CallbackBuffer.rawBatches (buffer : CallbackBuffer) : List (List GraphEvent) :=
  buffer.batches.map (List.map BufferedCallback.event)

def CallbackBuffer.enqueue (buffer : CallbackBuffer) (callback : BufferedCallback)
    : CallbackBuffer :=
  {
    buffer with
      pending := buffer.pending ++ [callback], received := buffer.received ++ [callback]
  }

def CallbackBuffer.reduce (buffer : CallbackBuffer) (front rest : List BufferedCallback)
    : CallbackBuffer :=
  {
    buffer with
      queue := (buffer.queue.handleGraphEvents (front.map BufferedCallback.event)).1,
      batches := buffer.batches ++ [front],
      pending := rest
  }

/-- Enqueue checks current permission and fixed original source laws, including all
earlier pending callbacks. Reduction takes a FIFO prefix and rechecks ownership through
the actual reducer. A callback may remain pending while its task is retired.
-/
inductive CallbackHistory (work : Work) (initial : ReferenceWorkQueue.State)
    : CallbackBuffer → Prop where
  | initial : CallbackHistory work initial { queue := initial }
  | enqueue {buffer} (history : CallbackHistory work initial buffer)
    (callback : BufferedCallback) (running : buffer.queue.terminated = false)
    (started : buffer.queue.acceptsGraphEvent callback.event = true)
    (receiptFresh : callback.receipt ∉ buffer.received.map BufferedCallback.receipt)
    (matching : callback.event.MatchesWork work)
    (fresh
      : callback.event.Fresh
          (buffer.rawBatches.flatten ++ buffer.pending.map BufferedCallback.event))
    (ready
      : callback.event.Ready work
          (buffer.rawBatches.flatten ++ buffer.pending.map BufferedCallback.event))
    : CallbackHistory work initial (buffer.enqueue callback)
  | reduce {buffer} (history : CallbackHistory work initial buffer)
    (front rest : List BufferedCallback) (fifo : buffer.pending = front ++ rest)
    : CallbackHistory work initial (buffer.reduce front rest)

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.BufferedCallbacks
