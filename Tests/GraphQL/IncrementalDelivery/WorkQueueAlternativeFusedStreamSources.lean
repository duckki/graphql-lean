import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedStreamSources
import Tests.GraphQL.IncrementalDelivery.Fixtures.SourceDrainCleanup

/-! Generated receipt source safety uses actual FIFO preparation, drain and effects. -/

namespace AlternativeFusedStreamSourceChecks
open GraphQL.IncrementalDelivery
open AlternativeWorkQueue
open AlternativeWorkQueue.NativeRefinement

example : GeneratedStreamReceiptResourceSafety :=
  GeneratedStreamReceiptResourceSafety_holds

open GraphQL.IncrementalDelivery.Tests.SourceDrainCleanup

-- Receipt consumption ends before its ready-drain cleanup, including a zero-item receipt.
example
    : (readyFailure.streamItems carrier []).2.2.1
      = [.acknowledge 9, .abortTask producer, .cancelSource 7, .abortStreamQueue 7] := by
  cbv

example : (readyFailure.streamItems carrier []).1.queue.taskNode? producer = none := by
  cbv

example : (readyFailure.streamItems carrier []).1.queue.rootStreams = [9] := by cbv

private def lease : ResourceState :=
  fun target => if target = .stream 7 then .owned .queue else .unacquired

example
    : (lease.observeHandlerCleanup readyFailure (.streamItems carrier [])).1 (.stream 7)
      = .cleanupRequested .queue := by cbv

example
    : (lease.observeHandlerCleanup readyFailure (.streamItems carrier [])).2
      = [.requestCleanup (.stream 7)] := by cbv

#print axioms referencePrefix_streamItems_sources
#print axioms GeneratedStreamReceiptResourceSafety_holds
#print axioms State.streamItems_cleanupStarts_eq

end AlternativeFusedStreamSourceChecks
