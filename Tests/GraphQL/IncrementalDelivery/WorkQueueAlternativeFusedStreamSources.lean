import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedStreamSources

/-! Generated receipt source safety uses actual FIFO preparation, drain and effects. -/

namespace AlternativeFusedStreamSourceChecks
open GraphQL.IncrementalDelivery
open AlternativeWorkQueue
open AlternativeWorkQueue.NativeRefinement

example : GeneratedStreamReceiptResourceSafety :=
  GeneratedStreamReceiptResourceSafety_holds

private def group : Execution.DeliveryNode := { ref := 0, path := [] }
private def carrier : Execution.DeliveryNode := { ref := 9, path := [] }
private def source : Execution.DeliveryNode := { ref := 7, path := [] }
private def producer : WorkQueueSemantics.Occurrence := .executionGroup [0]

private def readyFailure : State :=
  {
    queue :=
      {
        rootGroups := [0]
        rootStreams := [9]
        groupNodes := [{ group := ⟨group, none⟩, tasks := [producer], failure := some 1 }]
        tasks := [{ occurrence := producer, groups := [group] }]
        taskNodes :=
          [{
            task := { occurrence := producer, groups := [group] }
            value := some { deliveryGroups := [group], path := [], data := [] }
            childStreams := [7]
          }]
        streams := [⟨source⟩, ⟨carrier⟩]
      }
  }

-- Receipt consumption ends before its ready-drain cleanup, including a zero-item receipt.
example
    : (readyFailure.streamItems carrier []).2.2
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
