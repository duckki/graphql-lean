import GraphQL.IncrementalDelivery.WorkQueueImplementation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.GroupValueMetadata

namespace GraphQL.IncrementalDelivery.Tests.GroupValueConsolidation
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.WorkQueueSemantics
open GraphQL.IncrementalDelivery.ReferenceWorkQueue

/-- Raw and normalized outputs share their representation, not their owner semantics. -/
example (publisher : IncrementalPublisher) (event : WorkQueueEvent)
    : IncrementalPublisher × List WorkQueueEvent :=
  publisher.handleWorkQueueEvent event

/-- Queue task and item results retain the canonical execution payload types. -/
example (result : TaskResult) : ExecutionGroupValue := result.value

example (item : StreamItem) : StreamItemValue := item.value

def parent : DeliveryNode := { ref := 0, path := [] }
def child : DeliveryNode := { ref := 1, path := [.field "obj"] }

def value : ExecutionGroupValue :=
  { path := child.path, data := [("x", .scalar "X")], deliveryGroups := [parent, child] }

/-- Singleton group atoms can coalesce into one multi-value observable event. -/
example (first second : ExecutionGroupValue)
    : WorkBatching [.groupValues child [first], .groupValues child [second]]
        [[.groupValues child [first, second]]] :=
  .cons (by simp) (.combine _ (.separate _ .nil) rfl) .nil

/-- Stream atoms can likewise coalesce, retaining item order within one event. -/
example (first second : StreamItemValue)
    : WorkBatching [.streamValues child [first] [] [], .streamValues child [second] [] []]
        [[.streamValues child [first, second] [] []]] :=
  .cons (by simp) (.combine _ (.separate _ .nil) rfl) .nil

/-- The deepest active contributor becomes the owner without copying or erasing values. -/
example
    : (IncrementalPublisher.handleWorkQueueEvent { active := [parent, child] }
        (.groupValues parent [value])).2
      = [.groupValues child [value]] :=
  rfl

/-- One raw event can select different owners; each retained value keeps its metadata. -/
example
    : (IncrementalPublisher.handleWorkQueueEvent { active := [parent, child] }
        (.groupValues parent [value, { value with deliveryGroups := [parent] }])).2
      = [
        .groupValues child [value],
        .groupValues parent [{ value with deliveryGroups := [parent] }]
      ] :=
  rfl

/-- Removing metadata after normalization changes neither wire output nor ID allocation. -/
example (ids : IDState)
    : (mapWorkEventBatch [.groupValues child [value]]).run ids
      = (mapWorkEventBatch [.groupValues child [{ value with deliveryGroups := [] }]]).run
          ids :=
  rfl

/-- Abstract admission does not trust even a fabricated contributor annotation. -/
example (work initial matching before failures owner)
    : EventAllowed work initial matching before failures
        (.groupValues owner
          [{ value with deliveryGroups := [{ ref := 999, path := [] }] }])
      ↔ EventAllowed work initial matching before failures (.groupValues owner [value]) :=
  eventAllowed_groupValues_metadata _ _ _ _ _ _ _ _

def work : Execution.Work :=
  .executionGroup [{ node := parent }, { node := child }] value.path
    (.ok (value.data, value.errors)) .empty

/-- The reference source still rejects an incorrect contributor list before normalization.
Witness: its exact taskGroups lookup disagrees, regardless of the response payload.
-/
example
    : ¬GraphEvent.MatchesWork work
        (.taskSuccess (.executionGroup [])
          { value := { value with deliveryGroups := [] } }) := by
  simp [GraphEvent.MatchesWork, taskGroups?, locateWork, locateWork.go, work]

end GraphQL.IncrementalDelivery.Tests.GroupValueConsolidation
