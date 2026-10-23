import GraphQL.IncrementalDelivery.WorkQueueImplementation

/-! Object publication labels and raw payload projections used by implementation proofs. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (ExecutionGroupValue WorkQueueEvent)
open WorkQueueSemantics (Occurrence)

/-- A published object payload paired with its original execution-group occurrence.
The occurrence is proof evidence, not an added field in the implementation or wire format.
-/
abbrev ObjectPublication := Occurrence × ExecutionGroupValue

/-- Object values in one raw queue event; stream payloads and control events are excluded.
-/
abbrev _root_.GraphQL.IncrementalDelivery.Execution.WorkQueueEvent.objectValues
  : WorkQueueEvent → List ExecutionGroupValue
  | .groupValues _ values => values
  | _ => []

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
