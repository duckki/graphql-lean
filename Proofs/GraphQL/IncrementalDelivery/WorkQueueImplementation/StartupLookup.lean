import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupRefs

/-! Lookup provenance through startup removal of existing group records. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- A surviving startup lookup selects the same original record under unique group refs. -/
theorem State.startNewWork_lookup_before {queue : State} (unique : queue.GroupRefsUnique)
    (more : NewWork) (available : List (Occurrence × Nat)) {ref : NodeRef}
    {node : GroupNode}
    (found : (queue.startNewWork more available).1.groupNode? ref = some node)
    : queue.groupNode? ref = some node := by
  have old := (queue.startNewWork_groupNodes_sublist more available).subset
    (List.mem_of_find?_eq_some found)
  have original := unique.groupNode?_of_mem old
  rwa [(queue.startNewWork more available).1.groupNode?_ref found] at original

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
