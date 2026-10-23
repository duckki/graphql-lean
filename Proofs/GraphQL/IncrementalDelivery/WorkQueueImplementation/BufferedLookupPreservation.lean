import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskIntegrationLookups
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskLookupUpdates
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ReleasePublicationLedger

/-! Integration preserves exact buffered lookups outside the settling producer. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Registration and producer attachment cannot overwrite another stored task
-----------------------------------------------------------------------------------------

-----------------------------------------------------------------------------------------
-- Buffered carrier coverage transports through lookup-preserving preparation
-----------------------------------------------------------------------------------------

/-- The success handler's prepared state contains its input value and original task.
Witness: install the exact first-match node, then preserve its descriptor and value
through child integration; attaching streams may extend only its child-stream refs.
-/
theorem State.taskSuccess_prepared_value {queue : State} {occurrence node}
    (found : queue.taskNode? occurrence = some node) (result : TaskResult)
    : ∃ prepared,
        ((queue.putTaskNode { node with value := some result.value }).maybeIntegrateWork
            result.work (some occurrence)).1.taskNode?
            occurrence
          = some prepared
        ∧ prepared.task = node.task
        ∧ prepared.value = some result.value :=
  State.maybeIntegrateWork_lookup_producer
    (State.putTaskNode_value_lookup found result.value) result.work

/-- Coverage for a prepared queue also covers each unchanged input lookup.
Witness: use the exact retained node, including its contributor list and stored payload.
-/
theorem State.BufferedClosuresCovered.of_lookups {queue prepared : State}
    {published events} (covered : prepared.BufferedClosuresCovered published events)
    (retained
      : ∀ occurrence node value,
          queue.taskNode? occurrence = some node
          → node.value = some value
          → prepared.taskNode? occurrence = some node)
    : queue.BufferedClosuresCovered published events := by
  intro index group groups streams selected occurrence node value found stored contributes
  exact covered index group groups streams selected occurrence node value
    (retained occurrence node value found stored) stored contributes

/-- Output with no successful group carrier has no buffered closure obligations.
Witness: any indexed carrier would contradict its exclusion from the output list.
-/
theorem State.BufferedClosuresCovered.of_noGroupSuccess {queue : State} {published events}
    (absent
      : ∀ group groups streams,
          Execution.WorkQueueEvent.groupSuccess group groups streams ∉ events)
    : queue.BufferedClosuresCovered published events := by
  intro index group groups streams selected
  exact False.elim (absent group groups streams (List.mem_of_getElem? selected))

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
