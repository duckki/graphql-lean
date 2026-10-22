import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ResourceRequests

/-! Concrete record locations for independently supplied acquired resource leases.
Representation definitions are separate from generated stop-coverage proofs.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement

-----------------------------------------------------------------------------------------
-- Record representation mentions ownership locations, never computed cleanup targets
-----------------------------------------------------------------------------------------

/-- Three concrete locations that represent queue-owned task/source identities.
An unrejected task is linked to a live group; a source is active or held by a stored task. These are
record observations, not an acquisition mechanism or a complete native inventory by definition.
-/
inductive RecordTargetRepresented (queue : ReferenceWorkQueue.State)
    : CleanupTarget → Prop where
  | task {key occurrence group}
    (found : queue.groupNode? key = some group) (linked : occurrence ∈ group.tasks)
    (unrejected
      : (queue.taskNode? occurrence).any (fun node => node.rejection.isSome) = false)
    : RecordTargetRepresented queue (.task occurrence)
  | activeStream {key} (active : key ∈ queue.rootStreams)
    : RecordTargetRepresented queue (.stream key)
  | bufferedStream {occurrence node key}
    (found : queue.taskNode? occurrence = some node) (stored : node.value.isSome = true)
    (held : key ∈ node.childStreams)
    : RecordTargetRepresented queue (.stream key)

/-- Queued internal notices change none of the concrete resource-record locations. -/
theorem RecordTargetRepresented.withGroupFailures {queue target}
    (represented : RecordTargetRepresented queue target)
    (notices : List ReferenceWorkQueue.GroupFailureEvent)
    : RecordTargetRepresented ({ queue with groupFailureEvents := notices }) target := by
  cases represented with
  | task found linked unrejected => exact .task found linked unrejected
  | activeStream active => exact .activeStream active
  | bufferedStream found stored held => exact .bufferedStream found stored held

/-- Every independently acquired queue-owned lease has one concrete current record location.
This native construction obligation asks for record locations, not cleanup membership:
generated proofs derive the missing root path and stop traversal. Producer-owned and requested leases
are not queue-owned, and no lease is manufactured from the record map.
-/
def ResourcesRepresented (queue : ReferenceWorkQueue.State) (resources : ResourceState)
    : Prop :=
  ∀ target, resources target = .owned .queue → RecordTargetRepresented queue target

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
