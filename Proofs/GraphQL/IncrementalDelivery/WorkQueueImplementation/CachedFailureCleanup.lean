import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CachedFailures
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupRemoval

/-! Healthy accounting through the retained-failure branch of release-time draining. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Closing a supported cached failure removes no healthy registration record.
Witness: cache provenance supplies the failed contributor; canonical record edges
justify every descendant cancellation, including taskless wrappers.
-/
theorem State.CachedFailuresSupported.finishGroupFailure_recordHealthyRetained
    {queue work failed parents node errors}
    (supported : State.CachedFailuresSupported queue work failed)
    (links : queue.ChildLinksCanonical parents)
    (matching : queue.GroupNodesMatchWork work)
    (canonical
      : ∀ group dependencies,
          GroupRecordAt work group dependencies → dependencies = parents group.ref)
    (member : node ∈ queue.groupNodes) (cached : node.failure = some errors)
    : ∀ other ∈ queue.groupNodes,
        ¬GroupRecordInvalidated work failed other.group.node.ref
        → other ∈ (queue.finishGroupFailure node errors).1.groupNodes := by
  exact queue.removeGroup_recordHealthyRetained links matching canonical
    node.group.node.ref
    (supported.invalidated member (by simp [cached])).toRecordInvalidated

/-- A cached-failure closure preserves all registered unsettled tasks' healthy owners.
Witness: the original registered-task witness remains linked in a retained healthy node;
failure removal does not change the permanent task registry or surviving memberships.
-/
theorem State.HealthyRegisteredTaskAccounting.finishCachedGroupFailure
    {queue work settled failed parents node errors}
    (accounted : State.HealthyRegisteredTaskAccounting queue work settled failed)
    (supported : queue.CachedFailuresSupported work failed)
    (tasksMatch : queue.RegisteredTasksMatch work)
    (generated : ExecutedWork work)
    (links : queue.ChildLinksCanonical parents)
    (matching : queue.GroupNodesMatchWork work)
    (canonical
      : ∀ group dependencies,
          GroupRecordAt work group dependencies → dependencies = parents group.ref)
    (member : node ∈ queue.groupNodes) (cached : node.failure = some errors)
    : (queue.finishGroupFailure node errors).1.HealthyRegisteredTaskAccounting
        work settled failed := by
  exact accounted.removeInvalidatedGroup tasksMatch generated links matching canonical
    node.group.node.ref
    (supported.invalidated member (by simp [cached])).toRecordInvalidated

/-- A cached-failure closure also preserves the healthy pending-count ledger.
Witness: group removal filters nodes and does not mutate surviving pending counters.
-/
theorem State.HealthyPendingTracks.finishGroupFailure {queue work settled failed}
    (tracks : State.HealthyPendingTracks queue work settled failed)
    (node : GroupNode) (errors : Nat)
    : (queue.finishGroupFailure node errors).1.HealthyPendingTracks work settled failed :=
  tracks.removeGroup node.group.node.ref

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
