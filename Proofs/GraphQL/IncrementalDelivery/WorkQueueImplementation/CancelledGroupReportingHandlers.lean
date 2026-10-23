import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CancelledGroupReporting

/-! Actual task-failure handling retains the positive closure behind each cleanup marker. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Removing task bookkeeping changes no group cancellation marker.
Witness: report origins depend only on the unchanged cancellation registry.
-/
theorem State.CancelledRecordsReported.removeTask {queue : State} {work events}
    (reported : queue.CancelledRecordsReported work events) (task : Occurrence)
    : (queue.removeTask task).CancelledRecordsReported work events :=
  reported

/-- Updating a group's counter or cache does not change cancellation markers.
Witness: live-node replacement leaves the permanent cancellation registry unchanged.
-/
theorem State.CancelledRecordsReported.putGroupNode {queue : State} {work events}
    (reported : queue.CancelledRecordsReported work events) (node : GroupNode)
    : (queue.putGroupNode node).CancelledRecordsReported work events :=
  reported

/-- Failed-task processing reports every new cancellation marker in its own outputs.
Witness: the exact owner fold appends positive failure completions before recording their
subtree cleanup. Latent owners cache their errors but introduce no marker; ignored or
missing tasks also introduce none. Task presence is the only executable settlement check.
-/
theorem State.CancelledRecordsReported.taskFailure
    {queue : State} {work : Execution.Work} {events : List Execution.WorkQueueEvent}
    {parents : NodeRef → NodeRefs}
    (reported : queue.CancelledRecordsReported work events)
    (generated : ExecutedWork work) (records : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (occurrence : Occurrence) (errors : Nat) (positive : 0 < errors)
    : (queue.taskFailure occurrence errors).1.CancelledRecordsReported work
        (events ++ (queue.taskFailure occurrence errors).2) :=
  reported.taskFailure_causes generated records links canonical occurrence errors
    (fun _ _ _ _ => positive)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
