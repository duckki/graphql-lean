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
missing tasks also introduce none. The healthy-owner guard is unchanged.
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
        (events ++ (queue.taskFailure occurrence errors).2) := by
  let step (acc : State × List WorkQueueEvent) (group : Execution.DeliveryNode) :=
    let (current, outputs) := acc
    match current.groupNode? group.ref with
    | none => (current, outputs)
    | some node =>
        if current.rootGroups.contains group.ref then
          let (next, failure) := current.finishGroupFailure node errors
          (next, outputs ++ [failure])
        else (current.putGroupNode
          { node with
            pending := node.pending - 1
            failure := some (node.failure.getD 0 + errors) }, outputs)
  let invariant (acc : State × List WorkQueueEvent) :=
    acc.1.CancelledRecordsReported work (events ++ acc.2)
    ∧ acc.1.GroupNodesMatchWork work ∧ acc.1.ChildLinksCanonical parents
  have fold (groups : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent)
      (prior : invariant acc) : invariant (groups.foldl step acc) := by
    induction groups generalizing acc with
    | nil => exact prior
    | cons group rest ih =>
        apply ih
        obtain ⟨current, outputs⟩ := acc
        dsimp only [step]
        split
        · exact prior
        · rename_i node found
          have member := List.mem_of_find?_eq_some found
          split
          · exact ⟨by
              simpa only [List.append_assoc] using
                (prior.1.finishGroupFailure generated prior.2.1 prior.2.2 canonical
                  node errors positive),
              prior.2.1.removeGroup _, prior.2.2.removeGroup _⟩
          · exact ⟨prior.1.putGroupNode _,
              prior.2.1.putGroupNode _ (prior.2.1 node member),
              prior.2.2.putGroupNode _ (prior.2.2 node member)⟩
  unfold State.taskFailure
  split
  · simpa only [List.append_nil] using reported
  · rename_i node found
    split
    · simpa only [List.append_nil] using reported.removeTask occurrence
    · exact (fold node.task.groups (queue.removeTask occurrence, [])
        ⟨by simpa only [List.append_nil] using reported.removeTask occurrence,
          records.removeTask occurrence, links.removeTask occurrence⟩).1

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
