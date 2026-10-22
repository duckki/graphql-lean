import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.UnsettledTaskDrain
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedTaskRemoval

/-! Optional proof-only failure-frontier task membership. Actual task disposal follows the
real fused reductions; the filtered-view trace is not an emitted-effect oracle.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
private abbrev Kernel := ReferenceWorkQueue.State

/-- A complete emitted failure frontier covering every live owner requests this task.
This reduction uses the actual effect view and trace. The chronological cut is a separate
construction obligation, not a host-source premise or a desired cleanup assumption.
-/
theorem failureFrontier_task {before : Kernel}
    {event events parents occurrence task final targets}
    (trace
      : PruningGroups (failurePruningView before event events) (failureRoots events) final
          targets)
    (forest : (failurePruningView before event events).RemovalForest parents)
    (links
      : (failurePruningView before event events).TaskLinkedOn occurrence
          (task.groups.map Execution.DeliveryNode.ref))
    (catalogue : (failurePruningView before event events).task? occurrence = some task)
    (owned
      : ∃ owner ∈ task.groups,
          ∃ group,
            (failurePruningView before event events).groupNode? owner.ref = some group)
    (cut
      : ∀ owner ∈ task.groups,
          ∀ group,
            (failurePruningView before event events).groupNode? owner.ref = some group
            → ∃ root ∈ failureRoots events,
                (failurePruningView before event events).LiveDescendant root owner.ref)
    (unrejected
      : (failurePruningView before event events).TaskRejectionsSatisfy
          (fun rejected _ => rejected ≠ occurrence))
    : .task occurrence ∈ targets := by
  have requested : .task occurrence ∈ targets := by
    rcases trace.linkedOwnerOrAbort links catalogue owned unrejected with kept | aborted
    · obtain ⟨owner, member, group, lookup⟩ := kept
      obtain ⟨old, earlier, _⟩ := trace.groupEdgesFrom owner.ref group lookup
      obtain ⟨root, emitted, path⟩ := cut owner member old earlier
      rw [trace.coversDescendants forest root emitted owner.ref path] at lookup
      contradiction
    · exact aborted
  exact requested

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
