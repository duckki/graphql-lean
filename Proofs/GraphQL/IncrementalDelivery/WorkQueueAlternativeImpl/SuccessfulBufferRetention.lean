import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.PendingFailureCut

/-! Sound memberships rule out silent buffered-task loss during successful closures.
The proof-side registration frame is derived at generated preparation and preserved locally.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open GraphQL.IncrementalDelivery.WorkQueueSemantics (Occurrence)
open GraphQL.IncrementalDelivery.ReferenceWorkQueue (TaskNode GroupNode)

private abbrev Kernel := ReferenceWorkQueue.State

-----------------------------------------------------------------------------------------
-- The derived registration frame survives each non-registering release step
-----------------------------------------------------------------------------------------

/-- Success preserves sound memberships as well as buffered links and exact catalogue data. -/
theorem SnapshotTaskEvidence.finishGroupSuccess {queue : Kernel} {work}
    (frame : SnapshotTaskEvidence queue work) (group : GroupNode)
    : SnapshotTaskEvidence (queue.finishGroupSuccess group).1 work := by
  have registration := queue.finishGroupSuccess_registration frame.live frame.contributors group
  exact ⟨frame.keys.finishGroupSuccess group, registration.1, registration.2.1,
    frame.started.finishGroupSuccess group, frame.matching.finishGroupSuccess group,
    frame.buffered.finishGroupSuccess group, frame.sound.finishGroupSuccess group,
    frame.registration.finishGroupSuccess group⟩

/-- Activation creates no buffered value and preserves exact registered task ownership. -/
theorem SnapshotTaskEvidence.startNewWork {queue : Kernel} {work}
    (frame : SnapshotTaskEvidence queue work) (released : ReferenceWorkQueue.NewWork)
    : SnapshotTaskEvidence (queue.startNewWork released).1 work := by
  have registration := ReferenceWorkQueue.State.startNewWork_registration frame.live
    frame.contributors released
  exact ⟨frame.keys.startNewWork released, registration.1, registration.2,
    frame.started.startNewWork released, frame.matching.startNewWork released,
    frame.buffered.startNewWork released, frame.sound.startNewWork released,
    frame.registration.startNewWork released⟩

/-- Failure only removes live records; their permanent catalogue and surviving links remain. -/
theorem SnapshotTaskEvidence.removeGroup {queue : Kernel} {work}
    (frame : SnapshotTaskEvidence queue work) (key : Nat)
    : SnapshotTaskEvidence (queue.removeGroup key) work := by
  refine ⟨frame.keys.removeGroup key,
    fun node member => frame.live node (List.mem_filter.mp member).1,
    frame.contributors, frame.started.removeGroup key, frame.matching.removeGroup key,
    frame.buffered.removeGroup key, frame.sound.removeGroup key, ?_⟩
  apply frame.registration.retain (next := queue.removeGroup key)
    (fun node member => frame.live node (List.mem_filter.mp member).1)
    frame.contributors (frame.started.removeGroup key)
  · exact fun _ member => member
  · exact fun _ member => member

/-- Rejection replay preserves metadata for every surviving computation record. -/
theorem SnapshotTaskEvidence.taskFailure {queue : Kernel} {work}
    (frame : SnapshotTaskEvidence queue work) (occurrence : Occurrence) (errors : Nat)
    : SnapshotTaskEvidence (queue.taskFailure occurrence errors).1 work := by
  have registration := queue.taskFailure_registration frame.live frame.contributors occurrence
    errors
  exact ⟨frame.keys.taskFailure occurrence errors, registration.1, registration.2.1,
    frame.started.taskFailure occurrence errors, frame.matching.taskFailure occurrence errors,
    frame.buffered.taskFailure occurrence errors, frame.sound.taskFailure occurrence errors,
    frame.registration.taskFailure occurrence errors⟩

/-- Any bounded mixed drain retains the same sound registration frame on surviving records. -/
theorem SnapshotTaskEvidence.drainReadyGroups {queue : Kernel} {work}
    (frame : SnapshotTaskEvidence queue work) (fuel : Nat)
    : SnapshotTaskEvidence (ReferenceWorkQueue.State.drainReadyGroups.go [] fuel queue).1
        work :=
  ReferenceWorkQueue.State.drainReadyGroups_go_preserves
    (fun current => SnapshotTaskEvidence current work)
    (fun _ group prior _ _ _ => (prior.finishGroupSuccess group).startNewWork _)
    frame fuel

-----------------------------------------------------------------------------------------
-- A successful noncontributor cannot select or silently prune a prepared buffer
-----------------------------------------------------------------------------------------

/-- A live successful group not contributing to this buffer leaves its exact node and
every previously live contributor intact, even when a contributor has a cached failure.
Sound memberships exclude selecting the task; buffered links exclude taskless pruning.
No health, announcement, counter, or uncancelled-owner qualification is needed.
-/
theorem successfulFlush_noncontributorBuffer {queue : Kernel} {work occurrence node}
    (frame : SnapshotTaskEvidence queue work) (group : GroupNode)
    (live : group ∈ queue.groupNodes) (found : queue.taskNode? occurrence = some node)
    (stored : node.value.isSome = true)
    (noncontributor
      : group.group.node.ref ∉ node.task.groups.map Execution.DeliveryNode.ref)
    : (queue.finishGroupSuccess group).1.taskNode? occurrence = some node
      ∧ ∀ key ∈ node.task.groups.map Execution.DeliveryNode.ref,
          key ∈ queue.groupNodes.map (fun group => group.group.node.ref)
          → key
            ∈ (queue.finishGroupSuccess group).1.groupNodes.map
                (fun group => group.group.node.ref) := by
  have unlisted : occurrence ∉ group.tasks := by
    intro selected
    have known := ReferenceWorkQueue.State.taskNode?_some found
    exact noncontributor (frame.sound.startedOwner frame.started frame.matching known.1 live
      (known.2.symm ▸ selected))
  have retained := (queue.finishGroupSuccess_lookup_unselected group unlisted).trans found
  refine ⟨retained, ?_⟩
  intro key contributes present
  exact ReferenceWorkQueue.State.finishGroupSuccess_bufferedOwner_present frame.buffered
    group live (ReferenceWorkQueue.State.taskNode?_some retained).1 stored contributes
    present

/-- Generated preparation derives membership soundness, the inverse ownership direction.
Every listed live task belongs to that group's contributing keys; the caller supplies no
catalogue match or task-registration invariant.
-/
theorem generatedSnapshot_listedContributor {work inputs event occurrence node group}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (valid : ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ [event]))
    (started : ReferenceWorkQueue.inputsStarted work inputs = true)
    (found
      : (registrationSnapshot ((State.initialize work).runNormalized inputs).1.queue
          event).taskNode?
          occurrence
        = some node)
    (live
      : group
        ∈ (registrationSnapshot ((State.initialize work).runNormalized inputs).1.queue
            event).groupNodes)
    (selected : occurrence ∈ group.tasks)
    : group.group.node.ref ∈ node.task.groups.map Execution.DeliveryNode.ref := by
  have frame := GeneratedSnapshotTaskEvidence_holds work inputs event generated valid started
  have known := ReferenceWorkQueue.State.taskNode?_some found
  exact frame.sound.startedOwner frame.started frame.matching known.1 live
    (known.2.symm ▸ selected)

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
