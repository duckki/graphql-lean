import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.PublicationExclusion

/-! Optional generated failure-cut topology statements. Actual mixed-release resource
disposal is constructed directly in GeneratedBufferDisposal, independently of these cuts.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open GraphQL.IncrementalDelivery.WorkQueueSemantics (Occurrence)
open GraphQL.IncrementalDelivery.ReferenceWorkQueue (TaskNode)

-----------------------------------------------------------------------------------------
-- Isolate the actual generated pending-buffer cut, without assuming a disposal outcome
-----------------------------------------------------------------------------------------

/-- Generated failure-cut construction target, proved in GeneratedFailureCut. A prepared
buffered task that remains pending in the proof-only filter but disappears from this
dispatch has every still-live contributor
below an actually emitted failure root in that same view. It assumes neither cleanup
effects nor resource inventory, and is not a host/source law.
-/
def GeneratedPendingBufferFailureCut : Prop :=
  ∀ work inputs event,
    ReferenceWorkQueue.ExecutedWork work
    → ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ [event])
    → ReferenceWorkQueue.inputsStarted work (inputs ++ [[event]]) = true
    → (match event with
        | .taskSuccess _ _ | .streamItems _ _ => True
        | _ => False)
    → ∀ (occurrence : Occurrence) (node : TaskNode),
        let before := ((State.initialize work).runNormalized inputs).1
        let snapshot := registrationSnapshot before.queue event
        let events := (before.queue.handleGraphEvent event).2
        let view := failurePruningView before.queue event events
        snapshot.taskNode? occurrence = some node
        → node.value.isSome = true
        → pruningPending snapshot event events occurrence = true
        → (before.queue.handleGraphEvent event).1.taskNode? occurrence = none
        → ∀ owner ∈ node.task.groups,
            ∀ group,
              view.groupNode? owner.ref = some group
              → ∃ root ∈ failureRoots events, view.LiveDescendant root owner.ref

/-- Stronger exact-record cut: loss or replacement of the prepared node suffices.
This exposes the handler's retention alternative without assuming complete disappearance;
it remains a proof-construction target, not an additional source condition.
-/
def GeneratedPendingBufferLossCut : Prop :=
  ∀ work inputs event,
    ReferenceWorkQueue.ExecutedWork work
    → ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ [event])
    → ReferenceWorkQueue.inputsStarted work (inputs ++ [[event]]) = true
    → (match event with
        | .taskSuccess _ _ | .streamItems _ _ => True
        | _ => False)
    → ∀ (occurrence : Occurrence) (node : TaskNode),
        let before := ((State.initialize work).runNormalized inputs).1
        let snapshot := registrationSnapshot before.queue event
        let events := (before.queue.handleGraphEvent event).2
        let view := failurePruningView before.queue event events
        snapshot.taskNode? occurrence = some node
        → node.value.isSome = true
        → pruningPending snapshot event events occurrence = true
        → (before.queue.handleGraphEvent event).1.taskNode? occurrence ≠ some node
        → ∀ owner ∈ node.task.groups,
            ∀ group,
              view.groupNode? owner.ref = some group
              → ∃ root ∈ failureRoots events, view.LiveDescendant root owner.ref

/-- The exact-record cut includes the previously proved disappearance target. -/
theorem GeneratedPendingBufferFailureCut_of_lossCut (cuts : GeneratedPendingBufferLossCut)
    : GeneratedPendingBufferFailureCut := by
  intro work inputs event generated valid started release occurrence node
  dsimp only
  intro found stored pending dropped
  apply cuts work inputs event generated valid started release occurrence node found stored pending
  rw [dropped]
  intro impossible
  cases impossible

-----------------------------------------------------------------------------------------
-- Every other prerequisite of the universal resource target is already generated
-----------------------------------------------------------------------------------------

/-- Pending prepared buffers keep an initially live owner in the actual cleanup view.
Catalogue identity and contributor equality are derived, not supplied by a native port.
-/
theorem generatedSnapshot_pendingOwned {work inputs event occurrence}
    {node : TaskNode}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (valid : ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ [event]))
    (started : ReferenceWorkQueue.inputsStarted work inputs = true)
    (found
      : (registrationSnapshot ((State.initialize work).runNormalized inputs).1.queue
          event).taskNode?
          occurrence
        = some node)
    (pending
      : pruningPending
          (registrationSnapshot ((State.initialize work).runNormalized inputs).1.queue
            event)
          event
          ((((State.initialize work).runNormalized inputs).1.queue).handleGraphEvent
            event).2
          occurrence
        = true)
    (owned
      : ∃ owner ∈ node.task.groups,
          ∃ group,
            (registrationSnapshot ((State.initialize work).runNormalized inputs).1.queue
              event).groupNode?
              owner.ref
            = some group)
    : ∃ owner ∈ node.task.groups,
        ∃ group,
          (failurePruningView ((State.initialize work).runNormalized inputs).1.queue event
            ((((State.initialize work).runNormalized inputs).1.queue).handleGraphEvent
              event).2).groupNode?
            owner.ref
          = some group := by
  obtain ⟨task, catalogue, sameGroups⟩ := generatedSnapshot_taskCatalogue generated valid started found
  obtain ⟨owner, contributes, group, live⟩ := owned
  exact ⟨owner, contributes, failurePruningView_pendingOwner catalogue pending
    (sameGroups.symm ▸ contributes) live⟩

/- Actual disposal is now proved directly in GeneratedBufferDisposal. The former
cut-to-output-scan cleanup adapter is retired; the cut above remains topology evidence. -/

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
