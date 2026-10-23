import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CancellationRetirementReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureValueRetention

/-! Transfer prepared-buffer certificates through cancellation-aware owner conservation. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open WorkQueueSemantics
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)

/-- A later successful carrier retains every relevant old buffer through silent
preparation. Registered absent contributors cannot be recreated, and cancelled contributors
cannot become successful carriers. No unconditional task-lookup preservation is required.
-/
theorem State.BufferedClosuresCovered.of_preparationOwners {queue prepared : State}
    {published fuel available}
    (covered
      : prepared.BufferedClosuresCovered published
          (State.drainReadyGroups.go available fuel prepared).2.1)
    (owners : queue.StoredOwnersConserved [] prepared)
    (started : queue.StartedTasksRegistered) (registered : queue.TaskGroupsRegistered)
    (cancelled : prepared.CancellationsRetired)
    (retirement : ∀ ref, queue.RetiredGroup ref → prepared.RetiredGroup ref)
    : queue.BufferedClosuresCovered published
        (State.drainReadyGroups.go available fuel prepared).2.1 := by
  intro index group groups streams selected occurrence node value found stored contributes
  have old := (State.taskNode?_some found).1
  have known : group.ref ∈ queue.registeredGroups :=
    registered node.task (started node old) group.ref contributes
  have live : group.ref ∈ queue.groupNodes.map (fun owner => owner.group.node.ref) := by
    apply Classical.byContradiction
    intro missing
    exact (retirement group.ref ⟨known, missing⟩).drainReadyGroups_go_noSuccess
      fuel available selected rfl
  have uncancelled := cancelled.drainReadyGroups_go_carrier_uncancelled fuel available selected
  rcases owners occurrence node value found stored group.ref contributes live uncancelled
      with impossible | ⟨retained, _⟩
  · cases impossible
  · exact covered index group groups streams selected occurrence node value retained stored
      contributes

/-- Endpoint value conservation only needs buffers protected by a surviving contributor.
Permanent retirement transports the endpoint's live contributor back across preparation;
its cancellation exclusion licenses the existing empty-publication owner certificate.
-/
theorem State.StoredValuesConserved.of_preparationOwners {queue prepared next : State}
    {published} (conserved : prepared.StoredValuesConserved published next)
    (owners : queue.StoredOwnersConserved [] prepared)
    (started : queue.StartedTasksRegistered) (registered : queue.TaskGroupsRegistered)
    (cancelled : prepared.CancellationsRetired)
    (retirement : ∀ ref, queue.RetiredGroup ref → prepared.RetiredGroup ref)
    (future : ∀ ref, prepared.RetiredGroup ref → next.RetiredGroup ref)
    : queue.StoredValuesConserved published next := by
  intro occurrence node value found stored survivor
  obtain ⟨contributor, contributes, owner, present⟩ := survivor
  have ownerRef := State.groupNode?_ref present
  have endpoint : contributor.ref ∈ next.groupNodes.map (fun group => group.group.node.ref) :=
    List.mem_map.mpr ⟨owner, List.mem_of_find?_eq_some present, ownerRef⟩
  have known : contributor.ref ∈ queue.registeredGroups := registered node.task
    (started node (State.taskNode?_some found).1) contributor.ref (List.mem_map_of_mem contributes)
  have live : contributor.ref ∈ queue.groupNodes.map (fun group => group.group.node.ref) := by
    apply Classical.byContradiction
    intro missing
    exact (future _ (retirement _ ⟨known, missing⟩)).2 endpoint
  have uncancelled : contributor.ref ∉ prepared.cancelledGroups := by
    intro failed
    exact (future _ (cancelled _ failed)).2 endpoint
  rcases owners occurrence node value found stored contributor.ref
      (List.mem_map_of_mem contributes) live uncancelled with impossible | ⟨retained, _⟩
  · cases impossible
  · exact conserved occurrence node value retained stored ⟨contributor, contributes, owner, present⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
