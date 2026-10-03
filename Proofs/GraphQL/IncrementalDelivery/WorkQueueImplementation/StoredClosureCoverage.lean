import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StoredTaskLinks
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.DrainClosureBoundaries

/-! Buffered contributions are covered at actual indexed successful drain closures. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Buffered-only membership suffices for a live group's successful flush
-----------------------------------------------------------------------------------------

/-- A live group's buffered contributors publish before its completion event.
Witness: buffered memberships supply the complete flush selection. Unlike active-task
links, this invariant survives activation without requiring links for new empty nodes.
-/
theorem State.PublicationInventory.finishGroupSuccess_storedContributors {queue : State}
    {property published} (inventory : queue.PublicationInventory property published)
    (links : queue.StoredTaskLinks) (group : GroupNode) (live : group ∈ queue.groupNodes)
    : ∃ (added : List ObjectPublication) (before : List WorkQueueEvent),
        (queue.finishGroupSuccess group).2.1
          = before
            ++ [.groupSuccess group.group.node
                  (queue.finishGroupSuccess group).2.2.newGroups
                  (queue.finishGroupSuccess group).2.2.newStreams]
        ∧ added.map Prod.snd = before.flatMap WorkQueueEvent.objectValues
        ∧ (queue.finishGroupSuccess group).1.PublicationInventory property
            (published ++ added)
        ∧ (∀ occurrence node value,
            queue.taskNode? occurrence = some node
            → node.value = some value
            → group.group.node.ref ∈ node.task.groups.map Execution.DeliveryNode.ref
            → (occurrence, value) ∈ added) := by
  obtain ⟨added, before, output, values, next, covered, _⟩ :=
    inventory.finishGroupSuccess_coverage group
  refine ⟨added, before, output, values, next, ?_⟩
  intro occurrence node value found stored contributor
  have known := State.taskNode?_some found
  have member : occurrence ∈ group.tasks :=
    known.2 ▸ links node known.1 (by simp only [stored, Option.isSome_some])
      group live contributor
  exact covered occurrence member node value found stored

-----------------------------------------------------------------------------------------
-- Indexed executable carriers supply their own live boundary and inherited memberships
-----------------------------------------------------------------------------------------

/-- Each indexed successful drain carrier covers every initially buffered contributor.
Witness: recover the actual pre-closure queue, conserve values through its mixed prefix,
and flush using inherited buffered links. One labelled inventory covers that strict output
prefix and the post-flush state; no intermediate lookup or membership facts are assumed.
This local witness does not yet identify the common matching across all source handlers.
-/
theorem State.PublicationInventory.drainReadyGroups_go_success_coverage {queue : State}
    {property published} (inventory : queue.PublicationInventory property published)
    (links : queue.StoredTaskLinks) (fuel : Nat) {index group groups streams}
    (selected
      : (State.drainReadyGroups.go fuel queue).2[index]?
        = some (.groupSuccess group groups streams))
    : ∃ (steps : Nat) (node : GroupNode) (added : List ObjectPublication),
        steps < fuel
        ∧ (State.drainReadyGroups.go steps queue).1.groupNode? node.group.node.ref
          = some node
        ∧ node.group.node = group
        ∧ added.map Prod.snd
          = ((State.drainReadyGroups.go fuel queue).2.take index).flatMap
              WorkQueueEvent.objectValues
        ∧ ((State.drainReadyGroups.go steps queue).1.finishGroupSuccess
            node).1.PublicationInventory
            property (published ++ added)
        ∧ (∀ occurrence task value,
            queue.taskNode? occurrence = some task
            → task.value = some value
            → group.ref ∈ task.task.groups.map Execution.DeliveryNode.ref
            → (occurrence, value) ∈ added) := by
  obtain ⟨steps, node, before, bound, found, _, _, _, same, output, exactPrefix⟩ :=
    State.drainReadyGroups_go_success_boundary fuel queue selected
  obtain ⟨first, firstValues, advanced, conserved⟩ :=
    inventory.drainReadyGroups_go_conserves steps
  obtain ⟨last, closeBefore, closeOutput, lastValues, final, covered⟩ :=
    advanced.finishGroupSuccess_storedContributors (links.drainReadyGroups_go steps)
      node (List.mem_of_find?_eq_some found)
  have samePrefix : closeBefore = before :=
    List.append_inj_left' (closeOutput.symm.trans output) rfl
  refine ⟨steps, node, first ++ last, bound, found, same, ?_, ?_, ?_⟩
  · simp only [exactPrefix, List.map_append, List.flatMap_append, firstValues, lastValues,
      samePrefix]
  · simpa only [List.append_assoc] using final
  · intro occurrence task value lookup stored contributes
    obtain ⟨contributor, member, sameRef⟩ := List.mem_map.mp contributes
    have live : ∃ contributor ∈ task.task.groups, ∃ owner,
        (State.drainReadyGroups.go steps queue).1.groupNode? contributor.ref = some owner :=
      ⟨contributor, member, node, by simpa only [sameRef, same] using found⟩
    rcases conserved occurrence task value lookup stored live with earlier | retained
    · exact List.mem_append_left _ earlier
    · apply List.mem_append_right
      exact covered occurrence task value retained stored
        (same ▸ List.mem_map.mpr ⟨_, member, sameRef⟩)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
