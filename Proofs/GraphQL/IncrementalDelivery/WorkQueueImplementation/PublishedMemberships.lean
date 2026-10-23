import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskMembershipAbsence
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupPublication
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.DrainAccounting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PublicationInventory
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ActiveLinks

/-! Flushing an occurrence removes its membership from every shared contributor. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (ExecutionGroupValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Membership exclusion concerns group records, not only the stored-value map
-----------------------------------------------------------------------------------------

/-- The same exact publication ledger also excludes old and newly delivered memberships.
Witness: reuse the flush's existing selected-node witness and inventory proof, then show
each selected stored value's occurrence is removed globally. No independently chosen
publication sequence or stronger event/source premise is introduced.
-/
theorem State.PublicationInventory.finishGroupSuccess_memberships
    {queue : State} {property published}
    (inventory : queue.PublicationInventory property published)
    (absent : ∀ publication ∈ published, queue.TaskMembershipAbsent publication.1)
    (group : GroupNode)
    : ∃ added : List ObjectPublication,
        added.map Prod.snd
          = (queue.finishGroupSuccess group).2.1.flatMap WorkQueueEvent.objectValues
        ∧ (queue.finishGroupSuccess group).1.PublicationInventory property
            (published ++ added)
        ∧ ∀ publication ∈ published ++ added,
            (queue.finishGroupSuccess group).1.TaskMembershipAbsent publication.1 := by
  obtain ⟨selected, unique, known, events, retained, removed⟩ :=
    queue.finishGroupSuccess_publications group
  obtain ⟨values, next⟩ := inventory.finishGroupSuccess_selected group selected unique known
    events retained removed
  refine ⟨storedPublications selected, values, next, ?_⟩
  intro publication member
  rcases List.mem_append.mp member with old | new
  · exact (absent publication old).finishGroupSuccess group
  · obtain ⟨node, included, occurrenceEq, _⟩ := storedPublications_member new
    rw [← occurrenceEq]
    exact queue.finishGroupSuccess_selectedMembershipAbsent group
      (known node included).1 (known node included).2

/-- The full recursive drain retains membership exclusion on its one publication ledger.
Witness: success adds its actual selected values and removes their shared memberships;
activation preserves exclusions, and failure removes records without adding values.
All internal successful releases use the same growing ledger, including immediate drains
of children promoted through taskless wrappers.
-/
theorem State.PublicationInventory.drainReadyGroups_memberships
    {queue : State} {property published}
    (inventory : queue.PublicationInventory property published)
    (absent : ∀ publication ∈ published, queue.TaskMembershipAbsent publication.1)
    (available : List (Occurrence × Nat) := [])
    : ∃ added : List ObjectPublication,
        added.map Prod.snd
          = (queue.drainReadyGroups available).2.1.flatMap WorkQueueEvent.objectValues
        ∧ (queue.drainReadyGroups available).1.PublicationInventory property
            (published ++ added)
        ∧ ∀ publication ∈ published ++ added,
            (queue.drainReadyGroups available).1.TaskMembershipAbsent publication.1 := by
  have loop (fuel : Nat) (current : State) (priorPublished : List ObjectPublication)
      (prior : current.PublicationInventory property priorPublished)
      (excluded : ∀ publication ∈ priorPublished, current.TaskMembershipAbsent publication.1)
      : ∃ added : List ObjectPublication,
          added.map Prod.snd
            = (State.drainReadyGroups.go available fuel current).2.1.flatMap
                WorkQueueEvent.objectValues
          ∧ (State.drainReadyGroups.go available fuel current).1.PublicationInventory property
              (priorPublished ++ added)
          ∧ ∀ publication ∈ priorPublished ++ added,
              (State.drainReadyGroups.go available fuel current).1.TaskMembershipAbsent
                publication.1 := by
    induction fuel generalizing current priorPublished with
    | zero =>
        exact ⟨
          [],
          rfl,
          by simpa [State.drainReadyGroups.go] using prior,
          by simpa [State.drainReadyGroups.go] using excluded
        ⟩
    | succ fuel ih =>
        unfold State.drainReadyGroups.go
        dsimp only
        split
        · exact ⟨[], rfl, by simpa using prior, by simpa using excluded⟩
        · rename_i node selected
          obtain ⟨first, firstValues, flushed, removed⟩ :=
            prior.finishGroupSuccess_memberships excluded node
          obtain ⟨later, laterValues, final, excluded⟩ := ih _ _
            ⟨flushed.unique, flushed.provenance,
              flushed.stored.startNewWork (current.finishGroupSuccess node).2.2 available⟩
            (fun publication member =>
              (removed publication member).startNewWork
                (current.finishGroupSuccess node).2.2 available)
          refine ⟨first ++ later, ?_, ?_, ?_⟩
          · simp only [List.map_append, List.flatMap_append, firstValues, laterValues]
          · simpa only [List.append_assoc] using final
          · simpa only [List.append_assoc] using excluded
  exact loop _ queue published inventory absent

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
