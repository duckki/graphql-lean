import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SourceOutputBlocks
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamPublication

/-! Source-handler prefixes retain the exact item count needed by occurrence matching. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Every accepted handler block retains its exact item projection
-----------------------------------------------------------------------------------------

/-- Atomizing a list preserves its ordered item projection.
Witness: apply the existing eventwise item-erasure theorem under concatenation.
-/
theorem publicationAtoms_list_itemValues (events : List Execution.WorkQueueEvent)
    : (events.flatMap publicationAtoms).flatMap normalizedItemValues
      = events.flatMap normalizedItemValues := by
  induction events with
  | nil => rfl
  | cons event rest ih =>
      simp only [List.flatMap_cons, List.flatMap_append, (publicationAtoms_values event).2, ih]

/-- Each accepted handler block emits exactly the items supplied by its source label.
Witness: induction through actual handlers, with acceptance split at each input; publisher
normalization and atomic expansion preserve its item projection.
-/
theorem State.sourceOutputBlocks_itemValues (queue : State)
    (publisher : IncrementalPublisher) (received : List GraphEvent)
    (accepted : queue.acceptsBatch received = true)
    : ∀ block ∈ (queue.sourceOutputBlocks publisher received).2.2,
        block.2.flatMap normalizedItemValues
        = (block.1.toList.flatMap GraphEvent.itemPublications).map Prod.snd := by
  induction received generalizing queue publisher with
  | nil => intro block impossible; cases impossible
  | cons event rest ih =>
      have both : queue.acceptsGraphEvent event = true ∧
          (queue.handleGraphEvent event).1.acceptsBatch rest = true := by
        simpa only [State.acceptsBatch, Bool.and_eq_true] using accepted
      intro block member
      rcases List.mem_cons.mp member with same | later
      · subst block
        dsimp only
        rw [publicationAtoms_list_itemValues, publisher.normalizeBatch_itemValues,
          queue.handleGraphEvent_itemValues event both.1]
        simp
      · exact ih _ _ both.2 block later

/-- A started batch retains exact item projections for its handler and terminal blocks.
Witness: accepted handlers use the preceding theorem; a terminal block carries no items.
-/
theorem State.sourceBatchBlocks_itemValues (queue : State)
    (publisher : IncrementalPublisher) (received : List GraphEvent)
    (accepted : queue.acceptsBatch received = true)
    : ∀ block ∈ (queue.sourceBatchBlocks publisher received).2.2,
        block.2.flatMap normalizedItemValues
        = (block.1.toList.flatMap GraphEvent.itemPublications).map Prod.snd := by
  intro block member
  simp only [State.sourceBatchBlocks] at member
  split at member
  · cases member
  · split at member
    · rcases List.mem_append.mp member with handler | terminal
      · exact queue.sourceOutputBlocks_itemValues publisher received accepted block handler
      · have same := List.mem_singleton.mp terminal
        subst block
        rfl
    · exact queue.sourceOutputBlocks_itemValues publisher received accepted block member

/-- Every block of an accepted multi-batch run retains its source-label item projection.
Witness: actual batch acceptance and queue-state agreement thread the local certificate.
-/
theorem State.sourceRunBlocks_itemValues (queue : State)
    (publisher : IncrementalPublisher) (batches : List (List GraphEvent))
    (started : queue.batchesStarted batches = true)
    : ∀ block ∈ (queue.sourceRunBlocks publisher batches).2.2,
        block.2.flatMap normalizedItemValues
        = (block.1.toList.flatMap GraphEvent.itemPublications).map Prod.snd := by
  induction batches generalizing queue publisher with
  | nil => intro block impossible; cases impossible
  | cons batch rest ih =>
      obtain ⟨_, accepted, laterStarted⟩ := queue.batchesStarted_cons batch rest started
      intro block member
      rcases List.mem_append.mp member with first | later
      · exact queue.sourceBatchBlocks_itemValues publisher batch accepted block first
      · apply ih _ _ ?_ block later
        rwa [(queue.sourceBatchBlocks_agrees publisher batch).1]

-----------------------------------------------------------------------------------------
-- Earlier handler items fit strictly before every atom of the current handler
-----------------------------------------------------------------------------------------

/-- Concatenated exact block projections retain the entire ordered source item inventory.
Witness: list induction concatenates each label's projection, including silent blocks.
-/
theorem sourceBlocks_itemValues {blocks : List SourceOutputBlock}
    (exactItems
      : ∀ block ∈ blocks,
          block.2.flatMap normalizedItemValues
          = (block.1.toList.flatMap GraphEvent.itemPublications).map Prod.snd)
    : (blocks.flatMap Prod.snd).flatMap normalizedItemValues
      = ((blocks.filterMap Prod.fst).flatMap GraphEvent.itemPublications).map
          Prod.snd := by
  induction blocks with
  | nil => rfl
  | cons block rest ih =>
      rw [List.flatMap_cons, List.flatMap_append,
        exactItems block List.mem_cons_self,
        ih (fun next member => exactItems next (List.mem_cons_of_mem _ member))]
      cases source : block.1 <;>
        simp [source, List.flatMap_cons, List.map_append]

/-- Before an atom, all items from strictly earlier handlers have already been emitted.
Witness: their exact item count equals the preceding blocks' output count, and that
output is a prefix of the atom's strict prefix. No item payload identifies an occurrence.
-/
theorem sourceBlocks_earlierItemCount {blocks before after : List SourceOutputBlock}
    {block : SourceOutputBlock} {index localIndex : Nat}
    (exactItems
      : ∀ current ∈ blocks,
          current.2.flatMap normalizedItemValues
          = (current.1.toList.flatMap GraphEvent.itemPublications).map Prod.snd)
    (split : blocks = before ++ block :: after)
    (position : index = (before.flatMap Prod.snd).length + localIndex)
    : ((before.filterMap Prod.fst).flatMap GraphEvent.itemPublications).length
      ≤ (((blocks.flatMap Prod.snd).take index).flatMap normalizedItemValues).length := by
  have earlier := sourceBlocks_itemValues (blocks := before)
    (fun current member => exactItems current (split ▸ List.mem_append_left _ member))
  have lengths := congrArg List.length earlier
  simp only [List.length_map] at lengths
  rw [← lengths, split, List.flatMap_append, position, List.take_append,
    List.take_of_length_le (Nat.le_add_right _ _), List.flatMap_append, List.length_append]
  exact Nat.le_add_right _ _

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
