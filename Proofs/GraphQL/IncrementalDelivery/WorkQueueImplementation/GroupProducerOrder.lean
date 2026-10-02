import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskProducerOrder
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PublicationInventory

/-! Exact successful flush labels preserve structural producer ordering. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Dropping unresolved nodes does not change the order of stored publications
-----------------------------------------------------------------------------------------

/-- Stored publication labels retain their occurrence order in the selected task nodes.
Witness: nodes without values are omitted; nodes with values keep their original labels.
-/
theorem storedPublications_occurrences_sublist (nodes : List TaskNode)
    : ((storedPublications nodes).map Prod.fst).Sublist
        (nodes.map (fun node => node.task.occurrence)) := by
  induction nodes with
  | nil => exact .refl _
  | cons node rest ih =>
      cases value : node.value with
      | none =>
          simpa only [storedPublications, List.filterMap_cons, value, Option.map_none,
            List.map_cons] using ih.cons node.task.occurrence
      | some data =>
          simpa only [storedPublications, List.filterMap_cons, value, Option.map_some,
            List.map_cons] using ih.cons_cons node.task.occurrence

/-- A successful flush has one exact fresh publication ledger in producer order.
Witness: the complete executable selection is a subsequence of the ordered group list
and permanent registry. Filtering absent values preserves that order; the same selection
extends the supplied publication inventory and covers every stored membership.
-/
theorem State.PublicationInventory.finishGroupSuccess_producerOrder {queue : State}
    {work property published} (inventory : queue.PublicationInventory property published)
    (memberships : queue.GroupMembershipOrder)
    (ordered : ProducerOrder work (queue.tasks.map Task.occurrence))
    (group : GroupNode) (live : group ∈ queue.groupNodes)
    : ∃ added : List ObjectPublication,
        added.map Prod.snd
          = (queue.finishGroupSuccess group).2.1.flatMap WorkQueueEvent.objectValues
        ∧ (queue.finishGroupSuccess group).1.PublicationInventory property
            (published ++ added)
        ∧ ProducerOrder work (added.map Prod.fst)
        ∧ (∀ occurrence ∈ group.tasks,
            ∀ node value,
              queue.taskNode? occurrence = some node
              → node.value = some value
              → (occurrence, value) ∈ added) := by
  obtain ⟨selected, unique, known, events, retained, absent, _, covered, subsequence⟩ :=
    queue.finishGroupSuccess_completeSelection group
  obtain ⟨values, final⟩ := inventory.finishGroupSuccess_selected group selected unique known
    events retained absent
  refine ⟨storedPublications selected, values, final,
    ordered.sublist ((storedPublications_occurrences_sublist selected).trans
      (subsequence.trans (memberships group live))), ?_⟩
  intro occurrence member node value found stored
  exact List.mem_filterMap.mpr
    ⟨
      node,
      covered occurrence member node found,
      by simp only [stored, Option.map_some, (State.taskNode?_some found).2]
    ⟩

/-- Within a producer-ordered value block, any published object producer precedes its child.
Witness: find the producer's labelled index and use strict pairwise producer ordering.
Both payloads remain attached to their exact occurrence labels throughout the argument.
-/
theorem ProducerOrder.publication_before {work parent}
    {publications : List ObjectPublication} {childIndex : Nat} {child : ObjectPublication}
    (ordered : ProducerOrder work (publications.map Prod.fst))
    (childAt : publications[childIndex]? = some child)
    (known : TaskHasProducer work child.1 (some parent))
    (present : parent ∈ publications.map Prod.fst)
    : ∃ value, (parent, value) ∈ publications.take childIndex := by
  obtain ⟨entry, member, same⟩ := List.mem_map.mp present
  obtain ⟨index, selected⟩ := List.mem_iff_getElem?.mp member
  have parentAt : (publications.map Prod.fst)[index]? = some parent := by
    rw [List.getElem?_map, selected, Option.map_some, same]
  have earlier := ordered.producer_before
    (by rw [List.getElem?_map, childAt, Option.map_some]) parentAt known
  refine ⟨entry.2, ?_⟩
  have entryEq : (parent, entry.2) = entry := by cases entry; simp_all
  rw [entryEq]
  apply List.mem_of_getElem? (i := index)
  rwa [List.getElem?_take_of_lt earlier]

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
