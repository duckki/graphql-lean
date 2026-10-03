import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamCompletionSource
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamSourceOrder

/-! A source stream success accounts for every structural item in that stream. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Generated stream refs identify precisely their own finite list of item tasks
-----------------------------------------------------------------------------------------

/-- Every task owning a generated stream ref is an item of that exact located stream.
Witness: generated role separation excludes object tasks; unique stream allocation refs
identify the item address, and deterministic location lookup identifies its finite list.
-/
theorem ExecutedWork.streamContributor_ordinal {work : Execution.Work}
    (generated : ExecutedWork work) {address stream entries producer dependencies}
    (located : Located work address (.stream stream entries) producer dependencies)
    {occurrence owners} (known : TaskHasOwners work occurrence owners)
    (owner : stream.ref ∈ owners)
    : ∃ ordinal, occurrence = .item address ordinal ∧ ordinal < entries.length := by
  obtain ⟨parent, payload, task⟩ := known
  cases occurrence with
  | executionGroup route =>
      obtain ⟨groups, path, result, children, enclosing, atTask, sameOwners, _⟩ := task
      rw [sameOwners] at owner
      obtain ⟨group, member, sameRef⟩ := List.mem_map.mp owner
      have groupKnown : NodeAt work group.node .group
          (group.ancestors.map Execution.DeliveryNode.ref) parent :=
        ⟨route, groups, path, result, children, enclosing, group, atTask, member, rfl, rfl⟩
      exact False.elim (generated.groupStreamRefsDisjoint groupKnown (.stream located) sameRef)
  | item route ordinal =>
      obtain ⟨node, items, enclosing, result, children, atTask, atItem, sameOwners, _⟩ := task
      rw [sameOwners] at owner
      have sameRef := List.mem_singleton.mp owner
      have sameAddress := generated.streamAddress_unique located atTask sameRef
      subst route
      have sameWork := congrArg WorkLocation.current (Option.some.inj (located.symm.trans atTask))
      have sameItems := (Execution.Work.stream.inj sameWork).2
      rw [← sameItems] at atItem
      exact ⟨ordinal, rfl, (List.getElem?_eq_some_iff.mp atItem).choose⟩

-----------------------------------------------------------------------------------------
-- Successful source completion follows every finite item arrival
-----------------------------------------------------------------------------------------

/-- A selected source event retains its valid earlier prefix and readiness at that prefix.
Witness: split the append-based source derivation at the event, retaining later inputs.
-/
theorem ValidGraphEvents.event_ready_context {work events}
    (valid : ValidGraphEvents work events) {event} (member : event ∈ events)
    : ∃ before after,
        events = before ++ event :: after
        ∧ ValidGraphEvents work before
        ∧ event.Ready work before := by
  induction valid with
  | nil => cases member
  | @append prior last valid matching fresh ready ih =>
      rcases List.mem_append.mp member with earlier | final
      · obtain ⟨before, after, same, validBefore, atEvent⟩ := ih earlier
        exact ⟨before, after ++ [last], by simp [same, List.append_assoc], validBefore, atEvent⟩
      · have same := List.mem_singleton.mp final
        subst event
        exact ⟨prior, [], by simp, valid, ready⟩

/-- A source stream success has received every item task contributing to its ref.
Witness: its readiness cursor equals the finite list length; the earlier source prefix
contains the complete contiguous ordinal range, embedded in the full item inventory.
This is received input accounting, not yet output publication before the completion.
-/
theorem ValidGraphEvents.streamSuccess_itemInventory {work events}
    (valid : ValidGraphEvents work events) (generated : ExecutedWork work) {stream}
    (completed : GraphEvent.streamSuccess stream ∈ events)
    : (∃ dependencies producer, NodeAt work stream .stream dependencies producer)
      ∧ ∀ occurrence owners,
          TaskHasOwners work occurrence owners
          → stream.ref ∈ owners
          → occurrence ∈ (events.flatMap GraphEvent.itemPublications).map Prod.fst := by
  obtain ⟨before, after, same, validBefore, ready⟩ := valid.event_ready_context completed
  obtain ⟨address, entries, producer, dependencies, located, _, count⟩ := ready
  refine ⟨⟨dependencies, producer, .stream located⟩, ?_⟩
  intro occurrence owners known owner
  obtain ⟨ordinal, equal, bound⟩ := generated.streamContributor_ordinal located known owner
  have received : occurrence ∈ (GraphEvent.itemsBefore before stream.ref).map
      StreamItem.occurrence := by
    rw [validBefore.itemsBefore_order generated located, count, equal]
    exact List.mem_map.mpr ⟨ordinal, List.mem_range.mpr bound, rfl⟩
  have inventory := (GraphEvent.itemsBefore_occurrences_sublist before stream.ref).subset received
  rw [same, List.flatMap_append, List.map_append]
  exact List.mem_append_left _ inventory

/-- Actual successful stream closure has the same complete source item inventory.
Witness: recover its exact source-success constructor before applying finite source accounting.
Failure closures cannot be mistaken for successful completion, even with zero error counts.
-/
theorem createWorkQueue_runNormalized_streamSuccess_itemInventory {work : Execution.Work}
    {batches : List (List GraphEvent)} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work batches.flatten) {stream}
    (completed
      : Execution.WorkQueueEvent.streamSuccess stream
        ∈ ((State.initialize (Work.fromExecution work)).runNormalized
            batches).2.flatten.flatMap
            publicationAtoms)
    : (∃ dependencies producer, NodeAt work stream .stream dependencies producer)
      ∧ ∀ occurrence owners,
          TaskHasOwners work occurrence owners
          → stream.ref ∈ owners
          → occurrence
            ∈ (batches.flatten.flatMap GraphEvent.itemPublications).map Prod.fst := by
  have source := createWorkQueue_runNormalized_streamCompletion_source
    (Work.fromExecution work) batches completed rfl
  exact valid.streamSuccess_itemInventory generated source

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
