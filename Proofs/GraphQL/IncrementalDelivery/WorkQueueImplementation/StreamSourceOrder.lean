import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PublicationMatching
import Proofs.GraphQL.IncrementalDelivery.Semantics.ExecutedStreamAllocations

/-! Source stream cursors advance at one fixed structural address per generated ref. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics
open Semantics.GeneralScheduling

-----------------------------------------------------------------------------------------
-- A generated stream ref identifies its structural location
-----------------------------------------------------------------------------------------

/-- Existing stream allocations labelled by structural address, only for proof lookup.
The address parameter is the current subtree's absolute route, not a response path. -/
def streamRefAddresses (work : Execution.Work) (address : Address := [])
    : List (Nat × Address) :=
  match work with
  | .empty => []
  | .combine left right =>
      streamRefAddresses left (address ++ [0])
      ++ streamRefAddresses right (address ++ [1])
  | .executionGroup _ _ _ children => streamRefAddresses children (address ++ [0])
  | .stream node items =>
      (node.ref, address)
      :: items.zipIdx.attach.flatMap
          (fun entry => streamRefAddresses entry.val.1.2 (address ++ [entry.val.2]))
termination_by sizeOf work
decreasing_by
  all_goals subst_vars; simp_wf
  all_goals try decreasing_trivial
  have smaller := List.sizeOf_lt_of_mem (List.fst_mem_of_mem_zipIdx entry.property)
  rcases entry with ⟨⟨⟨result, children⟩, index⟩, member⟩
  simp only [Prod.mk.sizeOf_spec] at smaller
  dsimp only at *
  omega

/-- Stream enumeration uses ordinary indexed entries after erasing termination evidence.
Witness: discard the temporary membership proofs used in the structural recursion. -/
theorem streamRefAddresses_stream (node : Execution.DeliveryNode)
    (items : List (Execution.Result Execution.ResponseValue × Execution.Work))
    (address : Address)
    : streamRefAddresses (.stream node items) address
      = (node.ref, address)
        :: items.zipIdx.flatMap
            (fun entry => streamRefAddresses entry.1.2 (address ++ [entry.2])) := by
  rw [streamRefAddresses, List.flatMap_subtype
    (g := fun entry => streamRefAddresses entry.1.2 (address ++ [entry.2])) (fun _ _ => rfl)]
  simp

/-- Erasing address labels gives precisely the already-verified stream allocation list.
Witness: structural recursion and erasure of item indices. -/
theorem streamRefAddresses_refs (work : Execution.Work) (address : Address)
    : (streamRefAddresses work address).map Prod.fst = streamAllocationRefs work := by
  cases work with
  | empty => simp [streamRefAddresses, streamAllocationRefs]
  | combine left right =>
      simp only [streamRefAddresses, List.map_append, streamAllocationRefs]
      rw [streamRefAddresses_refs left, streamRefAddresses_refs right]
  | executionGroup groups path result children =>
      simpa only [streamRefAddresses, streamAllocationRefs]
        using streamRefAddresses_refs children (address ++ [0])
  | stream node items =>
      simp only [streamRefAddresses_stream, List.map_cons, List.map_flatMap]
      have erased : ∀ entry ∈ items.zipIdx,
          (streamRefAddresses entry.1.2 (address ++ [entry.2])).map Prod.fst =
            streamAllocationRefs entry.1.2 := by
        intro entry member
        exact streamRefAddresses_refs entry.1.2 _
      rw [List.flatMap_def, List.map_congr_left erased, ← List.flatMap_def]
      rw [← List.flatMap_map Prod.fst (fun entry => streamAllocationRefs entry.2) items.zipIdx,
        List.zipIdx_map_fst]
      rw [streamAllocationRefs]
termination_by sizeOf work
decreasing_by
  all_goals subst_vars; simp_wf
  all_goals try decreasing_trivial
  have smaller := List.sizeOf_lt_of_mem (List.fst_mem_of_mem_zipIdx member)
  rcases entry with ⟨⟨result, children⟩, index⟩
  simp only [Prod.mk.sizeOf_spec] at smaller
  dsimp only at *
  omega

/-- A located subtree's stream-address entries remain in the root enumeration.
Witness: structural navigation retains entries across combines, groups, and stream items.
-/
theorem Located.streamRefAddresses_subset {root address current producer owners}
    (located : Located root address current producer owners)
    : (streamRefAddresses current address).Subset (streamRefAddresses root []) := by
  have navigation := StructuralEquivalence.located_of_current located
  clear located
  induction navigation with
  | root => exact List.Subset.refl _
  | left _ ih =>
      rw [streamRefAddresses] at ih
      exact (List.subset_append_left _ _).trans ih
  | right _ ih =>
      rw [streamRefAddresses] at ih
      exact (List.subset_append_right _ _).trans ih
  | executionGroup _ ih => simpa only [streamRefAddresses] using ih
  | @item address node items producer owners index result children prior entry ih =>
      intro pair member
      apply ih
      rw [streamRefAddresses_stream]
      exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨((result, children), index),
        List.mk_mem_zipIdx_iff_getElem?.mpr entry, member⟩)

/-- A located stream contributes its own ref/address pair to the allocation enumeration.
Witness: its head allocation and structural inclusion in the root. -/
theorem Located.streamRefAddress_member {work address node items producer owners}
    (located : Located work address (.stream node items) producer owners)
    : (node.ref, address) ∈ streamRefAddresses work [] := by
  apply Located.streamRefAddresses_subset located
  rw [streamRefAddresses_stream]
  exact List.mem_cons_self

/-- Execution-generated stream refs are unique, including streams hidden under items.
Witness: the existing pure-execution stream-allocation theorem. -/
theorem ExecutedWork.streamRefsUnique {work : Execution.Work}
    (generated : ExecutedWork work)
    : (streamAllocationRefs work).Nodup := by
  obtain ⟨ObjectRef, schema, resolvers, variables, fuel, parentType, source,
    selections, same⟩ := generated
  exact same ▸ executeRoot_streamRefs_unique schema resolvers variables fuel parentType
    source selections 0

/-- Two generated stream descriptors sharing a ref have the same structural address.
Witness: their labelled allocation entries and duplicate-free allocated refs. -/
theorem ExecutedWork.streamAddress_unique {work : Execution.Work}
    (generated : ExecutedWork work)
    {left right first second firstItems secondItems firstProducer secondProducer
      firstOwners secondOwners}
    (firstAt : Located work left (.stream first firstItems) firstProducer firstOwners)
    (secondAt
      : Located work right (.stream second secondItems) secondProducer secondOwners)
    (sameRef : first.ref = second.ref)
    : left = right := by
  have unique : ((streamRefAddresses work []).map Prod.fst).Nodup := by
    rw [streamRefAddresses_refs]
    exact generated.streamRefsUnique
  obtain ⟨i, boundI, firstEntry⟩ := List.mem_iff_getElem.mp
    (Located.streamRefAddress_member firstAt)
  obtain ⟨j, boundJ, secondEntry⟩ := List.mem_iff_getElem.mp
    (Located.streamRefAddress_member secondAt)
  have equalIndex := unique.eq_of_getElem_eq
    (by simpa only [List.length_map] using boundI)
    (by simpa only [List.length_map] using boundJ)
    (by simpa only [List.getElem_map, firstEntry, secondEntry] using sameRef)
  subst j
  have same := firstEntry.symm.trans secondEntry
  exact congrArg Prod.snd same

-----------------------------------------------------------------------------------------
-- Existing source readiness makes each stream's received prefix a contiguous range
-----------------------------------------------------------------------------------------

/-- Items for a selected ref append across input prefixes without reordering.
Witness: the source's `flatMap` definition. -/
theorem GraphEvent.itemsBefore_append (before after : List GraphEvent) (ref : NodeRef)
    : GraphEvent.itemsBefore (before ++ after) ref
      = GraphEvent.itemsBefore before ref ++ GraphEvent.itemsBefore after ref := by
  simp only [GraphEvent.itemsBefore, List.flatMap_append]

/-- Every received prefix for a generated stream has indices zero through count minus one.
Witness: source readiness appends a contiguous range at the old count, and generated-ref
uniqueness keeps all arrivals at the same structural stream address. -/
theorem ValidGraphEvents.itemsBefore_order {work : Execution.Work}
    {events : List GraphEvent} (valid : ValidGraphEvents work events)
    (generated : ExecutedWork work) {address stream entries producer owners}
    (located : Located work address (.stream stream entries) producer owners)
    : (GraphEvent.itemsBefore events stream.ref).map StreamItem.occurrence
      = (List.range (GraphEvent.itemsBefore events stream.ref).length).map
          (Occurrence.item address) := by
  induction valid with
  | nil => rfl
  | @append before event valid matching fresh ready ih =>
      rw [GraphEvent.itemsBefore_append]
      cases event with
      | streamItems node items =>
          by_cases same : node.ref = stream.ref
          · obtain ⟨route, results, parent, dependencies, source, _, _, _, order⟩ := ready
            have routeSame := generated.streamAddress_unique source located same
            subst route
            simp only [GraphEvent.itemsBefore, List.flatMap_singleton, same, beq_self_eq_true,
              ite_true] at order ih ⊢
            simp only [List.map_append, List.length_append, List.range_add, List.map_append,
              List.map_map, Function.comp_def]
            rw [ih, order]
          · simpa [GraphEvent.itemsBefore, same] using ih
      | taskSuccess | taskFailure | streamSuccess | streamFailure =>
          simpa [GraphEvent.itemsBefore] using ih

-----------------------------------------------------------------------------------------
-- Earlier items occur before later items in the complete mixed source sequence
-----------------------------------------------------------------------------------------

/-- A single stream's received occurrences retain their order inside all item arrivals.
Witness: each source event either contributes its complete item list or contributes none.
-/
theorem GraphEvent.itemsBefore_occurrences_sublist (events : List GraphEvent)
    (ref : NodeRef)
    : ((GraphEvent.itemsBefore events ref).map StreamItem.occurrence).Sublist
        ((events.flatMap GraphEvent.itemPublications).map Prod.fst) := by
  have single (event : GraphEvent)
      : ((GraphEvent.itemsBefore [event] ref).map StreamItem.occurrence).Sublist
        (event.itemPublications.map Prod.fst) := by
    cases event <;> simp only [GraphEvent.itemsBefore, List.flatMap_singleton,
      GraphEvent.itemPublications, List.map_nil, List.map_map, Function.comp_def]
    · exact .refl []
    · exact .refl []
    · split
      · exact .refl _
      · exact List.nil_sublist _
    · exact .refl []
    · exact .refl []
  induction events with
  | nil => exact .refl []
  | cons event rest ih =>
      have splitItems : GraphEvent.itemsBefore (event :: rest) ref =
          GraphEvent.itemsBefore [event] ref ++ GraphEvent.itemsBefore rest ref := by
        exact GraphEvent.itemsBefore_append [event] rest ref
      rw [splitItems, List.map_append, List.flatMap_cons, List.map_append]
      exact (single event).append ih

/-- Two increasing indices form an ordered sublist of a finite range.
Witness: their increasing pair of valid range positions. -/
private theorem range_pair_sublist {first second count : Nat}
    (less : first < second) (bound : second < count)
    : [first, second].Sublist (List.range count) := by
  let indices : List (Fin (List.range count).length) :=
    [⟨first, by simpa using Nat.lt_trans less bound⟩, ⟨second, by simpa using bound⟩]
  have ordered : indices.Pairwise (· < ·) := by simpa [indices] using less
  simpa [indices] using List.map_getElem_sublist (l := List.range count) ordered

/-- Every earlier ordinal precedes a supplied item in the mixed source-item sequence.
Witness: locate the current item, use its stream's contiguous received range, then retain
the ordered pair while embedding that stream among all other source arrivals. -/
theorem ValidGraphEvents.earlier_item_sublist {work : Execution.Work}
    {events : List GraphEvent} (valid : ValidGraphEvents work events)
    (generated : ExecutedWork work) {address first second} (less : first < second)
    (current
      : .item address second ∈ (events.flatMap GraphEvent.itemPublications).map Prod.fst)
    : [Occurrence.item address first, .item address second].Sublist
        ((events.flatMap GraphEvent.itemPublications).map Prod.fst) := by
  obtain ⟨publication, publicationMember, sameOccurrence⟩ := List.mem_map.mp current
  obtain ⟨event, eventMember, inEvent⟩ := List.mem_flatMap.mp publicationMember
  have matching := valid.event_matches eventMember
  cases event with
  | taskSuccess | taskFailure | streamSuccess | streamFailure => cases inEvent
  | streamItems stream items =>
      obtain ⟨item, inItems, samePublication⟩ := List.mem_map.mp inEvent
      subst publication
      obtain ⟨owners, producer, known, _⟩ := matching item inItems
      change item.occurrence = .item address second at sameOccurrence
      rw [sameOccurrence] at known
      obtain ⟨node, results, enclosing, result, children, located, _, _, payload⟩ := known
      have sameNode := (Payload.item.inj payload).1
      subst node
      have received : item ∈ GraphEvent.itemsBefore events stream.ref := by
        apply List.mem_flatMap.mpr
        exact ⟨.streamItems stream items, eventMember, by simpa using inItems⟩
      have order := valid.itemsBefore_order generated located
      have member : .item address second ∈
          (GraphEvent.itemsBefore events stream.ref).map StreamItem.occurrence :=
        List.mem_map.mpr ⟨item, received, sameOccurrence⟩
      rw [order] at member
      obtain ⟨ordinal, inRange, sameItem⟩ := List.mem_map.mp member
      have ordinalSame := (Occurrence.item.inj sameItem).2
      subst ordinal
      have pair := (range_pair_sublist less (List.mem_range.mp inRange)).map
        (Occurrence.item address)
      have inStream : [Occurrence.item address first, .item address second].Sublist
          ((GraphEvent.itemsBefore events stream.ref).map StreamItem.occurrence) := by
        rw [order]
        exact pair
      exact inStream.trans (GraphEvent.itemsBefore_occurrences_sublist events stream.ref)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
