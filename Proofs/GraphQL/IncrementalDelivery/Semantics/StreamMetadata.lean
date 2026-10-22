import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.StructuralEquivalence
import Proofs.GraphQL.IncrementalDelivery.Semantics.StreamAllocations

/-! Unique stream allocations identify structural descriptors and dependency metadata. -/

namespace GraphQL.IncrementalDelivery.Semantics.GeneralScheduling
open GraphQL.IncrementalDelivery
open GraphQL.IncrementalDelivery.Execution WorkQueueSemantics

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
    (items : List (Execution.TaskOutcome Execution.ResponseValue × Execution.Work))
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

/-- Duplicate-free allocation refs identify a single structural stream location. -/
theorem streamAddress_unique {work : Work}
    (allocated : (streamAllocationRefs work).Nodup)
    {left right first second firstItems secondItems firstProducer secondProducer
      firstOwners secondOwners}
    (firstAt : Located work left (.stream first firstItems) firstProducer firstOwners)
    (secondAt
      : Located work right (.stream second secondItems) secondProducer secondOwners)
    (sameRef : first.ref = second.ref)
    : left = right := by
  have unique : ((streamRefAddresses work []).map Prod.fst).Nodup := by
    rw [streamRefAddresses_refs]
    exact allocated
  obtain ⟨i, boundI, firstEntry⟩ := List.mem_iff_getElem.mp
    (Located.streamRefAddress_member firstAt)
  obtain ⟨j, boundJ, secondEntry⟩ := List.mem_iff_getElem.mp
    (Located.streamRefAddress_member secondAt)
  have equalIndex := unique.eq_of_getElem_eq
    (by simpa only [List.length_map] using boundI)
    (by simpa only [List.length_map] using boundJ)
    (by simpa only [List.getElem_map, firstEntry, secondEntry] using sameRef)
  subst j
  exact congrArg Prod.snd (firstEntry.symm.trans secondEntry)

/-- A unique stream ref has one dependency list and producer, even under item work. -/
theorem streamMetadata_unique {work : Work}
    (allocated : (streamAllocationRefs work).Nodup)
    {first second dependencies otherDependencies producer otherProducer}
    (firstAt : NodeAt work first .stream dependencies producer)
    (secondAt : NodeAt work second .stream otherDependencies otherProducer)
    (sameRef : first.ref = second.ref)
    : dependencies = otherDependencies ∧ producer = otherProducer := by
  obtain ⟨left, firstItems, firstAt⟩ := firstAt
  obtain ⟨right, secondItems, secondAt⟩ := secondAt
  have same := streamAddress_unique allocated firstAt secondAt sameRef
  subst right
  have equal := Option.some.inj (firstAt.symm.trans secondAt)
  simp only [WorkLocation.mk.injEq] at equal
  exact ⟨equal.2.2, equal.2.1⟩

end GraphQL.IncrementalDelivery.Semantics.GeneralScheduling
