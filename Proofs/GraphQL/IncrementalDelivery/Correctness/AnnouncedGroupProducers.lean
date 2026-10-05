import Proofs.GraphQL.IncrementalDelivery.Correctness.InitialDependencyStability

/-! Actual announcements retain an available group producer, despite repeated descriptors. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open Semantics.Ancestry Semantics.GeneralScheduling
open WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- An announcement witnesses an available producer descriptor
-----------------------------------------------------------------------------------------

/-- An announced group has a root or published producer descriptor with the same ref.
Witness: invert initial or carried notice eligibility. A carrier's notice-only changes
preserve publications, which remain present in the final history. No particular descriptor
is selected as primary, and alternative unpublished descriptors do not erase this witness.
-/
theorem Explains.announced_group_producer_available
    {roles work groups streams events matching failures node dependencies producer}
    (roleCoherent : RefRoles.WorkRoles roles work)
    (explained : Explains work groups streams events matching failures)
    (known : NodeAt work node .group dependencies producer)
    (announced
      : node.ref ∈ announcedRefs ((groups ++ streams).map DeliveryNode.ref) events)
    : ∃ owner parents birth,
        NodeAt work owner .group parents birth
        ∧ owner.ref = node.ref
        ∧ ∀ source, birth = some source → Published matching events source := by
  rcases List.mem_append.mp announced with initial | carried
  · obtain ⟨notice, member, same⟩ := List.mem_map.mp initial
    rcases List.mem_append.mp member with group | stream
    · obtain ⟨parents, source, descriptor, eligible⟩ := explained.1.1.2.1 notice group
      refine ⟨notice, parents, source, descriptor, same, ?_⟩
      intro occurrence birth
      have impossible := eligible.2.2.1 occurrence birth
      simp [Published] at impossible
    · obtain ⟨parents, source, descriptor, _⟩ := explained.1.1.2.2 notice stream
      exact False.elim (stream_group_refs_distinct roleCoherent descriptor known same)
  · obtain ⟨event, member, notice⟩ := List.mem_flatMap.mp carried
    obtain ⟨index, selected⟩ := List.mem_iff_getElem?.mp member
    have fromCarrier {plain newGroups newStreams}
        (sameValue : IsValue plain ↔ IsValue event)
        (notices : Announcements work ((groups ++ streams).map DeliveryNode.ref) matching
          (events.take index ++ [plain]) (failures.filter (fun entry => entry.1 ≤ index))
          newGroups newStreams)
        (present : node.ref ∈ (newGroups ++ newStreams).map DeliveryNode.ref)
        : ∃ owner parents birth,
            NodeAt work owner .group parents birth
            ∧ owner.ref = node.ref
            ∧ ∀ source, birth = some source → Published matching events source := by
      obtain ⟨owner, member, same⟩ := List.mem_map.mp present
      rcases List.mem_append.mp member with group | stream
      · obtain ⟨parents, birth, descriptor, eligible⟩ := notices.2.1 owner group
        refine ⟨owner, parents, birth, descriptor, same, ?_⟩
        intro occurrence generated
        have published := eligible.2.2.1 occurrence generated
        have actual : Published matching (events.take index ++ [event]) occurrence := by
          simpa only [published_append_singleton_iff, sameValue] using published
        have shorter : Published matching (events.take (index + 1)) occurrence := by
          simpa only [List.take_add_one, selected, Option.toList_some] using actual
        simpa only [List.take_append_drop] using shorter.append (events.drop (index + 1))
      · obtain ⟨parents, birth, descriptor, _⟩ := notices.2.2 owner stream
        exact False.elim (stream_group_refs_distinct roleCoherent descriptor known same)
    have allowed := explained.2.2 index event selected
    simp only [EventAllowed,
      List.length_take_of_le (Nat.le_of_lt (List.getElem?_eq_some_iff.mp selected).1)] at allowed
    cases event <;> simp only [eventPending, List.not_mem_nil] at notice
    all_goals try contradiction
    case groupSuccess carrier newGroups newStreams =>
      exact fromCarrier (plain := .groupSuccess carrier [] []) Iff.rfl allowed.2.2.2.2 notice
    case streamValues carrier values newGroups newStreams =>
      obtain ⟨owners, birth, value, _, _, _, _, notices⟩ := allowed
      exact fromCarrier (plain := .streamValues carrier values [] []) Iff.rfl notices notice

-----------------------------------------------------------------------------------------
-- Announced group failure requires a recorded contributor
-----------------------------------------------------------------------------------------

/-- An announced group is healthy when it has no recorded contributor failure.
Witness: its actual notice preserves an available producer and lasting healthy full defer
dependencies. Causal inversion leaves no remaining group failure origin. This excludes
zero-contribution failures only for announced groups, not arbitrary hidden descriptors.
-/
theorem Explains.announced_group_healthy_of_no_recorded_failure
    {ancestry bound roles work groups streams events matching failures node dependencies
      producer}
    (valid : Valid ancestry bound) (coherent : MixedRefs.WorkAt ancestry 0 bound work)
    (roleCoherent : RefRoles.WorkRoles roles work)
    (explained : Explains work groups streams events matching failures)
    (known : NodeAt work node .group dependencies producer)
    (announced
      : node.ref ∈ announcedRefs ((groups ++ streams).map DeliveryNode.ref) events)
    (noRecord : ¬HasRecordedFailure work failures events.length node.ref)
    : ¬NodeFailed work matching events failures node.ref := by
  obtain ⟨owner, parents, birth, descriptor, same, available⟩ :=
    Explains.announced_group_producer_available roleCoherent explained known announced
  have notice : owner.ref ∈ announcedRefs ((groups ++ streams).map DeliveryNode.ref) events :=
    same ▸ announced
  have healthy := Explains.group_healthy_of_no_recorded_failure coherent roleCoherent
    explained descriptor (by simpa only [same] using noRecord) available
    (Explains.announced_group_dependencies_stay_healthy valid coherent roleCoherent
      explained descriptor notice)
  simpa only [same] using healthy

end GraphQL.IncrementalDelivery.Correctness
