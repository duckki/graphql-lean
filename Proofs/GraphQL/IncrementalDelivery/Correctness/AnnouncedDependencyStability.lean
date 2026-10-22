import Proofs.GraphQL.IncrementalDelivery.Correctness.DeferredDependencyStability

/-! Emitted group notices preserve the health of their satisfied defer ancestry. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open Semantics.Ancestry Semantics.GeneralScheduling
open WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Eligibility at a real carrier supplies lasting dependency support
-----------------------------------------------------------------------------------------

/-- Dependencies of an eligible carried group notice remain healthy after that carrier.
Witness: notice eligibility supplies satisfied full ancestry before the next settlements.
Removing notices changes neither publications nor completions nor causal snapshots, so
healthy accounting transfers to the actual prefix. Ordered-boundary stability then excludes
both later direct settlements and inherited failure. No terminal or reporting law is used.
-/
theorem Explains.carried_group_dependencies_stay_healthy
    {ancestry bound roles work groups streams events matching failures index event plain
      node dependencies producer}
    (valid : Valid ancestry bound) (coherent : MixedRefs.WorkAt ancestry 0 bound work)
    (roleCoherent : RefRoles.WorkRoles roles work)
    (explained : Explains work groups streams events matching failures)
    (selected : events[index]? = some event)
    (sameValue : IsValue plain ↔ IsValue event)
    (sameCompleted : eventCompleted plain = eventCompleted event)
    (known : NodeAt work node .group dependencies producer)
    (eligible
      : CanAnnounce work ((groups ++ streams).map DeliveryNode.ref) matching
          (events.take index ++ [plain]) (failures.filter (fun entry => entry.1 ≤ index))
          node .group dependencies producer)
    : ∀ ref ∈ dependencies, ¬NodeFailed work matching events failures ref := by
  have shorter := explained.after_carrier_before_settlements selected
  have actual : events.take (index + 1) = events.take index ++ [event] := by
    rw [List.take_add_one, selected, Option.toList_some]
  have sameFailure := causality_carrier_eq (work := work) (matching := matching)
    (events := events.take index)
    (failures := failures.filter (fun entry => entry.1 ≤ index)) sameValue
  have samePublication : Published matching (events.take index ++ [plain])
      = Published matching (events.take index ++ [event]) := by
    funext occurrence
    apply propext
    simp only [published_append_singleton_iff, sameValue]
  have sameClosure : completedRefs (events.take index ++ [plain])
      = completedRefs (events.take index ++ [event]) := by
    simp only [completedRefs, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      sameCompleted]
  have supported (ref) (member : ref ∈ dependencies)
      : ¬NodeFailed work matching (events.take (index + 1))
            (failures.filter (fun entry => entry.1 ≤ index)) ref
          ∧ NodeAccounted work matching (events.take (index + 1))
              (failures.filter (fun entry => entry.1 ≤ index)) ref := by
    have satisfied := eligible.2.2.2 ref member
    have healthy : ¬NodeFailed work matching (events.take (index + 1))
        (failures.filter (fun entry => entry.1 ≤ index)) ref := by
      rw [actual, ← sameFailure.1]
      exact satisfied.1
    refine ⟨healthy, ?_⟩
    rcases satisfied.2 with absent | closed | ⟨_, accounted⟩
    · intro occurrence owners ⟨birth, payload, task⟩ contributes
      obtain ⟨owner, kind, parents, source, descriptor, same⟩ := task.owner_known contributes
      exact False.elim (absent ⟨source, owner, kind, parents, descriptor, same⟩)
    · rw [sameClosure, ← actual] at closed
      exact (shorter.completed_accounted closed).resolve_left healthy
    · simpa only [actual, NodeAccounted, TaskAccounted, sameFailure.2, samePublication]
        using accounted
  have full := DeferOnly.node_dependencies coherent known
  intro ref member
  have included := member
  rw [full] at included
  have smaller := valid node.ref (coherent_node_bounds coherent known).2 ref included
  apply Explains.supported_defer_dependency_stays_healthy_before_next_settlements
    valid coherent roleCoherent explained shorter (Nat.le_refl _)
    (group_dependency_role roleCoherent known member) (supported ref member)
  intro ancestor selected
  apply supported ancestor
  rw [full]
  exact smaller.2 selected

/-- Every defer dependency of an actually emitted group notice stays healthy thereafter.
Witness: invert its real stream-value or group-success carrier and use carried eligibility.
Role separation rules out mistaking a stream notice for a group with the same ref; generated
full ancestry identifies dependencies even when the group has repeated producer descriptors.
-/
theorem Explains.carried_group_notice_dependencies_stay_healthy
    {ancestry bound roles work groups streams events matching failures event node
      dependencies producer} {index : Nat}
    (valid : Valid ancestry bound) (coherent : MixedRefs.WorkAt ancestry 0 bound work)
    (roleCoherent : RefRoles.WorkRoles roles work)
    (explained : Explains work groups streams events matching failures)
    (selected : events[index]? = some event)
    (known : NodeAt work node .group dependencies producer)
    (noticed : node.ref ∈ eventPending event)
    : ∀ ref ∈ dependencies, ¬NodeFailed work matching events failures ref := by
  have carried {plain newGroups newStreams}
      (sameValue : IsValue plain ↔ IsValue event)
      (sameCompleted : eventCompleted plain = eventCompleted event)
      (notices : Announcements work ((groups ++ streams).map DeliveryNode.ref) matching
        (events.take index ++ [plain]) (failures.filter (fun entry => entry.1 ≤ index))
        newGroups newStreams)
      (present : node.ref ∈ (newGroups ++ newStreams).map DeliveryNode.ref)
      : ∀ ref ∈ dependencies, ¬NodeFailed work matching events failures ref := by
    obtain ⟨announced, member, same⟩ := List.mem_map.mp present
    rcases List.mem_append.mp member with group | stream
    · obtain ⟨parents, birth, descriptor, eligible⟩ := notices.2.1 announced group
      have sameParents : parents = dependencies := by
        rw [DeferOnly.node_dependencies coherent descriptor,
          DeferOnly.node_dependencies coherent known, same]
      rw [← sameParents]
      exact Explains.carried_group_dependencies_stay_healthy valid coherent roleCoherent
        explained selected sameValue sameCompleted descriptor eligible
    · obtain ⟨parents, birth, descriptor, _⟩ := notices.2.2 announced stream
      exact False.elim (stream_group_refs_distinct roleCoherent descriptor known same)
  have allowed := explained.eventAllowed index event selected
  simp only [EventAllowed,
    List.length_take_of_le (Nat.le_of_lt (List.getElem?_eq_some_iff.mp selected).1)] at allowed
  cases event <;> simp only [eventPending, List.not_mem_nil] at noticed
  all_goals try contradiction
  case groupSuccess carrier newGroups newStreams =>
    exact carried (plain := .groupSuccess carrier [] []) Iff.rfl rfl allowed.2.2.2.2 noticed
  case streamValues carrier values newGroups newStreams =>
    obtain ⟨owners, birth, value, _, _, _, _, notices⟩ := allowed
    exact carried (plain := .streamValues carrier values [] []) Iff.rfl rfl notices noticed

end GraphQL.IncrementalDelivery.Correctness
