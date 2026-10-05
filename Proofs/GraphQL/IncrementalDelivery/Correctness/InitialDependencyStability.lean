import Proofs.GraphQL.IncrementalDelivery.Correctness.AnnouncedDependencyStability

/-! Initial group notices and carried notices provide stable full defer dependencies. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open Semantics.Ancestry Semantics.GeneralScheduling
open WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Initial notices cannot depend on represented deferred work
-----------------------------------------------------------------------------------------

/-- An initially announced group has no represented defer dependency.
Witness: empty-prefix satisfaction cannot complete a node or account for any represented
group task. Ref roles exclude empty stream descriptors from satisfying a defer dependency.
Unused syntax refs may remain in ancestry, but cannot later become represented work.
-/
theorem Initializes.initial_group_dependencies_absent
    {ancestry bound roles work groups streams node dependencies producer}
    (coherent : MixedRefs.WorkAt ancestry 0 bound work)
    (roleCoherent : RefRoles.WorkRoles roles work)
    (initialized : Initializes work groups streams)
    (known : NodeAt work node .group dependencies producer)
    (notice : node ∈ groups)
    : ∀ ref ∈ dependencies, ¬∃ birth, NodeHasProducer work ref birth := by
  obtain ⟨parents, source, descriptor, eligible⟩ := initialized.1.2.1 node notice
  have accounting (ref) (satisfied : DependencySatisfied work []
      (fun _ => .executionGroup []) [] [] ref)
      : NodeAccounted work (fun _ => .executionGroup []) [] [] ref := by
    rcases satisfied.2 with absent | closed | ⟨_, accounted⟩
    · intro occurrence owners ⟨birth, payload, task⟩ member
      obtain ⟨owner, kind, deps, producer, represented, same⟩ := task.owner_known member
      exact False.elim (absent ⟨producer, owner, kind, deps, represented, same⟩)
    · simp [completedRefs] at closed
    · exact accounted
  have sameParents : parents = dependencies := by
    rw [DeferOnly.node_dependencies coherent descriptor,
      DeferOnly.node_dependencies coherent known]
  intro ref member represented
  have satisfied := eligible.2.2.2 ref (sameParents ▸ member)
  rcases represented with ⟨birth, owner, kind, deps, ownerKnown, sameRef⟩
  cases kind with
  | stream =>
      have role := node_ref_role roleCoherent ownerKnown
      rw [sameRef, group_dependency_role roleCoherent known member] at role
      cases role
  | group =>
      obtain ⟨address, fragments, path, result, children, enclosing, fragment, located,
        selected, ownerEq, depsEq⟩ := ownerKnown
      have contributes : ref ∈ fragments.map (fun group => group.node.ref) :=
        List.mem_map.mpr ⟨fragment, selected,
          (congrArg DeliveryNode.ref ownerEq.symm).trans sameRef⟩
      have impossible := accounting ref satisfied (.executionGroup address) _
        ⟨birth, _, TaskAt.executionGroup located⟩ contributes
      simp [TaskAccounted, TaskCancelled, Published] at impossible

/-- Every dependency of any announced defer group remains healthy in the whole history.
Witness: initial notices depend only on absent work refs; carried notices use ordered
carrier stability. Coherent full ancestry handles repeated descriptors and shared owners.
This concerns group dependencies, not the health of the announced group itself.
-/
theorem Explains.announced_group_dependencies_stay_healthy
    {ancestry bound roles work groups streams events matching failures node dependencies
      producer}
    (valid : Valid ancestry bound) (coherent : MixedRefs.WorkAt ancestry 0 bound work)
    (roleCoherent : RefRoles.WorkRoles roles work)
    (explained : Explains work groups streams events matching failures)
    (known : NodeAt work node .group dependencies producer)
    (announced
      : node.ref ∈ announcedRefs ((groups ++ streams).map DeliveryNode.ref) events)
    : ∀ ref ∈ dependencies, ¬NodeFailed work matching events failures ref := by
  rcases List.mem_append.mp announced with initial | carried
  · obtain ⟨notice, member, same⟩ := List.mem_map.mp initial
    rcases List.mem_append.mp member with group | stream
    · obtain ⟨parents, source, descriptor, _⟩ := explained.1.1.2.1 notice group
      have equal : parents = dependencies := by
        rw [DeferOnly.node_dependencies coherent descriptor,
          DeferOnly.node_dependencies coherent known, same]
      intro ref member failed
      have absent := Initializes.initial_group_dependencies_absent coherent roleCoherent
        explained.1 descriptor group ref (equal ▸ member)
      obtain ⟨owner, kind, deps, birth, represented, sameRef⟩ :=
        Explains.failed_node_known explained failed
      exact absent ⟨birth, owner, kind, deps, represented, sameRef⟩
    · obtain ⟨parents, source, descriptor, _⟩ := explained.1.1.2.2 notice stream
      exact False.elim (stream_group_refs_distinct roleCoherent descriptor known same)
  · obtain ⟨event, member, notice⟩ := List.mem_flatMap.mp carried
    obtain ⟨index, selected⟩ := List.mem_iff_getElem?.mp member
    exact Explains.carried_group_notice_dependencies_stay_healthy valid coherent
      roleCoherent explained selected known notice

end GraphQL.IncrementalDelivery.Correctness
