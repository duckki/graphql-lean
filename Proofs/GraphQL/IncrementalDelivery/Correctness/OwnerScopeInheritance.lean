import Proofs.GraphQL.IncrementalDelivery.Correctness.WorkMetadata
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.TerminalReporting

/-! An owner's full defer ancestors also bound its task's response attachment. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Canonical ancestor refs select the descriptor already in the task's defer map
-----------------------------------------------------------------------------------------

/-- A contributing group's ancestor scope contains the task's attachment.
Witness: canonical ancestor refs identify a descriptor in the task's own defer map;
coherent path assignment identifies it with the supplied closing node. This does not
assume that the task or its contributing group was announced.
-/
theorem workAt_owner_ancestor_prefix
    {paths bound work address owners producer payload owner dependencies birth
      ancestor ancestorKind ancestorDependencies ancestorBirth}
    {parents : NodeRef → NodeRefs}
    (coherent : MixedOwnerPaths.WorkAt paths bound work)
    (canonical
      : ∀ node dependencies producer,
          NodeAt work node .group dependencies producer → dependencies = parents node.ref)
    (known : TaskAt work (.executionGroup address) owners producer payload)
    (ownerKnown : NodeAt work owner .group dependencies birth)
    (contributes : owner.ref ∈ owners)
    (ancestorKnown : NodeAt work ancestor ancestorKind ancestorDependencies ancestorBirth)
    (above : ancestor.ref ∈ dependencies)
    : ancestor.path.IsPrefix payload.path := by
  cases StructuralEquivalence.taskAt_of_current known with
  | executionGroup located =>
      obtain ⟨fragment, member, sameRef⟩ := List.mem_map.mp contributes
      have fragmentKnown := NodeAt.group located.toCurrent member
      have sameDependencies : dependencies = fragment.ancestors.map DeliveryNode.ref := by
        rw [canonical _ _ _ ownerKnown, canonical _ _ _ fragmentKnown, sameRef]
      rw [sameDependencies] at above
      obtain ⟨descriptor, ancestorMember, descriptorRef⟩ := List.mem_map.mp above
      have localWork := workAt_located coherent located.toCurrent
      rw [MixedOwnerPaths.WorkAt] at localWork
      have included : descriptor ∈ OwnerPaths.mapNodes _ :=
        List.mem_flatMap.mpr ⟨fragment, member,
          List.mem_cons_of_mem _ ancestorMember⟩
      obtain ⟨assigned, below⟩ := localWork.1 descriptor included
      have samePath : ancestor.path = descriptor.path :=
        (workAt_node coherent ancestorKnown).2.symm.trans (descriptorRef ▸ assigned.2)
      obtain ⟨suffix, attachment⟩ := below
      exact ⟨suffix, by simpa only [Payload.path, samePath] using attachment.symm⟩

/-- An owner's actual report covers the same task attachment even without a task notice.
Witness: direct contributing-owner path coherence and failure-scope prefix transitivity.
-/
theorem reported_owner_covers_task
    {paths bound work occurrence owners producer payload owner kind dependencies birth
      events}
    (coherent : MixedOwnerPaths.WorkAt paths bound work)
    (known : TaskAt work occurrence owners producer payload)
    (ownerKnown : NodeAt work owner kind dependencies birth)
    (contributes : owner.ref ∈ owners)
    (reported : FailureReportedFor events owner.path)
    : FailureReportedFor events payload.path := by
  obtain ⟨suffix, equal⟩ := workAt_owner_prefix coherent known ownerKnown contributes
  have attachment : payloadPath payload = payload.path := by cases payload <;> rfl
  rw [attachment] at equal
  exact reported.descendant ⟨suffix, equal.symm⟩

/-- A reported ancestor of a contributing group covers its task's attachment.
Witness: the task's generated defer-map ancestor and the same positive-error completion.
No assumption about reporting all cancellations or closing the contributing group is used.
-/
theorem reported_owner_ancestor_covers_task
    {paths bound work address owners producer payload owner dependencies birth
      ancestor ancestorKind ancestorDependencies ancestorBirth events}
    {parents : NodeRef → NodeRefs}
    (coherent : MixedOwnerPaths.WorkAt paths bound work)
    (canonical
      : ∀ node dependencies producer,
          NodeAt work node .group dependencies producer → dependencies = parents node.ref)
    (known : TaskAt work (.executionGroup address) owners producer payload)
    (ownerKnown : NodeAt work owner .group dependencies birth)
    (contributes : owner.ref ∈ owners)
    (ancestorKnown : NodeAt work ancestor ancestorKind ancestorDependencies ancestorBirth)
    (above : ancestor.ref ∈ dependencies)
    (reported : FailureReportedFor events ancestor.path)
    : FailureReportedFor events payload.path :=
  reported.descendant
    (workAt_owner_ancestor_prefix coherent canonical known ownerKnown
      contributes ancestorKnown above)

end GraphQL.IncrementalDelivery.Correctness
