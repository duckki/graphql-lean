import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupNoticeSafety

/-! Select a ready group descriptor without requiring every structural producer to publish. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Ancestor accounting and generated defer continuity select one ready descriptor
-----------------------------------------------------------------------------------------

/-- A satisfied dependency with a real contributor is accounted once healthy closures are.
Witness: absence contradicts the contributor's group descriptor; a completed dependency
uses the closure certificate, while silent completion already contains task accounting.
The closure premise is a proof obligation, not an added scheduler or source law.
-/
theorem DependencySatisfied.accounted_of_objectContributor
    {work initial matching events failures key address owners producer payload}
    (ready : DependencySatisfied work initial matching events failures key)
    (known : TaskAt work (.executionGroup address) owners producer payload)
    (contributes : key ∈ owners)
    (closed
      : key ∈ completedKeys events
        → ¬NodeFailed work matching events failures key
        → NodeAccounted work matching events failures key)
    : NodeAccounted work matching events failures key := by
  rcases ready.2 with absent | completed | ⟨_, accounted⟩
  · obtain ⟨node, dependencies, descriptor, same⟩ := known.executionGroup_owner contributes
    exact False.elim (absent ⟨producer, node, .group, dependencies, descriptor, same⟩)
  · exact closed completed ready.1
  · exact accounted

/-- A source-ready contributor supplies some ready descriptor for its shared group.
Witness: descend through object producers by strict dependency rank. Reusing the same
group selects the earlier contributor's descriptor; a strict ancestor is accounted and
healthy, so its successful source task must have published. Root descriptors stop the
descent, and item boundaries use their actual item-publication certificate. Group
producers need not be unique, and other retained producers may remain buffered.
-/
theorem ExecutedWork.groupNotice_readyDescriptor
    {work initial matching events failures received child dependencies address owners
      producer payload}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work received)
    (failedPayloads
      : ∀ cut occurrence,
          (cut, occurrence) ∈ failures
          → ∃ owners producer payload,
              TaskAt work occurrence owners producer payload
              ∧ payload.failure.isSome = true)
    (itemsSafe
      : ∀ source index,
          Occurrence.item source index ∈ received.flatMap GraphEvent.successes
          → ¬TaskCancelled work matching events failures (.item source index))
    (itemsPublished
      : ∀ source index,
          NodeAt work child .group dependencies (some (.item source index))
          → Occurrence.item source index ∈ received.flatMap GraphEvent.successes
          → Published matching events (.item source index))
    (dependenciesReady
      : ∀ key ∈ dependencies,
          DependencySatisfied work initial matching events failures key)
    (closed
      : ∀ key ∈ dependencies,
          key ∈ completedKeys events
          → ¬NodeFailed work matching events failures key
          → NodeAccounted work matching events failures key)
    (known : TaskAt work (.executionGroup address) owners producer payload)
    (contributes : child.key ∈ owners)
    (descriptor : NodeAt work child .group dependencies producer)
    (sourceReady
      : ∀ source, producer = some source → source ∈ received.flatMap GraphEvent.successes)
    : ∃ birth,
        NodeAt work child .group dependencies birth
        ∧ ∀ source, birth = some source → Published matching events source := by
  induction rank : (Occurrence.executionGroup address).dependencyRank
    using Nat.strongRecOn generalizing address owners producer payload with
  | ind rank ih =>
      cases producer with
      | none => exact ⟨none, descriptor, by intro source impossible; cases impossible⟩
      | some parent =>
          have succeeded := sourceReady parent rfl
          cases parent with
          | item source ordinal =>
              exact ⟨some (.item source ordinal), descriptor,
                fun _ same => Option.some.inj same ▸
                  itemsPublished source ordinal descriptor succeeded⟩
          | executionGroup source =>
              obtain ⟨lower, parentOwners, ancestor, value, parent⟩ := known.producer_dependency
              have parentReady : ∀ prior, ancestor = some prior
                  → prior ∈ received.flatMap GraphEvent.successes := by
                intro prior same
                subst ancestor
                exact valid.groupSettlement_producerBefore parent
                  (GraphEvent.successes_mem_settled succeeded)
              obtain ⟨supportOwners, supportBirth, supportValue, key,
                supportTask, member, support⟩ := generated.group_objectProducer_support descriptor
              have owner : key ∈ parentOwners := (supportTask.unique parent).1 ▸ member
              rcases support with reused | dependency
              · have contributor : child.key ∈ parentOwners := reused ▸ owner
                obtain ⟨node, parents, atParent, same⟩ := parent.executionGroup_owner contributor
                have nodeEq := generated.nodeKeyCoherent _ _ _ _ _ _ _ _
                  atParent descriptor same
                obtain ⟨assignment, canonical⟩ := generated.groupDependenciesCanonical
                have parentsEq : parents = dependencies := by
                  rw [canonical _ _ _ atParent, canonical _ _ _ descriptor, same]
                have nextDescriptor : NodeAt work child .group dependencies ancestor :=
                  nodeEq ▸ parentsEq ▸ atParent
                exact ih _ (by omega) parent contributor nextDescriptor parentReady rfl
              · have ready := dependenciesReady key dependency
                have accounted := DependencySatisfied.accounted_of_objectContributor
                  ready parent owner (closed key dependency)
                rcases accounted (.executionGroup source) parentOwners
                    ⟨ancestor, value, parent⟩ owner with cancelled | published
                · exact False.elim (ready.1
                    (generated.object_cancelled_owner_failed_of_itemSafety valid failedPayloads
                      itemsSafe parent owner parentReady cancelled))
                · exact ⟨some (.executionGroup source), descriptor,
                    fun _ same => Option.some.inj same ▸ published⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
