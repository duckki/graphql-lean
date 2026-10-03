import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupNoticeProducers

/-! Both retained tasks and error-only caches supply a source-ready notice contributor. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- An actual group contributor cannot be a stream item
-----------------------------------------------------------------------------------------

/-- A task contributing to a generated group is an execution-group occurrence.
Witness: an item's only owner is its stream ref, disjoint from every generated group ref.
-/
theorem ExecutedWork.groupContributor_object
    {work child dependencies birth occurrence owners producer payload}
    (generated : ExecutedWork work)
    (group : NodeAt work child .group dependencies birth)
    (known : TaskAt work occurrence owners producer payload) (owner : child.ref ∈ owners)
    : ∃ address, occurrence = .executionGroup address := by
  cases occurrence with
  | executionGroup address => exact ⟨address, rfl⟩
  | item address ordinal =>
      obtain ⟨stream, items, enclosing, result, children, located, _, same, _⟩ := known
      have refEq : child.ref = stream.ref := by simpa only [same, List.mem_singleton] using owner
      exact False.elim
        (generated.groupStreamRefsDisjoint group ⟨address, items, located⟩ refEq)

-----------------------------------------------------------------------------------------
-- Cached failures retain their original source prerequisite after task removal
-----------------------------------------------------------------------------------------

/-- A retained notice has a source-ready object contributor even when its task list is empty.
Witness: nonempty memberships use permanent task registration. An error-only record uses
the contributing accepted failure, whose source-readiness bridge replaces the removed
membership. Generated role separation excludes stream items in either group inventory.
-/
theorem RetainedNoticeContents.sourceReadyContributor
    {work matching events failed received child}
    (contents : RetainedNoticeContents work matching events failed received child)
    (generated : ExecutedWork work)
    (failedReady
      : ∀ address owners producer payload,
          TaskAt work (.executionGroup address) owners producer payload
          → Occurrence.executionGroup address ∈ failed
          → ∀ source,
              producer = some source → source ∈ received.flatMap GraphEvent.successes)
    : ∃ address owners producer payload,
        TaskAt work (.executionGroup address) owners producer payload
        ∧ child.ref ∈ owners
        ∧ ∀ source,
            producer = some source → source ∈ received.flatMap GraphEvent.successes := by
  obtain ⟨⟨dependencies, birth, located⟩, queue, node, found, same, retained,
    sound, registered, cached, producers, _⟩ := contents
  have member := List.mem_of_find?_eq_some found
  by_cases hasTasks : node.tasks ≠ []
  · obtain ⟨occurrence, listed⟩ := List.exists_mem_of_ne_nil _ hasTasks
    obtain ⟨task, taskMember, _, owner⟩ := sound node member occurrence listed
    obtain ⟨address, payload, producer, isObject, known⟩ := (registered task taskMember).1
    refine ⟨address, _, producer, payload, isObject ▸ known, same ▸ owner, ?_⟩
    intro source parent
    exact producers task taskMember source ⟨_, payload, parent ▸ known⟩
  · obtain ⟨occurrence, failed, owners, ⟨producer, payload, known⟩, owner⟩ :=
      cached node member (retained.resolve_left hasTasks)
    have contributes : child.ref ∈ owners := same ▸ owner
    obtain ⟨address, rfl⟩ := generated.groupContributor_object located known contributes
    exact ⟨address, owners, producer, payload, known, contributes,
      failedReady address owners producer payload known failed⟩

/-- Concrete retained contents select a ready descriptor once causal dependencies are ready.
Witness: recover a source-ready contributor from live tasks or its accepted error cache,
identify the group's canonical dependencies, then descend through reused producers.
No separate readiness premise for all retained task producers is introduced.
-/
theorem RetainedNoticeContents.readyDescriptor
    {work initial matching events failures received child dependencies birth}
    (contents
      : RetainedNoticeContents work matching events
          (failedBefore failures events.length) received child)
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
    (failedReady
      : ∀ address owners producer payload,
          TaskAt work (.executionGroup address) owners producer payload
          → Occurrence.executionGroup address ∈ failedBefore failures events.length
          → ∀ source,
              producer = some source → source ∈ received.flatMap GraphEvent.successes)
    (known : NodeAt work child .group dependencies birth)
    (itemsPublished
      : ∀ source index,
          NodeAt work child .group dependencies (some (.item source index))
          → Occurrence.item source index ∈ received.flatMap GraphEvent.successes
          → Published matching events (.item source index))
    (ready
      : ∀ ref ∈ dependencies,
          DependencySatisfied work initial matching events failures ref)
    (closed
      : ∀ ref ∈ dependencies,
          ref ∈ completedRefs events
          → ¬NodeFailed work matching events failures ref
          → NodeAccounted work matching events failures ref)
    : ∃ producer,
        NodeAt work child .group dependencies producer
        ∧ ∀ source, producer = some source → Published matching events source := by
  obtain ⟨address, owners, producer, payload, task, owner, sourceReady⟩ :=
    contents.sourceReadyContributor generated failedReady
  obtain ⟨node, parents, descriptor, same⟩ := task.executionGroup_owner owner
  have nodeEq := generated.nodeRefCoherent _ _ _ _ _ _ _ _ descriptor known same
  obtain ⟨assignment, canonical⟩ := generated.groupDependenciesCanonical
  have parentsEq : parents = dependencies := by
    rw [canonical _ _ _ descriptor, canonical _ _ _ known, same]
  exact generated.groupNotice_readyDescriptor valid failedPayloads itemsSafe
    itemsPublished ready closed task owner (nodeEq ▸ parentsEq ▸ descriptor) sourceReady

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
