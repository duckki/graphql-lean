import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SourceNoticeAncestorRetirements
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SuccessfulOwnerReplay

/-! Actual notice ancestors identify prior publication, exact storage or the incoming success. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- A structural notice-ancestor contributor has prior ledger output, exact storage or
this handler's incoming success. The same actual queue cut supplies the source, retirement,
noncancellation and owner metadata; no output-admission or replacement matching is assumed. -/
theorem OwnerPublicationFrame.noticeAncestor_contributor_accounted
    {queue work parents before published output child dependencies ref address owners
      producer payload}
    (frame : OwnerPublicationFrame queue work parents before published)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (event : GraphEvent) (valid : ValidGraphEvents work (before ++ [event]))
    (accepted : queue.acceptsGraphEvent event = true)
    (available : List (Occurrence × Nat))
    (licensed
      : ∀ occurrence errors,
          (occurrence, errors) ∈ available
          → (GraphEvent.taskFailure occurrence errors).MatchesWork work)
    (emitted : output ∈ (queue.handleGraphEvent event available).2.1)
    (noticed : child.ref ∈ rawGroupNoticeRefs output)
    (known : GroupRecordAt work child dependencies) (ancestor : ref ∈ dependencies)
    (task : TaskAt work (.executionGroup address) owners producer payload)
    (contributes : ref ∈ owners)
    : UncancelledRetirement (queue.handleGraphEvent event available).1 ref
      ∧ ∃ result,
          event = .taskSuccess (.executionGroup address) result
          ∨ (GraphEvent.taskSuccess (.executionGroup address) result ∈ before
              ∧ ((Occurrence.executionGroup address, result.value) ∈ published
                  ∨ ∃ node,
                      queue.taskNode? (.executionGroup address) = some node
                      ∧ node.value = some result.value
                      ∧ TaskHasOwners work (.executionGroup address)
                          (node.task.groups.map Execution.DeliveryNode.ref)
                      ∧ ref ∈ node.task.groups.map Execution.DeliveryNode.ref
                      ∧ ref
                        ∈ queue.groupNodes.map (fun owner => owner.group.node.ref))) := by
  have notices := frame.source.noticeAncestorRetirements generated canonical event valid
    available licensed
  have retired := notices child.ref (List.mem_flatMap.mpr ⟨output, emitted, noticed⟩)
    child dependencies known rfl ref ancestor (.executionGroup address) owners
    ⟨producer, payload, task⟩ contributes
  obtain ⟨result, succeeded⟩ := frame.source.noticeAncestor_structuralContributor_succeeded
    generated canonical event valid accepted available licensed emitted noticed known ancestor task
    contributes
  refine ⟨retired, result, ?_⟩
  rcases List.mem_append.mp succeeded with succeededBefore | current
  · apply Or.inr
    refine ⟨succeededBefore, ?_⟩
    have uncancelled : ref ∉ queue.cancelledGroups := fun member =>
      retired.uncancelled (queue.handleGraphEvent_cancelledGroups_subset event available member)
    rcases frame.accounted (.executionGroup address) result succeededBefore owners producer payload
        task ref
        contributes uncancelled with emittedBefore | ⟨node, found, stored, owns, live⟩
    · exact .inl emittedBefore
    · have lookup := State.taskNode?_some found
      obtain ⟨_, _, _, _, descriptor⟩ := (frame.source.pending.matching node.task
        (frame.source.pending.started node lookup.1)).1
      have sameOwners := (TaskAt.unique (lookup.2 ▸ descriptor) task).1
      exact .inr ⟨node, found, stored, sameOwners.symm ▸ ⟨producer, payload, task⟩, owns, live⟩
  · exact .inl (List.mem_singleton.mp current).symm

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
