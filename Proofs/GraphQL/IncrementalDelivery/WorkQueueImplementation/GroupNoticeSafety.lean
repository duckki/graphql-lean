import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupCarrierNoticeContents
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupNoticeEligibility
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ObjectProducerSafety

/-! Source-ready retained tasks give group notice contents without published producers. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Buffered object producers cannot silently cancel a healthy retained contributor
-----------------------------------------------------------------------------------------

/-- A healthy retained group has unaccounted work unless it carries a recorded failure.
Witness: sound retained membership supplies an original object task, and its registration
proves that its source producer succeeded. Generated defer continuity propagates object
producer cancellation to this owner; successful item safety stops that induction at item
boundaries. The contributor is therefore uncancelled and remains unpublished. Neither
the contributor nor its producer is required to have published already.
-/
theorem RetainedNoticeContents.recorded_or_unaccounted
    {work matching events failures received child}
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
    (healthy : ¬NodeFailed work matching events failures child.key)
    : HasRecordedFailure work failures events.length child.key
      ∨ ¬NodeAccounted work matching events failures child.key := by
  obtain ⟨_, queue, node, found, same, retained, sound, registered, cached,
    producers, unpublished⟩ := contents
  have member := List.mem_of_find?_eq_some found
  by_cases present : node.failure.isSome = true
  · left
    rw [← same]
    exact cached.recorded (List.Subset.refl _) member present
  · right
    intro accounted
    obtain ⟨occurrence, listed⟩ := List.exists_mem_of_ne_nil _ (retained.resolve_right present)
    obtain ⟨task, taskMember, sameTask, owner⟩ := sound node member occurrence listed
    obtain ⟨address, payload, producer, isObject, known⟩ := (registered task taskMember).1
    have contributes : child.key ∈ task.groups.map Execution.DeliveryNode.key := same ▸ owner
    rcases accounted task.occurrence _ ⟨producer, payload, known⟩ contributes with
      cancelled | published
    · apply healthy
      apply generated.object_cancelled_owner_failed_of_itemSafety valid failedPayloads itemsSafe
        (isObject ▸ known) contributes _ (isObject ▸ cancelled)
      intro source parent
      exact producers task taskMember source ⟨_, payload, parent ▸ known⟩
    · exact unpublished occurrence listed (sameTask ▸ published)

-----------------------------------------------------------------------------------------
-- The remaining notice obligations are descriptor readiness and freshness
-----------------------------------------------------------------------------------------

/-- Source-ready concrete contents meet the group eligibility test once its notice is ready.
Witness: recorded errors directly license the failure alternative. Otherwise producer and
ancestor readiness exclude node failure, and the retained-task theorem supplies genuinely
unaccounted work. No all-member producer-publication premise or admission premise remains.
-/
theorem RetainedNoticeContents.canAnnounce
    {work initial matching events failures received child dependencies producer}
    (contents
      : RetainedNoticeContents work matching events
          (failedBefore failures events.length) received child)
    (generated : ExecutedWork work) (valid : ValidGraphEvents work received)
    (support : PublicationSupport work matching events failures)
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
    (known : NodeAt work child .group dependencies producer)
    (fresh : child.key ∉ announcedKeys initial events)
    (produced : ∀ source, producer = some source → Published matching events source)
    (ready
      : ∀ key ∈ dependencies,
          DependencySatisfied work initial matching events failures key)
    : CanAnnounce work initial matching events failures child .group dependencies
        producer := by
  apply (groupNotice_canAnnounce_iff_contents generated support failedPayloads known
    produced ready).mpr
  refine ⟨fresh, ?_⟩
  classical
  by_cases recorded : HasRecordedFailure work failures events.length child.key
  · exact .inr recorded
  · have healthy : ¬NodeFailed work matching events failures child.key := by
      intro failed
      rcases support.groupFailure_causes generated failedPayloads known produced failed with
        ⟨occurrence, owners, task, owner, member⟩ | ⟨key, member, ancestor⟩
      · exact recorded ⟨occurrence, owners, member, task, owner⟩
      · exact (ready key member).1 ancestor
    exact .inl ((contents.recorded_or_unaccounted generated valid failedPayloads itemsSafe
      healthy).resolve_left recorded)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
