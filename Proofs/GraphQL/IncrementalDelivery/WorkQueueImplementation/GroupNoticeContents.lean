import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupNoticeEligibility
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.MembershipSoundness
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CachedFailures

/-! Reduce concrete notice contents to producer readiness, unpublished tasks, and caches. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Cancellation safety is derived, rather than assumed for each retained membership
-----------------------------------------------------------------------------------------

/-- A kept group record supplies the semantic reason for announcing its descriptor.
Witness: a cache supplies a recorded contributor failure. Otherwise a retained membership
has exact registered-task provenance; its healthy owner and ready producer exclude
cancellation, and the supplied publication exclusion makes that task unaccounted for.
The producer and publication-exclusion premises are local proof obligations to derive
at actual release boundaries, not changes to the host source or conformance contract.
-/
theorem State.groupNotice_canAnnounce_of_contents
    {queue : State} {work initial matching events failures node dependencies producer}
    (generated : ExecutedWork work)
    (support : PublicationSupport work matching events failures)
    (failedPayloads
      : ∀ cut occurrence,
          (cut, occurrence) ∈ failures
          → ∃ owners producer payload,
              TaskAt work occurrence owners producer payload
              ∧ payload.failure.isSome = true)
    (known : NodeAt work node.group.node .group dependencies producer)
    (member : node ∈ queue.groupNodes)
    (contents : node.tasks ≠ [] ∨ node.failure.isSome = true)
    (sound : queue.GroupMembershipSound) (registered : queue.RegisteredTasksMatch work)
    (cached : queue.CachedFailuresSupported work (failedBefore failures events.length))
    (fresh : node.group.node.ref ∉ announcedRefs initial events)
    (produced : ∀ source, producer = some source → Published matching events source)
    (ready
      : ∀ ref ∈ dependencies,
          DependencySatisfied work initial matching events failures ref)
    (memberProducers
      : ∀ occurrence ∈ node.tasks,
          ∀ source,
            TaskHasProducer work occurrence (some source)
            → Published matching events source)
    (unpublished : ∀ occurrence ∈ node.tasks, ¬Published matching events occurrence)
    : CanAnnounce work initial matching events failures node.group.node .group
        dependencies producer := by
  apply (groupNotice_canAnnounce_iff_contents generated support failedPayloads known
    produced ready).mpr
  refine ⟨fresh, ?_⟩
  classical
  by_cases recorded : HasRecordedFailure work failures events.length node.group.node.ref
  · exact .inr recorded
  have noCache : node.failure.isSome ≠ true := by
    intro hasCache
    obtain ⟨occurrence, failed, owners, task, owner⟩ := cached node member hasCache
    exact recorded ⟨occurrence, owners, failed, task, owner⟩
  have nonempty := contents.resolve_right noCache
  have healthy : ¬NodeFailed work matching events failures node.group.node.ref := by
    intro failed
    rcases support.groupFailure_causes generated failedPayloads known produced failed with
      ⟨occurrence, owners, task, owner, failed⟩ | ⟨ref, ancestor, failed⟩
    · exact recorded ⟨occurrence, owners, failed, task, owner⟩
    · exact (ready ref ancestor).1 failed
  left
  intro accounted
  cases members : node.tasks with
  | nil => exact nonempty members
  | cons occurrence rest =>
      have listed : occurrence ∈ node.tasks := by rw [members]; exact List.mem_cons_self
      obtain ⟨task, taskMember, same, owner⟩ := sound node member occurrence listed
      obtain ⟨_, payload, parent, _, descriptor⟩ := (registered task taskMember).1
      rw [same] at descriptor
      have uncancelled := support.pendingTask_not_cancelled failedPayloads descriptor owner
        healthy (fun source parentEq =>
          memberProducers occurrence listed source ⟨_, payload, parentEq ▸ descriptor⟩)
      exact (accounted occurrence _ ⟨parent, payload, descriptor⟩ owner).elim
        uncancelled (unpublished occurrence listed)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
