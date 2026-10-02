import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NoticeCarrierContext
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NoticeContributorSources
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NoticeItemPublication

/-! Canonical group-notice eligibility reduces to freshness and dependency readiness. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- No producer, task-accounting, or error-cache premise is added to the host source
-----------------------------------------------------------------------------------------

/-- Actual retained group contents are eligible once freshness and dependencies are ready.
Witness: accepted cuts recover a source-ready contributor even for an error-only cache.
Rank descent selects a ready descriptor, using the canonical item-publication bridge and
healthy completed-key accounting at the frozen carrier boundary. Retained memberships
remain unpublished there, giving the semantic contents alternative without assuming it.
Freshness and dependency readiness are the remaining implementation obligations; the
certificates here are independently derived on the same witness, not new source laws.
-/
theorem groupNotice_canAnnounce_of_fresh_dependencies
    {work inputs} {w : Witness} {index event child dependencies birth streamCuts}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (announced : AnnouncedFailures work w)
    (support : PublicationSupport work w.matching w.events w.failures)
    (safe : SuccessfulItemsSafe work inputs.flatten w)
    (groups : GroupSuccessesAccounted work w)
    (streams : StreamSuccessAdmission work w) (failures : FailureAdmission work w)
    (streamReady : StreamPublicationReady work w)
    (ledger : BufferedClosureLedger work inputs w)
    (cuts
      : StreamFailureCuts work
          (((initialQueue work).runNormalized inputs).2.flatten.flatMap publicationAtoms)
          streamCuts)
    (partition
      : let queue := initialQueue work
        let publisher : IncrementalPublisher :=
          { active := queue.initialGroups ++ queue.initialStreams }
        w.failures.Perm
          (streamCuts
            ++ sourceObjectFailureCuts 0
                (queue.eligibleFailureBlocks
                  (queue.sourceRunBlocks publisher inputs).2.2)))
    (contents
      : RetainedNoticeContents work w.matching (w.events.take index)
          (failedBefore w.failures index) inputs.flatten child)
    (selected : w.events[index]? = some event)
    (noticed : child.key ∈ groupNoticeKeys event)
    (known : NodeAt work child .group dependencies birth)
    (fresh : child.key ∉ announcedKeys (initialKeys work) (w.events.take index))
    (ready
      : ∀ key ∈ dependencies,
          DependencySatisfied work (initialKeys work) w.matching
            (w.events.take index ++ [withoutChildNotices event])
            (w.failures.filter (fun entry => entry.1 ≤ index)) key)
    : ∃ producer,
        NodeAt work child .group dependencies producer
        ∧ CanAnnounce work (initialKeys work) w.matching
            (w.events.take index ++ [withoutChildNotices event])
            (w.failures.filter (fun entry => entry.1 ≤ index))
            child .group dependencies producer := by
  obtain ⟨address, owners, producer, payload, task, owner, sourceReady⟩ :=
    retainedNotice_sourceReadyContributor generated valid started cuts partition contents
  obtain ⟨node, parents, descriptor, same⟩ := task.executionGroup_owner owner
  have nodeEq := generated.nodeKeyCoherent _ _ _ _ _ _ _ _ descriptor known same
  obtain ⟨assignment, canonical⟩ := generated.groupDependenciesCanonical
  have parentsEq : parents = dependencies := by
    rw [canonical _ _ _ descriptor, canonical _ _ _ known, same]
  have sameValue := (withoutChildNotices_projections event).1
  obtain ⟨carrierSupport, itemSafety⟩ :=
    noticeCarrier_support_and_itemSafety support safe selected sameValue
  have failedPayloads : ∀ cut occurrence,
      (cut, occurrence) ∈ w.failures.filter (fun entry => entry.1 ≤ index)
      → ∃ owners producer payload,
          TaskAt work occurrence owners producer payload ∧ payload.failure.isSome = true := by
    intro cut occurrence member
    exact (announced.1.2.2.1 (cut, occurrence) (List.mem_filter.mp member).1).2.2
  have itemsPublished source ordinal
      (atItem : NodeAt work child .group dependencies (some (.item source ordinal)))
      (_ : Occurrence.item source ordinal ∈ inputs.flatten.flatMap GraphEvent.successes)
      : Published w.matching (w.events.take index ++ [withoutChildNotices event])
          (.item source ordinal) := by
    have published := w.groupNotice_itemProducerPublished generated valid started history
      ledger selected atItem noticed
    simpa only [List.take_add_one, selected, Option.toList_some,
      published_carrier_eq sameValue] using published
  obtain ⟨chosen, atChosen, produced⟩ := generated.groupNotice_readyDescriptor valid
    failedPayloads itemSafety itemsPublished ready
    (fun _ _ closed healthy => healthy_completed_accounted_noticeCarrier
      groups streams failures selected closed healthy)
    task owner (nodeEq ▸ parentsEq ▸ descriptor) sourceReady
  have retained := groupNotice_contents_atCarrier streamReady contents selected noticed
  refine ⟨chosen, atChosen, retained.canAnnounce generated valid carrierSupport
    failedPayloads itemSafety atChosen ?_ produced ready⟩
  simpa only [announcedKeys, pendingKeys, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, (withoutChildNotices_projections event).2.1, List.nil_append,
    List.append_nil]
    using fresh

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
