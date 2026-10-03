import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamNoticeEligibility
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamReleaseOwnerReplay

/-! Actual stream notice carriers need only their still-unproved freshness certificate. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- A group carrier closes a healthy dependency before releasing its child streams
-----------------------------------------------------------------------------------------

/-- A fresh stream notice on a group completion satisfies the complete eligibility rule.
Witness: the actual carrier is a contributing dependency, its successful closure is
healthy, and its stream producer has already published on the common matching. Only
freshness is supplied; health, producer readiness, and dependency satisfaction are derived.
-/
theorem groupStreamNotice_canAnnounce {work inputs w index group groups streams child}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (announced : AnnouncedFailures work w)
    (support : PublicationSupport work w.matching w.events w.failures)
    (healthy : GroupSuccessesHealthy work w) (producers : StreamNoticeProducers work w)
    (selected : w.events[index]? = some (.groupSuccess group groups streams))
    (noticed : child ∈ streams)
    (fresh : child.ref ∉ announcedRefs (initialRefs work) (w.events.take index))
    : ∃ dependencies producer,
        NodeAt work child .stream dependencies producer
        ∧ CanAnnounce work (initialRefs work) w.matching
            (w.events.take index ++ [.groupSuccess group [] []])
            (w.failures.filter (fun entry => decide (entry.1 ≤ index)))
            child .stream dependencies producer := by
  obtain ⟨dependencies, producer, located, published⟩ := producers.group selected noticed
  obtain ⟨atFull, _⟩ := Witness.canonical_event history selected
  obtain ⟨sourceIndex, atSource, _⟩ := publicationAtoms_groupSuccess_prefix _ atFull
  have contributes := createWorkQueue_runNormalized_streamReleaseDependencies generated inputs
    (fun _ member => valid.eachMatches member) group groups streams
    (List.mem_of_getElem? atSource) child noticed dependencies (some producer) located
  have length : (w.events.take index).length = index :=
    List.length_take_of_le (Nat.le_of_lt (List.getElem?_eq_some_iff.mp selected).1)
  have carrierHealth : ¬NodeFailed work w.matching
      (w.events.take index ++ [.groupSuccess group [] []])
      (w.failures.filter (fun entry => decide (entry.1 ≤ index))) group.ref := by
    have frozen :=
      causality_append_eq (work := work) (matching := w.matching)
        (events := w.events.take index)
        (failures := w.failures.filter (fun entry => decide (entry.1 ≤ index)))
        (by
          intro entry member; simpa only [length]
            using (of_decide_eq_true (List.mem_filter.mp member).2))
        [.groupSuccess group [] []]
    simpa only [frozen.1, nodeFailed_filter (Nat.le_of_eq length)]
      using healthy.atPrefix selected index
  refine ⟨dependencies, some producer, located,
    streamNotice_canAnnounce generated announced support selected Iff.rfl rfl located
      (published.append _) fresh (.inr ⟨group.ref, contributes, carrierHealth, ?_⟩)⟩
  exact .inr (.inl (by simp [completedRefs, eventCompleted]))

-----------------------------------------------------------------------------------------
-- Item carriers reset defer dependencies and may publish the producer themselves
-----------------------------------------------------------------------------------------

/-- A fresh stream notice on an item publication satisfies complete eligibility.
Witness: exact item-release metadata resets defer dependencies to empty; the retained
producer publication survives erasing the carrier's notices. Historical health follows
from announced-failure licensing and joint publication support, not future item success.
-/
theorem itemStreamNotice_canAnnounce
    {work inputs w index stream values groups streams child}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (announced : AnnouncedFailures work w)
    (support : PublicationSupport work w.matching w.events w.failures)
    (producers : StreamNoticeProducers work w)
    (selected : w.events[index]? = some (.streamValues stream values groups streams))
    (noticed : child ∈ streams)
    (fresh : child.ref ∉ announcedRefs (initialRefs work) (w.events.take index))
    : ∃ producer,
        NodeAt work child .stream [] producer
        ∧ CanAnnounce work (initialRefs work) w.matching
            (w.events.take index ++ [.streamValues stream values [] []])
            (w.failures.filter (fun entry => decide (entry.1 ≤ index)))
            child .stream [] producer := by
  obtain ⟨dependencies, producer, located, published⟩ := producers.item selected noticed
  obtain ⟨atFull, _⟩ := Witness.canonical_event history selected
  obtain ⟨other, empty, _⟩ :=
    (createWorkQueue_runNormalized_itemStreamReleasePublications valid started).publicationAtoms
      index stream values groups streams atFull child noticed
  have same := generated.streamDependencies_unique located empty rfl
  subst dependencies
  exact ⟨some producer, located,
    streamNotice_canAnnounce generated announced support selected Iff.rfl rfl located
      published fresh (.inl rfl)⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
