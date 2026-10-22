import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupNoticeAncestorCompletion
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupNoticeItemPublication
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupGroupNoticeFreshness
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupNoticeAdmission

/-! Actual startup group notices satisfy full eligibility from shared replay certificates. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Every actual carried group notice has ready dependencies on the canonical witness.
Witness: provenance identifies the announced descriptor, and generated ref coherence
identifies it with the supplied node. Both carrier forms derive complete ancestor readiness
from the same publication ledger and failure inventory, with no local status premise.
-/
theorem startup_groupNotice_dependenciesReady
    {work inputs index event child dependencies producer} {w : Witness}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (matched : startup.MatchesWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (history
      : w.events
        = ((State.initialize (Work.fromExecution work) startup)).nonterminalAtoms inputs)
    (ledger
      : BufferedClosureLedger work inputs w
          (State.initialize (Work.fromExecution work) startup))
    (support : PublicationSupport work w.matching w.events w.failures)
    (failures : AnnouncedFailures work w)
    (selected : w.events[index]? = some event)
    (noticed : child.ref ∈ groupNoticeRefs event)
    (known : NodeAt work child .group dependencies producer)
    : ∀ ref ∈ dependencies,
        DependencySatisfied work (initialRefs work) w.matching
          (w.events.take index ++ [withoutChildNotices event])
          (w.failures.filter (fun entry => entry.1 ≤ index)) ref := by
  have located := State.startup_runNormalized_atomicGroupNoticesLocated generated startup valid
    event
    (List.mem_of_getElem? (Witness.startup_event startup history selected).1)
  cases event <;> simp only [groupNoticeRefs] at noticed
  case groupSuccess group groups streams =>
    obtain ⟨actual, member, sameRef⟩ := List.mem_map.mp noticed
    obtain ⟨_, _, actualKnown⟩ := located actual member
    have same := generated.nodeRefCoherent _ _ _ _ _ _ _ _ actualKnown known sameRef
    subst actual
    exact startup_groupNoticeAncestor_dependencySatisfied generated startup matched valid started
      history ledger
      support failures selected member (groupRecordAt_of_nodeAt known)
  case streamValues owner values groups streams =>
    obtain ⟨actual, member, sameRef⟩ := List.mem_map.mp noticed
    obtain ⟨_, _, actualKnown⟩ := located actual member
    have same := generated.nodeRefCoherent _ _ _ _ _ _ _ _ actualKnown known sameRef
    subst actual
    exact startup_itemGroupNoticeAncestor_dependencySatisfied generated startup matched valid
      started history ledger
      support failures selected member (groupRecordAt_of_nodeAt known)
  all_goals cases noticed

/-- Actual retained group contents are eligible once freshness and dependencies are ready.
Witness: accepted cuts recover a source-ready contributor even for an error-only cache.
Rank descent selects a ready descriptor, using the canonical item-publication bridge and
healthy completed-ref accounting at the frozen carrier boundary. Retained memberships
remain unpublished there, giving the semantic contents alternative without assuming it.
Freshness and dependency readiness are the remaining implementation obligations; the
certificates here are independently derived on the same witness, not new source laws.
-/
theorem startup_groupNotice_canAnnounce
    {work inputs} {w : Witness} {index event child dependencies birth}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (matched : startup.MatchesWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (history
      : w.events
        = ((State.initialize (Work.fromExecution work) startup)).nonterminalAtoms inputs)
    (announced : AnnouncedFailures work w)
    (support : PublicationSupport work w.matching w.events w.failures)
    (safe : SuccessfulItemsSafe work inputs.flatten w)
    (groups : GroupSuccessesAccounted work w)
    (streams : StreamSuccessAdmission work w) (failures : FailureAdmission work w)
    (streamReady : StreamPublicationReady work w)
    (ledger
      : BufferedClosureLedger work inputs w
          (State.initialize (Work.fromExecution work) startup))
    (contents
      : RetainedNoticeContents work w.matching (w.events.take index)
          (failedBefore w.failures index) inputs.flatten child)
    (selected : w.events[index]? = some event)
    (noticed : child.ref ∈ groupNoticeRefs event)
    (known : NodeAt work child .group dependencies birth)
    : ∃ producer,
        NodeAt work child .group dependencies producer
        ∧ CanAnnounce work (initialRefs work) w.matching
            (w.events.take index ++ [withoutChildNotices event])
            (w.failures.filter (fun entry => entry.1 ≤ index))
            child .group dependencies producer := by
  have fresh := startup_groupNotice_fresh generated startup matched valid started history
    selected noticed known
  have ready := startup_groupNotice_dependenciesReady generated startup matched valid started
    history ledger support announced selected noticed known
  obtain ⟨address, owners, producer, payload, task, owner, sourceReady⟩ :=
    contents.sourceReadyContributor
  obtain ⟨node, parents, descriptor, same⟩ := task.executionGroup_owner owner
  have nodeEq := generated.nodeRefCoherent _ _ _ _ _ _ _ _ descriptor known same
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
    have published := w.startup_groupNotice_itemProducerPublished generated startup matched valid
      started history
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
  simpa only [announcedRefs, pendingRefs, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, (withoutChildNotices_projections event).2.1, List.nil_append,
    List.append_nil]
    using fresh

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
