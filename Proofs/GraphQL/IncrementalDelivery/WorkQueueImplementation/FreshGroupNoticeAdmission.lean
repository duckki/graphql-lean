import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CanonicalNoticeCompletion
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupNoticeAdmission
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CanonicalGroupNoticeFreshness

/-! General carried group notices satisfy their complete scheduler eligibility rule. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Notice-ref lookup recovers the real descriptor before checking its entire ancestry
-----------------------------------------------------------------------------------------

/-- Every actual carried group notice has ready dependencies on the canonical witness.
Witness: provenance identifies the announced descriptor, and generated ref coherence
identifies it with the supplied node. Both carrier forms derive complete ancestor readiness
from the same publication ledger and failure inventory, with no local status premise.
-/
theorem groupNotice_dependenciesReady
    {work inputs index event child dependencies producer} {w : Witness}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (ledger : BufferedClosureLedger work inputs w)
    (support : PublicationSupport work w.matching w.events w.failures)
    (failures : AnnouncedFailures work w)
    (selected : w.events[index]? = some event)
    (noticed : child.ref ∈ groupNoticeRefs event)
    (known : NodeAt work child .group dependencies producer)
    : ∀ ref ∈ dependencies,
        DependencySatisfied work (initialRefs work) w.matching
          (w.events.take index ++ [withoutChildNotices event])
          (w.failures.filter (fun entry => entry.1 ≤ index)) ref := by
  have located := createWorkQueue_runNormalized_atomicGroupNoticesLocated generated valid event
    (List.mem_of_getElem? (Witness.canonical_event history selected).1)
  cases event <;> simp only [groupNoticeRefs] at noticed
  case groupSuccess group groups streams =>
    obtain ⟨actual, member, sameRef⟩ := List.mem_map.mp noticed
    obtain ⟨_, _, actualKnown⟩ := located actual member
    have same := generated.nodeRefCoherent _ _ _ _ _ _ _ _ actualKnown known sameRef
    subst actual
    exact groupNoticeAncestor_dependencySatisfied generated valid started history ledger
      support failures selected member (groupRecordAt_of_nodeAt known)
  case streamValues owner values groups streams =>
    obtain ⟨actual, member, sameRef⟩ := List.mem_map.mp noticed
    obtain ⟨_, _, actualKnown⟩ := located actual member
    have same := generated.nodeRefCoherent _ _ _ _ _ _ _ _ actualKnown known sameRef
    subst actual
    exact itemGroupNoticeAncestor_dependencySatisfied generated valid started history ledger
      support failures selected member (groupRecordAt_of_nodeAt known)
  all_goals cases noticed

-----------------------------------------------------------------------------------------
-- Producer choice, contents, errors, and dependencies are all derived rather than assumed
-----------------------------------------------------------------------------------------

/-- A fresh actual group notice satisfies its full scheduler eligibility rule.
Witness: the source-derived canonical dependency theorem discharges the last readiness
premise of descriptor selection. Retained contents, producer publication, cancellation
safety, and failure licensing use the existing shared certificates, not new host laws.
-/
theorem groupNotice_canAnnounce_of_fresh
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
    (noticed : child.ref ∈ groupNoticeRefs event)
    (known : NodeAt work child .group dependencies birth)
    (fresh : child.ref ∉ announcedRefs (initialRefs work) (w.events.take index))
    : ∃ producer,
        NodeAt work child .group dependencies producer
        ∧ CanAnnounce work (initialRefs work) w.matching
            (w.events.take index ++ [withoutChildNotices event])
            (w.failures.filter (fun entry => entry.1 ≤ index))
            child .group dependencies producer :=
  groupNotice_canAnnounce_of_fresh_dependencies generated valid started history announced
    support safe groups streams failures streamReady ledger cuts partition contents
    selected noticed known fresh
    (groupNotice_dependenciesReady generated valid started history ledger
      support announced selected noticed known)

/-- Every actual group notice satisfies complete eligibility on the shared canonical witness.
Witness: exact raw replay separation and group/stream role separation discharge freshness;
the existing contents, producer, dependency, and failure certificates discharge readiness.
No freshness or eligibility premise is added to the host-source contract.
-/
theorem groupNotice_canAnnounce
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
    (noticed : child.ref ∈ groupNoticeRefs event)
    (known : NodeAt work child .group dependencies birth)
    : ∃ producer,
        NodeAt work child .group dependencies producer
        ∧ CanAnnounce work (initialRefs work) w.matching
            (w.events.take index ++ [withoutChildNotices event])
            (w.failures.filter (fun entry => entry.1 ≤ index))
            child .group dependencies producer :=
  groupNotice_canAnnounce_of_fresh generated valid started history announced support safe
    groups streams failures streamReady ledger cuts partition contents selected noticed
    known (groupNotice_fresh generated valid started history selected noticed known)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
