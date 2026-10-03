import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.LeadingNoticeAncestors
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NoticeCarrierContext

/-! Successful ancestor accounting excludes semantic failure at the frozen notice cut. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Complete defer chains and supported publication supply semantic ancestor health
-----------------------------------------------------------------------------------------

/-- A supported published task has also published its structural producer, when present.
Witness: locate that exact publication, identify its unique structural descriptor, and
extend the producer's strict-prefix publication to the current history.
-/
theorem PublicationSupport.published_producer
    {work matching events failures occurrence owners producer payload}
    (support : PublicationSupport work matching events failures)
    (known : TaskAt work occurrence owners producer payload)
    (published : Published matching events occurrence)
    : ∀ source, producer = some source → Published matching events source := by
  obtain ⟨index, event, selected, value, same⟩ := published
  obtain ⟨otherOwners, otherProducer, otherPayload, _, descriptor, _, _, _, ready⟩ :=
    support index event selected value
  rw [same] at descriptor
  intro source produced
  obtain ⟨position, output, _, atOutput, isValue, matched⟩ :=
    (ready source ((descriptor.unique known).2.1.trans produced)).before
  exact ⟨position, output, atOutput, isValue, matched⟩

/-- Entirely published defer ancestry cannot be semantically failed.
Witness: recurse on strictly smaller ancestor refs. Real failures contradict supported
successful publication; dependency failure stays in the same full ancestry. Every group
producer comes from a published contributor and is therefore ready. Generated role
separation excludes stream rules, including for taskless ancestor-only records.
-/
theorem ExecutedWork.groupRecordAncestors_healthy_of_published
    {work child dependencies matching events failures}
    (generated : ExecutedWork work) (known : GroupRecordAt work child dependencies)
    (support : PublicationSupport work matching events failures)
    (failedPayloads
      : ∀ cut occurrence,
          (cut, occurrence) ∈ failures
          → ∃ owners producer payload,
              TaskAt work occurrence owners producer payload
              ∧ payload.failure.isSome = true)
    (published
      : ∀ ref ∈ dependencies,
          ∀ occurrence owners,
            TaskHasOwners work occurrence owners
            → ref ∈ owners
            → Published matching events occurrence)
    : ∀ ref ∈ dependencies, ¬NodeFailed work matching events failures ref := by
  intro ref
  induction ref using Nat.strongRecOn with
  | ind ref ih =>
      intro ancestor failure
      have snapshot := support.nodeFailed_snapshot failedPayloads failure
      cases snapshot with
      | task task owner failed =>
          exact support.failed_unpublished failedPayloads failed
            (published ref ancestor _ _ task owner)
      | @groupDependency _ parents parent descriptor member failed =>
          obtain ⟨node, birth, located, same⟩ := descriptor
          have included := generated.groupRecordAncestors_trans known
            (groupRecordAt_of_nodeAt located) (same ▸ ancestor)
          have smaller := generated.groupAncestorSmaller located member
          rw [same] at smaller
          exact ih parent smaller (included member)
            (support.snapshot_nodeFailed failedPayloads failed)
      | streamDependencies descriptor _ _ =>
          obtain ⟨stream, birth, located, same⟩ := descriptor
          exact generated.groupRecord_ancestor_ne_stream known ancestor located same.symm
      | producers descriptor noRoot unpublished _ =>
          obtain ⟨producer, node, kind, parents, located, same⟩ := descriptor
          cases kind with
          | stream =>
              exact generated.groupRecord_ancestor_ne_stream known ancestor located same.symm
          | group =>
              obtain ⟨occurrence, owners, payload, task, owner⟩ := located.group_task
              have value := published ref ancestor occurrence owners ⟨_, _, task⟩ (same ▸ owner)
              cases producer with
              | none => exact noRoot ⟨node, .group, parents, located, same⟩
              | some source =>
                  exact unpublished source ⟨node, .group, parents, located, same⟩
                    (support.published_producer task value source rfl)

-----------------------------------------------------------------------------------------
-- Both real carrier forms instantiate health on the one canonical matching
-----------------------------------------------------------------------------------------

namespace ConformancePlan

/-- A group-success notice has semantically healthy defer ancestors at its strict prefix.
Witness: arbitrary-cut ancestor accounting at the empty failure list forces publication,
then supported ancestry excludes all failure causes. Failure payloads come from the
existing announced-failure certificate, not an added scheduler premise.
-/
theorem groupNoticeAncestor_healthy
    {work inputs w index group groups streams child dependencies}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (ledger : BufferedClosureLedger work inputs w)
    (support : PublicationSupport work w.matching w.events w.failures)
    (announced : AnnouncedFailures work w)
    (selected : w.events[index]? = some (.groupSuccess group groups streams))
    (noticed : child ∈ groups) (known : GroupRecordAt work child dependencies)
    : ∀ ref ∈ dependencies,
        ¬NodeFailed work w.matching (w.events.take index) w.failures ref := by
  apply generated.groupRecordAncestors_healthy_of_published known (support.take index)
    (fun cut occurrence member => (announced.1.2.2.1 (cut, occurrence) member).2.2)
  intro ref ancestor occurrence owners task contributes
  rcases groupNoticeAncestor_nodeAccounted generated valid started history ledger selected
      noticed known ancestor [] occurrence owners task contributes with cancelled | published
  · obtain ⟨cut, member, _⟩ := cancelled
    cases member
  · exact published

/-- An item-carried group notice has semantically healthy defer ancestors before the item.
Witness: the leading-carrier accounting theorem forces all ancestor contributions into
the same strict prefix. Supported publication and generated chains rule out semantic
failure, even for silently pruned ancestors with no contributing descriptor.
-/
theorem itemGroupNoticeAncestor_healthy
    {work inputs w index owner values groups streams child dependencies}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (ledger : BufferedClosureLedger work inputs w)
    (support : PublicationSupport work w.matching w.events w.failures)
    (announced : AnnouncedFailures work w)
    (selected : w.events[index]? = some (.streamValues owner values groups streams))
    (noticed : child ∈ groups) (known : GroupRecordAt work child dependencies)
    : ∀ ref ∈ dependencies,
        ¬NodeFailed work w.matching (w.events.take index) w.failures ref := by
  apply generated.groupRecordAncestors_healthy_of_published known (support.take index)
    (fun cut occurrence member => (announced.1.2.2.1 (cut, occurrence) member).2.2)
  intro ref ancestor occurrence owners task contributes
  rcases itemGroupNoticeAncestor_nodeAccounted generated valid started history ledger selected
      noticed known ancestor [] occurrence owners task contributes with cancelled | published
  · obtain ⟨cut, member, _⟩ := cancelled
    cases member
  · exact published

/-- Strict-prefix health remains valid through a carrier with failures frozen at its start.
Witness: every retained cut is at or before the unchanged strict prefix. Appending the
notice-free carrier cannot expose a new failure cut, even when that carrier publishes.
-/
theorem healthy_noticeCarrier {work} {w : Witness} {index event ref}
    (selected : w.events[index]? = some event)
    (healthy : ¬NodeFailed work w.matching (w.events.take index) w.failures ref)
    : ¬NodeFailed work w.matching (w.events.take index ++ [withoutChildNotices event])
        (w.failures.filter (fun entry => entry.1 ≤ index)) ref := by
  have length : (w.events.take index).length = index :=
    List.length_take_of_le (Nat.le_of_lt (List.getElem?_eq_some_iff.mp selected).1)
  have frozen := causality_append_eq (work := work) (matching := w.matching)
    (events := w.events.take index)
    (failures := w.failures.filter (fun entry => entry.1 ≤ index))
    (by
      intro entry member
      simpa only [length] using of_decide_eq_true (List.mem_filter.mp member).2)
    [withoutChildNotices event]
  simpa only [frozen.1, nodeFailed_filter (Nat.le_of_eq length)] using healthy

/-- Healthy accounted ancestry is ready unless an earlier announcement remains open.
Witness: freeze causal health at the carrier start and retain existing task accounting.
The status alternative is deliberately explicit: proving it from concrete queue replay
is the remaining dependency-readiness obligation, not a new host-source assumption.
-/
theorem dependencySatisfied_noticeCarrier_of_status
    {work} {w : Witness} {index event ref}
    (selected : w.events[index]? = some event)
    (healthy : ¬NodeFailed work w.matching (w.events.take index) w.failures ref)
    (accounted
      : NodeAccounted work w.matching (w.events.take index)
          (w.failures.filter (fun entry => entry.1 ≤ index)) ref)
    (status
      : ref ∈ completedRefs (w.events.take index ++ [withoutChildNotices event])
        ∨ ref ∉ announcedRefs (initialRefs work) (w.events.take index))
    : DependencySatisfied work (initialRefs work) w.matching
        (w.events.take index ++ [withoutChildNotices event])
        (w.failures.filter (fun entry => entry.1 ≤ index)) ref := by
  refine ⟨healthy_noticeCarrier selected healthy, .inr ?_⟩
  rcases status with closed | unannounced
  · exact .inl closed
  · refine .inr ⟨?_, accounted.append _⟩
    simpa only [announcedRefs, pendingRefs, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, (withoutChildNotices_projections event).2.1,
      List.nil_append, List.append_nil] using unannounced

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
