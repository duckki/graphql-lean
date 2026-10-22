import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupLeadingNoticeAncestors
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NoticeAncestorSemantics

/-! Successful startup ancestor publications exclude semantic failure at notice cuts. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

namespace ConformancePlan

/-- A group-success notice has semantically healthy defer ancestors at its strict prefix.
Witness: arbitrary-cut ancestor accounting at the empty failure list forces publication,
then supported ancestry excludes all failure causes. Failure payloads come from the
existing announced-failure certificate, not an added scheduler premise.
-/
theorem startup_groupNoticeAncestor_healthy
    {work inputs w index group groups streams child dependencies}
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
    (announced : AnnouncedFailures work w)
    (selected : w.events[index]? = some (.groupSuccess group groups streams))
    (noticed : child ∈ groups) (known : GroupRecordAt work child dependencies)
    : ∀ ref ∈ dependencies,
        ¬NodeFailed work w.matching (w.events.take index) w.failures ref := by
  apply generated.groupRecordAncestors_healthy_of_published known (support.take index)
    (fun cut occurrence member => (announced.1.2.2.1 (cut, occurrence) member).2.2)
  intro ref ancestor occurrence owners task contributes
  rcases startup_groupNoticeAncestor_nodeAccounted generated startup matched valid started
    history ledger selected
      noticed known ancestor [] occurrence owners task contributes with cancelled | published
  · obtain ⟨cut, member, _⟩ := cancelled
    cases member
  · exact published

/-- An item-carried group notice has semantically healthy defer ancestors before the item.
Witness: the leading-carrier accounting theorem forces all ancestor contributions into
the same strict prefix. Supported publication and generated chains rule out semantic
failure, even for silently pruned ancestors with no contributing descriptor.
-/
theorem startup_itemGroupNoticeAncestor_healthy
    {work inputs w index owner values groups streams child dependencies}
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
    (announced : AnnouncedFailures work w)
    (selected : w.events[index]? = some (.streamValues owner values groups streams))
    (noticed : child ∈ groups) (known : GroupRecordAt work child dependencies)
    : ∀ ref ∈ dependencies,
        ¬NodeFailed work w.matching (w.events.take index) w.failures ref := by
  apply generated.groupRecordAncestors_healthy_of_published known (support.take index)
    (fun cut occurrence member => (announced.1.2.2.1 (cut, occurrence) member).2.2)
  intro ref ancestor occurrence owners task contributes
  rcases startup_itemGroupNoticeAncestor_nodeAccounted generated startup matched valid started
    history ledger selected
      noticed known ancestor [] occurrence owners task contributes with cancelled | published
  · obtain ⟨cut, member, _⟩ := cancelled
    cases member
  · exact published

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
