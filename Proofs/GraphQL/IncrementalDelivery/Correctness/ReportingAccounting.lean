import Proofs.GraphQL.IncrementalDelivery.Correctness.ReportingProgressEvents
import Proofs.GraphQL.IncrementalDelivery.Correctness.MixedOwnerSupport

/-! Construct mixed-work accounting while retaining observable report opportunities. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open Semantics.Ancestry Semantics.GeneralScheduling
open WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- A maximal reporting-aware history accounts for every task
-----------------------------------------------------------------------------------------

/-- A reporting-covered prefix extends to accounting with its reporting frontier intact.
Witness: maximize only extensions preserving healthy support and eligible failed groups.
Covering success carriers and the reporting-aware ready-task step contradict outstanding
work. Every healthy ref then satisfies its dependencies; observable failure scopes remain
a separate obligation, rather than following from accounting alone.
-/
theorem mixed_reporting_accounted_extension
    {ancestry bound roles paths pathBound work groups streams head matching failures}
    (valid : Valid ancestry bound) (coherent : MixedRefs.WorkAt ancestry 0 bound work)
    (roleCoherent : RefRoles.WorkRoles roles work)
    (continuous : DeferContinuous ancestry work) (ordered : StreamOwnersOrdered work)
    (pathCoherent : MixedOwnerPaths.WorkAt paths pathBound work)
    (initial : Explains work groups streams head matching failures)
    (coverage
      : ReportingNoticesCovered ancestry work ((groups ++ streams).map DeliveryNode.ref)
          matching head failures)
    : ∃ tail next cuts,
        Explains work groups streams (head ++ tail) next cuts
        ∧ ReportingNoticesCovered ancestry work ((groups ++ streams).map DeliveryNode.ref)
            next (head ++ tail) cuts
        ∧ (∀ occurrence owners producer payload,
            TaskAt work occurrence owners producer payload
            → TaskAccounted work next (head ++ tail) cuts occurrence)
        ∧ ∀ ref,
            ¬NodeFailed work next (head ++ tail) cuts ref
            → DependencySatisfied work ((groups ++ streams).map DeliveryNode.ref) next
                (head ++ tail) cuts ref := by
  classical
  obtain ⟨tail, matching, failures, explained, covered, maximal⟩ :=
    initial.maximal_extension_preserving
      (fun events matching failures => ReportingNoticesCovered ancestry work
        ((groups ++ streams).map DeliveryNode.ref) matching events failures)
      coverage
  generalize joined : head ++ tail = events at explained covered maximal
  have dependency {ref}
      (healthy : ¬NodeFailed work matching events failures ref)
      (accounted : NodeAccounted work matching events failures ref)
      : DependencySatisfied work ((groups ++ streams).map DeliveryNode.ref) matching events
          failures ref := by
    refine ⟨healthy, ?_⟩
    by_cases supported : ∃ birth, NodeHasProducer work ref birth
    · by_cases announced :
        ref ∈ announcedRefs ((groups ++ streams).map DeliveryNode.ref) events
      · by_cases completed : ref ∈ completedRefs events
        · exact Or.inr (Or.inl completed)
        · obtain ⟨birth, node, kind, parents, descriptor, same⟩ := supported
          cases kind with
          | group =>
              obtain ⟨newGroups, newStreams, extended, notices⟩ :=
                explained.complete_group_noticesCovered descriptor
                  (same ▸ ⟨announced, completed⟩) (same ▸ healthy) (same ▸ accounted)
              have impossible := maximal [.groupSuccess node newGroups newStreams]
                matching failures extended (reportingNoticesCovered_of_noticesCovered notices)
              cases impossible
          | stream =>
              obtain ⟨extended, retained⟩ := reporting_complete_stream valid coherent
                roleCoherent explained covered descriptor (same ▸ ⟨announced, completed⟩)
                  (same ▸ healthy) (same ▸ accounted)
              have impossible := maximal [.streamSuccess node] matching failures extended retained
              cases impossible
      · exact Or.inr (Or.inr ⟨announced, accounted⟩)
    · exact Or.inl supported
  have accounted : ∀ occurrence owners producer payload,
      TaskAt work occurrence owners producer payload →
      TaskAccounted work matching events failures occurrence := by
    intro occurrence owners producer payload known
    apply Classical.byContradiction
    intro outstanding
    obtain ⟨next, nextOwners, nextProducer, result, ref, task, ready, member, healthy, least⟩ :=
      least_ready_owner valid coherent continuous ordered explained known outstanding
    have notified : ref ∈ announcedRefs ((groups ++ streams).map DeliveryNode.ref) events := by
      apply Classical.byContradiction
      intro fresh
      obtain ⟨node, kind, dependencies, descriptor, same⟩ := task.owner_at_producer member
      have supported := least_owner_supported explained valid coherent ordered task ready descriptor
        (same ▸ member) (same ▸ healthy) (same ▸ fresh)
        (fun smaller before smallerHealthy => dependency smallerHealthy
          (least smaller (by simpa only [same] using before) smallerHealthy))
      exact covered.1 node kind dependencies nextProducer descriptor
        supported
    obtain ⟨event, nextMatching, cuts, extended, retained⟩ :=
      extend_ready_reporting valid coherent roleCoherent continuous ordered pathCoherent
        explained covered task ready ⟨ref, member, notified, healthy⟩
    have impossible := maximal [event] nextMatching cuts extended retained
    cases impossible
  have dependencies : ∀ ref,
      ¬NodeFailed work matching events failures ref →
      DependencySatisfied work ((groups ++ streams).map DeliveryNode.ref) matching events
        failures ref := by
    intro ref healthy
    apply dependency healthy
    intro occurrence owners projected _
    obtain ⟨producer, payload, known⟩ := projected
    exact accounted occurrence owners producer payload known
  exact ⟨tail, matching, failures, joined.symm ▸ explained, joined.symm ▸ covered,
    joined.symm ▸ accounted, joined.symm ▸ dependencies⟩

-----------------------------------------------------------------------------------------
-- Retained contributor notices are observable when their dependencies are healthy
-----------------------------------------------------------------------------------------

/-- A produced retained-failure group is announced once all its dependencies are satisfied.
Witness: otherwise the group is eligible under the retained-failure alternative, directly
contradicting the reporting frontier. This derives visibility, not a terminal law.
-/
theorem GroupNoticesCovered.recorded_group_announced
    {work initial matching events failures node dependencies producer}
    (covered : GroupNoticesCovered work initial matching events failures)
    (known : NodeAt work node .group dependencies producer)
    (recorded : HasRecordedFailure work failures events.length node.ref)
    (produced : ∀ source, producer = some source → Published matching events source)
    (satisfied
      : ∀ ref ∈ dependencies,
          DependencySatisfied work initial matching events failures ref)
    : node.ref ∈ announcedRefs initial events := by
  classical
  apply Classical.byContradiction
  intro fresh
  exact covered node dependencies producer known
    ⟨fresh, Or.inr ⟨rfl, recorded⟩, produced, satisfied⟩

end GraphQL.IncrementalDelivery.Correctness
