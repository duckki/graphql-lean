import Proofs.GraphQL.IncrementalDelivery.Correctness.MixedProgressEvents
import Proofs.GraphQL.IncrementalDelivery.Correctness.MixedOwnerSupport
import Proofs.GraphQL.IncrementalDelivery.Correctness.GroupScopeReporting

/-! Complete finite runs for arbitrary coherent generated mixed defer/stream work.
Supported notice coverage is a proof choice, not a restriction on admitted histories.
-/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open Semantics.Ancestry Semantics.GeneralScheduling
open WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- A maximal supported history accounts for every task
-----------------------------------------------------------------------------------------

/-- A supported explained prefix extends to task accounting without changing its outputs.
Witness: maximize a finite extension preserving supported notice coverage. Healthy accounted
groups close with covering notices; stream completions preserve support. A least healthy
outstanding owner must then be announced and has a coverage-preserving success or failure
step, contradicting maximality. Matching and failure evidence remain existential.
-/
theorem mixed_supported_accounted_extension
    {ancestry bound roles paths pathBound work groups streams head matching failures}
    (valid : Valid ancestry bound) (coherent : MixedRefs.WorkAt ancestry 0 bound work)
    (roleCoherent : RefRoles.WorkRoles roles work)
    (continuous : DeferContinuous ancestry work) (ordered : StreamOwnersOrdered work)
    (pathCoherent : MixedOwnerPaths.WorkAt paths pathBound work)
    (initial : Explains work groups streams head matching failures)
    (coverage
      : SupportedNoticesCovered ancestry work ((groups ++ streams).map DeliveryNode.ref)
          matching head failures)
    : ∃ tail next cuts,
        Explains work groups streams (head ++ tail) next cuts
        ∧ ∀ occurrence owners producer payload,
            TaskAt work occurrence owners producer payload
            → TaskAccounted work next (head ++ tail) cuts occurrence := by
  classical
  obtain ⟨tail, matching, failures, explained, covered, maximal⟩ :=
    initial.maximal_extension_preserving
      (fun events matching failures => SupportedNoticesCovered ancestry work
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
                matching failures extended (supportedNoticesCovered_of_noticesCovered notices)
              cases impossible
          | stream =>
              obtain ⟨extended, retained⟩ := supported_complete_stream valid coherent
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
      exact covered node kind dependencies nextProducer descriptor
        supported
    obtain ⟨event, nextMatching, cuts, extended, retained⟩ :=
      extend_ready_supported valid coherent roleCoherent continuous ordered pathCoherent
        explained covered task ready ⟨ref, member, notified, healthy⟩
    have impossible := maximal [event] nextMatching cuts extended retained
    cases impossible
  exact ⟨tail, matching, failures, joined.symm ▸ explained, joined.symm ▸ accounted⟩

/-- A reporting-covered mixed-work prefix has a terminal continuation preserving its
initial notices and batches. Witness: close an accounted reporting frontier, derive actual
cancellation reports from execution scope origins, and finalize. This is a constructive
progress policy, not a restriction on all admitted prefixes or a host fairness premise.
-/
theorem mixed_reporting_continuation
    {ancestry bound roles base paths pathBound work groups streams events matching
      failures batches}
    (valid : Valid ancestry bound) (coherent : MixedRefs.WorkAt ancestry 0 bound work)
    (roleCoherent : RefRoles.WorkRoles roles work)
    (continuous : DeferContinuous ancestry work) (ordered : StreamOwnersOrdered work)
    (pathCoherent : MixedOwnerPaths.WorkAt paths pathBound work)
    (under : ExecutionPaths.WorkUnder base work)
    (certified : ScopeMetadata.WorkScoped work)
    (positive : ExecutionErrors.WorkPositive work)
    (explained : Explains work groups streams events matching failures)
    (covered
      : ReportingNoticesCovered ancestry work ((groups ++ streams).map DeliveryNode.ref)
          matching events failures)
    (batched : WorkBatching events batches)
    : (History.mk groups streams batches).CanFinish work := by
  have origins := groupScopeOrigins_of_scopes valid coherent roleCoherent continuous ordered
    pathCoherent under certified
  obtain ⟨tail, next, cuts, extended, frontier, accounted, closed, satisfied⟩ :=
    mixed_reporting_closed_extension
    valid coherent roleCoherent continuous ordered pathCoherent explained covered
  have reports : ∀ occurrence owners producer payload,
      TaskAt work occurrence owners producer payload
      → ¬Published next (events ++ tail) occurrence
      → FailureReportedFor (events ++ tail) payload.path := by
    intro occurrence owners producer payload known unpublished
    exact Explains.cancelled_reported_of_scope_origins valid coherent roleCoherent continuous
      ordered pathCoherent under certified positive origins extended frontier.2 satisfied
      closed accounted ((accounted _ _ _ _ known).resolve_right unpublished) known
  obtain ⟨closures, run, _, _⟩ :=
    (batched.append (WorkBatching.singletons tail)).finish_accounted extended accounted reports
  refine ⟨tail.map (fun event => [event]) ++ closures.map (fun event => [event])
    ++ [[.workQueueTermination]], ?_⟩
  simpa only [List.append_assoc] using run

/-- Every nonempty coherent scope-preserving mixed work tree has a complete finite run.
Witness: covering initial notices and reporting-prefix continuation supply completion.
Execution derives the structural scope and positive-failure certificates independently.
This does not assert completion of arbitrary admitted prefixes or host fairness.
-/
theorem mixed_completeRun_exists {ancestry bound roles base paths pathBound work}
    (valid : Valid ancestry bound) (coherent : MixedRefs.WorkAt ancestry 0 bound work)
    (roleCoherent : RefRoles.WorkRoles roles work)
    (continuous : DeferContinuous ancestry work) (ordered : StreamOwnersOrdered work)
    (pathCoherent : MixedOwnerPaths.WorkAt paths pathBound work)
    (under : ExecutionPaths.WorkUnder base work)
    (certified : ScopeMetadata.WorkScoped work)
    (positive : ExecutionErrors.WorkPositive work) (nonempty : work.size ≠ 0)
    : ∃ history, AdmissibleRun work history := by
  obtain ⟨groups, streams, initialized⟩ :=
    initialization_exists valid coherent continuous ordered nonempty
  obtain ⟨groups, streams, initialized, covers⟩ := initialized.covering_exists
  have initial : Explains work groups streams [] (fun _ => .executionGroup []) [] :=
    ⟨initialized, by simp [FailureWitness], by simp⟩
  obtain ⟨batches, run⟩ := mixed_reporting_continuation valid coherent roleCoherent
    continuous ordered pathCoherent under certified positive initial
    (reportingNoticesCovered_of_noticesCovered (NoticesCovered.initial covers _))
    WorkBatching.nil
  exact ⟨⟨groups, streams, batches⟩, run⟩

end GraphQL.IncrementalDelivery.Correctness
