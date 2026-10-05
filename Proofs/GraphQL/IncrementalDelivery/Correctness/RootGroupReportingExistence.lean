import Proofs.GraphQL.IncrementalDelivery.Correctness.CausalTaskReportAssembly
import Proofs.GraphQL.IncrementalDelivery.Correctness.AcceptedFailureReporting
import Proofs.GraphQL.IncrementalDelivery.Correctness.UnannouncedGroupFailureOrigins
import Proofs.GraphQL.IncrementalDelivery.Correctness.ReportingClosures

/-! Root defer descriptors admit complete reporting runs with arbitrary nested streams. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open Semantics.Ancestry Semantics.GeneralScheduling
open WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Task-local origin construction discharges every causal cancellation branch
-----------------------------------------------------------------------------------------

/-- Cancelled tasks are reported at a closed reporting frontier with root group descriptors.
Witness: failed-owner ancestor descent supplies task-local defer reports, accepted failures
supply settlement reports, and mutual causal assembly handles nested streams and producers.
Groups may depend on other groups and need not all have been announced.
-/
theorem Explains.cancelled_reported_of_root_groups
    {ancestry bound roles base paths pathBound work groups streams events matching
      failures occurrence owners producer payload}
    (valid : Valid ancestry bound) (coherent : MixedRefs.WorkAt ancestry 0 bound work)
    (roleCoherent : RefRoles.WorkRoles roles work)
    (pathCoherent : MixedOwnerPaths.WorkAt paths pathBound work)
    (under : ExecutionPaths.WorkUnder base work)
    (positive : ExecutionErrors.WorkPositive work)
    (explained : Explains work groups streams events matching failures)
    (covered
      : GroupNoticesCovered work ((groups ++ streams).map DeliveryNode.ref) matching
          events failures)
    (satisfied
      : ∀ ref,
          ¬NodeFailed work matching events failures ref
          → DependencySatisfied work ((groups ++ streams).map DeliveryNode.ref) matching
              events failures ref)
    (closedRefs
      : ∀ ref ∈ announcedRefs ((groups ++ streams).map DeliveryNode.ref) events,
          ref ∈ completedRefs events)
    (roots
      : ∀ node dependencies producer,
          NodeAt work node .group dependencies producer → producer = none)
    (cancelled : TaskCancelled work matching events failures occurrence)
    (known : TaskAt work occurrence owners producer payload)
    : FailureReportedFor events payload.path := by
  apply cancelled_reported_of_owner_task_scopes roleCoherent pathCoherent under ?_ ?_
    cancelled known
  · intro address owners producer payload node dependencies birth task descriptor member
      failed
    exact Explains.failed_owner_reported_of_root_groups valid coherent roleCoherent
      pathCoherent positive explained covered satisfied closedRefs roots task descriptor
      member failed
  · intro cut task recorded taskOwners birth result descriptor
    exact Explains.accepted_failure_reported valid coherent roleCoherent pathCoherent positive
      explained closedRefs recorded descriptor

-----------------------------------------------------------------------------------------
-- Preserve an existing reporting-covered prefix and its supplied batches
-----------------------------------------------------------------------------------------

/-- A reporting-covered root-group prefix has a complete continuation preserving batches.
Witness: constructive accounting closes announced IDs while retaining eligible failed
notices; task-local scope assembly then proves the actual terminal reporting obligation.
This is a restricted finite-progress proof, not completion from every admitted prefix.
-/
theorem root_groups_reporting_continuation
    {ancestry bound roles base paths pathBound work groups streams events matching
      failures batches}
    (valid : Valid ancestry bound) (coherent : MixedRefs.WorkAt ancestry 0 bound work)
    (roleCoherent : RefRoles.WorkRoles roles work)
    (continuous : DeferContinuous ancestry work) (ordered : StreamOwnersOrdered work)
    (pathCoherent : MixedOwnerPaths.WorkAt paths pathBound work)
    (under : ExecutionPaths.WorkUnder base work)
    (positive : ExecutionErrors.WorkPositive work)
    (roots
      : ∀ node dependencies producer,
          NodeAt work node .group dependencies producer → producer = none)
    (explained : Explains work groups streams events matching failures)
    (covered
      : ReportingNoticesCovered ancestry work ((groups ++ streams).map DeliveryNode.ref)
          matching events failures)
    (batched : WorkBatching events batches)
    : (History.mk groups streams batches).CanFinish work := by
  obtain ⟨tail, next, cuts, extended, frontier, accounted, closed, satisfied⟩ :=
    mixed_reporting_closed_extension valid coherent roleCoherent continuous ordered
      pathCoherent explained covered
  have reports : ∀ occurrence owners producer payload,
      TaskAt work occurrence owners producer payload
      → ¬Published next (events ++ tail) occurrence
      → FailureReportedFor (events ++ tail) payload.path := by
    intro occurrence owners producer payload known unpublished
    exact Explains.cancelled_reported_of_root_groups valid coherent roleCoherent
      pathCoherent under positive extended frontier.2 satisfied closed roots
      ((accounted _ _ _ _ known).resolve_right unpublished) known
  obtain ⟨closures, run, _, _⟩ :=
    (batched.append (WorkBatching.singletons tail)).finish_accounted extended accounted
      reports
  refine ⟨tail.map (fun event => [event]) ++ closures.map (fun event => [event])
    ++ [[.workQueueTermination]], ?_⟩
  simpa only [List.append_assoc] using run

/-- Nonempty coherent work with root group descriptors has a complete finite reporting run.
Witness: covering initialization establishes the constructive reporting frontier, and its
batch-preserving continuation derives all actual failure scopes before termination.
Nested streams and nonempty defer ancestry are permitted; produced defer groups remain
the separate unavailable-ancestor obligation of the general mixed-work proof.
-/
theorem completeRun_exists_of_root_group_descriptors
    {ancestry bound roles base paths pathBound work}
    (valid : Valid ancestry bound) (coherent : MixedRefs.WorkAt ancestry 0 bound work)
    (roleCoherent : RefRoles.WorkRoles roles work)
    (continuous : DeferContinuous ancestry work) (ordered : StreamOwnersOrdered work)
    (pathCoherent : MixedOwnerPaths.WorkAt paths pathBound work)
    (under : ExecutionPaths.WorkUnder base work)
    (positive : ExecutionErrors.WorkPositive work)
    (roots
      : ∀ node dependencies producer,
          NodeAt work node .group dependencies producer → producer = none)
    (nonempty : work.size ≠ 0)
    : ∃ history, AdmissibleRun work history := by
  obtain ⟨groups, streams, initialized⟩ :=
    initialization_exists valid coherent continuous ordered nonempty
  obtain ⟨groups, streams, initialized, covers⟩ := initialized.covering_exists
  have initial : Explains work groups streams [] (fun _ => .executionGroup []) [] :=
    ⟨initialized, by simp [FailureWitness], by simp⟩
  obtain ⟨batches, run⟩ := root_groups_reporting_continuation valid coherent roleCoherent
    continuous ordered pathCoherent under positive roots initial
    (reportingNoticesCovered_of_noticesCovered (NoticesCovered.initial covers _))
    WorkBatching.nil
  exact ⟨⟨groups, streams, batches⟩, run⟩

end GraphQL.IncrementalDelivery.Correctness
