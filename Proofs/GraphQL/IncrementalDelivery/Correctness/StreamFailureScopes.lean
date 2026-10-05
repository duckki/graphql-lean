import Proofs.GraphQL.IncrementalDelivery.Correctness.StreamShape
import Proofs.GraphQL.IncrementalDelivery.Correctness.TaskAttachmentPaths
import Proofs.GraphQL.IncrementalDelivery.Correctness.FailureReportOrigins
import Proofs.GraphQL.IncrementalDelivery.Correctness.CausalReportAssembly

/-! Recorded stream failures explain cancellation of unannounced descendants. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Causal propagation preserves observable attachment coverage
-----------------------------------------------------------------------------------------

/-- Reports for recorded failures cover every snapshot-cancelled stream task.
Witness: causal scope assembly. Stream-only work has no group descriptors, so no group
report premise is needed; actual reports descend through certified producer attachments.
The intermediate recorded-report premise is discharged by actual closures below.
-/
theorem StreamOnly.snapshot_cancelled_reported
    {base paths bound work failed published events occurrence owners producer payload}
    (onlyStreams : StreamOnly work)
    (coherent : MixedOwnerPaths.WorkAt paths bound work)
    (under : ExecutionPaths.WorkUnder base work)
    (reports
      : ∀ occurrence ∈ failed,
          ∀ owners producer payload,
            TaskAt work occurrence owners producer payload
            → FailureReportedFor events payload.path)
    (cancelled : Causality.TaskCancelled work failed published occurrence)
    (known : TaskAt work occurrence owners producer payload)
    : FailureReportedFor events payload.path := by
  apply snapshot_cancelled_reported_of_group_and_task_scopes coherent under ?_
    reports cancelled known
  intro node dependencies birth descriptor _
  cases (onlyStreams.node descriptor).1

-----------------------------------------------------------------------------------------
-- Actual closures discharge the recorded-report premise
-----------------------------------------------------------------------------------------

/-- Closing announced IDs reports every cancelled attachment in coherent stream-only work.
Witness: each recorded stream failure has one open owner and a positive count; actual
closures report it, then mutual causal induction propagates those reports to descendants.
Neither terminal reporting nor a previously supplied cancellation report is assumed.
-/
theorem StreamOnly.cancelled_reported
    {base paths bound work groups streams events matching failures occurrence owners
      producer payload}
    (onlyStreams : StreamOnly work)
    (coherent : MixedOwnerPaths.WorkAt paths bound work)
    (under : ExecutionPaths.WorkUnder base work)
    (positive : ExecutionErrors.WorkPositive work)
    (explained : Explains work groups streams events matching failures)
    (closedRefs
      : ∀ ref ∈ announcedRefs ((groups ++ streams).map DeliveryNode.ref) events,
          ref ∈ completedRefs events)
    (cancelled : TaskCancelled work matching events failures occurrence)
    (known : TaskAt work occurrence owners producer payload)
    : FailureReportedFor events payload.path := by
  obtain ⟨cut, _, _, cause⟩ := cancelled
  apply onlyStreams.snapshot_cancelled_reported coherent under ?_ cause known
  intro task member taskOwners birth result descriptor
  obtain ⟨entry, recorded, same⟩ := List.mem_map.mp member
  have recorded : entry ∈ failures := (List.mem_filter.mp recorded).1
  have recordedTask : (entry.1, task) ∈ failures := by simpa only [← same] using recorded
  have count := positive.task descriptor
    (explained.2.1.recorded_payload_fails recordedTask descriptor)
  obtain ⟨node, outcome, ownersEq, _, _⟩ := onlyStreams.task descriptor
  rw [ownersEq] at descriptor
  exact Explains.singleton_recorded_task_reported coherent explained closedRefs
    recordedTask descriptor count

end GraphQL.IncrementalDelivery.Correctness
