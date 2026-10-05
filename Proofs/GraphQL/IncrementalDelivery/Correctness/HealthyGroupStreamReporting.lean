import Proofs.GraphQL.IncrementalDelivery.Correctness.StreamFailureScopes
import Proofs.GraphQL.IncrementalDelivery.Correctness.CausalReportAssembly

/-! Stream failure reporting after healthy deferred groups have released their work. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Healthy deferred groups cannot supply a cancellation cause
-----------------------------------------------------------------------------------------

/-- Actual failure reports cover snapshot-cancelled work when every deferred group remains
healthy. Witness: causal scope assembly, with failed group scopes excluded by health;
producer-local attachment prefixes transport actual reports to unannounced descendants.
Group health is a property of this reached snapshot, not a public queue-admission law.
-/
theorem snapshot_cancelled_reported_of_healthy_groups
    {base paths bound work failed published events occurrence owners producer payload}
    (coherent : MixedOwnerPaths.WorkAt paths bound work)
    (under : ExecutionPaths.WorkUnder base work)
    (healthyGroups
      : ∀ node dependencies birth,
          NodeAt work node .group dependencies birth
          → ¬Causality.NodeFailed work failed published node.ref)
    (reports
      : ∀ occurrence ∈ failed,
          ∀ owners producer payload,
            TaskAt work occurrence owners producer payload
            → FailureReportedFor events payload.path)
    (cancelled : Causality.TaskCancelled work failed published occurrence)
    (known : TaskAt work occurrence owners producer payload)
    : FailureReportedFor events payload.path := by
  exact snapshot_cancelled_reported_of_group_and_task_scopes coherent under
    (fun node dependencies birth descriptor failure =>
      False.elim (healthyGroups node dependencies birth descriptor failure))
    reports cancelled known

-----------------------------------------------------------------------------------------
-- Singleton stream failures supply reports from actual closures
-----------------------------------------------------------------------------------------

/-- Closing announced refs reports cancelled attachments if all deferred groups stay
healthy. Witness: a recorded failure cannot belong to a group task, so every such failure
has one stream owner. Licensing and positive counts supply its actual later error closure;
the snapshot theorem then propagates this report through producer-local cancellation.
No terminal reporting law or report premise is supplied.
-/
theorem Explains.cancelled_reported_of_healthy_groups
    {base paths bound work groups streams events matching failures occurrence owners
      producer payload}
    (coherent : MixedOwnerPaths.WorkAt paths bound work)
    (under : ExecutionPaths.WorkUnder base work)
    (positive : ExecutionErrors.WorkPositive work)
    (explained : Explains work groups streams events matching failures)
    (healthyGroups
      : ∀ node dependencies birth,
          NodeAt work node .group dependencies birth
          → ¬NodeFailed work matching events failures node.ref)
    (closedRefs
      : ∀ ref ∈ announcedRefs ((groups ++ streams).map DeliveryNode.ref) events,
          ref ∈ completedRefs events)
    (cancelled : TaskCancelled work matching events failures occurrence)
    (known : TaskAt work occurrence owners producer payload)
    : FailureReportedFor events payload.path := by
  obtain ⟨cut, reached, bounded, cause⟩ := cancelled
  apply snapshot_cancelled_reported_of_healthy_groups coherent under ?_ ?_ cause known
  · exact fun node dependencies birth descriptor failure =>
      healthyGroups node dependencies birth descriptor ⟨cut, reached, bounded, failure⟩
  · intro task member taskOwners birth result descriptor
    obtain ⟨entry, recorded, same⟩ := List.mem_map.mp member
    have recorded : entry ∈ failures := (List.mem_filter.mp recorded).1
    have recordedTask : (entry.1, task) ∈ failures := by simpa only [← same] using recorded
    have count := positive.task descriptor
      (explained.2.1.recorded_payload_fails recordedTask descriptor)
    cases StructuralEquivalence.taskAt_of_current descriptor with
    | executionGroup located =>
        obtain ⟨ref, owner, _⟩ := explained.2.1.announced_owner recordedTask descriptor
        obtain ⟨group, member, same⟩ := List.mem_map.mp owner
        have failedTask := mem_failedBefore recordedTask (explained.2.1.cut_le recorded)
        exact False.elim (healthyGroups _ _ _ (NodeAt.group located.toCurrent member)
          (NodeFailed.task descriptor (same ▸ owner) failedTask))
    | item located entry =>
        exact Explains.singleton_recorded_task_reported coherent explained closedRefs
          recordedTask descriptor count

end GraphQL.IncrementalDelivery.Correctness
