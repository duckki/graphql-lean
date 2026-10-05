import Proofs.GraphQL.IncrementalDelivery.Correctness.ReportingAccounting
import Proofs.GraphQL.IncrementalDelivery.Correctness.FailureReportOrigins

/-! Retained constructive notices produce actual scopes, not just hidden cancellation.
Unavailable producers, failed dependencies, and already-closed contributors remain
separate causal obligations in the general mixed progress proof.
-/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Derive the retained notice before using its actual completion
-----------------------------------------------------------------------------------------

/-- A produced retained-failure group with satisfied dependencies reports its whole scope
after its eventual completion. Witness: the constructive frontier derives announcement;
ordered settlement and actual closure then count the execution-certified positive failure.
The owner may be latent at settlement. Neither Terminal nor a supplied report or eventual
notice is assumed; pre-settlement unfinishedness remains explicit.
-/
theorem Explains.recorded_group_reported_of_covered_frontier
    {paths bound work groups streams events matching failures cut occurrence owners
      producer payload node dependencies birth}
    (coherent : MixedOwnerPaths.WorkAt paths bound work)
    (positive : ExecutionErrors.WorkPositive work)
    (explained : Explains work groups streams events matching failures)
    (covered
      : GroupNoticesCovered work ((groups ++ streams).map DeliveryNode.ref) matching
          events failures)
    (closedRefs
      : ∀ ref ∈ announcedRefs ((groups ++ streams).map DeliveryNode.ref) events,
          ref ∈ completedRefs events)
    (recorded : (cut, occurrence) ∈ failures)
    (known : TaskAt work occurrence owners producer payload)
    (descriptor : NodeAt work node .group dependencies birth)
    (contributes : node.ref ∈ owners)
    (unfinished : node.ref ∉ completedRefs (events.take cut))
    (produced : ∀ source, birth = some source → Published matching events source)
    (satisfied
      : ∀ ref ∈ dependencies,
          DependencySatisfied work ((groups ++ streams).map DeliveryNode.ref) matching
            events failures ref)
    : FailureReportedFor events node.path := by
  have bounded := explained.2.1.cut_le recorded
  have pending : HasRecordedFailure work failures events.length node.ref :=
    ⟨occurrence, owners, mem_failedBefore recorded bounded, ⟨producer, payload, known⟩,
      contributes⟩
  have announced := GroupNoticesCovered.recorded_group_announced covered descriptor pending
    produced satisfied
  have counted := positive.task known
    (explained.2.1.recorded_payload_fails recorded known)
  exact Explains.recorded_owner_reported_of_eventual_notice coherent explained closedRefs
    recorded known counted descriptor contributes unfinished announced

end GraphQL.IncrementalDelivery.Correctness
