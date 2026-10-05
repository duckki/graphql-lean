import Proofs.GraphQL.IncrementalDelivery.Correctness.AcceptedFailureReporting
import Proofs.GraphQL.IncrementalDelivery.Correctness.CausalReportAssembly

/-! Announced group scopes cover unannounced stream and producer cancellations. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open Semantics.Ancestry Semantics.GeneralScheduling
open WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Concrete group notices supply every origin needed by causal report assembly
-----------------------------------------------------------------------------------------

/-- Cancelled task attachments are reported when every defer group has been announced.
Witness: closed announced groups provide actual positive full-scope reports; accepted tasks
provide actual attachment reports. Mutual causal assembly transports these scopes through
defer dependencies and producer-local attachment prefixes, including unannounced streams.
This restricted notice premise does not demand that streams have their own IDs or assume
terminal reporting; arbitrary unannounced defer groups remain a separate construction case.
-/
theorem Explains.cancelled_reported_of_announced_groups
    {ancestry bound roles base paths pathBound work groups streams events matching
      failures occurrence owners producer payload}
    (valid : Valid ancestry bound) (coherent : MixedRefs.WorkAt ancestry 0 bound work)
    (roleCoherent : RefRoles.WorkRoles roles work)
    (pathCoherent : MixedOwnerPaths.WorkAt paths pathBound work)
    (under : ExecutionPaths.WorkUnder base work)
    (positive : ExecutionErrors.WorkPositive work)
    (explained : Explains work groups streams events matching failures)
    (groupsAnnounced
      : ∀ node dependencies birth,
          NodeAt work node .group dependencies birth
          → node.ref ∈ announcedRefs ((groups ++ streams).map DeliveryNode.ref) events)
    (closedRefs
      : ∀ ref ∈ announcedRefs ((groups ++ streams).map DeliveryNode.ref) events,
          ref ∈ completedRefs events)
    (cancelled : TaskCancelled work matching events failures occurrence)
    (known : TaskAt work occurrence owners producer payload)
    : FailureReportedFor events payload.path := by
  apply cancelled_reported_of_group_and_task_scopes pathCoherent under ?_ ?_ cancelled known
  · intro node dependencies birth descriptor failed
    exact Explains.announced_failed_group_reports_scope valid coherent roleCoherent
      pathCoherent positive explained closedRefs descriptor
      (groupsAnnounced _ _ _ descriptor) failed
  · intro cut task recorded taskOwners birth result descriptor
    exact Explains.accepted_failure_reported valid coherent roleCoherent pathCoherent
      positive explained closedRefs recorded descriptor

end GraphQL.IncrementalDelivery.Correctness
