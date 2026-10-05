import Proofs.GraphQL.IncrementalDelivery.Correctness.BoundedOwnerScopeReporting
import Proofs.GraphQL.IncrementalDelivery.Correctness.AcceptedFailureReporting
import Proofs.GraphQL.IncrementalDelivery.Correctness.UnannouncedGroupFailureOrigins
import Proofs.GraphQL.IncrementalDelivery.Correctness.ReportingClosures

/-! Actual failure reports cover group notice scopes, including unannounced descendants. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open Semantics.Ancestry Semantics.GeneralScheduling WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Failed group scopes descend through strictly earlier notice scopes
-----------------------------------------------------------------------------------------

/-- Every failed group scope is covered at an accounted, closed reporting frontier.
Witness: strong ref induction. Announced failures supply actual positive notices; failed
ancestors and cancelled introducing producers descend through earlier covering scopes.
The structural certificate comes from execution and contains no reporting premise.
-/
theorem Explains.failed_group_scope_reported
    {ancestry refBound roles base paths pathBound work groups streams events matching
      failures node dependencies birth}
    (valid : Valid ancestry refBound)
    (coherent : MixedRefs.WorkAt ancestry 0 refBound work)
    (roleCoherent : RefRoles.WorkRoles roles work)
    (continuous : DeferContinuous ancestry work) (ordered : StreamOwnersOrdered work)
    (pathCoherent : MixedOwnerPaths.WorkAt paths pathBound work)
    (under : ExecutionPaths.WorkUnder base work)
    (certified : ScopeMetadata.WorkScoped work)
    (positive : ExecutionErrors.WorkPositive work) (origins : GroupScopeOrigins work)
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
    (accounted
      : ∀ occurrence owners producer payload,
          TaskAt work occurrence owners producer payload
          → TaskAccounted work matching events failures occurrence)
    (known : NodeAt work node .group dependencies birth)
    (failed : NodeFailed work matching events failures node.ref)
    : FailureReportedFor events node.path := by
  have reports : ∀ ref, ∀ node dependencies birth,
      NodeAt work node .group dependencies birth
      → node.ref = ref
      → NodeFailed work matching events failures ref
      → FailureReportedFor events node.path := by
    intro ref
    induction ref using Nat.strongRecOn with
    | ind ref ih =>
        intro node dependencies birth descriptor same failed
        obtain ⟨origin, parents, source, originKnown, originSame, support⟩ :=
          origins _ _ _ descriptor
        have originRef : origin.ref = ref := originSame.trans same
        have originFailed : NodeFailed work matching events failures origin.ref :=
          originRef ▸ failed
        have scope := workAt_same_path pathCoherent originKnown descriptor originSame
        suffices report : FailureReportedFor events origin.path from scope ▸ report
        by_cases announced
          : origin.ref ∈ announcedRefs ((groups ++ streams).map DeliveryNode.ref) events
        · exact Explains.announced_failed_group_reports_scope valid coherent roleCoherent
            pathCoherent positive explained closedRefs originKnown announced originFailed
        · rcases Explains.unannounced_group_failure_origin coherent roleCoherent explained
            covered satisfied originKnown announced originFailed with ancestor | unavailable
          · obtain ⟨parentRef, member, parentFailed⟩ := ancestor
            have canonical := DeferOnly.node_dependencies coherent originKnown
            have before := valid origin.ref (coherent_node_bounds coherent originKnown).2
              parentRef (canonical ▸ member)
            obtain ⟨parent, kind, parentDeps, parentBirth, parentKnown, parentSame⟩ :=
              Explains.failed_node_known explained parentFailed
            have group : kind = .group := by
              have role := node_ref_role roleCoherent parentKnown
              have parentRole := group_dependency_role roleCoherent originKnown member
              rw [parentSame, parentRole] at role
              cases kind with
              | group => rfl
              | stream => cases role
            subst kind
            have report := ih parentRef (by simpa only [originRef] using before.1)
              parent parentDeps parentBirth parentKnown parentSame parentFailed
            exact report.descendant (certified.dependency_prefix pathCoherent originKnown
              parentKnown (parentSame.symm ▸ member))
          · obtain ⟨producer, generated, unpublished⟩ := unavailable
            rcases support with root | introduced
            · cases root.symm.trans generated
            · obtain ⟨producer', owners, ancestor, payload, parent, kind, parentDeps,
                producerSame, task, parentKnown, member, before, below⟩ := introduced
              cases Option.some.inj (producerSame.symm.trans generated)
              have cancelled := (accounted _ _ _ _ task).resolve_right unpublished
              have report := cancelled_owner_scope_reported_below valid coherent
                roleCoherent continuous ordered pathCoherent under certified
                (fun node deps birth known bounded failed =>
                  ih node.ref bounded node deps birth known rfl failed)
                (fun cut task recorded owners birth result known =>
                  Explains.accepted_failure_reported valid coherent roleCoherent
                    pathCoherent positive explained closedRefs recorded known)
                cancelled task parentKnown member
                (by simpa only [originRef] using before)
              exact report.descendant below
  exact reports node.ref node dependencies birth known rfl failed

-----------------------------------------------------------------------------------------
-- Full notice scopes supply task-local terminal reports
-----------------------------------------------------------------------------------------

/-- Every cancelled task is covered by an actual positive-error completion at the frontier.
Witness: failed group scopes cover their contributing payloads; accepted settlements and
mutual causal descent cover stream dependencies and unavailable structural producers.
-/
theorem Explains.cancelled_reported_of_scope_origins
    {ancestry refBound roles base paths pathBound work groups streams events matching
      failures occurrence owners producer payload}
    (valid : Valid ancestry refBound)
    (coherent : MixedRefs.WorkAt ancestry 0 refBound work)
    (roleCoherent : RefRoles.WorkRoles roles work)
    (continuous : DeferContinuous ancestry work) (ordered : StreamOwnersOrdered work)
    (pathCoherent : MixedOwnerPaths.WorkAt paths pathBound work)
    (under : ExecutionPaths.WorkUnder base work)
    (certified : ScopeMetadata.WorkScoped work)
    (positive : ExecutionErrors.WorkPositive work) (origins : GroupScopeOrigins work)
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
    (accounted
      : ∀ occurrence owners producer payload,
          TaskAt work occurrence owners producer payload
          → TaskAccounted work matching events failures occurrence)
    (cancelled : TaskCancelled work matching events failures occurrence)
    (known : TaskAt work occurrence owners producer payload)
    : FailureReportedFor events payload.path := by
  apply cancelled_reported_of_owner_task_scopes roleCoherent pathCoherent under ?_ ?_
    cancelled known
  · intro address owners producer payload node dependencies birth task descriptor member
      failed
    exact reported_owner_covers_task pathCoherent task descriptor member
      (Explains.failed_group_scope_reported valid coherent roleCoherent continuous ordered
        pathCoherent under certified positive origins explained covered satisfied closedRefs accounted
        descriptor failed)
  · intro cut occurrence recorded owners producer payload task
    exact Explains.accepted_failure_reported valid coherent roleCoherent pathCoherent
      positive explained closedRefs recorded task

end GraphQL.IncrementalDelivery.Correctness
