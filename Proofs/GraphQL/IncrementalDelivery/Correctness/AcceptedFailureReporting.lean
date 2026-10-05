import Proofs.GraphQL.IncrementalDelivery.Correctness.GroupFailurePositivity
import Proofs.GraphQL.IncrementalDelivery.Correctness.OwnerScopeInheritance

/-! Closed announced IDs report accepted failures, including shared later settlements. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open Semantics.Ancestry Semantics.GeneralScheduling
open WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Licensing provides a real contributor notice, not a promised reporting owner
-----------------------------------------------------------------------------------------

/-- Every accepted failed task has an observable covering report once announced IDs close.
Witness: a stream item's sole owner remains open by licensing. A shared group task has a
previously announced contributor; its earlier closure is a positive group-scope report,
or its later closure counts this settlement. Generated owner paths cover the attachment.
No retained-frontier, terminal-reporting, or future-notice premise is needed for this origin.
Unsettled causal cancellations still require their separate inheritance argument.
-/
theorem Explains.accepted_failure_reported
    {ancestry bound roles paths pathBound work groups streams events matching failures cut
      occurrence owners producer payload}
    (valid : Valid ancestry bound) (coherent : MixedRefs.WorkAt ancestry 0 bound work)
    (roleCoherent : RefRoles.WorkRoles roles work)
    (pathCoherent : MixedOwnerPaths.WorkAt paths pathBound work)
    (positive : ExecutionErrors.WorkPositive work)
    (explained : Explains work groups streams events matching failures)
    (closedRefs
      : ∀ ref ∈ announcedRefs ((groups ++ streams).map DeliveryNode.ref) events,
          ref ∈ completedRefs events)
    (recorded : (cut, occurrence) ∈ failures)
    (known : TaskAt work occurrence owners producer payload)
    : FailureReportedFor events payload.path := by
  have count := positive.task known (explained.2.1.recorded_payload_fails recorded known)
  cases StructuralEquivalence.taskAt_of_current known with
  | executionGroup located =>
      obtain ⟨ref, contributes, announced⟩ := explained.2.1.announced_owner recorded known
      obtain ⟨owner, dependencies, descriptor, same⟩ := known.executionGroup_owner contributes
      have member := same.symm ▸ contributes
      by_cases closed : owner.ref ∈ completedRefs (events.take cut)
      · exact reported_owner_covers_task pathCoherent known descriptor member
          (Explains.closed_group_contributor_reports_scope valid coherent roleCoherent
            pathCoherent positive explained recorded known descriptor member closed)
      · have eventual : owner.ref ∈ announcedRefs ((groups ++ streams).map DeliveryNode.ref)
            events := by
          have old := same.symm ▸ announced
          rcases List.mem_append.mp old with initial | pending
          · exact List.mem_append_left _ initial
          · obtain ⟨event, included, notice⟩ := List.mem_flatMap.mp pending
            exact List.mem_append_right _ (List.mem_flatMap.mpr
              ⟨event, List.mem_of_mem_take included, notice⟩)
        exact Explains.recorded_task_reported_of_eventual_notice pathCoherent explained
          closedRefs recorded known count ⟨owner.ref, member, closed, eventual⟩
  | item located entry =>
      exact Explains.singleton_recorded_task_reported pathCoherent explained closedRefs
        recorded known count

end GraphQL.IncrementalDelivery.Correctness
