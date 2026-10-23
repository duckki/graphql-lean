import Proofs.GraphQL.IncrementalDelivery.Correctness.AnnouncedGroupProducers
import Proofs.GraphQL.IncrementalDelivery.Correctness.ZeroFailureOrigins
import Proofs.GraphQL.IncrementalDelivery.Correctness.FailureReportOrigins

/-! Every admitted generated-work group failure reports a positive error count. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open Semantics.Ancestry Semantics.GeneralScheduling
open WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- An open group cannot fail with no recorded contribution
-----------------------------------------------------------------------------------------

/-- Every actual group-failure completion has a positive error count on coherent work.
Witness: zero excludes recorded contributors. The open announced group retains an available
producer and healthy defer ancestry, so causal inversion would make it healthy instead.
Execution-certified positive failed payloads supply the count; no terminal law is assumed.
-/
theorem Explains.group_failure_positive
    {ancestry bound roles work groups streams events matching failures node errors}
    {index : Nat}
    (valid : Valid ancestry bound) (coherent : MixedRefs.WorkAt ancestry 0 bound work)
    (roleCoherent : RefRoles.WorkRoles roles work)
    (positive : ExecutionErrors.WorkPositive work)
    (explained : Explains work groups streams events matching failures)
    (selected : events[index]? = some (.groupFailure node errors))
    : 0 < errors := by
  by_cases zero : errors = 0
  · subst errors
    have combined : Explains work groups streams (events.take index ++ events.drop index)
        matching failures := by simpa only [List.take_append_drop] using explained
    have shorter := combined.prefix
    obtain ⟨dependencies, producer, known⟩ := (explained.eventAllowed index _ selected).1
    have noRecord : ¬HasRecordedFailure work
        (failures.filter (fun entry => entry.1 ≤ (events.take index).length))
        (events.take index).length node.ref := by
      simpa only [HasRecordedFailure, failedBefore_filter _ (Nat.le_refl _)]
        using Explains.zero_group_completion_no_recorded_failure positive explained
          selected
    have healthy := Explains.announced_group_healthy_of_no_recorded_failure valid coherent
      roleCoherent shorter known (explained.eventAllowed index _ selected).2.1.1 noRecord
    exact False.elim (healthy (explained.eventAllowed index _ selected).2.2.1)
  · omega

-----------------------------------------------------------------------------------------
-- A contributor closed before settlement already has an observable failure scope
-----------------------------------------------------------------------------------------

/-- A group contributor closed before a later accepted failure has reported its full scope.
Witness: licensing forces an earlier failed closure rather than success. Role separation
identifies a group event, positivity makes it a real report, and same-ref path coherence
transfers that actual completion's scope to the original contributor descriptor.
-/
theorem Explains.closed_group_contributor_reports_scope
    {ancestry bound roles paths pathBound work groups streams events matching failures cut
      occurrence owners producer payload owner dependencies birth}
    (valid : Valid ancestry bound) (coherent : MixedRefs.WorkAt ancestry 0 bound work)
    (roleCoherent : RefRoles.WorkRoles roles work)
    (pathCoherent : MixedOwnerPaths.WorkAt paths pathBound work)
    (positive : ExecutionErrors.WorkPositive work)
    (explained : Explains work groups streams events matching failures)
    (recorded : (cut, occurrence) ∈ failures)
    (known : TaskAt work occurrence owners producer payload)
    (descriptor : NodeAt work owner .group dependencies birth)
    (contributes : owner.ref ∈ owners)
    (closed : owner.ref ∈ completedRefs (events.take cut))
    : FailureReportedFor events owner.path := by
  obtain ⟨index, node, errors, _, same, selected⟩ :=
    explained.contributor_closed_before_settlement_failed recorded known contributes closed
  rcases selected with group | stream
  · have nonzero := Explains.group_failure_positive valid coherent roleCoherent positive
      explained group
    obtain ⟨parents, source, actual⟩ := (explained.eventAllowed index _ group).1
    have path := workAt_same_path pathCoherent actual descriptor same
    exact ⟨node, errors, nonzero, ⟨[], by simp only [List.append_nil, path]⟩,
      Or.inl (List.mem_of_getElem? group)⟩
  · obtain ⟨parents, source, actual⟩ := (explained.eventAllowed index _ stream).1
    exact False.elim (stream_group_refs_distinct roleCoherent actual descriptor same)

/-- A failed announced group reports its full scope once all announced refs have closed.
Witness: stable notice dependencies and an available producer force a recorded contributor.
An earlier closure is a positive failed report; an unfinished contributor's eventual closure
counts that accepted failure. No terminal reporting premise or promised scope is supplied.
-/
theorem Explains.announced_failed_group_reports_scope
    {ancestry bound roles paths pathBound work groups streams events matching failures
      owner dependencies birth}
    (valid : Valid ancestry bound) (coherent : MixedRefs.WorkAt ancestry 0 bound work)
    (roleCoherent : RefRoles.WorkRoles roles work)
    (pathCoherent : MixedOwnerPaths.WorkAt paths pathBound work)
    (positive : ExecutionErrors.WorkPositive work)
    (explained : Explains work groups streams events matching failures)
    (closedRefs
      : ∀ ref ∈ announcedRefs ((groups ++ streams).map DeliveryNode.ref) events,
          ref ∈ completedRefs events)
    (descriptor : NodeAt work owner .group dependencies birth)
    (announced
      : owner.ref ∈ announcedRefs ((groups ++ streams).map DeliveryNode.ref) events)
    (failed : NodeFailed work matching events failures owner.ref)
    : FailureReportedFor events owner.path := by
  classical
  have recorded : HasRecordedFailure work failures events.length owner.ref := by
    apply Classical.byContradiction
    intro absent
    exact Explains.announced_group_healthy_of_no_recorded_failure valid coherent roleCoherent
      explained descriptor announced absent failed
  obtain ⟨occurrence, owners, settled, ⟨producer, payload, task⟩, member⟩ := recorded
  obtain ⟨entry, included, same⟩ := List.mem_map.mp settled
  have inCuts := (List.mem_filter.mp included).1
  have actual : (entry.1, occurrence) ∈ failures := by simpa only [← same] using inCuts
  by_cases closed : owner.ref ∈ completedRefs (events.take entry.1)
  · exact Explains.closed_group_contributor_reports_scope valid coherent roleCoherent
      pathCoherent positive explained actual task descriptor member closed
  · exact Explains.recorded_owner_reported_of_eventual_notice pathCoherent explained
      closedRefs actual task
      (positive.task task (explained.2.1.recorded_payload_fails actual task)) descriptor
      member closed announced

end GraphQL.IncrementalDelivery.Correctness
