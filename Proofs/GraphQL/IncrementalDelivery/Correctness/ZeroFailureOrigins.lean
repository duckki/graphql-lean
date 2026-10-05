import Proofs.GraphQL.IncrementalDelivery.Correctness.ReportingNoticeCoverage
import Proofs.GraphQL.IncrementalDelivery.Correctness.TaskErrors
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.SettlementClosures

/-! Zero-count failed group closures need dependency or producer explanations.
They cannot substitute for positive-error reports of a directly settled contributor.
-/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- A zero-count closure has no direct settled contributor
-----------------------------------------------------------------------------------------

/-- A zero-count group completion has no contributor failure recorded at its boundary.
Witness: each accepted contributor has an execution-certified positive count, and that
count is bounded by the completion's exact contribution sum. Later settlements are not
included by this statement, even if they have already been recorded in the final history.
-/
theorem Explains.zero_group_completion_no_recorded_failure
    {work groups streams events matching failures index node}
    (positive : ExecutionErrors.WorkPositive work)
    (explained : Explains work groups streams events matching failures)
    (selected : events[index]? = some (.groupFailure node 0))
    : ¬HasRecordedFailure work failures (events.take index).length node.ref := by
  intro recorded
  obtain ⟨occurrence, owners, settled, ⟨producer, payload, known⟩, contributes⟩ := recorded
  obtain ⟨entry, member, same⟩ := List.mem_map.mp settled
  have inCuts := (List.mem_filter.mp member).1
  have actual : (entry.1, occurrence) ∈ failures := by simpa only [← same] using inCuts
  have counted := positive.task known (explained.2.1.recorded_payload_fails actual known)
  have allowed := explained.2.2 index _ selected
  simp only [EventAllowed, failedBefore_filter _ (Nat.le_refl _)] at allowed
  have bound := allowed.2.2.2.contribution_le
    (List.mem_map.mpr ⟨entry, member, same⟩) known contributes
  omega

-----------------------------------------------------------------------------------------
-- No direct contribution leaves only dependency and producer failure
-----------------------------------------------------------------------------------------

/-- A zero-count group completion has a failed dependency or an unpublished producer.
Witness: the zero count excludes direct settlements; if dependencies were all healthy and
the supplied descriptor's producer published, causal inversion would keep the group
healthy. The conclusion locates a smaller causal obligation, not a covering report.
-/
theorem Explains.zero_group_completion_dependency_or_unavailable_producer
    {ancestry bound roles work groups streams events matching failures index node
      dependencies producer}
    (coherent : MixedRefs.WorkAt ancestry 0 bound work)
    (roleCoherent : RefRoles.WorkRoles roles work)
    (positive : ExecutionErrors.WorkPositive work)
    (explained : Explains work groups streams events matching failures)
    (known : NodeAt work node .group dependencies producer)
    (selected : events[index]? = some (.groupFailure node 0))
    : (∃ ref ∈ dependencies, NodeFailed work matching (events.take index) failures ref)
      ∨ ∃ source,
          producer = some source ∧ ¬Published matching (events.take index) source := by
  classical
  apply Classical.byContradiction
  intro absent
  have combined : Explains work groups streams
      (events.take index ++ events.drop index) matching failures := by
    simpa only [List.take_append_drop] using explained
  have shorter := combined.prefix
  have noRecord : ¬HasRecordedFailure work
      (failures.filter (fun entry => entry.1 ≤ (events.take index).length))
      (events.take index).length node.ref := by
    simpa only [HasRecordedFailure, failedBefore_filter _ (Nat.le_refl _)]
      using Explains.zero_group_completion_no_recorded_failure positive explained selected
  have produced : ∀ source, producer = some source →
      Published matching (events.take index) source := by
    intro source birth
    apply Classical.byContradiction
    intro unpublished
    exact absent (Or.inr ⟨source, birth, unpublished⟩)
  have healthyDependencies : ∀ ref ∈ dependencies,
      ¬NodeFailed work matching (events.take index)
        (failures.filter (fun entry => entry.1 ≤ (events.take index).length)) ref := by
    intro ref member failed
    apply absent
    apply Or.inl
    refine ⟨ref, member, ?_⟩
    simpa only [nodeFailed_filter (Nat.le_refl _)] using failed
  have healthy := Explains.group_healthy_of_no_recorded_failure coherent roleCoherent
    shorter known noRecord produced healthyDependencies
  exact healthy (explained.2.2 index _ selected).2.2.1

end GraphQL.IncrementalDelivery.Correctness
