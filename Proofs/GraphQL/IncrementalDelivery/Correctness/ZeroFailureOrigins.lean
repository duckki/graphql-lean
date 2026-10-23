import Proofs.GraphQL.IncrementalDelivery.Correctness.ReportingNoticeCoverage
import Proofs.GraphQL.IncrementalDelivery.Correctness.TaskErrors
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.SettlementClosures

/-! Selected failure completions always carry a positive contributor cause. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- A zero-count closure has no direct settled contributor
-----------------------------------------------------------------------------------------

/-- A zero-count group failure is excluded by the supported-cause admission rule.
Witness: every admitted failure completion has a positive selected cause.
-/
theorem Explains.zero_group_completion_no_recorded_failure
    {work groups streams events matching failures index node}
    (_positive : ExecutionErrors.WorkPositive work)
    (explained : Explains work groups streams events matching failures)
    (selected : events[index]? = some (.groupFailure node 0))
    : ¬HasRecordedFailure work failures (events.take index).length node.ref := by
  have positive := (explained.eventAllowed index _ selected).2.2.2.positive
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
  exact healthy (explained.eventAllowed index _ selected).2.2.1

end GraphQL.IncrementalDelivery.Correctness
