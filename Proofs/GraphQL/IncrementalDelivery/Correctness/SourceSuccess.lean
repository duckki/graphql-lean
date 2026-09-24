import Proofs.GraphQL.IncrementalDelivery.Correctness.SourceReconstruction
import Proofs.GraphQL.IncrementalDelivery.Correctness.PublicationCoverage

/-! Successful source-work certificates follow from complete zero-error observations. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open WorkScheduler

/-- Successful zero-count object outcomes contain a value with no counted errors.
Witness: the two result constructors exclude a failed payload.
-/
theorem object_payload_success {path result}
    (success : (Payload.object path result).failure = none)
    (zero : payloadErrors (.object path result) = 0)
    : ∃ data, result = .ok (data, 0) := by
  cases result with
  | error errors => simp [Payload.failure] at success
  | ok pair =>
      rcases pair with ⟨data, errors⟩
      exact ⟨data, by simp_all [payloadErrors]⟩

/-- The same success criterion for a streamed item, by result case analysis. -/
theorem item_payload_success {node result}
    (success : (Payload.item node result).failure = none)
    (zero : payloadErrors (.item node result) = 0)
    : ∃ data, result = .ok (data, 0) := by
  cases result with
  | error errors => simp [Payload.failure] at success
  | ok pair =>
      rcases pair with ⟨data, errors⟩
      exact ⟨data, by simp_all [payloadErrors]⟩

/-- Per-item zero-error results and successful child work give list success, by induction.
-/
theorem itemsSuccess_of_forall {items : List (Result ResponseValue × Work)}
    (all
      : ∀ entry ∈ items,
          (∃ data, entry.1 = .ok (data, 0)) ∧ SourceReconstruction.WorkSuccess entry.2)
    : SourceReconstruction.ItemsSuccess items := by
  induction items with
  | nil => trivial
  | cons entry rest ih =>
      exact ⟨
        (all entry (by simp)).1,
        (all entry (by simp)).2,
        ih (fun item member => all item (by simp [member]))
      ⟩

/-- Every located subtree is successful when all its real tasks succeed with zero errors.
Witness: structural navigation supplies each deferred/item task and its child subtree.
-/
theorem located_workSuccess {root address work producer owners}
    (located : Located root address work producer owners)
    (all
      : ∀ occurrence owners producer payload,
          TaskAt root occurrence owners producer payload
          → payload.failure = none ∧ payloadErrors payload = 0)
    : SourceReconstruction.WorkSuccess work := by
  cases work with
  | empty => trivial
  | combine left right =>
      exact ⟨located_workSuccess (.left located) all,
        located_workSuccess (.right located) all⟩
  | executionGroup groups path result children =>
      have success := all _ _ _ _ (.executionGroup located)
      exact ⟨object_payload_success success.1 success.2,
        located_workSuccess (.executionGroup located) all⟩
  | stream node items =>
      apply itemsSuccess_of_forall
      intro entry member
      obtain ⟨index, selected⟩ := List.mem_iff_getElem?.mp member
      cases equal : entry with
      | mk result children =>
          have smaller := List.sizeOf_lt_of_mem member
          rw [equal] at selected
          have success := all _ _ _ _ (.item located selected)
          exact ⟨item_payload_success success.1 success.2,
            located_workSuccess (.item located selected) all⟩
termination_by sizeOf work
decreasing_by all_goals simp_all; omega

/-- Complete zero-error observations supply the internal reconstruction success premise.
Witness: every task's successful publication and conserved zero payload-error count.
-/
theorem WorkObservation.workSuccess {response work result}
    (observed : WorkObservation response work true result)
    (positive : ExecutionErrors.WorkPositive work) (zero : result.totalErrors = 0)
    : SourceReconstruction.WorkSuccess work :=
  located_workSuccess .root
    (fun _ _ _ _ known =>
      ⟨
        observed.tasks_succeed positive zero known,
        observed.payload_errors_zero positive zero known
      ⟩)

/-- The initial completion also succeeds with zero errors; positive bubbling failures
cannot hide behind a zero-error response envelope. Together with work success, this
discharges the full internal reconstruction premise.
-/
theorem WorkObservation.completionSuccess
    {completed : Completion (List (Name × ResponseValue))} {result}
    (observed
      : WorkObservation (selectionSetResultToResponse completed.result)
          completed.work true result)
    (positive : ExecutionErrors.Positive completed) (zero : result.totalErrors = 0)
    : SourceReconstruction.CompletionSuccess completed := by
  refine ⟨?_, observed.workSuccess positive.2 zero⟩
  have errors := observed.initial_errors_le
  cases equal : completed.result with
  | error count =>
      have nonzero := positive.1 count equal
      simp [selectionSetResultToResponse, GraphQL.Execution.selectionSetResultToResponse,
        equal, zero] at errors
      omega
  | ok pair =>
      rcases pair with ⟨data, count⟩
      simp [selectionSetResultToResponse, GraphQL.Execution.selectionSetResultToResponse,
        equal, zero] at errors
      exact ⟨data, by simp [errors]⟩

end GraphQL.IncrementalDelivery.Correctness
