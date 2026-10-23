import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.MissingParentCertificates
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.AncestorGuardHealth

/-! Fresh registered settlements cannot newly invalidate retired healthy ancestors. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- A fresh task cannot contribute to an already retired healthy ancestor
-----------------------------------------------------------------------------------------

/-- Adding a fresh registered task to the failure inventory preserves healthy retired
ancestry. Witness: direct old failures contradict prior health; a new contribution would
require a live pending owner at a retired ref. Generated transitivity handles taskless
intermediate records. This concerns the inventory extension, before changing queue state.
-/
theorem State.AncestorsRetired.healthy_append_fresh
    {queue : State} {work settled failed node dependencies}
    (protectedAncestors : queue.AncestorsRetired work node.ref)
    (generated : ExecutedWork work) (record : GroupRecordAt work node dependencies)
    (healthy : ∀ ancestor ∈ dependencies, ¬GroupRecordInvalidated work failed ancestor)
    (accounted : queue.HealthyRegisteredTaskAccounting work settled failed)
    {task : Task} (registered : task ∈ queue.tasks)
    (matching : TaskMatches work task) (fresh : task.occurrence ∉ settled)
    : ∀ ancestor ∈ dependencies,
        ¬GroupRecordInvalidated work (failed ++ [task.occurrence]) ancestor := by
  intro ancestor member invalid
  have excludes {ref} (failure : GroupRecordInvalidated work (failed ++ [task.occurrence]) ref)
      : ref ∈ dependencies → False := by
    induction failure with
    | @task occurrence owners ref known owner recorded =>
        intro dependency
        rcases List.mem_append.mp recorded with old | new
        · exact healthy ref dependency (.task known owner old)
        · obtain rfl := List.mem_singleton.mp new
          obtain ⟨birth, payload, structural⟩ := known
          obtain ⟨⟨address, actualPayload, actualBirth, _, actual⟩, _⟩ := matching
          have contributor : ref ∈ task.groups.map Execution.DeliveryNode.ref :=
            (structural.unique actual).1 ▸ owner
          have retired := protectedAncestors node dependencies record rfl ref dependency
            task.occurrence owners ⟨birth, payload, structural⟩ owner
          have wasSettled := accounted.retired_contributor_settled registered contributor
            (fun failure => healthy ref dependency failure.toRecordInvalidated) retired
          exact fresh wasSettled
    | @ancestor other otherDependencies ref known earlier _ ih =>
        intro dependency
        exact ih ((generated.groupRecordAncestors_trans record known dependency) earlier)
  exact excludes invalid member

-----------------------------------------------------------------------------------------
-- The health guard's absent-parent boundary reduces to retirement preservation
-----------------------------------------------------------------------------------------

/-- At a protected missing-parent boundary, recording a fresh registered settlement
preserves the health obligation. Witness: instantiate retired-ancestry preservation for
each uncached live record; no output admission, publication, or guard-soundness assumption
is needed. State changes from the actual failure handler remain a separate obligation.
-/
theorem State.MissingParentAncestorsHealthy.append_fresh
    {queue : State} {work settled failed}
    (healthy : queue.MissingParentAncestorsHealthy work failed)
    (retired : queue.MissingParentAncestorsRetired work)
    (generated : ExecutedWork work)
    (accounted : queue.HealthyRegisteredTaskAccounting work settled failed)
    {task : Task} (registered : task ∈ queue.tasks)
    (matching : TaskMatches work task) (fresh : task.occurrence ∉ settled)
    : queue.MissingParentAncestorsHealthy work (failed ++ [task.occurrence]) := by
  intro node member dependencies record parent parentEq missing uncancelled
  exact (retired node member parent parentEq missing uncancelled).healthy_append_fresh
    generated record
    (healthy node member dependencies record parent parentEq missing uncancelled)
    accounted registered matching fresh

-----------------------------------------------------------------------------------------
-- Failure removal cannot create a new uncancelled missing-parent boundary
-----------------------------------------------------------------------------------------

/-- Failure cleanup preserves missing-parent health for the same failure inventory.
Witness: every accepting missing-parent boundary existed before filtering; new missing
parents carry cancellation markers and cannot use the guard's accepting branch.
-/
theorem State.MissingParentAncestorsHealthy.removeGroup {queue : State} {work failed}
    (healthy : queue.MissingParentAncestorsHealthy work failed) (root : Nat)
    : (queue.removeGroup root).MissingParentAncestorsHealthy work failed := by
  intro node member dependencies record parent parentEq missing uncancelled
  have prior := queue.removeGroup_missing_uncancelled root parent missing uncancelled
  exact healthy node (List.mem_filter.mp member).1 dependencies record
    parent parentEq prior.1 prior.2

/-- Replaying a retained rejection preserves historical health of uncancelled parents.
Witness: task replacement leaves group metadata unchanged; each owner removal either
preserves an old missing parent or records its cancellation.
-/
theorem State.MissingParentAncestorsHealthy.taskFailure_preserves {queue : State}
    {work failed} (healthy : queue.MissingParentAncestorsHealthy work failed)
    (occurrence : Occurrence) (errors : Nat)
    : (queue.taskFailure occurrence errors).1.MissingParentAncestorsHealthy work
        failed := by
  cases found : queue.taskNode? occurrence with
  | none => simpa [State.taskFailure, found] using healthy
  | some task =>
      rw [queue.taskFailure_eq occurrence errors task found]
      exact failureGroupFold_preserves
        (fun current => current.MissingParentAncestorsHealthy work failed)
        (fun _ ref valid => valid.removeGroup ref) errors task.task.groups _ healthy

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
