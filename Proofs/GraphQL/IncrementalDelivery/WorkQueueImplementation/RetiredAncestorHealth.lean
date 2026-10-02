import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.AncestorCertificates
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.AncestorGuardHealth

/-! Fresh registered settlements cannot newly invalidate retired healthy ancestors. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- A fresh task cannot contribute to an already retired healthy ancestor
-----------------------------------------------------------------------------------------

/-- Adding a fresh registered task to the failure inventory preserves healthy retired
ancestry. Witness: direct old failures contradict prior health; a new contribution would
require a live pending owner at a retired key. Generated transitivity handles taskless
intermediate records. This concerns the inventory extension, before changing queue state.
-/
theorem State.AncestorsRetired.healthy_append_fresh
    {queue : State} {work settled failed node dependencies}
    (protectedAncestors : queue.AncestorsRetired work node.key)
    (generated : ExecutedWork work) (record : GroupRecordAt work node dependencies)
    (healthy : ∀ ancestor ∈ dependencies, ¬GroupRecordInvalidated work failed ancestor)
    (accounted : queue.HealthyRegisteredTaskAccounting work settled failed)
    {task : Task} (registered : task ∈ queue.tasks)
    (matching : TaskMatches work task) (fresh : task.occurrence ∉ settled)
    : ∀ ancestor ∈ dependencies,
        ¬GroupRecordInvalidated work (failed ++ [task.occurrence]) ancestor := by
  intro ancestor member invalid
  have excludes {key} (failure : GroupRecordInvalidated work (failed ++ [task.occurrence]) key)
      : key ∈ dependencies → False := by
    induction failure with
    | @task occurrence owners key known owner recorded =>
        intro dependency
        rcases List.mem_append.mp recorded with old | new
        · exact healthy key dependency (.task known owner old)
        · obtain rfl := List.mem_singleton.mp new
          obtain ⟨birth, payload, structural⟩ := known
          obtain ⟨⟨address, actualPayload, actualBirth, _, actual⟩, _⟩ := matching
          have contributor : key ∈ task.groups.map Execution.DeliveryNode.key :=
            (structural.unique actual).1 ▸ owner
          have retired := protectedAncestors node dependencies record rfl key dependency
            task.occurrence owners ⟨birth, payload, structural⟩ owner
          have wasSettled := accounted.retired_contributor_settled registered contributor
            (fun failure => healthy key dependency failure.toRecordInvalidated) retired
          exact fresh wasSettled
    | @ancestor other otherDependencies key known earlier _ ih =>
        intro dependency
        exact ih ((generated.groupRecordAncestors_trans record known dependency) earlier)
  exact excludes invalid member

-----------------------------------------------------------------------------------------
-- The health guard's absent-parent boundary reduces to retirement preservation
-----------------------------------------------------------------------------------------

/-- Each live record with an absent, uncancelled parent retains its ancestor-retirement
certificate. `queue` is the actual state; `work` supplies full registration ancestry.
This is an internal replay invariant to prove, not a host-input or scheduler premise.
-/
def State.MissingParentAncestorsRetired (queue : State) (work : Execution.Work) : Prop :=
  ∀ node ∈ queue.groupNodes,
    ∀ parent,
      node.group.parent = some parent
      → queue.groupNode? parent = none
      → parent ∉ queue.cancelledGroups
      → queue.AncestorsRetired work node.group.node.key

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
  intro node member uncached dependencies record parent parentEq missing uncancelled
  exact (retired node member parent parentEq missing uncancelled).healthy_append_fresh
    generated record
    (healthy node member uncached dependencies record parent parentEq missing uncancelled)
    accounted registered matching fresh

-----------------------------------------------------------------------------------------
-- Failure removal cannot create a new uncancelled missing-parent boundary
-----------------------------------------------------------------------------------------

/-- An absent uncancelled key after failure removal was already absent and uncancelled.
Witness: every filtered-out key is recorded as cancelled by the same operation. This
needs no generated-work, subtree-coverage, or traversal-budget premise.
-/
theorem State.removeGroup_missing_uncancelled (queue : State) (root parent : Nat)
    (missing : (queue.removeGroup root).groupNode? parent = none)
    (uncancelled : parent ∉ (queue.removeGroup root).cancelledGroups)
    : queue.groupNode? parent = none ∧ parent ∉ queue.cancelledGroups := by
  let removed := State.removeGroup.collect (queue.groupNodes.length + 1) queue [root] []
  have noCancellation : parent ∉ queue.cancelledGroups ++ removed := uncancelled
  have oldUncancelled : parent ∉ queue.cancelledGroups :=
    fun member => noCancellation (List.mem_append_left _ member)
  refine ⟨?_, oldUncancelled⟩
  cases found : queue.groupNode? parent with
  | none => rfl
  | some node =>
      have same := State.groupNode?_key found
      have notRemoved : parent ∉ removed :=
        fun member => noCancellation (List.mem_append_right _ member)
      have retained : node ∈ (queue.removeGroup root).groupNodes :=
        List.mem_filter.mpr ⟨List.mem_of_find?_eq_some found, by
          change (!removed.contains node.group.node.key) = true
          simp [same, notRemoved]⟩
      have absent := List.find?_eq_none.mp missing node retained
      exact False.elim (absent (beq_iff_eq.mpr same))

/-- Failure cleanup preserves missing-parent retirement certificates.
Witness: surviving records retain their parents, newly absent keys are cancelled, and
permanent ancestor retirement survives removal.
-/
theorem State.MissingParentAncestorsRetired.removeGroup {queue : State} {work}
    (retired : queue.MissingParentAncestorsRetired work) (root : Nat)
    : (queue.removeGroup root).MissingParentAncestorsRetired work := by
  intro node member parent parentEq missing uncancelled
  have prior := queue.removeGroup_missing_uncancelled root parent missing uncancelled
  exact (retired node (List.mem_filter.mp member).1 parent parentEq prior.1 prior.2).mono
    (fun _ ancestorRetired => ancestorRetired.removeGroup root)

/-- Failure cleanup preserves missing-parent health for the same failure inventory.
Witness: every accepting missing-parent boundary existed before filtering; new missing
parents carry cancellation markers and cannot use the guard's accepting branch.
-/
theorem State.MissingParentAncestorsHealthy.removeGroup {queue : State} {work failed}
    (healthy : queue.MissingParentAncestorsHealthy work failed) (root : Nat)
    : (queue.removeGroup root).MissingParentAncestorsHealthy work failed := by
  intro node member uncached dependencies record parent parentEq missing uncancelled
  have prior := queue.removeGroup_missing_uncancelled root parent missing uncancelled
  exact healthy node (List.mem_filter.mp member).1 uncached dependencies record
    parent parentEq prior.1 prior.2

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
