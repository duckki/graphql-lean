import Proofs.GraphQL.IncrementalDelivery.Correctness.DeferExistence
import Proofs.GraphQL.IncrementalDelivery.Correctness.QueryRealization

/-! Shared deferred owners retain causal support through nested task producers. -/

namespace GraphQL.IncrementalDelivery.Tests.DeferExistence
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Semantics
open Semantics.Ancestry Semantics.GeneralScheduling
open WorkScheduler

/-- A test-only recursive certificate excludes streams without restricting defer owners.
-/
def Tree : Work → Prop
  | .empty => True
  | .combine left right => Tree left ∧ Tree right
  | .executionGroup _ _ _ children => Tree children
  | .stream .. => False

/-- Every located subtree retains the recursive certificate, by navigation induction. -/
theorem Tree.located {work address current producer owners}
    (shape : Tree work) (located : Located work address current producer owners)
    : Tree current := by
  have navigation := StructuralEquivalence.located_of_current located
  clear located
  induction navigation with
  | root => exact shape
  | left _ ih => exact ih.1
  | right _ ih => exact ih.2
  | executionGroup _ ih => exact ih
  | item _ _ ih => exact False.elim ih

/-- The recursive test certificate implies the relational defer-only work shape.
Witness: structural lookup rules out every stream descriptor.
-/
theorem Tree.defer_only {work} (shape : Tree work) : DeferOnly work := by
  intro node kind parents producer known
  cases StructuralEquivalence.nodeAt_of_current known with
  | group => rfl
  | stream located => exact False.elim (shape.located located.toCurrent)

/-- Shared fixture descriptors all refer to the same response object. -/
def node (key : Nat) : DeliveryNode := { key, path := [] }

/-- A shared producer reveals a shared child whose owners have different ancestors. -/
def work (first second : Result (List (Name × ResponseValue))) : Work :=
  .executionGroup [{ node := node 0 }, { node := node 1 }] [] first
    (.executionGroup
      [
        { node := node 2, ancestors := [node 0] },
        { node := node 3, ancestors := [node 1] }
      ]
      [] second .empty)

/-- Each produced owner inherits the ancestry of its own supporting producer owner. -/
def ancestors (key : Nat) : Keys :=
  if key = 2 then [0] else if key = 3 then [1] else []

/-- Cancelling the shared child fails both its owners, not just the selected delivery ID.
Witness: the general defer-only cancellation theorem, instantiated for either key.
-/
example (first second : Result (List (Name × ResponseValue))) (failed : List Occurrence)
    (cancelled : TaskCancelled (work first second) failed (.executionGroup [0]))
    (key : Nat) (member : key ∈ [2, 3])
    : NodeFailed (work first second) failed key := by
  apply DeferOnly.cancelled_owner_failed (parents := ancestors) (bound := 4)
    (producer := some (.executionGroup [])) (payload := .object [] second)
    (Tree.defer_only (by simp [Tree, work]))
  · simp [work, MixedKeys.WorkAt, FragmentAt, node, ancestors]
  · simp [work, DeferContinuous, DeferUnder, Descends, mapKeys, node, ancestors]
  · simp [work, StreamOwnersOrdered, OwnersBefore]
  · exact TaskAt.executionGroup (.executionGroup .root)
  · exact member
  · exact cancelled

-----------------------------------------------------------------------------------------
-- Shared nested work and silently accounted ancestor owners
-----------------------------------------------------------------------------------------

/-- Shared nested producers admit a complete run for every pair of fixed outcomes.
Witness: general defer-only progress; neither successful outcomes nor initially covered
child owners are required.
-/
theorem shared_run_exists (first second : Result (List (Name × ResponseValue)))
    : ∃ history, AdmissibleRun (work first second) history := by
  apply (Tree.defer_only (by simp [Tree, work])).completeRun_exists
    (parents := ancestors) (bound := 4) (paths := fun _ => []) (pathBound := 4)
  · intro key bounded parent member
    by_cases two : key = 2
    · simp [ancestors, two] at member
      subst parent
      simp [two, ancestors, List.Subset]
    · by_cases three : key = 3
      · simp [ancestors, three] at member
        subst parent
        simp [three, ancestors, List.Subset]
      · simp [ancestors, two, three] at member
  · simp [work, MixedKeys.WorkAt, FragmentAt, node, ancestors]
  · simp [work, DeferContinuous, DeferUnder, Descends, mapKeys, node, ancestors]
  · simp [work, StreamOwnersOrdered, OwnersBefore]
  · simp [work, MixedOwnerPaths.WorkAt, OwnerPaths.MapAt, OwnerPaths.mapNodes,
      OwnerPaths.fragmentNodes, OwnerPaths.Assigned, Below, node]
  · simp [work, Work.size]

/-- Key one shares a task with its own ancestor. Publication under zero can silently
account for one; the child still requires the full transitive ancestry to be satisfied.
-/
def silent (first second : Result (List (Name × ResponseValue))) : Work :=
  .executionGroup [{ node := node 0 }, { node := node 1, ancestors := [node 0] }] [] first
    (.executionGroup [{ node := node 2, ancestors := [node 1, node 0] }] [] second .empty)

/-- Full transitive ancestry includes the silently accounted owner's ancestor. -/
def silentAncestors (key : Nat) : Keys :=
  if key = 1 then [0] else if key = 2 then [1, 0] else []

/-- Silent shared-owner accounting does not strand a produced descendant.
Witness: defer-only existence with full ancestry, preserving the public dependency rule.
-/
example (first second : Result (List (Name × ResponseValue)))
    : ∃ history, AdmissibleRun (silent first second) history := by
  apply (Tree.defer_only (by simp [Tree, silent])).completeRun_exists
    (parents := silentAncestors) (bound := 3) (paths := fun _ => []) (pathBound := 3)
  · intro key bounded parent member
    by_cases one : key = 1
    · simp [silentAncestors, one] at member
      subst parent
      simp [one, silentAncestors, List.Subset]
    · by_cases two : key = 2
      · simp [silentAncestors, two] at member
        rcases member with rfl | rfl <;> simp [two, silentAncestors, List.Subset]
      · simp [silentAncestors, one, two] at member
  · simp [silent, MixedKeys.WorkAt, FragmentAt, node, silentAncestors]
  · simp [silent, DeferContinuous, DeferUnder, Descends, mapKeys, node, silentAncestors]
  · simp [silent, StreamOwnersOrdered, OwnersBefore]
  · simp [silent, MixedOwnerPaths.WorkAt, OwnerPaths.MapAt, OwnerPaths.mapNodes,
      OwnerPaths.fragmentNodes, OwnerPaths.Assigned, Below, node]
  · simp [silent, Work.size]

/-- The nested shared fixture has a complete actual wire observation for every outcome.
Witness: construct its admitted history, then apply conforming-source realization.
-/
example (response : Response) (first second : Result (List (Name × ResponseValue)))
    : ∃ scheduler : Execution.WorkScheduler,
      ∃ observed : ExecutionObservation,
        scheduler.Conforms (work first second)
        ∧ (executionFromWork scheduler response (work first second)).Observes observed
            true :=
  (completeObservation_exists_iff _ _).mpr (Or.inr (shared_run_exists first second))

end GraphQL.IncrementalDelivery.Tests.DeferExistence
