import Proofs.GraphQL.IncrementalDelivery.Correctness.SingletonDeferExistence
import Proofs.GraphQL.IncrementalDelivery.Correctness.QueryRealization

/-! Nested singleton deferred producers retain causal owner support. -/

namespace GraphQL.IncrementalDelivery.Tests.SingletonDeferExistence
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Semantics
open Semantics.Ancestry Semantics.GeneralScheduling
open WorkQueueSemantics

/-- A test-only recursive certificate with singleton groups and arbitrary defer nesting.
-/
def Tree : Work → Prop
  | .empty => True
  | .combine left right => Tree left ∧ Tree right
  | .executionGroup groups _ _ children => (∃ group, groups = [group]) ∧ Tree children
  | .stream .. => False

/-- Structural lookup preserves the test certificate, by navigation induction. -/
theorem Tree.located {work address current producer owners}
    (shape : Tree work) (located : Located work address current producer owners)
    : Tree current := by
  have navigation := StructuralEquivalence.located_of_current located
  clear located
  induction navigation with
  | root => exact shape
  | left _ ih => exact ih.1
  | right _ ih | executionGroup _ ih => exact ih.2
  | item _ _ ih => exact False.elim ih

/-- The recursive test certificate implies the relational singleton-defer shape.
Witness: locate each task and node in its certified subtree.
-/
theorem Tree.singleton_defer {work} (shape : Tree work) : SingletonDefer work := by
  constructor
  · intro node kind parents producer known
    cases StructuralEquivalence.nodeAt_of_current known with
    | group => rfl
    | stream located => exact False.elim (shape.located located.toCurrent)
  · intro occurrence owners producer payload known
    cases StructuralEquivalence.taskAt_of_current known with
    | executionGroup located =>
        obtain ⟨⟨group, same⟩, _⟩ := shape.located located.toCurrent
        exact ⟨group.node.ref, by simp [same]⟩
    | item located _ => exact False.elim (shape.located located.toCurrent)

/-- Fixture descriptors share an object path but carry distinct defer refs. -/
def node (ref : NodeRef) : DeliveryNode := { ref, path := [] }

/-- The second task is structurally produced by the first and depends on its owner.
Both fixed outcomes are arbitrary, including raw zero-count failures.
-/
def work (first second : Result (List (Name × ResponseValue))) : Work :=
  .executionGroup [{ node := node 0 }] [] first
    (.executionGroup [{ node := node 1, ancestors := [node 0] }] [] second .empty)

/-- The nested task's owner inherits ref zero as its strict ancestor. -/
def ancestors (ref : NodeRef) : NodeRefs := if ref = 1 then [0] else []

/-- Cancelling the nested task fails its owner, not merely its producer's owner.
Witness: the general nested cancellation lemma with explicit fixture metadata.
-/
example (first second : Result (List (Name × ResponseValue)))
    (matching : PublicationMatching) (events : List WorkQueueEvent)
    (failures : FailureCuts)
    (cancelled
      : TaskCancelled (work first second) matching events failures (.executionGroup [0]))
    : NodeFailed (work first second) matching events failures 1 := by
  apply SingletonDefer.cancelled_owner_failed (parents := ancestors) (bound := 2)
    (producer := some (.executionGroup [])) (payload := .object [] second)
    (Tree.singleton_defer (by simp [Tree, work]))
  · simp [work, MixedRefs.WorkAt, FragmentAt, node, ancestors]
  · simp [work, DeferContinuous, DeferUnder, Descends, mapRefs, node, ancestors]
  · simp [work, StreamOwnersOrdered, OwnersBefore]
  · exact TaskAt.executionGroup (.executionGroup .root)
  · exact cancelled

-----------------------------------------------------------------------------------------
-- Complete runs through produced values and reused owner IDs
-----------------------------------------------------------------------------------------

/-- Nested task-producing defer work admits a terminal history for both arbitrary
outcomes. Witness: the singleton-defer progress theorem and explicit ancestry metadata.
No initial notice, preselected history, or successful outcome is assumed.
-/
theorem nested_run_exists (first second : Result (List (Name × ResponseValue)))
    : ∃ history, AdmissibleRun (work first second) history := by
  apply (Tree.singleton_defer (by simp [Tree, work])).completeRun_exists
    (parents := ancestors) (bound := 2) (paths := fun _ => []) (pathBound := 2)
  · intro ref bounded parent member
    by_cases same : ref = 1
    · simp [ancestors, same] at member
      subst parent
      simp [same, ancestors, List.Subset]
    · simp [ancestors, same] at member
  · simp [work, MixedRefs.WorkAt, FragmentAt, node, ancestors]
  · simp [work, DeferContinuous, DeferUnder, Descends, mapRefs, node, ancestors]
  · simp [work, StreamOwnersOrdered, OwnersBefore]
  · simp [work, MixedOwnerPaths.WorkAt, OwnerPaths.MapAt, OwnerPaths.mapNodes,
      OwnerPaths.fragmentNodes, OwnerPaths.Assigned, Below, node]
  · simp [work, Work.size]

/-- A produced child can reuse its producer's owner, repeating that node descriptor. -/
def reused (first second : Result (List (Name × ResponseValue))) : Work :=
  .executionGroup [{ node := node 0 }] [] first
    (.executionGroup [{ node := node 0 }] [] second .empty)

/-- Repeated owner descriptors do not block nested progress. Witness: the same theorem
with empty ancestry; both tasks must be accounted for before their shared ID closes.
-/
example (first second : Result (List (Name × ResponseValue)))
    : ∃ history, AdmissibleRun (reused first second) history := by
  apply (Tree.singleton_defer (by simp [Tree, reused])).completeRun_exists
    (parents := fun _ => []) (bound := 1) (paths := fun _ => []) (pathBound := 1)
  · simp [Valid]
  · simp [reused, MixedRefs.WorkAt, FragmentAt, node]
  · simp [reused, DeferContinuous, DeferUnder, Descends, mapRefs, node]
  · simp [reused, StreamOwnersOrdered, OwnersBefore]
  · simp [reused, MixedOwnerPaths.WorkAt, OwnerPaths.MapAt, OwnerPaths.mapNodes,
      OwnerPaths.fragmentNodes, OwnerPaths.Assigned, Below, node]
  · simp [reused, Work.size]

/-- Constructed nested histories realize actual complete response streams, including
producer failures that cancel the child. Witness: raw progress followed by source
realization; the mapper and response batching remain the actual implementation.
-/
example (response : Response) (first second : Result (List (Name × ResponseValue)))
    : ∃ scheduler : (Execution.Work → Execution.WorkQueue),
      ∃ observed : ExecutionObservation,
        ((work first second).size ≠ 0
          → (scheduler (work first second)).Conforms (work first second))
        ∧ (executionFromWork scheduler response (work first second)).Observes observed
            true :=
  (completeObservation_exists_iff _ _).mpr (Or.inr (nested_run_exists first second))

end GraphQL.IncrementalDelivery.Tests.SingletonDeferExistence
