import Proofs.GraphQL.IncrementalDelivery.Correctness.DeferDependencies
import Proofs.GraphQL.IncrementalDelivery.WorkScheduler.SingletonOwners

/-! Singleton defer owners retain causal ancestry through arbitrarily nested producers.
The shape restriction is proof-only and does not alter scheduler admission.
-/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open Semantics.Ancestry Semantics.GeneralScheduling
open WorkScheduler

-----------------------------------------------------------------------------------------
-- Singleton deferred work may contain nested task producers
-----------------------------------------------------------------------------------------

/-- Every node is a defer group and every task has one owner; producers may be nested.
Several tasks and descriptors may share the same key.
-/
def SingletonDefer (work : Work) : Prop :=
  (∀ node kind parents producer, NodeAt work node kind parents producer → kind = .group)
  ∧ ∀ occurrence owners producer payload,
      TaskAt work occurrence owners producer payload → ∃ key, owners = [key]

/-- Singleton defer work is defer-only work, by forgetting the owner-list restriction. -/
theorem SingletonDefer.toDeferOnly {work} (shape : SingletonDefer work)
    : DeferOnly work :=
  shape.1

/-- Each singleton defer node supplies a task owned by exactly its key.
Witness: its deferred descriptor and the singleton task-owner hypothesis.
-/
theorem SingletonDefer.node_task {work node kind parents producer}
    (shape : SingletonDefer work) (known : NodeAt work node kind parents producer)
    : kind = .group
      ∧ ∃ occurrence payload, TaskAt work occurrence [node.key] producer payload := by
  have same := shape.1 _ _ _ _ known
  subst kind
  refine ⟨rfl, ?_⟩
  cases StructuralEquivalence.nodeAt_of_current known with
  | group located member =>
      have task := TaskAt.executionGroup located.toCurrent
      obtain ⟨key, same⟩ := shape.2 _ _ _ _ task
      have owns := List.mem_map_of_mem
        (f := fun group : DeferredFragment => group.node.key) member
      rw [same] at owns
      have equal := List.mem_singleton.mp owns
      exact ⟨_, _, by simpa only [same, equal] using task⟩

/-- Singleton defer tasks are execution-group occurrences, never stream items.
Witness: a stream task would exhibit a forbidden stream node.
-/
theorem SingletonDefer.task_shape {work occurrence owners producer payload}
    (shape : SingletonDefer work)
    (known : TaskAt work occurrence owners producer payload)
    : ∃ address key, occurrence = .executionGroup address ∧ owners = [key] := by
  cases StructuralEquivalence.taskAt_of_current known with
  | executionGroup =>
      obtain ⟨key, same⟩ := shape.2 _ _ _ _ known
      exact ⟨_, key, rfl, same⟩
  | item located _ =>
      have impossible := shape.1 _ _ _ _ (NodeAt.stream located.toCurrent)
      cases impossible

/-- A located produced subtree retains the enclosing deferred task's ancestry support.
Witness: its producer-generating edge and append descent; stream edges are impossible.
-/
theorem SingletonDefer.producer_context
    {parents work address current enclosing producer}
    (shape : SingletonDefer work) (continuous : DeferContinuous parents work)
    (ordered : StreamOwnersOrdered work)
    (located : Located work address current (some producer) enclosing)
    : ∃ owners ancestor payload,
        TaskAt work producer owners ancestor payload
        ∧ DeferUnder parents owners current :=
  shape.toDeferOnly.producer_context continuous ordered located

/-- A produced singleton defer node reuses its producer's owner or depends on that key.
Witness: generated defer continuity, with stream-item producer regions excluded by shape.
-/
theorem SingletonDefer.producer_parent
    {parents bound work node kind dependencies producer}
    (shape : SingletonDefer work) (coherent : MixedKeys.WorkAt parents 0 bound work)
    (continuous : DeferContinuous parents work) (ordered : StreamOwnersOrdered work)
    (known : NodeAt work node kind dependencies (some producer))
    : ∃ key ancestor payload,
        TaskAt work producer [key] ancestor payload
        ∧ (key = node.key ∨ key ∈ dependencies) := by
  obtain ⟨owners, ancestor, payload, key, task, member, support⟩ :=
    shape.toDeferOnly.producer_parent coherent continuous ordered known
  obtain ⟨owner, same⟩ := shape.2 _ _ _ _ task
  have equal : key = owner := by simpa [same] using member
  exact ⟨owner, ancestor, payload, same ▸ task, equal ▸ support⟩

-----------------------------------------------------------------------------------------
-- Cancellation cannot silently account for a healthy singleton owner
-----------------------------------------------------------------------------------------

/-- Failure of a produced task's singleton parent owner fails its own owner.
Witness: the owner is reused or is an explicit group dependency.
-/
theorem SingletonDefer.producer_failure
    {parents bound work failed occurrence key producer payload parentKey ancestor result}
    (shape : SingletonDefer work) (coherent : MixedKeys.WorkAt parents 0 bound work)
    (continuous : DeferContinuous parents work) (ordered : StreamOwnersOrdered work)
    (known : TaskAt work occurrence [key] (some producer) payload)
    (parent : TaskAt work producer [parentKey] ancestor result)
    (failure : NodeFailed work failed parentKey)
    : NodeFailed work failed key := by
  apply shape.toDeferOnly.producer_failure coherent continuous ordered known (by simp)
    parent
  intro owner member
  exact (List.mem_singleton.mp member).symm ▸ failure

/-- Cancellation of any singleton defer task fails its sole owner, even with nested
producers. Witness: dependency-rank induction and defer ancestry propagation; repeated
descriptors do not require a unique producer for the owner's key.
-/
theorem SingletonDefer.cancelled_owner_failed
    {parents bound work failed occurrence key producer payload}
    (shape : SingletonDefer work) (coherent : MixedKeys.WorkAt parents 0 bound work)
    (continuous : DeferContinuous parents work) (ordered : StreamOwnersOrdered work)
    (known : TaskAt work occurrence [key] producer payload)
    (cancelled : TaskCancelled work failed occurrence)
    : NodeFailed work failed key :=
  shape.toDeferOnly.cancelled_owner_failed coherent continuous ordered known (by simp)
    cancelled

/-- A represented healthy singleton defer dependency is satisfied only after completion.
Witness: cancellation would fail its owner, while publication necessarily announces it.
Absent ancestor placeholders are handled separately by the scheduler dependency rule.
-/
theorem SingletonDefer.dependency_cases
    {parents bound work groups streams events matching failures key}
    (shape : SingletonDefer work) (coherent : MixedKeys.WorkAt parents 0 bound work)
    (continuous : DeferContinuous parents work) (ordered : StreamOwnersOrdered work)
    (explained : Explains work groups streams events matching failures)
    (dependency
      : DependencySatisfied work ((groups ++ streams).map DeliveryNode.key) matching
          events (failures.map Prod.snd) key)
    : (¬∃ birth, NodeHasProducer work key birth) ∨ key ∈ completedKeys events := by
  rcases dependency with ⟨healthy, absent | completed | ⟨fresh, accounted⟩⟩
  · exact Or.inl absent
  · exact Or.inr completed
  · classical
    by_cases absent : ¬∃ birth, NodeHasProducer work key birth
    · exact Or.inl absent
    obtain ⟨birth, node, kind, dependencies, descriptor, same⟩ := Classical.not_not.mp absent
    obtain ⟨_, occurrence, payload, task⟩ := shape.node_task descriptor
    have known : TaskAt work occurrence [key] birth payload := same ▸ task
    rcases accounted occurrence [key] ⟨birth, payload, known⟩ (by simp)
      with cancelled | published
    · exact False.elim (healthy
        (shape.cancelled_owner_failed coherent continuous ordered known cancelled))
    · exact False.elim (fresh (explained.singleton_published_announced known published))

end GraphQL.IncrementalDelivery.Correctness
