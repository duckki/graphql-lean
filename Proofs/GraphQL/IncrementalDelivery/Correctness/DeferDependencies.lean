import Proofs.GraphQL.IncrementalDelivery.Correctness.DependencyKeys

/-! Causal owner support for defer-only work, including shared owners and nested producers.
These structural consequences do not strengthen scheduler admission.
-/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open Semantics.Ancestry Semantics.GeneralScheduling
open WorkScheduler

-----------------------------------------------------------------------------------------
-- Deferred producers preserve the ancestry of every contributing owner
-----------------------------------------------------------------------------------------

/-- All actual work nodes are defer groups; owner lists and nested producers are arbitrary.
-/
def DeferOnly (work : Work) : Prop :=
  ∀ node kind parents producer, NodeAt work node kind parents producer → kind = .group

/-- Every defer-only task is a deferred occurrence. Witness: an item task would supply
a stream descriptor, contradicting the work-shape hypothesis.
-/
theorem DeferOnly.task_shape {work occurrence owners producer payload}
    (shape : DeferOnly work) (known : TaskAt work occurrence owners producer payload)
    : ∃ address, occurrence = .deferred address := by
  cases StructuralEquivalence.taskAt_of_current known with
  | deferred => exact ⟨_, rfl⟩
  | item located _ =>
      have impossible := shape _ _ _ _ (NodeAt.stream located.toCurrent)
      cases impossible

/-- Located produced work retains its deferred producer's owner support.
Witness: the producer-generating edge, then append descent; stream edges are excluded.
-/
theorem DeferOnly.producer_context
    {parents work address current enclosing producer}
    (shape : DeferOnly work) (continuous : DeferContinuous parents work)
    (ordered : StreamOwnersOrdered work)
    (located : Located work address current (some producer) enclosing)
    : ∃ owners ancestor payload,
        TaskAt work producer owners ancestor payload
        ∧ DeferUnder parents owners current := by
  have context {address current birth enclosing}
      (navigation : StructuralEquivalence.Located work address current birth enclosing)
      {producer} (generated : birth = some producer) :
      ∃ owners ancestor payload,
        TaskAt work producer owners ancestor payload ∧ DeferUnder parents owners current := by
    induction navigation with
    | root => contradiction
    | left _ ih =>
        obtain ⟨owners, ancestor, payload, task, under⟩ := ih generated
        exact ⟨owners, ancestor, payload, task, under.1⟩
    | right _ ih =>
        obtain ⟨owners, ancestor, payload, task, under⟩ := ih generated
        exact ⟨owners, ancestor, payload, task, under.2⟩
    | deferred navigation =>
        cases generated
        have properties := dependencyProperties_located continuous ordered navigation.toCurrent
        simp only [DeferContinuous] at properties
        exact ⟨_, _, _, .deferred navigation.toCurrent, properties.1.1⟩
    | item navigation _ =>
        have impossible := shape _ _ _ _ (NodeAt.stream navigation.toCurrent)
        cases impossible
  exact context (StructuralEquivalence.located_of_current located) rfl

/-- A produced defer owner reuses or depends on some contributing producer owner.
Witness: generated defer continuity and the coherent ancestry of the child descriptor.
-/
theorem DeferOnly.producer_parent
    {parents bound work node kind dependencies producer}
    (shape : DeferOnly work) (coherent : MixedKeys.WorkAt parents 0 bound work)
    (continuous : DeferContinuous parents work) (ordered : StreamOwnersOrdered work)
    (known : NodeAt work node kind dependencies (some producer))
    : ∃ owners ancestor payload key,
        TaskAt work producer owners ancestor payload
        ∧ key ∈ owners
        ∧ (key = node.key ∨ key ∈ dependencies) := by
  have same := shape _ _ _ _ known
  subst kind
  cases StructuralEquivalence.nodeAt_of_current known with
  | group located member =>
      obtain ⟨owners, ancestor, payload, task, under⟩ :=
        shape.producer_context continuous ordered located.toCurrent
      obtain ⟨key, contributes, support⟩ := under.1 _ member
      refine ⟨owners, ancestor, payload, key, task, contributes, ?_⟩
      rcases support with reused | dependency
      · exact Or.inl reused
      · have localWork := coherent_located coherent located.toCurrent
        rw [MixedKeys.WorkAt] at localWork
        exact Or.inr (by simpa only [(localWork.2.1 _ member).2.2] using dependency)

/-- Coherent group descriptors use exactly the full ancestry assigned to their key.
Witness: locate the deferred fragment and project its execution metadata.
-/
theorem DeferOnly.node_parents {parents lower bound work node dependencies producer}
    (coherent : MixedKeys.WorkAt parents lower bound work)
    (known : NodeAt work node .group dependencies producer)
    : dependencies = parents node.key := by
  cases StructuralEquivalence.nodeAt_of_current known with
  | group located member =>
      have localWork := coherent_located coherent located.toCurrent
      rw [MixedKeys.WorkAt] at localWork
      exact (localWork.2.1 _ member).2.2

-----------------------------------------------------------------------------------------
-- Healthy owner accounting requires actual publication
-----------------------------------------------------------------------------------------

/-- If all producer owners fail, each child owner fails too.
Witness: the supporting producer owner is reused or an explicit failed group dependency.
-/
theorem DeferOnly.producer_failure
    {parents bound work failed occurrence owners key producer payload parentOwners
      ancestor result}
    (shape : DeferOnly work) (coherent : MixedKeys.WorkAt parents 0 bound work)
    (continuous : DeferContinuous parents work) (ordered : StreamOwnersOrdered work)
    (known : TaskAt work occurrence owners (some producer) payload)
    (member : key ∈ owners) (parent : TaskAt work producer parentOwners ancestor result)
    (failures : ∀ parentKey ∈ parentOwners, NodeFailed work failed parentKey)
    : NodeFailed work failed key := by
  obtain ⟨node, kind, dependencies, descriptor, same⟩ := known.owner_at_producer member
  obtain ⟨supportOwners, birth, value, parentKey, task, contributes, support⟩ :=
    shape.producer_parent coherent continuous ordered descriptor
  have equal := (TaskAt.unique task parent).1
  have failure := failures parentKey (equal ▸ contributes)
  rcases support with reused | dependency
  · exact (reused.trans same) ▸ failure
  · have group := shape _ _ _ _ descriptor
    subst kind
    exact same ▸ NodeFailed.groupParent descriptor dependency failure

/-- Cancelling a defer-only task fails every contributing owner, including shared owners.
Witness: dependency-rank induction, propagating all producer failures through ancestry.
Repeated descriptors and arbitrarily nested producers remain permitted.
-/
theorem DeferOnly.cancelled_owner_failed
    {parents bound work failed occurrence owners key producer payload}
    (shape : DeferOnly work) (coherent : MixedKeys.WorkAt parents 0 bound work)
    (continuous : DeferContinuous parents work) (ordered : StreamOwnersOrdered work)
    (known : TaskAt work occurrence owners producer payload) (member : key ∈ owners)
    (cancelled : TaskCancelled work failed occurrence)
    : NodeFailed work failed key := by
  induction rank : occurrence.dependencyRank
    using Nat.strongRecOn generalizing occurrence owners key producer payload with
  | ind rank ih =>
      cases cancelled with
      | owners projected _ failedOwners =>
          obtain ⟨birth, result, task⟩ := projected
          exact failedOwners key ((TaskAt.unique task known).1.symm ▸ member)
      | producerFailed projected failure =>
          obtain ⟨otherOwners, result, task⟩ := projected
          have same := (TaskAt.unique known task).2.1
          subst producer
          obtain ⟨_, parentOwners, ancestor, value, parent⟩ := task.producer_dependency
          exact shape.producer_failure coherent continuous ordered known member parent
            (fun parentKey contributes => .task parent contributes failure)
      | producerCancelled projected cancellation =>
          obtain ⟨otherOwners, result, task⟩ := projected
          have same := (TaskAt.unique known task).2.1
          subst producer
          obtain ⟨lower, parentOwners, ancestor, value, parent⟩ := task.producer_dependency
          exact shape.producer_failure coherent continuous ordered known member parent
            (fun parentKey contributes =>
              ih _ (by omega) parent contributes cancellation rfl)

/-- A task with any healthy owner is accounted for exactly when it has published.
Witness: cancellation would fail that owner; publication is itself an accounting case.
Unlike singleton ownership, this need not announce every healthy co-owner.
-/
theorem DeferOnly.accounted_iff_published
    {parents bound work matching events failed occurrence owners key producer payload}
    (shape : DeferOnly work) (coherent : MixedKeys.WorkAt parents 0 bound work)
    (continuous : DeferContinuous parents work) (ordered : StreamOwnersOrdered work)
    (known : TaskAt work occurrence owners producer payload) (member : key ∈ owners)
    (healthy : ¬NodeFailed work failed key)
    : Accounted work matching events failed occurrence
      ↔ Published matching events occurrence := by
  constructor
  · rintro (cancelled | published)
    · exact False.elim (healthy
        (shape.cancelled_owner_failed coherent continuous ordered known member cancelled))
    · exact published
  · exact Or.inr

end GraphQL.IncrementalDelivery.Correctness
