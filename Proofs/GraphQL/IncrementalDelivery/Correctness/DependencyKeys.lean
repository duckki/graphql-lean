import Proofs.GraphQL.IncrementalDelivery.Correctness.Initialization
import Proofs.GraphQL.IncrementalDelivery.WorkScheduler.TaskReadiness

/-! Execution's existing key/ancestry certificates order task-producer dependencies.
No readiness, notice coverage, or response-correctness premise is added to admission.
-/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open Semantics.Ancestry Semantics.GeneralScheduling
open WorkScheduler

-----------------------------------------------------------------------------------------
-- Structural lookup preserves the generated dependency context
-----------------------------------------------------------------------------------------

/-- Defer continuity and stream-owner ordering hold in every located subtree.
Witness: navigation induction through their structural execution certificates.
-/
theorem dependencyProperties_located {parents work address current producer owners}
    (continuous : DeferContinuous parents work) (ordered : StreamOwnersOrdered work)
    (located : Located work address current producer owners)
    : DeferContinuous parents current ∧ StreamOwnersOrdered current := by
  have navigation := StructuralEquivalence.located_of_current located
  clear located
  induction navigation with
  | root => exact ⟨continuous, ordered⟩
  | left _ ih =>
      simp only [DeferContinuous, StreamOwnersOrdered] at ih
      exact ⟨ih.1.1, ih.2.1⟩
  | right _ ih =>
      simp only [DeferContinuous, StreamOwnersOrdered] at ih
      exact ⟨ih.1.2, ih.2.2⟩
  | executionGroup _ ih =>
      simp only [DeferContinuous, StreamOwnersOrdered] at ih
      exact ⟨ih.1.2, ih.2.2⟩
  | item _ selected ih =>
      simp only [DeferContinuous, StreamOwnersOrdered] at ih
      exact ⟨ih.1 _ (List.mem_of_getElem? selected),
        ih.2 _ (List.mem_of_getElem? selected)⟩

/-- Located producer contexts either retain deferred ancestry/owner support or enter a
fresh stream-item key region. Witness: the producer-generating edge, then append descent.
-/
theorem producer_key_context {parents bound work address current enclosing producer}
    (coherent : MixedKeys.WorkAt parents 0 bound work)
    (continuous : DeferContinuous parents work) (ordered : StreamOwnersOrdered work)
    (located : Located work address current (some producer) enclosing)
    : ∃ owners ancestor payload,
        TaskAt work producer owners ancestor payload
        ∧ ((DeferUnder parents owners current ∧ OwnersBefore owners current)
            ∨ ∃ key,
                owners = [key] ∧ MixedKeys.WorkAt parents (key + 1) bound current) := by
  have context {address current birth enclosing}
      (navigation : StructuralEquivalence.Located work address current birth enclosing)
      {producer} (generated : birth = some producer) :
      ∃ owners ancestor payload,
        TaskAt work producer owners ancestor payload
        ∧ ((DeferUnder parents owners current ∧ OwnersBefore owners current)
          ∨ ∃ key, owners = [key] ∧ MixedKeys.WorkAt parents (key + 1) bound current) := by
    induction navigation with
    | root => contradiction
    | left _ ih =>
        obtain ⟨owners, ancestor, payload, known, supported⟩ := ih generated
        refine ⟨owners, ancestor, payload, known, ?_⟩
        rcases supported with ⟨under, before⟩ | ⟨key, same, bounded⟩
        · exact Or.inl ⟨under.1, before.1⟩
        · rw [MixedKeys.WorkAt] at bounded
          exact Or.inr ⟨key, same, bounded.1⟩
    | right _ ih =>
        obtain ⟨owners, ancestor, payload, known, supported⟩ := ih generated
        refine ⟨owners, ancestor, payload, known, ?_⟩
        rcases supported with ⟨under, before⟩ | ⟨key, same, bounded⟩
        · exact Or.inl ⟨under.2, before.2⟩
        · rw [MixedKeys.WorkAt] at bounded
          exact Or.inr ⟨key, same, bounded.2⟩
    | executionGroup navigation =>
        cases generated
        have properties := dependencyProperties_located continuous ordered navigation.toCurrent
        simp only [DeferContinuous, StreamOwnersOrdered] at properties
        exact ⟨_, _, _, .executionGroup navigation.toCurrent,
          Or.inl ⟨properties.1.1, properties.2.1⟩⟩
    | item navigation selected =>
        cases generated
        have localWork := coherent_located coherent navigation.toCurrent
        rw [MixedKeys.WorkAt] at localWork
        exact ⟨_, _, _, .item navigation.toCurrent selected,
          Or.inr ⟨_, rfl, localWork.2.2 _ (List.mem_of_getElem? selected)⟩⟩
  exact context (StructuralEquivalence.located_of_current located) rfl

/-- Generated task owner lists are nonempty at every structural occurrence.
Witness: nonempty deferred maps or a stream item's singleton owner list.
-/
theorem coherent_task_owners_nonempty
    {parents lower bound work occurrence owners producer payload}
    (coherent : MixedKeys.WorkAt parents lower bound work)
    (known : TaskAt work occurrence owners producer payload)
    : owners ≠ [] := by
  cases StructuralEquivalence.taskAt_of_current known with
  | executionGroup located =>
      have localWork := coherent_located coherent located.toCurrent
      rw [MixedKeys.WorkAt] at localWork
      exact fun empty => localWork.1 (List.map_eq_nil_iff.mp empty)
  | item => simp

/-- An uncancelled child has some healthy producer owner when producer owners are nonempty.
Witness: failure of all those owners would cancel the producer and then the child.
-/
theorem healthy_producer_owner
    {work failed occurrence owners producer payload parentOwners ancestor result}
    (known : TaskAt work occurrence owners (some producer) payload)
    (parentKnown : TaskAt work producer parentOwners ancestor result)
    (nonempty : parentOwners ≠ []) (active : ¬TaskCancelled work failed occurrence)
    : ∃ key ∈ parentOwners, ¬NodeFailed work failed key := by
  classical
  apply Classical.byContradiction
  intro absent
  apply active
  apply TaskCancelled.producerCancelled known
  apply TaskCancelled.owners parentKnown nonempty
  intro key member
  apply Classical.byContradiction
  intro healthy
  exact absent ⟨key, member, healthy⟩

-----------------------------------------------------------------------------------------
-- A healthy child owner is supported by a no-larger healthy producer owner
-----------------------------------------------------------------------------------------

/-- Every healthy contributing key of an uncancelled generated child task has a healthy
producer owner with a no-larger key. Witness: reused/dependent defer ancestry, ordered
stream owners, or the fresh key interval below a stream item. This prevents a producer
dependency from forcing progress through a strictly later owner key.
-/
theorem producer_owner_key_le
    {parents bound work failed occurrence owners producer payload key}
    (valid : Valid parents bound) (coherent : MixedKeys.WorkAt parents 0 bound work)
    (continuous : DeferContinuous parents work) (ordered : StreamOwnersOrdered work)
    (known : TaskAt work occurrence owners (some producer) payload)
    (member : key ∈ owners) (healthy : ¬NodeFailed work failed key)
    (active : ¬TaskCancelled work failed occurrence)
    : ∃ parentOwners ancestor result parentKey,
        TaskAt work producer parentOwners ancestor result
        ∧ parentKey ∈ parentOwners
        ∧ ¬NodeFailed work failed parentKey
        ∧ parentKey ≤ key := by
  cases StructuralEquivalence.taskAt_of_current known with
  | executionGroup located =>
      obtain ⟨group, inGroups, rfl⟩ := List.mem_map.mp member
      obtain ⟨parentOwners, ancestor, result, parentKnown, support⟩ :=
        producer_key_context coherent continuous ordered located.toCurrent
      rcases support with ⟨under, before⟩ | ⟨parentKey, same, fresh⟩
      · obtain ⟨parentKey, inOwners, reused | dependency⟩ := under.1 group inGroups
        · exact ⟨parentOwners, ancestor, result, parentKey, parentKnown, inOwners,
            reused ▸ healthy, Nat.le_of_eq reused⟩
        · have localWork := coherent_located coherent located.toCurrent
          rw [MixedKeys.WorkAt] at localWork
          obtain ⟨_, keyBound, ancestors⟩ := localWork.2.1 group inGroups
          have parentHealthy : ¬NodeFailed work failed parentKey := by
            intro failed
            apply healthy
            exact .groupDependency (.group located.toCurrent inGroups)
              (by simpa only [ancestors] using dependency) failed
          exact ⟨parentOwners, ancestor, result, parentKey, parentKnown, inOwners,
            parentHealthy, Nat.le_of_lt (valid group.node.key keyBound parentKey dependency).1⟩
      · subst parentOwners
        have parentHealthy := healthy_producer_owner known parentKnown (by simp) active
        obtain ⟨healthyKey, inOwners, parentHealthy⟩ := parentHealthy
        have equal := List.mem_singleton.mp inOwners
        subst healthyKey
        rw [MixedKeys.WorkAt] at fresh
        exact ⟨[parentKey], ancestor, result, parentKey, parentKnown, by simp,
          parentHealthy, Nat.le_trans (Nat.le_succ _) (fresh.2.1 group inGroups).1⟩
  | item located selected =>
      have equal := List.mem_singleton.mp member
      subst key
      obtain ⟨parentOwners, ancestor, result, parentKnown, support⟩ :=
        producer_key_context coherent continuous ordered located.toCurrent
      obtain ⟨parentKey, inOwners, parentHealthy⟩ := healthy_producer_owner known parentKnown
        (coherent_task_owners_nonempty coherent parentKnown) active
      refine ⟨parentOwners, ancestor, result, parentKey, parentKnown, inOwners,
        parentHealthy, ?_⟩
      rcases support with ⟨under, before⟩ | ⟨key, same, fresh⟩
      · exact Nat.le_of_lt (before parentKey inOwners)
      · subst parentOwners
        have equal := List.mem_singleton.mp inOwners
        subst parentKey
        rw [MixedKeys.WorkAt] at fresh
        exact Nat.le_trans (Nat.le_succ _) fresh.1

/-- Outstanding work with a healthy owner can find a ready task with a no-larger healthy
owner. Witness: dependency-rank descent, retaining the key bound through producer support
and the shared owner list of successive stream items. No publication order is selected.
-/
theorem readyTask_owner_key_le
    {parents bound work matching events failed occurrence owners producer payload key}
    (valid : Valid parents bound) (coherent : MixedKeys.WorkAt parents 0 bound work)
    (continuous : DeferContinuous parents work) (ordered : StreamOwnersOrdered work)
    (known : TaskAt work occurrence owners producer payload)
    (member : key ∈ owners) (healthy : ¬NodeFailed work failed key)
    (outstanding : ¬Accounted work matching events failed occurrence)
    : ∃ next nextOwners nextProducer result nextKey,
        TaskAt work next nextOwners nextProducer result
        ∧ CanPublish work matching events failed next nextProducer
        ∧ nextKey ∈ nextOwners
        ∧ ¬NodeFailed work failed nextKey
        ∧ nextKey ≤ key := by
  classical
  induction rank : occurrence.dependencyRank
    using Nat.strongRecOn generalizing occurrence owners producer payload key with
  | ind rank ih =>
      have active : ¬TaskCancelled work failed occurrence := fun cancelled =>
        outstanding (Or.inl cancelled)
      have fresh : ¬Published matching events occurrence := fun published =>
        outstanding (Or.inr published)
      by_cases generated :
        ∀ parent, producer = some parent → Published matching events parent
      · cases occurrence with
        | executionGroup address =>
            exact ⟨_, _, _, _, key, known, ⟨fresh, active, generated, trivial⟩,
              member, healthy, Nat.le_refl _⟩
        | item address index =>
            cases index with
            | zero => exact ⟨_, _, _, _, key, known, ⟨fresh, active, generated, trivial⟩,
                member, healthy, Nat.le_refl _⟩
            | succ index =>
                obtain ⟨previous, prior⟩ := known.predecessor
                by_cases accounted :
                  Accounted work matching events failed (.item address index)
                · rcases accounted with cancelled | published
                  · exact False.elim (active (cancelled.same_prerequisites prior known))
                  · exact ⟨_, _, _, _, key, known, ⟨fresh, active, generated, published⟩,
                      member, healthy, Nat.le_refl _⟩
                · exact ih (Occurrence.item address index).dependencyRank
                    (by simp only [Occurrence.dependencyRank] at rank ⊢; omega)
                    prior member healthy accounted rfl
      · obtain ⟨parent, produces, unpublished⟩ := Classical.not_forall.mp generated
          |>.imp fun _ h => not_imp.mp h
        subst producer
        obtain ⟨parentOwners, ancestor, result, parentKey, parentKnown, inOwners,
          parentHealthy, keyBound⟩ := producer_owner_key_le valid coherent continuous ordered
            known member healthy active
        have lower := known.producer_dependency.1
        have unaccounted : ¬Accounted work matching events failed parent := by
          rintro (cancelled | published)
          · exact active (.producerCancelled known cancelled)
          · exact unpublished published
        obtain ⟨next, nextOwners, nextProducer, result, nextKey,
          task, ready, nextMember, nextHealthy, smaller⟩ :=
            ih parent.dependencyRank (by omega) parentKnown inOwners parentHealthy unaccounted rfl
        exact ⟨next, nextOwners, nextProducer, result, nextKey,
          task, ready, nextMember, nextHealthy, Nat.le_trans smaller keyBound⟩

-----------------------------------------------------------------------------------------
-- Every explicit node dependency has a smaller key
-----------------------------------------------------------------------------------------

/-- Empty enclosing-owner lists impose no stream-order constraint. Witness: append
descent until an execution-group boundary or a vacuous stream-owner check.
-/
private theorem ownersBefore_nil (work : Work) : OwnersBefore [] work := by
  cases work with
  | empty | executionGroup => trivial
  | combine left right => exact ⟨ownersBefore_nil left, ownersBefore_nil right⟩
  | stream => simp [OwnersBefore]
termination_by sizeOf work

/-- The enclosing owners recorded by structural lookup precede a stream in that context.
Witness: inherited append context, deferred-owner ordering, or the empty stream-item reset.
-/
theorem ownersBefore_located {work address current producer owners}
    (ordered : StreamOwnersOrdered work)
    (located : Located work address current producer owners)
    : OwnersBefore owners current := by
  have navigation := StructuralEquivalence.located_of_current located
  clear located
  have localOrder {address current producer owners}
      (navigation : StructuralEquivalence.Located work address current producer owners)
      : StreamOwnersOrdered current := by
    induction navigation with
    | root => exact ordered
    | left _ ih =>
        rw [StreamOwnersOrdered] at ih; exact ih.1
    | right _ ih | executionGroup _ ih =>
        rw [StreamOwnersOrdered] at ih; exact ih.2
    | item _ selected ih =>
        rw [StreamOwnersOrdered] at ih
        exact ih _ (List.mem_of_getElem? selected)
  induction navigation with
  | root => exact ownersBefore_nil _
  | left _ ih => exact ih.1
  | right _ ih => exact ih.2
  | executionGroup navigation =>
      have properties := localOrder navigation
      rw [StreamOwnersOrdered] at properties
      exact properties.1
  | item => exact ownersBefore_nil _

/-- Every stream's explicit enclosing-owner dependency has a smaller key. Witness:
the located owner's ordering certificate at its exact stream boundary.
-/
theorem coherent_stream_dependencies {work node dependencies birth}
    (ordered : StreamOwnersOrdered work)
    (known : NodeAt work node .stream dependencies birth)
    : ∀ key ∈ dependencies, key < node.key := by
  obtain ⟨address, items, located⟩ := known
  exact ownersBefore_located ordered located

end GraphQL.IncrementalDelivery.Correctness
