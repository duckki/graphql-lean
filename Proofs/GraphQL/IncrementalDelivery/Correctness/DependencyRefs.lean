import Proofs.GraphQL.IncrementalDelivery.Correctness.Initialization
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.TaskReadiness

/-! Execution's existing ref/ancestry certificates order task-producer dependencies.
No readiness, notice coverage, or response-correctness premise is added to admission.
-/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open Semantics.Ancestry Semantics.GeneralScheduling
open WorkQueueSemantics

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
fresh stream-item ref region. Witness: the producer-generating edge, then append descent.
-/
theorem producer_ref_context {parents bound work address current enclosing producer}
    (coherent : MixedRefs.WorkAt parents 0 bound work)
    (continuous : DeferContinuous parents work) (ordered : StreamOwnersOrdered work)
    (located : Located work address current (some producer) enclosing)
    : ∃ owners ancestor payload,
        TaskAt work producer owners ancestor payload
        ∧ ((DeferUnder parents owners current ∧ OwnersBefore owners current)
            ∨ ∃ ref,
                owners = [ref] ∧ MixedRefs.WorkAt parents (ref + 1) bound current) := by
  have context {address current birth enclosing}
      (navigation : StructuralEquivalence.Located work address current birth enclosing)
      {producer} (generated : birth = some producer) :
      ∃ owners ancestor payload,
        TaskAt work producer owners ancestor payload
        ∧ ((DeferUnder parents owners current ∧ OwnersBefore owners current)
          ∨ ∃ ref, owners = [ref] ∧ MixedRefs.WorkAt parents (ref + 1) bound current) := by
    induction navigation with
    | root => contradiction
    | left _ ih =>
        obtain ⟨owners, ancestor, payload, known, supported⟩ := ih generated
        refine ⟨owners, ancestor, payload, known, ?_⟩
        rcases supported with ⟨under, before⟩ | ⟨ref, same, bounded⟩
        · exact Or.inl ⟨under.1, before.1⟩
        · rw [MixedRefs.WorkAt] at bounded
          exact Or.inr ⟨ref, same, bounded.1⟩
    | right _ ih =>
        obtain ⟨owners, ancestor, payload, known, supported⟩ := ih generated
        refine ⟨owners, ancestor, payload, known, ?_⟩
        rcases supported with ⟨under, before⟩ | ⟨ref, same, bounded⟩
        · exact Or.inl ⟨under.2, before.2⟩
        · rw [MixedRefs.WorkAt] at bounded
          exact Or.inr ⟨ref, same, bounded.2⟩
    | executionGroup navigation =>
        cases generated
        have properties := dependencyProperties_located continuous ordered navigation.toCurrent
        simp only [DeferContinuous, StreamOwnersOrdered] at properties
        exact ⟨_, _, _, .executionGroup navigation.toCurrent,
          Or.inl ⟨properties.1.1, properties.2.1⟩⟩
    | item navigation selected =>
        cases generated
        have localWork := coherent_located coherent navigation.toCurrent
        rw [MixedRefs.WorkAt] at localWork
        exact ⟨_, _, _, .item navigation.toCurrent selected,
          Or.inr ⟨_, rfl, localWork.2.2 _ (List.mem_of_getElem? selected)⟩⟩
  exact context (StructuralEquivalence.located_of_current located) rfl

/-- Generated task owner lists are nonempty at every structural occurrence.
Witness: nonempty deferred maps or a stream item's singleton owner list.
-/
theorem coherent_task_owners_nonempty
    {parents lower bound work occurrence owners producer payload}
    (coherent : MixedRefs.WorkAt parents lower bound work)
    (known : TaskAt work occurrence owners producer payload)
    : owners ≠ [] := by
  cases StructuralEquivalence.taskAt_of_current known with
  | executionGroup located =>
      have localWork := coherent_located coherent located.toCurrent
      rw [MixedRefs.WorkAt] at localWork
      exact fun empty => localWork.1 (List.map_eq_nil_iff.mp empty)
  | item => simp

/-- An unpublished, uncancelled child with an unpublished producer has a healthy producer
owner. Witness: combine failures at the admitted current snapshot, then cancel both tasks.
-/
theorem healthy_producer_owner
    {work groups streams matching events failed
      occurrence owners producer payload parentOwners ancestor result}
    (explained : Explains work groups streams events matching failed)
    (known : TaskAt work occurrence owners (some producer) payload)
    (parentKnown : TaskAt work producer parentOwners ancestor result)
    (nonempty : parentOwners ≠ [])
    (fresh : ¬Published matching events occurrence)
    (parentFresh : ¬Published matching events producer)
    (active : ¬TaskCancelled work matching events failed occurrence)
    : ∃ ref ∈ parentOwners, ¬NodeFailed work matching events failed ref := by
  classical
  apply Classical.byContradiction
  intro absent
  apply active
  apply explained.snapshot_taskCancelled
  apply Causality.TaskCancelled.producerCancelled ⟨_, _, known⟩ fresh
  apply Causality.TaskCancelled.owners ⟨_, _, parentKnown⟩ parentFresh nonempty
  intro ref member
  apply explained.nodeFailed_snapshot
  apply Classical.byContradiction
  intro healthy
  exact absent ⟨ref, member, healthy⟩

-----------------------------------------------------------------------------------------
-- A healthy child owner is supported by a no-larger healthy producer owner
-----------------------------------------------------------------------------------------

/-- Every healthy contributing ref of an uncancelled generated child task has a healthy
producer owner with a no-larger ref. Witness: reused/dependent defer ancestry, ordered
stream owners, or the fresh ref interval below a stream item. This prevents a producer
dependency from forcing progress through a strictly later owner ref.
-/
theorem producer_owner_ref_le
    {parents bound work groups streams matching events failed
      occurrence owners producer payload ref}
    (explained : Explains work groups streams events matching failed)
    (valid : Valid parents bound) (coherent : MixedRefs.WorkAt parents 0 bound work)
    (continuous : DeferContinuous parents work) (ordered : StreamOwnersOrdered work)
    (known : TaskAt work occurrence owners (some producer) payload)
    (member : ref ∈ owners) (healthy : ¬NodeFailed work matching events failed ref)
    (fresh : ¬Published matching events occurrence)
    (parentFresh : ¬Published matching events producer)
    (active : ¬TaskCancelled work matching events failed occurrence)
    : ∃ parentOwners ancestor result parentRef,
        TaskAt work producer parentOwners ancestor result
        ∧ parentRef ∈ parentOwners
        ∧ ¬NodeFailed work matching events failed parentRef
        ∧ parentRef ≤ ref := by
  cases StructuralEquivalence.taskAt_of_current known with
  | executionGroup located =>
      obtain ⟨group, inGroups, rfl⟩ := List.mem_map.mp member
      obtain ⟨parentOwners, ancestor, result, parentKnown, support⟩ :=
        producer_ref_context coherent continuous ordered located.toCurrent
      rcases support with ⟨under, before⟩ | ⟨parentRef, same, freshRefs⟩
      · obtain ⟨parentRef, inOwners, reused | dependency⟩ := under.1 group inGroups
        · exact ⟨parentOwners, ancestor, result, parentRef, parentKnown, inOwners,
            reused ▸ healthy, Nat.le_of_eq reused⟩
        · have localWork := coherent_located coherent located.toCurrent
          rw [MixedRefs.WorkAt] at localWork
          obtain ⟨_, refBound, ancestors⟩ := localWork.2.1 group inGroups
          have parentHealthy : ¬NodeFailed work matching events failed parentRef := by
            intro failed
            apply healthy
            exact .groupDependency (.group located.toCurrent inGroups)
              (by simpa only [ancestors] using dependency) failed
          exact ⟨parentOwners, ancestor, result, parentRef, parentKnown, inOwners,
            parentHealthy, Nat.le_of_lt (valid group.node.ref refBound parentRef dependency).1⟩
      · subst parentOwners
        have parentHealthy := healthy_producer_owner explained known parentKnown
          (by simp) fresh parentFresh active
        obtain ⟨healthyRef, inOwners, parentHealthy⟩ := parentHealthy
        have equal := List.mem_singleton.mp inOwners
        subst healthyRef
        rw [MixedRefs.WorkAt] at freshRefs
        exact ⟨[parentRef], ancestor, result, parentRef, parentKnown, by simp,
          parentHealthy, Nat.le_trans (Nat.le_succ _) (freshRefs.2.1 group inGroups).1⟩
  | item located selected =>
      have equal := List.mem_singleton.mp member
      subst ref
      obtain ⟨parentOwners, ancestor, result, parentKnown, support⟩ :=
        producer_ref_context coherent continuous ordered located.toCurrent
      obtain ⟨parentRef, inOwners, parentHealthy⟩ :=
        healthy_producer_owner explained known parentKnown
          (coherent_task_owners_nonempty coherent parentKnown) fresh parentFresh active
      refine ⟨parentOwners, ancestor, result, parentRef, parentKnown, inOwners,
        parentHealthy, ?_⟩
      rcases support with ⟨under, before⟩ | ⟨ref, same, fresh⟩
      · exact Nat.le_of_lt (before parentRef inOwners)
      · subst parentOwners
        have equal := List.mem_singleton.mp inOwners
        subst parentRef
        rw [MixedRefs.WorkAt] at fresh
        exact Nat.le_trans (Nat.le_succ _) fresh.1

/-- Outstanding work with a healthy owner can find a ready task with a no-larger healthy
owner. Witness: dependency-rank descent, retaining the ref bound through producer support
and the shared owner list of successive stream items. No publication order is selected.
-/
theorem readyTask_owner_ref_le
    {parents bound work groups streams matching events failed
      occurrence owners producer payload ref}
    (explained : Explains work groups streams events matching failed)
    (valid : Valid parents bound) (coherent : MixedRefs.WorkAt parents 0 bound work)
    (continuous : DeferContinuous parents work) (ordered : StreamOwnersOrdered work)
    (known : TaskAt work occurrence owners producer payload)
    (member : ref ∈ owners) (healthy : ¬NodeFailed work matching events failed ref)
    (outstanding : ¬TaskAccounted work matching events failed occurrence)
    : ∃ next nextOwners nextProducer result nextRef,
        TaskAt work next nextOwners nextProducer result
        ∧ CanPublish work matching events failed next nextProducer
        ∧ nextRef ∈ nextOwners
        ∧ ¬NodeFailed work matching events failed nextRef
        ∧ nextRef ≤ ref := by
  classical
  induction rank : occurrence.dependencyRank
    using Nat.strongRecOn generalizing occurrence owners producer payload ref with
  | ind rank ih =>
      have active : ¬TaskCancelled work matching events failed occurrence := fun cancelled =>
        outstanding (Or.inl cancelled)
      have fresh : ¬Published matching events occurrence := fun published =>
        outstanding (Or.inr published)
      by_cases generated :
        ∀ parent, producer = some parent → Published matching events parent
      · cases occurrence with
        | executionGroup address =>
            exact ⟨_, _, _, _, ref, known, ⟨fresh, active, generated, trivial⟩,
              member, healthy, Nat.le_refl _⟩
        | item address index =>
            cases index with
            | zero => exact ⟨_, _, _, _, ref, known, ⟨fresh, active, generated, trivial⟩,
                member, healthy, Nat.le_refl _⟩
            | succ index =>
                obtain ⟨previous, prior⟩ := known.predecessor
                by_cases accounted :
                  TaskAccounted work matching events failed (.item address index)
                · rcases accounted with cancelled | published
                  · exact False.elim (active (cancelled.same_prerequisites prior known fresh))
                  · exact ⟨_, _, _, _, ref, known, ⟨fresh, active, generated, published⟩,
                      member, healthy, Nat.le_refl _⟩
                · exact ih (Occurrence.item address index).dependencyRank
                    (by simp only [Occurrence.dependencyRank] at rank ⊢; omega)
                    prior member healthy accounted rfl
      · obtain ⟨parent, produces, unpublished⟩ := Classical.not_forall.mp generated
          |>.imp fun _ h => not_imp.mp h
        subst producer
        obtain ⟨parentOwners, ancestor, result, parentRef, parentKnown, inOwners,
          parentHealthy, refBound⟩ :=
          producer_owner_ref_le explained valid coherent continuous ordered
            known member healthy fresh unpublished active
        have lower := known.producer_dependency.1
        have unaccounted : ¬TaskAccounted work matching events failed parent := by
          rintro (cancelled | published)
          · exact active (.producerCancelled known fresh cancelled)
          · exact unpublished published
        obtain ⟨next, nextOwners, nextProducer, result, nextRef,
          task, ready, nextMember, nextHealthy, smaller⟩ :=
            ih parent.dependencyRank (by omega) parentKnown inOwners parentHealthy unaccounted rfl
        exact ⟨next, nextOwners, nextProducer, result, nextRef,
          task, ready, nextMember, nextHealthy, Nat.le_trans smaller refBound⟩

-----------------------------------------------------------------------------------------
-- Every explicit node dependency has a smaller ref
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

/-- Every stream's explicit enclosing-owner dependency has a smaller ref. Witness:
the located owner's ordering certificate at its exact stream boundary.
-/
theorem coherent_stream_dependencies {work node dependencies birth}
    (ordered : StreamOwnersOrdered work)
    (known : NodeAt work node .stream dependencies birth)
    : ∀ ref ∈ dependencies, ref < node.ref := by
  obtain ⟨address, items, located⟩ := known
  exact ownersBefore_located ordered located

end GraphQL.IncrementalDelivery.Correctness
