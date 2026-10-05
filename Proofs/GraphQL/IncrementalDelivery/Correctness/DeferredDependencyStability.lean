import Proofs.GraphQL.IncrementalDelivery.Correctness.GroupProducerAvailability
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.SettlementCarrierBoundaries

/-! Full satisfied defer ancestry remains healthy during one explained observation.
Silent accounting alone does not supply the required full-ancestor support.
-/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open Semantics.Ancestry Semantics.GeneralScheduling
open WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- All supported ancestors exclude future direct and inherited group failures
-----------------------------------------------------------------------------------------

/-- A satisfied defer ref stays healthy even before the carrier's next settlements.
Witness: strong ref induction. Healthy accounting excludes later direct settlements and
retains a root or published producer; full transitive ancestry supplies the same facts for
every possible failed dependency. Stream-role failures are excluded by generated ref roles.
The earlier explanation retains exactly the cuts through `cutoff`, and its output prefix
ends no later than the next boundary. Equal-boundary settlements retain their licensing
order instead of being retroactively inserted into the carrier's notice checks.
-/
theorem Explains.supported_defer_dependency_stays_healthy_before_next_settlements
    {ancestry bound roles work groups streams events matching failures index cutoff ref}
    (valid : Valid ancestry bound) (coherent : MixedRefs.WorkAt ancestry 0 bound work)
    (roleCoherent : RefRoles.WorkRoles roles work)
    (explained : Explains work groups streams events matching failures)
    (shorter
      : Explains work groups streams (events.take index) matching
          (failures.filter (fun entry => entry.1 ≤ cutoff)))
    (adjacent : index ≤ cutoff + 1)
    (role : roles ref = false)
    (satisfied
      : ¬NodeFailed work matching (events.take index)
          (failures.filter (fun entry => entry.1 ≤ cutoff)) ref
        ∧ NodeAccounted work matching (events.take index)
            (failures.filter (fun entry => entry.1 ≤ cutoff)) ref)
    (ancestors
      : ∀ parent ∈ ancestry ref,
          ¬NodeFailed work matching (events.take index)
            (failures.filter (fun entry => entry.1 ≤ cutoff)) parent
          ∧ NodeAccounted work matching (events.take index)
              (failures.filter (fun entry => entry.1 ≤ cutoff)) parent)
    : ¬NodeFailed work matching events failures ref := by
  induction ref using Nat.strongRecOn with
  | ind ref ih =>
      intro failed
      obtain ⟨node, kind, dependencies, producer, known, same⟩ :=
        Explains.failed_node_known explained failed
      have group : kind = .group := by
        have nodeRole := node_ref_role roleCoherent known
        rw [same, role] at nodeRole
        cases kind with
        | group => rfl
        | stream => cases nodeRole
      subst kind
      have accounted := satisfied.2
      have oldHealthy : ¬NodeFailed work matching (events.take index)
          (failures.filter (fun entry => entry.1 ≤ cutoff)) node.ref := by
        simpa only [same] using satisfied.1
      have oldAccounted : NodeAccounted work matching (events.take index)
          (failures.filter (fun entry => entry.1 ≤ cutoff)) node.ref := by
        simpa only [same] using accounted
      obtain ⟨birth, descriptor, available⟩ :=
        Explains.healthy_group_accounted_producer_available roleCoherent shorter known
          oldHealthy oldAccounted
      have noRecord :=
        explained.healthy_accounted_no_recorded_failure_before_next_settlements adjacent
          satisfied.1 accounted
      have snapshot := explained.nodeFailed_snapshot failed
      cases snapshot with
      | task projected member recorded =>
          exact noRecord ⟨_, _, recorded, projected, member⟩
      | groupDependency projected member failure =>
          obtain ⟨owner, source, descriptor, ownerRef⟩ := projected
          have full := DeferOnly.node_dependencies coherent descriptor
          have included := member
          rw [full, ownerRef] at included
          have bounded := (coherent_node_bounds coherent descriptor).2
          have before := valid owner.ref bounded _ (by simpa only [ownerRef] using included)
          apply ih _ (by simpa only [ownerRef] using before.1)
            (by
              simpa only [ownerRef]
                using group_dependency_role roleCoherent descriptor member)
            (ancestors _ included)
            (fun parent selected =>
              ancestors parent (by simpa only [ownerRef] using before.2 selected))
          exact explained.snapshot_nodeFailed failure
      | streamDependencies projected _ _ =>
          obtain ⟨stream, source, descriptor, streamRef⟩ := projected
          have streamRole := node_ref_role roleCoherent descriptor
          rw [streamRef, role] at streamRole
          cases streamRole
      | producers _ noRoot unpublished _ =>
          rw [same] at descriptor
          cases birth with
          | none => exact noRoot descriptor
          | some source =>
              apply unpublished source descriptor
              simpa only [List.take_append_drop]
                using (available source rfl).append (events.drop index)

/-- A satisfied defer ref and its satisfied ancestry stay healthy in one explained history.
Witness: the carrier-boundary theorem specialized to all cuts visible at the chosen prefix.
The publication matching and failure inventory belong to the same explained history.
-/
theorem Explains.supported_defer_dependency_stays_healthy
    {ancestry bound roles work groups streams events matching failures index ref}
    (valid : Valid ancestry bound) (coherent : MixedRefs.WorkAt ancestry 0 bound work)
    (roleCoherent : RefRoles.WorkRoles roles work)
    (explained : Explains work groups streams events matching failures)
    (role : roles ref = false)
    (satisfied
      : DependencySatisfied work ((groups ++ streams).map DeliveryNode.ref) matching
          (events.take index) failures ref)
    (ancestors
      : ∀ parent ∈ ancestry ref,
          DependencySatisfied work ((groups ++ streams).map DeliveryNode.ref) matching
            (events.take index) failures parent)
    : ¬NodeFailed work matching events failures ref := by
  let oldIndex := (events.take index).length
  have same : events.take oldIndex = events.take index := by
    by_cases bounded : index ≤ events.length
    · simp only [oldIndex, List.length_take, Nat.min_eq_left bounded]
    · have reached : events.length ≤ index := by omega
      simp only [oldIndex, List.length_take, Nat.min_eq_right reached,
        List.take_length, List.take_of_length_le reached]
  have combined : Explains work groups streams (events.take oldIndex ++ events.drop oldIndex)
      matching failures := by simpa only [List.take_append_drop] using explained
  have shorter := combined.prefix
  have bounded : oldIndex ≤ events.length := by simp only [oldIndex, List.length_take]; omega
  rw [List.length_take_of_le bounded] at shorter
  have accounting (ref) (supported
      : DependencySatisfied work ((groups ++ streams).map DeliveryNode.ref) matching
          (events.take oldIndex) (failures.filter (fun entry => entry.1 ≤ oldIndex)) ref)
      : NodeAccounted work matching (events.take oldIndex)
          (failures.filter (fun entry => entry.1 ≤ oldIndex)) ref := by
    rcases supported.2 with absent | closed | ⟨_, accounted⟩
    · intro occurrence owners ⟨producer, payload, known⟩ member
      obtain ⟨node, kind, dependencies, birth, descriptor, same⟩ := known.owner_known member
      exact False.elim (absent ⟨birth, node, kind, dependencies, descriptor, same⟩)
    · exact (shorter.completed_accounted closed).resolve_left supported.1
    · exact accounted
  apply Explains.supported_defer_dependency_stays_healthy_before_next_settlements
    (index := oldIndex) (cutoff := oldIndex) valid coherent roleCoherent explained shorter
    (by omega) role
  · have supported : DependencySatisfied work ((groups ++ streams).map DeliveryNode.ref)
        matching (events.take oldIndex) (failures.filter (fun entry => entry.1 ≤ oldIndex))
        ref := by
      simpa only [DependencySatisfied, same,
        nodeFailed_filter (events := events.take index) (bound := oldIndex)
          (Nat.le_refl _), NodeAccounted, TaskAccounted,
        taskCancelled_filter (events := events.take index) (bound := oldIndex) (Nat.le_refl _)]
        using satisfied
    exact ⟨supported.1, accounting ref supported⟩
  · intro parent member
    have supported : DependencySatisfied work ((groups ++ streams).map DeliveryNode.ref)
        matching (events.take oldIndex) (failures.filter (fun entry => entry.1 ≤ oldIndex))
        parent := by
      simpa only [DependencySatisfied, same,
        nodeFailed_filter (events := events.take index) (bound := oldIndex)
          (Nat.le_refl _), NodeAccounted, TaskAccounted,
        taskCancelled_filter (events := events.take index) (bound := oldIndex) (Nat.le_refl _)]
        using ancestors parent member
    exact ⟨supported.1, accounting parent supported⟩

end GraphQL.IncrementalDelivery.Correctness
