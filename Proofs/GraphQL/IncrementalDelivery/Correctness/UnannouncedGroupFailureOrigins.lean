import Proofs.GraphQL.IncrementalDelivery.Correctness.GroupFailurePositivity
import Proofs.GraphQL.IncrementalDelivery.Correctness.ReportingAccounting
import Proofs.GraphQL.IncrementalDelivery.Correctness.OwnerScopeInheritance

/-! Unannounced failed groups reduce to failed ancestors or unavailable producers. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open Semantics.Ancestry Semantics.GeneralScheduling
open WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- A covered failed group cannot hide a ready, produced contributor failure
-----------------------------------------------------------------------------------------

/-- An unannounced failed group has a failed ancestor or an unpublished producer.
Witness: with healthy satisfied ancestors and an available producer, absence of a recorded
contributor failure would make the group healthy; presence would require its retained
notice at the reporting frontier. Neither branch assumes terminal reporting.
-/
theorem Explains.unannounced_group_failure_origin
    {ancestry bound roles work groups streams events matching failures node dependencies
      producer}
    (coherent : MixedRefs.WorkAt ancestry 0 bound work)
    (roleCoherent : RefRoles.WorkRoles roles work)
    (explained : Explains work groups streams events matching failures)
    (covered
      : GroupNoticesCovered work ((groups ++ streams).map DeliveryNode.ref) matching
          events failures)
    (satisfied
      : ∀ ref,
          ¬NodeFailed work matching events failures ref
          → DependencySatisfied work ((groups ++ streams).map DeliveryNode.ref) matching
              events failures ref)
    (known : NodeAt work node .group dependencies producer)
    (fresh : node.ref ∉ announcedRefs ((groups ++ streams).map DeliveryNode.ref) events)
    (failed : NodeFailed work matching events failures node.ref)
    : (∃ ref ∈ dependencies, NodeFailed work matching events failures ref)
      ∨ ∃ source, producer = some source ∧ ¬Published matching events source := by
  classical
  by_cases ancestor : ∃ ref ∈ dependencies, NodeFailed work matching events failures ref
  · exact Or.inl ancestor
  have healthy : ∀ ref ∈ dependencies, ¬NodeFailed work matching events failures ref := by
    intro ref member failed
    exact ancestor ⟨ref, member, failed⟩
  by_cases available : ∀ source, producer = some source → Published matching events source
  · have recorded : HasRecordedFailure work failures events.length node.ref := by
      apply Classical.byContradiction
      intro absent
      exact Explains.group_healthy_of_no_recorded_failure coherent roleCoherent explained
        known absent available healthy failed
    exact False.elim (fresh (covered.recorded_group_announced known recorded available
      (fun ref member => satisfied ref (healthy ref member))))
  · right
    cases producer with
    | none => exact False.elim (available (by intro source impossible; cases impossible))
    | some source =>
        refine ⟨source, rfl, ?_⟩
        intro published
        exact available (by intro other same; cases Option.some.inj same; exact published)

-----------------------------------------------------------------------------------------
-- Reduce inherited defer failure without assuming a report for every group scope
-----------------------------------------------------------------------------------------

/-- A failed contributing group either reports this task or has an unavailable ancestral
producer. Witness: strong ref descent through the full defer ancestry. Announced groups
give actual positive completion scopes, whose generated paths cover the original task;
unannounced groups use the reporting-frontier origin classifier. This keeps task-local
coverage separate from a stronger, generally unwarranted full-group-scope claim.
-/
theorem Explains.failed_owner_reported_or_unavailable_ancestor
    {ancestry bound roles paths pathBound work groups streams events matching failures
      address owners producer payload owner dependencies birth}
    (valid : Valid ancestry bound) (coherent : MixedRefs.WorkAt ancestry 0 bound work)
    (roleCoherent : RefRoles.WorkRoles roles work)
    (pathCoherent : MixedOwnerPaths.WorkAt paths pathBound work)
    (positive : ExecutionErrors.WorkPositive work)
    (explained : Explains work groups streams events matching failures)
    (covered
      : GroupNoticesCovered work ((groups ++ streams).map DeliveryNode.ref) matching
          events failures)
    (satisfied
      : ∀ ref,
          ¬NodeFailed work matching events failures ref
          → DependencySatisfied work ((groups ++ streams).map DeliveryNode.ref) matching
              events failures ref)
    (closedRefs
      : ∀ ref ∈ announcedRefs ((groups ++ streams).map DeliveryNode.ref) events,
          ref ∈ completedRefs events)
    (known : TaskAt work (.executionGroup address) owners producer payload)
    (ownerKnown : NodeAt work owner .group dependencies birth)
    (contributes : owner.ref ∈ owners)
    (failed : NodeFailed work matching events failures owner.ref)
    : FailureReportedFor events payload.path
      ∨ ∃ ancestor parents source,
          NodeAt work ancestor .group parents (some source)
          ∧ (ancestor.ref = owner.ref ∨ ancestor.ref ∈ dependencies)
          ∧ NodeFailed work matching events failures ancestor.ref
          ∧ ¬Published matching events source := by
  have canonical : ∀ node dependencies producer,
      NodeAt work node .group dependencies producer → dependencies = ancestry node.ref :=
    fun _ _ _ known => DeferOnly.node_dependencies coherent known
  have descend : ∀ ref, ∀ node parents source,
      NodeAt work node .group parents source
      → node.ref = ref
      → (ref = owner.ref ∨ ref ∈ dependencies)
      → NodeFailed work matching events failures ref
      → FailureReportedFor events payload.path
        ∨ ∃ ancestor parents source,
            NodeAt work ancestor .group parents (some source)
            ∧ (ancestor.ref = owner.ref ∨ ancestor.ref ∈ dependencies)
            ∧ NodeFailed work matching events failures ancestor.ref
            ∧ ¬Published matching events source := by
    intro ref
    induction ref using Nat.strongRecOn with
    | ind ref ih =>
        intro node parents source descriptor same related failed
        have nodeFailed : NodeFailed work matching events failures node.ref := same ▸ failed
        by_cases announced
          : node.ref ∈ announcedRefs ((groups ++ streams).map DeliveryNode.ref) events
        · have reported := Explains.announced_failed_group_reports_scope valid coherent
            roleCoherent pathCoherent positive explained closedRefs descriptor announced
            nodeFailed
          left
          rcases related with direct | ancestor
          · have sameOwner := same.trans direct
            have path := workAt_same_path pathCoherent descriptor ownerKnown sameOwner
            rw [path] at reported
            exact reported_owner_covers_task pathCoherent known ownerKnown contributes
              reported
          · exact reported_owner_ancestor_covers_task pathCoherent canonical known
              ownerKnown contributes descriptor (same.symm ▸ ancestor) reported
        · rcases Explains.unannounced_group_failure_origin coherent roleCoherent explained
            covered satisfied descriptor announced nodeFailed with ancestor | unavailable
          · obtain ⟨parent, member, failedParent⟩ := ancestor
            have full := canonical _ _ _ descriptor
            have bounded := (coherent_node_bounds coherent descriptor).2
            have prior := valid node.ref bounded parent (full ▸ member)
            obtain ⟨ancestor, kind, dependencies', birth', known', parentRef⟩ :=
              Explains.failed_node_known explained failedParent
            have group : kind = .group := by
              have role := node_ref_role roleCoherent known'
              have parentRole := group_dependency_role roleCoherent descriptor member
              rw [parentRef, parentRole] at role
              cases kind with
              | group => rfl
              | stream => cases role
            subst kind
            apply ih parent (by simpa only [same] using prior.1) ancestor dependencies'
              birth' known' parentRef ?_ failedParent
            right
            rcases related with direct | above
            · have original := canonical _ _ _ ownerKnown
              simpa only [full, same, direct, original] using member
            · have original := canonical _ _ _ ownerKnown
              have higher := valid owner.ref (coherent_node_bounds coherent ownerKnown).2
                ref (original ▸ above)
              rw [original]
              have parentMember : parent ∈ ancestry node.ref := full ▸ member
              exact higher.2 (by simpa only [same] using parentMember)
          · obtain ⟨birth, eq, unpublished⟩ := unavailable
            right
            exact ⟨node, parents, birth, eq ▸ descriptor, same ▸ related, nodeFailed,
              unpublished⟩
  exact descend owner.ref owner dependencies birth ownerKnown rfl (Or.inl rfl) failed

/-- Failed contributing groups with root descriptors report their task attachments even
when some groups were never announced. Witness: ancestor reduction cannot end at an
unavailable producer, because every represented group has no structural producer.
The group dependency graph may still be nonempty; the reporting frontier handles it.
-/
theorem Explains.failed_owner_reported_of_root_groups
    {ancestry bound roles paths pathBound work groups streams events matching failures
      address owners producer payload owner dependencies birth}
    (valid : Valid ancestry bound) (coherent : MixedRefs.WorkAt ancestry 0 bound work)
    (roleCoherent : RefRoles.WorkRoles roles work)
    (pathCoherent : MixedOwnerPaths.WorkAt paths pathBound work)
    (positive : ExecutionErrors.WorkPositive work)
    (explained : Explains work groups streams events matching failures)
    (covered
      : GroupNoticesCovered work ((groups ++ streams).map DeliveryNode.ref) matching
          events failures)
    (satisfied
      : ∀ ref,
          ¬NodeFailed work matching events failures ref
          → DependencySatisfied work ((groups ++ streams).map DeliveryNode.ref) matching
              events failures ref)
    (closedRefs
      : ∀ ref ∈ announcedRefs ((groups ++ streams).map DeliveryNode.ref) events,
          ref ∈ completedRefs events)
    (roots
      : ∀ node dependencies producer,
          NodeAt work node .group dependencies producer → producer = none)
    (known : TaskAt work (.executionGroup address) owners producer payload)
    (ownerKnown : NodeAt work owner .group dependencies birth)
    (contributes : owner.ref ∈ owners)
    (failed : NodeFailed work matching events failures owner.ref)
    : FailureReportedFor events payload.path := by
  rcases Explains.failed_owner_reported_or_unavailable_ancestor valid coherent roleCoherent
    pathCoherent positive explained covered satisfied closedRefs known ownerKnown
    contributes failed with reported | unavailable
  · exact reported
  · obtain ⟨ancestor, parents, source, descriptor, _⟩ := unavailable
    cases roots ancestor parents (some source) descriptor

end GraphQL.IncrementalDelivery.Correctness
