import Proofs.GraphQL.IncrementalDelivery.Correctness.CausalTaskReportAssembly
import Proofs.GraphQL.IncrementalDelivery.Correctness.DependencyRefs

/-! Cancellation reporting below a ref bound uses only earlier failed defer owners. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open Semantics.Ancestry Semantics.GeneralScheduling
open WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Producer and stream dependency edges retain the ref bound during causal induction
-----------------------------------------------------------------------------------------

/-- A cancelled task with an owner below `limit` needs only earlier failed-owner reports.
Witness: mutual causal induction. Structural producer support chooses a no-larger ref;
stream dependencies and stream producers have strictly earlier refs. Deferred branches use
task-local scope reports below the bound, while accepted failures keep their actual reports.
This is the bounded induction step for unpublished group producers, not terminal coverage
or a blanket report assumption about later groups.
-/
theorem snapshot_cancelled_reported_of_bounded_owner_task_scopes
    {ancestry refBound roles base paths pathBound work failed published events limit
      occurrence owners producer payload ref}
    (valid : Valid ancestry refBound)
    (coherent : MixedRefs.WorkAt ancestry 0 refBound work)
    (roleCoherent : RefRoles.WorkRoles roles work)
    (continuous : DeferContinuous ancestry work) (ordered : StreamOwnersOrdered work)
    (pathCoherent : MixedOwnerPaths.WorkAt paths pathBound work)
    (under : ExecutionPaths.WorkUnder base work)
    (ownerTaskReports
      : ∀ address owners producer payload node dependencies birth,
          TaskAt work (.executionGroup address) owners producer payload
          → NodeAt work node .group dependencies birth
          → node.ref ∈ owners
          → node.ref < limit
          → Causality.NodeFailed work failed published node.ref
          → FailureReportedFor events payload.path)
    (taskReports
      : ∀ occurrence ∈ failed,
          ∀ owners producer payload,
            TaskAt work occurrence owners producer payload
            → FailureReportedFor events payload.path)
    (cancelled : Causality.TaskCancelled work failed published occurrence)
    (known : TaskAt work occurrence owners producer payload)
    (member : ref ∈ owners) (bounded : ref < limit)
    : FailureReportedFor events payload.path := by
  revert owners producer payload ref
  induction cancelled
    using Causality.TaskCancelled.rec
      (motive_1 :=
        fun ref _ =>
          ∀ node dependencies birth,
            NodeAt work node .stream dependencies birth
            → node.ref = ref
            → ref < limit
            → FailureReportedFor events node.path) with
  | task projected owner recorded =>
      rename_i node dependencies birth descriptor same bounded
      obtain ⟨taskBirth, taskPayload, task⟩ := projected
      cases StructuralEquivalence.taskAt_of_current task with
      | executionGroup located =>
          obtain ⟨group, member, selected⟩ := List.mem_map.mp owner
          exact False.elim (stream_group_refs_distinct roleCoherent descriptor
            (NodeAt.group located.toCurrent member) (same.trans selected.symm))
      | item located entry =>
          have scope := workAt_same_path pathCoherent (NodeAt.stream located.toCurrent)
            descriptor ((List.mem_singleton.mp owner).symm.trans same.symm)
          simpa only [Payload.path, scope] using taskReports _ recorded _ _ _ task
  | groupDependency projected _ _ _ =>
      rename_i node dependencies birth descriptor same bounded
      obtain ⟨group, source, groupKnown, selected⟩ := projected
      exact False.elim (stream_group_refs_distinct roleCoherent descriptor groupKnown
        (same.trans selected.symm))
  | streamDependencies projected nonempty failures _ =>
      rename_i node dependencies birth descriptor same bounded
      obtain ⟨stream, source, streamKnown, selected⟩ := projected
      obtain ⟨ref, member⟩ := List.exists_mem_of_ne_nil _ nonempty
      obtain ⟨address, ancestor, path, result, generated, task⟩ :=
        stream_dependency_task streamKnown member
      obtain ⟨group, parents, groupKnown, groupSame⟩ := task.executionGroup_owner member
      have earlier := coherent_stream_dependencies ordered streamKnown ref member
      have small : group.ref < limit := by
        rw [groupSame]
        have streamBound : stream.ref < limit := selected ▸ bounded
        exact Nat.lt_trans earlier streamBound
      have report := ownerTaskReports _ _ _ _ _ _ _ task groupKnown
        (groupSame.symm ▸ member) small (groupSame.symm ▸ failures ref member)
      rw [generated] at streamKnown
      obtain ⟨parentOwners, parentBirth, parentPayload, parent, belowStream⟩ :=
        under.stream_producer_under streamKnown
      have parentSame := (task.unique parent).2.2
      have belowStream : path.IsPrefix stream.path := by
        simpa only [← parentSame, Payload.path] using belowStream
      have scope := workAt_same_path pathCoherent streamKnown descriptor
        (selected.trans same.symm)
      exact scope ▸ report.descendant belowStream
  | producers projected noRoot _ _ ih =>
      rename_i node dependencies birth descriptor same bounded
      cases birth with
      | none => exact False.elim (noRoot ⟨node, .stream, dependencies, descriptor, same⟩)
      | some source =>
          have sourceKnown : NodeHasProducer work _ (some source) :=
            ⟨node, .stream, dependencies, descriptor, same⟩
          obtain ⟨owners, ancestor, payload, task, below⟩ :=
            under.stream_producer_under descriptor
          by_cases recorded : source ∈ failed
          · exact (taskReports source recorded owners ancestor payload task).descendant below
          · obtain ⟨parentOwners, parentBirth, parentPayload, parentRef, parent, member,
              earlier⟩ := stream_producer_owner_lt coherent continuous ordered descriptor
            have equal := task.unique parent
            have report := ih source sourceKnown recorded parent member (by
              have nodeBound : node.ref < limit := same ▸ bounded
              exact Nat.lt_trans earlier nodeBound)
            exact (equal.2.2.symm ▸ report).descendant below
  | owners projected _ _ failures ih =>
      intro more birth result ref descriptor member bounded
      obtain ⟨taskBirth, taskPayload, task⟩ := projected
      have contributes : ref ∈ _ := (task.unique descriptor).1.symm ▸ member
      cases StructuralEquivalence.taskAt_of_current task with
      | executionGroup located =>
          obtain ⟨group, included, same⟩ := List.mem_map.mp contributes
          have groupKnown := NodeAt.group located.toCurrent included
          have report := ownerTaskReports _ _ _ _ _ _ _ task groupKnown
            (same.symm ▸ contributes) (same.symm ▸ bounded)
            (same.symm ▸ failures ref contributes)
          exact (task.unique descriptor).2.2 ▸ report
      | item located entry =>
          have sameRef := List.mem_singleton.mp contributes
          have report := ih _ contributes _ _ _ (NodeAt.stream located.toCurrent)
            sameRef.symm bounded
          exact (task.unique descriptor).2.2 ▸ report
  | producerFailed projected _ recorded =>
      intro more birth result ref descriptor member bounded
      obtain ⟨taskOwners, taskPayload, task⟩ := projected
      obtain ⟨owners, ancestor, payload, parent⟩ := task.producer_dependency.2
      have report := (taskReports _ recorded owners ancestor payload parent).descendant
        (under.producer_prefix task parent)
      exact (task.unique descriptor).2.2 ▸ report
  | producerCancelled projected _ _ ih =>
      intro more birth result ref descriptor member bounded
      obtain ⟨taskOwners, taskPayload, task⟩ := projected
      have contributes : ref ∈ taskOwners := (task.unique descriptor).1.symm ▸ member
      obtain ⟨owners, ancestor, payload, parentRef, parent, parentMember, earlier⟩ :=
        producer_owner_ref_le_structural valid coherent continuous ordered task contributes
      have report := (ih parent parentMember (Nat.lt_of_le_of_lt earlier bounded)).descendant
        (under.producer_prefix task parent)
      exact (task.unique descriptor).2.2 ▸ report

-----------------------------------------------------------------------------------------
-- Historical cuts preserve the same bounded origin inventory
-----------------------------------------------------------------------------------------

/-- A cancelled task below `limit` is covered by earlier failed-owner and accepted reports.
Witness: retain its ordered-cut snapshot, instantiate bounded mutual assembly, and lift
each actual origin back to the full history. The bound applies to the chosen task owner,
not to every co-owner or every event in the history.
-/
theorem cancelled_reported_of_bounded_owner_task_scopes
    {ancestry refBound roles base paths pathBound work events matching failures limit
      occurrence owners producer payload ref}
    (valid : Valid ancestry refBound)
    (coherent : MixedRefs.WorkAt ancestry 0 refBound work)
    (roleCoherent : RefRoles.WorkRoles roles work)
    (continuous : DeferContinuous ancestry work) (ordered : StreamOwnersOrdered work)
    (pathCoherent : MixedOwnerPaths.WorkAt paths pathBound work)
    (under : ExecutionPaths.WorkUnder base work)
    (ownerTaskReports
      : ∀ address owners producer payload node dependencies birth,
          TaskAt work (.executionGroup address) owners producer payload
          → NodeAt work node .group dependencies birth
          → node.ref ∈ owners
          → node.ref < limit
          → NodeFailed work matching events failures node.ref
          → FailureReportedFor events payload.path)
    (taskReports
      : ∀ cut occurrence,
          (cut, occurrence) ∈ failures
          → ∀ owners producer payload,
              TaskAt work occurrence owners producer payload
              → FailureReportedFor events payload.path)
    (cancelled : TaskCancelled work matching events failures occurrence)
    (known : TaskAt work occurrence owners producer payload)
    (member : ref ∈ owners) (bounded : ref < limit)
    : FailureReportedFor events payload.path := by
  obtain ⟨cut, reached, cutBound, cause⟩ := cancelled
  apply snapshot_cancelled_reported_of_bounded_owner_task_scopes valid coherent
    roleCoherent continuous ordered pathCoherent under ?_ ?_ cause known member bounded
  · intro address owners producer payload node dependencies birth task descriptor member
      earlier failed
    exact ownerTaskReports address owners producer payload node dependencies birth task
      descriptor member earlier ⟨cut, reached, cutBound, failed⟩
  · intro task member taskOwners birth result descriptor
    obtain ⟨entry, recorded, same⟩ := List.mem_map.mp member
    have recorded : entry ∈ failures := (List.mem_filter.mp recorded).1
    exact taskReports entry.1 task (by simpa only [← same] using recorded) taskOwners birth
      result descriptor

end GraphQL.IncrementalDelivery.Correctness
