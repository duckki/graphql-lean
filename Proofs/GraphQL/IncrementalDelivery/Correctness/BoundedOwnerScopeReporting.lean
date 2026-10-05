import Proofs.GraphQL.IncrementalDelivery.Correctness.GroupScopeOrigins
import Proofs.GraphQL.IncrementalDelivery.Correctness.CausalTaskReportAssembly

/-! Earlier group notice scopes cover cancelled producer owners at ordered failure cuts. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open Semantics.Ancestry Semantics.GeneralScheduling WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Mutual causal assembly preserves a chosen owner's notice scope
-----------------------------------------------------------------------------------------

/-- Cancellation below a ref bound reports the chosen owner's scope, not just its task
attachment. Witness: mutual causal descent with scope-preserving producer support. Group
branches use only earlier group-scope reports; stream settlements keep their actual list
reports. This is an induction step, not an additional terminal or admission premise.
-/
theorem snapshot_cancelled_owner_scope_reported_below
    {ancestry refBound roles base paths pathBound work failed published events limit
      occurrence owners producer payload node kind dependencies birth}
    (valid : Valid ancestry refBound)
    (coherent : MixedRefs.WorkAt ancestry 0 refBound work)
    (roleCoherent : RefRoles.WorkRoles roles work)
    (continuous : DeferContinuous ancestry work) (ordered : StreamOwnersOrdered work)
    (pathCoherent : MixedOwnerPaths.WorkAt paths pathBound work)
    (under : ExecutionPaths.WorkUnder base work)
    (certified : ScopeMetadata.WorkScoped work)
    (groupReports
      : ∀ node dependencies birth,
          NodeAt work node .group dependencies birth
          → node.ref < limit
          → Causality.NodeFailed work failed published node.ref
          → FailureReportedFor events node.path)
    (taskReports
      : ∀ occurrence ∈ failed,
          ∀ owners producer payload,
            TaskAt work occurrence owners producer payload
            → FailureReportedFor events payload.path)
    (cancelled : Causality.TaskCancelled work failed published occurrence)
    (known : TaskAt work occurrence owners producer payload)
    (owner : NodeAt work node kind dependencies birth) (member : node.ref ∈ owners)
    (bounded : node.ref < limit)
    : FailureReportedFor events node.path := by
  have settledOwner {occurrence owners producer payload node kind dependencies birth}
      (recorded : occurrence ∈ failed)
      (known : TaskAt work occurrence owners producer payload)
      (owner : NodeAt work node kind dependencies birth) (member : node.ref ∈ owners)
      (bounded : node.ref < limit) : FailureReportedFor events node.path := by
    cases StructuralEquivalence.taskAt_of_current known with
    | executionGroup located =>
        cases kind with
        | group =>
            exact groupReports _ _ _ owner bounded
              (Causality.NodeFailed.task ⟨_, _, known⟩ member recorded)
        | stream =>
            obtain ⟨group, included, same⟩ := List.mem_map.mp member
            exact False.elim (stream_group_refs_distinct roleCoherent owner
              (NodeAt.group located.toCurrent included) same.symm)
    | item located entry =>
        have scope := workAt_same_path pathCoherent (NodeAt.stream located.toCurrent)
          owner (List.mem_singleton.mp member).symm
        simpa only [Payload.path, scope] using taskReports _ recorded _ _ _ known
  revert owners producer payload node kind dependencies birth
  induction cancelled
    using Causality.TaskCancelled.rec
      (motive_1 :=
        fun ref _ =>
          ∀ node dependencies birth,
            NodeAt work node .stream dependencies birth
            → node.ref = ref
            → ref < limit
            → FailureReportedFor events node.path) with
  | task projected member recorded =>
      rename_i node dependencies birth descriptor same bounded
      obtain ⟨taskBirth, taskPayload, task⟩ := projected
      exact settledOwner recorded task descriptor (same.symm ▸ member)
        (same ▸ bounded)
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
      have small : group.ref < limit := by
        rw [groupSame]
        exact Nat.lt_trans (coherent_stream_dependencies ordered streamKnown ref member)
          (selected ▸ bounded)
      have report := groupReports _ _ _ groupKnown small
        (groupSame.symm ▸ failures ref member)
      rw [generated] at streamKnown
      obtain ⟨parentOwners, parentBirth, parentPayload, parent, belowStream⟩ :=
        under.stream_producer_under streamKnown
      have parentSame := (task.unique parent).2.2
      have ownBelow := ScopeMetadata.owner_payload_prefix pathCoherent task groupKnown
        (groupSame.symm ▸ member)
      have belowStream : (.object path result : Payload).path.IsPrefix stream.path := by
        simpa only [← parentSame] using belowStream
      have scope := workAt_same_path pathCoherent streamKnown descriptor
        (selected.trans same.symm)
      exact scope ▸ report.descendant (ownBelow.trans belowStream)
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
          · exact (taskReports _ recorded _ _ _ task).descendant below
          · obtain ⟨parentOwners, parentBirth, parentPayload, parentRef, parentTask,
              contributes, earlier⟩ := stream_producer_owner_lt coherent continuous ordered
                descriptor
            obtain ⟨parent, parentKind, parents, parentKnown, parentSame⟩ :=
              parentTask.owner_at_producer contributes
            have small : parent.ref < limit := by
              rw [parentSame]
              exact Nat.lt_trans earlier (same ▸ bounded)
            have report := ih source sourceKnown recorded parentTask parentKnown
              (parentSame.symm ▸ contributes) small
            have ownBelow := ScopeMetadata.owner_payload_prefix pathCoherent parentTask
              parentKnown (parentSame.symm ▸ contributes)
            have payloadSame := (task.unique parentTask).2.2
            have below : parentPayload.path.IsPrefix node.path := payloadSame ▸ below
            exact report.descendant (ownBelow.trans below)
  | owners projected _ _ failures ih =>
      intro more birth result node kind dependencies nodeBirth descriptor owner member bounded
      obtain ⟨taskBirth, taskPayload, task⟩ := projected
      have contributes : node.ref ∈ _ := (task.unique descriptor).1.symm ▸ member
      cases kind with
      | group => exact groupReports _ _ _ owner bounded (failures _ contributes)
      | stream => exact ih _ contributes node dependencies nodeBirth owner rfl bounded
  | producerFailed projected _ recorded =>
      intro more birth result node kind dependencies nodeBirth descriptor owner member bounded
      obtain ⟨taskOwners, taskPayload, task⟩ := projected
      have same := (task.unique descriptor).2.1
      have actual := same.symm ▸ descriptor
      obtain ⟨parentOwners, ancestor, parentPayload, parent, parentKind, parents, parentTask,
        parentKnown, parentMember, before, below⟩ :=
        ScopeMetadata.producer_owner_scope valid coherent continuous ordered pathCoherent
          under certified actual owner member
      exact (settledOwner recorded parentTask parentKnown parentMember
        (Nat.lt_of_le_of_lt before bounded)).descendant below
  | producerCancelled projected _ _ ih =>
      intro more birth result node kind dependencies nodeBirth descriptor owner member bounded
      obtain ⟨taskOwners, taskPayload, task⟩ := projected
      have same := (task.unique descriptor).2.1
      have actual := same.symm ▸ descriptor
      obtain ⟨parentOwners, ancestor, parentPayload, parent, parentKind, parents, parentTask,
        parentKnown, parentMember, before, below⟩ :=
        ScopeMetadata.producer_owner_scope valid coherent continuous ordered pathCoherent
          under certified actual owner member
      exact (ih parentTask parentKnown parentMember
        (Nat.lt_of_le_of_lt before bounded)).descendant
        below

-----------------------------------------------------------------------------------------
-- Ordered histories retain the same earlier-scope inventory
-----------------------------------------------------------------------------------------

/-- A cancelled producer's chosen owner scope is reported using only earlier group scopes.
Witness: retain the actual cancellation cut, lift failed-group evidence to the full history,
and use actual accepted-settlement reports. No terminal reporting conclusion is assumed.
-/
theorem cancelled_owner_scope_reported_below
    {ancestry refBound roles base paths pathBound work events matching failures limit
      occurrence owners producer payload node kind dependencies birth}
    (valid : Valid ancestry refBound)
    (coherent : MixedRefs.WorkAt ancestry 0 refBound work)
    (roleCoherent : RefRoles.WorkRoles roles work)
    (continuous : DeferContinuous ancestry work) (ordered : StreamOwnersOrdered work)
    (pathCoherent : MixedOwnerPaths.WorkAt paths pathBound work)
    (under : ExecutionPaths.WorkUnder base work)
    (certified : ScopeMetadata.WorkScoped work)
    (groupReports
      : ∀ node dependencies birth,
          NodeAt work node .group dependencies birth
          → node.ref < limit
          → NodeFailed work matching events failures node.ref
          → FailureReportedFor events node.path)
    (taskReports
      : ∀ cut occurrence,
          (cut, occurrence) ∈ failures
          → ∀ owners producer payload,
              TaskAt work occurrence owners producer payload
              → FailureReportedFor events payload.path)
    (cancelled : TaskCancelled work matching events failures occurrence)
    (known : TaskAt work occurrence owners producer payload)
    (owner : NodeAt work node kind dependencies birth) (member : node.ref ∈ owners)
    (bounded : node.ref < limit)
    : FailureReportedFor events node.path := by
  obtain ⟨cut, reached, cutBound, cause⟩ := cancelled
  apply snapshot_cancelled_owner_scope_reported_below valid coherent roleCoherent
    continuous ordered pathCoherent under certified ?_ ?_ cause known owner member bounded
  · intro node dependencies birth known before failed
    exact groupReports _ _ _ known before ⟨cut, reached, cutBound, failed⟩
  · intro task member owners birth payload known
    obtain ⟨entry, recorded, same⟩ := List.mem_map.mp member
    have recorded : entry ∈ failures := (List.mem_filter.mp recorded).1
    exact taskReports entry.1 task (by simpa only [← same] using recorded) owners birth
      payload known

end GraphQL.IncrementalDelivery.Correctness
