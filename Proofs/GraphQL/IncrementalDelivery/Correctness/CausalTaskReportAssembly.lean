import Proofs.GraphQL.IncrementalDelivery.Correctness.CausalReportAssembly
import Proofs.GraphQL.IncrementalDelivery.Correctness.NodeRoles

/-! Causal report assembly needs task-local defer coverage, not full group scopes. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Failed defer owners cover attachments; stream and producer rules transport them
-----------------------------------------------------------------------------------------

/-- Task-local failed-owner reports and accepted settlement reports cover cancellation.
Witness: mutual causal induction whose node motive requests only stream scopes. Deferred
tasks use their own attachment report; a failed stream dependency uses its generating
deferred task's attachment. Producer-local prefixes propagate both forms of coverage.
Unlike full-group assembly, no report for every failed group's entire scope is assumed.
-/
theorem snapshot_cancelled_reported_of_owner_task_scopes
    {base roles paths bound work failed published events occurrence owners producer
      payload}
    (roleCoherent : RefRoles.WorkRoles roles work)
    (coherent : MixedOwnerPaths.WorkAt paths bound work)
    (under : ExecutionPaths.WorkUnder base work)
    (ownerTaskReports
      : ∀ address owners producer payload node dependencies birth,
          TaskAt work (.executionGroup address) owners producer payload
          → NodeAt work node .group dependencies birth
          → node.ref ∈ owners
          → Causality.NodeFailed work failed published node.ref
          → FailureReportedFor events payload.path)
    (taskReports
      : ∀ occurrence ∈ failed,
          ∀ owners producer payload,
            TaskAt work occurrence owners producer payload
            → FailureReportedFor events payload.path)
    (cancelled : Causality.TaskCancelled work failed published occurrence)
    (known : TaskAt work occurrence owners producer payload)
    : FailureReportedFor events payload.path := by
  revert owners producer payload
  induction cancelled
    using Causality.TaskCancelled.rec
      (motive_1 :=
        fun ref _ =>
          ∀ node dependencies birth,
            NodeAt work node .stream dependencies birth
            → node.ref = ref
            → FailureReportedFor events node.path) with
  | task projected owner recorded =>
      rename_i node dependencies birth descriptor same
      obtain ⟨taskBirth, taskPayload, task⟩ := projected
      cases StructuralEquivalence.taskAt_of_current task with
      | executionGroup located =>
          obtain ⟨group, member, selected⟩ := List.mem_map.mp owner
          have groupKnown := NodeAt.group located.toCurrent member
          exact False.elim (stream_group_refs_distinct roleCoherent descriptor groupKnown
            (same.trans selected.symm))
      | item located entry =>
          have scope := workAt_same_path coherent (NodeAt.stream located.toCurrent)
            descriptor ((List.mem_singleton.mp owner).symm.trans same.symm)
          simpa only [Payload.path, scope] using taskReports _ recorded _ _ _ task
  | groupDependency projected _ _ _ =>
      rename_i node dependencies birth descriptor same
      obtain ⟨group, source, groupKnown, selected⟩ := projected
      exact False.elim (stream_group_refs_distinct roleCoherent descriptor groupKnown
        (same.trans selected.symm))
  | streamDependencies projected nonempty failures _ =>
      rename_i node dependencies birth descriptor same
      obtain ⟨stream, source, streamKnown, selected⟩ := projected
      obtain ⟨ref, member⟩ := List.exists_mem_of_ne_nil _ nonempty
      obtain ⟨address, ancestor, path, result, generated, task⟩ :=
        stream_dependency_task streamKnown member
      obtain ⟨group, parents, groupKnown, groupSame⟩ := task.executionGroup_owner member
      have report := ownerTaskReports _ _ _ _ _ _ _ task groupKnown
        (groupSame.symm ▸ member) (groupSame.symm ▸ failures ref member)
      rw [generated] at streamKnown
      obtain ⟨parentOwners, parentBirth, parentPayload, parent, belowStream⟩ :=
        under.stream_producer_under streamKnown
      have parentSame := (task.unique parent).2.2
      have belowStream : path.IsPrefix stream.path := by
        simpa only [← parentSame, Payload.path] using belowStream
      have scope := workAt_same_path coherent streamKnown descriptor
        (selected.trans same.symm)
      exact scope ▸ report.descendant belowStream
  | producers projected noRoot _ _ ih =>
      rename_i node dependencies birth descriptor same
      cases birth with
      | none => exact False.elim (noRoot ⟨node, .stream, dependencies, descriptor, same⟩)
      | some source =>
          have sourceKnown : NodeHasProducer work _ (some source) :=
            ⟨node, .stream, dependencies, descriptor, same⟩
          obtain ⟨owners, ancestor, payload, task, below⟩ :=
            under.stream_producer_under descriptor
          by_cases recorded : source ∈ failed
          · exact (taskReports source recorded owners ancestor payload task).descendant below
          · exact (ih source sourceKnown recorded task).descendant below
  | owners projected _ nonempty failures ih =>
      intro more birth result descriptor
      obtain ⟨taskBirth, taskPayload, task⟩ := projected
      cases StructuralEquivalence.taskAt_of_current task with
      | executionGroup located =>
          obtain ⟨ref, member⟩ := List.exists_mem_of_ne_nil _ nonempty
          obtain ⟨group, included, same⟩ := List.mem_map.mp member
          have groupKnown := NodeAt.group located.toCurrent included
          have report := ownerTaskReports _ _ _ _ _ _ _ task groupKnown
            (same.symm ▸ member) (same.symm ▸ failures ref member)
          exact (task.unique descriptor).2.2 ▸ report
      | item located entry =>
          have report := ih _ (by simp) _ _ _ (NodeAt.stream located.toCurrent) rfl
          exact (task.unique descriptor).2.2 ▸ report
  | producerFailed projected _ recorded =>
      intro more birth result descriptor
      obtain ⟨taskOwners, taskPayload, task⟩ := projected
      obtain ⟨owners, ancestor, payload, parent⟩ := task.producer_dependency.2
      have report := (taskReports _ recorded owners ancestor payload parent).descendant
        (under.producer_prefix task parent)
      exact (task.unique descriptor).2.2 ▸ report
  | producerCancelled projected _ _ ih =>
      intro more birth result descriptor
      obtain ⟨taskOwners, taskPayload, task⟩ := projected
      obtain ⟨owners, ancestor, payload, parent⟩ := task.producer_dependency.2
      have report := (ih parent).descendant (under.producer_prefix task parent)
      exact (task.unique descriptor).2.2 ▸ report

-----------------------------------------------------------------------------------------
-- Retained ordered cuts supply the same task-local origins
-----------------------------------------------------------------------------------------

/-- Historical cancellation needs only task-local failed-owner and accepted-task reports.
Witness: freeze the retained failure/publication snapshot, translate its origins into the
actual history, and apply the mutual task-local assembly theorem. Reports remain concrete
positive-error completion scopes; no terminal law or reconstruction premise is supplied.
-/
theorem cancelled_reported_of_owner_task_scopes
    {base roles paths bound work events matching failures occurrence owners producer
      payload}
    (roleCoherent : RefRoles.WorkRoles roles work)
    (coherent : MixedOwnerPaths.WorkAt paths bound work)
    (under : ExecutionPaths.WorkUnder base work)
    (ownerTaskReports
      : ∀ address owners producer payload node dependencies birth,
          TaskAt work (.executionGroup address) owners producer payload
          → NodeAt work node .group dependencies birth
          → node.ref ∈ owners
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
    : FailureReportedFor events payload.path := by
  obtain ⟨cut, reached, bounded, cause⟩ := cancelled
  apply snapshot_cancelled_reported_of_owner_task_scopes roleCoherent coherent under ?_ ?_
    cause known
  · intro address owners producer payload node dependencies birth task descriptor member
      failed
    exact ownerTaskReports address owners producer payload node dependencies birth task
      descriptor member ⟨cut, reached, bounded, failed⟩
  · intro task member taskOwners birth result descriptor
    obtain ⟨entry, recorded, same⟩ := List.mem_map.mp member
    have recorded : entry ∈ failures := (List.mem_filter.mp recorded).1
    exact taskReports entry.1 task (by simpa only [← same] using recorded) taskOwners birth
      result descriptor

end GraphQL.IncrementalDelivery.Correctness
