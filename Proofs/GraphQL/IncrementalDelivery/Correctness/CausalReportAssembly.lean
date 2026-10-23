import Proofs.GraphQL.IncrementalDelivery.Correctness.TaskAttachmentPaths
import Proofs.GraphQL.IncrementalDelivery.Correctness.MixedNoticeMetadata
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.CompletionExistence

/-! Assemble supplied actual report origins through all causal cancellation rules.
Constructing these origins from notices remains a separate progress obligation.
-/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Group scopes, stream scopes, and producer attachments
-----------------------------------------------------------------------------------------

/-- Reports at failed group scopes and recorded task attachments cover every task cancelled
at a snapshot. Witness: mutual causal induction. A failed defer dependency covers its
stream through their common producer attachment; producer cancellation descends through
local path certificates. A group's broader scope is supplied separately, since a shared
task's narrower attachment report need not cover the group's other cancelled selections.
This assembles actual report evidence; it does not construct or assume a complete run.
-/
theorem snapshot_cancelled_reported_of_group_and_task_scopes
    {base paths bound work failed published events occurrence owners producer payload}
    (coherent : MixedOwnerPaths.WorkAt paths bound work)
    (under : ExecutionPaths.WorkUnder base work)
    (groupReports
      : ∀ node dependencies birth,
          NodeAt work node .group dependencies birth
          → Causality.NodeFailed work failed published node.ref
          → FailureReportedFor events node.path)
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
          ∀ node kind dependencies birth,
            NodeAt work node kind dependencies birth
            → node.ref = ref
            → FailureReportedFor events node.path) with
  | task projected owner recorded =>
      rename_i node kind dependencies birth descriptor same
      obtain ⟨taskBirth, taskPayload, task⟩ := projected
      cases StructuralEquivalence.taskAt_of_current task with
      | executionGroup located =>
          obtain ⟨group, member, selected⟩ := List.mem_map.mp owner
          have groupKnown := NodeAt.group located.toCurrent member
          have report := groupReports _ _ _ groupKnown
            (.task ⟨_, _, task⟩ (selected ▸ owner) recorded)
          have scope := workAt_same_path coherent groupKnown descriptor
            (selected.trans same.symm)
          simpa only [scope] using report
      | @item address stream items source enclosing index result children located entry =>
          have scope := workAt_same_path coherent (NodeAt.stream located.toCurrent)
            descriptor ((List.mem_singleton.mp owner).symm.trans same.symm)
          simpa only [Payload.path, scope] using taskReports _ recorded _ _ _ task
  | groupDependency projected member failure _ =>
      rename_i node kind dependencies birth descriptor same
      obtain ⟨group, source, groupKnown, selected⟩ := projected
      have report := groupReports _ _ _ groupKnown
        (selected.symm ▸ Causality.NodeFailed.groupDependency
          ⟨group, source, groupKnown, selected⟩ member failure)
      have scope := workAt_same_path coherent groupKnown descriptor
        (selected.trans same.symm)
      simpa only [scope] using report
  | streamDependencies projected nonempty failures _ =>
      rename_i node kind dependencies birth descriptor same
      obtain ⟨stream, source, streamKnown, selected⟩ := projected
      obtain ⟨ref, member⟩ := List.exists_mem_of_ne_nil _ nonempty
      obtain ⟨address, ancestor, path, result, generated, task⟩ :=
        stream_dependency_task streamKnown member
      obtain ⟨group, parents, groupKnown, groupSame⟩ := task.executionGroup_owner member
      have report := groupReports _ _ _ groupKnown (groupSame.symm ▸ failures ref member)
      obtain ⟨suffix, below⟩ := workAt_owner_prefix coherent task groupKnown
        (groupSame.symm ▸ member)
      have belowTask : group.path.IsPrefix path := ⟨suffix, below.symm⟩
      rw [generated] at streamKnown
      obtain ⟨parentOwners, parentBirth, parentPayload, parent, belowStream⟩ :=
        under.stream_producer_under streamKnown
      have parentSame := (task.unique parent).2.2
      have belowStream : path.IsPrefix stream.path := by
        simpa only [← parentSame, Payload.path] using belowStream
      have scope := workAt_same_path coherent streamKnown descriptor
        (selected.trans same.symm)
      exact scope ▸ report.descendant (belowTask.trans belowStream)
  | producers projected noRoot unpublished cancelled ih =>
      rename_i node kind dependencies birth descriptor same
      cases kind with
      | group =>
          exact groupReports _ _ _ descriptor
            (same.symm ▸ Causality.NodeFailed.producers projected noRoot unpublished cancelled)
      | stream =>
          cases birth with
          | none =>
              exact False.elim (noRoot ⟨node, .stream, dependencies, descriptor, same⟩)
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
          have report := groupReports _ _ _ groupKnown (same.symm ▸ failures ref member)
          obtain ⟨suffix, below⟩ := workAt_owner_prefix coherent task groupKnown
            (same.symm ▸ member)
          have report := report.descendant ⟨suffix, below.symm⟩
          exact (task.unique descriptor).2.2 ▸ report
      | @item address stream items source enclosing index outcome children located entry
        =>
          have report := ih stream.ref (by simp) stream .stream _ taskBirth
            (NodeAt.stream located.toCurrent) rfl
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
-- Ordered-cut cancellation retains the same observable scopes
-----------------------------------------------------------------------------------------

/-- Reported failed groups and reported accepted settlements cover historical cancellation.
Witness: restrict to the cancellation's retained snapshot, preserve recorded-cut members,
then apply causal scope assembly. Both premises refer to actual output notices; neither
internal accounting nor a total error count can substitute for their scopes.
-/
theorem cancelled_reported_of_group_and_task_scopes
    {base paths bound work events matching failures occurrence owners producer payload}
    (coherent : MixedOwnerPaths.WorkAt paths bound work)
    (under : ExecutionPaths.WorkUnder base work)
    (groupReports
      : ∀ node dependencies birth,
          NodeAt work node .group dependencies birth
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
    : FailureReportedFor events payload.path := by
  obtain ⟨cut, reached, bounded, cause⟩ := cancelled
  apply snapshot_cancelled_reported_of_group_and_task_scopes coherent under ?_ ?_ cause
    known
  · exact fun node dependencies birth descriptor failure =>
      groupReports node dependencies birth descriptor ⟨cut, reached, bounded, failure⟩
  · intro task member taskOwners birth result descriptor
    obtain ⟨entry, recorded, same⟩ := List.mem_map.mp member
    have recorded : entry ∈ failures := (List.mem_filter.mp recorded).1
    apply taskReports entry.1 task (by simpa only [← same] using recorded)
      taskOwners birth result descriptor

-----------------------------------------------------------------------------------------
-- Finalization uses assembled scopes rather than an assumed terminal law
-----------------------------------------------------------------------------------------

/-- An internally accounted history with actual group/task report origins can finish while
retaining all supplied batches. Witness: assemble every unpublished task's cancellation
scope, then append bounded notice-free closures and termination. The two origin premises
are separate construction obligations; healthy-notice coverage alone does not imply them.
-/
theorem finish_accounted_of_report_scopes
    {base paths bound work groups streams events matching failures batches}
    (coherent : MixedOwnerPaths.WorkAt paths bound work)
    (under : ExecutionPaths.WorkUnder base work)
    (explained : Explains work groups streams events matching failures)
    (supported
      : OpenFailureCauses work ((groups ++ streams).map DeliveryNode.ref)
          matching events failures)
    (batched : WorkBatching events batches)
    (accounted
      : ∀ occurrence owners producer payload,
          TaskAt work occurrence owners producer payload
          → TaskAccounted work matching events failures occurrence)
    (groupReports
      : ∀ node dependencies birth,
          NodeAt work node .group dependencies birth
          → NodeFailed work matching events failures node.ref
          → FailureReportedFor events node.path)
    (taskReports
      : ∀ cut occurrence,
          (cut, occurrence) ∈ failures
          → ∀ owners producer payload,
              TaskAt work occurrence owners producer payload
              → FailureReportedFor events payload.path)
    : ∃ tail : List WorkQueueEvent,
        AdmissibleRun work
          ⟨
            groups,
            streams,
            batches ++ tail.map (fun event => [event]) ++ [[.workQueueTermination]]
          ⟩
        ∧ (∀ event ∈ tail, eventPending event = [] ∧ ¬IsValue event)
        ∧ tail.length
          ≤ (announcedRefs ((groups ++ streams).map DeliveryNode.ref) events).length := by
  apply batched.finish_accounted explained supported accounted
  intro occurrence owners producer payload known unpublished
  exact cancelled_reported_of_group_and_task_scopes coherent under groupReports taskReports
    ((accounted occurrence owners producer payload known).resolve_right unpublished) known

end GraphQL.IncrementalDelivery.Correctness
