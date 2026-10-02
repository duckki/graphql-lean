import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskEligibility
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CachedFailures
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.HealthyContributors
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RecordCancellation

/-! Causal health and cancellation at the executable task-eligibility boundary. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Generated ancestry makes the finite health guard complete for healthy groups
-----------------------------------------------------------------------------------------

/-- A live, uninvalidated generated record passes the executable healthy-owner check.
Witness: supported caches and cancellation keys exclude false rejections, canonical
parent descriptors propagate health to ancestors, and generated parent keys decrease.
The finite guard lemma supplies the node-count bound without assuming extra traversal fuel.
-/
theorem State.CachedFailuresSupported.groupIsHealthy_of_recordHealthy {queue : State}
    {work failed key node} (supported : queue.CachedFailuresSupported work failed)
    (cancelled : queue.CancelledRecordsSupported work failed)
    (generated : ExecutedWork work)
    (descriptors
      : ∀ node ∈ queue.groupNodes,
          ∃ dependencies,
            GroupRecordAt work node.group.node dependencies
            ∧ node.group.parent = dependencies.head?)
    (found : queue.groupNode? key = some node)
    (healthy : ¬GroupRecordInvalidated work failed key)
    : queue.groupIsHealthy key = true := by
  apply State.groupIsHealthy_of_invariant found
    (fun key => ¬GroupRecordInvalidated work failed key)
    (fun node member good => supported.healthy_none member
      (fun invalid => good invalid.toRecordInvalidated)) ?_ ?_
    (fun _ healthy => cancelled.healthy_not_mem healthy) healthy
  · intro node member parent parentEq good failed
    obtain ⟨dependencies, known, canonical⟩ := descriptors node member
    have ancestor : parent ∈ dependencies := List.mem_of_head?
      (canonical.symm.trans parentEq)
    exact good (.ancestor known ancestor failed)
  · intro node member parent parentEq
    obtain ⟨dependencies, known, canonical⟩ := descriptors node member
    exact generated.groupRecordAncestorSmaller known
      (List.mem_of_head? (canonical.symm.trans parentEq))

/-- A causally healthy actual contributor passes the same record-aware executable guard.
Witness: contributor equivalence turns original causal health into record health before
the finite walk. The descriptor premise excludes cancelled taskless wrappers.
-/
theorem State.CachedFailuresSupported.groupIsHealthy {queue : State}
    {work failed key node} (supported : queue.CachedFailuresSupported work failed)
    (cancelled : queue.CancelledRecordsSupported work failed)
    (generated : ExecutedWork work)
    (descriptors
      : ∀ node ∈ queue.groupNodes,
          ∃ dependencies,
            GroupRecordAt work node.group.node dependencies
            ∧ node.group.parent = dependencies.head?)
    (contributor : ∃ dependencies, NodeHasDependencies work key .group dependencies)
    (found : queue.groupNode? key = some node)
    (healthy : ¬GroupInvalidated work failed key)
    : queue.groupIsHealthy key = true := by
  obtain ⟨dependencies, source, producer, known, same⟩ := contributor
  apply supported.groupIsHealthy_of_recordHealthy cancelled generated descriptors found
  intro failure
  have invalid := (generated.groupRecordInvalidated_iff_groupInvalidated known).mp
    (same.symm ▸ failure)
  exact healthy (same ▸ invalid)

-----------------------------------------------------------------------------------------
-- Rejected fresh tasks have no causally healthy owners left
-----------------------------------------------------------------------------------------

/-- A rejected started task is absent from every still-healthy group's memberships.
Witness: membership soundness identifies the group as a contributor; its present healthy
record would force the executable task guard to accept. No freshness or pending-count
premise is needed for this local exclusion.
-/
theorem State.GroupMembershipSound.rejectedTask_absentFromHealthy {queue : State}
    {work failed} (sound : queue.GroupMembershipSound)
    (registered : queue.StartedTasksRegistered)
    (matching : queue.RegisteredTasksMatch work)
    (supported : queue.CachedFailuresSupported work failed)
    (cancelled : queue.CancelledRecordsSupported work failed)
    (generated : ExecutedWork work)
    (descriptors
      : ∀ node ∈ queue.groupNodes,
          ∃ dependencies,
            GroupRecordAt work node.group.node dependencies
            ∧ node.group.parent = dependencies.head?)
    {taskNode : TaskNode} (taskMember : taskNode ∈ queue.taskNodes)
    (rejected : queue.taskHasHealthyOwner taskNode.task = false) {node : GroupNode}
    (member : node ∈ queue.groupNodes)
    (healthy : ¬GroupInvalidated work failed node.group.node.key)
    : taskNode.task.occurrence ∉ node.tasks := by
  intro listed
  have contributes := sound.startedOwner registered matching taskMember member listed
  have present : ∃ found, queue.groupNode? node.group.node.key = some found := by
    cases found : queue.groupNode? node.group.node.key with
    | some owner => exact ⟨owner, rfl⟩
    | none =>
        have absent := List.find?_eq_none.mp found node member
        simp at absent
  obtain ⟨owner, found⟩ := present
  have known := (matching taskNode.task (registered taskNode taskMember)).contributorKnown
    contributes
  have passes := supported.groupIsHealthy cancelled generated descriptors known found healthy
  obtain ⟨group, groupMember, groupKey⟩ := List.mem_map.mp contributes
  have accepted : queue.taskHasHealthyOwner taskNode.task = true :=
    State.taskHasHealthyOwner_iff.mpr ⟨group, groupMember, groupKey ▸ passes⟩
  simp [rejected] at accepted

/-- Rejecting a registered unsettled task implies that every contributor is invalidated.
Witness: registered-task accounting supplies any purported healthy owner; cache provenance
and generated ancestry would then make the executable guard accept that owner.
All premises are internal queue invariants, not additional host-source laws.
-/
theorem State.HealthyRegisteredTaskAccounting.rejectedTask_ownersInvalidated
    {queue : State} {work settled failed}
    (accounted : queue.HealthyRegisteredTaskAccounting work settled failed)
    (matching : queue.RegisteredTasksMatch work)
    (supported : queue.CachedFailuresSupported work failed)
    (cancelled : queue.CancelledRecordsSupported work failed)
    (generated : ExecutedWork work)
    (descriptors
      : ∀ node ∈ queue.groupNodes,
          ∃ dependencies,
            GroupRecordAt work node.group.node dependencies
            ∧ node.group.parent = dependencies.head?)
    {task : Task} (registered : task ∈ queue.tasks) (fresh : task.occurrence ∉ settled)
    (rejected : queue.taskHasHealthyOwner task = false)
    : ∀ key ∈ task.groups.map Execution.DeliveryNode.key,
        GroupInvalidated work failed key := by
  classical
  intro key contributes
  apply Classical.byContradiction
  intro healthy
  obtain ⟨owner, member, ownerKey, _⟩ := accounted task registered fresh key contributes healthy
  have present : ∃ node, queue.groupNode? key = some node := by
    cases found : queue.groupNode? key with
    | some node => exact ⟨node, rfl⟩
    | none =>
        have absent := List.find?_eq_none.mp found owner member
        simp [ownerKey] at absent
  obtain ⟨node, found⟩ := present
  have known := (matching task registered).contributorKnown contributes
  have passes := supported.groupIsHealthy cancelled generated descriptors known found healthy
  obtain ⟨group, groupMember, groupKey⟩ := List.mem_map.mp contributes
  have accepted : queue.taskHasHealthyOwner task = true :=
    State.taskHasHealthyOwner_iff.mpr ⟨group, groupMember, groupKey ▸ passes⟩
  simp [rejected] at accepted

/-- An unpublished rejected generated task is cancelled in the independent causal kernel.
Witness: every owner is invalidated by prior failures; generated tasks have at least one
owner. No output-admission premise or special cancellation rule is added to the contract.
-/
theorem State.HealthyRegisteredTaskAccounting.rejectedTask_cancelled {queue : State}
    {work settled failed published}
    (accounted : queue.HealthyRegisteredTaskAccounting work settled failed)
    (matching : queue.RegisteredTasksMatch work)
    (supported : queue.CachedFailuresSupported work failed)
    (cancelled : queue.CancelledRecordsSupported work failed)
    (generated : ExecutedWork work)
    (descriptors
      : ∀ node ∈ queue.groupNodes,
          ∃ dependencies,
            GroupRecordAt work node.group.node dependencies
            ∧ node.group.parent = dependencies.head?)
    {task : Task} (registered : task ∈ queue.tasks) (fresh : task.occurrence ∉ settled)
    (known
      : TaskHasOwners work task.occurrence (task.groups.map Execution.DeliveryNode.key))
    (rejected : queue.taskHasHealthyOwner task = false)
    (unpublished : ¬published task.occurrence)
    : Causality.TaskCancelled work failed published task.occurrence := by
  obtain ⟨producer, payload, taskKnown⟩ := known
  refine .owners ⟨producer, payload, taskKnown⟩ unpublished
    (generated.taskOwners_nonempty taskKnown) ?_
  intro key contributes
  exact (accounted.rejectedTask_ownersInvalidated matching supported cancelled generated descriptors
    registered fresh rejected key contributes).toCausality published

/-- Ignored task failures do not change which groups the source failure ledger invalidates.
Witness: all contributing owners were already invalidated before the rejected settlement.
The coarse health ledger may retain this redundant token; error inventories must omit it.
-/
theorem State.HealthyRegisteredTaskAccounting.rejectedTask_invalidation_iff
    {queue : State} {work settled failed}
    (accounted : queue.HealthyRegisteredTaskAccounting work settled failed)
    (matching : queue.RegisteredTasksMatch work)
    (supported : queue.CachedFailuresSupported work failed)
    (cancelled : queue.CancelledRecordsSupported work failed)
    (generated : ExecutedWork work)
    (descriptors
      : ∀ node ∈ queue.groupNodes,
          ∃ dependencies,
            GroupRecordAt work node.group.node dependencies
            ∧ node.group.parent = dependencies.head?)
    {task : Task} (registered : task ∈ queue.tasks) (fresh : task.occurrence ∉ settled)
    (known
      : TaskHasOwners work task.occurrence (task.groups.map Execution.DeliveryNode.key))
    (rejected : queue.taskHasHealthyOwner task = false) (key : Nat)
    : GroupInvalidated work (task.occurrence :: failed) key
      ↔ GroupInvalidated work failed key :=
  groupInvalidated_cons_iff_of_ownersInvalidated known
    (accounted.rejectedTask_ownersInvalidated matching supported cancelled generated
      descriptors registered fresh rejected)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
