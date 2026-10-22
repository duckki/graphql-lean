import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskLookupUpdates
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureDebt
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupRefs
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskEligibility

/-! Rejected task retention and the absence of earlier failures at fresh group refs.
These certificates describe existing queue records; they introduce no runtime ledger.
-/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Every earlier failed contributor of a live group remains listed and rejected.
An unregistered group ref has no earlier failed contributor. Counts are selected from
individual task rejections rather than added across a group.
-/
def State.RetainedFailures (queue : State) (work : Execution.Work)
    (failed : List Occurrence)
    : Prop :=
  (∀ occurrence ∈ failed,
    ∀ owners,
      TaskHasOwners work occurrence owners
      → ∀ group ∈ queue.groupNodes,
          group.group.node.ref ∈ owners
          → occurrence ∈ group.tasks
            ∧ ∃ task,
                queue.taskNode? occurrence = some task
                ∧ task.rejection.isSome = true
                ∧ group.group.node.ref ∈ task.task.groups.map Execution.DeliveryNode.ref)
  ∧ ∀ ref,
      ref ∉ queue.registeredGroups
      → ∀ occurrence ∈ failed,
          ∀ owners, TaskHasOwners work occurrence owners → ref ∉ owners

/-- Failure retention at an existing live owning group. -/
theorem State.RetainedFailures.retained {queue : State} {work failed}
    (prior : queue.RetainedFailures work failed)
    : ∀ occurrence ∈ failed,
        ∀ owners,
          TaskHasOwners work occurrence owners
          → ∀ group ∈ queue.groupNodes,
              group.group.node.ref ∈ owners
              → occurrence ∈ group.tasks
                ∧ ∃ task,
                    queue.taskNode? occurrence = some task
                    ∧ task.rejection.isSome = true
                    ∧ group.group.node.ref
                      ∈ task.task.groups.map Execution.DeliveryNode.ref :=
  prior.1

/-- No earlier failed task contributes to an unregistered group ref. -/
theorem State.RetainedFailures.fresh {queue : State} {work failed}
    (prior : queue.RetainedFailures work failed)
    : ∀ ref,
        ref ∉ queue.registeredGroups
        → ∀ occurrence ∈ failed,
            ∀ owners, TaskHasOwners work occurrence owners → ref ∉ owners :=
  prior.2

/-- An empty failure history imposes no retention or fresh-ref obligation. -/
theorem State.RetainedFailures.nil (queue : State) (work : Execution.Work)
    : queue.RetainedFailures work [] := by
  constructor <;> simp

/-- A task-record update with the same task and persistent rejection preserves retention.
Witness: the updated first match replaces only that occurrence; all others are unchanged.
-/
theorem State.RetainedFailures.putTaskNode {queue : State} {work failed}
    (prior : queue.RetainedFailures work failed) {old : TaskNode} {occurrence}
    (found : queue.taskNode? occurrence = some old) (updated : TaskNode)
    (sameTask : updated.task = old.task)
    (rejected : old.rejection.isSome = true → updated.rejection.isSome = true)
    : (queue.putTaskNode updated).RetainedFailures work failed := by
  refine ⟨?_, prior.fresh⟩
  intro other recorded owners known group member contributes
  obtain ⟨listed, task, lookup, failure, owner⟩ :=
    prior.retained other recorded owners known group member contributes
  refine ⟨listed, ?_⟩
  by_cases same : other = occurrence
  · subst other
    have equal : task = old := Option.some.inj (lookup.symm.trans found)
    subst task
    have occurrenceEq : old.task.occurrence = occurrence :=
      (occurrence_beq_iff_eq _ _).mp
        (List.find?_some (p := fun node : TaskNode => node.task.occurrence == occurrence) found)
    exact ⟨updated, State.putTaskNode_lookup_same found updated
      (sameTask ▸ occurrenceEq), rejected failure, sameTask ▸ owner⟩
  · have different : updated.task.occurrence ≠ other := by
      rw [sameTask]
      have selected := (occurrence_beq_iff_eq _ _).mp
        (List.find?_some (p := fun node : TaskNode => node.task.occurrence == occurrence) found)
      exact fun equal => same (equal.symm.trans selected)
    exact ⟨task, State.putTaskNode_lookup_other lookup updated different, failure, owner⟩

/-- A ref-preserving group replacement with unchanged tasks preserves failure retention.
Witness: unique refs identify the replaced node, while task records stay unchanged.
-/
theorem State.RetainedFailures.putGroupNodeSameTasks {queue : State} {work failed}
    (prior : queue.RetainedFailures work failed) (unique : queue.GroupRefsUnique)
    (old : GroupNode) (member : old ∈ queue.groupNodes) (updated : GroupNode)
    (sameRef : updated.group.node.ref = old.group.node.ref)
    (sameTasks : updated.tasks = old.tasks)
    : (queue.putGroupNode updated).RetainedFailures work failed := by
  refine ⟨?_, prior.fresh⟩
  intro occurrence recorded owners known group included owner
  obtain ⟨previous, previousMember, equal⟩ := List.mem_map.mp included
  split at equal
  · rename_i same
    subst group
    have refEq : previous.group.node.ref = old.group.node.ref :=
      (beq_iff_eq.mp same).trans sameRef
    have identical := unique.sameNode previousMember member refEq
    subst previous
    obtain ⟨listed, task, lookup, rejected, contributes⟩ :=
      prior.retained occurrence recorded owners known old member (sameRef ▸ owner)
    exact ⟨sameTasks ▸ listed, task, lookup, rejected, sameRef ▸ contributes⟩
  · subst group
    exact prior.retained occurrence recorded owners known previous previousMember owner

/-- Growing a looked-up group's memberships while keeping its ref retains failures.
Witness: unique refs identify the original record and all required memberships survive.
-/
theorem State.RetainedFailures.putGroupNodeTasksGrow {queue : State} {work failed}
    (prior : queue.RetainedFailures work failed) (unique : queue.GroupRefsUnique)
    (old : GroupNode) (member : old ∈ queue.groupNodes) (updated : GroupNode)
    (sameRef : updated.group.node.ref = old.group.node.ref)
    (included : old.tasks.Subset updated.tasks)
    : (queue.putGroupNode updated).RetainedFailures work failed := by
  refine ⟨?_, prior.fresh⟩
  intro occurrence recorded owners known group present owner
  obtain ⟨previous, previousMember, equal⟩ := List.mem_map.mp present
  split at equal
  · rename_i same
    subst group
    have refEq := (beq_iff_eq.mp same).trans sameRef
    have identical := unique.sameNode previousMember member refEq
    subst previous
    obtain ⟨listed, task, lookup, rejected, contributes⟩ :=
      prior.retained occurrence recorded owners known old member (sameRef ▸ owner)
    exact ⟨included listed, task, lookup, rejected, sameRef ▸ contributes⟩
  · subst group
    exact prior.retained occurrence recorded owners known previous previousMember owner

/-- Filtering whole group records preserves retained failures on every survivor. -/
theorem State.RetainedFailures.filterGroups {queue : State} {work failed}
    (prior : queue.RetainedFailures work failed) (keep : GroupNode → Bool)
    : ({ queue with groupNodes := queue.groupNodes.filter keep }).RetainedFailures work
        failed :=
  ⟨
    fun occurrence recorded owners known group member contributes =>
      prior.retained occurrence recorded owners known group (List.mem_filter.mp member).1
        contributes,
    prior.fresh
  ⟩

/-- Filtering task nodes retains the original first match when that node is kept. -/
private theorem taskNode_filter_lookup {nodes : List TaskNode} {occurrence task}
    (found : nodes.find? (fun node => node.task.occurrence == occurrence) = some task)
    (keep : TaskNode → Bool) (kept : keep task = true)
    : (nodes.filter keep).find? (fun node => node.task.occurrence == occurrence)
      = some task := by
  induction nodes with
  | nil => cases found
  | cons head rest ih =>
      by_cases selected : (head.task.occurrence == occurrence) = true
      · have same : head = task := by simpa [List.find?_cons, selected] using found
        subst head
        simp [kept, selected]
      · have tail : rest.find? (fun node => node.task.occurrence == occurrence) = some task := by
          simpa [List.find?_cons, selected] using found
        by_cases keepHead : keep head = true
        · simpa [List.filter_cons, keepHead, List.find?_cons, selected] using ih tail
        · simpa [List.filter_cons, keepHead] using ih tail

/-- Removing a failed subtree retains each rejected task with a surviving owning group.
Witness: that group satisfies the handler's last-owner retention predicate.
-/
theorem State.RetainedFailures.removeGroup {queue : State} {work failed}
    (prior : queue.RetainedFailures work failed) (ref : NodeRef)
    : (queue.removeGroup ref).RetainedFailures work failed := by
  refine ⟨?_, prior.fresh⟩
  intro occurrence recorded owners known group member contributes
  obtain ⟨listed, task, found, rejection, owner⟩ := prior.retained occurrence recorded owners
    known group (List.mem_filter.mp member).1 contributes
  refine ⟨listed, task, ?_, rejection, owner⟩
  apply taskNode_filter_lookup found
  obtain ⟨ownerGroup, included, equal⟩ := List.mem_map.mp owner
  apply List.any_eq_true.mpr
  refine ⟨ownerGroup, included, List.any_eq_true.mpr ?_⟩
  exact ⟨group, member, beq_iff_eq.mpr equal.symm⟩

/-- Removing a task outside the failed inventory preserves every retained failure.
Witness: failed occurrences survive both the membership filter and task-node filter.
-/
theorem State.RetainedFailures.removeTask {queue : State} {work failed}
    (prior : queue.RetainedFailures work failed) (occurrence : Occurrence)
    (notFailed : occurrence ∉ failed)
    : (queue.removeTask occurrence).RetainedFailures work failed := by
  refine ⟨?_, prior.fresh⟩
  intro other recorded owners known group member contributes
  obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
  obtain ⟨listed, task, found, rejection, owner⟩ :=
    prior.retained other recorded owners known old oldMember contributes
  have different : other ≠ occurrence := fun equal => notFailed (equal ▸ recorded)
  have unequal : (other == occurrence) = false :=
    Bool.eq_false_iff.mpr (fun equal => different ((occurrence_beq_iff_eq _ _).mp equal))
  refine ⟨
    List.mem_filter.mpr ⟨listed, by simp [bne, unequal]⟩,
    task,
    ?_,
    rejection,
    owner
  ⟩
  apply taskNode_filter_lookup found
  have same := (occurrence_beq_iff_eq _ _).mp
    (List.find?_some (p := fun node : TaskNode => node.task.occurrence == other) found)
  simp only [same, bne, unequal, Bool.not_false]

/-- A live group with no replayable rejection has no failed contributor in the inventory.
Witness: a contributing failed task would be listed with a rejected first-match record.
-/
theorem State.RetainedFailures.unrejected_noFailedContributor
    {queue : State} {work failed} (prior : queue.RetainedFailures work failed)
    {group : GroupNode} (member : group ∈ queue.groupNodes)
    (unrejected : queue.rejectedTask? group = none)
    {occurrence owners} (known : TaskHasOwners work occurrence owners)
    (owner : group.group.node.ref ∈ owners)
    : occurrence ∉ failed := by
  intro recorded
  obtain ⟨listed, task, found, rejection, _⟩ :=
    prior.retained occurrence recorded owners known group member owner
  have empty := State.rejectedTask?_eq_none_iff.mp unrejected occurrence listed task found
  simp [empty] at rejection

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
