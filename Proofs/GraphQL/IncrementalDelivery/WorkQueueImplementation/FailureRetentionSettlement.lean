import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureRetentionRegistration
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PendingAccounting

/-! Successful release cannot discard the retained rejection of a failed contributor. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (ExecutionGroupValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Successful closure preserves retained failures when its flushed tasks are not failed.
Witness: each task removal is outside the failed inventory; final pruning only filters
whole group records and leaves the remaining task computations untouched.
-/
theorem State.RetainedFailures.finishGroupSuccess {queue : State} {work failed}
    (prior : queue.RetainedFailures work failed) (group : GroupNode)
    (notFailed : ∀ occurrence ∈ group.tasks, occurrence ∉ failed)
    : (queue.finishGroupSuccess group).1.RetainedFailures work failed := by
  let step (acc : State × List ExecutionGroupValue × NodeRefs) (occurrence : Occurrence) :=
    let (current, values, streams) := acc
    match current.taskNode? occurrence with
    | none => (current, values, streams)
    | some node =>
        let values := match node.value with
          | none => values
          | some value => values ++ [value]
        (current.removeTask occurrence, values, streams ++ node.childStreams)
  have loop (tasks : List Occurrence) (safe : ∀ occurrence ∈ tasks, occurrence ∉ failed)
      (acc : State × List ExecutionGroupValue × NodeRefs)
      (valid : acc.1.RetainedFailures work failed)
      : (tasks.foldl step acc).1.RetainedFailures work failed := by
    induction tasks generalizing acc with
    | nil => exact valid
    | cons occurrence rest ih =>
        apply ih (fun other member => safe other (List.mem_cons_of_mem _ member))
        obtain ⟨current, values, streams⟩ := acc
        dsimp only [step]
        split
        · exact valid
        · exact valid.removeTask occurrence (safe occurrence List.mem_cons_self)
  let flushed := (group.tasks.foldl step (queue, [], [])).1
  have flushedRetained : flushed.RetainedFailures work failed :=
    loop group.tasks notFailed (queue, [], []) prior
  let current : State :=
    { flushed with
      groupNodes := flushed.groupNodes.filter
        (fun node => node.group.node.ref != group.group.node.ref)
      rootGroups := flushed.rootGroups.filter (· != group.group.node.ref) }
  have filtered : current.RetainedFailures work failed := flushedRetained.filterGroups _
  exact filtered.pruneEmptyGroups _

/-- Failure replay retains the same earlier failure inventory.
Witness: replacement keeps the task and supplies a rejection; owner processing removes
only groups and last-owner task records.
-/
theorem State.RetainedFailures.taskFailure_preserves {queue : State} {work failed}
    (prior : queue.RetainedFailures work failed) (occurrence : Occurrence) (errors : Nat)
    : (queue.taskFailure occurrence errors).1.RetainedFailures work failed := by
  cases found : queue.taskNode? occurrence with
  | none => simpa [State.taskFailure, found] using prior
  | some task =>
      rw [queue.taskFailure_eq occurrence errors task found]
      apply failureGroupFold_preserves (fun current => current.RetainedFailures work failed)
        (fun _ ref valid => valid.removeGroup ref)
      exact prior.putTaskNode found _ rfl (fun _ => rfl)

/-- A fresh failed source task is retained on every surviving contributor.
Witness: the success-only ledger still links its pending token at every owner. Permanent
registration excludes earlier failure at a fresh ref; exact source ownership identifies
the rejected task without storing any new failure-origin metadata.
-/
theorem State.RetainedFailures.taskFailure {queue : State} {work failed settled}
    (prior : queue.RetainedFailures work failed)
    (ledger : queue.PendingAccounting work settled) (occurrence : Occurrence)
    (errors : Nat) (task : TaskNode) (found : queue.taskNode? occurrence = some task)
    (fresh : occurrence ∉ settled)
    (source : (GraphEvent.taskFailure occurrence errors).MatchesWork work)
    : (queue.taskFailure occurrence errors).1.RetainedFailures work
        (occurrence :: failed) := by
  have member := ledger.started task (List.mem_of_find?_eq_some found)
  obtain ⟨⟨_, payload, producer, _, descriptor⟩, _⟩ := ledger.matching task.task member
  have same : task.task.occurrence = occurrence :=
    (occurrence_beq_iff_eq _ _).mp
      (List.find?_some (p := fun node : TaskNode => node.task.occurrence == occurrence) found)
  obtain ⟨owners, birth, path, known⟩ := source
  rw [same] at descriptor
  let stored := queue.putTaskNode { task with rejection := some errors }
  have oldRetained : stored.RetainedFailures work failed :=
    prior.putTaskNode found _ rfl (fun _ => rfl)
  have retained : stored.RetainedFailures work (occurrence :: failed) := by
    refine ⟨?_, ?_⟩
    · intro other recorded otherOwners taskKnown group included owner
      rcases List.mem_cons.mp recorded with rfl | old
      · obtain ⟨otherBirth, otherPayload, otherKnown⟩ := taskKnown
        have exactOwners := (descriptor.unique otherKnown).1
        have contributes : group.group.node.ref ∈ task.task.groups.map Execution.DeliveryNode.ref :=
          exactOwners.symm ▸ owner
        have listed := ledger.links task.task member (same ▸ fresh) group included contributes
        refine ⟨same ▸ listed, { task with rejection := some errors }, ?_, rfl, contributes⟩
        exact State.putTaskNode_lookup_same found _ same
      · exact oldRetained.retained other old otherOwners taskKnown group included owner
    · intro ref absent other recorded otherOwners taskKnown owner
      rcases List.mem_cons.mp recorded with rfl | old
      · obtain ⟨otherBirth, otherPayload, otherKnown⟩ := taskKnown
        have exactOwners := (descriptor.unique otherKnown).1
        exact absent (ledger.taskGroups task.task member ref (exactOwners.symm ▸ owner))
      · exact prior.fresh ref absent other old otherOwners taskKnown owner
  rw [queue.taskFailure_eq occurrence errors task found]
  exact failureGroupFold_preserves
    (fun current => current.RetainedFailures work (occurrence :: failed))
    (fun _ ref valid => valid.removeGroup ref) errors task.task.groups _ retained

/-- Sound membership and an unrejected group exclude every failed task in its task list. -/
theorem State.RetainedFailures.unrejected_tasks_notFailed {queue : State} {work failed}
    (prior : queue.RetainedFailures work failed) (sound : queue.GroupMembershipSound)
    (matching : queue.RegisteredTasksMatch work) {group : GroupNode}
    (member : group ∈ queue.groupNodes) (unrejected : queue.rejectedTask? group = none)
    : ∀ occurrence ∈ group.tasks, occurrence ∉ failed := by
  intro occurrence listed
  obtain ⟨task, registered, same, owner⟩ := sound group member occurrence listed
  obtain ⟨⟨_, payload, producer, _, known⟩, _⟩ := matching task registered
  rw [same] at known
  exact prior.unrejected_noFailedContributor member unrejected ⟨producer, payload, known⟩ owner

/-- Every finite drain prefix preserves retained failures.
Witness: success flushes an unrejected sound task list; rejection replay removes owners
while retaining the rejected computation wherever another owner survives.
-/
theorem State.RetainedFailures.drainReadyGroups_go {queue : State} {work failed}
    (prior : queue.RetainedFailures work failed) (sound : queue.GroupMembershipSound)
    (matching : queue.RegisteredTasksMatch work) (fuel : Nat)
    : (State.drainReadyGroups.go fuel queue).1.RetainedFailures work failed := by
  let invariant (current : State) := current.RetainedFailures work failed
    ∧ current.GroupMembershipSound ∧ current.RegisteredTasksMatch work
  have preserved := State.drainReadyGroups_go_preserves invariant
    (fun current node valid member _ unrejected _ => by
      have safe := valid.1.unrejected_tasks_notFailed valid.2.1 valid.2.2 member unrejected
      exact ⟨(valid.1.finishGroupSuccess node safe).startNewWork _,
        (valid.2.1.finishGroupSuccess node).startNewWork _,
        (valid.2.2.finishGroupSuccess node).startNewWork _⟩)
    (fun _ _ occurrence errors valid _ _ _ =>
      ⟨valid.1.taskFailure_preserves occurrence errors,
        valid.2.1.taskFailure occurrence errors, valid.2.2.taskFailure occurrence errors⟩)
    (show invariant queue from ⟨prior, sound, matching⟩) fuel
  exact preserved.1

/-- Full draining preserves retained failures under sound task registration. -/
theorem State.RetainedFailures.drainReadyGroups {queue : State} {work failed}
    (prior : queue.RetainedFailures work failed) (sound : queue.GroupMembershipSound)
    (matching : queue.RegisteredTasksMatch work)
    : queue.drainReadyGroups.1.RetainedFailures work failed :=
  prior.drainReadyGroups_go sound matching _

/-- A fresh successful task preserves the rejected computations of earlier failures.
Witness: success-only counter debt makes every flushed membership a successful settlement;
source-disjoint failures cannot be retired by that flush. Child registration and the final
rejection drain preserve the same retention certificate.
-/
theorem State.RetainedFailures.taskSuccess {queue : State} {work failed settled}
    (prior : queue.RetainedFailures work failed)
    (ledger : queue.PendingAccounting work settled) (occurrence : Occurrence)
    (result : TaskResult) (taskNode : TaskNode)
    (found : queue.taskNode? occurrence = some taskNode) (fresh : occurrence ∉ settled)
    (notFailed : occurrence ∉ failed) (disjoint : ∀ task ∈ settled, task ∉ failed)
    (uniqueOwners : (taskNode.task.groups.map Execution.DeliveryNode.ref).Nodup)
    (childrenMatch : ∀ task ∈ result.work.tasks, TaskMatches work task)
    : (queue.taskSuccess occurrence result).1.RetainedFailures work failed := by
  rw [queue.taskSuccess_eq occurrence result taskNode found]
  let stored := queue.putTaskNode { taskNode with value := some result.value }
  let integrated := (stored.maybeIntegrateWork result.work (some occurrence)).1
  have storedRefs : stored.GroupRefsUnique := ledger.refs
  have storedMembers : stored.TaskMembershipsUnique := ledger.memberships
  have storedCounts : stored.PendingBound (fun _ => True) settled := ledger.pending
  have storedCovered : stored.TaskGroupsRegistered := ledger.taskGroups
  have storedSound : stored.GroupMembershipSound := ledger.sound
  have storedMatch : stored.RegisteredTasksMatch work := ledger.matching
  have integratedLinks : integrated.UnsettledTaskLinks settled :=
    (ledger.links.putTaskNode _).maybeIntegrateWork storedRefs storedCovered result.work
      (some occurrence)
  have integratedCounts : integrated.PendingBound (fun _ => True) settled :=
    storedCounts.maybeIntegrateWork result.work (some occurrence)
  have integratedRefs := storedRefs.maybeIntegrateWork result.work (some occurrence)
  have integratedMembers := storedMembers.maybeIntegrateWork result.work (some occurrence)
  have integratedSound := storedSound.maybeIntegrateWork result.work (some occurrence)
  have integratedMatch := storedMatch.maybeIntegrateWork result.work childrenMatch
    (some occurrence)
  have taskMember : taskNode.task ∈ integrated.tasks := by
    rw [State.maybeIntegrateWork_tasks_append]
    exact List.mem_append_left _ (ledger.started taskNode (List.mem_of_find?_eq_some found))
  have same : taskNode.task.occurrence = occurrence :=
    (occurrence_beq_iff_eq _ _).mp (List.find?_some
      (p := fun candidate : TaskNode => candidate.task.occurrence == occurrence) found)
  have owned := integratedLinks.ownedExactlyBy integratedSound integratedMatch taskMember
    (same.symm ▸ fresh)
  rw [same] at owned
  have debt : integrated.PendingDebtBound (fun _ => True) (occurrence :: settled)
      (taskNode.task.groups.map Execution.DeliveryNode.ref) :=
    integratedCounts.beginSettlement integratedMembers
      (fun node member _ => owned node member) fresh
  have storedRetained : stored.RetainedFailures work failed :=
    prior.putTaskNode found _ rfl (fun rejected => rejected)
  have integratedRetained := storedRetained.maybeIntegrateWork ledger.refs result.work
    (some occurrence)
  let invariant (current : State) := current.GroupRefsUnique
    ∧ current.RetainedFailures work failed ∧ current.GroupMembershipSound
    ∧ current.RegisteredTasksMatch work
  have initial : invariant integrated :=
    ⟨integratedRefs, integratedRetained, integratedSound, integratedMatch⟩
  have safe : ∀ task ∈ occurrence :: settled, task ∉ failed := by
    intro task member
    rcases List.mem_cons.mp member with rfl | earlier
    · exact notFailed
    · exact disjoint task earlier
  have loop := successGroupFold_preservesBound (fun _ => True) (occurrence :: settled)
    invariant (fun _ valid => valid.1) (by intros; trivial)
    (fun _ node valid selected =>
      ⟨valid.1.putGroupNode _, valid.2.1.putGroupNodeSameTasks valid.1 node
        (List.mem_of_find?_eq_some selected) _ rfl rfl,
        valid.2.2.1.putGroupNode _ (valid.2.2.1 node (List.mem_of_find?_eq_some selected)),
        valid.2.2.2.putGroupNode _⟩)
    (fun _ node _ valid _ _ _ _ all =>
      ⟨valid.1.finishGroupSuccess node,
        valid.2.1.finishGroupSuccess node (fun task member => safe task (all task member)),
        valid.2.2.1.finishGroupSuccess node, valid.2.2.2.finishGroupSuccess node⟩)
    taskNode.task.groups uniqueOwners (integrated, [], {}) initial debt
  exact ((loop.1.2.1.startNewWork _).drainReadyGroups
    (loop.1.2.2.1.startNewWork _) (loop.1.2.2.2.startNewWork _))

/-- A matched stream item preserves earlier failure retention while integrating children. -/
theorem State.RetainedFailures.integrateStreamItem {queue : State} {work failed}
    (prior : queue.RetainedFailures work failed) (refs : queue.GroupRefsUnique)
    (item : StreamItem)
    : (queue.integrateStreamItem item).RetainedFailures work failed :=
  ((prior.maybeIntegrateWork refs item.work).pruneEmptyGroups _).startNewWork _

/-- Matched stream items preserve retained failures through child integration and draining.
Witness: integration never clears a rejection; the final drain uses sound memberships
and exact task provenance to distinguish successful closure from rejection replay.
-/
theorem State.RetainedFailures.streamItems {queue : State} {work failed stream items}
    (prior : queue.RetainedFailures work failed) (refs : queue.GroupRefsUnique)
    (sound : queue.GroupMembershipSound) (matching : queue.RegisteredTasksMatch work)
    (source : (GraphEvent.streamItems stream items).MatchesWork work)
    : (queue.streamItems stream items).1.RetainedFailures work failed := by
  let step (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List Execution.StreamItemValue) (item : StreamItem) :=
    let (current, groups, streams, values) := acc
    let (integrated, newWork) := current.maybeIntegrateWork item.work
    let (pruned, nonempty) := integrated.pruneEmptyGroups newWork.newGroups
    (pruned.startNewWork { newWork with newGroups := nonempty },
      groups ++ nonempty, streams ++ newWork.newStreams, values ++ [item.value])
  let invariant (current : State) := current.RetainedFailures work failed
    ∧ current.GroupRefsUnique ∧ current.GroupMembershipSound ∧ current.RegisteredTasksMatch work
  have preserve (acc) (item : StreamItem) (member : item ∈ items)
      (valid : invariant acc.1) : invariant (step acc item).1 := by
    obtain ⟨current, groups, streams, values⟩ := acc
    have childrenMatch : ∀ task ∈ item.work.tasks, TaskMatches work task := by
      intro task included
      obtain ⟨address, payload, same, known⟩ := source.streamItem_childTask_producer member included
      exact ⟨⟨address, payload, _, same, known⟩,
        source.streamItem_childTask_groupsExact member included⟩
    exact ⟨valid.1.integrateStreamItem valid.2.1 item,
      ((valid.2.1.maybeIntegrateWork item.work none).pruneEmptyGroups _).startNewWork _,
      ((valid.2.2.1.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _,
      ((valid.2.2.2.maybeIntegrateWork item.work childrenMatch).pruneEmptyGroups _).startNewWork _⟩
  have loop (more : List StreamItem) (included : more.Subset items) (acc)
      (valid : invariant acc.1) : invariant (more.foldl step acc).1 := by
    induction more generalizing acc with
    | nil => exact valid
    | cons item rest ih =>
        exact ih (fun _ member => included (List.mem_cons_of_mem _ member)) _
          (preserve acc item (included List.mem_cons_self) valid)
  dsimp only [State.streamItems]
  split
  · exact prior
  · have final := loop items (fun _ member => member) (queue, [], [], [])
      ⟨prior, refs, sound, matching⟩
    exact final.1.drainReadyGroups final.2.2.1 final.2.2.2

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
