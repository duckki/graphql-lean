import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.StartupTaskProgress
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedTaskRemoval
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedFailureTaskRetention
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedDrainProjection
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedCleanupTargets
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.UnsettledTaskRetention
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ResourceRecords

/-! Unsettled-task ownership through successful draining and cached startup removal.
Pending accounting rules out
successful selection of unfinished work; actual removal supplies the last-owner abort.
No output-filter cleanup oracle or computation-node existence is assumed.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open WorkQueueSemantics (NodeRefs Occurrence)

private theorem readyFacts {queue : ReferenceWorkQueue.State}
    {group : ReferenceWorkQueue.GroupNode} (selected : fusedReadyGroup queue = some group)
    : group ∈ queue.groupNodes ∧ group.pending = 0 := by
  unfold fusedReadyGroup at selected
  obtain ⟨key, _, choice⟩ := List.exists_of_findSome?_eq_some selected
  cases found : queue.groupNode? key with
  | none => simp [found] at choice
  | some candidate =>
      simp only [found] at choice
      change (if candidate.pending == 0 then some candidate else none) = some group at choice
      split at choice
      · rename_i ready
        cases Option.some.inj choice
        exact ⟨List.mem_of_find?_eq_some found, beq_iff_eq.mp ready⟩
      · cases choice

private theorem targetSurvives (fuel : Nat) (state : State) (targets : List CleanupTarget)
    (unique : targets.Nodup) (available : List (Occurrence × Nat))
    {target : CleanupTarget} (member : target ∈ targets)
    : target ∈ (State.drainReadyGroups.go available fuel state targets).2.2.1 := by
  obtain ⟨suffix, same⟩ := (state.drainReadyGroups_go_targets fuel targets unique available).2
  rw [← same]
  exact List.mem_append_left _ member

private theorem ownerLookup {queue : ReferenceWorkQueue.State} {key : Nat}
    (present : key ∈ queue.groupNodes.map (fun group => group.group.node.ref))
    : ∃ group, queue.groupNode? key = some group := by
  cases found : queue.groupNode? key with
  | some group => exact ⟨group, rfl⟩
  | none =>
      obtain ⟨group, member, same⟩ := List.mem_map.mp present
      exact False.elim ((List.find?_eq_none.mp found group member) (by simp [same]))

-----------------------------------------------------------------------------------------
-- Actual bounded draining preserves an unsettled owner or returns its abort
-----------------------------------------------------------------------------------------

theorem drain_unsettledTask_available {state : State} {work : Work}
    {parents : Nat → NodeRefs} {settled : List Occurrence}
    (running : state.stopped = false) (frame : state.queue.TaskOwnerFrame work)
    (forest : state.queue.RemovalForest parents) (task : ReferenceWorkQueue.Task)
    (catalogue : state.queue.task? task.occurrence = some task)
    (links
      : state.queue.TaskLinkedOn task.occurrence
          (task.groups.map Execution.DeliveryNode.ref))
    (bounded : state.queue.PendingBound (fun _ => True) settled)
    (fresh : task.occurrence ∉ settled)
    (owned
      : ∃ owner ∈ task.groups, ∃ group, state.queue.groupNode? owner.ref = some group)
    (fuel : Nat) (targets : List CleanupTarget) (unique : targets.Nodup)
    (unrejected
      : state.queue.TaskRejectionsSatisfy (fun rejected _ => rejected ≠ task.occurrence))
    (available : List (Occurrence × Nat))
    (licensed
      : ∀ occurrence errors,
          (occurrence, errors) ∈ available → occurrence ≠ task.occurrence)
    : let reduced := State.drainReadyGroups.go available fuel state targets
      (reduced.1.queue.TaskLinkedOn task.occurrence
          (task.groups.map Execution.DeliveryNode.ref)
        ∧ ∃ owner ∈ task.groups,
            ∃ group, reduced.1.queue.groupNode? owner.ref = some group)
      ∨ .task task.occurrence ∈ reduced.2.2.1 := by
  induction fuel generalizing state targets with
  | zero => exact .inl ⟨links, owned⟩
  | succ fuel ih =>
      rw [State.drainReadyGroups_go_eq fuel state targets available]
      cases selected : fusedReadyGroup state.queue with
      | none => exact .inl ⟨links, owned⟩
      | some group =>
          simp only
          obtain ⟨member, zero⟩ := readyFacts selected
          let released := state.queue.finishGroupSuccess group
          let preparing : State := { state with queue := released.1 }
          let active := preparing.startNewWork released.2.2 {} targets available
          have all := bounded.allSettled member trivial zero
          have unlisted : task.occurrence ∉ group.tasks := fun listed => fresh (all
            task.occurrence listed)
          have afterFrame := frame.finishGroupSuccess group member
          have afterForest := forest.finishGroupSuccess group
          have afterLinks := links.finishOtherGroupSuccess group unlisted
          have afterCatalogue : preparing.queue.task? task.occurrence = some task := by
            change (state.queue.finishGroupSuccess group).1.task? task.occurrence = some task
            simpa only [ReferenceWorkQueue.State.task?,
              ReferenceWorkQueue.State.finishGroupSuccess_tasks] using catalogue
          have afterOwned : ∃ owner ∈ task.groups, ∃ ownerNode,
              preparing.queue.groupNode? owner.ref = some ownerNode := by
            obtain ⟨owner, contributes, old, found⟩ := owned
            have present : owner.ref ∈ state.queue.groupNodes.map (fun node =>
              node.group.node.ref) :=
              List.mem_map.mpr ⟨old, List.mem_of_find?_eq_some found,
                ReferenceWorkQueue.State.groupNode?_ref found⟩
            have kept := finishGroupSuccess_linkedOwner_present links group member unlisted
              (List.mem_map_of_mem contributes) present
            exact ⟨owner, contributes, ownerLookup kept⟩
          have same : active.1.queue = (released.1.startNewWork released.2.2 available).1 := by
            simpa only [List.foldl_nil]
              using State.startNewWork_queue preparing released.2.2 {}
                targets running available afterFrame afterForest
          have nextFrame : active.1.queue.TaskOwnerFrame work := by
            rw [same]; exact afterFrame.startNewWork _ available
          have nextForest : active.1.queue.RemovalForest parents := by
            rw [same]; exact afterForest.startNewWork _ available
          have nextBound : active.1.queue.PendingBound (fun _ => True) settled := by
            rw [same]; exact (bounded.finishGroupSuccess group all).startNewWork _ available
          have nextCatalogue : active.1.queue.task? task.occurrence = some task := by
            rw [same]
            simpa only [ReferenceWorkQueue.State.task?,
              ReferenceWorkQueue.State.startNewWork_tasks]
              using afterCatalogue
          have nextRunning := (State.startNewWork_stopped preparing released.2.2 {}
            targets available).trans running
          have nextUnique := State.startNewWork_targets_nodup preparing released.2.2 {} targets
            unique available
          have afterUnrejected := unrejected.finishGroupSuccess group
          rcases startNewWork_linkedTask_progress_available preparing released.2.2 {} task targets
              unique afterCatalogue afterLinks afterOwned afterUnrejected available licensed
              with kept | requested
          · exact ih nextRunning nextFrame nextForest nextCatalogue kept.1 nextBound kept.2
              active.2.1 nextUnique
              (State.startNewWork_taskRejections afterUnrejected released.2.2 {} targets
                available licensed)
          · exact .inr (targetSurvives fuel active.1 active.2.1 nextUnique available requested)

/-- Existing empty-snapshot drain progress specializes the actual-snapshot theorem. -/
theorem drain_unsettledTask {state : State} {work : Work} {parents : Nat → NodeRefs}
    {settled : List Occurrence} (running : state.stopped = false)
    (frame : state.queue.TaskOwnerFrame work) (forest : state.queue.RemovalForest parents)
    (task : ReferenceWorkQueue.Task)
    (catalogue : state.queue.task? task.occurrence = some task)
    (links
      : state.queue.TaskLinkedOn task.occurrence
          (task.groups.map Execution.DeliveryNode.ref))
    (bounded : state.queue.PendingBound (fun _ => True) settled)
    (fresh : task.occurrence ∉ settled)
    (owned
      : ∃ owner ∈ task.groups, ∃ group, state.queue.groupNode? owner.ref = some group)
    (fuel : Nat) (targets : List CleanupTarget) (unique : targets.Nodup)
    (unrejected
      : state.queue.TaskRejectionsSatisfy (fun rejected _ => rejected ≠ task.occurrence))
    : let reduced := State.drainReadyGroups.go [] fuel state targets
      (reduced.1.queue.TaskLinkedOn task.occurrence
          (task.groups.map Execution.DeliveryNode.ref)
        ∧ ∃ owner ∈ task.groups,
            ∃ group, reduced.1.queue.groupNode? owner.ref = some group)
      ∨ .task task.occurrence ∈ reduced.2.2.1 :=
  drain_unsettledTask_available running frame forest task catalogue links bounded fresh
    owned fuel targets unique unrejected []
    (by intro occurrence errors impossible; cases impossible)

-----------------------------------------------------------------------------------------
-- Convert that same endpoint/target witness to concrete task-resource representation
-----------------------------------------------------------------------------------------

/-- Local actual-drain target. Its owner, membership, pending and source-provenance frames
are ordinary implementation invariants; no caller supplies cleanup or a desired endpoint.
FusedTaskHandlerProgress constructs these premises at generated handler boundaries.
-/
def FusedUnsettledDrainProgress : Prop :=
  ∀ (state : State) (work : Work) (parents : Nat → NodeRefs) (settled : List Occurrence)
    (task : ReferenceWorkQueue.Task) (targets : List CleanupTarget),
    state.stopped = false
    → state.queue.TaskOwnerFrame work
    → state.queue.RemovalForest parents
    → state.queue.task? task.occurrence = some task
    → state.queue.TaskLinkedOn task.occurrence
        (task.groups.map Execution.DeliveryNode.ref)
    → state.queue.PendingBound (fun _ => True) settled
    → task.occurrence ∉ settled
    → (∃ owner ∈ task.groups, ∃ group, state.queue.groupNode? owner.ref = some group)
    → targets.Nodup
    → state.queue.TaskRejectionsSatisfy (fun rejected _ => rejected ≠ task.occurrence)
    → let reduced := state.drainReadyGroups targets
      RecordTargetRepresented reduced.1.queue (.task task.occurrence)
      ∨ .abortTask task.occurrence ∈ reduced.2.2.1.flatMap CleanupTarget.effects

/-- Actual supplied cache snapshots preserve unfinished task representation or emit its abort.
The tracked task is absent from availability; other task failures may remove any owner.
-/
theorem fusedUnsettledDrainProgress_available {state : State} {work parents settled}
    (task : ReferenceWorkQueue.Task) (targets : List CleanupTarget)
    (running : state.stopped = false) (frame : state.queue.TaskOwnerFrame work)
    (forest : state.queue.RemovalForest parents)
    (catalogue : state.queue.task? task.occurrence = some task)
    (links
      : state.queue.TaskLinkedOn task.occurrence
          (task.groups.map Execution.DeliveryNode.ref))
    (bounded : state.queue.PendingBound (fun _ => True) settled)
    (fresh : task.occurrence ∉ settled)
    (owned
      : ∃ owner ∈ task.groups, ∃ group, state.queue.groupNode? owner.ref = some group)
    (unique : targets.Nodup)
    (unrejected
      : state.queue.TaskRejectionsSatisfy (fun rejected _ => rejected ≠ task.occurrence))
    (available : List (Occurrence × Nat))
    (licensed
      : ∀ occurrence errors,
          (occurrence, errors) ∈ available → occurrence ≠ task.occurrence)
    : let reduced := state.drainReadyGroups targets available
      RecordTargetRepresented reduced.1.queue (.task task.occurrence)
      ∨ .abortTask task.occurrence ∈ reduced.2.2.1.flatMap CleanupTarget.effects := by
  rcases drain_unsettledTask_available running frame forest task catalogue links bounded fresh owned
      state.queue.groupNodes.length targets unique unrejected available licensed
      with kept | requested
  · obtain ⟨owner, contributes, group, found⟩ := kept.2
    have projection := state.drainReadyGroups_projection running frame forest targets available
    have finalUnrejected : (state.drainReadyGroups targets available).1.queue.TaskRejectionsSatisfy
        (fun rejected _ => rejected ≠ task.occurrence) := by
      have same : (state.drainReadyGroups targets available).1.queue
          = (state.queue.drainReadyGroups available).1 := congrArg Prod.fst projection
      rw [same]
      exact unrejected.drainReadyGroups available licensed
    exact .inl (.task found (kept.1 group (List.mem_of_find?_eq_some found)
      (List.mem_map.mpr ⟨owner, contributes, (ReferenceWorkQueue.State.groupNode?_ref found).symm⟩))
      finalUnrejected.unrejected_lookup)
  · exact .inr (List.mem_flatMap.mpr ⟨.task task.occurrence, requested, List.mem_cons_self⟩)

theorem FusedUnsettledDrainProgress_holds : FusedUnsettledDrainProgress := by
  intro state work parents settled task targets running frame forest catalogue links bounded
    fresh owned unique unrejected
  exact fusedUnsettledDrainProgress_available task targets running frame forest catalogue
    links bounded fresh owned unique unrejected []
    (by intro occurrence errors impossible; cases impossible)

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
