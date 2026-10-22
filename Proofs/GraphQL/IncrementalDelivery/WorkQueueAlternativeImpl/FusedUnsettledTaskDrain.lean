import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedTaskRemoval
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedFailureTaskRetention
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedDrainProjection
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedCleanupTargets
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.UnsettledTaskRetention
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ResourceRecords

/-! Unsettled-task ownership through the actual mixed drain. Pending accounting rules out
successful selection of unfinished work; actual removal supplies the last-owner abort.
No output-filter cleanup oracle or computation-node existence is assumed.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open WorkQueueSemantics (NodeRefs Occurrence)

private theorem readyFacts {queue : ReferenceWorkQueue.State}
    {group : ReferenceWorkQueue.GroupNode} (selected : fusedReadyGroup queue = some group)
    : group ∈ queue.groupNodes
      ∧ (queue.rejectedTask? group = none → group.pending = 0) := by
  unfold fusedReadyGroup at selected
  obtain ⟨key, _, choice⟩ := List.exists_of_findSome?_eq_some selected
  cases found : queue.groupNode? key with
  | none => simp [found] at choice
  | some candidate =>
      simp only [found] at choice
      change (if (queue.rejectedTask? candidate).isSome || candidate.pending == 0 then some candidate else none) = some group at choice
      split at choice
      · rename_i ready
        cases Option.some.inj choice
        exact ⟨List.mem_of_find?_eq_some found, fun healthy => by
          simpa only [healthy, Option.isSome_none, Bool.false_or, beq_iff_eq] using ready⟩
      · cases choice

private theorem targetSurvives (fuel : Nat) (state : State) (targets : List CleanupTarget)
    (unique : targets.Nodup) {target : CleanupTarget} (member : target ∈ targets)
    : target ∈ (State.drainReadyGroups.go fuel state targets).2.2 := by
  obtain ⟨suffix, same⟩ := (state.drainReadyGroups_go_targets fuel targets unique).2
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
    : let reduced := State.drainReadyGroups.go fuel state targets
      (reduced.1.queue.TaskLinkedOn task.occurrence
          (task.groups.map Execution.DeliveryNode.ref)
        ∧ ∃ owner ∈ task.groups,
            ∃ group, reduced.1.queue.groupNode? owner.ref = some group)
      ∨ .task task.occurrence ∈ reduced.2.2 := by
  induction fuel generalizing state targets with
  | zero => exact .inl ⟨links, owned⟩
  | succ fuel ih =>
      rw [State.drainReadyGroups_go_eq]
      cases selected : fusedReadyGroup state.queue with
      | none => exact .inl ⟨links, owned⟩
      | some group =>
          simp only
          obtain ⟨member, zero⟩ := readyFacts selected
          cases cached : state.queue.rejectedTask? group with
          | some rejection =>
              obtain ⟨failed, errors⟩ := rejection
              simp only
              obtain ⟨_, node, found, rejected⟩ := ReferenceWorkQueue.State.rejectedTask?_sound cached
              let stored : State := { state with queue := state.queue.putTaskNode { node with rejection := some errors } }
              have storedFrame : stored.queue.TaskOwnerFrame work :=
                frame.putExistingTaskNode node (List.mem_of_find?_eq_some found)
                  { node with rejection := some errors } rfl
              have storedForest : stored.queue.RemovalForest parents :=
                ⟨forest.uniqueChildren, forest.canonical, forest.increasing⟩
              have storedUnrejected : stored.queue.TaskRejectionsSatisfy
                  (fun rejected _ => rejected ≠ task.occurrence) :=
                unrejected.putTaskNode _ (fun _ _ =>
                  unrejected node (List.mem_of_find?_eq_some found) errors rejected)
              let reduced := state.taskFailure failed errors targets
              have projection := state.taskFailure_projection frame forest failed errors targets
              have same : reduced.1.queue = (state.queue.taskFailure failed errors).1 :=
                congrArg Prod.fst projection
              have nextFrame : reduced.1.queue.TaskOwnerFrame work := by
                rw [same]; exact frame.taskFailure failed errors
              have nextForest : reduced.1.queue.RemovalForest parents := by
                rw [same]
                exact forest.of_subset (state.queue.taskFailure_groupNodes_sublist failed errors).subset
              have nextBound : reduced.1.queue.PendingBound (fun _ => True) settled := by
                rw [same]; exact bounded.taskFailure_preserves failed errors
              have nextCatalogue : reduced.1.queue.task? task.occurrence = some task := by
                rw [same]
                simpa only [ReferenceWorkQueue.State.task?,
                  ReferenceWorkQueue.State.taskFailure_tasks]
                  using catalogue
              have nextRunning := (state.taskFailure_stopped failed errors targets).trans running
              have nextUnique := (state.taskFailure_targets failed errors targets unique).1
              have different : failed ≠ task.occurrence :=
                (ReferenceWorkQueue.State.taskNode?_some found).2 ▸
                  unrejected node (List.mem_of_find?_eq_some found) errors rejected
              have nextUnrejected : reduced.1.queue.TaskRejectionsSatisfy
                  (fun rejected _ => rejected ≠ task.occurrence) := by
                rw [same]
                exact unrejected.taskFailure failed errors different
              have step := failureFold_unsettledTask errors node.task.groups (stored, [], targets)
                storedFrame storedForest task catalogue links owned unique storedUnrejected
              have reducedEq : reduced = node.task.groups.foldl (fusedFailureGroupStep errors)
                  (stored, [], targets) := by simp only [reduced, State.taskFailure, found]; rfl
              rw [← reducedEq] at step
              change (reduced.1.queue.TaskLinkedOn task.occurrence
                  (task.groups.map Execution.DeliveryNode.ref)
                ∧ ∃ owner ∈ task.groups, ∃ group, reduced.1.queue.groupNode? owner.ref = some group)
                ∨ .task task.occurrence ∈ reduced.2.2 at step
              rcases step with kept | requested
              · exact ih nextRunning nextFrame nextForest nextCatalogue kept.1 nextBound
                  kept.2 reduced.2.2 nextUnique nextUnrejected
              · exact .inr (targetSurvives fuel reduced.1 reduced.2.2 nextUnique requested)
          | none =>
              simp only
              let released := state.queue.finishGroupSuccess group
              let active := ({ state with queue := released.1 }).startNewWork released.2.2 {} targets
              have all := bounded.allSettled member trivial (zero cached)
              have unlisted : task.occurrence ∉ group.tasks := fun listed => fresh (all task.occurrence listed)
              have same : active.1.queue = released.1.startNewWork released.2.2 := by
                simpa only [List.foldl_nil]
                  using State.startNewWork_queue
                    { state with queue := released.1 } released.2.2 {} targets running
              have nextFrame : active.1.queue.TaskOwnerFrame work := by
                rw [same]; exact (frame.finishGroupSuccess group member).startNewWork _
              have nextForest : active.1.queue.RemovalForest parents := by
                rw [same]; exact (forest.finishGroupSuccess group).startNewWork _
              have nextBound : active.1.queue.PendingBound (fun _ => True) settled := by
                rw [same]; exact (bounded.finishGroupSuccess group all).startNewWork _
              have nextLinks : active.1.queue.TaskLinkedOn task.occurrence (task.groups.map Execution.DeliveryNode.ref) := by
                rw [same]; exact (links.finishOtherGroupSuccess group unlisted).startNewWork _
              have nextCatalogue : active.1.queue.task? task.occurrence = some task := by
                rw [same]
                change (released.1.startNewWork released.2.2).tasks.find? _ = some task
                rw [(ReferenceWorkQueue.State.startNewWork_groupCore _ _).2.1]
                have unchanged : released.1.tasks = state.queue.tasks := by
                  rw [ReferenceWorkQueue.State.finishGroupSuccess_tasks]
                rw [unchanged]; exact catalogue
              have nextOwned : ∃ owner ∈ task.groups, ∃ group, active.1.queue.groupNode? owner.ref = some group := by
                obtain ⟨owner, contributes, old, found⟩ := owned
                have present : owner.ref ∈ state.queue.groupNodes.map (fun node => node.group.node.ref) :=
                  List.mem_map.mpr ⟨old, List.mem_of_find?_eq_some found,
                  ReferenceWorkQueue.State.groupNode?_ref found⟩
                have kept := finishGroupSuccess_linkedOwner_present links group member unlisted
                  (List.mem_map_of_mem contributes) present
                rw [same]
                apply Exists.intro owner
                refine ⟨contributes, ?_⟩
                apply ownerLookup
                rw [(ReferenceWorkQueue.State.startNewWork_groupCore _ _).1]
                exact kept
              have nextRunning := (State.startNewWork_stopped
                { state with queue := released.1 } released.2.2 {} targets).trans running
              have nextUnique := State.startNewWork_targets_nodup
                { state with queue := released.1 } released.2.2 {} targets unique
              exact ih nextRunning nextFrame nextForest nextCatalogue nextLinks nextBound
                nextOwned active.2 nextUnique
                (by
                  rw [same]
                  exact (unrejected.finishGroupSuccess group).startNewWork _)

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
      ∨ .abortTask task.occurrence ∈ reduced.2.2.flatMap CleanupTarget.effects

theorem FusedUnsettledDrainProgress_holds : FusedUnsettledDrainProgress := by
  intro state work parents settled task targets running frame forest catalogue links bounded fresh owned unique unrejected
  rcases drain_unsettledTask running frame forest task catalogue links bounded fresh owned
      state.queue.groupNodes.length targets unique unrejected with kept | requested
  · obtain ⟨owner, contributes, group, found⟩ := kept.2
    have projection := state.drainReadyGroups_projection running frame forest targets
    have finalUnrejected : (state.drainReadyGroups targets).1.queue.TaskRejectionsSatisfy
        (fun rejected _ => rejected ≠ task.occurrence) := by
      have same : (state.drainReadyGroups targets).1.queue = state.queue.drainReadyGroups.1 :=
        congrArg Prod.fst projection
      rw [same]
      exact unrejected.drainReadyGroups
    exact .inl (.task found (kept.1 group (List.mem_of_find?_eq_some found)
      (List.mem_map.mpr ⟨owner, contributes, (ReferenceWorkQueue.State.groupNode?_ref found).symm⟩))
      finalUnrejected.unrejected_lookup)
  · exact .inr (List.mem_flatMap.mpr ⟨.task task.occurrence, requested, List.mem_cons_self⟩)

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
