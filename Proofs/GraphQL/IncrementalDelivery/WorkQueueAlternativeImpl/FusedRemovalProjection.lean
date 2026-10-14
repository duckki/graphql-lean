import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedRemovalAccounting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedRemovalTaskRecords

/-! Full queue-state projection for the actual fused failed-group removal.
Accounting and task-record witnesses use the same returned walk endpoint. The record frame
is a local transition premise; deriving it at generated handlers and lifting to public
replay remain distinct obligations, not new host-source laws.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue
open WorkQueueSemantics (NodeRefs)
open ReferenceWorkQueue (Task)

private theorem removalTaskLive_mono {first second : ReferenceWorkQueue.State}
    (included : first.groupNodes.Sublist second.groupNodes) (task : Task)
    (live : removalTaskLive first task = true)
    : removalTaskLive second task = true := by
  obtain ⟨owner, contributes, present⟩ := List.any_eq_true.mp live
  obtain ⟨group, member, same⟩ := List.any_eq_true.mp present
  exact List.any_eq_true.mpr ⟨owner, contributes,
    List.any_eq_true.mpr ⟨group, included.subset member, same⟩⟩

-----------------------------------------------------------------------------------------
-- Actual walk retains exactly the records with a surviving contributing owner
-----------------------------------------------------------------------------------------

/-- The full shrinking walk computes the reference retention filter in original record
order and preserves the live-record frame, at any finite budget. Task-node equality is
paired with this actual endpoint's group store, never a separately chosen disposal trace.
-/
theorem removeGroup_walk_taskRecords {work : Work} (fuel : Nat) (state : State)
    (pending removed : NodeRefs) (targets : List CleanupTarget)
    (matching : state.queue.RegisteredTasksMatch work)
    (sound : state.queue.GroupMembershipSound) (frame : RemovalTaskFrame state.queue)
    : let final := State.removeGroup.walk fuel state pending removed targets
      final.1.queue.groupNodes.Sublist state.queue.groupNodes
      ∧ RemovalTaskFrame final.1.queue
      ∧ final.1.queue.taskNodes
        = state.queue.taskNodes.filter
            (fun node => removalTaskLive final.1.queue node.task) := by
  induction fuel generalizing state pending removed targets with
  | zero =>
      simp only [State.removeGroup.walk]
      exact ⟨.refl _, frame, (List.filter_eq_self.mpr frame.supported).symm⟩
  | succ fuel ih =>
      induction pending generalizing state removed targets with
      | nil =>
          simp only [State.removeGroup.walk]
          exact ⟨.refl _, frame, (List.filter_eq_self.mpr frame.supported).symm⟩
      | cons key rest tailIH =>
          cases found : state.queue.groupNode? key with
          | none =>
              simpa only [State.removeGroup.walk, found] using tailIH state removed targets
                matching sound frame
          | some group =>
              rw [State.removeGroup.walk, found]
              let erased := eraseRemovalGroup state key
              let folded := group.tasks.foldl fusedRemovalTaskStep (erased, targets)
              have erasedMatch := eraseRemovalGroup_registeredTasksMatch matching key
              have erasedSound := eraseRemovalGroup_groupMembershipSound sound key
              have book := fusedRemovalTaskFold_bookkeeping group.tasks (erased, targets)
                erasedMatch erasedSound
              have visit := fusedRemovalVisit_taskRecords matching sound frame found targets
              have next := ih folded.1 (group.childGroups ++ rest) (key :: removed) folded.2
                book.2.1 book.2.2 visit.2
              refine ⟨next.1.trans ?_, next.2.1, ?_⟩
              · rw [book.1]
                exact List.filter_sublist
              · change (State.removeGroup.walk fuel folded.1 (group.childGroups ++ rest)
                    (key :: removed) folded.2).1.queue.taskNodes = _
                rw [next.2.2, visit.1, List.filter_filter]
                apply List.filter_congr
                intro node _
                change (removalTaskLive
                    (State.removeGroup.walk fuel folded.1 (group.childGroups ++ rest)
                      (key :: removed) folded.2).1.queue node.task &&
                    removalTaskLive erased.queue node.task) = removalTaskLive
                    (State.removeGroup.walk fuel folded.1 (group.childGroups ++ rest)
                      (key :: removed) folded.2).1.queue node.task
                cases live
                      : removalTaskLive
                          (State.removeGroup.walk fuel folded.1
                            (group.childGroups ++ rest) (key :: removed) folded.2).1.queue
                          node.task with
                | false => simp only [Bool.false_and]
                | true =>
                    have prior := removalTaskLive_mono next.1 node.task live
                    have priorErased : removalTaskLive erased.queue node.task = true := by
                      unfold removalTaskLive at prior ⊢
                      rw [book.1] at prior
                      exact prior
                    simp only [priorErased, Bool.true_and]

-----------------------------------------------------------------------------------------
-- Combine compatible accounting and record projections into exact kernel equality
-----------------------------------------------------------------------------------------

private theorem queue_eq_of_core_and_taskNodes {first second : ReferenceWorkQueue.State}
    (core : registrationCore first = registrationCore second)
    (nodes : first.taskNodes = second.taskNodes)
    : first = second := by
  calc
    first = { registrationCore first with taskNodes := first.taskNodes } := rfl
    _ = { registrationCore second with taskNodes := second.taskNodes } := by
      rw [core, nodes]
    _ = second := rfl

/-- Exact local removal projection, using only independently stated structural bookkeeping
and live-record premises. Generated handler construction must discharge those premises;
neither conformance nor cleanup completeness is assumed by this local theorem.
-/
def FusedRemovalProjection : Prop :=
  ∀ (state : State) (work : Work) (parents : Nat → NodeRefs) (root : Nat)
    (targets : List CleanupTarget),
    state.queue.RegisteredTasksMatch work
    → state.queue.GroupMembershipSound
    → state.queue.RemovalForest parents
    → RemovalTaskFrame state.queue
    → (state.removeGroup root targets).1.queue = state.queue.removeGroup root

theorem FusedRemovalProjection_holds : FusedRemovalProjection := by
  intro state work parents root targets matching sound forest frame
  have core := FusedRemovalAccounting_holds state work parents root targets matching sound forest
  apply queue_eq_of_core_and_taskNodes core
  have records := removeGroup_walk_taskRecords (state.queue.groupNodes.length + 1)
    state [root] [] targets matching sound frame
  have groups := congrArg ReferenceWorkQueue.State.groupNodes core
  change (State.removeGroup.walk (state.queue.groupNodes.length + 1)
      state [root] [] targets).1.queue.groupNodes = (state.queue.removeGroup root).groupNodes
    at groups
  change (State.removeGroup.walk (state.queue.groupNodes.length + 1)
      state [root] [] targets).1.queue.taskNodes = _
  rw [records.2.2]
  change state.queue.taskNodes.filter (fun node =>
    node.task.groups.any (fun owner =>
      (State.removeGroup.walk (state.queue.groupNodes.length + 1)
        state [root] [] targets).1.queue.groupNodes.any
        (fun group => group.group.node.ref == owner.ref))) = _
  rw [groups]
  rfl

end GraphQL.IncrementalDelivery.AlternativeWorkQueue
