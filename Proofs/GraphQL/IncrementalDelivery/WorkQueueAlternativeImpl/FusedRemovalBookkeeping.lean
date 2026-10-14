import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationTaskCompletion
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.MembershipSoundness
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RemovalCoverage

/-! Ownership bookkeeping for the literal last-owner task step of fused removal.
Structural task provenance and sound memberships are reused from the reference proofs;
they are internal transition premises, not new host-source assumptions.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue
open WorkQueueSemantics (Occurrence NodeRefs)
open ReferenceWorkQueue (Task GroupNode)

-----------------------------------------------------------------------------------------
-- Last-owner unlinking cannot mutate a surviving group's membership list
-----------------------------------------------------------------------------------------

/-- A structurally matched task with no live contributor cannot appear in a surviving
group's sound membership list. Failed-but-live contributors still count as live here.
-/
theorem ownerlessTask_membership_absent {queue : ReferenceWorkQueue.State} {work : Work}
    (matching : queue.RegisteredTasksMatch work) (sound : queue.GroupMembershipSound)
    {task : Task} (registered : task ∈ queue.tasks)
    (ownerless
      : task.groups.all (fun owner => (queue.groupNode? owner.ref).isNone) = true)
    {group : GroupNode} (member : group ∈ queue.groupNodes)
    : task.occurrence ∉ group.tasks := by
  intro linked
  obtain ⟨other, known, same, contributor⟩ := sound group member task.occurrence linked
  have identical := matchedTasks_eq_of_occurrence_eq (matching other known)
    (matching task registered) same
  subst other
  obtain ⟨owner, ownerMember, keyEq⟩ := List.mem_map.mp contributor
  have absent : queue.groupNode? owner.ref = none :=
    Option.isNone_iff_eq_none.mp (List.all_eq_true.mp ownerless owner ownerMember)
  have excluded := List.find?_eq_none.mp absent group member
  exact excluded (beq_iff_eq.mpr keyEq.symm)

/-- Last-owner removal changes only the task-node store. Soundness plus structural
matching makes the shared removeTask membership map the identity on remaining groups.
-/
theorem removeOwnerlessTask_eq {queue : ReferenceWorkQueue.State} {work : Work}
    (matching : queue.RegisteredTasksMatch work) (sound : queue.GroupMembershipSound)
    {task : Task} (registered : task ∈ queue.tasks)
    (ownerless
      : task.groups.all (fun owner => (queue.groupNode? owner.ref).isNone) = true)
    : queue.removeTask task.occurrence
      = {
        queue with
          taskNodes :=
            queue.taskNodes.filter (fun node => node.task.occurrence != task.occurrence)
      } := by
  have groups : (queue.removeTask task.occurrence).groupNodes = queue.groupNodes := by
    change queue.groupNodes.map _ = queue.groupNodes
    apply Eq.trans (b := queue.groupNodes.map id) ?_ (List.map_id _)
    apply List.map_congr_left
    intro group member
    have excluded := ownerlessTask_membership_absent matching sound registered ownerless member
    have unchanged : group.tasks.filter (· != task.occurrence) = group.tasks := by
      apply List.filter_eq_self.mpr
      intro occurrence present
      have different : (occurrence == task.occurrence) = false :=
        Bool.eq_false_iff.mpr (fun selected =>
          excluded ((ReferenceWorkQueue.occurrence_beq_iff_eq _ _).mp selected ▸ present))
      simp only [bne, different, Bool.not_false]
    rw [unchanged]
    rfl
  change queue.groupNodes.map _ = queue.groupNodes at groups
  unfold ReferenceWorkQueue.State.removeTask
  rw [groups]

-----------------------------------------------------------------------------------------
-- Proof notation for the public task fold and group filter
-----------------------------------------------------------------------------------------

/-- The exact task-step expression inside State.removeGroup.walk, named for induction. -/
def fusedRemovalTaskStep (acc : State × List CleanupTarget) (occurrence : Occurrence)
    : State × List CleanupTarget :=
  match acc.1.queue.task? occurrence with
  | none => acc
  | some task =>
      if task.groups.all (fun owner => (acc.1.queue.groupNode? owner.ref).isNone) then
        (
          { acc.1 with queue := acc.1.queue.removeTask occurrence },
          uniqueCleanupTargets (acc.2 ++ acc.1.cancelTask occurrence)
        )
      else
        acc

/-- The task fold erases no surviving group data, under the existing bookkeeping frame. -/
theorem fusedRemovalTaskStep_groupNodes {work : Work}
    (acc : State × List CleanupTarget)
    (matching : acc.1.queue.RegisteredTasksMatch work)
    (sound : acc.1.queue.GroupMembershipSound) (occurrence : Occurrence)
    : (fusedRemovalTaskStep acc occurrence).1.queue.groupNodes
      = acc.1.queue.groupNodes := by
  unfold fusedRemovalTaskStep
  split
  · rfl
  · rename_i task found
    have registered := List.mem_of_find?_eq_some found
    have same := (ReferenceWorkQueue.occurrence_beq_iff_eq _ _).mp
      (List.find?_some (p := fun candidate : Task => candidate.occurrence == occurrence) found)
    split
    · rename_i ownerless
      rw [← same, removeOwnerlessTask_eq matching sound registered ownerless]
    · rfl

/-- Last-owner task disposal retains every non-task-node field exactly. -/
theorem fusedRemovalTaskStep_registrationCore {work : Work}
    (acc : State × List CleanupTarget)
    (matching : acc.1.queue.RegisteredTasksMatch work)
    (sound : acc.1.queue.GroupMembershipSound) (occurrence : Occurrence)
    : registrationCore (fusedRemovalTaskStep acc occurrence).1.queue
      = registrationCore acc.1.queue := by
  unfold fusedRemovalTaskStep
  split
  · rfl
  · rename_i task found
    have registered := List.mem_of_find?_eq_some found
    have same := (ReferenceWorkQueue.occurrence_beq_iff_eq _ _).mp
      (List.find?_some (p := fun candidate : Task => candidate.occurrence == occurrence) found)
    split
    · rename_i ownerless
      rw [← same, removeOwnerlessTask_eq matching sound registered ownerless]
      rfl
    · rfl

/-- Permanent structural task provenance survives every literal task step. -/
theorem fusedRemovalTaskStep_registeredTasksMatch {work : Work}
    (acc : State × List CleanupTarget)
    (matching : acc.1.queue.RegisteredTasksMatch work) (occurrence : Occurrence)
    : (fusedRemovalTaskStep acc occurrence).1.queue.RegisteredTasksMatch work := by
  unfold fusedRemovalTaskStep
  split
  · exact matching
  · split
    · exact matching.removeTask occurrence
    · exact matching

/-- Sound surviving memberships are preserved even when a last-owner task is disposed. -/
theorem fusedRemovalTaskStep_groupMembershipSound (acc : State × List CleanupTarget)
    (sound : acc.1.queue.GroupMembershipSound) (occurrence : Occurrence)
    : (fusedRemovalTaskStep acc occurrence).1.queue.GroupMembershipSound := by
  unfold fusedRemovalTaskStep
  split
  · exact sound
  · split
    · exact sound.removeTask occurrence
    · exact sound

/-- Exact state-side group and active-root filter used before visiting its tasks. -/
def eraseRemovalGroup (state : State) (key : Nat) : State :=
  {
    state with
      queue :=
        {
          state.queue with
            groupNodes :=
              state.queue.groupNodes.filter (fun node => node.group.node.ref != key)
            rootGroups := state.queue.rootGroups.filter (· != key)
        }
  }

/-- Removing one group leaves permanent task provenance untouched. -/
theorem eraseRemovalGroup_registeredTasksMatch {state : State} {work : Work}
    (matching : state.queue.RegisteredTasksMatch work) (key : Nat)
    : (eraseRemovalGroup state key).queue.RegisteredTasksMatch work :=
  matching

/-- The shrinking group filter retains only previously sound membership lists. -/
theorem eraseRemovalGroup_groupMembershipSound {state : State}
    (sound : state.queue.GroupMembershipSound) (key : Nat)
    : (eraseRemovalGroup state key).queue.GroupMembershipSound :=
  fun group member occurrence linked =>
    sound group (List.mem_filter.mp member).1 occurrence linked

/-- Exact task-fold bookkeeping, not an observer trace or a reconstructed endpoint. -/
theorem fusedRemovalTaskFold_bookkeeping {work : Work} (tasks : List Occurrence)
    (acc : State × List CleanupTarget)
    (matching : acc.1.queue.RegisteredTasksMatch work)
    (sound : acc.1.queue.GroupMembershipSound)
    : let final := tasks.foldl fusedRemovalTaskStep acc
      final.1.queue.groupNodes = acc.1.queue.groupNodes
      ∧ final.1.queue.RegisteredTasksMatch work
      ∧ final.1.queue.GroupMembershipSound := by
  induction tasks generalizing acc with
  | nil => exact ⟨rfl, matching, sound⟩
  | cons occurrence rest ih =>
      have next := ih (fusedRemovalTaskStep acc occurrence)
        (fusedRemovalTaskStep_registeredTasksMatch acc matching occurrence)
        (fusedRemovalTaskStep_groupMembershipSound acc sound occurrence)
      exact ⟨next.1.trans (fusedRemovalTaskStep_groupNodes acc matching sound occurrence), next.2⟩

/-- The complete literal disposal fold has the identical accounting core. -/
theorem fusedRemovalTaskFold_registrationCore {work : Work} (tasks : List Occurrence)
    (acc : State × List CleanupTarget)
    (matching : acc.1.queue.RegisteredTasksMatch work)
    (sound : acc.1.queue.GroupMembershipSound)
    : registrationCore (tasks.foldl fusedRemovalTaskStep acc).1.queue
      = registrationCore acc.1.queue := by
  induction tasks generalizing acc with
  | nil => rfl
  | cons occurrence rest ih =>
      exact (ih (fusedRemovalTaskStep acc occurrence)
        (fusedRemovalTaskStep_registeredTasksMatch acc matching occurrence)
        (fusedRemovalTaskStep_groupMembershipSound acc sound occurrence)).trans
          (fusedRemovalTaskStep_registrationCore acc matching sound occurrence)

end GraphQL.IncrementalDelivery.AlternativeWorkQueue
