import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedRemovalProjection
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskOwnerExistence
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupRootCoverage

/-! Cache-aware startup projects to the reference using actual live-task removal frames. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue
open WorkQueueSemantics (NodeRefs Occurrence)

/-- Live task ownership and complete membership links supply the literal removal frame. -/
theorem
    _root_.GraphQL.IncrementalDelivery.ReferenceWorkQueue.State.TaskOwnerFrame.removalTaskFrame
    {queue : ReferenceWorkQueue.State} {work : Work} (frame : queue.TaskOwnerFrame work)
    : RemovalTaskFrame queue := by
  refine ⟨frame.registered,
    fun _ member => frame.disposition.startedLinks frame.registered member, ?_⟩
  intro node member
  obtain ⟨key, contributes, present⟩ := frame.owners node member
  obtain ⟨owner, ownerMember, ownerKey⟩ := List.mem_map.mp contributes
  obtain ⟨group, groupMember, groupKey⟩ := List.mem_map.mp present
  exact List.any_eq_true.mpr ⟨owner, ownerMember,
    List.any_eq_true.mpr ⟨group, groupMember, beq_iff_eq.mpr (groupKey.trans ownerKey.symm)⟩⟩

private theorem cacheTaskFrame {queue : ReferenceWorkQueue.State} {work : Work}
    (frame : queue.TaskOwnerFrame work) (available : List (Occurrence × Nat))
    : (queue.cacheTaskFailures available).TaskOwnerFrame work :=
  ⟨
    frame.owners.cacheTaskFailures available,
    frame.disposition.cacheTaskFailures available,
    frame.keys.cacheTaskFailures available,
    frame.registered.cacheTaskFailures available,
    frame.matching.cacheTaskFailures available,
    frame.sound.cacheTaskFailures available
  ⟩

/-- Both startup paths return the same queue and aggregate notice when the live-task
and finite-forest invariants needed by literal fused removal hold at this actual state.
Cleanup targets remain the alternative transition's own inline observations.
-/
theorem State.startGroup_projects {state : State} {work : Work} {parents : Nat → NodeRefs}
    (frame : state.queue.TaskOwnerFrame work) (forest : state.queue.RemovalForest parents)
    (ref : Nat) (targets : List CleanupTarget)
    (available : List (Occurrence × Nat) := [])
    : (
        (state.startGroup ref targets available).1.queue,
        (state.startGroup ref targets available).2.2
      )
      = state.queue.startGroup ref available := by
  have cached := cacheTaskFrame frame available
  have cachedForest : (state.queue.cacheTaskFailures available).RemovalForest parents := by
    apply forest.of_subset
    rw [ReferenceWorkQueue.State.cacheTaskFailures_groupNodes]
    exact List.Subset.refl _
  unfold State.startGroup ReferenceWorkQueue.State.startGroup
  dsimp only
  cases found : (state.queue.cacheTaskFailures available).groupNode? ref with
  | none => rfl
  | some group =>
      dsimp only
      by_cases healthy : (group.tasks.filterMap (fun task =>
        ((state.queue.cacheTaskFailures available).taskNode? task).bind (·.rejection))).isEmpty
          = true
      · simp only [healthy, ite_true]
      · have same := FusedRemovalProjection_holds
          { state with queue := state.queue.cacheTaskFailures available } work parents
          group.group.node.ref targets cached.matching cached.sound cachedForest
          cached.removalTaskFrame
        simp only [healthy, Bool.false_eq_true, ite_false,
          State.finishGroupFailure, ReferenceWorkQueue.State.finishGroupFailure]
        rw [same]

private theorem startGroup_taskFrame {queue : ReferenceWorkQueue.State} {work : Work}
    (frame : queue.TaskOwnerFrame work) (ref : Nat) (available : List (Occurrence × Nat))
    : (queue.startGroup ref available).1.TaskOwnerFrame work :=
  ⟨
    frame.owners.startGroup frame.sound frame.registered frame.matching ref available,
    frame.disposition.startGroup ref available,
    List.Nodup.sublist ((queue.startGroup_groupNodes_sublist ref available).map _)
      frame.keys,
    frame.registered.startGroup ref available,
    frame.matching.startGroup ref available,
    frame.sound.startGroup ref available
  ⟩

/-- The actual startup fold retains exact reference state and queued notice order.
Every internal removal uses a live-task frame transported through the preceding real
startup; no desired endpoint equality or source-admission premise is assumed.
-/
theorem State.startGroups_projects {state : State} {work : Work}
    {parents : Nat → NodeRefs} (frame : state.queue.TaskOwnerFrame work)
    (forest : state.queue.RemovalForest parents) (groups : NodeRefs)
    (targets : List CleanupTarget) (failures : List ReferenceWorkQueue.GroupFailureEvent)
    (available : List (Occurrence × Nat) := [])
    : let alternative :=
        groups.foldl
          (fun (current, targets, failures) ref =>
            let (next, targets, queued) := current.startGroup ref targets available
            (next, targets, failures ++ queued))
          (state, targets, failures)
      let reference :=
        groups.foldl
          (fun (current, failures) ref =>
            let (next, queued) := current.startGroup ref available
            (next, failures ++ queued))
          (state.queue, failures)
      (alternative.1.queue, alternative.2.2) = reference := by
  induction groups generalizing state targets failures with
  | nil => rfl
  | cons ref rest ih =>
      have same := State.startGroup_projects frame forest ref targets available
      have queueEq := congrArg Prod.fst same
      have noticesEq := congrArg Prod.snd same
      dsimp only at queueEq noticesEq
      have nextFrame : (state.startGroup ref targets available).1.queue.TaskOwnerFrame work := by
        rw [queueEq]
        exact startGroup_taskFrame frame ref available
      have nextForest : (state.startGroup ref targets available).1.queue.RemovalForest parents := by
        rw [queueEq]
        exact forest.of_subset (state.queue.startGroup_groupNodes_sublist ref available).subset
      simpa only [List.foldl_cons, queueEq, noticesEq]
        using ih nextFrame nextForest (state.startGroup ref targets available).2.1
          (failures ++ (state.startGroup ref targets available).2.2)

end GraphQL.IncrementalDelivery.AlternativeWorkQueue
