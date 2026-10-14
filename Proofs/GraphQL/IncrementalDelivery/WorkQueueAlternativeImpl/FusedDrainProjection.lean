import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.GeneratedFusedRemoval
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedRemovalGuards
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationRelease
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.DrainRootCoverage

/-! Exact reference projection of actual mixed draining, with the cleanup prefix carried
by the real reductions. Failure and successful release share one compatible queue frame.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue
open WorkQueueSemantics (NodeRefs)

def fusedReadyGroup (queue : ReferenceWorkQueue.State)
    : Option ReferenceWorkQueue.GroupNode :=
  queue.rootGroups.findSome?
    fun key => do
      let node ← queue.groupNode? key
      if node.failure.isSome || node.pending == 0 then some node else none

theorem fusedReadyGroup_member {queue : ReferenceWorkQueue.State}
    {group : ReferenceWorkQueue.GroupNode} (selected : fusedReadyGroup queue = some group)
    : group ∈ queue.groupNodes := by
  obtain ⟨key, _, choice⟩ := List.exists_of_findSome?_eq_some selected
  cases found : queue.groupNode? key with
  | none => simp [found] at choice
  | some node =>
      rw [found] at choice
      change (if node.failure.isSome || node.pending == 0 then some node else none) = some group
        at choice
      split at choice
      · have same := Option.some.inj choice
        exact same ▸ List.mem_of_find?_eq_some found
      · cases choice

theorem State.drainReadyGroups_go_eq (fuel : Nat) (state : State)
    (targets : List CleanupTarget)
    : State.drainReadyGroups.go (fuel + 1) state targets
      = match fusedReadyGroup state.queue with
        | none => (state, [], targets)
        | some node =>
            let next :=
              match node.failure with
              | some errors =>
                  let reduced := state.finishGroupFailure node errors targets
                  (reduced.1, [reduced.2.1], reduced.2.2)
              | none =>
                  let released := state.queue.finishGroupSuccess node
                  let started :=
                    ({ state with queue := released.1 }).startNewWork released.2.2 {}
                      targets
                  (started.1, released.2.1, started.2)
            let later := State.drainReadyGroups.go fuel next.1 next.2.2
            (later.1, next.2.1 ++ later.2.1, later.2.2) :=
  rfl

private theorem reference_go_eq (fuel : Nat) (queue : ReferenceWorkQueue.State)
    : ReferenceWorkQueue.State.drainReadyGroups.go (fuel + 1) queue
      = match fusedReadyGroup queue with
        | none => (queue, [])
        | some node =>
            let next :=
              match node.failure with
              | some errors =>
                  let reduced := queue.finishGroupFailure node errors
                  (reduced.1, [reduced.2])
              | none =>
                  let released := queue.finishGroupSuccess node
                  (released.1.startNewWork released.2.2, released.2.1)
            let later := ReferenceWorkQueue.State.drainReadyGroups.go fuel next.1
            (later.1, next.2 ++ later.2) :=
  rfl

/-- Each actual bounded drain prefix has the identical reference queue and wire events.
Cleanup identity order is not equated to an old output scan; it comes from the new real
walk and remains available independently in the third returned component.
-/
theorem State.drainReadyGroups_go_projection {state : State} {work : Work}
    {parents : Nat → NodeRefs} (running : state.stopped = false)
    (frame : state.queue.TaskOwnerFrame work) (forest : state.queue.RemovalForest parents)
    (fuel : Nat) (targets : List CleanupTarget)
    : let actual := State.drainReadyGroups.go fuel state targets
      (actual.1.queue, actual.2.1)
      = ReferenceWorkQueue.State.drainReadyGroups.go fuel state.queue := by
  induction fuel generalizing state targets with
  | zero => rfl
  | succ fuel ih =>
      rw [State.drainReadyGroups_go_eq, reference_go_eq]
      cases selected : fusedReadyGroup state.queue with
      | none => rfl
      | some node =>
          simp only
          cases cached : node.failure with
          | some errors =>
              simp only
              let removed := state.removeGroup node.group.node.ref targets
              have same : removed.1.queue = state.queue.removeGroup node.group.node.ref :=
                FusedRemovalProjection_holds state work parents node.group.node.ref targets
                  frame.matching frame.sound forest frame.removalTaskFrame
              have nextFrame : removed.1.queue.TaskOwnerFrame work := by
                rw [same]
                exact frame.removeGroup node.group.node.ref
              have nextForest : removed.1.queue.RemovalForest parents := by
                rw [same]
                exact forest.removeGroup node.group.node.ref
              have next := ih ((state.removeGroup_stopped node.group.node.ref targets).trans running)
                nextFrame nextForest removed.2
              rw [same] at next
              change ((State.drainReadyGroups.go fuel removed.1 removed.2).1.queue,
                [.groupFailure node.group.node errors] ++
                  (State.drainReadyGroups.go fuel removed.1 removed.2).2.1) = _
              exact congrArg
                (fun pair => (pair.1, [.groupFailure node.group.node errors] ++ pair.2))
                next
          | none =>
              simp only
              let released := state.queue.finishGroupSuccess node
              let started := ({ state with queue := released.1 }).startNewWork released.2.2 {} targets
              have same : started.1.queue = released.1.startNewWork released.2.2 := by
                simpa only [List.foldl_nil]
                  using State.startNewWork_queue
                    { state with queue := released.1 } released.2.2 {} targets running
              have nextFrame : started.1.queue.TaskOwnerFrame work := by
                rw [same]
                exact (frame.finishGroupSuccess node (fusedReadyGroup_member selected)).startNewWork _
              have nextForest : started.1.queue.RemovalForest parents := by
                rw [same]
                exact (forest.finishGroupSuccess node).startNewWork _
              have next := ih ((State.startNewWork_stopped
                  { state with queue := released.1 } released.2.2 {} targets).trans running)
                nextFrame nextForest started.2
              rw [same] at next
              change ((State.drainReadyGroups.go fuel started.1 started.2).1.queue,
                released.2.1 ++ (State.drainReadyGroups.go fuel started.1 started.2).2.1) = _
              exact congrArg (fun pair => (pair.1, released.2.1 ++ pair.2)) next

theorem State.drainReadyGroups_projection {state : State} {work : Work}
    {parents : Nat → NodeRefs} (running : state.stopped = false)
    (frame : state.queue.TaskOwnerFrame work) (forest : state.queue.RemovalForest parents)
    (targets : List CleanupTarget)
    : ((state.drainReadyGroups targets).1.queue, (state.drainReadyGroups targets).2.1)
      = state.queue.drainReadyGroups :=
  state.drainReadyGroups_go_projection running frame forest _ targets

/-- Exact local mixed-drain target with a compatible owner/forest frame. -/
def FusedDrainProjection : Prop :=
  ∀ (state : State) (work : Work) (parents : Nat → NodeRefs)
    (targets : List CleanupTarget),
    state.stopped = false
    → state.queue.TaskOwnerFrame work
    → state.queue.RemovalForest parents
    → ((state.drainReadyGroups targets).1.queue, (state.drainReadyGroups targets).2.1)
      = state.queue.drainReadyGroups

theorem FusedDrainProjection_holds : FusedDrainProjection := by
  intro state work parents targets running frame forest
  exact state.drainReadyGroups_projection running frame forest targets

/-- Original generated-prefix target; the compatible frame is constructed, not assumed.
RegistrationNormalizedReplay composes this local bridge through complete normalized replay.
-/
def GeneratedReferenceDrainProjection : Prop :=
  ∀ (work : Work) (batches : List (List GraphEvent)),
    ReferenceWorkQueue.ExecutedWork work
    → ReferenceWorkQueue.ValidGraphEvents work batches.flatten
    → ReferenceWorkQueue.inputsStarted work batches = true
    → ∀ targets : List CleanupTarget,
        let queue :=
          ((ReferenceWorkQueue.State.initialize
              (ReferenceWorkQueue.Work.fromExecution work)).runNormalized
            batches).1
        let actual := ({ queue } : State).drainReadyGroups targets
        (actual.1.queue, actual.2.1) = queue.drainReadyGroups

theorem GeneratedReferenceDrainProjection_holds : GeneratedReferenceDrainProjection := by
  intro work batches generated valid started targets
  obtain ⟨parents, forest⟩ := generated.runNormalized_removalForest batches valid
  exact FusedDrainProjection_holds _ work parents targets rfl
    (generated.runNormalized_taskOwnerFrame batches valid started) forest

end GraphQL.IncrementalDelivery.AlternativeWorkQueue
