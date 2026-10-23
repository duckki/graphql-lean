import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.AvailableSourceStartup

/-! Source-record progress through actual mixed draining with supplied cache availability.
The record may change rejection slots while retaining its value and stream attachment.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open WorkQueueSemantics (Occurrence NodeRefs)

private theorem sourceRecord_drain_active_available {state : State} {work parents key}
    (running : state.stopped = false) (frame : state.queue.TaskOwnerFrame work)
    (forest : state.queue.RemovalForest parents) (fuel : Nat)
    (targets : List CleanupTarget) (available : List (Occurrence × Nat))
    (active : key ∈ state.queue.rootStreams)
    : RecordTargetRepresented
        (State.drainReadyGroups.go available fuel state targets).1.queue
        (.stream key) := by
  apply RecordTargetRepresented.activeStream
  rw [congrArg (fun result => result.1.rootStreams)
    (state.drainReadyGroups_go_projection running frame forest fuel targets available)]
  exact ReferenceWorkQueue.State.drainReadyGroups_go_streamRoots_cover fuel state.queue available
    (List.mem_append_left _ active)

/-- Cached draining retains a source record or its actual cumulative cleanup target.
It follows successful transfer, cached startup removal and later draining at the same cut.
-/
theorem sourceRecord_drain_go_available {state : State} {work parents}
    (running : state.stopped = false) (frame : state.queue.TaskOwnerFrame work)
    (forest : state.queue.RemovalForest parents)
    (inventory : state.queue.ChildStreamInventory) (keys : state.queue.TaskNodeKeysUnique)
    (available : List (Occurrence × Nat)) (fuel : Nat) (targets : List CleanupTarget)
    (unique : targets.Nodup) {key}
    (represented : RecordTargetRepresented state.queue (.stream key))
    : let reduced := State.drainReadyGroups.go available fuel state targets
      RecordTargetRepresented reduced.1.queue (.stream key)
      ∨ .stream key ∈ reduced.2.2.1 := by
  induction fuel generalizing state targets with
  | zero => exact .inl represented
  | succ fuel ih =>
      cases represented with
      | activeStream active =>
          exact .inl (sourceRecord_drain_active_available running frame forest (fuel + 1)
            targets available active)
      | @bufferedStream occurrence node _ found stored held =>
          rw [State.drainReadyGroups_go_eq fuel state targets available]
          cases selected : fusedReadyGroup state.queue with
          | none => exact .inl (.bufferedStream found stored held)
          | some group =>
              dsimp only
              let released := state.queue.finishGroupSuccess group
              let started := ({ state with queue := released.1 }).startNewWork released.2.2
                {} targets available
              have releasedFrame := frame.finishGroupSuccess group (fusedReadyGroup_member selected)
              have releasedForest := forest.finishGroupSuccess group
              have releasedKeys := keys.finishGroupSuccess group
              have same : started.1.queue = (released.1.startNewWork released.2.2 available).1 := by
                simpa only [List.foldl_nil]
                  using State.startNewWork_queue { state with queue := released.1 }
                    released.2.2 {} targets running available releasedFrame releasedForest
              have nextFrame : started.1.queue.TaskOwnerFrame work := by
                rw [same]; exact releasedFrame.startNewWork _ available
              have nextForest : started.1.queue.RemovalForest parents := by
                rw [same]; exact releasedForest.startNewWork _ available
              have nextInventory : started.1.queue.ChildStreamInventory := by
                rw [same]; exact (inventory.finishGroupSuccess group).startNewWork _ available
              have nextKeys : started.1.queue.TaskNodeKeysUnique := by
                rw [same]; exact releasedKeys.startNewWork _ available
              have nextRunning := (State.startNewWork_stopped
                { state with queue := released.1 } released.2.2 {} targets available).trans running
              have nextUnique := State.startNewWork_targets_nodup
                { state with queue := released.1 } released.2.2 {} targets unique available
              by_cases listed : occurrence ∈ group.tasks
              · have transferred : key ∈ started.1.queue.rootStreams := by
                  rw [same]
                  have releasedKey :=
                    inventory.finishGroupSuccess_childRef_covered group listed found held
                  have noticed := state.queue.finishGroupSuccess_streamNotices group ▸ releasedKey
                  exact state.queue.finishGroupSuccess_streamRoots_cover group available
                    (List.mem_append_right _ noticed)
                exact .inl (sourceRecord_drain_active_available nextRunning nextFrame nextForest
                  fuel started.2.1 available transferred)
              · have retained : released.1.taskNode? occurrence = some node :=
                  (state.queue.finishGroupSuccess_lookup_unselected group listed).trans found
                rcases sourceRecord_startNewWork_available { state with queue := released.1 }
                    releasedKeys released.2.2 {} targets available
                    (.bufferedStream retained stored held) with kept | requested
                · exact ih nextRunning nextFrame nextForest nextInventory nextKeys
                    started.2.1 nextUnique kept
                · exact .inr ((State.drainReadyGroups_go_targets fuel started.1 started.2.1
                    nextUnique available).2.sublist.subset requested)

/-- The actual bounded drain supplies the same source record or inline cleanup target. -/
theorem sourceRecord_drainReadyGroups_available {state : State} {work parents}
    (running : state.stopped = false) (frame : state.queue.TaskOwnerFrame work)
    (forest : state.queue.RemovalForest parents)
    (inventory : state.queue.ChildStreamInventory) (keys : state.queue.TaskNodeKeysUnique)
    (targets : List CleanupTarget) (unique : targets.Nodup)
    (available : List (Occurrence × Nat)) {key}
    (represented : RecordTargetRepresented state.queue (.stream key))
    : let reduced := state.drainReadyGroups targets available
      RecordTargetRepresented reduced.1.queue (.stream key)
      ∨ .stream key ∈ reduced.2.2.1 :=
  sourceRecord_drain_go_available running frame forest inventory keys available _ targets
    unique represented

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
