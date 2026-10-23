import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ResourceCompletion
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ChildStreamInventoryReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ChildStreamReleaseCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamCompletionReplay

/-! Successful task removal transfers held sources to active stream roots, not disposal.
Reuse the reference release/activation kernel and connect its roots to alternative stop.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open GraphQL.IncrementalDelivery.ReferenceWorkQueue (
  GroupNode TaskNode rawStreamNoticeRefs)

-----------------------------------------------------------------------------------------
-- Released sources remain reachable independently of their removed producer record
-----------------------------------------------------------------------------------------

/-- Every active source is a concrete target of the alternative stop traversal. -/
theorem State.rootStream_cleanupTarget (queue : State) {key : Nat}
    (active : key ∈ queue.queue.rootStreams)
    : .stream key ∈ queue.cleanupTargets := by
  apply (mem_uniqueCleanupTargets _ _).mpr
  exact List.mem_append_right _ (List.mem_map.mpr ⟨key, active, rfl⟩)

/-- Successful closure and activation preserve each selected task's held source as a root.
Registration inventory supplies the real source descriptor; the existing flush witness
releases it and activation covers that exact release list. No resource is acquired here.
-/
theorem successfulFlush_heldSource {queue : ReferenceWorkQueue.State}
    (inventory : queue.ChildStreamInventory) (group : GroupNode) {occurrence node key}
    (selected : occurrence ∈ group.tasks) (found : queue.taskNode? occurrence = some node)
    (held : key ∈ node.childStreams)
    : let closed := queue.finishGroupSuccess group
      key ∈ closed.2.2.newStreams.map Execution.DeliveryNode.ref
      ∧ key ∈ (closed.1.startNewWork closed.2.2).1.rootStreams
      ∧ .stream key
        ∈ ({ queue := (closed.1.startNewWork closed.2.2).1 } : State).cleanupTargets := by
  have released := inventory.finishGroupSuccess_childRef_covered group selected found held
  have notice := queue.finishGroupSuccess_streamNotices group ▸ released
  have active := queue.finishGroupSuccess_streamRoots_cover group []
    (List.mem_append_right _ notice)
  exact ⟨released, active, State.rootStream_cleanupTarget _ active⟩

/-- Generated alternative replay retains the reference's permanent child-source inventory. -/
theorem generatedReplay_childStreamInventory (work : Work)
    (inputs : List (List GraphEvent))
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (valid : ReferenceWorkQueue.ValidGraphEvents work inputs.flatten)
    (started : ReferenceWorkQueue.inputsStarted work inputs = true)
    : ((State.initialize work).runNormalized inputs).1.queue.ChildStreamInventory := by
  rw [State.runNormalized_initialize work inputs generated valid started]
  simp only [State.fromReference]
  split
  · intro node impossible; cases impossible
  · exact ReferenceWorkQueue.createWorkQueue_runNormalized_childStreamInventory _ _

/-- Generated flush boundaries transfer every selected held source into stop reachability.
The inventory is derived, not assumed. This names the local release/activation boundary;
complete native ownership and release-time failure disposal remain different obligations.
-/
def GeneratedFlushStreamCoverage : Prop :=
  ∀ work inputs,
    ReferenceWorkQueue.ExecutedWork work
    → ReferenceWorkQueue.ValidGraphEvents work inputs.flatten
    → ReferenceWorkQueue.inputsStarted work inputs = true
    → ∀ (group : GroupNode) (occurrence : WorkQueueSemantics.Occurrence) (node : TaskNode)
        (key : Nat),
        let queue := ((State.initialize work).runNormalized inputs).1.queue
        queue.groupNode? group.group.node.ref = some group
        → occurrence ∈ group.tasks
        → queue.taskNode? occurrence = some node
        → key ∈ node.childStreams
        → let closed := queue.finishGroupSuccess group
          key ∈ closed.2.2.newStreams.map Execution.DeliveryNode.ref
          ∧ key ∈ (closed.1.startNewWork closed.2.2).1.rootStreams
          ∧ .stream key
            ∈ ({ queue := (closed.1.startNewWork closed.2.2).1 } : State).cleanupTargets

/-- Reuse concrete reference release coverage on the actual projected replay inventory. -/
theorem GeneratedFlushStreamCoverage_holds : GeneratedFlushStreamCoverage := by
  intro work inputs generated valid started group occurrence node key
  dsimp only
  intro live selected found held
  exact successfulFlush_heldSource (generatedReplay_childStreamInventory work inputs
    generated valid started) group selected found held

-----------------------------------------------------------------------------------------
-- Actual single-event dispatch covers newly announced sources at the stop boundary
-----------------------------------------------------------------------------------------

/-- A stream notice from any one handler is active after that handler.
Success/item handlers activate releases; failure and source-finalization inputs produce
no new stream notices. Earlier accumulated batch notices are intentionally not used.
-/
theorem graphEvent_newStream_active (queue : ReferenceWorkQueue.State)
    (event : GraphEvent) {key : Nat}
    (noticed : key ∈ (queue.handleGraphEvent event).2.1.flatMap rawStreamNoticeRefs)
    : key ∈ (queue.handleGraphEvent event).1.rootStreams := by
  cases event with
  | taskSuccess occurrence result =>
      exact queue.taskSuccess_streamRoots_cover occurrence result []
        (List.mem_append_right _ noticed)
  | streamItems stream items =>
      exact queue.streamItems_streamRoots_cover stream items [] (List.mem_append_right _ noticed)
  | taskFailure occurrence errors =>
      simp only [ReferenceWorkQueue.State.handleGraphEvent,
        ReferenceWorkQueue.State.cacheTaskFailures, List.foldl_nil] at noticed
      rw [queue.taskFailure_streamNoticeRefs] at noticed
      cases noticed
  | streamSuccess stream =>
      simp only [ReferenceWorkQueue.State.handleGraphEvent, ReferenceWorkQueue.State.streamSuccess,
        ReferenceWorkQueue.State.cacheTaskFailures,
        List.foldl_nil] at noticed
      cases active : queue.rootStreams.contains stream.ref <;>
        simp only [active, Bool.false_eq_true, ↓reduceIte, List.flatMap_nil,
          List.flatMap_cons, rawStreamNoticeRefs, List.append_nil] at noticed <;> cases noticed
  | streamFailure stream errors =>
      simp only [ReferenceWorkQueue.State.handleGraphEvent, ReferenceWorkQueue.State.streamFailure,
        ReferenceWorkQueue.State.cacheTaskFailures,
        List.foldl_nil] at noticed
      cases active : queue.rootStreams.contains stream.ref <;>
        simp only [active, Bool.false_eq_true, ↓reduceIte, List.flatMap_nil,
          List.flatMap_cons, rawStreamNoticeRefs, List.append_nil] at noticed <;> cases noticed
  | groupFailure notice =>
      simp only [ReferenceWorkQueue.State.handleGraphEvent, ReferenceWorkQueue.State.groupFailure,
        ReferenceWorkQueue.State.cacheTaskFailures, List.foldl_nil] at noticed
      split at noticed
      · cases noticed
      · split at noticed <;> simp_all [rawStreamNoticeRefs]

/-- Dispatch's actual newly announced source is reachable by the alternative stop walk. -/
theorem GraphBatchResult.releasedStream_cleanupTarget (result : GraphBatchResult)
    (event : GraphEvent) {key : Nat}
    (projection
      : (
          (result.state.handleGraphEvent event).1.queue,
          (result.state.handleGraphEvent event).2.1,
          (result.state.handleGraphEvent event).2.2.2
        )
        = result.state.queue.handleGraphEvent event)
    (noticed
      : key ∈ (result.state.queue.handleGraphEvent event).2.1.flatMap rawStreamNoticeRefs)
    : .stream key ∈ (result.handleGraphEvent event).state.cleanupTargets := by
  apply State.rootStream_cleanupTarget
  change key ∈ (result.state.handleGraphEvent event).1.queue.rootStreams
  rw [congrArg (fun pair => pair.1.rootStreams) projection]
  exact graphEvent_newStream_active _ _ noticed

/-- An immediate stop requests cleanup for that released source, despite task-node removal. -/
theorem GraphBatchResult.releasedStream_stopRequest (result : GraphBatchResult)
    (event : GraphEvent) (running : result.state.stopped = false) {key : Nat}
    (projection
      : (
          (result.state.handleGraphEvent event).1.queue,
          (result.state.handleGraphEvent event).2.1,
          (result.state.handleGraphEvent event).2.2.2
        )
        = result.state.queue.handleGraphEvent event)
    (noticed
      : key ∈ (result.state.queue.handleGraphEvent event).2.1.flatMap rawStreamNoticeRefs)
    : .cancelSource key ∈ (result.handleGraphEvent event).state.cancel.2 := by
  have covered := GraphBatchResult.releasedStream_cleanupTarget result event projection noticed
  rw [State.cancel_effects]
  change HostEffect.cancelSource key
    ∈ if (result.state.handleGraphEvent event).1.stopped then [] else _
  rw [State.handleGraphEvent_stopped]
  simp only [running, Bool.false_eq_true, ↓reduceIte]
  exact List.mem_flatMap.mpr ⟨.stream key, covered, List.mem_cons_self⟩

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
