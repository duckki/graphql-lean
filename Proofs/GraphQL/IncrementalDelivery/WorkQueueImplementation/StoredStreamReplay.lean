import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StoredStreamCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ChildStreamReleaseCoverage

/-! Replay retains complete child-stream links until the producer leaves the task map. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Release and activation retain links or remove the whole producer node
-----------------------------------------------------------------------------------------

private theorem fold_preserves {α β : Type} (property : α → Prop) (step : α → β → α)
    (preserved : ∀ current item, property current → property (step current item))
    (items : List β) (current : α) (prior : property current)
    : property (items.foldl step current) := by
  induction items generalizing current with
  | nil => exact prior
  | cons item rest ih => exact ih _ (preserved current item prior)

/-- Empty-group pruning changes no buffered producer or child-stream link.
Witness: the exact task-map projection of the bounded pruning traversal.
-/
theorem State.StoredStreamsComplete.pruneEmptyGroups {queue : State} {work}
    (complete : queue.StoredStreamsComplete work) (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.StoredStreamsComplete work := by
  intro node member
  rw [State.pruneEmptyGroups_taskNodes] at member
  exact complete node member

/-- Rejection exposure preserves the producer, buffered value and child-stream slots. -/
theorem State.StoredStreamsComplete.cacheTaskFailures {queue : State} {work}
    (complete : queue.StoredStreamsComplete work) (available : List (Occurrence × Nat))
    : (queue.cacheTaskFailures available).StoredStreamsComplete work := by
  induction available generalizing queue with
  | nil => exact complete
  | cons entry rest ih =>
      simp only [State.cacheTaskFailures, List.foldl_cons]
      split
      · exact ih complete
      · rename_i node found
        exact ih (complete.putTaskNode { node with rejection := some entry.2 }
          (complete node (List.mem_of_find?_eq_some found)))

/-- Starting a task retains earlier links and creates only an unresolved node.
Witness: the start guard either does nothing or appends a node with no stored value.
-/
theorem State.StoredStreamsComplete.startTask {queue : State} {work}
    (complete : queue.StoredStreamsComplete work) (occurrence : Occurrence)
    (available : List (Occurrence × Nat) := [])
    : (queue.startTask occurrence available).StoredStreamsComplete work := by
  unfold State.startTask
  split
  · exact complete
  · split
    · exact complete
    · intro node member stored
      rcases List.mem_append.mp member with old | new
      · exact complete node old stored
      · have same := List.mem_singleton.mp new
        subst node; cases stored

/-- Group startup retains child links or removes the entire rejected producer record. -/
theorem State.StoredStreamsComplete.startGroup {queue : State} {work}
    (complete : queue.StoredStreamsComplete work) (ref : NodeRef)
    (available : List (Occurrence × Nat) := [])
    : (queue.startGroup ref available).1.StoredStreamsComplete work := by
  have cached := complete.cacheTaskFailures available
  unfold State.startGroup
  dsimp only
  split
  · exact cached
  · split
    · exact fold_preserves (fun (current : State) => current.StoredStreamsComplete work)
        (fun current task => current.startTask task available)
        (fun _ occurrence prior => prior.startTask occurrence available) _ _ cached
    · exact fun node member => cached node (List.mem_filter.mp member).1

/-- Released group/source startup preserves every retained buffered producer's links. -/
theorem State.StoredStreamsComplete.startNewWork {queue : State} {work}
    (complete : queue.StoredStreamsComplete work) (released : NewWork)
    (available : List (Occurrence × Nat) := [])
    : (queue.startNewWork released available).1.StoredStreamsComplete work := by
  let refs := released.newGroups.map Execution.DeliveryNode.ref
  have groups := fold_preserves
    (fun (acc : State × List GroupFailureEvent) => acc.1.StoredStreamsComplete work)
    (fun (current, failures) ref =>
      let (next, queued) := current.startGroup ref available
      (next, failures ++ queued))
    (fun acc ref prior => prior.startGroup ref available) refs
    ({ queue with rootGroups := queue.rootGroups ++ refs }, []) complete
  unfold State.startNewWork
  apply fold_preserves (fun current => current.StoredStreamsComplete work)
    State.startStream _ _ _ groups
  intro current ref prior
  unfold State.startStream
  split <;> exact prior

/-- Failed-group removal leaves retained producer nodes unchanged.
Witness: each surviving task node is an entry of the original filtered map.
-/
theorem State.StoredStreamsComplete.removeGroup {queue : State} {work}
    (complete : queue.StoredStreamsComplete work) (ref : NodeRef)
    : (queue.removeGroup ref).StoredStreamsComplete work :=
  fun node member => complete node (List.mem_filter.mp member).1

/-- A successful flush leaves all residual buffered links complete.
Witness: the exact selection only removes task nodes; subsequent pruning changes no others.
-/
theorem State.StoredStreamsComplete.finishGroupSuccess {queue : State} {work}
    (complete : queue.StoredStreamsComplete work) (group : GroupNode)
    : (queue.finishGroupSuccess group).1.StoredStreamsComplete work := by
  obtain ⟨_, _, _, _, retained, _⟩ := queue.finishGroupSuccess_publications group
  exact fun node member => complete node (retained member)

/-- Task failure cannot silently strip links from a retained buffered producer.
Witness: cache updates leave task nodes unchanged, and failure cleanup only removes nodes.
-/
theorem State.StoredStreamsComplete.taskFailure {queue : State} {work}
    (complete : queue.StoredStreamsComplete work) (occurrence : Occurrence) (errors : Nat)
    : (queue.taskFailure occurrence errors).1.StoredStreamsComplete work := by
  cases found : queue.taskNode? occurrence with
  | none => simpa only [State.taskFailure, found] using complete
  | some node =>
      rw [queue.taskFailure_eq occurrence errors node found]
      apply failureGroupFold_preserves (fun current => current.StoredStreamsComplete work)
        (fun current ref prior => prior.removeGroup ref)
      exact complete.putTaskNode _ (complete node (List.mem_of_find?_eq_some found))

/-- Successful draining and cached child startup retain complete surviving producers. -/
theorem State.StoredStreamsComplete.drainReadyGroups {queue : State} {work}
    (complete : queue.StoredStreamsComplete work)
    (available : List (Occurrence × Nat) := [])
    : (queue.drainReadyGroups available).1.StoredStreamsComplete work := by
  apply State.drainReadyGroups_preserves (fun current => current.StoredStreamsComplete work)
    (available := available) (valid := complete)
  intro current node prior _ _ _
  exact (prior.finishGroupSuccess node).startNewWork _ available

-----------------------------------------------------------------------------------------
-- The actual single-pass handlers preserve the complete boundary invariant
-----------------------------------------------------------------------------------------

/-- Object success preserves complete child links through integration, owner flushes, and drain.
Witness: fresh matched integration discharges the temporary exception before any flush;
the original contributor loop then preserves all residual links. Ignored successes add none.
-/
theorem State.StoredStreamsComplete.taskSuccess {queue : State} {work occurrence result}
    (complete : queue.StoredStreamsComplete work)
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (fresh : ∀ stream ∈ result.work.streams, queue.stream? stream.node.ref = none)
    (available : List (Occurrence × Nat) := [])
    : (queue.taskSuccess occurrence result available).1.StoredStreamsComplete work := by
  cases found : queue.taskNode? occurrence with
  | none => simpa only [State.taskSuccess, found] using complete
  | some node =>
      have integrated := complete.integrateSuccess found matching fresh
      have step (acc : State × List WorkQueueEvent × NewWork) (group : Execution.DeliveryNode)
          (prior : acc.1.StoredStreamsComplete work)
          : (successGroupStep acc group).1.StoredStreamsComplete work := by
        obtain ⟨current, events, released⟩ := acc
        dsimp only [successGroupStep]
        split
        · exact prior
        · split
          · exact (prior.putGroupNode _).finishGroupSuccess _
          · exact prior
      have processed := fold_preserves (fun acc => acc.1.StoredStreamsComplete work)
        successGroupStep step node.task.groups (_, [], {}) integrated
      rw [queue.taskSuccess_eq occurrence result node found available]
      exact (processed.startNewWork _ available).drainReadyGroups available

/-- Stream item integration preserves all existing buffered object links.
Witness: each item registers root work without installing an object value, then the final
drain removes or retains complete producer nodes in its actual execution order.
-/
theorem State.StoredStreamsComplete.streamItems {queue : State} {work}
    (complete : queue.StoredStreamsComplete work) (stream : Execution.DeliveryNode)
    (items : List StreamItem) (available : List (Occurrence × Nat) := [])
    : (queue.streamItems stream items available).1.StoredStreamsComplete work := by
  have folded := fold_preserves
    (fun (acc : State × List Execution.DeliveryNode × List Execution.DeliveryNode
      × List StreamItemValue × List GroupFailureEvent) => acc.1.StoredStreamsComplete work)
    (fun acc item => streamItemStep acc item available)
    (fun acc item prior =>
      ((prior.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _ available)
    items (queue, [], [], [], []) complete
  rw [queue.streamItems_eq stream items available]
  split
  · exact complete
  · exact folded.drainReadyGroups available

-----------------------------------------------------------------------------------------
-- Generated replay supplies freshness without strengthening the public source laws
-----------------------------------------------------------------------------------------

/-- Initial task nodes contain no buffered values requiring child-stream attachment.
Witness: root integration, pruning, and activation preserve vacuous empty-map coverage.
-/
theorem createWorkQueue_storedStreamsComplete (work : Execution.Work)
    : (State.initialize (Work.fromExecution work)).StoredStreamsComplete work := by
  have empty : ({} : State).StoredStreamsComplete work := by
    intro node impossible; cases impossible
  exact ((empty.maybeIntegrateWork (Work.fromExecution work)).pruneEmptyGroups
          _).startNewWork
    _

/-- Every buffered value throughout valid generated replay retains all its child streams.
Witness: source freshness and generated producer uniqueness supply fresh registration;
the actual handlers preserve complete attachment. No output admission or start premise
is assumed, and no temporary exception remains at a replay boundary.
-/
theorem ExecutedWork.replayGraphEvents_storedStreamsComplete {work events}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work events)
    (available : List (Occurrence × Nat) := [])
    : ((State.initialize (Work.fromExecution work)).replayGraphEvents
        events available).StoredStreamsComplete
        work := by
  induction valid with
  | nil => exact createWorkQueue_storedStreamsComplete work
  | @append before event valid matching fresh ready ih =>
      rw [State.replayGraphEvents_append _ before [event] available]
      let current := (State.initialize (Work.fromExecution work)).replayGraphEvents before available
      have cached := ih.cacheTaskFailures available
      change (current.handleGraphEvent event available).1.StoredStreamsComplete work
      cases event with
      | taskSuccess occurrence result =>
          apply cached.taskSuccess matching (available := available)
          intro stream member
          have absent := generated.replayGraphEvents_taskChildStream_absent valid matching
            fresh member available
          have streams := congrArg State.streams (current.cacheTaskFailures_frame available)
          dsimp only at streams
          change (current.cacheTaskFailures available).stream? stream.node.ref = none
          change current.stream? stream.node.ref = none at absent
          simpa only [State.stream?, streams] using absent
      | taskFailure occurrence errors => exact cached.taskFailure occurrence errors
      | streamItems stream items => exact cached.streamItems stream items available
      | streamSuccess stream =>
          change State.StoredStreamsComplete
            ((current.cacheTaskFailures available).streamSuccess stream).1 work
          unfold State.streamSuccess
          split <;> exact cached
      | streamFailure stream errors =>
          change State.StoredStreamsComplete
            ((current.cacheTaskFailures available).streamFailure stream errors).1 work
          unfold State.streamFailure
          split <;> exact cached

      | groupFailure failure =>
          simp only [State.handleGraphEvent, State.groupFailure]
          split
          · exact cached
          · split <;> exact cached

private structure StoredStreamFrame (queue : State) (work : Execution.Work)
    (before : List GraphEvent)
    : Prop where
  complete : queue.StoredStreamsComplete work
  origins
    : queue.StreamsSatisfy
        (StreamProducerSeen work (before.flatMap (fun event => event.identities.1)))

private theorem StoredStreamFrame.weakenHistory {queue work before after}
    (frame : StoredStreamFrame queue work before) (included : before.Subset after)
    : StoredStreamFrame queue work after :=
  ⟨
    frame.complete,
    fun stream member => (frame.origins stream member).mono (by
      intro occurrence received
      obtain ⟨event, old, emitted⟩ := List.mem_flatMap.mp received
      exact List.mem_flatMap.mpr ⟨event, included old, emitted⟩)
  ⟩

private theorem StoredStreamFrame.handleGraphEvent {queue work before}
    (frame : StoredStreamFrame queue work before) (generated : ExecutedWork work)
    (event : GraphEvent) (matching : event.MatchesWork work) (fresh : event.Fresh before)
    (available : List (Occurrence × Nat))
    : StoredStreamFrame (queue.handleGraphEvent event available).1 work
        (before ++ [event]) := by
  have cached := frame.complete.cacheTaskFailures available
  have origins := frame.origins.cacheTaskFailures available
  have complete : (queue.handleGraphEvent event available).1.StoredStreamsComplete work := by
    cases event with
    | taskSuccess occurrence result =>
        apply cached.taskSuccess matching (available := available)
        intro stream member
        obtain ⟨dependencies, known⟩ := matching.childStream_producer member
        exact origins.freshProducer_streamAbsent generated known
          (fresh.2.2.1 occurrence List.mem_cons_self)
    | taskFailure occurrence errors => exact cached.taskFailure occurrence errors
    | streamItems stream items => exact cached.streamItems stream items available
    | streamSuccess stream =>
        change State.StoredStreamsComplete
          ((queue.cacheTaskFailures available).streamSuccess stream).1 work
        unfold State.streamSuccess
        split <;> exact cached
    | streamFailure stream errors =>
        change State.StoredStreamsComplete
          ((queue.cacheTaskFailures available).streamFailure stream errors).1 work
        unfold State.streamFailure
        split <;> exact cached
    | groupFailure failure =>
        simp only [State.handleGraphEvent, State.groupFailure]
        split
        · exact cached
        · split <;> exact cached
  refine ⟨complete, ?_⟩
  simp only [List.flatMap_append, List.flatMap_singleton]
  have earlier : queue.StreamsSatisfy (StreamProducerSeen work
      (before.flatMap (fun event => event.identities.1) ++ event.identities.1)) :=
    fun stream member => (frame.origins stream member).mono (List.subset_append_left _ _)
  apply earlier.handleGraphEvent event (available := available)
  have children := matching.childStreams_producerSeen
  cases event with
  | taskSuccess occurrence result =>
      exact fun stream member => (children stream member).mono (List.subset_append_right _ _)
  | streamItems stream items =>
      exact fun item member child supplied =>
        (children item member child supplied).mono (List.subset_append_right _ _)
  | taskFailure | groupFailure | streamSuccess | streamFailure => trivial

private theorem StoredStreamFrame.dispatchGraphEvent {queue work before}
    (frame : StoredStreamFrame queue work before) (generated : ExecutedWork work)
    (event : GraphEvent) (matching : event.MatchesWork work) (fresh : event.Fresh before)
    (available : List (Occurrence × Nat))
    : StoredStreamFrame (queue.dispatchGraphEvent event available).1 work
        (before ++ [event]) := by
  have next := frame.handleGraphEvent generated event matching fresh available
  exact ⟨next.complete, next.origins⟩

private theorem StoredStreamFrame.replayGraphEvents {queue work before available}
    (frame : StoredStreamFrame queue work before) (generated : ExecutedWork work)
    (events : List GraphEvent) (valid : ValidGraphEvents work (before ++ events))
    : StoredStreamFrame (queue.replayGraphEvents events available) work
        (before ++ events) := by
  induction events generalizing queue before with
  | nil => simpa [State.replayGraphEvents] using frame
  | cons event rest ih =>
      have earlier : (before ++ [event]).IsPrefix (before ++ event :: rest) :=
        ⟨rest, by simp⟩
      obtain ⟨_, matching, fresh⟩ := validGraphEvents_last (valid.prefix earlier)
      have next := frame.dispatchGraphEvent generated event matching fresh available
      have result := ih next (by simpa [List.append_assoc] using valid)
      simpa only [State.replayGraphEvents, List.foldl_cons, List.append_assoc,
        List.singleton_append]
        using result

private theorem StoredStreamFrame.withTerminated {queue work before}
    (frame : StoredStreamFrame queue work before) (terminal : Bool)
    : StoredStreamFrame {queue with terminated := terminal} work before :=
  ⟨frame.complete, frame.origins⟩

private theorem StoredStreamFrame.handleBatch {queue work before}
    (frame : StoredStreamFrame queue work before) (generated : ExecutedWork work)
    (events : List GraphEvent) (valid : ValidGraphEvents work (before ++ events))
    : StoredStreamFrame (queue.handleGraphEvents events).1 work (before ++ events) := by
  by_cases ended : queue.terminated = true
  · have extended := frame.weakenHistory (List.subset_append_left before events)
    simpa only [State.handleGraphEvents, ended, ite_true] using extended
  · have running : queue.terminated = false := Bool.eq_false_iff.mpr ended
    obtain ⟨terminal, same⟩ := queue.handleGraphEvents_stateCore events running
    have replayed := frame.replayGraphEvents generated events valid
      (available := GraphEvent.availableFailures events)
    rw [same]
    exact replayed.withTerminated terminal

private theorem StoredStreamFrame.runNormalized {queue work before}
    (frame : StoredStreamFrame queue work before) (generated : ExecutedWork work)
    (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work (before ++ batches.flatten))
    : StoredStreamFrame (queue.runNormalized batches).1 work
        (before ++ batches.flatten) := by
  rw [State.runNormalized_replayBatches]
  induction batches generalizing queue before with
  | nil => simpa [State.replayBatches] using frame
  | cons batch rest ih =>
      have earlier : (before ++ batch).IsPrefix (before ++ (batch :: rest).flatten) :=
        ⟨rest.flatten, by simp [List.append_assoc]⟩
      have next := frame.handleBatch generated batch (valid.prefix earlier)
      have result := ih next (by simpa [List.append_assoc] using valid)
      simpa only [State.replayBatches, List.foldl_cons, List.flatten_cons,
        List.append_assoc]
        using result

/-- Actual host batches retain every buffered producer's structural child-stream links.
The joint frame derives producer freshness from consumed inputs while each batch uses
its own rejection snapshot. Matching and freshness suffice, including ignored inputs;
no source-start or emitted-history admission premise is added.
-/
theorem ExecutedWork.runNormalized_storedStreamsComplete {work}
    (generated : ExecutedWork work) (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work batches.flatten)
    : ((State.initialize (Work.fromExecution work)).runNormalized
        batches).1.StoredStreamsComplete
        work := by
  have initial : StoredStreamFrame (State.initialize (Work.fromExecution work)) work [] :=
    ⟨createWorkQueue_storedStreamsComplete work,
      createWorkQueue_replay_streamProducersSeen (.nil : ValidGraphEvents work [])⟩
  exact (initial.runNormalized generated batches (by simpa using valid)).complete

/-- Streams registered at an actual batch/FIFO cut have already consumed their producers. -/
theorem ExecutedWork.batchPrefix_streamProducersSeen {work}
    (generated : ExecutedWork work) (earlier : List (List GraphEvent))
    (fifo : List GraphEvent) (available : List (Occurrence × Nat))
    (valid : ValidGraphEvents work (earlier.flatten ++ fifo))
    : (((State.initialize (Work.fromExecution work)).replayBatches
          earlier).replayGraphEvents
        fifo available).StreamsSatisfy
        (StreamProducerSeen work
          ((earlier.flatten ++ fifo).flatMap (fun event => event.identities.1))) := by
  have initial : StoredStreamFrame (State.initialize (Work.fromExecution work)) work [] :=
    ⟨createWorkQueue_storedStreamsComplete work,
      createWorkQueue_replay_streamProducersSeen (.nil : ValidGraphEvents work [])⟩
  have first := initial.runNormalized generated earlier (valid.prefix
    (before := earlier.flatten) ⟨fifo, rfl⟩)
  rw [State.runNormalized_replayBatches] at first
  exact (first.replayGraphEvents generated fifo valid (available := available)).origins

-----------------------------------------------------------------------------------------
-- The complete links become notices at the actual producer flush boundary
-----------------------------------------------------------------------------------------

/-- Flushing a buffered producer announces every stream generated by that producer.
Witness: replay-derived complete links and registered-link inventory feed the complete
flush theorem. The premise is a real selected task lookup, not output admission.
-/
theorem State.StoredStreamsComplete.finishGroupSuccess_streamComplete {queue : State}
    {work} (complete : queue.StoredStreamsComplete work)
    (inventory : queue.ChildStreamInventory) (group : GroupNode)
    {occurrence node stream dependencies} (member : occurrence ∈ group.tasks)
    (found : queue.taskNode? occurrence = some node) (stored : node.value.isSome = true)
    (known : NodeAt work stream .stream dependencies (some occurrence))
    : stream.ref
      ∈ (queue.finishGroupSuccess group).2.2.newStreams.map
          Execution.DeliveryNode.ref := by
  apply inventory.finishGroupSuccess_childRef_covered group member found
  exact complete node (State.taskNode?_some found).1 stored (by simp) stream dependencies
    ((State.taskNode?_some found).2.symm ▸ known)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
