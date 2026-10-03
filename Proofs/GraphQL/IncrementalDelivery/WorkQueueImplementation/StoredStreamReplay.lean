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

/-- Starting a task retains earlier links and creates only an unresolved node.
Witness: the start guard either does nothing or appends a node with no stored value.
-/
theorem State.StoredStreamsComplete.startTask {queue : State} {work}
    (complete : queue.StoredStreamsComplete work) (occurrence : Occurrence)
    : (queue.startTask occurrence).StoredStreamsComplete work := by
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

/-- Activating a group preserves complete links on every buffered value.
Witness: healthy group activation folds unresolved task starts; other branches do nothing.
-/
theorem State.StoredStreamsComplete.startGroup {queue : State} {work}
    (complete : queue.StoredStreamsComplete work) (ref : NodeRef)
    : (queue.startGroup ref).StoredStreamsComplete work := by
  unfold State.startGroup
  split
  · exact complete
  · split
    · exact complete
    · exact fold_preserves (fun current => current.StoredStreamsComplete work) State.startTask
        (fun _ occurrence prior => prior.startTask occurrence) _ _ complete

/-- Activating released groups and streams retains complete producer links.
Witness: group starts preserve links; stream starts modify only active stream refs.
-/
theorem State.StoredStreamsComplete.startNewWork {queue : State} {work}
    (complete : queue.StoredStreamsComplete work) (released : NewWork)
    : (queue.startNewWork released).StoredStreamsComplete work := by
  let newRefs := released.newGroups.map Execution.DeliveryNode.ref
  have groups := fold_preserves (fun current => current.StoredStreamsComplete work)
    State.startGroup (fun _ ref prior => prior.startGroup ref)
    newRefs { queue with rootGroups := queue.rootGroups ++ newRefs }
    complete
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

/-- Recursive mixed draining preserves complete links for all surviving buffered tasks.
Witness: both closure branches remove whole nodes; successful activation adds empty nodes.
-/
theorem State.StoredStreamsComplete.drainReadyGroups {queue : State} {work}
    (complete : queue.StoredStreamsComplete work)
    : queue.drainReadyGroups.1.StoredStreamsComplete work := by
  apply State.drainReadyGroups_preserves (fun current => current.StoredStreamsComplete work)
    (valid := complete)
  · intro current node prior _ _ _ _
    exact (prior.finishGroupSuccess node).startNewWork _
  · intro current node errors prior _ _ _
    exact prior.removeGroup _

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
    : (queue.taskSuccess occurrence result).1.StoredStreamsComplete work := by
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
      rw [queue.taskSuccess_eq occurrence result node found]
      split
      · exact complete.removeTask occurrence
      · exact (processed.startNewWork _).drainReadyGroups

/-- Task failure cannot silently strip links from a retained buffered producer.
Witness: cache updates leave task nodes unchanged, and failure cleanup only removes nodes.
-/
theorem State.StoredStreamsComplete.taskFailure {queue : State} {work}
    (complete : queue.StoredStreamsComplete work) (occurrence : Occurrence) (errors : Nat)
    : (queue.taskFailure occurrence errors).1.StoredStreamsComplete work := by
  unfold State.taskFailure
  split
  · exact complete
  · split
    · exact complete.removeTask occurrence
    apply fold_preserves
      (fun acc : State × List WorkQueueEvent => acc.1.StoredStreamsComplete work)
    · intro acc group prior
      obtain ⟨current, events⟩ := acc
      dsimp only
      split
      · exact prior
      · split
        · exact prior.removeGroup _
        · exact prior
    · exact fun node member => complete node (List.mem_filter.mp member).1

/-- Stream item integration preserves all existing buffered object links.
Witness: each item registers root work without installing an object value, then the final
drain removes or retains complete producer nodes in its actual execution order.
-/
theorem State.StoredStreamsComplete.streamItems {queue : State} {work}
    (complete : queue.StoredStreamsComplete work) (stream : Execution.DeliveryNode)
    (items : List StreamItem)
    : (queue.streamItems stream items).1.StoredStreamsComplete work := by
  let step (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue) (item : StreamItem) :=
    let (current, groups, streams, values) := acc
    let (integrated, newWork) := current.maybeIntegrateWork item.work
    let (pruned, nonempty) := integrated.pruneEmptyGroups newWork.newGroups
    (pruned.startNewWork { newWork with newGroups := nonempty },
      groups ++ nonempty, streams ++ newWork.newStreams, values ++ [item.value])
  have folded := fold_preserves (fun acc => acc.1.StoredStreamsComplete work) step
    (fun acc item prior =>
      ((prior.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _)
    items (queue, [], [], []) complete
  unfold State.streamItems
  split
  · exact complete
  · exact folded.drainReadyGroups

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
    : ((State.initialize (Work.fromExecution work)).replayGraphEvents
        events).StoredStreamsComplete
        work := by
  induction valid with
  | nil => exact createWorkQueue_storedStreamsComplete work
  | @append before event valid matching fresh ready ih =>
      rw [State.replayGraphEvents_append]
      cases event with
      | taskSuccess occurrence result =>
          exact ih.taskSuccess matching
            (fun _ member => generated.replayGraphEvents_taskChildStream_absent
              valid matching fresh member)
      | taskFailure occurrence errors => exact ih.taskFailure occurrence errors
      | streamItems stream items => exact ih.streamItems stream items
      | streamSuccess stream =>
          simp only [State.handleGraphEvent, State.streamSuccess]
          split <;> exact ih
      | streamFailure stream errors =>
          simp only [State.handleGraphEvent, State.streamFailure]
          split <;> exact ih

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
