import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedDrainProjection
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureRootCompletion

/-! Derive compatible ready-drain frames at the actual reference handler phases.
These constructions use generated source prefixes, not a desired reduction endpoint or
alternative replay equivalence. The registration bridge can transport them afterwards.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue
open WorkQueueSemantics (NodeRefs Occurrence)
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)

/-- Proof notation for the reference task-success state immediately before ready draining.
It names the actual shared registration/owner/release calculation, not a new public queue
algorithm or a cleanup observer.
-/
def referenceTaskSuccessReady (queue : ReferenceWorkQueue.State) (occurrence : Occurrence)
    (result : ReferenceWorkQueue.TaskResult) (node : ReferenceWorkQueue.TaskNode)
    : ReferenceWorkQueue.State :=
  let integrated :=
    (ReferenceWorkQueue.State.maybeIntegrateWork
      (queue.putTaskNode { node with value := some result.value }) result.work
      (some occurrence)).1
  let released :=
    node.task.groups.foldl ReferenceWorkQueue.successGroupStep (integrated, [], {})
  released.1.startNewWork released.2.2

theorem referencePrefix_childGroupsUnique (work : Work) (events : List GraphEvent)
    : (ReferenceWorkQueue.State.replayGraphEvents
        (ReferenceWorkQueue.State.initialize (ReferenceWorkQueue.Work.fromExecution work))
        events).ChildGroupsUnique := by
  have loop (more : List GraphEvent) (queue : ReferenceWorkQueue.State)
      (unique : queue.ChildGroupsUnique)
      : (queue.replayGraphEvents more).ChildGroupsUnique := by
    induction more generalizing queue with
    | nil => exact unique
    | cons event rest ih => exact ih _ (unique.handleGraphEvent event)
  exact loop events _ (ReferenceWorkQueue.createWorkQueue_childGroupsUnique _)

theorem referencePrefix_removalForest {work : Work}
    (generated : ReferenceWorkQueue.ExecutedWork work) (events : List GraphEvent)
    (matching : ∀ event ∈ events, event.MatchesWork work)
    : ∃ parents,
        (ReferenceWorkQueue.State.replayGraphEvents
          (ReferenceWorkQueue.State.initialize
            (ReferenceWorkQueue.Work.fromExecution work))
          events).RemovalForest
          parents := by
  obtain ⟨parents, canonical, frame⟩ := generated.replay_rootClosureFrame matching
  exact ⟨parents, ReferenceWorkQueue.State.RemovalForest.of_generated generated
    (referencePrefix_childGroupsUnique work events) frame.links frame.records canonical⟩

private theorem childGroupsUnique_successFold (groups : List Execution.DeliveryNode)
    (acc : ReferenceWorkQueue.State × List WorkQueueEvent × ReferenceWorkQueue.NewWork)
    (unique : acc.1.ChildGroupsUnique)
    : (groups.foldl ReferenceWorkQueue.successGroupStep acc).1.ChildGroupsUnique := by
  induction groups generalizing acc with
  | nil => exact unique
  | cons group rest ih =>
      simp only [List.foldl_cons, ReferenceWorkQueue.successGroupStep]
      split
      · exact ih _ unique
      · rename_i node found
        have changed := unique.putGroupNode { node with pending := node.pending - 1 }
          (unique node (List.mem_of_find?_eq_some found))
        split
        · exact ih _ (changed.finishGroupSuccess _)
        · exact ih _ changed

private theorem childGroupsUnique_preparedItems (queue : ReferenceWorkQueue.State)
    (unique : queue.ChildGroupsUnique) (items : List ReferenceWorkQueue.StreamItem)
    : (queue.preparedStreamItems items).ChildGroupsUnique :=
  ReferenceWorkQueue.State.preparedStreamItems_preserves
    ReferenceWorkQueue.State.ChildGroupsUnique unique items
    (fun _ item _ prior =>
      ((prior.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _)

/-- The same reference task-success ready boundary supplies owners and the removal forest.
All local record and forest premises are independently derived at that exact phase.
-/
theorem referencePrefix_taskSuccess_drainFrames {work : Work}
    (generated : ReferenceWorkQueue.ExecutedWork work) (events : List GraphEvent)
    (occurrence : Occurrence) (result : ReferenceWorkQueue.TaskResult)
    (valid
      : ReferenceWorkQueue.ValidGraphEvents work
          (events ++ [.taskSuccess occurrence result]))
    (accepted
      : (ReferenceWorkQueue.State.initialize
          (ReferenceWorkQueue.Work.fromExecution work)).acceptsBatch
          events
        = true)
    (node : ReferenceWorkQueue.TaskNode)
    (found
      : (ReferenceWorkQueue.State.replayGraphEvents
          (ReferenceWorkQueue.State.initialize
            (ReferenceWorkQueue.Work.fromExecution work))
          events).taskNode?
          occurrence
        = some node)
    : let queue :=
        (ReferenceWorkQueue.State.initialize
          (ReferenceWorkQueue.Work.fromExecution work)).replayGraphEvents
          events
      let ready := referenceTaskSuccessReady queue occurrence result node
      ∃ parents, ready.TaskOwnerFrame work ∧ ready.RemovalForest parents := by
  obtain ⟨prior, matched, _⟩ := ReferenceWorkQueue.validGraphEvents_last valid
  have sources : ∀ event ∈ events, event.MatchesWork work := fun _ member => prior.eachMatches member
  have roots := generated.replayGraphEvents_rootsPresent events sources
  have accounted := (ReferenceWorkQueue.createWorkQueue_pendingAccounting work).replayGraphEvents
    (before := []) generated events prior accepted
  have frame := generated.replayGraphEvents_taskOwnerFrame events prior accepted
  have known : ∀ task ∈ result.work.tasks, ReferenceWorkQueue.TaskMatches work task := by
    intro task member
    obtain ⟨address, payload, same, located⟩ := matched.childTask_producer member
    exact ⟨⟨address, payload, some occurrence, same, located⟩, matched.childTask_groupsExact member⟩
  have stored := frame.putExistingTaskNode node (List.mem_of_find?_eq_some found)
    { node with value := some result.value } rfl
  have integrated := stored.maybeIntegrateWork roots accounted.taskGroups result.work known (some occurrence)
  let queue := ReferenceWorkQueue.State.replayGraphEvents
    (ReferenceWorkQueue.State.initialize (ReferenceWorkQueue.Work.fromExecution work)) events
  let prepared := ((queue.putTaskNode { node with value := some result.value }).maybeIntegrateWork
    result.work (some occurrence)).1
  let released := node.task.groups.foldl ReferenceWorkQueue.successGroupStep (prepared, [], {})
  have ready := (integrated.successFold node.task.groups [] {}).startNewWork released.2.2
  obtain ⟨parents, canonical, metadata⟩ := generated.taskSuccess_drain_liveRootFrame
    sources matched node roots
  have initialChildren := referencePrefix_childGroupsUnique work events
  have storedChildren : (queue.putTaskNode { node with value := some result.value }).ChildGroupsUnique :=
    initialChildren
  have integratedChildren := storedChildren.maybeIntegrateWork result.work (some occurrence)
  have readyChildren := (childGroupsUnique_successFold node.task.groups (_, [], {})
    integratedChildren).startNewWork released.2.2
  refine ⟨parents, ready, ReferenceWorkQueue.State.RemovalForest.of_generated generated
    readyChildren metadata.links metadata.records canonical⟩

/-- Arbitrary-width prepared stream items have one compatible owner/forest endpoint. -/
theorem referencePrefix_streamItems_drainFrames {work : Work}
    (generated : ReferenceWorkQueue.ExecutedWork work) (events : List GraphEvent)
    (valid : ReferenceWorkQueue.ValidGraphEvents work events)
    (accepted
      : (ReferenceWorkQueue.State.initialize
          (ReferenceWorkQueue.Work.fromExecution work)).acceptsBatch
          events
        = true)
    (stream : Execution.DeliveryNode) (items : List ReferenceWorkQueue.StreamItem)
    (matched : (ReferenceWorkQueue.GraphEvent.streamItems stream items).MatchesWork work)
    : let queue :=
        (ReferenceWorkQueue.State.initialize
          (ReferenceWorkQueue.Work.fromExecution work)).replayGraphEvents
          events
      ∃ parents,
        (queue.preparedStreamItems items).TaskOwnerFrame work
        ∧ (queue.preparedStreamItems items).RemovalForest parents := by
  have sources : ∀ event ∈ events, event.MatchesWork work := fun _ member => valid.eachMatches member
  have roots := generated.replayGraphEvents_rootsPresent events sources
  have accounted := (ReferenceWorkQueue.createWorkQueue_pendingAccounting work).replayGraphEvents
    (before := []) generated events valid accepted
  have frame := generated.replayGraphEvents_taskOwnerFrame events valid accepted
  obtain ⟨parents, canonical, metadata⟩ := generated.streamItems_prepared_liveRootFrame sources matched roots
  exact ⟨parents, frame.prepareItems accounted roots matched,
    ReferenceWorkQueue.State.RemovalForest.of_generated generated
      (childGroupsUnique_preparedItems _ (referencePrefix_childGroupsUnique work events) items)
      metadata.links metadata.records canonical⟩

end GraphQL.IncrementalDelivery.AlternativeWorkQueue
