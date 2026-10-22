import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskOwnerExistence

/-! Generated source handlers preserve live owners for unfinished and buffered records.
The original reference pending ledger supplies structural registration facts; no resource
inventory or desired actual-removal endpoint is assumed.
-/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open WorkQueueSemantics (Occurrence)
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)

theorem State.TaskOwnerFrame.taskSuccess {queue : State} {work : Execution.Work}
    {settled : List Occurrence} (frame : queue.TaskOwnerFrame work)
    (accounted : queue.PendingAccounting work settled) (roots : queue.RootGroupsPresent)
    (occurrence : Occurrence) (result : TaskResult)
    (known : ∀ task ∈ result.work.tasks, TaskMatches work task)
    : (queue.taskSuccess occurrence result).1.TaskOwnerFrame work := by
  cases found : queue.taskNode? occurrence with
  | none => simpa only [State.taskSuccess, found] using frame
  | some node =>
      rw [queue.taskSuccess_eq occurrence result node found]
      have stored := frame.putExistingTaskNode node (List.mem_of_find?_eq_some found)
        { node with value := some result.value } rfl
      have prepared := stored.maybeIntegrateWork roots accounted.taskGroups
        result.work known (some occurrence)
      exact ((prepared.successFold node.task.groups [] {}).startNewWork _).drainReadyGroups

theorem State.TaskOwnerFrame.prepareItems {queue : State} {work : Execution.Work}
    {settled : List Occurrence} {stream : Execution.DeliveryNode}
    {items : List StreamItem} (frame : queue.TaskOwnerFrame work)
    (accounted : queue.PendingAccounting work settled) (roots : queue.RootGroupsPresent)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    : (queue.preparedStreamItems items).TaskOwnerFrame work := by
  let property (current : State) := current.TaskOwnerFrame work ∧ current.LiveGroupsRegistered
    ∧ current.TaskGroupsRegistered ∧ current.RootGroupsPresent
  have step (current : State) (item : StreamItem) (member : item ∈ items)
      (prior : property current) : property (current.integrateStreamItem item) := by
    have known : ∀ task ∈ item.work.tasks, TaskMatches work task := by
      intro task listed
      obtain ⟨address, payload, occurrenceEq, located⟩ :=
        matching.streamItem_childTask_producer member listed
      exact ⟨⟨address, payload, some item.occurrence, occurrenceEq, located⟩,
        matching.streamItem_childTask_groupsExact member listed⟩
    have prepared := prior.1.maybeIntegrateWork prior.2.2.2 prior.2.2.1 item.work known
    have registered := current.integrateStreamItem_registration prior.2.1 prior.2.2.1 matching member
    exact ⟨(prepared.pruneEmptyGroups _).startNewWork _, registered.1, registered.2.1,
      prior.2.2.2.integrateStreamItem_registered prior.2.1 prior.1.keys item⟩
  exact (State.preparedStreamItems_preserves property
    ⟨frame, accounted.liveGroups, accounted.taskGroups, roots⟩ items step).1

theorem State.TaskOwnerFrame.streamItems {queue : State} {work : Execution.Work}
    {settled : List Occurrence} {stream : Execution.DeliveryNode}
    {items : List StreamItem} (frame : queue.TaskOwnerFrame work)
    (accounted : queue.PendingAccounting work settled) (roots : queue.RootGroupsPresent)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    : (queue.streamItems stream items).1.TaskOwnerFrame work := by
  rw [queue.streamItems_eq stream items]
  split
  · exact frame
  · exact (frame.prepareItems accounted roots matching).drainReadyGroups

theorem State.TaskOwnerFrame.handleGraphEvent {queue : State} {work : Execution.Work}
    {settled : List Occurrence} (frame : queue.TaskOwnerFrame work)
    (accounted : queue.PendingAccounting work settled) (roots : queue.RootGroupsPresent)
    (event : GraphEvent) (matching : event.MatchesWork work)
    : (queue.handleGraphEvent event).1.TaskOwnerFrame work := by
  cases event with
  | taskSuccess occurrence result =>
      apply frame.taskSuccess accounted roots occurrence result
      intro task member
      obtain ⟨address, payload, occurrenceEq, known⟩ := matching.childTask_producer member
      exact ⟨⟨address, payload, some occurrence, occurrenceEq, known⟩,
        matching.childTask_groupsExact member⟩
  | taskFailure occurrence errors => exact frame.taskFailure occurrence errors
  | streamItems stream items => exact frame.streamItems accounted roots matching
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess]
      split <;> exact ⟨frame.owners, frame.disposition, frame.keys,
        frame.registered, frame.matching, frame.sound⟩
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> exact ⟨frame.owners, frame.disposition, frame.keys,
        frame.registered, frame.matching, frame.sound⟩

theorem ExecutedWork.replayGraphEvents_taskOwnerFrame {work : Execution.Work}
    (generated : ExecutedWork work) (events : List GraphEvent)
    (valid : ValidGraphEvents work events)
    (accepted : (State.initialize (Work.fromExecution work)).acceptsBatch events = true)
    : ((State.initialize (Work.fromExecution work)).replayGraphEvents
        events).TaskOwnerFrame
        work := by
  induction valid with
  | nil => exact createWorkQueue_taskOwnerFrame work
  | @append before event prior matching fresh ready ih =>
      have beforeAccepted := State.acceptsBatch_prefix accepted
      have accounted := (createWorkQueue_pendingAccounting work).replayGraphEvents (before := [])
        generated before prior beforeAccepted
      have roots := generated.replayGraphEvents_rootsPresent before
        (fun _ member => prior.eachMatches member)
      rw [State.replayGraphEvents_append]
      exact (ih beforeAccepted).handleGraphEvent accounted roots event matching

theorem ExecutedWork.runNormalized_taskOwnerFrame {work : Execution.Work}
    (generated : ExecutedWork work) (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    : ((State.initialize (Work.fromExecution work)).runNormalized
        batches).1.TaskOwnerFrame
        work := by
  have accepted := (State.initialize (Work.fromExecution work)).batchesStarted_acceptsBatch batches
    (by rwa [← inputsStarted_eq_batchesStarted])
  have replayed := generated.replayGraphEvents_taskOwnerFrame batches.flatten valid accepted
  obtain ⟨terminal, same⟩ := createWorkQueue_runNormalized_stateCore started
  rw [same]
  exact ⟨replayed.owners, replayed.disposition, replayed.keys,
    replayed.registered, replayed.matching, replayed.sound⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
