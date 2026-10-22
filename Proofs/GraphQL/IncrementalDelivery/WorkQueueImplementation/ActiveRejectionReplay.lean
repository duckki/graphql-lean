import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ActiveFailureCaches
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskNodeKeys
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskOwnerHandlers
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureRemoval

/-! Actual source-handler boundaries leave no retained rejection on an active owner. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

private def ClearOn (queue : State) (keep : NodeRef → Prop) : Prop :=
  ∀ group ∈ queue.groupNodes,
    group.group.node.ref ∈ queue.rootGroups
    → keep group.group.node.ref
    → queue.rejectedTask? group = none

private theorem ClearOn.removeGroup {queue : State} {keep}
    (clear : ClearOn queue keep) (unique : queue.TaskNodeKeysUnique) (ref : NodeRef)
    : ClearOn (queue.removeGroup ref) keep := by
  intro group member active selected
  apply State.rejectedTask?_eq_none_iff.mpr
  intro occurrence listed node found
  obtain ⟨included, same⟩ := State.taskNode?_some found
  have oldMember : node ∈ queue.taskNodes := (List.mem_filter.mp included).1
  have oldFound : queue.taskNode? occurrence = some node := by
    simpa only [same] using unique.lookup oldMember
  exact State.rejectedTask?_eq_none_iff.mp
    (clear group (List.mem_filter.mp member).1
      (queue.removeGroup_rootsSubset ref active) selected) occurrence listed node oldFound

/-- Recording a rejection closes all its active owners while dormant owners retain it. -/
theorem State.NoActiveCachedFailure.taskFailure {queue : State} {work : Execution.Work}
    (clear : queue.NoActiveCachedFailure) (unique : queue.TaskNodeKeysUnique)
    (present : queue.RootGroupsPresent) (registered : queue.StartedTasksRegistered)
    (matching : queue.RegisteredTasksMatch work) (sound : queue.GroupMembershipSound)
    (occurrence : Occurrence) (errors : Nat)
    : (queue.taskFailure occurrence errors).1.NoActiveCachedFailure := by
  cases found : queue.taskNode? occurrence with
  | none => simpa only [State.taskFailure, found] using clear
  | some incoming =>
      have incomingMember := (State.taskNode?_some found).1
      have incomingRef := (State.taskNode?_some found).2
      have incomingRegistered := registered incoming incomingMember
      obtain ⟨⟨address, payload, producer, _, incomingTask⟩, _⟩ :=
        matching incoming.task incomingRegistered
      let keep := fun ref => ref ∉ incoming.task.groups.map Execution.DeliveryNode.ref
      let stored := queue.putTaskNode { incoming with rejection := some errors }
      have initial : ClearOn stored keep := by
        intro group member active outside
        apply State.rejectedTask?_eq_none_iff.mpr
        intro task listed node selected
        obtain ⟨nodeMember, nodeRef⟩ := State.taskNode?_some selected
        obtain ⟨old, oldMember, equal⟩ := List.mem_map.mp nodeMember
        split at equal
        · subst node
          have taskEq : task = occurrence := nodeRef.symm.trans incomingRef
          obtain ⟨catalogue, included, identity, owner⟩ := sound group member task listed
          obtain ⟨⟨_, otherPayload, birth, _, otherTask⟩, _⟩ := matching catalogue included
          rw [identity, taskEq, ← incomingRef] at otherTask
          have owners := (otherTask.unique incomingTask).1
          exact False.elim (outside (owners ▸ owner))
        · subst node
          have oldFound : queue.taskNode? task = some old := by
            simpa only [nodeRef] using unique.lookup oldMember
          exact State.rejectedTask?_eq_none_iff.mp (clear group member active)
            task listed old oldFound
      let invariant (current : State) :=
        current.TaskNodeKeysUnique ∧ current.RootGroupsPresent ∧ ClearOn current keep
      have final := failureGroupFold_preserves invariant
        (fun current ref prior =>
          ⟨prior.1.removeGroup ref, prior.2.1.removeGroup ref,
            prior.2.2.removeGroup prior.1 ref⟩) errors incoming.task.groups
        (stored, []) ⟨unique.putTaskNode _, present, initial⟩
      intro group member active
      have outside : keep group.group.node.ref := by
        intro owner
        exact queue.taskFailure_ownerRootsAbsent present occurrence errors incoming found
          group.group.node.ref owner active
      rw [queue.taskFailure_eq occurrence errors incoming found] at member active ⊢
      exact final.2.2 group member active outside

/-- Success ends with a full drain; absent computation results preserve the old boundary. -/
theorem State.NoActiveCachedFailure.taskSuccess {queue : State} {work : Execution.Work}
    {settled : List Occurrence}
    (clear : queue.NoActiveCachedFailure) (frame : queue.TaskOwnerFrame work)
    (accounted : queue.PendingAccounting work settled) (roots : queue.RootGroupsPresent)
    (occurrence : Occurrence) (result : TaskResult)
    (known : ∀ task ∈ result.work.tasks, TaskMatches work task)
    : (queue.taskSuccess occurrence result).1.NoActiveCachedFailure := by
  cases found : queue.taskNode? occurrence with
  | none => simpa only [State.taskSuccess, found] using clear
  | some node =>
      rw [queue.taskSuccess_eq occurrence result node found]
      have stored := frame.putExistingTaskNode node (List.mem_of_find?_eq_some found)
        { node with value := some result.value } rfl
      have prepared := stored.maybeIntegrateWork roots accounted.taskGroups result.work known
        (some occurrence)
      let integrated := ((queue.putTaskNode { node with value := some result.value }).maybeIntegrateWork
        result.work (some occurrence)).1
      let folded := node.task.groups.foldl successGroupStep (integrated, [], {})
      have activated := (prepared.successFold node.task.groups [] {}).startNewWork folded.2.2
      exact State.drainReadyGroups_noActiveCachedFailure _ activated.sound activated.registered
        activated.matching activated.drainReadyGroups.keys

/-- Item preparation ends with a full drain before exposing the next source boundary. -/
theorem State.NoActiveCachedFailure.streamItems {queue : State} {work : Execution.Work}
    {settled : List Occurrence} {stream items}
    (clear : queue.NoActiveCachedFailure) (frame : queue.TaskOwnerFrame work)
    (accounted : queue.PendingAccounting work settled) (roots : queue.RootGroupsPresent)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    : (queue.streamItems stream items).1.NoActiveCachedFailure := by
  have prepared := frame.prepareItems accounted roots matching
  rw [queue.streamItems_eq stream items]
  split
  · exact clear
  · exact State.drainReadyGroups_noActiveCachedFailure _ prepared.sound prepared.registered
      prepared.matching prepared.drainReadyGroups.keys

/-- Initialization retains no rejection from which an active group could fail. -/
theorem createWorkQueue_noActiveCachedFailure (input : Work)
    : (State.initialize input).NoActiveCachedFailure := by
  intro group member active
  apply State.rejectedTask?_eq_none_iff.mpr
  intro occurrence listed node found
  have facts := createWorkQueue_taskRejections input (fun _ _ => False)
  cases rejected : node.rejection with
  | none => rfl
  | some errors =>
      exact False.elim (facts node (State.taskNode?_some found).1 errors rejected)

/-- Valid admitted source prefixes leave active groups without a replayable rejection. -/
theorem ExecutedWork.replayGraphEvents_noActiveCachedFailure {work : Execution.Work}
    (generated : ExecutedWork work) (events : List GraphEvent)
    (valid : ValidGraphEvents work events)
    (accepted : (State.initialize (Work.fromExecution work)).acceptsBatch events = true)
    : ((State.initialize (Work.fromExecution work)).replayGraphEvents
        events).NoActiveCachedFailure := by
  induction valid with
  | nil => exact createWorkQueue_noActiveCachedFailure _
  | @append before event prior matching fresh ready ih =>
      have beforeAccepted := State.acceptsBatch_prefix accepted
      have accounted := (createWorkQueue_pendingAccounting work).replayGraphEvents (before := [])
        generated before prior beforeAccepted
      have roots := generated.replayGraphEvents_rootsPresent before
        (fun _ member => prior.eachMatches member)
      have frame := generated.replayGraphEvents_taskOwnerFrame before prior beforeAccepted
      have unique := (createWorkQueue_taskNodeKeysUnique (Work.fromExecution work)).replayGraphEvents before
      have clear := ih beforeAccepted
      rw [State.replayGraphEvents_append]
      cases event with
      | taskSuccess occurrence result =>
          exact clear.taskSuccess frame accounted roots occurrence result
            (by
              intro task member
              obtain ⟨address, payload, equal, known⟩ := matching.childTask_producer member
              exact ⟨⟨address, payload, some occurrence, equal, known⟩,
                matching.childTask_groupsExact member⟩)
      | taskFailure occurrence errors =>
          exact clear.taskFailure unique roots frame.registered frame.matching frame.sound occurrence errors
      | streamItems stream items => exact clear.streamItems frame accounted roots matching
      | streamSuccess stream =>
          simp only [State.handleGraphEvent, State.streamSuccess]
          split <;> exact clear
      | streamFailure stream errors =>
          simp only [State.handleGraphEvent, State.streamFailure]
          split <;> exact clear

/-- Normalized replay preserves the same rejection-free active boundary. -/
theorem createWorkQueue_runNormalized_noActiveCachedFailure {work : Execution.Work}
    (generated : ExecutedWork work) (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    : ((State.initialize (Work.fromExecution work)).runNormalized
        batches).1.NoActiveCachedFailure := by
  have accepted := (State.initialize (Work.fromExecution work)).batchesStarted_acceptsBatch batches
    (by rwa [← inputsStarted_eq_batchesStarted])
  obtain ⟨terminal, same⟩ := createWorkQueue_runNormalized_stateCore started
  rw [same]
  exact generated.replayGraphEvents_noActiveCachedFailure batches.flatten valid accepted

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
