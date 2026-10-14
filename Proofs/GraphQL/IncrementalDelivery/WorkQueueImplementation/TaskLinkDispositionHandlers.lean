import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskLinkDisposition
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PendingReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamPreparation

/-! Source-handler construction of complete-or-retired task links. These reference-kernel
facts are independent of alternative replay and use the original generated source contract.
-/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open WorkQueueSemantics (Occurrence NodeRefs)
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)

-----------------------------------------------------------------------------------------
-- Owner settlement updates preserve dispositions through success and failure
-----------------------------------------------------------------------------------------

private theorem successFold_disposition (groups : List Execution.DeliveryNode)
    (acc : State × List WorkQueueEvent × NewWork)
    (disposition : acc.1.TaskLinkDisposition) (unique : acc.1.GroupRefsUnique)
    : (groups.foldl successGroupStep acc).1.TaskLinkDisposition := by
  induction groups generalizing acc with
  | nil => exact disposition
  | cons group rest ih =>
      simp only [List.foldl_cons, successGroupStep]
      split
      · exact ih _ disposition unique
      · rename_i node found
        let updated := { node with pending := node.pending - 1 }
        have next := disposition.putGroupNodeSameTasks unique node
          (List.mem_of_find?_eq_some found) updated rfl rfl
        have nextKeys := unique.putGroupNode updated
        split
        · exact ih _ (next.finishGroupSuccess updated) (nextKeys.finishGroupSuccess updated)
        · exact ih _ next nextKeys

private theorem failureFold_disposition (errors : Nat)
    (groups : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent)
    (disposition : acc.1.TaskLinkDisposition) (unique : acc.1.GroupRefsUnique)
    : (groups.foldl (failureGroupStep errors) acc).1.TaskLinkDisposition := by
  induction groups generalizing acc with
  | nil => exact disposition
  | cons group rest ih =>
      simp only [List.foldl_cons, failureGroupStep]
      split
      · exact ih _ disposition unique
      · rename_i node found
        split
        · exact ih _ (disposition.removeGroup node.group.node.ref)
            (unique.removeGroup node.group.node.ref)
        · let updated := { node with
            pending := node.pending - 1
            failure := some (node.failure.getD 0 + errors) }
          exact ih _ (disposition.putGroupNodeSameTasks unique node
            (List.mem_of_find?_eq_some found) updated rfl rfl) (unique.putGroupNode updated)

theorem State.TaskLinkDisposition.taskSuccess {queue : State} {work : Execution.Work}
    {settled : List Occurrence} (disposition : queue.TaskLinkDisposition)
    (accounted : queue.PendingAccounting work settled) (occurrence : Occurrence)
    (result : TaskResult) (known : ∀ task ∈ result.work.tasks, TaskMatches work task)
    : (queue.taskSuccess occurrence result).1.TaskLinkDisposition := by
  cases found : queue.taskNode? occurrence with
  | none => simpa only [State.taskSuccess, found] using disposition
  | some node =>
      rw [queue.taskSuccess_eq occurrence result node found]
      split
      · exact disposition.removeTask occurrence
      · let stored := queue.putTaskNode { node with value := some result.value }
        have registered : stored.TaskGroupsRegistered := accounted.taskGroups
        have matching : stored.RegisteredTasksMatch work := accounted.matching
        have keys : stored.GroupRefsUnique := accounted.refs
        have installed : stored.TaskLinkDisposition :=
          disposition.putTaskNode { node with value := some result.value }
        have prepared := installed.maybeIntegrateWork keys registered matching
          result.work known (some occurrence)
        have preparedKeys := keys.maybeIntegrateWork result.work (some occurrence)
        have folded := successFold_disposition node.task.groups (_, [], {}) prepared preparedKeys
        exact (folded.startNewWork _).drainReadyGroups

theorem State.TaskLinkDisposition.taskFailure {queue : State}
    (disposition : queue.TaskLinkDisposition) (unique : queue.GroupRefsUnique)
    (occurrence : Occurrence) (errors : Nat)
    : (queue.taskFailure occurrence errors).1.TaskLinkDisposition := by
  cases found : queue.taskNode? occurrence with
  | none => simpa only [State.taskFailure, found] using disposition
  | some node =>
      rw [queue.taskFailure_eq occurrence errors node found]
      split
      · exact disposition.removeTask occurrence
      · exact failureFold_disposition errors node.task.groups (_, [])
          (disposition.removeTask occurrence) (unique.removeTask occurrence)

-----------------------------------------------------------------------------------------
-- Stream preparation reuses the same scope and release primitives
-----------------------------------------------------------------------------------------

theorem State.TaskLinkDisposition.prepareItems {queue : State} {work : Execution.Work}
    {settled : List Occurrence} {stream : Execution.DeliveryNode}
    {items : List StreamItem} (disposition : queue.TaskLinkDisposition)
    (accounted : queue.PendingAccounting work settled)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    : (queue.preparedStreamItems items).TaskLinkDisposition := by
  let property (current : State) := current.TaskLinkDisposition ∧ current.GroupRefsUnique
    ∧ current.LiveGroupsRegistered ∧ current.TaskGroupsRegistered ∧ current.RegisteredTasksMatch work
  have step (current : State) (item : StreamItem) (member : item ∈ items)
      (prior : property current) : property (current.integrateStreamItem item) := by
    have known : ∀ task ∈ item.work.tasks, TaskMatches work task := by
      intro task listed
      obtain ⟨address, payload, occurrenceEq, located⟩ :=
        matching.streamItem_childTask_producer member listed
      exact ⟨⟨address, payload, some item.occurrence, occurrenceEq, located⟩,
        matching.streamItem_childTask_groupsExact member listed⟩
    have prepared := prior.1.maybeIntegrateWork prior.2.1 prior.2.2.2.1 prior.2.2.2.2
      item.work known
    have registered := current.integrateStreamItem_registration prior.2.2.1 prior.2.2.2.1
      matching member
    exact ⟨(prepared.pruneEmptyGroups _).startNewWork _,
      ((prior.2.1.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _,
      registered.1, registered.2.1,
      ((prior.2.2.2.2.maybeIntegrateWork item.work known).pruneEmptyGroups _).startNewWork _⟩
  exact (State.preparedStreamItems_preserves property
          ⟨
            disposition,
            accounted.refs,
            accounted.liveGroups,
            accounted.taskGroups,
            accounted.matching
          ⟩
          items step).1

theorem State.TaskLinkDisposition.streamItems {queue : State} {work : Execution.Work}
    {settled : List Occurrence} {stream : Execution.DeliveryNode}
    {items : List StreamItem} (disposition : queue.TaskLinkDisposition)
    (accounted : queue.PendingAccounting work settled)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    : (queue.streamItems stream items).1.TaskLinkDisposition := by
  rw [queue.streamItems_eq stream items]
  split
  · exact disposition
  · exact (disposition.prepareItems accounted matching).drainReadyGroups

-----------------------------------------------------------------------------------------
-- Generated source prefixes construct complete links for every live task record
-----------------------------------------------------------------------------------------

theorem State.TaskLinkDisposition.handleGraphEvent {queue : State} {work : Execution.Work}
    {settled : List Occurrence} (disposition : queue.TaskLinkDisposition)
    (accounted : queue.PendingAccounting work settled) (event : GraphEvent)
    (matching : event.MatchesWork work)
    : (queue.handleGraphEvent event).1.TaskLinkDisposition := by
  cases event with
  | taskSuccess occurrence result =>
      apply disposition.taskSuccess accounted occurrence result
      intro task member
      obtain ⟨address, payload, occurrenceEq, known⟩ := matching.childTask_producer member
      exact ⟨⟨address, payload, some occurrence, occurrenceEq, known⟩,
        matching.childTask_groupsExact member⟩
  | taskFailure occurrence errors =>
      exact disposition.taskFailure accounted.refs occurrence errors
  | streamItems stream items => exact disposition.streamItems accounted matching
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess]
      split <;> exact disposition
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> exact disposition

theorem State.TaskLinkDisposition.replayGraphEvents {queue : State} {work before}
    (disposition : queue.TaskLinkDisposition)
    (accounted : queue.PendingAccounting work (GraphEvent.taskSettlements before))
    (generated : ExecutedWork work) (events : List GraphEvent)
    (valid : ValidGraphEvents work (before ++ events))
    (accepted : queue.acceptsBatch events = true)
    : (queue.replayGraphEvents events).TaskLinkDisposition := by
  induction events generalizing queue before with
  | nil => exact disposition
  | cons event rest ih =>
      have earlier : (before ++ [event]).IsPrefix (before ++ event :: rest) :=
        ⟨rest, by simp⟩
      obtain ⟨_, matching, fresh⟩ := validGraphEvents_last (valid.prefix earlier)
      have accepts : queue.acceptsGraphEvent event = true
          ∧ (queue.handleGraphEvent event).1.acceptsBatch rest = true := by
        simpa only [State.acceptsBatch, Bool.and_eq_true] using accepted
      have next := accounted.handleGraphEvent generated
        (GraphEvent.taskSettlements_subsetIdentities before) event matching fresh accepts.1
      rw [← GraphEvent.taskSettlements_append] at next
      exact ih (disposition.handleGraphEvent accounted event matching) next
        (by simpa only [List.append_assoc, List.singleton_append] using valid) accepts.2

theorem ExecutedWork.runNormalized_taskLinkDisposition {work : Execution.Work}
    (generated : ExecutedWork work) (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    : ((State.initialize (Work.fromExecution work)).runNormalized
        batches).1.TaskLinkDisposition := by
  have accepted := (State.initialize (Work.fromExecution work)).batchesStarted_acceptsBatch batches
    (by rwa [← inputsStarted_eq_batchesStarted])
  have replayed := (createWorkQueue_taskLinkDisposition (Work.fromExecution work)).replayGraphEvents
    (before := []) (createWorkQueue_pendingAccounting work) generated batches.flatten valid accepted
  obtain ⟨terminal, same⟩ := createWorkQueue_runNormalized_stateCore started
  rw [same]
  exact replayed

/-- Original generated source-domain target, with no caller-supplied record-frame facts. -/
def GeneratedStartedTaskLinks : Prop :=
  ∀ (work : Execution.Work) (batches : List (List GraphEvent)),
    ExecutedWork work
    → ValidGraphEvents work batches.flatten
    → inputsStarted work batches = true
    → let queue := ((State.initialize (Work.fromExecution work)).runNormalized batches).1
      ∀ node ∈ queue.taskNodes,
        queue.TaskLinkedOn node.task.occurrence
          (node.task.groups.map Execution.DeliveryNode.ref)

theorem GeneratedStartedTaskLinks_holds : GeneratedStartedTaskLinks := by
  intro work batches generated valid started
  dsimp only
  intro node member
  exact (generated.runNormalized_taskLinkDisposition batches valid started).startedLinks
    (State.runNormalized_startedTasksRegistered
      (createWorkQueue_startedTasksRegistered (Work.fromExecution work)) batches) member

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
