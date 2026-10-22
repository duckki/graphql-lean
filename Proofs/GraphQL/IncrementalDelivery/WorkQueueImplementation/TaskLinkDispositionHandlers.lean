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

theorem State.TaskLinkDisposition.taskSuccess {queue : State} {work : Execution.Work}
    {settled : List Occurrence} (disposition : queue.TaskLinkDisposition)
    (accounted : queue.PendingAccounting work settled) (occurrence : Occurrence)
    (result : TaskResult) (known : ∀ task ∈ result.work.tasks, TaskMatches work task)
    (available : List (Occurrence × Nat) := [])
    : (queue.taskSuccess occurrence result available).1.TaskLinkDisposition := by
  cases found : queue.taskNode? occurrence with
  | none => simpa only [State.taskSuccess, found] using disposition
  | some node =>
      rw [queue.taskSuccess_eq occurrence result node found available]
      let stored := queue.putTaskNode { node with value := some result.value }
      have registered : stored.TaskGroupsRegistered := accounted.taskGroups
      have matching : stored.RegisteredTasksMatch work := accounted.matching
      have keys : stored.GroupRefsUnique := accounted.refs
      have installed : stored.TaskLinkDisposition :=
        disposition.putTaskNode { node with value := some result.value }
      have prepared := installed.maybeIntegrateWork keys registered matching
        result.work known (some occurrence)
      have preparedKeys := keys.maybeIntegrateWork result.work (some occurrence)
      have folded := successFold_disposition node.task.groups (_, [], {}) prepared preparedKeys
      exact (folded.startNewWork _ available).drainReadyGroups available

-----------------------------------------------------------------------------------------
-- Stream preparation reuses the same scope and release primitives
-----------------------------------------------------------------------------------------

theorem State.TaskLinkDisposition.prepareItems {queue : State} {work : Execution.Work}
    {settled : List Occurrence} {stream : Execution.DeliveryNode}
    {items : List StreamItem} (disposition : queue.TaskLinkDisposition)
    (accounted : queue.PendingAccounting work settled)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : (queue.preparedStreamItems items available).TaskLinkDisposition := by
  let property (current : State) := current.TaskLinkDisposition ∧ current.GroupRefsUnique
    ∧ current.RegistrationFrame work ∧ current.RegisteredTasksMatch work
  have step (current : State) (item : StreamItem) (member : item ∈ items)
      (prior : property current) : property (current.integrateStreamItem item available) := by
    have known : ∀ task ∈ item.work.tasks, TaskMatches work task := by
      intro task listed
      obtain ⟨address, payload, occurrenceEq, located⟩ :=
        matching.streamItem_childTask_producer member listed
      exact ⟨⟨address, payload, some item.occurrence, occurrenceEq, located⟩,
        matching.streamItem_childTask_groupsExact member listed⟩
    have prepared := prior.1.maybeIntegrateWork prior.2.1 prior.2.2.1.tasks prior.2.2.2
      item.work known
    have registered := (prior.2.2.1.integrateStreamItem matching member available).1
    exact ⟨(prepared.pruneEmptyGroups _).startNewWork _ available,
      ((prior.2.1.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _ available,
      registered,
      ((prior.2.2.2.maybeIntegrateWork item.work known).pruneEmptyGroups _).startNewWork
        _ available⟩
  exact (State.preparedStreamItems_preserves property
          ⟨
            disposition,
            accounted.refs,
            accounted.registration,
            accounted.matching
          ⟩
          items available step).1

theorem State.TaskLinkDisposition.streamItems {queue : State} {work : Execution.Work}
    {settled : List Occurrence} {stream : Execution.DeliveryNode}
    {items : List StreamItem} (disposition : queue.TaskLinkDisposition)
    (accounted : queue.PendingAccounting work settled)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : (queue.streamItems stream items available).1.TaskLinkDisposition := by
  rw [queue.streamItems_eq stream items available]
  split
  · exact disposition
  · exact (disposition.prepareItems accounted matching available).drainReadyGroups available

-----------------------------------------------------------------------------------------
-- Generated source prefixes construct complete links for every live task record
-----------------------------------------------------------------------------------------

theorem State.TaskLinkDisposition.handleGraphEvent {queue : State} {work : Execution.Work}
    {settled : List Occurrence} (disposition : queue.TaskLinkDisposition)
    (accounted : queue.PendingAccounting work settled) (event : GraphEvent)
    (matching : event.MatchesWork work) (available : List (Occurrence × Nat) := [])
    : (queue.handleGraphEvent event available).1.TaskLinkDisposition := by
  have cached := disposition.cacheTaskFailures available
  have ledger := accounted.cacheTaskFailures available
  cases event with
  | taskSuccess occurrence result =>
      apply cached.taskSuccess ledger occurrence result (available := available)
      intro task member
      obtain ⟨address, payload, occurrenceEq, known⟩ := matching.childTask_producer member
      exact ⟨⟨address, payload, some occurrence, occurrenceEq, known⟩,
        matching.childTask_groupsExact member⟩
  | taskFailure occurrence errors =>
      exact cached.taskFailure occurrence errors
  | streamItems stream items => exact cached.streamItems ledger matching available
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess]
      split <;> exact cached
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> exact cached

  | groupFailure notice =>
      change ((queue.cacheTaskFailures available).groupFailure notice).1.TaskLinkDisposition
      unfold State.groupFailure
      split
      · exact cached
      · split <;> exact cached

/-- Dispatch retains complete-or-retired links while realizing enqueue effects. -/
theorem State.TaskLinkDisposition.dispatchGraphEvent {queue : State}
    {work : Execution.Work} {settled : List Occurrence}
    (disposition : queue.TaskLinkDisposition)
    (accounted : queue.PendingAccounting work settled) (event : GraphEvent)
    (matching : event.MatchesWork work) (available : List (Occurrence × Nat) := [])
    : (queue.dispatchGraphEvent event available).1.TaskLinkDisposition := by
  exact disposition.handleGraphEvent accounted event matching available

theorem State.TaskLinkDisposition.replayGraphEvents_ofMatching {queue : State}
    {work before} {available : List (Occurrence × Nat)}
    (disposition : queue.TaskLinkDisposition)
    (accounted : queue.PendingAccounting work (GraphEvent.taskSettlements before))
    (generated : ExecutedWork work) (events : List GraphEvent)
    (valid : ValidGraphEvents work (before ++ events))
    : (queue.replayGraphEvents events available).TaskLinkDisposition := by
  induction events generalizing queue before with
  | nil => exact disposition
  | cons event rest ih =>
      have earlier : (before ++ [event]).IsPrefix (before ++ event :: rest) :=
        ⟨rest, by simp⟩
      obtain ⟨_, matching, fresh⟩ := validGraphEvents_last (valid.prefix earlier)
      have next := accounted.dispatchGraphEvent_ofMatching generated
        (GraphEvent.taskSettlements_subsetIdentities before) event matching fresh
        available
      rw [← GraphEvent.taskSettlements_append] at next
      exact ih (disposition.dispatchGraphEvent accounted event matching available) next
        (by simpa only [List.append_assoc, List.singleton_append] using valid)

/-- The strict eventwise specialization of matching disposition replay. -/
theorem State.TaskLinkDisposition.replayGraphEvents {queue : State} {work before}
    {available : List (Occurrence × Nat)}
    (disposition : queue.TaskLinkDisposition)
    (accounted : queue.PendingAccounting work (GraphEvent.taskSettlements before))
    (generated : ExecutedWork work) (events : List GraphEvent)
    (valid : ValidGraphEvents work (before ++ events))
    (_accepted : State.eventsStarted available queue events = true)
    : (queue.replayGraphEvents events available).TaskLinkDisposition :=
  disposition.replayGraphEvents_ofMatching accounted generated events valid

/-- Actual batch handling preserves task disposition with the matching counter ledger. -/
theorem State.TaskLinkDisposition.handleGraphEvents {queue : State} {work before}
    (disposition : queue.TaskLinkDisposition)
    (accounted : queue.PendingAccounting work (GraphEvent.taskSettlements before))
    (generated : ExecutedWork work) (events : List GraphEvent)
    (valid : ValidGraphEvents work (before ++ events))
    (running : queue.terminated = false) (_accepted : queue.acceptsBatch events = true)
    : (queue.handleGraphEvents events).1.TaskLinkDisposition := by
  have replayed := disposition.replayGraphEvents_ofMatching
    (available := GraphEvent.availableFailures events) accounted generated events valid
  obtain ⟨terminal, same⟩ := queue.handleGraphEvents_stateCore events running
  rw [same]
  exact replayed

/-- The actual normalized batch fold retains complete-or-retired catalogue links. -/
theorem State.TaskLinkDisposition.runNormalized {queue : State} {work before}
    (disposition : queue.TaskLinkDisposition)
    (accounted : queue.PendingAccounting work (GraphEvent.taskSettlements before))
    (generated : ExecutedWork work) (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work (before ++ batches.flatten))
    (started : queue.batchesStarted batches = true)
    : (queue.runNormalized batches).1.TaskLinkDisposition := by
  rw [State.runNormalized_replayBatches]
  induction batches generalizing queue before with
  | nil => exact disposition
  | cons batch rest ih =>
      obtain ⟨running, accepted, restStarted⟩ := queue.batchesStarted_cons batch rest started
      have earlier : (before ++ batch).IsPrefix (before ++ (batch :: rest).flatten) :=
        ⟨rest.flatten, by simp [List.append_assoc]⟩
      have batchValid := valid.prefix earlier
      exact ih
        (disposition.handleGraphEvents accounted generated batch batchValid running
          accepted)
        (accounted.handleGraphEvents generated batch batchValid running accepted)
        (by simpa only [List.flatten_cons, List.append_assoc] using valid) restStarted

theorem ExecutedWork.runNormalized_taskLinkDisposition {work : Execution.Work}
    (generated : ExecutedWork work) (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    : ((State.initialize (Work.fromExecution work)).runNormalized
        batches).1.TaskLinkDisposition :=
  (createWorkQueue_taskLinkDisposition (Work.fromExecution work)).runNormalized
    (before := []) (createWorkQueue_pendingAccounting work generated.declarations)
    generated batches valid (by rwa [inputsStarted_eq_batchesStarted] at started)

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
