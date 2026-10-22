import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskOwnerExistence
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskNodeKeys

/-! Generated source handlers preserve live owners for unfinished and buffered records.
The original reference pending ledger supplies structural registration facts; no resource
inventory or desired actual-removal endpoint is assumed.
-/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open WorkQueueSemantics (Occurrence NodeRefs)
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)

theorem State.TaskOwnerFrame.taskSuccess_of_registered {queue : State}
    {work : Execution.Work} (frame : queue.TaskOwnerFrame work)
    (taskGroups : queue.TaskGroupsRegistered) (roots : queue.RootGroupsPresent)
    (occurrence : Occurrence) (result : TaskResult)
    (known : ∀ task ∈ result.work.tasks, TaskMatches work task)
    (available : List (Occurrence × Nat) := [])
    : (queue.taskSuccess occurrence result available).1.TaskOwnerFrame work := by
  cases found : queue.taskNode? occurrence with
  | none => simpa only [State.taskSuccess, found] using frame
  | some node =>
      rw [queue.taskSuccess_eq occurrence result node found available]
      have stored := frame.putExistingTaskNode node (List.mem_of_find?_eq_some found)
        { node with value := some result.value } rfl
      have prepared := stored.maybeIntegrateWork roots taskGroups
        result.work known (some occurrence)
      exact ((prepared.successFold node.task.groups [] {}).startNewWork _ available)
        |>.drainReadyGroups available

theorem State.TaskOwnerFrame.prepareItems_of_registered {queue : State}
    {work : Execution.Work} {stream : Execution.DeliveryNode} {items : List StreamItem}
    (frame : queue.TaskOwnerFrame work) (live : queue.LiveGroupsRegistered)
    (taskGroups : queue.TaskGroupsRegistered) (roots : queue.RootGroupsPresent)
    (source : DeclarationCoverage.Certified [] work)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : (queue.preparedStreamItems items available).TaskOwnerFrame work := by
  let property (current : State) := current.TaskOwnerFrame work ∧ current.LiveGroupsRegistered
    ∧ current.TaskGroupsRegistered ∧ current.RootGroupsPresent
  have step (current : State) (item : StreamItem) (member : item ∈ items)
      (prior : property current) : property (current.integrateStreamItem item available) := by
    have known : ∀ task ∈ item.work.tasks, TaskMatches work task := by
      intro task listed
      obtain ⟨address, payload, occurrenceEq, located⟩ :=
        matching.streamItem_childTask_producer member listed
      exact ⟨⟨address, payload, some item.occurrence, occurrenceEq, located⟩,
        matching.streamItem_childTask_groupsExact member listed⟩
    have prepared := prior.1.maybeIntegrateWork prior.2.2.2 prior.2.2.1 item.work known
    have registered := State.integrateStreamItem_registration_of_certificate prior.2.1 prior.2.2.1 item
      (source.sourceStreamItem matching member current.registeredGroups) available
    exact ⟨(prepared.pruneEmptyGroups _).startNewWork _ available, registered.1, registered.2.1,
      prior.2.2.2.integrateStreamItem_registered prior.2.1 prior.1.keys item available⟩
  exact (State.preparedStreamItems_preserves property
    ⟨frame, live, taskGroups, roots⟩ items available step).1

theorem State.TaskOwnerFrame.streamItems_of_registered {queue : State}
    {work : Execution.Work} {stream : Execution.DeliveryNode} {items : List StreamItem}
    (frame : queue.TaskOwnerFrame work) (live : queue.LiveGroupsRegistered)
    (taskGroups : queue.TaskGroupsRegistered) (roots : queue.RootGroupsPresent)
    (source : DeclarationCoverage.Certified [] work)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : (queue.streamItems stream items available).1.TaskOwnerFrame work := by
  rw [queue.streamItems_eq stream items available]
  split
  · exact frame
  · exact (frame.prepareItems_of_registered live taskGroups roots source matching available)
      |>.drainReadyGroups available

/-- Cache exposure changes task outcomes while preserving live-owner bookkeeping. -/
theorem State.TaskOwnerFrame.cacheTaskFailures {queue : State} {work : Execution.Work}
    (frame : queue.TaskOwnerFrame work) (available : List (Occurrence × Nat))
    : (queue.cacheTaskFailures available).TaskOwnerFrame work :=
  ⟨
    frame.owners.cacheTaskFailures _,
    frame.disposition.cacheTaskFailures _,
    frame.keys.cacheTaskFailures _,
    frame.registered.cacheTaskFailures _,
    frame.matching.cacheTaskFailures _,
    frame.sound.cacheTaskFailures _
  ⟩

/-- Live-owner bookkeeping can be recovered from a common task-cache exposure.
Witness: unique task keys preserve each descriptor under exposure; all remaining frame
fields depend only on unchanged group records, occurrence presence and permanent tasks.
-/
theorem State.TaskOwnerFrame.of_cacheTaskFailures {queue : State} {work : Execution.Work}
    (unique : queue.TaskNodeKeysUnique) (available : List (Occurrence × Nat))
    (frame : (queue.cacheTaskFailures available).TaskOwnerFrame work)
    : queue.TaskOwnerFrame work := by
  let exposed := fun node : TaskNode =>
    { node with
      rejection := available.foldl
        (fun prior (entry : Occurrence × Nat) =>
          if entry.1 == node.task.occurrence then some entry.2 else prior)
        node.rejection }
  have included {node : TaskNode} (member : node ∈ queue.taskNodes)
      : exposed node ∈ (queue.cacheTaskFailures available).taskNodes := by
    rw [unique.cacheTaskFailures_nodes available]
    exact List.mem_map_of_mem member
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro node member
    obtain ⟨ref, owner, present⟩ := frame.owners (exposed node) (included member)
    rw [State.cacheTaskFailures_groupNodes] at present
    exact ⟨ref, owner, present⟩
  · intro task member
    have registered : task ∈ (queue.cacheTaskFailures available).tasks := by
      rwa [State.cacheTaskFailures_tasks]
    rcases frame.disposition task registered with linked | retired
    · exact .inl (by
        simpa only [State.TaskLinkedOn, State.cacheTaskFailures_groupNodes] using linked)
    · refine .inr ⟨?_, ?_⟩
      · have missing := retired.1
        rw [unique.cacheTaskFailures_lookup available] at missing
        cases found : queue.taskNode? task.occurrence with
        | none => rfl
        | some node => simp [found] at missing
      · simpa only [State.TaskMembershipAbsent, State.cacheTaskFailures_groupNodes]
          using retired.2
  · simpa only [State.GroupRefsUnique, State.cacheTaskFailures_groupNodes] using frame.keys
  · intro node member
    have registered := frame.registered (exposed node) (included member)
    rwa [State.cacheTaskFailures_tasks] at registered
  · simpa only [State.RegisteredTasksMatch, State.cacheTaskFailures_tasks] using frame.matching
  · simpa only [State.GroupMembershipSound, State.cacheTaskFailures_groupNodes,
      State.cacheTaskFailures_tasks] using frame.sound

/-- Equal exposed queues share their live-owner bookkeeping frame.
Witness: expose the known frame, use concrete queue equality, then recover the original
queue's unchanged ownership metadata through its unique-key cache projection.
-/
theorem State.TaskOwnerFrame.of_cacheTaskFailures_eq {queue other : State}
    {work : Execution.Work} (unique : queue.TaskNodeKeysUnique)
    (available : List (Occurrence × Nat))
    (same : queue.cacheTaskFailures available = other.cacheTaskFailures available)
    (frame : other.TaskOwnerFrame work)
    : queue.TaskOwnerFrame work := by
  have exposed := frame.cacheTaskFailures available
  rw [← same] at exposed
  exact State.TaskOwnerFrame.of_cacheTaskFailures unique available exposed

/-- Owner preservation needs structural registration, independently of the pending ledger. -/
theorem State.TaskOwnerFrame.handleGraphEvent_of_registered {queue : State}
    {work : Execution.Work} (frame : queue.TaskOwnerFrame work)
    (live : queue.LiveGroupsRegistered) (taskGroups : queue.TaskGroupsRegistered)
    (roots : queue.RootGroupsPresent) (context : queue.RegistrationFrame work)
    (event : GraphEvent)
    (matching : event.MatchesWork work) (available : List (Occurrence × Nat) := [])
    : (queue.handleGraphEvent event available).1.TaskOwnerFrame work := by
  have cached := frame.cacheTaskFailures available
  have registered := queue.cacheTaskFailures_registration live taskGroups available
  have present : (queue.cacheTaskFailures available).RootGroupsPresent := by
    intro ref active
    rw [State.cacheTaskFailures_rootGroups] at active
    rw [State.cacheTaskFailures_groupNodes]
    exact roots ref active
  simp only [State.handleGraphEvent]
  cases event with
  | taskSuccess occurrence result =>
      apply cached.taskSuccess_of_registered registered.2 present occurrence result _ available
      intro task member
      obtain ⟨address, payload, occurrenceEq, known⟩ := matching.childTask_producer member
      exact ⟨⟨address, payload, some occurrence, occurrenceEq, known⟩,
        matching.childTask_groupsExact member⟩
  | taskFailure occurrence errors => exact cached.taskFailure occurrence errors
  | streamItems stream items =>
      exact cached.streamItems_of_registered registered.1 registered.2 present context.source matching available
  | streamSuccess stream =>
      simp only [State.streamSuccess]
      split <;> exact ⟨cached.owners, cached.disposition, cached.keys,
        cached.registered, cached.matching, cached.sound⟩
  | streamFailure stream errors =>
      simp only [State.streamFailure]
      split <;> exact ⟨cached.owners, cached.disposition, cached.keys,
        cached.registered, cached.matching, cached.sound⟩

  | groupFailure failure =>
      simp only [State.groupFailure]
      split
      · exact cached
      · split <;> exact ⟨cached.owners, cached.disposition, cached.keys,
          cached.registered, cached.matching, cached.sound⟩

theorem State.TaskOwnerFrame.taskSuccess {queue : State} {work : Execution.Work}
    {settled : List Occurrence} (frame : queue.TaskOwnerFrame work)
    (accounted : queue.PendingAccounting work settled) (roots : queue.RootGroupsPresent)
    (occurrence : Occurrence) (result : TaskResult)
    (known : ∀ task ∈ result.work.tasks, TaskMatches work task)
    (available : List (Occurrence × Nat) := [])
    : (queue.taskSuccess occurrence result available).1.TaskOwnerFrame work :=
  frame.taskSuccess_of_registered accounted.taskGroups roots occurrence result known
    available

theorem State.TaskOwnerFrame.prepareItems {queue : State} {work : Execution.Work}
    {settled : List Occurrence} {stream : Execution.DeliveryNode}
    {items : List StreamItem} (frame : queue.TaskOwnerFrame work)
    (accounted : queue.PendingAccounting work settled) (roots : queue.RootGroupsPresent)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : (queue.preparedStreamItems items available).TaskOwnerFrame work :=
  frame.prepareItems_of_registered accounted.liveGroups accounted.taskGroups roots
    accounted.registration.source matching available

theorem State.TaskOwnerFrame.streamItems {queue : State} {work : Execution.Work}
    {settled : List Occurrence} {stream : Execution.DeliveryNode}
    {items : List StreamItem} (frame : queue.TaskOwnerFrame work)
    (accounted : queue.PendingAccounting work settled) (roots : queue.RootGroupsPresent)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : (queue.streamItems stream items available).1.TaskOwnerFrame work :=
  frame.streamItems_of_registered accounted.liveGroups accounted.taskGroups roots
    accounted.registration.source matching available

theorem State.TaskOwnerFrame.handleGraphEvent {queue : State} {work : Execution.Work}
    {settled : List Occurrence} (frame : queue.TaskOwnerFrame work)
    (accounted : queue.PendingAccounting work settled) (roots : queue.RootGroupsPresent)
    (event : GraphEvent) (matching : event.MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : (queue.handleGraphEvent event available).1.TaskOwnerFrame work :=
  frame.handleGraphEvent_of_registered accounted.liveGroups accounted.taskGroups roots
    accounted.registration event matching available

private structure OwnerReplayFrame (queue : State) (work : Execution.Work)
    (parents : Nat → NodeRefs)
    : Prop where
  owners : queue.TaskOwnerFrame work
  roots : LiveRootFrame queue work parents
  retired : queue.UncancelledRetiredAncestors work
  context : queue.RegistrationFrame work

private theorem OwnerReplayFrame.handleGraphEvent {queue work parents}
    (frame : OwnerReplayFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (event : GraphEvent) (matching : event.MatchesWork work)
    (available : List (Occurrence × Nat))
    : OwnerReplayFrame (queue.handleGraphEvent event available).1 work parents := by
  have roots := frame.roots.handleGraphEvent frame.retired generated frame.context canonical event
    matching available
  exact ⟨frame.owners.handleGraphEvent_of_registered frame.roots.registered frame.roots.tasks
    frame.roots.present frame.context event matching available, roots.1, roots.2,
    (frame.context.handleGraphEvent event matching available).1⟩

private theorem OwnerReplayFrame.dispatchGraphEvent {queue work parents}
    (frame : OwnerReplayFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (event : GraphEvent) (matching : event.MatchesWork work)
    (available : List (Occurrence × Nat))
    : OwnerReplayFrame (queue.dispatchGraphEvent event available).1 work parents := by
  have next := frame.handleGraphEvent generated canonical event matching available
  exact ⟨⟨next.owners.owners, next.owners.disposition, next.owners.keys,
      next.owners.registered, next.owners.matching, next.owners.sound⟩,
    ⟨next.roots.refs, next.roots.records, next.roots.links, next.roots.registered,
      next.roots.tasks, next.roots.roots, ⟨next.roots.support.contents, next.roots.support.roots⟩,
      next.roots.present⟩, next.retired,
    (frame.context.dispatchGraphEvent event matching available).1⟩

private theorem OwnerReplayFrame.replayGraphEvents {queue work parents}
    (frame : OwnerReplayFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (events : List GraphEvent) (matching : ∀ event ∈ events, event.MatchesWork work)
    (available : List (Occurrence × Nat))
    : OwnerReplayFrame (queue.replayGraphEvents events available) work parents := by
  induction events generalizing queue with
  | nil => exact frame
  | cons event rest ih =>
      exact ih (frame.dispatchGraphEvent generated canonical event
        (matching event List.mem_cons_self) available)
        (fun next member => matching next (List.mem_cons_of_mem _ member))

private theorem OwnerReplayFrame.handleGraphEvents {queue work parents}
    (frame : OwnerReplayFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (events : List GraphEvent) (matching : ∀ event ∈ events, event.MatchesWork work)
    : OwnerReplayFrame (queue.handleGraphEvents events).1 work parents := by
  by_cases ended : queue.terminated = true
  · simpa only [State.handleGraphEvents, ended, ite_true] using frame
  · have running : queue.terminated = false := Bool.eq_false_iff.mpr ended
    obtain ⟨terminal, same⟩ := queue.handleGraphEvents_stateCore events running
    have replayed := frame.replayGraphEvents generated canonical events matching
      (GraphEvent.availableFailures events)
    rw [same]
    exact ⟨⟨replayed.owners.owners, replayed.owners.disposition, replayed.owners.keys,
      replayed.owners.registered, replayed.owners.matching, replayed.owners.sound⟩,
      ⟨replayed.roots.refs, replayed.roots.records, replayed.roots.links,
        replayed.roots.registered, replayed.roots.tasks, replayed.roots.roots,
        ⟨replayed.roots.support.contents, replayed.roots.support.roots⟩,
        replayed.roots.present⟩, replayed.retired, replayed.context.withTerminated terminal⟩

/-- Matching generated FIFO replay retains owner metadata under any supplied snapshot.
These structural frames do not require a source acceptance or failure-provenance premise.
-/
theorem ExecutedWork.replayGraphEvents_taskOwnerFrame_of_matching {work : Execution.Work}
    (generated : ExecutedWork work) (events : List GraphEvent)
    (matching : ∀ event ∈ events, event.MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : ((State.initialize (Work.fromExecution work)).replayGraphEvents
        events available).TaskOwnerFrame
        work := by
  obtain ⟨parents, canonical, roots, retired⟩ := generated.runNormalized_liveRootFrame [] (by simp)
  have initial : OwnerReplayFrame (State.initialize (Work.fromExecution work)) work parents :=
    ⟨createWorkQueue_taskOwnerFrame work, roots, retired,
      State.initialize_registrationFrame generated.declarations⟩
  exact (initial.replayGraphEvents generated canonical events matching available).owners

/-- Matching generated replay supplies owner existence without requiring accepted starts.
The compatibility argument is retained for existing eventwise consumers.
-/
theorem ExecutedWork.replayGraphEvents_taskOwnerFrame {work : Execution.Work}
    (generated : ExecutedWork work) (events : List GraphEvent)
    (valid : ValidGraphEvents work events)
    (_accepted : (State.initialize (Work.fromExecution work)).acceptsBatch events = true)
    : ((State.initialize (Work.fromExecution work)).replayGraphEvents
        events).TaskOwnerFrame
        work :=
  generated.replayGraphEvents_taskOwnerFrame_of_matching events
    (fun _ => valid.eachMatches)

/-- Owner existence and complete contributor links hold through actual normalized batches.
Matching and the independently derived live-root frame suffice; no flattened-state or
source-acceptance bridge enters the proof.
-/
theorem ExecutedWork.runNormalized_taskOwnerFrame_of_matching {work : Execution.Work}
    (generated : ExecutedWork work) (batches : List (List GraphEvent))
    (matching : ∀ event ∈ batches.flatten, event.MatchesWork work)
    : ((State.initialize (Work.fromExecution work)).runNormalized
        batches).1.TaskOwnerFrame
        work := by
  obtain ⟨parents, canonical, roots, retired⟩ := generated.runNormalized_liveRootFrame [] (by simp)
  have initial : OwnerReplayFrame (State.initialize (Work.fromExecution work)) work parents :=
    ⟨createWorkQueue_taskOwnerFrame work, roots, retired,
      State.initialize_registrationFrame generated.declarations⟩
  have loop (more : List (List GraphEvent)) (included : more.Subset batches)
      (current : State) (frame : OwnerReplayFrame current work parents)
      : OwnerReplayFrame
          (more.foldl (fun next batch => (next.handleGraphEvents batch).1) current)
          work parents := by
    induction more generalizing current with
    | nil => exact frame
    | cons batch rest ih =>
        exact ih (fun _ member => included (List.mem_cons_of_mem _ member)) _
          (frame.handleGraphEvents generated canonical batch (fun _ member =>
            matching _ (List.mem_flatten.mpr ⟨batch, included List.mem_cons_self, member⟩)))
  rw [State.runNormalized_stateFold]
  exact (loop batches (List.Subset.refl _) _ initial).owners

theorem ExecutedWork.runNormalized_taskOwnerFrame {work : Execution.Work}
    (generated : ExecutedWork work) (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work batches.flatten)
    (_started : inputsStarted work batches = true)
    : ((State.initialize (Work.fromExecution work)).runNormalized
        batches).1.TaskOwnerFrame
        work :=
  generated.runNormalized_taskOwnerFrame_of_matching batches
    (fun _ member => valid.eachMatches member)

/-- Actual batch prefixes followed by a fixed-snapshot FIFO prefix supply structural frames.
Witness: retain the normalized boundary's live roots and owner metadata, then replay the
actual FIFO handlers under their common availability snapshot. Matching alone suffices.
-/
theorem ExecutedWork.batchPrefix_structuralFrames {work : Execution.Work}
    (generated : ExecutedWork work) (batches : List (List GraphEvent))
    (events : List GraphEvent)
    (matchingBatches : ∀ event ∈ batches.flatten, event.MatchesWork work)
    (matchingEvents : ∀ event ∈ events, event.MatchesWork work)
    (available : List (Occurrence × Nat))
    : let queue :=
        ((State.initialize (Work.fromExecution work)).replayBatches
          batches).replayGraphEvents
          events available
      ∃ parents,
        (∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
        ∧ queue.TaskOwnerFrame work
        ∧ LiveRootFrame queue work parents
        ∧ queue.UncancelledRetiredAncestors work := by
  obtain ⟨parents, canonical, roots, retired⟩ :=
    generated.runNormalized_liveRootFrame batches matchingBatches
  have owners := generated.runNormalized_taskOwnerFrame_of_matching batches matchingBatches
  have context := ((State.initialize_registrationFrame generated.declarations).runNormalized
    batches (fun _ batch _ event => matchingBatches _
      (List.mem_flatten.mpr ⟨_, batch, event⟩))).1
  rw [State.runNormalized_replayBatches] at roots retired owners context
  have frame : OwnerReplayFrame
      ((State.initialize (Work.fromExecution work)).replayBatches batches) work parents :=
    ⟨owners, roots, retired, context⟩
  have result := frame.replayGraphEvents generated canonical events matchingEvents available
  exact ⟨parents, canonical, result.owners, result.roots, result.retired⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
