import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartedTaskAnnouncements

/-! Historical task-start notices through complete source handlers and finite replay. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Package existing registration facts while composing executable handler stages
-----------------------------------------------------------------------------------------

/-- Local proof bookkeeping for notice history `seen` and original work `work`.
Every field is an existing queue invariant; this is not an additional source premise.
-/
private structure AnnouncementFacts (work : Execution.Work) (seen : NodeRefs)
    (queue : State)
    : Prop where
  known : queue.StartedTasksAnnounced seen
  roots : queue.rootGroups.Subset seen
  sound : queue.GroupMembershipSound
  registered : queue.StartedTasksRegistered
  matching : queue.RegisteredTasksMatch work

/-- Child integration preserves existing notices because it activates no new roots.
Witness: registration guards justify any immediate task start using an old root.
-/
private theorem AnnouncementFacts.integrate {work seen queue}
    (facts : AnnouncementFacts work seen queue) (newWork : Work)
    (located : ∀ task ∈ newWork.tasks, TaskMatches work task)
    (parentTask : Option Occurrence := none)
    : AnnouncementFacts work seen (queue.maybeIntegrateWork newWork parentTask).1 where
  known := facts.known.maybeIntegrateWork facts.roots newWork parentTask
  roots := by rw [State.maybeIntegrateWork_rootGroups]; exact facts.roots
  sound := facts.sound.maybeIntegrateWork newWork parentTask
  registered := facts.registered.maybeIntegrateWork newWork parentTask
  matching := facts.matching.maybeIntegrateWork newWork located parentTask

/-- Empty-shell pruning changes neither root refs nor started task definitions.
Witness: existing pruning preservation for each registration and notice fact.
-/
private theorem AnnouncementFacts.prune {work seen queue}
    (facts : AnnouncementFacts work seen queue) (groups : List Execution.DeliveryNode)
    : AnnouncementFacts work seen (queue.pruneEmptyGroups groups).1 where
  known := facts.known.pruneEmptyGroups groups
  roots := by rw [State.pruneEmptyGroups_rootGroups]; exact facts.roots
  sound := facts.sound.pruneEmptyGroups groups
  registered := facts.registered.pruneEmptyGroups groups
  matching := facts.matching.pruneEmptyGroups groups

/-- Activating released work extends the historical refs by its actual group notices.
Witness: sound task activation and the exact appended root-ref equation.
-/
private theorem AnnouncementFacts.start {work seen queue}
    (facts : AnnouncementFacts work seen queue) (released : NewWork)
    : AnnouncementFacts work (seen ++ released.newGroups.map Execution.DeliveryNode.ref)
        (queue.startNewWork released) where
  known := facts.known.startNewWork facts.sound facts.registered facts.matching released
  roots := by
    rw [(queue.startNewWork_groupCore released).2.2]
    intro ref member
    exact (List.mem_append.mp member).elim
      (fun old => List.mem_append_left _ (facts.roots old))
      (fun fresh => List.mem_append_right _ fresh)
  sound := facts.sound.startNewWork released
  registered := facts.registered.startNewWork released
  matching := facts.matching.startNewWork released

/-- Counter decrements preserve task memberships and every historical notice witness.
Witness: only the selected group's pending count changes.
-/
private theorem AnnouncementFacts.decrement {work seen queue ref node}
    (facts : AnnouncementFacts work seen queue) (found : queue.groupNode? ref = some node)
    : AnnouncementFacts work seen
        (queue.putGroupNode { node with pending := node.pending - 1 }) where
  known := facts.known
  roots := facts.roots
  sound := facts.sound.putGroupNode _ (facts.sound node (List.mem_of_find?_eq_some found))
  registered := facts.registered.putGroupNode _
  matching := facts.matching.putGroupNode _

/-- Successful flushing retains only old started nodes and can only shrink active roots.
Witness: existing task selection and group-flush registration preservation.
-/
private theorem AnnouncementFacts.flush {work seen queue}
    (facts : AnnouncementFacts work seen queue) (node : GroupNode)
    : AnnouncementFacts work seen (queue.finishGroupSuccess node).1 where
  known := facts.known.finishGroupSuccess node
  roots := (queue.finishGroupSuccess_rootsSubset node).trans facts.roots
  sound := facts.sound.finishGroupSuccess node
  registered := facts.registered.finishGroupSuccess node
  matching := facts.matching.finishGroupSuccess node

/-- Release-time draining extends history by exactly its emitted group notices.
Witness: start witnesses compose with the independently proved root-notice accounting.
-/
private theorem AnnouncementFacts.drain {work seen queue}
    (facts : AnnouncementFacts work seen queue)
    : AnnouncementFacts work (seen ++ queue.drainReadyGroups.2.flatMap rawGroupNoticeRefs)
        queue.drainReadyGroups.1 where
  known := facts.known.drainReadyGroups facts.sound facts.registered facts.matching
  roots := by
    intro ref member
    exact (List.mem_append.mp (queue.drainReadyGroups_groupFailureNotices.1 member)).elim
      (fun old => List.mem_append_left _ (facts.roots old))
      (fun fresh => List.mem_append_right _ fresh)
  sound := facts.sound.drainReadyGroups
  registered := facts.registered.drainReadyGroups
  matching := facts.matching.drainReadyGroups

-----------------------------------------------------------------------------------------
-- Successful task and item handlers include their real release and drain stages
-----------------------------------------------------------------------------------------

/-- Task success preserves historical owners through integration, shared flushes, and drain.
Witness: the actual single-pass success fold, with its emitted/released notice equality.
-/
private theorem AnnouncementFacts.taskSuccess {work seen queue}
    (facts : AnnouncementFacts work seen queue) (occurrence : Occurrence)
    (result : TaskResult) (located : ∀ task ∈ result.work.tasks, TaskMatches work task)
    : (queue.taskSuccess occurrence result).1.StartedTasksAnnounced
        (seen ++ (queue.taskSuccess occurrence result).2.flatMap rawGroupNoticeRefs) := by
  cases found : queue.taskNode? occurrence with
  | none => simpa [State.taskSuccess, found] using facts.known
  | some node =>
      rw [queue.taskSuccess_eq occurrence result node found]
      split
      · simpa using facts.known.removeTask occurrence
      · let stored := queue.putTaskNode { node with value := some result.value }
        have storedFacts : AnnouncementFacts work seen stored := {
          known := facts.known.putTaskNode _
            (facts.known node (List.mem_of_find?_eq_some found))
          roots := facts.roots
          sound := facts.sound
          registered := facts.registered.putTaskNode _
            (facts.registered node (List.mem_of_find?_eq_some found))
          matching := facts.matching }
        let integrated := (stored.maybeIntegrateWork result.work (some occurrence)).1
        have integratedFacts : AnnouncementFacts work seen integrated :=
          storedFacts.integrate result.work located (some occurrence)
        have loop (groups : List Execution.DeliveryNode)
            (acc : State × List WorkQueueEvent × NewWork)
            (prior : AnnouncementFacts work seen acc.1)
            (notices : acc.2.2.newGroups.map Execution.DeliveryNode.ref
              = acc.2.1.flatMap rawGroupNoticeRefs)
            : AnnouncementFacts work seen (groups.foldl successGroupStep acc).1
              ∧ (groups.foldl successGroupStep acc).2.2.newGroups.map Execution.DeliveryNode.ref
                = (groups.foldl successGroupStep acc).2.1.flatMap rawGroupNoticeRefs := by
          induction groups generalizing acc with
          | nil => exact ⟨prior, notices⟩
          | cons group rest ih =>
              apply ih
              · dsimp only [successGroupStep]
                split
                · exact prior
                · rename_i selected foundGroup
                  have decremented := prior.decrement foundGroup
                  split
                  · exact decremented.flush _
                  · exact decremented
              · dsimp only [successGroupStep]
                split
                · exact notices
                · split
                  · simp only [List.map_append, List.flatMap_append, notices,
                      State.finishGroupSuccess_groupNotices]
                  · exact notices
        let folded := node.task.groups.foldl successGroupStep (integrated, [], {})
        obtain ⟨foldedFacts, notices⟩ := loop node.task.groups (integrated, [], {})
          integratedFacts rfl
        have finished := (foldedFacts.start folded.2.2).drain
        rw [notices] at finished
        simpa only [List.flatMap_append, List.append_assoc] using finished.known

/-- Stream-item handling records each activated task's owner in the actual item carrier.
Witness: itemwise integration and activation accumulate the carrier's exact group list;
the subsequent ready-group drain retains that history and contributes its own notices.
-/
private theorem AnnouncementFacts.streamItems {work seen queue}
    (facts : AnnouncementFacts work seen queue) (stream : Execution.DeliveryNode)
    (items : List StreamItem)
    (located : ∀ item ∈ items, ∀ task ∈ item.work.tasks, TaskMatches work task)
    : (queue.streamItems stream items).1.StartedTasksAnnounced
        (seen ++ (queue.streamItems stream items).2.flatMap rawGroupNoticeRefs) := by
  let step (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue) (item : StreamItem) :=
    let integrated := acc.1.maybeIntegrateWork item.work
    let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
    (pruned.1.startNewWork { integrated.2 with newGroups := pruned.2 },
      acc.2.1 ++ pruned.2, acc.2.2.1 ++ integrated.2.newStreams,
      acc.2.2.2 ++ [item.value])
  have loop (more : List StreamItem) (subset : more.Subset items)
      (acc : State × List Execution.DeliveryNode
        × List Execution.DeliveryNode × List StreamItemValue)
      (prior : AnnouncementFacts work (seen ++ acc.2.1.map Execution.DeliveryNode.ref) acc.1)
      : AnnouncementFacts work
          (seen ++ (more.foldl step acc).2.1.map Execution.DeliveryNode.ref)
          (more.foldl step acc).1 := by
    induction more generalizing acc with
    | nil => exact prior
    | cons item rest ih =>
        apply ih (fun _ member => subset (List.mem_cons_of_mem _ member))
        have integrated := prior.integrate item.work (located item (subset (by simp)))
        have pruned := integrated.prune (acc.1.maybeIntegrateWork item.work).2.newGroups
        have started := pruned.start
          { (acc.1.maybeIntegrateWork item.work).2 with newGroups :=
            ((acc.1.maybeIntegrateWork item.work).1.pruneEmptyGroups
              (acc.1.maybeIntegrateWork item.work).2.newGroups).2 }
        simpa only [step, List.map_append, List.append_assoc] using started
  unfold State.streamItems
  split
  · simpa using facts.known
  · let folded := items.foldl step (queue, [], [], [])
    have foldedFacts := loop items (List.Subset.refl _) (queue, [], [], [])
      (by simpa using facts)
    simpa only [List.flatMap_cons, rawGroupNoticeRefs, List.append_assoc]
      using foldedFacts.drain.known

-----------------------------------------------------------------------------------------
-- Every matching handler and every finite source prefix preserve historical owners
-----------------------------------------------------------------------------------------

/-- A matching graph-event handler preserves task starts' prior contributing notices.
Witness: the success/item proofs above; failures and stream closure only retain old tasks.
All registration premises are internal invariants, not strengthened event-source laws.
-/
theorem State.StartedTasksAnnounced.handleGraphEvent {queue : State}
    {work : Execution.Work} {seen : NodeRefs} (known : queue.StartedTasksAnnounced seen)
    (roots : queue.rootGroups.Subset seen) (sound : queue.GroupMembershipSound)
    (registered : queue.StartedTasksRegistered)
    (matching : queue.RegisteredTasksMatch work) (event : GraphEvent)
    (eventMatch : event.MatchesWork work)
    : (queue.handleGraphEvent event).1.StartedTasksAnnounced
        (seen ++ (queue.handleGraphEvent event).2.flatMap rawGroupNoticeRefs) := by
  have facts : AnnouncementFacts work seen queue := ⟨known, roots, sound, registered, matching⟩
  cases event with
  | taskSuccess occurrence result =>
      apply facts.taskSuccess occurrence result
      intro task member
      obtain ⟨address, payload, occurrenceEq, located⟩ := eventMatch.childTask_producer member
      exact ⟨⟨address, payload, some occurrence, occurrenceEq, located⟩,
        eventMatch.childTask_groupsExact member⟩
  | taskFailure occurrence errors =>
      exact (known.taskFailure occurrence errors).mono (List.subset_append_left _ _)
  | streamItems stream items =>
      apply facts.streamItems stream items
      intro item member task taskMember
      obtain ⟨address, payload, occurrenceEq, located⟩ :=
        eventMatch.streamItem_childTask_producer member taskMember
      exact ⟨⟨address, payload, some item.occurrence, occurrenceEq, located⟩,
        eventMatch.streamItem_childTask_groupsExact member taskMember⟩
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess]
      split <;> simpa [rawGroupNoticeRefs, State.StartedTasksAnnounced] using known
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> simpa [rawGroupNoticeRefs, State.StartedTasksAnnounced] using known

/-- All local bookkeeping facts survive a matching handler with its exact notice list.
Witness: historical task notices above plus independently checked root and registry laws.
-/
private theorem AnnouncementFacts.handleGraphEvent {work seen queue}
    (facts : AnnouncementFacts work seen queue) (event : GraphEvent)
    (eventMatch : event.MatchesWork work)
    : AnnouncementFacts work
        (seen ++ (queue.handleGraphEvent event).2.flatMap rawGroupNoticeRefs)
        (queue.handleGraphEvent event).1 where
  known :=
    facts.known.handleGraphEvent facts.roots facts.sound facts.registered facts.matching
      event eventMatch
  roots := by
    intro ref member
    exact (List.mem_append.mp ((queue.handleGraphEvent_groupFailureNotices event).1 member)).elim
      (fun old => List.mem_append_left _ (facts.roots old))
      (fun fresh => List.mem_append_right _ fresh)
  sound := facts.sound.handleGraphEvent event
  registered := facts.registered.handleGraphEvent event
  matching := facts.matching.handleGraphEvent event eventMatch

/-- Finite source replay composes task-start notice evidence across all matching handlers.
Witness: list induction with the actual output concatenation and final queue state.
-/
private theorem AnnouncementFacts.rawEventReplay {work seen queue}
    (facts : AnnouncementFacts work seen queue) (events : List GraphEvent)
    (allMatch : ∀ event ∈ events, event.MatchesWork work)
    : AnnouncementFacts work
        (seen ++ (queue.rawEventReplay events).2.flatMap rawGroupNoticeRefs)
        (queue.rawEventReplay events).1 := by
  induction events generalizing queue seen with
  | nil => simpa [State.rawEventReplay] using facts
  | cons event rest ih =>
      rw [State.rawEventReplay_cons]
      have first := facts.handleGraphEvent event (allMatch event (by simp))
      simpa only [List.flatMap_append, List.append_assoc]
        using ih first
          (fun later member => allMatch later (List.mem_cons_of_mem _ member))

/-- Initialization supplies all local announcement and exact registration facts.
Witness: initial start ownership and the established queue initialization theorems.
-/
private theorem initialAnnouncementFacts (work : Execution.Work)
    : let queue := State.initialize (Work.fromExecution work)
      AnnouncementFacts work (queue.initialGroups.map Execution.DeliveryNode.ref)
        queue where
  known := createWorkQueue_startedTasksAnnounced work
  roots := by rw [createWorkQueue_rootGroups]; exact List.Subset.refl _
  sound := createWorkQueue_groupMembershipSound _
  registered := createWorkQueue_startedTasksRegistered _
  matching := createWorkQueue_fromSpec_registeredTasksMatch work

/-- Every surviving started task has an initial or earlier carrier notice after valid replay.
Witness: initialization followed by matching-handler composition, with no output-admission,
generated-work, start-check, failure-licensing, or cancellation-safety assumption.
-/
theorem createWorkQueue_rawEventReplay_startedTasksAnnounced {work : Execution.Work}
    {events : List GraphEvent} (valid : ValidGraphEvents work events)
    : let queue := State.initialize (Work.fromExecution work)
      (queue.rawEventReplay events).1.StartedTasksAnnounced
        (queue.initialGroups.map Execution.DeliveryNode.ref
          ++ (queue.rawEventReplay events).2.flatMap rawGroupNoticeRefs) :=
  ((initialAnnouncementFacts work).rawEventReplay events
    (fun _ => valid.eachMatches)).known

/-- A live source-task lookup has a structurally contributing, previously announced owner.
Witness: exact registered provenance identifies the spec owners; historical start evidence
supplies one owner's ref, even if that owner no longer has an active queue node.
-/
theorem createWorkQueue_replayGraphEvents_announcedOwner {work : Execution.Work}
    {events : List GraphEvent} (valid : ValidGraphEvents work events)
    {occurrence : Occurrence} {node : TaskNode}
    (found
      : ((State.initialize (Work.fromExecution work)).replayGraphEvents events).taskNode?
          occurrence
        = some node)
    : ∃ owners owner,
        TaskHasOwners work occurrence owners
        ∧ owner ∈ owners
        ∧ owner
          ∈ (State.initialize (Work.fromExecution work)).initialGroups.map
              Execution.DeliveryNode.ref
            ++ ((State.initialize (Work.fromExecution work)).rawEventReplay
                  events).2.flatMap
                rawGroupNoticeRefs := by
  let queue := State.initialize (Work.fromExecution work)
  have facts := (initialAnnouncementFacts work).rawEventReplay events
    (fun _ => valid.eachMatches)
  have foundRaw : (queue.rawEventReplay events).1.taskNode? occurrence = some node := by
    rwa [State.rawEventReplay_state]
  obtain ⟨member, occurrenceEq⟩ := State.taskNode?_some foundRaw
  obtain ⟨owner, contributes, announced⟩ := facts.known node member
  obtain ⟨⟨_, payload, producer, _, located⟩, _⟩ :=
    facts.matching node.task (facts.registered node member)
  exact ⟨node.task.groups.map Execution.DeliveryNode.ref, owner.ref,
    ⟨producer, payload, occurrenceEq ▸ located⟩,
    List.mem_map.mpr ⟨owner, contributes, rfl⟩, announced⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
