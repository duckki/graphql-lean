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
structure AnnouncementFacts (work : Execution.Work) (seen : NodeRefs) (queue : State)
    : Prop where
  known : queue.StartedTasksAnnounced seen
  roots : queue.rootGroups.Subset seen
  sound : queue.GroupMembershipSound
  registered : queue.StartedTasksRegistered
  matching : queue.RegisteredTasksMatch work

/-- Computation-cache exposure preserves historical notices and group/registry metadata. -/
private theorem AnnouncementFacts.cacheTaskFailures {work seen queue}
    (facts : AnnouncementFacts work seen queue) (available : List (Occurrence × Nat))
    : AnnouncementFacts work seen (queue.cacheTaskFailures available) where
  known := facts.known.cacheTaskFailures available
  roots := by rw [State.cacheTaskFailures_rootGroups]; exact facts.roots
  sound := facts.sound.cacheTaskFailures available
  registered := facts.registered.cacheTaskFailures available
  matching := facts.matching.cacheTaskFailures available

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
    (available : List (Occurrence × Nat) := [])
    : AnnouncementFacts work (seen ++ released.newGroups.map Execution.DeliveryNode.ref)
        (queue.startNewWork released available).1 where
  known :=
    facts.known.startNewWork facts.sound facts.registered facts.matching released
      available
  roots := by
    intro ref member
    have old := (queue.startNewWork_groupCore released available).2.2.subset member
    exact (List.mem_append.mp old).elim
      (fun old => List.mem_append_left _ (facts.roots old))
      (fun fresh => List.mem_append_right _ fresh)
  sound := facts.sound.startNewWork released available
  registered := facts.registered.startNewWork released available
  matching := facts.matching.startNewWork released available

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
    (available : List (Occurrence × Nat) := [])
    : AnnouncementFacts work
        (seen ++ (queue.drainReadyGroups available).2.1.flatMap rawGroupNoticeRefs)
        (queue.drainReadyGroups available).1 where
  known :=
    facts.known.drainReadyGroups facts.sound facts.registered facts.matching available
  roots := by
    intro ref member
    exact (List.mem_append.mp
      ((queue.drainReadyGroups_groupFailureNotices available).1.1 member)).elim
      (fun old => List.mem_append_left _ (facts.roots old))
      (fun fresh => List.mem_append_right _ fresh)
  sound := facts.sound.drainReadyGroups available
  registered := facts.registered.drainReadyGroups available
  matching := facts.matching.drainReadyGroups available

-----------------------------------------------------------------------------------------
-- Successful task and item handlers include their real release and drain stages
-----------------------------------------------------------------------------------------

/-- Task success preserves historical owners through integration, shared flushes, and drain.
Witness: the actual single-pass success fold, with its emitted/released notice equality.
-/
private theorem AnnouncementFacts.taskSuccess {work seen queue}
    (facts : AnnouncementFacts work seen queue) (occurrence : Occurrence)
    (result : TaskResult) (located : ∀ task ∈ result.work.tasks, TaskMatches work task)
    (available : List (Occurrence × Nat) := [])
    : (queue.taskSuccess occurrence result available).1.StartedTasksAnnounced
        (seen
          ++ (queue.taskSuccess occurrence result available).2.1.flatMap
              rawGroupNoticeRefs) := by
  cases found : queue.taskNode? occurrence with
  | none => simpa [State.taskSuccess, found] using facts.known
  | some node =>
      rw [queue.taskSuccess_eq occurrence result node found available]
      let stored := queue.putTaskNode { node with value := some result.value }
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
            obtain ⟨current, events, released⟩ := acc
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
      have finished := (foldedFacts.start folded.2.2 available).drain available
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
    (available : List (Occurrence × Nat) := [])
    : (queue.streamItems stream items available).1.StartedTasksAnnounced
        (seen
          ++ (queue.streamItems stream items available).2.1.flatMap
              rawGroupNoticeRefs) := by
  let step (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue × List GroupFailureEvent)
      (item : StreamItem) :=
    let integrated := acc.1.maybeIntegrateWork item.work
    let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
    let (started, queued) :=
      pruned.1.startNewWork { integrated.2 with newGroups := pruned.2 } available
    (started, acc.2.1 ++ pruned.2, acc.2.2.1 ++ integrated.2.newStreams,
      acc.2.2.2.1 ++ [item.value], acc.2.2.2.2 ++ queued)
  have loop (more : List StreamItem) (subset : more.Subset items)
      (acc : State × List Execution.DeliveryNode
        × List Execution.DeliveryNode × List StreamItemValue × List GroupFailureEvent)
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
              (acc.1.maybeIntegrateWork item.work).2.newGroups).2 } available
        simpa only [step, List.map_append, List.append_assoc] using started
  unfold State.streamItems
  split
  · simpa using facts.known
  · let folded := items.foldl step (queue, [], [], [], [])
    have foldedFacts := loop items (List.Subset.refl _) (queue, [], [], [], [])
      (by simpa using facts)
    simpa only [List.flatMap_cons, rawGroupNoticeRefs, List.append_assoc]
      using (foldedFacts.drain available).known

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
    (eventMatch : event.MatchesWork work) (available : List (Occurrence × Nat) := [])
    : (queue.handleGraphEvent event available).1.StartedTasksAnnounced
        (seen
          ++ (queue.handleGraphEvent event available).2.1.flatMap
              rawGroupNoticeRefs) := by
  have original : AnnouncementFacts work seen queue :=
    ⟨known, roots, sound, registered, matching⟩
  have facts := original.cacheTaskFailures available
  cases event with
  | taskSuccess occurrence result =>
      apply facts.taskSuccess occurrence result (available := available)
      intro task member
      obtain ⟨address, payload, occurrenceEq, located⟩ := eventMatch.childTask_producer member
      exact ⟨⟨address, payload, some occurrence, occurrenceEq, located⟩,
        eventMatch.childTask_groupsExact member⟩
  | taskFailure occurrence errors =>
      exact (facts.known.taskFailure occurrence errors).mono (List.subset_append_left _ _)
  | streamItems stream items =>
      apply facts.streamItems stream items (available := available)
      intro item member task taskMember
      obtain ⟨address, payload, occurrenceEq, located⟩ :=
        eventMatch.streamItem_childTask_producer member taskMember
      exact ⟨⟨address, payload, some item.occurrence, occurrenceEq, located⟩,
        eventMatch.streamItem_childTask_groupsExact member taskMember⟩
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess]
      split <;> simpa [rawGroupNoticeRefs, State.StartedTasksAnnounced] using facts.known
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> simpa [rawGroupNoticeRefs, State.StartedTasksAnnounced] using facts.known

  | groupFailure notice =>
      simp only [State.handleGraphEvent, State.groupFailure]
      split
      · simpa [State.StartedTasksAnnounced] using facts.known
      · split <;> simpa [rawGroupNoticeRefs, State.StartedTasksAnnounced] using facts.known

/-- All local bookkeeping facts survive a matching handler with its exact notice list.
Witness: historical task notices above plus independently checked root and registry laws.
-/
private theorem AnnouncementFacts.handleGraphEvent {work seen queue}
    (facts : AnnouncementFacts work seen queue) (event : GraphEvent)
    (eventMatch : event.MatchesWork work) (available : List (Occurrence × Nat) := [])
    : AnnouncementFacts work
        (seen ++ (queue.handleGraphEvent event available).2.1.flatMap rawGroupNoticeRefs)
        (queue.handleGraphEvent event available).1 where
  known :=
    facts.known.handleGraphEvent facts.roots facts.sound facts.registered facts.matching
      event eventMatch available
  roots := by
    intro ref member
    exact (List.mem_append.mp
      (queue.handleGraphEvent_groupRoots_subset event available member)).elim
      (fun old => List.mem_append_left _ (facts.roots old))
      (fun fresh => List.mem_append_right _ fresh)
  sound := facts.sound.handleGraphEvent event available
  registered := facts.registered.handleGraphEvent event available
  matching := facts.matching.handleGraphEvent event eventMatch available

/-- Enqueue effects preserve the actual task-start announcement evidence. -/
private theorem AnnouncementFacts.dispatchGraphEvent {work seen queue}
    (facts : AnnouncementFacts work seen queue) (event : GraphEvent)
    (eventMatch : event.MatchesWork work) (available : List (Occurrence × Nat) := [])
    : AnnouncementFacts work
        (seen ++ (queue.dispatchGraphEvent event available).2.flatMap rawGroupNoticeRefs)
        (queue.dispatchGraphEvent event available).1 := by
  have next := facts.handleGraphEvent event eventMatch available
  exact ⟨next.known, next.roots, next.sound, next.registered, next.matching⟩

/-- Finite source replay composes task-start notice evidence across all matching handlers.
Witness: list induction with the actual output concatenation and final queue state.
-/
theorem AnnouncementFacts.rawEventReplay {work seen queue}
    (facts : AnnouncementFacts work seen queue) (events : List GraphEvent)
    (allMatch : ∀ event ∈ events, event.MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : AnnouncementFacts work
        (seen ++ (queue.rawEventReplay events available).2.flatMap rawGroupNoticeRefs)
        (queue.rawEventReplay events available).1 := by
  induction events generalizing queue seen with
  | nil => simpa [State.rawEventReplay] using facts
  | cons event rest ih =>
      rw [State.rawEventReplay_cons _ _ _ available]
      have first := facts.dispatchGraphEvent event (allMatch event (by simp)) available
      simpa only [List.flatMap_append, List.append_assoc]
        using ih first
          (fun later member => allMatch later (List.mem_cons_of_mem _ member))

/-- Actual batching retains historical notices while forwarding startup failures. -/
theorem AnnouncementFacts.handleGraphEvents {work seen queue}
    (facts : AnnouncementFacts work seen queue) (events : List GraphEvent)
    (allMatch : ∀ event ∈ events, event.MatchesWork work)
    : AnnouncementFacts work
        (seen ++ (queue.handleGraphEvents events).2.flatMap rawGroupNoticeRefs)
        (queue.handleGraphEvents events).1 := by
  have immediate := facts.rawEventReplay events allMatch (GraphEvent.availableFailures events)
  rw [queue.handleGraphEvents_eq_rawEventReplay events]
  split
  · simpa only [List.flatMap_nil, List.append_nil] using facts
  · dsimp only
    split
    · simpa only [List.flatMap_append, List.flatMap_singleton, rawGroupNoticeRefs,
        List.append_nil]
        using (show AnnouncementFacts work
                      (seen
                        ++ (queue.rawEventReplay events
                              (GraphEvent.availableFailures events)).2.flatMap
                            rawGroupNoticeRefs)
                      {
                        (queue.rawEventReplay events
                            (GraphEvent.availableFailures events)).1 with
                          terminated := true
                      } from ⟨
                immediate.known,
                immediate.roots,
                immediate.sound,
                immediate.registered,
                immediate.matching
              ⟩)
    · simpa only [List.flatMap_append, List.append_nil] using immediate

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

/-- The actual normalized runner retains all notice and registry evidence jointly. -/
private theorem initial_runNormalized_announcementFacts {work : Execution.Work}
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    : let queue := State.initialize (Work.fromExecution work)
      AnnouncementFacts work
        (queue.initialGroups.map Execution.DeliveryNode.ref
          ++ (queue.runNormalized batches).2.flatten.flatMap groupNoticeRefs)
        (queue.runNormalized batches).1 := by
  let initial :=
    (State.initialize (Work.fromExecution work)).initialGroups.map Execution.DeliveryNode.ref
  have loop (more : List (List GraphEvent)) (acc : NormalizedAcc)
      (facts : AnnouncementFacts work (initial ++ acc.2.2.flatten.flatMap groupNoticeRefs) acc.1)
      (allMatch : ∀ event ∈ more.flatten, event.MatchesWork work)
      : AnnouncementFacts work
          (initial ++ (more.foldl normalizedStep acc).2.2.flatten.flatMap groupNoticeRefs)
          (more.foldl normalizedStep acc).1 := by
    induction more generalizing acc with
    | nil => exact facts
    | cons batch rest ih =>
        apply ih
        · rw [normalizedStep_queue, normalizedStep_flatten, List.flatMap_append,
            IncrementalPublisher.normalizeBatch_groupNotices]
          simpa only [List.append_assoc] using facts.handleGraphEvents batch
            (fun event member => allMatch event (List.mem_append_left _ member))
        · exact fun event member => allMatch event (List.mem_append_right _ member)
  exact loop batches (_, _, [])
    (by
      simpa only [List.flatten_nil, List.flatMap_nil, List.append_nil]
        using initialAnnouncementFacts work)
    (fun event member => valid.event_matches member)

/-- Every actual normalized endpoint retains each task's historical contributing notice. -/
theorem createWorkQueue_runNormalized_startedTasksAnnounced {work : Execution.Work}
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    : let queue := State.initialize (Work.fromExecution work)
      (queue.runNormalized batches).1.StartedTasksAnnounced
        (queue.initialGroups.map Execution.DeliveryNode.ref
          ++ (queue.runNormalized batches).2.flatten.flatMap groupNoticeRefs) :=
  (initial_runNormalized_announcementFacts valid).known

/-- An actual normalized task lookup has a contributing owner announced in that run. -/
theorem createWorkQueue_runNormalized_announcedOwner {work : Execution.Work}
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    {occurrence : Occurrence} {node : TaskNode}
    (found
      : ((State.initialize (Work.fromExecution work)).runNormalized batches).1.taskNode?
          occurrence
        = some node)
    : ∃ owners owner,
        TaskHasOwners work occurrence owners
        ∧ owner ∈ owners
        ∧ owner
          ∈ (State.initialize (Work.fromExecution work)).initialGroups.map
              Execution.DeliveryNode.ref
            ++ ((State.initialize (Work.fromExecution work)).runNormalized
                  batches).2.flatten.flatMap
                groupNoticeRefs := by
  have facts := initial_runNormalized_announcementFacts valid
  obtain ⟨member, occurrenceEq⟩ := State.taskNode?_some found
  obtain ⟨owner, contributes, announced⟩ := facts.known node member
  obtain ⟨⟨_, payload, producer, _, located⟩, _⟩ :=
    facts.matching node.task (facts.registered node member)
  exact ⟨node.task.groups.map Execution.DeliveryNode.ref, owner.ref,
    ⟨producer, payload, occurrenceEq ▸ located⟩,
    List.mem_map.mpr ⟨owner, contributes, rfl⟩, announced⟩

/-- A within-batch task lookup retains an owner announced before that FIFO cut.
The earlier host batches use their actual normalized states; the current prefix uses
one supplied cache snapshot. No flattened source-state correspondence is assumed.
-/
theorem createWorkQueue_batchPrefix_announcedOwner {work : Execution.Work}
    (earlier : List (List GraphEvent)) (before : List GraphEvent)
    (valid : ValidGraphEvents work (earlier.flatten ++ before))
    (available : List (Occurrence × Nat)) {occurrence : Occurrence} {node : TaskNode}
    (found
      : ((((State.initialize (Work.fromExecution work)).runNormalized
            earlier).1.replayGraphEvents
            before available).taskNode?
            occurrence
          = some node))
    : let initial := State.initialize (Work.fromExecution work)
      let current := (initial.runNormalized earlier).1
      ∃ owners owner,
        TaskHasOwners work occurrence owners
        ∧ owner ∈ owners
        ∧ owner
          ∈ initial.initialGroups.map Execution.DeliveryNode.ref
            ++ (initial.runNormalized earlier).2.flatten.flatMap groupNoticeRefs
            ++ (current.rawEventReplay before available).2.flatMap
                rawGroupNoticeRefs := by
  have prior := initial_runNormalized_announcementFacts
    (valid.prefix (List.prefix_append earlier.flatten before))
  have facts := prior.rawEventReplay before
    (fun event member => valid.eachMatches (List.mem_append_right _ member)) available
  let current := ((State.initialize (Work.fromExecution work)).runNormalized earlier).1
  have foundRaw : (current.rawEventReplay before available).1.taskNode? occurrence
      = some node := by
    rwa [State.rawEventReplay_state _ _ available]
  obtain ⟨member, occurrenceEq⟩ := State.taskNode?_some foundRaw
  obtain ⟨owner, contributes, announced⟩ := facts.known node member
  obtain ⟨⟨_, payload, producer, _, located⟩, _⟩ :=
    facts.matching node.task (facts.registered node member)
  exact ⟨node.task.groups.map Execution.DeliveryNode.ref, owner.ref,
    ⟨producer, payload, occurrenceEq ▸ located⟩,
    List.mem_map.mpr ⟨owner, contributes, rfl⟩, announced⟩

/-- Every surviving started task has an initial or earlier carrier notice after valid replay.
Witness: initialization followed by matching-handler composition, with no output-admission,
generated-work, start-check, failure-licensing, or cancellation-safety assumption.
-/
theorem createWorkQueue_rawEventReplay_startedTasksAnnounced {work : Execution.Work}
    {events : List GraphEvent} (valid : ValidGraphEvents work events)
    (available : List (Occurrence × Nat) := [])
    : let queue := State.initialize (Work.fromExecution work)
      (queue.rawEventReplay events available).1.StartedTasksAnnounced
        (queue.initialGroups.map Execution.DeliveryNode.ref
          ++ (queue.rawEventReplay events available).2.flatMap rawGroupNoticeRefs) :=
  ((initialAnnouncementFacts work).rawEventReplay events
    (fun _ => valid.eachMatches) available).known

/-- A live source-task lookup has a structurally contributing, previously announced owner.
Witness: exact registered provenance identifies the spec owners; historical start evidence
supplies one owner's ref, even if that owner no longer has an active queue node.
-/
theorem createWorkQueue_replayGraphEvents_announcedOwner {work : Execution.Work}
    {events : List GraphEvent} (valid : ValidGraphEvents work events)
    (available : List (Occurrence × Nat) := [])
    {occurrence : Occurrence} {node : TaskNode}
    (found
      : ((State.initialize (Work.fromExecution work)).replayGraphEvents events
          available).taskNode?
          occurrence
        = some node)
    : ∃ owners owner,
        TaskHasOwners work occurrence owners
        ∧ owner ∈ owners
        ∧ owner
          ∈ (State.initialize (Work.fromExecution work)).initialGroups.map
              Execution.DeliveryNode.ref
            ++ ((State.initialize (Work.fromExecution work)).rawEventReplay
                  events available).2.flatMap
                rawGroupNoticeRefs := by
  let queue := State.initialize (Work.fromExecution work)
  have facts := (initialAnnouncementFacts work).rawEventReplay events
    (fun _ => valid.eachMatches) available
  have foundRaw : (queue.rawEventReplay events available).1.taskNode? occurrence = some node := by
    rwa [State.rawEventReplay_state _ _ available]
  obtain ⟨member, occurrenceEq⟩ := State.taskNode?_some foundRaw
  obtain ⟨owner, contributes, announced⟩ := facts.known node member
  obtain ⟨⟨_, payload, producer, _, located⟩, _⟩ :=
    facts.matching node.task (facts.registered node member)
  exact ⟨node.task.groups.map Execution.DeliveryNode.ref, owner.ref,
    ⟨producer, payload, occurrenceEq ▸ located⟩,
    List.mem_map.mpr ⟨owner, contributes, rfl⟩, announced⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
