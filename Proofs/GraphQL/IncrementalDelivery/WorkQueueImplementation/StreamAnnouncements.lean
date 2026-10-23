import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamActivation

/-! Every active stream is justified by an initial or previously emitted stream notice. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Stream notices are the only source of new active stream refs
-----------------------------------------------------------------------------------------

/-- Stream refs announced by a raw output event; group notices are deliberately excluded.
-/
def rawStreamNoticeRefs : WorkQueueEvent → NodeRefs
  | .groupSuccess _ _ streams | .streamValues _ _ _ streams =>
      streams.map Execution.DeliveryNode.ref
  | _ => []

/-- Stream refs announced by a normalized output event, independently of wire ID allocation.
-/
def streamNoticeRefs : Execution.WorkQueueEvent → NodeRefs
  | .groupSuccess _ _ streams | .streamValues _ _ _ streams =>
      streams.map Execution.DeliveryNode.ref
  | _ => []

/-- A flush's release list is exactly its output's stream notices.
Witness: optional object values announce nothing; the final group-success event carries
precisely the streams returned as released work. -/
theorem State.finishGroupSuccess_streamNotices (queue : State) (group : GroupNode)
    : (queue.finishGroupSuccess group).2.2.newStreams.map Execution.DeliveryNode.ref
      = (queue.finishGroupSuccess group).2.1.flatMap rawStreamNoticeRefs := by
  obtain ⟨selected, _, _, events, _, _⟩ := queue.finishGroupSuccess_publications group
  rw [events, List.flatMap_append]
  split <;> simp [rawStreamNoticeRefs]

/-- Failed-task cleanup does not start a stream, including when it caches latent errors.
Witness: every contributor branch leaves rootStreams unchanged. -/
theorem State.taskFailure_rootStreams (queue : State) (occurrence : Occurrence)
    (errors : Nat)
    : (queue.taskFailure occurrence errors).1.rootStreams = queue.rootStreams := by
  cases found : queue.taskNode? occurrence with
  | none => simp [State.taskFailure, found]
  | some task =>
      rw [queue.taskFailure_eq occurrence errors task found]
      exact failureGroupFold_preserves (fun current => current.rootStreams = queue.rootStreams)
        (fun _ _ prior => prior) errors task.task.groups _ rfl

/-- Rejection output announces no stream refs. -/
theorem State.taskFailure_streamNotices (queue : State) (occurrence : Occurrence)
    (errors : Nat)
    : (queue.taskFailure occurrence errors).2.flatMap rawStreamNoticeRefs = [] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro event member
  obtain ⟨owner, rfl⟩ := queue.taskFailure_event_failure occurrence errors event member
  rfl

/-- Recursive draining activates only old streams or streams announced in its own output.
Witness: each successful flush names every newly activated ref; startup failure removes
groups without activating streams, and later drain steps concatenate their notices.
-/
theorem State.drainReadyGroups_streamRoots (queue : State)
    (available : List (Occurrence × Nat) := [])
    : (queue.drainReadyGroups available).1.rootStreams.Subset
        (queue.rootStreams
          ++ (queue.drainReadyGroups available).2.1.flatMap rawStreamNoticeRefs) := by
  have loop (fuel : Nat) (current : State)
      : (State.drainReadyGroups.go available fuel current).1.rootStreams.Subset
          (current.rootStreams
            ++ (State.drainReadyGroups.go available fuel current).2.1.flatMap
              rawStreamNoticeRefs) := by
    induction fuel generalizing current with
    | zero => intro ref member; exact List.mem_append_left _ member
    | succ fuel ih =>
        unfold State.drainReadyGroups.go
        dsimp only
        split
        · intro ref member; exact List.mem_append_left _ member
        · rename_i node selected
          intro ref member
          have later := ih _ member
          have activated := (current.finishGroupSuccess node).1.startNewWork_rootStreams
            (current.finishGroupSuccess node).2.2 available
          rw [State.finishGroupSuccess_rootStreams,
            State.finishGroupSuccess_streamNotices] at activated
          simp only [List.flatMap_append, List.mem_append]
          rcases List.mem_append.mp later with earlier | announced
          · rcases List.mem_append.mp (activated earlier) with old | fresh
            · exact .inl old
            · exact .inr (.inl fresh)
          · exact .inr (.inr announced)

  exact loop _ queue

/-- A task-success handler activates only old streams or streams announced in its output.
Witness: its contributor fold preserves old active refs and accumulates the exact flush
notice lists; activation and the final drain add only explicitly announced stream refs.
-/
theorem State.taskSuccess_streamRoots (queue : State) (occurrence : Occurrence)
    (result : TaskResult) (available : List (Occurrence × Nat) := [])
    : (queue.taskSuccess occurrence result available).1.rootStreams.Subset
        (queue.rootStreams
          ++ (queue.taskSuccess occurrence result available).2.1.flatMap
              rawStreamNoticeRefs) := by
  cases found : queue.taskNode? occurrence with
  | none =>
      simp only [State.taskSuccess, found]; intro ref member; exact List.mem_append_left _ member
  | some node =>
      let settled := queue.putTaskNode { node with value := some result.value }
      let integrated := settled.maybeIntegrateWork result.work (some occurrence)
      have loop (groups : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent × NewWork)
          (same : acc.1.rootStreams = queue.rootStreams)
          (notices : acc.2.2.newStreams.map Execution.DeliveryNode.ref
            = acc.2.1.flatMap rawStreamNoticeRefs)
          : (groups.foldl successGroupStep acc).1.rootStreams = queue.rootStreams
            ∧ (groups.foldl successGroupStep acc).2.2.newStreams.map Execution.DeliveryNode.ref
              = (groups.foldl successGroupStep acc).2.1.flatMap rawStreamNoticeRefs := by
        induction groups generalizing acc with
        | nil => exact ⟨same, notices⟩
        | cons group rest ih =>
            obtain ⟨current, events, released⟩ := acc
            apply ih
            · dsimp only [successGroupStep]
              split
              · exact same
              · split
                · rw [State.finishGroupSuccess_rootStreams]; exact same
                · exact same
            · dsimp only [successGroupStep]
              split
              · exact notices
              · split
                · simp only [List.map_append, List.flatMap_append, notices,
                    State.finishGroupSuccess_streamNotices]
                · exact notices
      have initial : integrated.1.rootStreams = queue.rootStreams :=
        State.maybeIntegrateWork_rootStreams _ _ _
      obtain ⟨same, notices⟩ := loop node.task.groups (integrated.1, [], {}) initial rfl
      rw [queue.taskSuccess_eq occurrence result node found available]
      have included := ((node.task.groups.foldl successGroupStep
        (integrated.1, [], {})).1).startNewWork_rootStreams
          (node.task.groups.foldl successGroupStep (integrated.1, [], {})).2.2 available
      rw [same, notices] at included
      intro ref member
      have later := State.drainReadyGroups_streamRoots _ available member
      simp only [List.flatMap_append, List.mem_append]
      rcases List.mem_append.mp later with earlier | announced
      · rcases List.mem_append.mp (included earlier) with old | fresh
        · exact .inl old
        · exact .inr (.inl fresh)
      · exact .inr (.inr announced)

/-- Stream-item integration activates only streams named in its emitted notice list.
Witness: item activation uses its accumulated newStreams; the final drain justifies any
further activation with its own subsequent group-success notices.
-/
theorem State.streamItems_streamRoots (queue : State) (stream : Execution.DeliveryNode)
    (items : List StreamItem) (available : List (Occurrence × Nat) := [])
    : (queue.streamItems stream items available).1.rootStreams.Subset
        (queue.rootStreams
          ++ (queue.streamItems stream items available).2.1.flatMap
              rawStreamNoticeRefs) := by
  let step (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue × List GroupFailureEvent)
      (item : StreamItem) :=
    let integrated := acc.1.maybeIntegrateWork item.work
    let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
    let (started, queued) :=
      pruned.1.startNewWork { integrated.2 with newGroups := pruned.2 } available
    (started, acc.2.1 ++ pruned.2, acc.2.2.1 ++ integrated.2.newStreams,
      acc.2.2.2.1 ++ [item.value], acc.2.2.2.2 ++ queued)
  have loop (more : List StreamItem) (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue × List GroupFailureEvent)
      (prior : acc.1.rootStreams.Subset
        (queue.rootStreams ++ acc.2.2.1.map Execution.DeliveryNode.ref))
      : (more.foldl step acc).1.rootStreams.Subset
          (queue.rootStreams ++ (more.foldl step acc).2.2.1.map Execution.DeliveryNode.ref) := by
    induction more generalizing acc with
    | nil => exact prior
    | cons item rest ih =>
        apply ih
        intro ref active
        have included := ((acc.1.maybeIntegrateWork item.work).1.pruneEmptyGroups
          (acc.1.maybeIntegrateWork item.work).2.newGroups).1.startNewWork_rootStreams
            { (acc.1.maybeIntegrateWork item.work).2 with newGroups :=
                ((acc.1.maybeIntegrateWork item.work).1.pruneEmptyGroups
                  (acc.1.maybeIntegrateWork item.work).2.newGroups).2 } available
        have membership := included active
        rw [State.pruneEmptyGroups_rootStreams, State.maybeIntegrateWork_rootStreams] at membership
        change ref ∈ queue.rootStreams ++
          (acc.2.2.1 ++ (acc.1.maybeIntegrateWork item.work).2.newStreams).map
            Execution.DeliveryNode.ref
        simp only [List.map_append, List.mem_append]
        rcases List.mem_append.mp membership with old | added
        · rcases List.mem_append.mp (prior old) with root | priorNotice
          · exact .inl root
          · exact .inr (.inl priorNotice)
        · exact .inr (.inr added)
  unfold State.streamItems
  split
  · intro ref member; exact List.mem_append_left _ member
  · have included := loop items (queue, [], [], [], []) (by
      intro ref member; exact List.mem_append_left _ member)
    intro ref member
    have later := State.drainReadyGroups_streamRoots _ available member
    simp only [List.flatMap_cons, rawStreamNoticeRefs, List.mem_append]
    rcases List.mem_append.mp later with earlier | announced
    · rcases List.mem_append.mp (included earlier) with old | fresh
      · exact .inl old
      · exact .inr (.inl fresh)
    · exact .inr (.inr announced)

/-- Every handler's new active streams are justified by that handler's stream notices.
Witness: the two release paths above; failure only preserves refs and stream closure only
removes them. This property is unconditional on work generation or source admissibility.
-/
theorem State.handleGraphEvent_streamRoots (queue : State) (event : GraphEvent)
    (available : List (Occurrence × Nat) := [])
    : (queue.handleGraphEvent event available).1.rootStreams.Subset
        (queue.rootStreams
          ++ (queue.handleGraphEvent event available).2.1.flatMap
              rawStreamNoticeRefs) := by
  have roots : (queue.cacheTaskFailures available).rootStreams = queue.rootStreams := by
    have frame := congrArg State.rootStreams (queue.cacheTaskFailures_frame available)
    exact frame
  cases event with
  | taskSuccess occurrence result =>
      simpa only [State.handleGraphEvent, roots]
        using (queue.cacheTaskFailures available).taskSuccess_streamRoots occurrence
          result available
  | taskFailure occurrence errors =>
      intro ref member
      rw [State.handleGraphEvent, State.taskFailure_rootStreams, roots] at member
      exact List.mem_append_left _ (by simpa only [roots] using member)
  | streamItems stream items =>
      simpa only [State.handleGraphEvent, roots]
        using (queue.cacheTaskFailures available).streamItems_streamRoots stream items
          available
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess, roots]
      split
      · intro ref member; exact List.mem_append_left _ (List.mem_filter.mp member).1
      · intro ref member; exact List.mem_append_left _ (by simpa only [roots] using member)
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure, roots]
      split
      · intro ref member; exact List.mem_append_left _ (List.mem_filter.mp member).1
      · intro ref member; exact List.mem_append_left _ (by simpa only [roots] using member)

  -----------------------------------------------------------------------------------------
  -- Replay and termination retain the same notice justification
  -----------------------------------------------------------------------------------------

  | groupFailure notice =>
      simp only [State.handleGraphEvent, State.groupFailure]
      split
      · intro ref member; exact List.mem_append_left _ (by simpa only [roots] using member)
      · split <;> intro ref member <;>
          exact List.mem_append_left _ (by simpa only [roots] using member)

/-- Raw event replay activates no stream outside the old roots and its emitted notices.
Witness: concatenate each handler's activation evidence in exact execution/output order.
-/
theorem State.rawEventReplay_streamRoots (queue : State) (events : List GraphEvent)
    (available : List (Occurrence × Nat) := [])
    : (queue.rawEventReplay events available).1.rootStreams.Subset
        (queue.rootStreams
          ++ (queue.rawEventReplay events available).2.flatMap rawStreamNoticeRefs) := by
  induction events generalizing queue with
  | nil => intro ref member; exact List.mem_append_left _ member
  | cons event rest ih =>
      rw [State.rawEventReplay_cons _ _ _ available]
      intro ref member
      have later := ih (queue.dispatchGraphEvent event available).1 member
      simp only [List.flatMap_append, List.mem_append]
      rcases List.mem_append.mp later with current | announced
      · have present := queue.handleGraphEvent_streamRoots event available current
        rcases List.mem_append.mp present with old | added
        · exact .inl old
        · exact .inr (.inl added)
      · exact .inr (.inr announced)

/-- The batch wrapper cannot activate streams without the batch's stream notices.
Witness: raw replay provides the refs; termination only sets a flag and appends a control
event. Calls made after termination emit nothing and leave the queue unchanged.
-/
theorem State.handleGraphEvents_streamRoots (queue : State) (events : List GraphEvent)
    : (queue.handleGraphEvents events).1.rootStreams.Subset
        (queue.rootStreams
          ++ (queue.handleGraphEvents events).2.flatMap rawStreamNoticeRefs) := by
  have noNotices (failures : List GroupFailureEvent)
      : (failures.map (fun failure =>
          WorkQueueEvent.groupFailure failure.group failure.errors)).flatMap rawStreamNoticeRefs
          = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro event member
    obtain ⟨failure, _, rfl⟩ := List.mem_map.mp member
    rfl
  rw [State.handleGraphEvents_eq_rawEventReplay]
  split
  · intro ref member; exact List.mem_append_left _ member
  · have included := queue.rawEventReplay_streamRoots events (GraphEvent.availableFailures events)
    dsimp only
    split
    · simpa only [List.flatMap_append, List.flatMap_singleton, rawStreamNoticeRefs,
        noNotices, List.append_nil] using included
    · simpa only [List.flatMap_append, noNotices, List.append_nil] using included

/-- Every initially active stream is recorded in the queue's initial stream notices.
Witness: immediate integration/pruning leaves no active streams; initialization starts
only the stream refs stored in its initialStreams field.
-/
theorem createWorkQueue_streamRoots (work : Work)
    : (State.initialize work).rootStreams.Subset
        ((State.initialize work).initialStreams.map Execution.DeliveryNode.ref) := by
  let integrated := ({} : State).maybeIntegrateWork work
  let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
  let released := { integrated.2 with newGroups := pruned.2 }
  have empty : pruned.1.rootStreams = [] := by
    rw [State.pruneEmptyGroups_rootStreams, State.maybeIntegrateWork_rootStreams]
  have included := pruned.1.startNewWork_rootStreams released
  change (pruned.1.startNewWork released).1.rootStreams.Subset
    (released.newStreams.map Execution.DeliveryNode.ref)
  simpa only [empty, List.nil_append] using included

-----------------------------------------------------------------------------------------
-- The publisher retains stream notice refs exactly, independently of owner selection
-----------------------------------------------------------------------------------------

/-- Normalizing one queue event retains exactly its stream notices.
Witness: object-owner remapping has no notices; stream carriers keep their notice lists.
-/
theorem IncrementalPublisher.handleWorkQueueEvent_streamNotices
    (publisher : IncrementalPublisher) (event : WorkQueueEvent)
    : (publisher.handleWorkQueueEvent event).2.flatMap streamNoticeRefs
      = rawStreamNoticeRefs event := by
  cases event <;> simp [IncrementalPublisher.handleWorkQueueEvent, rawStreamNoticeRefs,
    streamNoticeRefs, List.flatMap_map]

/-- Stateful publisher normalization retains every stream notice in order.
Witness: each head preserves its notice projection and the actual fold concatenates it.
-/
theorem IncrementalPublisher.normalizeBatch_streamNotices
    (publisher : IncrementalPublisher) (events : List WorkQueueEvent)
    : (publisher.normalizeBatch events).2.flatMap streamNoticeRefs
      = events.flatMap rawStreamNoticeRefs := by
  induction events generalizing publisher with
  | nil => rfl
  | cons event rest ih =>
      rw [IncrementalPublisher.normalizeBatch_cons]
      simp only [List.flatMap_append, IncrementalPublisher.handleWorkQueueEvent_streamNotices,
        ih, List.flatMap_cons]

/-- A normalized batch step activates only streams already in the prior output or this batch.
Witness: queue activation accounting followed by the publisher's exact notice projection.
-/
theorem normalizedStep_streamRoots (acc : NormalizedAcc) (batch : List GraphEvent)
    {initial : NodeRefs}
    (prior
      : acc.1.rootStreams.Subset (initial ++ acc.2.2.flatten.flatMap streamNoticeRefs))
    : (normalizedStep acc batch).1.rootStreams.Subset
        (initial ++ (normalizedStep acc batch).2.2.flatten.flatMap streamNoticeRefs) := by
  rw [normalizedStep_queue, normalizedStep_flatten, List.flatMap_append,
    IncrementalPublisher.normalizeBatch_streamNotices]
  intro ref member
  rcases List.mem_append.mp (acc.1.handleGraphEvents_streamRoots batch member) with old | added
  · rcases List.mem_append.mp (prior old) with initialNotice | previousNotice
    · exact List.mem_append_left _ initialNotice
    · exact List.mem_append_right _ (List.mem_append_left _ previousNotice)
  · exact List.mem_append_right _ (List.mem_append_right _ added)

/-- Every active stream in actual normalized replay has an initial or emitted stream notice.
Witness: queue initialization, per-handler activation accounting, and notice-preserving
publisher normalization through the real batch fold. This holds for arbitrary implementation
work and inputs, without any generated-work, source, lifecycle, or admission assumption.
It establishes prior announcement, not freshness or continued openness of the notice.
-/
theorem createWorkQueue_runNormalized_streamRoots (work : Work)
    (batches : List (List GraphEvent))
    : ((State.initialize work).runNormalized batches).1.rootStreams.Subset
        ((State.initialize work).initialStreams.map Execution.DeliveryNode.ref
          ++ ((State.initialize work).runNormalized batches).2.flatten.flatMap
              streamNoticeRefs) := by
  let initial := (State.initialize work).initialStreams.map Execution.DeliveryNode.ref
  have loop (more : List (List GraphEvent)) (acc : NormalizedAcc)
      (prior
        : acc.1.rootStreams.Subset (initial ++ acc.2.2.flatten.flatMap streamNoticeRefs))
      : (more.foldl normalizedStep acc).1.rootStreams.Subset
          (initial
            ++ (more.foldl normalizedStep acc).2.2.flatten.flatMap streamNoticeRefs) := by
    induction more generalizing acc with
    | nil => exact prior
    | cons batch rest ih => exact ih _ (normalizedStep_streamRoots acc batch prior)
  let queue := State.initialize work
  let publisher : IncrementalPublisher := { active := queue.initialGroups ++ queue.initialStreams }
  exact loop batches (queue, publisher, [])
    (by
      intro ref member
      exact List.mem_append_left _ (createWorkQueue_streamRoots work member))

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
