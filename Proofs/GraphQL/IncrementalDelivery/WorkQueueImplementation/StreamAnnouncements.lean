import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamActivation

/-! Every active stream is justified by an initial or previously emitted stream notice. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Stream notices are the only source of new active stream keys
-----------------------------------------------------------------------------------------

/-- Stream keys announced by a raw output event; group notices are deliberately excluded.
-/
def rawStreamNoticeKeys : WorkQueueEvent → Keys
  | .groupSuccess _ _ streams | .streamValues _ _ _ streams =>
      streams.map Execution.DeliveryNode.key
  | _ => []

/-- Stream keys announced by a normalized output event, independently of wire ID allocation.
-/
def streamNoticeKeys : Execution.WorkQueueEvent → Keys
  | .groupSuccess _ _ streams | .streamValues _ _ _ streams =>
      streams.map Execution.DeliveryNode.key
  | _ => []

/-- A flush's release list is exactly its output's stream notices.
Witness: optional object values announce nothing; the final group-success event carries
precisely the streams returned as released work. -/
theorem State.finishGroupSuccess_streamNotices (queue : State) (group : GroupNode)
    : (queue.finishGroupSuccess group).2.2.newStreams.map Execution.DeliveryNode.key
      = (queue.finishGroupSuccess group).2.1.flatMap rawStreamNoticeKeys := by
  obtain ⟨selected, _, _, events, _, _⟩ := queue.finishGroupSuccess_publications group
  rw [events, List.flatMap_append]
  split <;> simp [rawStreamNoticeKeys]

/-- Recursive draining activates only old streams or streams announced in its own output.
Witness: each successful flush names every newly activated key; failure closures preserve
active streams, and induction concatenates the notice evidence from later drain steps.
-/
theorem State.drainReadyGroups_streamRoots (queue : State)
    : queue.drainReadyGroups.1.rootStreams.Subset
        (queue.rootStreams ++ queue.drainReadyGroups.2.flatMap rawStreamNoticeKeys) := by
  have loop (fuel : Nat) (current : State)
      : (State.drainReadyGroups.go fuel current).1.rootStreams.Subset
          (current.rootStreams
            ++ (State.drainReadyGroups.go fuel current).2.flatMap rawStreamNoticeKeys) := by
    induction fuel generalizing current with
    | zero => intro key member; exact List.mem_append_left _ member
    | succ fuel ih =>
        unfold State.drainReadyGroups.go
        dsimp only
        split
        · intro key member; exact List.mem_append_left _ member
        · rename_i node selected
          cases cached : node.failure with
          | none =>
              dsimp only
              intro key member
              have later := ih _ member
              have activated := (current.finishGroupSuccess node).1.startNewWork_rootStreams
                (current.finishGroupSuccess node).2.2
              rw [State.finishGroupSuccess_rootStreams,
                State.finishGroupSuccess_streamNotices] at activated
              simp only [List.flatMap_append, List.mem_append]
              rcases List.mem_append.mp later with earlier | announced
              · rcases List.mem_append.mp (activated earlier) with old | fresh
                · exact .inl old
                · exact .inr (.inl fresh)
              · exact .inr (.inr announced)
          | some errors =>
              have same : (current.removeGroup node.group.node.key).rootStreams
                  = current.rootStreams := rfl
              simpa only [State.finishGroupFailure, List.flatMap_append,
                List.flatMap_singleton, rawStreamNoticeKeys, List.nil_append, same]
                using ih (current.removeGroup node.group.node.key)
  exact loop _ queue

/-- A task-success handler activates only old streams or streams announced in its output.
Witness: its contributor fold preserves old active keys and accumulates the exact flush
notice lists; activation and the final drain add only explicitly announced stream keys.
-/
theorem State.taskSuccess_streamRoots (queue : State) (occurrence : Occurrence)
    (result : TaskResult)
    : (queue.taskSuccess occurrence result).1.rootStreams.Subset
        (queue.rootStreams
          ++ (queue.taskSuccess occurrence result).2.flatMap rawStreamNoticeKeys) := by
  cases found : queue.taskNode? occurrence with
  | none =>
      simp only [State.taskSuccess, found]; intro key member; exact List.mem_append_left _ member
  | some node =>
      let settled := queue.putTaskNode { node with value := some result.value }
      let integrated := settled.maybeIntegrateWork result.work (some occurrence)
      have loop (groups : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent × NewWork)
          (same : acc.1.rootStreams = queue.rootStreams)
          (notices : acc.2.2.newStreams.map Execution.DeliveryNode.key
            = acc.2.1.flatMap rawStreamNoticeKeys)
          : (groups.foldl successGroupStep acc).1.rootStreams = queue.rootStreams
            ∧ (groups.foldl successGroupStep acc).2.2.newStreams.map Execution.DeliveryNode.key
              = (groups.foldl successGroupStep acc).2.1.flatMap rawStreamNoticeKeys := by
        induction groups generalizing acc with
        | nil => exact ⟨same, notices⟩
        | cons group rest ih =>
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
      rw [queue.taskSuccess_eq occurrence result node found]
      split
      · exact fun _ member => List.mem_append_left _ member
      have included := ((node.task.groups.foldl successGroupStep
        (integrated.1, [], {})).1).startNewWork_rootStreams
          (node.task.groups.foldl successGroupStep (integrated.1, [], {})).2.2
      rw [same, notices] at included
      intro key member
      have later := State.drainReadyGroups_streamRoots _ member
      simp only [List.flatMap_append, List.mem_append]
      rcases List.mem_append.mp later with earlier | announced
      · rcases List.mem_append.mp (included earlier) with old | fresh
        · exact .inl old
        · exact .inr (.inl fresh)
      · exact .inr (.inr announced)

/-- Failed-task cleanup does not start a stream, including when it caches latent errors.
Witness: every contributor branch leaves rootStreams unchanged. -/
theorem State.taskFailure_rootStreams (queue : State) (occurrence : Occurrence)
    (errors : Nat)
    : (queue.taskFailure occurrence errors).1.rootStreams = queue.rootStreams := by
  let step (acc : State × List WorkQueueEvent) (group : Execution.DeliveryNode) :=
    match acc.1.groupNode? group.key with
    | none => acc
    | some node =>
        if acc.1.rootGroups.contains group.key then
          let failure := acc.1.finishGroupFailure node errors
          (failure.1, acc.2 ++ [failure.2])
        else (acc.1.putGroupNode
          { node with pending := node.pending - 1
                      failure := some (node.failure.getD 0 + errors) }, acc.2)
  have loop (groups : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent)
      : (groups.foldl step acc).1.rootStreams = acc.1.rootStreams := by
    induction groups generalizing acc with
    | nil => rfl
    | cons group rest ih =>
        rw [List.foldl_cons, ih]
        unfold step
        split
        · rfl
        · split <;> rfl
  unfold State.taskFailure
  split
  · rfl
  · split
    · rfl
    exact loop _ (_, [])

/-- Stream-item integration activates only streams named in its emitted notice list.
Witness: item activation uses its accumulated newStreams; the final drain justifies any
further activation with its own subsequent group-success notices.
-/
theorem State.streamItems_streamRoots (queue : State) (stream : Execution.DeliveryNode)
    (items : List StreamItem)
    : (queue.streamItems stream items).1.rootStreams.Subset
        (queue.rootStreams
          ++ (queue.streamItems stream items).2.flatMap rawStreamNoticeKeys) := by
  let step (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue) (item : StreamItem) :=
    let integrated := acc.1.maybeIntegrateWork item.work
    let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
    (pruned.1.startNewWork { integrated.2 with newGroups := pruned.2 },
      acc.2.1 ++ pruned.2, acc.2.2.1 ++ integrated.2.newStreams,
      acc.2.2.2 ++ [item.value])
  have loop (more : List StreamItem) (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue)
      (prior : acc.1.rootStreams.Subset
        (queue.rootStreams ++ acc.2.2.1.map Execution.DeliveryNode.key))
      : (more.foldl step acc).1.rootStreams.Subset
          (queue.rootStreams ++ (more.foldl step acc).2.2.1.map Execution.DeliveryNode.key) := by
    induction more generalizing acc with
    | nil => exact prior
    | cons item rest ih =>
        apply ih
        intro key active
        have included := ((acc.1.maybeIntegrateWork item.work).1.pruneEmptyGroups
          (acc.1.maybeIntegrateWork item.work).2.newGroups).1.startNewWork_rootStreams
            { (acc.1.maybeIntegrateWork item.work).2 with newGroups :=
                ((acc.1.maybeIntegrateWork item.work).1.pruneEmptyGroups
                  (acc.1.maybeIntegrateWork item.work).2.newGroups).2 }
        have membership := included active
        rw [State.pruneEmptyGroups_rootStreams, State.maybeIntegrateWork_rootStreams] at membership
        change key ∈ queue.rootStreams ++
          (acc.2.2.1 ++ (acc.1.maybeIntegrateWork item.work).2.newStreams).map
            Execution.DeliveryNode.key
        simp only [List.map_append, List.mem_append]
        rcases List.mem_append.mp membership with old | added
        · rcases List.mem_append.mp (prior old) with root | priorNotice
          · exact .inl root
          · exact .inr (.inl priorNotice)
        · exact .inr (.inr added)
  unfold State.streamItems
  split
  · intro key member; exact List.mem_append_left _ member
  · have included := loop items (queue, [], [], []) (by
      intro key member; exact List.mem_append_left _ member)
    intro key member
    have later := State.drainReadyGroups_streamRoots _ member
    simp only [List.flatMap_cons, rawStreamNoticeKeys, List.mem_append]
    rcases List.mem_append.mp later with earlier | announced
    · rcases List.mem_append.mp (included earlier) with old | fresh
      · exact .inl old
      · exact .inr (.inl fresh)
    · exact .inr (.inr announced)

/-- Every handler's new active streams are justified by that handler's stream notices.
Witness: the two release paths above; failure only preserves keys and stream closure only
removes them. This property is unconditional on work generation or source admissibility.
-/
theorem State.handleGraphEvent_streamRoots (queue : State) (event : GraphEvent)
    : (queue.handleGraphEvent event).1.rootStreams.Subset
        (queue.rootStreams
          ++ (queue.handleGraphEvent event).2.flatMap rawStreamNoticeKeys) := by
  cases event with
  | taskSuccess occurrence result => exact queue.taskSuccess_streamRoots occurrence result
  | taskFailure occurrence errors =>
      intro key member
      rw [State.handleGraphEvent, State.taskFailure_rootStreams] at member
      exact List.mem_append_left _ member
  | streamItems stream items => exact queue.streamItems_streamRoots stream items
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess]
      split
      · intro key member; exact List.mem_append_left _ (List.mem_filter.mp member).1
      · intro key member; exact List.mem_append_left _ member
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure]
      split
      · intro key member; exact List.mem_append_left _ (List.mem_filter.mp member).1
      · intro key member; exact List.mem_append_left _ member

-----------------------------------------------------------------------------------------
-- Replay and termination retain the same notice justification
-----------------------------------------------------------------------------------------

/-- Raw event replay activates no stream outside the old roots and its emitted notices.
Witness: concatenate each handler's activation evidence in exact execution/output order.
-/
theorem State.rawEventReplay_streamRoots (queue : State) (events : List GraphEvent)
    : (queue.rawEventReplay events).1.rootStreams.Subset
        (queue.rootStreams
          ++ (queue.rawEventReplay events).2.flatMap rawStreamNoticeKeys) := by
  induction events generalizing queue with
  | nil => intro key member; exact List.mem_append_left _ member
  | cons event rest ih =>
      rw [State.rawEventReplay_cons]
      intro key member
      have later := ih (queue.handleGraphEvent event).1 member
      simp only [List.flatMap_append, List.mem_append]
      rcases List.mem_append.mp later with current | announced
      · have present := queue.handleGraphEvent_streamRoots event current
        rcases List.mem_append.mp present with old | added
        · exact .inl old
        · exact .inr (.inl added)
      · exact .inr (.inr announced)

/-- The batch wrapper cannot activate streams without the batch's stream notices.
Witness: raw replay provides the keys; termination only sets a flag and appends a control
event. Calls made after termination emit nothing and leave the queue unchanged.
-/
theorem State.handleGraphEvents_streamRoots (queue : State) (events : List GraphEvent)
    : (queue.handleGraphEvents events).1.rootStreams.Subset
        (queue.rootStreams
          ++ (queue.handleGraphEvents events).2.flatMap rawStreamNoticeKeys) := by
  rw [State.handleGraphEvents_eq_rawEventReplay]
  split
  · intro key member; exact List.mem_append_left _ member
  · have included := queue.rawEventReplay_streamRoots events
    dsimp only
    split
    · simpa only [List.flatMap_append, List.flatMap_singleton, rawStreamNoticeKeys,
        List.append_nil] using included
    · exact included

/-- Every initially active stream is recorded in the queue's initial stream notices.
Witness: immediate integration/pruning leaves no active streams; initialization starts
only the stream keys stored in its initialStreams field.
-/
theorem createWorkQueue_streamRoots (work : Work)
    : (State.initialize work).rootStreams.Subset
        ((State.initialize work).initialStreams.map Execution.DeliveryNode.key) := by
  let integrated := ({} : State).maybeIntegrateWork work
  let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
  let released := { integrated.2 with newGroups := pruned.2 }
  have empty : pruned.1.rootStreams = [] := by
    rw [State.pruneEmptyGroups_rootStreams, State.maybeIntegrateWork_rootStreams]
  have included := pruned.1.startNewWork_rootStreams released
  change (pruned.1.startNewWork released).rootStreams.Subset
    (released.newStreams.map Execution.DeliveryNode.key)
  simpa only [empty, List.nil_append] using included

-----------------------------------------------------------------------------------------
-- The publisher retains stream notice keys exactly, independently of owner selection
-----------------------------------------------------------------------------------------

/-- Normalizing one queue event retains exactly its stream notices.
Witness: object-owner remapping has no notices; stream carriers keep their notice lists.
-/
theorem IncrementalPublisher.handleWorkQueueEvent_streamNotices
    (publisher : IncrementalPublisher) (event : WorkQueueEvent)
    : (publisher.handleWorkQueueEvent event).2.flatMap streamNoticeKeys
      = rawStreamNoticeKeys event := by
  cases event <;> simp [IncrementalPublisher.handleWorkQueueEvent, rawStreamNoticeKeys,
    streamNoticeKeys, List.flatMap_map]

/-- Stateful publisher normalization retains every stream notice in order.
Witness: each head preserves its notice projection and the actual fold concatenates it.
-/
theorem IncrementalPublisher.normalizeBatch_streamNotices
    (publisher : IncrementalPublisher) (events : List WorkQueueEvent)
    : (publisher.normalizeBatch events).2.flatMap streamNoticeKeys
      = events.flatMap rawStreamNoticeKeys := by
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
    {initial : Keys}
    (prior
      : acc.1.rootStreams.Subset (initial ++ acc.2.2.flatten.flatMap streamNoticeKeys))
    : (normalizedStep acc batch).1.rootStreams.Subset
        (initial ++ (normalizedStep acc batch).2.2.flatten.flatMap streamNoticeKeys) := by
  rw [normalizedStep_queue, normalizedStep_flatten, List.flatMap_append,
    IncrementalPublisher.normalizeBatch_streamNotices]
  intro key member
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
        ((State.initialize work).initialStreams.map Execution.DeliveryNode.key
          ++ ((State.initialize work).runNormalized batches).2.flatten.flatMap
              streamNoticeKeys) := by
  let initial := (State.initialize work).initialStreams.map Execution.DeliveryNode.key
  have loop (more : List (List GraphEvent)) (acc : NormalizedAcc)
      (prior
        : acc.1.rootStreams.Subset (initial ++ acc.2.2.flatten.flatMap streamNoticeKeys))
      : (more.foldl normalizedStep acc).1.rootStreams.Subset
          (initial
            ++ (more.foldl normalizedStep acc).2.2.flatten.flatMap streamNoticeKeys) := by
    induction more generalizing acc with
    | nil => exact prior
    | cons batch rest ih => exact ih _ (normalizedStep_streamRoots acc batch prior)
  let queue := State.initialize work
  let publisher : IncrementalPublisher := { active := queue.initialGroups ++ queue.initialStreams }
  exact loop batches (queue, publisher, [])
    (by
      intro key member
      exact List.mem_append_left _ (createWorkQueue_streamRoots work member))

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
