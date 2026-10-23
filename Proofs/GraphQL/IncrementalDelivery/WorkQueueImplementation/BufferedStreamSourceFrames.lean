import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ObjectStreamSupportReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.BufferedStreamReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TerminalRoots

/-! Buffered child-stream conservation follows actual source frames and cache snapshots. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

private theorem success_failure_disjoint {work occurrence result errors}
    (success : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (failure : (GraphEvent.taskFailure occurrence errors).MatchesWork work)
    : False := by
  obtain ⟨owners, producer, path, known⟩ := failure
  obtain ⟨otherOwners, birth, descriptor, value⟩ := success
  have same := (known.unique descriptor).2.2
  cases same

/-- Source and link certificates for conserving buffered child streams at a FIFO cut. -/
structure BufferedStreamSourceFrame (queue : State) (work : Execution.Work)
    (parents : Nat → NodeRefs) (before : List GraphEvent)
    : Prop where
  source : ObjectStreamReplayFrame queue work parents before
  links : queue.StoredTaskLinks
  children : queue.ChildStreamInventory

/-- Pending notices leave buffered links and child inventories unchanged. -/
theorem BufferedStreamSourceFrame.withGroupFailures {queue work parents before}
    (frame : BufferedStreamSourceFrame queue work parents before)
    (groupFailureEvents : List GroupFailureEvent)
    : BufferedStreamSourceFrame { queue with groupFailureEvents } work parents before :=
  ⟨frame.source.withGroupFailures groupFailureEvents, frame.links, frame.children⟩

/-- Licensed rejection snapshots exclude every previously stored successful producer. -/
theorem BufferedStreamSourceFrame.buffersCacheClean {queue work parents before}
    (frame : BufferedStreamSourceFrame queue work parents before)
    (valid : ValidGraphEvents work before) (available : List (Occurrence × Nat))
    (licensed
      : ∀ occurrence errors,
          (occurrence, errors) ∈ available
          → (GraphEvent.taskFailure occurrence errors).MatchesWork work)
    : queue.StoredValuesSatisfy
        (fun occurrence _ => ∀ errors, (occurrence, errors) ∉ available) := by
  obtain ⟨published, inventory⟩ := frame.source.publications
  intro node member value stored errors rejected
  obtain ⟨result, received, same⟩ := (inventory.stored node member value stored).1
  exact success_failure_disjoint (valid.eachMatches received) (licensed _ _ rejected)

/-- A matched successful computation is absent from every licensed rejection snapshot. -/
theorem GraphEvent.MatchesWork.success_cacheClean {work occurrence result}
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (available : List (Occurrence × Nat))
    (licensed
      : ∀ occurrence errors,
          (occurrence, errors) ∈ available
          → (GraphEvent.taskFailure occurrence errors).MatchesWork work)
    : ∀ errors, (occurrence, errors) ∉ available :=
  fun _ rejected => success_failure_disjoint matching (licensed _ _ rejected)

/-- A valid source input preserves the source and buffered-link certificates. -/
theorem BufferedStreamSourceFrame.handleGraphEvent {queue work parents before event}
    (frame : BufferedStreamSourceFrame queue work parents before)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (valid : ValidGraphEvents work (before ++ [event]))
    (accepted : queue.acceptsGraphEvent event = true)
    (available : List (Occurrence × Nat))
    (licensed
      : ∀ occurrence errors,
          (occurrence, errors) ∈ available
          → (GraphEvent.taskFailure occurrence errors).MatchesWork work)
    : BufferedStreamSourceFrame (queue.handleGraphEvent event available).1 work parents
        (before ++ [event]) := by
  obtain ⟨_, matching, fresh⟩ := validGraphEvents_last valid
  exact ⟨frame.source.handleGraphEvent generated canonical event valid accepted available licensed,
    frame.links.handleGraphEvent frame.source.source.pending
      (GraphEvent.groupSettlements_subsetIdentities before) event matching fresh available,
    frame.children.handleGraphEvent event available⟩

/-- Every actual FIFO handler conserves streams of its previously buffered successes. -/
theorem BufferedStreamSourceFrame.conserves {queue work parents before event}
    (frame : BufferedStreamSourceFrame queue work parents before)
    (valid : ValidGraphEvents work (before ++ [event]))
    (available : List (Occurrence × Nat))
    (licensed
      : ∀ occurrence errors,
          (occurrence, errors) ∈ available
          → (GraphEvent.taskFailure occurrence errors).MatchesWork work)
    : queue.BufferedStreamsConserved (queue.handleGraphEvent event available).2.1
        (queue.handleGraphEvent event available).1 := by
  obtain ⟨published, inventory⟩ := frame.source.publications
  have sources := inventory.stored.mono (fun _ _ source => source.1)
  obtain ⟨prior, matching, fresh⟩ := validGraphEvents_last valid
  refine State.handleGraphEvent_bufferedStreamsConserved frame.source.source.pending frame.links
    frame.children sources (GraphEvent.groupSettlements_subsetIdentities before) event matching
    fresh
    available ?_ ?_
  · intro node member value stored errors rejected
    obtain ⟨result, received, same⟩ := sources node member value stored
    exact success_failure_disjoint (prior.eachMatches received) (licensed _ _ rejected)
  · intro occurrence result same errors rejected
    subst event
    exact success_failure_disjoint matching (licensed _ _ rejected)

/-- Fixed-snapshot replay retains the same source and buffered-link frame. -/
theorem BufferedStreamSourceFrame.replayGraphEvents {queue work parents before}
    (frame : BufferedStreamSourceFrame queue work parents before)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (events : List GraphEvent) (valid : ValidGraphEvents work (before ++ events))
    (available : List (Occurrence × Nat))
    (licensed
      : ∀ occurrence errors,
          (occurrence, errors) ∈ available
          → (GraphEvent.taskFailure occurrence errors).MatchesWork work)
    (accepted : State.eventsStarted available queue events = true)
    : BufferedStreamSourceFrame (queue.replayGraphEvents events available) work parents
        (before ++ events) := by
  induction events generalizing queue before with
  | nil =>
      simpa only [State.replayGraphEvents, List.foldl_nil, List.append_nil] using frame
  | cons event rest ih =>
      have earlier : (before ++ [event]).IsPrefix (before ++ event :: rest) :=
        ⟨rest, by simp [List.append_assoc]⟩
      have accepts : queue.acceptsGraphEvent event = true ∧
          State.eventsStarted available (queue.dispatchGraphEvent event available).1 rest
            = true := by
        simpa only [State.eventsStarted, Bool.and_eq_true] using accepted
      have next : BufferedStreamSourceFrame (queue.dispatchGraphEvent event available).1
          work parents (before ++ [event]) :=
        frame.handleGraphEvent generated canonical (valid.prefix earlier) accepts.1
          available licensed |>.withGroupFailures _
      have retained := ih next
        (by simpa only [List.append_assoc, List.singleton_append] using valid)
        accepts.2
      simpa only [State.replayGraphEvents, List.foldl_cons, List.append_assoc,
        List.singleton_append]
        using retained

/-- A fixed-snapshot continuation conserves every protected buffered child stream. -/
theorem BufferedStreamSourceFrame.replayGraphEvents_conserves {queue work parents before}
    (frame : BufferedStreamSourceFrame queue work parents before)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (events : List GraphEvent) (valid : ValidGraphEvents work (before ++ events))
    (available : List (Occurrence × Nat))
    (licensed
      : ∀ occurrence errors,
          (occurrence, errors) ∈ available
          → (GraphEvent.taskFailure occurrence errors).MatchesWork work)
    (accepted : State.eventsStarted available queue events = true)
    : queue.BufferedStreamsConserved (queue.rawEventReplay events available).2
        (queue.replayGraphEvents events available) := by
  induction events generalizing queue before with
  | nil => exact .refl _
  | cons event rest ih =>
      have earlier : (before ++ [event]).IsPrefix (before ++ event :: rest) :=
        ⟨rest, by simp [List.append_assoc]⟩
      have accepts : queue.acceptsGraphEvent event = true ∧
          State.eventsStarted available (queue.dispatchGraphEvent event available).1 rest
            = true := by
        simpa only [State.eventsStarted, Bool.and_eq_true] using accepted
      have next : BufferedStreamSourceFrame (queue.dispatchGraphEvent event available).1
          work parents (before ++ [event]) :=
        frame.handleGraphEvent generated canonical (valid.prefix earlier) accepts.1
          available licensed |>.withGroupFailures _
      have retained := ih next
        (by simpa only [List.append_assoc, List.singleton_append] using valid)
        accepts.2
      have first : queue.BufferedStreamsConserved (queue.dispatchGraphEvent event available).2
          (queue.dispatchGraphEvent event available).1 :=
        frame.conserves (valid.prefix earlier) available licensed
      have combined := first.append retained
        (State.replayGraphEvents_cancelledGroups_subset _ rest available)
      simpa only [State.rawEventReplay_cons, State.replayGraphEvents, List.foldl_cons]
        using combined

/-- Buffered replay combines independently derived source frames with matching link and
child inventories. No current task-membership premise is needed by their handlers.
-/
theorem BufferedStreamSourceFrame.replayGraphEvents_admitted {queue work parents before}
    (frame : BufferedStreamSourceFrame queue work parents before)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (events : List GraphEvent) (valid : ValidGraphEvents work (before ++ events))
    (available : List (Occurrence × Nat))
    (licensed
      : ∀ occurrence errors,
          (occurrence, errors) ∈ available
          → (GraphEvent.taskFailure occurrence errors).MatchesWork work)
    (accepted : State.acceptsBatch.go (fun _ => false) available queue events = true)
    : BufferedStreamSourceFrame (queue.replayGraphEvents events available) work parents
        (before ++ events) := by
  have sourceAt (fifo : List GraphEvent) (earlier : fifo.IsPrefix events) :
      ObjectStreamReplayFrame (queue.replayGraphEvents fifo available) work parents
        (before ++ fifo) := by
    obtain ⟨tail, joined⟩ := earlier
    apply frame.source.replayGraphEvents_admitted generated canonical fifo
      (valid.prefix ⟨tail, by rw [List.append_assoc, joined]⟩) available licensed
    apply State.acceptsBatch_go_prefix (after := tail)
    simpa only [joined] using accepted
  have loop (remaining fifo : List GraphEvent) (split : events = fifo ++ remaining)
      (links : (queue.replayGraphEvents fifo available).StoredTaskLinks)
      (children : (queue.replayGraphEvents fifo available).ChildStreamInventory)
      : (queue.replayGraphEvents events available).StoredTaskLinks
          ∧ (queue.replayGraphEvents events available).ChildStreamInventory := by
    induction remaining generalizing fifo with
    | nil =>
        have same : events = fifo := by simpa only [List.append_nil] using split
        simpa only [same] using And.intro links children
    | cons event rest ih =>
        have boundary : (before ++ fifo ++ [event]).IsPrefix (before ++ events) :=
          ⟨rest, by simp [split, List.append_assoc]⟩
        obtain ⟨_, matching, fresh⟩ := validGraphEvents_last (valid.prefix boundary)
        have source := sourceAt fifo ⟨event :: rest, split.symm⟩
        have nextLinks : ((queue.replayGraphEvents fifo available).dispatchGraphEvent event available).1.StoredTaskLinks :=
          links.handleGraphEvent source.source.pending
          (GraphEvent.groupSettlements_subsetIdentities (before ++ fifo)) event matching fresh
          available
        have nextChildren : ((queue.replayGraphEvents fifo available).dispatchGraphEvent event available).1.ChildStreamInventory :=
          children.handleGraphEvent event available
        apply ih (fifo ++ [event]) (by simp [split, List.append_assoc])
        · simpa only [State.replayGraphEvents_append, State.replayGraphEvents,
            List.foldl_append, List.foldl_cons, List.foldl_nil] using nextLinks
        · simpa only [State.replayGraphEvents_append, State.replayGraphEvents,
            List.foldl_append, List.foldl_cons, List.foldl_nil] using nextChildren
  have facts := loop events [] (by simp) frame.links frame.children
  exact ⟨sourceAt events (List.prefix_refl _), facts.1, facts.2⟩

/-- Exact source frames at every prefix suffice for buffered stream conservation.
This also handles a suffix whose eligibility came from an earlier batch-entry queue.
-/
theorem BufferedStreamSourceFrame.replayGraphEvents_conserves_of_prefixFrames
    {queue : State} {work parents before} (events : List GraphEvent)
    (valid : ValidGraphEvents work (before ++ events))
    (available : List (Occurrence × Nat))
    (licensed
      : ∀ occurrence errors,
          (occurrence, errors) ∈ available
          → (GraphEvent.taskFailure occurrence errors).MatchesWork work)
    (framesAt
      : ∀ fifo,
          fifo.IsPrefix events
          → BufferedStreamSourceFrame (queue.replayGraphEvents fifo available) work
              parents (before ++ fifo))
    : queue.BufferedStreamsConserved (queue.rawEventReplay events available).2
        (queue.replayGraphEvents events available) := by
  have loop (remaining fifo : List GraphEvent) (split : events = fifo ++ remaining) :
      (queue.replayGraphEvents fifo available).BufferedStreamsConserved
        ((queue.replayGraphEvents fifo available).rawEventReplay remaining available).2
        ((queue.replayGraphEvents fifo available).replayGraphEvents remaining available) := by
    induction remaining generalizing fifo with
    | nil => exact .refl _
    | cons event rest ih =>
        have boundary : (before ++ fifo ++ [event]).IsPrefix (before ++ events) :=
          ⟨rest, by simp [split, List.append_assoc]⟩
        have first : (queue.replayGraphEvents fifo available).BufferedStreamsConserved
            ((queue.replayGraphEvents fifo available).dispatchGraphEvent event available).2
            ((queue.replayGraphEvents fifo available).dispatchGraphEvent event available).1 :=
          (framesAt fifo ⟨event :: rest, split.symm⟩).conserves
          (valid.prefix boundary) available licensed
        have later := ih (fifo ++ [event]) (by simp [split, List.append_assoc])
        let nextQueue := ((queue.replayGraphEvents fifo available).dispatchGraphEvent event
          available).1
        have retained : nextQueue.BufferedStreamsConserved
            (nextQueue.rawEventReplay rest available).2
            (nextQueue.replayGraphEvents rest available) := by
          simpa only [State.replayGraphEvents_append, State.replayGraphEvents,
            List.foldl_append, List.foldl_cons, List.foldl_nil, nextQueue]
            using later
        have combined := first.append retained
          (State.replayGraphEvents_cancelledGroups_subset _ rest available)
        simpa only [State.rawEventReplay_cons, State.replayGraphEvents, List.foldl_cons,
          nextQueue]
          using combined
  exact loop events [] (by simp)

/-- Conservation composes at actual buffered prefix states with the complete cache snapshot. -/
theorem BufferedStreamSourceFrame.replayGraphEvents_conserves_admitted
    {queue work parents before}
    (frame : BufferedStreamSourceFrame queue work parents before)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (events : List GraphEvent) (valid : ValidGraphEvents work (before ++ events))
    (available : List (Occurrence × Nat))
    (licensed
      : ∀ occurrence errors,
          (occurrence, errors) ∈ available
          → (GraphEvent.taskFailure occurrence errors).MatchesWork work)
    (accepted : State.acceptsBatch.go (fun _ => false) available queue events = true)
    : queue.BufferedStreamsConserved (queue.rawEventReplay events available).2
        (queue.replayGraphEvents events available) := by
  have frameAt (fifo : List GraphEvent) (earlier : fifo.IsPrefix events) :
      BufferedStreamSourceFrame (queue.replayGraphEvents fifo available) work parents
        (before ++ fifo) := by
    obtain ⟨tail, joined⟩ := earlier
    apply frame.replayGraphEvents_admitted generated canonical fifo
      (valid.prefix ⟨tail, by rw [List.append_assoc, joined]⟩) available licensed
    apply State.acceptsBatch_go_prefix (after := tail)
    simpa only [joined] using accepted
  exact BufferedStreamSourceFrame.replayGraphEvents_conserves_of_prefixFrames
    events valid available licensed frameAt

/-- Updating the terminal flag leaves all stream-conservation premises unchanged. -/
theorem BufferedStreamSourceFrame.withTerminated {queue work parents before}
    (frame : BufferedStreamSourceFrame queue work parents before) (terminal : Bool)
    : BufferedStreamSourceFrame {queue with terminated := terminal} work parents before :=
  ⟨frame.source.withTerminated terminal, frame.links, frame.children⟩

private theorem batchRejections_match {work before events}
    (valid : ValidGraphEvents work (before ++ events))
    : ∀ occurrence errors,
        (occurrence, errors) ∈ GraphEvent.availableFailures events
        → (GraphEvent.taskFailure occurrence errors).MatchesWork work := by
  intro occurrence errors member
  obtain ⟨event, received, same⟩ := List.mem_filterMap.mp member
  cases event <;> simp only [Option.some.injEq, reduceCtorEq, Prod.mk.injEq] at same
  obtain ⟨rfl, rfl⟩ := same
  exact valid.eachMatches (List.mem_append_right _ received)

/-- Actual host batching preserves the joint buffered-stream frame. -/
theorem BufferedStreamSourceFrame.handleGraphEvents {queue work parents before}
    (frame : BufferedStreamSourceFrame queue work parents before)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (events : List GraphEvent) (valid : ValidGraphEvents work (before ++ events))
    (running : queue.terminated = false) (accepted : queue.acceptsBatch events = true)
    : BufferedStreamSourceFrame (queue.handleGraphEvents events).1 work parents
        (before ++ events) := by
  have replayed := frame.replayGraphEvents_admitted generated canonical events valid
    (GraphEvent.availableFailures events) (batchRejections_match valid) accepted
  obtain ⟨terminal, same⟩ := queue.handleGraphEvents_stateCore events running
  rw [same]
  exact replayed.withTerminated terminal

/-- Batch-final diagnostic forwarding changes no buffered stream obligation. -/
theorem BufferedStreamSourceFrame.handleGraphEvents_conserves {queue work parents before}
    (frame : BufferedStreamSourceFrame queue work parents before)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (events : List GraphEvent) (valid : ValidGraphEvents work (before ++ events))
    (running : queue.terminated = false) (accepted : queue.acceptsBatch events = true)
    : queue.BufferedStreamsConserved (queue.handleGraphEvents events).2
        (queue.handleGraphEvents events).1 := by
  have replayed := frame.replayGraphEvents_conserves_admitted generated canonical events valid
    (GraphEvent.availableFailures events) (batchRejections_match valid) accepted
  rw [State.handleGraphEvents_eq_rawEventReplay]
  simp only [running, Bool.false_eq_true, ↓reduceIte]
  split
  <;> simpa only [State.BufferedStreamsConserved, State.taskNode?,
    State.rawEventReplay_state, List.flatMap_append, List.flatMap_singleton,
    rawStreamNoticeRefs, List.append_nil]
    using replayed

/-- Valid started batches retain the joint frame at their actual final queue state. -/
theorem BufferedStreamSourceFrame.runNormalized {queue work parents before}
    (frame : BufferedStreamSourceFrame queue work parents before)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work (before ++ batches.flatten))
    (started : queue.batchesStarted batches = true)
    : BufferedStreamSourceFrame (queue.runNormalized batches).1 work parents
        (before ++ batches.flatten) := by
  rw [State.runNormalized_replayBatches]
  induction batches generalizing queue before with
  | nil =>
      simpa only [State.replayBatches, List.foldl_nil, List.flatten_nil, List.append_nil]
        using frame
  | cons batch rest ih =>
      obtain ⟨running, accepted, restStarted⟩ := queue.batchesStarted_cons batch rest started
      have earlier : (before ++ batch).IsPrefix (before ++ (batch :: rest).flatten) :=
        ⟨rest.flatten, by simp [List.append_assoc]⟩
      have next := frame.handleGraphEvents generated canonical batch (valid.prefix earlier)
        running accepted
      have retained := ih next (by simpa only [List.flatten_cons, List.append_assoc] using valid)
        restStarted
      simpa only [State.replayBatches, List.foldl_cons, List.flatten_cons,
        List.append_assoc]
        using retained

/-- Actual batch continuations conserve every protected buffered child stream. -/
theorem BufferedStreamSourceFrame.rawBatches_conserves {queue work parents before}
    (frame : BufferedStreamSourceFrame queue work parents before)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work (before ++ batches.flatten))
    (started : queue.batchesStarted batches = true)
    : queue.BufferedStreamsConserved (queue.rawBatches batches).2
        (queue.replayBatches batches) := by
  induction batches generalizing queue before with
  | nil => exact .refl _
  | cons batch rest ih =>
      obtain ⟨running, accepted, restStarted⟩ := queue.batchesStarted_cons batch rest started
      have earlier : (before ++ batch).IsPrefix (before ++ (batch :: rest).flatten) :=
        ⟨rest.flatten, by simp [List.append_assoc]⟩
      have next := frame.handleGraphEvents generated canonical batch (valid.prefix earlier)
        running accepted
      have retained := ih next (by simpa only [List.flatten_cons, List.append_assoc] using valid)
        restStarted
      have cancellation := (queue.handleGraphEvents batch).1.rawBatches_cancelledGroups_subset rest
      rw [State.rawBatches_state] at cancellation
      have combined := (frame.handleGraphEvents_conserves generated canonical batch
        (valid.prefix earlier) running accepted).append retained cancellation
      simpa only [State.rawBatches, State.replayBatches, List.foldl_cons] using combined

/-- Initialization supplies source provenance and complete buffered link inventories. -/
theorem initial_bufferedStreamSourceFrame {work parents} (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    : BufferedStreamSourceFrame (State.initialize (Work.fromExecution work)) work parents
        [] :=
  ⟨
    initial_objectStreamReplayFrame generated canonical,
    createWorkQueue_storedTaskLinks _,
    createWorkQueue_childStreamInventory _
  ⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
