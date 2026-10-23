import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SuccessfulRetirement
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamReleaseOwnerReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ItemStreamRelease
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamNoticeMetadata

/-! Active object-produced streams retain their actual successful, retired support. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Proof evidence for stream activation at a consumed source cut, including inside a batch.
The support is a previously released contributing owner, not a new runtime record. -/
structure ObjectStreamReplayFrame (queue : State) (work : Execution.Work)
    (parents : Nat → NodeRefs) (before : List GraphEvent)
    : Prop where
  source : UncancelledReplayFrame queue work parents before
  publications
    : ∃ published, queue.PublicationInventory (ObjectValueFrom before) published
  settled : queue.ChildStreamsSettled
  links : queue.ChildStreamsMatchWork work
  streams : queue.StreamsSatisfy (StreamLocated work)
  support
    : ∀ stream dependencies address,
        NodeAt work stream .stream dependencies (some (.executionGroup address))
        → stream.ref ∈ queue.rootStreams
        → ∃ ref ∈ dependencies,
            UncancelledRetirement queue ref
            ∧ Occurrence.executionGroup address ∈ before.flatMap GraphEvent.successes

/-- Pending internal notices change no publication or stream-support certificate. -/
theorem ObjectStreamReplayFrame.withGroupFailures {queue work parents before}
    (frame : ObjectStreamReplayFrame queue work parents before)
    (groupFailureEvents : List GroupFailureEvent)
    : ObjectStreamReplayFrame { queue with groupFailureEvents } work parents before := by
  obtain ⟨published, inventory⟩ := frame.publications
  exact ⟨frame.source.withGroupFailures groupFailureEvents,
    ⟨published, ⟨inventory.unique, inventory.provenance, inventory.stored⟩⟩,
    frame.settled, frame.links, frame.streams, frame.support⟩

/-- Activation obtains producer settlement and retired support from the same actual handler.
Old support persists structurally; new item-produced notices cannot be object-produced. -/
theorem ObjectStreamReplayFrame.handleGraphEvent_ofSourceFrame {queue work parents before}
    (frame : ObjectStreamReplayFrame queue work parents before)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (event : GraphEvent) (valid : ValidGraphEvents work (before ++ [event]))
    (available : List (Occurrence × Nat))
    (_licensed
      : ∀ occurrence errors,
          (occurrence, errors) ∈ available
          → (GraphEvent.taskFailure occurrence errors).MatchesWork work)
    (sourceAfter
      : UncancelledReplayFrame (queue.handleGraphEvent event available).1
          work parents (before ++ [event]))
    (itemsLive
      : ∀ stream items,
          event = .streamItems stream items
          → queue.acceptsGraphEvent (.streamItems stream items) = true)
    : ObjectStreamReplayFrame (queue.handleGraphEvent event available).1 work parents
        (before ++ [event]) := by
  obtain ⟨matching, fresh, _⟩ := valid.atPrefix (List.prefix_refl _)
  obtain ⟨published, inventory⟩ := frame.publications
  have current := inventory.mono (fun _ _ source =>
    source.mono (List.subset_append_left before [event]))
  obtain ⟨added, _, after, release⟩ := current.handleGraphEvent_streamRelease frame.settled
    frame.links generated event matching (by
      intro occurrence result same
      subst event
      exact ⟨⟨result, List.mem_append_right _ List.mem_cons_self, rfl⟩,
        inventory.fresh_success fresh⟩) available
  refine ⟨
    sourceAfter,
    ⟨published ++ added, after⟩,
    frame.settled.handleGraphEvent event available,
    frame.links.handleGraphEvent matching available,
    frame.streams.handleGraphEvent event matching.childStreamsLocated available,
    ?_
  ⟩
  intro stream dependencies address known active
  rcases List.mem_append.mp (queue.handleGraphEvent_streamRoots event available active)
      with earlier | newly
  · obtain ⟨ref, dependency, retired, success⟩ :=
      frame.support stream dependencies address known earlier
    refine ⟨ref, dependency, retired.handleGraphEvent event available, ?_⟩
    simpa only [List.flatMap_append] using List.mem_append_left
      ([event].flatMap GraphEvent.successes) success
  · obtain ⟨output, emitted, noticed⟩ := List.mem_flatMap.mp newly
    have located := frame.streams.handleGraphEvent_notices event matching.childStreamsLocated
      available output emitted
    cases output with
    | groupSuccess group groups streams =>
        obtain ⟨child, member, same⟩ := List.mem_map.mp noticed
        obtain ⟨owners, producer, descriptor⟩ := located child member
        have producerEq := generated.streamProducer_unique descriptor known same
        have depsEq := generated.streamDependencies_unique descriptor known same
        have childKnown := producerEq ▸ descriptor
        obtain ⟨_, _, retired⟩ := State.handleGraphEvent_successfulRetirements
          frame.source.parent frame.source.cancellations generated canonical event matching
          available group groups streams emitted
        have dependency := State.handleGraphEvent_streamDependencies generated
          frame.source.pending.sound frame.source.pending.matching frame.links event matching
          available group groups streams emitted child member owners _ childKnown
        obtain ⟨index, atEvent⟩ := List.mem_iff_getElem?.mp emitted
        obtain ⟨occurrence, producerSame, delivered⟩ :=
          release index group groups streams atEvent child member owners _ childKnown
        have occurrenceEq := Option.some.inj producerSame
        obtain ⟨entry, earlier, equal⟩ := List.mem_map.mp delivered
        have source := after.provenance entry
          (List.mem_append_right published (List.mem_of_mem_take earlier))
        obtain ⟨result, received, _⟩ := source
        refine ⟨group.ref, depsEq ▸ dependency, retired, ?_⟩
        apply List.mem_flatMap.mpr
        refine ⟨_, received, ?_⟩
        simpa only [GraphEvent.successes, List.mem_singleton]
          using (equal.trans occurrenceEq.symm).symm
    | streamValues owner values groups streams =>
        obtain ⟨child, member, same⟩ := List.mem_map.mp noticed
        obtain ⟨index, atEvent⟩ := List.mem_iff_getElem?.mp emitted
        obtain ⟨occurrence, descriptor, _⟩ :=
          queue.handleGraphEvent_itemStreamRelease_of_itemsStarted event matching available
            itemsLive
            index owner values groups streams atEvent child member
        have depsEq := generated.streamDependencies_unique descriptor known same
        obtain ⟨ancestor, path, result, producerTask⟩ :=
          NodeAt.stream_objectProducer_owners known
        exact False.elim (generated.taskOwners_nonempty producerTask depsEq.symm)
    | groupValues | groupFailure | streamSuccess | streamFailure | workQueueTermination =>
        cases noticed

/-- Strict eventwise input checks specialize the source-frame preservation step. -/
theorem ObjectStreamReplayFrame.handleGraphEvent {queue work parents before}
    (frame : ObjectStreamReplayFrame queue work parents before)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (event : GraphEvent) (valid : ValidGraphEvents work (before ++ [event]))
    (accepted : queue.acceptsGraphEvent event = true)
    (available : List (Occurrence × Nat))
    (licensed
      : ∀ occurrence errors,
          (occurrence, errors) ∈ available
          → (GraphEvent.taskFailure occurrence errors).MatchesWork work)
    : ObjectStreamReplayFrame (queue.handleGraphEvent event available).1 work parents
        (before ++ [event]) :=
  frame.handleGraphEvent_ofSourceFrame generated canonical event valid available licensed
    (frame.source.handleGraphEvent generated canonical event valid accepted available
      licensed)
    (fun _ _ same => same ▸ accepted)

/-- The support certificate follows the exact FIFO replay under one fixed cache snapshot. -/
theorem ObjectStreamReplayFrame.replayGraphEvents {queue work parents before}
    (frame : ObjectStreamReplayFrame queue work parents before)
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
    : ObjectStreamReplayFrame (queue.replayGraphEvents events available) work parents
        (before ++ events) := by
  induction events generalizing queue before with
  | nil =>
      simpa only [List.append_nil, State.replayGraphEvents, List.foldl_nil] using frame
  | cons event rest ih =>
      have checked
          : queue.acceptsGraphEvent event = true
            ∧ State.eventsStarted available (queue.dispatchGraphEvent event available).1
                rest
              = true := by
        simpa only [State.eventsStarted, Bool.and_eq_true] using accepted
      have next : ObjectStreamReplayFrame (queue.dispatchGraphEvent event available).1
          work parents (before ++ [event]) := frame.handleGraphEvent generated canonical event
        (valid.prefix ⟨rest, by simp⟩) checked.1 available licensed |>.withGroupFailures _
      have final := ih next (by simpa only [List.append_assoc, List.singleton_append] using valid)
        checked.2
      simpa only [State.replayGraphEvents, List.foldl_cons, List.append_assoc,
        List.singleton_append]
        using final

/-- Buffered replay supplies exact source frames independently at every FIFO prefix.
Only item callbacks require current stream liveness for the release-support argument.
-/
theorem ObjectStreamReplayFrame.replayGraphEvents_admitted {queue work parents before}
    (frame : ObjectStreamReplayFrame queue work parents before)
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
    : ObjectStreamReplayFrame (queue.replayGraphEvents events available) work parents
        (before ++ events) := by
  have sourceAt (fifo : List GraphEvent) (earlier : fifo.IsPrefix events) :
      UncancelledReplayFrame (queue.replayGraphEvents fifo available) work parents
        (before ++ fifo) := by
    obtain ⟨tail, joined⟩ := earlier
    apply frame.source.replayGraphEvents_admitted generated canonical fifo
      (valid.prefix ⟨tail, by rw [List.append_assoc, joined]⟩) available licensed
    apply State.acceptsBatch_go_prefix (after := tail)
    simpa only [joined] using accepted
  apply prefix_invariant events
    (fun fifo =>
      ObjectStreamReplayFrame (queue.replayGraphEvents fifo available) work parents
        (before ++ fifo))
  · simpa only [State.replayGraphEvents, List.foldl_nil, List.append_nil] using frame
  · intro fifo event rest split past
    have validCut := valid.prefix (show (before ++ fifo ++ [event]).IsPrefix (before ++ events) from
      ⟨rest, by simp [split, List.append_assoc]⟩)
    have current := past fifo (List.prefix_refl _)
    have sourceAfter : UncancelledReplayFrame
        ((queue.replayGraphEvents fifo available).handleGraphEvent event available).1
        work parents ((before ++ fifo) ++ [event]) := by
      have next := sourceAt (fifo ++ [event]) ⟨rest, by simp [split, List.append_assoc]⟩
      have restored := next.withGroupFailures
        (((queue.replayGraphEvents fifo available).handleGraphEvent event available).1.groupFailureEvents)
      simpa only [State.replayGraphEvents_append, State.replayGraphEvents,
        List.foldl_append, List.foldl_cons, List.foldl_nil, List.append_assoc,
        State.dispatchGraphEvent, State.enqueueGroupFailures] using restored
    have itemsLive : ∀ stream items, event = .streamItems stream items →
        (queue.replayGraphEvents fifo available).acceptsGraphEvent (.streamItems stream items) = true := by
      intro stream items same
      subst event
      obtain ⟨seen, seenPrefix, eligible⟩ := queue.acceptsBatch_go_eachAccepted events fifo
        (.streamItems stream items) available accepted ⟨rest, by simp [split]⟩
      obtain ⟨remaining, history⟩ := seenPrefix
      obtain ⟨address, results, producer, dependencies, located, nonempty, unclosed, rest⟩ :=
        validCut.last_ready
      have unclosedRemaining : stream.ref ∉ remaining.flatMap (fun event => event.identities.2) := by
        intro member
        apply unclosed
        rw [← history, List.flatMap_append, List.flatMap_append]
        exact List.mem_append_right _ (List.mem_append_right _ member)
      rw [← history, State.replayGraphEvents_append queue seen remaining available]
      exact List.contains_iff_mem.mpr ((queue.replayGraphEvents seen available
        ).replayGraphEvents_retains_unclosed_stream remaining stream.ref
          (List.contains_iff_mem.mp eligible) unclosedRemaining available)
    have next : ObjectStreamReplayFrame
        ((queue.replayGraphEvents fifo available).dispatchGraphEvent event available).1
        work parents ((before ++ fifo) ++ [event]) :=
      current.handleGraphEvent_ofSourceFrame generated canonical event validCut
      available licensed sourceAfter itemsLive |>.withGroupFailures _
    simpa only [State.replayGraphEvents_append, State.replayGraphEvents,
      List.foldl_append, List.foldl_cons, List.foldl_nil, List.append_assoc] using next

/-- Termination changes only the control flag, retaining support and publication evidence. -/
theorem ObjectStreamReplayFrame.withTerminated {queue work parents before}
    (frame : ObjectStreamReplayFrame queue work parents before) (terminated : Bool)
    : ObjectStreamReplayFrame { queue with terminated } work parents before := by
  obtain ⟨published, inventory⟩ := frame.publications
  exact ⟨frame.source.withTerminated terminated,
    ⟨published, ⟨inventory.unique, inventory.provenance, inventory.stored⟩⟩,
    frame.settled, frame.links, frame.streams, fun stream dependencies address known active => by
      obtain ⟨ref, member, retired, success⟩ :=
        frame.support stream dependencies address known active
      exact ⟨ref, member, retired.withTerminated terminated, success⟩⟩

/-- Batch-end forwarding and termination leave the support established by immediate handlers. -/
theorem ObjectStreamReplayFrame.handleGraphEvents {queue work parents before}
    (frame : ObjectStreamReplayFrame queue work parents before)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (events : List GraphEvent) (valid : ValidGraphEvents work (before ++ events))
    (running : queue.terminated = false) (accepted : queue.acceptsBatch events = true)
    : ObjectStreamReplayFrame (queue.handleGraphEvents events).1 work parents
        (before ++ events) := by
  have licensed : ∀ occurrence errors,
      (occurrence, errors) ∈ GraphEvent.availableFailures events →
        (GraphEvent.taskFailure occurrence errors).MatchesWork work := by
    intro occurrence errors member
    obtain ⟨event, received, same⟩ := List.mem_filterMap.mp member
    cases event <;> simp only [Option.some.injEq, reduceCtorEq, Prod.mk.injEq] at same
    obtain ⟨rfl, rfl⟩ := same
    exact valid.eachMatches (List.mem_append_right _ received)
  have replayed := frame.replayGraphEvents_admitted generated canonical events valid
    (GraphEvent.availableFailures events) licensed accepted
  obtain ⟨terminal, same⟩ := queue.handleGraphEvents_stateCore events running
  rw [same]
  exact replayed.withTerminated terminal

/-- Actual earlier host batches preserve stream support using their own availability snapshots. -/
theorem ObjectStreamReplayFrame.runNormalized {queue work parents before}
    (frame : ObjectStreamReplayFrame queue work parents before)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work (before ++ batches.flatten))
    (started : queue.batchesStarted batches = true)
    : ObjectStreamReplayFrame (queue.runNormalized batches).1 work parents
        (before ++ batches.flatten) := by
  rw [State.runNormalized_replayBatches]
  induction batches generalizing queue before with
  | nil =>
      simpa only [List.flatten_nil, List.append_nil, State.replayBatches, List.foldl_nil]
        using frame
  | cons batch rest ih =>
      obtain ⟨running, accepted, restStarted⟩ := queue.batchesStarted_cons batch rest started
      have next := frame.handleGraphEvents generated canonical batch
        (valid.prefix ⟨rest.flatten, by simp [List.append_assoc]⟩) running accepted
      have retained := ih next (by simpa only [List.flatten_cons, List.append_assoc] using valid)
        restStarted
      simpa only [State.replayBatches, List.foldl_cons, List.flatten_cons,
        List.append_assoc]
        using retained

/-- Initial stream roots have no object producer, so support starts without any such roots. -/
theorem initial_objectStreamReplayFrame {work parents} (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    : ObjectStreamReplayFrame (State.initialize (Work.fromExecution work)) work parents
        [] := by
  have streams := (createWorkQueue_initialStreams_nodeAt work).1
  refine ⟨
    initial_uncancelledReplayFrame generated canonical,
    ⟨[], ⟨by simp, by simp, createWorkQueue_storedValues _ _⟩⟩,
    createWorkQueue_childStreamsSettled _,
    createWorkQueue_childStreamsMatchWork _ _,
    (fun stream member => ⟨[], none, streams stream member⟩),
    ?_
  ⟩
  intro stream dependencies address known active
  have initial := createWorkQueue_streamRoots (Work.fromExecution work) active
  cases generated.initialStream_producerNone known initial

/-- Active-stream support is available at each real batch/FIFO input cut. -/
theorem ExecutedWork.objectStreamFrame_atBatchPrefix {work : Execution.Work}
    {parents : Nat → NodeRefs} (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (earlier : List (List GraphEvent)) (batch : List GraphEvent)
    (later : List (List GraphEvent)) (fifo : List GraphEvent)
    (valid : ValidGraphEvents work (earlier ++ batch :: later).flatten)
    (started : inputsStarted work (earlier ++ batch :: later) = true)
    (prefixOfBatch : fifo.IsPrefix batch)
    : ObjectStreamReplayFrame
        (((State.initialize (Work.fromExecution work)).replayBatches
            earlier).replayGraphEvents
          fifo (GraphEvent.availableFailures batch))
        work parents (earlier.flatten ++ fifo) := by
  let initial := State.initialize (Work.fromExecution work)
  have checked : initial.batchesStarted (earlier ++ batch :: later) = true := by
    rwa [← inputsStarted_eq_batchesStarted]
  rw [State.batchesStarted_append, Bool.and_eq_true] at checked
  have validEarlier : ValidGraphEvents work earlier.flatten :=
    valid.prefix ⟨(batch :: later).flatten, by simp [List.flatten_append]⟩
  have before := (initial_objectStreamReplayFrame generated canonical).runNormalized
    (before := []) generated canonical earlier validEarlier checked.1
  rw [State.runNormalized_replayBatches] at before
  simp only [List.nil_append] at before
  obtain ⟨_, accepted, _⟩ :=
    (initial.replayBatches earlier).batchesStarted_cons batch later checked.2
  obtain ⟨tail, same⟩ := prefixOfBatch
  have fifoAccepted : State.acceptsBatch.go (fun _ => false)
      (GraphEvent.availableFailures batch) (initial.replayBatches earlier) fifo = true := by
    apply State.acceptsBatch_go_prefix (after := tail)
    simpa only [State.acceptsBatch, same] using accepted
  have validFifo : ValidGraphEvents work (earlier.flatten ++ fifo) := by
    apply valid.prefix
    refine ⟨tail ++ later.flatten, ?_⟩
    simp only [List.flatten_append, List.flatten_cons, ← same, List.append_assoc]
  have licensed : ∀ occurrence errors,
      (occurrence, errors) ∈ GraphEvent.availableFailures batch →
        (GraphEvent.taskFailure occurrence errors).MatchesWork work := by
    intro occurrence errors member
    obtain ⟨event, received, identity⟩ := List.mem_filterMap.mp member
    cases event <;> simp only [Option.some.injEq, reduceCtorEq, Prod.mk.injEq] at identity
    obtain ⟨rfl, rfl⟩ := identity
    apply valid.eachMatches
    simp only [List.flatten_append, List.flatten_cons]
    exact List.mem_append_right _ (List.mem_append_left _ received)
  exact before.replayGraphEvents_admitted generated canonical fifo validFifo
    (GraphEvent.availableFailures batch) licensed fifoAccepted

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
