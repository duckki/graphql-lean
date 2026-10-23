import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SuccessfulOwnerAccounting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.BatchOutputReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.MembershipExclusionWitness

/-! Successful-owner accounting follows actual batch slices of one publication ledger. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Source accounting and successful-value tracking refer to the same actual queue cut. -/
structure OwnerPublicationFrame (queue : State) (work : Execution.Work)
    (parents : Nat → NodeRefs) (before : List GraphEvent)
    (published : List ObjectPublication)
    : Prop where
  source : UncancelledReplayFrame queue work parents before
  accounted : queue.SuccessfulOwnersAccounted work before published

/-- One actual FIFO replay extends the original publication list by its consumed slice. -/
theorem OwnerPublicationFrame.replayGraphEvents
    {queue work parents before published added}
    (frame : OwnerPublicationFrame queue work parents before published)
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
    (covered : queue.ReplayClosuresCovered events added available)
    : OwnerPublicationFrame (queue.replayGraphEvents events available) work parents
        (before ++ events)
        (published
          ++ added.take
              ((queue.rawEventReplay events available).2.flatMap
                WorkQueueEvent.objectValues).length) := by
  induction events generalizing queue before published added with
  | nil => simpa only [State.replayGraphEvents, State.rawEventReplay, List.foldl_nil,
      List.flatMap_nil, List.length_nil, List.take_zero, List.append_nil] using frame
  | cons event rest ih =>
      have checked : queue.acceptsGraphEvent event = true ∧
          State.eventsStarted available (queue.dispatchGraphEvent event available).1 rest
            = true := by
        simpa only [State.eventsStarted, Bool.and_eq_true] using accepted
      have firstValid := valid.prefix (show (before ++ [event]).IsPrefix
        (before ++ event :: rest) from ⟨rest, by simp⟩)
      have single := State.ReplayClosuresCovered.prefix [event] rest covered
      have next : OwnerPublicationFrame (queue.dispatchGraphEvent event available).1 work parents
          (before ++ [event]) (published ++ added.take
            ((queue.dispatchGraphEvent event available).2.flatMap
              WorkQueueEvent.objectValues).length)
          := ⟨frame.source.handleGraphEvent generated canonical event firstValid checked.1
            available licensed |>.withGroupFailures _,
            frame.accounted.handleGraphEvent frame.source event firstValid checked.1 available
              single⟩
      have retained := ih next
        (by simpa only [List.append_assoc, List.singleton_append] using valid)
        checked.2 covered.tail
      simpa only [State.replayGraphEvents, List.foldl_cons,
        State.rawEventReplay_cons _ _ _ available, List.flatMap_append,
        List.length_append, List.take_add, List.append_assoc, List.singleton_append]
        using retained

/-- Buffered source replay retains exact successful-value accounting on the same ledger.
At a fresh success, an uncancelled contributor forces a live task; callbacks without such
contributors need no published-or-buffered value. Source frames retain the full snapshot.
-/
theorem OwnerPublicationFrame.replayGraphEvents_admitted
    {queue work parents before published added}
    (frame : OwnerPublicationFrame queue work parents before published)
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
    (covered : queue.ReplayClosuresCovered events added available)
    : OwnerPublicationFrame (queue.replayGraphEvents events available) work parents
        (before ++ events)
        (published
          ++ added.take
              ((queue.rawEventReplay events available).2.flatMap
                WorkQueueEvent.objectValues).length) := by
  have sourceAt (fifo : List GraphEvent) (earlier : fifo.IsPrefix events) :
      UncancelledReplayFrame (queue.replayGraphEvents fifo available) work parents
        (before ++ fifo) := by
    obtain ⟨tail, joined⟩ := earlier
    apply frame.source.replayGraphEvents_admitted generated canonical fifo
      (valid.prefix ⟨tail, by rw [List.append_assoc, joined]⟩) available licensed
    apply State.acceptsBatch_go_prefix (after := tail)
    simpa only [joined] using accepted
  have loop (remaining fifo : List GraphEvent) (split : events = fifo ++ remaining)
      (publishedNow localPublications : List ObjectPublication)
      (current : OwnerPublicationFrame (queue.replayGraphEvents fifo available) work parents
        (before ++ fifo) publishedNow)
      (coverage : (queue.replayGraphEvents fifo available).ReplayClosuresCovered remaining
        localPublications available)
      : OwnerPublicationFrame
          ((queue.replayGraphEvents fifo available).replayGraphEvents remaining available)
          work parents ((before ++ fifo) ++ remaining)
          (publishedNow ++ localPublications.take
            (((queue.replayGraphEvents fifo available).rawEventReplay remaining available
              ).2.flatMap WorkQueueEvent.objectValues).length) := by
    induction remaining generalizing fifo publishedNow localPublications with
    | nil => simpa only [State.replayGraphEvents, State.rawEventReplay, List.foldl_nil,
        List.flatMap_nil, List.length_nil, List.take_zero, List.append_nil] using current
    | cons event rest ih =>
        have boundary : (before ++ fifo ++ [event]).IsPrefix (before ++ events) :=
          ⟨rest, by simp [split, List.append_assoc]⟩
        have validCut := valid.prefix boundary
        have tracked : ∀ occurrence result, event = .taskSuccess occurrence result
            → (queue.replayGraphEvents fifo available).StartedTaskDisposition occurrence
              ∧ ∃ task ∈ (queue.replayGraphEvents fifo available).tasks,
                  task.occurrence = occurrence := by
          intro occurrence result same
          subst event
          obtain ⟨seen, seenPrefix, eligible⟩ := queue.acceptsBatch_go_eachAccepted events fifo
            (.taskSuccess occurrence result) available accepted ⟨rest, by simp [split]⟩
          have prior := sourceAt seen (seenPrefix.trans ⟨.taskSuccess occurrence result :: rest, split.symm⟩)
          cases found : (queue.replayGraphEvents seen available).taskNode? occurrence with
          | none => simp [State.acceptsGraphEvent, found] at eligible
          | some node =>
              obtain ⟨remaining, history⟩ := seenPrefix
              have disposition :=
                prior.pending.startedTaskDisposition_atPrefix found prior.producers
                  prior.producerOrder remaining
                  (by
                    simpa [history, List.append_assoc]
                      using (validGraphEvents_last validCut).1)
                  available
              rw [← history, State.replayGraphEvents_append queue seen remaining available]
              exact ⟨
                disposition,
                node.task,
                (queue.replayGraphEvents seen available).replayGraphEvents_tasks_subset
                  remaining available
                  (prior.pending.started node (List.mem_of_find?_eq_some found)),
                (State.taskNode?_some found).2
              ⟩
        let consumed := ((queue.replayGraphEvents fifo available).dispatchGraphEvent event
          available).2.flatMap WorkQueueEvent.objectValues
        have nextFrame : OwnerPublicationFrame
            ((queue.replayGraphEvents fifo available).dispatchGraphEvent event available).1
            work parents ((before ++ fifo) ++ [event])
            (publishedNow ++ localPublications.take consumed.length) := by
          refine ⟨
            ?_,
            current.accounted.handleGraphEvent_ofDisposition current.source event validCut
              available (State.ReplayClosuresCovered.prefix [event] rest coverage) tracked
          ⟩
          simpa only [State.replayGraphEvents_append, State.replayGraphEvents,
            List.foldl_append, List.foldl_cons, List.foldl_nil, List.append_assoc]
            using sourceAt (fifo ++ [event]) ⟨rest, by simp [split, List.append_assoc]⟩
        have result := ih (fifo ++ [event]) (by simp [split, List.append_assoc])
          (publishedNow ++ localPublications.take consumed.length)
          (localPublications.drop consumed.length)
          (by simpa only [State.replayGraphEvents_append, State.replayGraphEvents,
            List.foldl_append, List.foldl_cons, List.foldl_nil, List.append_assoc] using nextFrame)
          (by simpa only [State.replayGraphEvents_append, State.replayGraphEvents,
            List.foldl_append, List.foldl_cons, List.foldl_nil, consumed] using coverage.tail)
        simpa only [State.replayGraphEvents_append, State.replayGraphEvents,
          List.foldl_append, List.foldl_cons, List.foldl_nil,
          State.rawEventReplay_cons _ _ _ available, List.flatMap_append,
          List.length_append, List.take_add, List.append_assoc, List.singleton_append,
          consumed]
          using result
  simpa only [State.replayGraphEvents, List.foldl_nil, List.nil_append, List.append_nil]
    using loop events [] (by simp) published added
      (by
        simpa only [State.replayGraphEvents, List.foldl_nil, List.append_nil] using frame)
      covered

/-- The terminal flag does not change source or successful-value accounting. -/
theorem OwnerPublicationFrame.withTerminated {queue work parents before published}
    (frame : OwnerPublicationFrame queue work parents before published)
    (terminated : Bool)
    : OwnerPublicationFrame { queue with terminated } work parents before published :=
  ⟨frame.source.withTerminated terminated, frame.accounted.withTerminated terminated⟩

/-- Forwarded startup failures carry no object values and retain the same ledger slice. -/
theorem OwnerPublicationFrame.handleGraphEvents
    {queue work parents before published added}
    (frame : OwnerPublicationFrame queue work parents before published)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (events : List GraphEvent) (valid : ValidGraphEvents work (before ++ events))
    (running : queue.terminated = false) (accepted : queue.acceptsBatch events = true)
    (covered
      : queue.ReplayClosuresCovered events added (GraphEvent.availableFailures events))
    : OwnerPublicationFrame (queue.handleGraphEvents events).1 work parents
        (before ++ events)
        (published
          ++ added.take
              ((queue.handleGraphEvents events).2.flatMap
                WorkQueueEvent.objectValues).length) := by
  have licensed : ∀ occurrence errors,
      (occurrence, errors) ∈ GraphEvent.availableFailures events →
        (GraphEvent.taskFailure occurrence errors).MatchesWork work := by
    intro occurrence errors member
    obtain ⟨event, received, same⟩ := List.mem_filterMap.mp member
    cases event <;> simp only [Option.some.injEq, reduceCtorEq, Prod.mk.injEq] at same
    obtain ⟨rfl, rfl⟩ := same
    exact valid.eachMatches (List.mem_append_right _ received)
  have replayed := frame.replayGraphEvents_admitted generated canonical events valid
    (GraphEvent.availableFailures events) licensed accepted covered
  rw [queue.handleGraphEvents_objectValues events running]
  obtain ⟨terminal, same⟩ := queue.handleGraphEvents_stateCore events running
  rw [same]
  exact replayed.withTerminated terminal

/-- Actual host batches compose their consecutive publication slices without flattening state. -/
theorem OwnerPublicationFrame.rawBatches {queue work parents before published added}
    (frame : OwnerPublicationFrame queue work parents before published)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work (before ++ batches.flatten))
    (started : queue.batchesStarted batches = true)
    (covered : queue.BatchClosuresCovered batches added)
    : OwnerPublicationFrame (queue.rawBatches batches).1 work parents
        (before ++ batches.flatten)
        (published
          ++ added.take
              ((queue.rawBatches batches).2.flatMap
                WorkQueueEvent.objectValues).length) := by
  induction batches generalizing queue before published added with
  | nil =>
      simpa only [State.rawBatches, List.flatten_nil, List.flatMap_nil, List.length_nil,
        List.take_zero, List.append_nil] using frame
  | cons batch rest ih =>
      obtain ⟨running, accepted, remaining⟩ := queue.batchesStarted_cons batch rest started
      have next := frame.handleGraphEvents generated canonical batch
        (valid.prefix ⟨rest.flatten, by simp [List.append_assoc]⟩) running accepted covered.1
      simp only [List.take_take, Nat.min_self] at next
      have final := ih next (by simpa only [List.flatten_cons, List.append_assoc] using valid)
        remaining covered.2.2
      simpa only [State.rawBatches, List.flatten_cons, List.flatMap_append,
        List.length_append, List.take_add, List.append_assoc]
        using final

/-- Initial accounting contains neither consumed successes nor object publications. -/
theorem initial_ownerPublicationFrame {work parents} (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    : OwnerPublicationFrame (State.initialize (Work.fromExecution work)) work parents []
        [] :=
  ⟨initial_uncancelledReplayFrame generated canonical, .empty _ _⟩

/-- Every real batch/FIFO source cut retains exact accounting on the original ledger prefix. -/
theorem ExecutedWork.ownerPublicationFrame_atBatchPrefix
    {work parents batches published} (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    (covered
      : (State.initialize (Work.fromExecution work)).BatchClosuresCovered batches
          published)
    (earlier : List (List GraphEvent)) (batch : List GraphEvent)
    (later : List (List GraphEvent)) (fifo : List GraphEvent)
    (partition : batches = earlier ++ batch :: later) (fifoPrefix : fifo.IsPrefix batch)
    : let initial := State.initialize (Work.fromExecution work)
      let current := initial.replayBatches earlier
      let available := GraphEvent.availableFailures batch
      let offset :=
        ((initial.rawBatches earlier).2.flatMap WorkQueueEvent.objectValues).length
      let count :=
        ((current.rawEventReplay fifo available).2.flatMap
          WorkQueueEvent.objectValues).length
      OwnerPublicationFrame (current.replayGraphEvents fifo available) work parents
        (earlier.flatten ++ fifo) (published.take (offset + count)) := by
  let initial := State.initialize (Work.fromExecution work)
  let current := initial.replayBatches earlier
  let available := GraphEvent.availableFailures batch
  let offset := ((initial.rawBatches earlier).2.flatMap WorkQueueEvent.objectValues).length
  let count := ((current.handleGraphEvents batch).2.flatMap WorkQueueEvent.objectValues).length
  let localCount := ((current.rawEventReplay fifo available).2.flatMap
    WorkQueueEvent.objectValues).length
  have batchStarts : initial.batchesStarted (earlier ++ batch :: later) = true := by
    rw [← partition, ← inputsStarted_eq_batchesStarted]
    exact started
  rw [State.batchesStarted_append, Bool.and_eq_true] at batchStarts
  have priorValid : ValidGraphEvents work earlier.flatten := valid.prefix
    ⟨(batch :: later).flatten, by simp [partition]⟩
  have priorLedger := State.BatchClosuresCovered.prefix earlier (batch :: later)
    (partition ▸ covered)
  have beforeFrame := (initial_ownerPublicationFrame generated canonical).rawBatches
    generated canonical earlier priorValid batchStarts.1 priorLedger
  rw [State.rawBatches_state] at beforeFrame
  simp only [List.nil_append] at beforeFrame
  obtain ⟨suffix, batchEq⟩ := fifoPrefix
  obtain ⟨running, accepted, _⟩ := current.batchesStarted_cons batch later batchStarts.2
  have atBatch := State.BatchClosuresCovered.atBatch earlier batch later (partition ▸ covered)
  have fifoCovered := State.ReplayClosuresCovered.prefix fifo suffix (show
      current.ReplayClosuresCovered (fifo ++ suffix) ((published.drop offset).take count)
        available from by rw [batchEq]; exact atBatch.1)
  have fifoValid : ValidGraphEvents work (earlier.flatten ++ fifo) := valid.prefix
    ⟨suffix ++ later.flatten, by simp [partition, ← batchEq, List.append_assoc]⟩
  have fifoAccepted : State.acceptsBatch.go (fun _ => false) available current fifo = true := by
    apply State.acceptsBatch_go_prefix (after := suffix)
    simpa only [State.acceptsBatch, batchEq] using accepted
  have licensed : ∀ occurrence errors, (occurrence, errors) ∈ available →
      (GraphEvent.taskFailure occurrence errors).MatchesWork work := by
    intro occurrence errors member
    obtain ⟨event, received, same⟩ := List.mem_filterMap.mp member
    cases event <;> simp only [Option.some.injEq, reduceCtorEq, Prod.mk.injEq] at same
    obtain ⟨rfl, rfl⟩ := same
    apply valid.eachMatches
    rw [partition, List.flatten_append, List.flatten_cons]
    exact List.mem_append_right _ (List.mem_append_left _ received)
  have localLe : localCount ≤ count := by
    have same := congrArg (fun events => current.rawEventReplay events available) batchEq.symm
    have append := current.rawEventReplay_append fifo suffix available
    have lengths := congrArg (fun result : State × List WorkQueueEvent =>
      (result.2.flatMap WorkQueueEvent.objectValues).length) (same.trans append)
    have batchValues := congrArg List.length (current.handleGraphEvents_objectValues batch running)
    dsimp only [localCount, count, available]
    simp only [List.flatMap_append, List.length_append] at lengths
    dsimp only [available] at lengths
    omega
  have final := beforeFrame.replayGraphEvents_admitted generated canonical fifo fifoValid available
    licensed fifoAccepted fifoCovered
  change OwnerPublicationFrame (current.replayGraphEvents fifo available) work parents
    (earlier.flatten ++ fifo)
    (published.take offset ++ ((published.drop offset).take count).take localCount) at final
  rw [List.take_take, Nat.min_eq_left localLe, ← List.take_add] at final
  exact final

/-- Uncancelled retirement forces each structural object contributor into this ledger prefix.
Witness: registration and owner accounting identify its consumed success; successful-value
tracking excludes a retained live contributor at a retired ref. -/
theorem OwnerPublicationFrame.retired_structuralContributor_published
    {queue work parents before published address owners producer payload ref}
    (frame : OwnerPublicationFrame queue work parents before published)
    (generated : ExecutedWork work) (valid : ValidGraphEvents work before)
    (known : TaskAt work (.executionGroup address) owners producer payload)
    (contributes : ref ∈ owners) (retired : queue.RetiredGroup ref)
    (uncancelled : ref ∉ queue.cancelledGroups)
    : ∃ value, (Occurrence.executionGroup address, value) ∈ published := by
  obtain ⟨task, registered, occurrence, groups⟩ :=
    frame.source.retired_structuralContributor_registered generated valid known contributes
      retired uncancelled
  have settled := frame.source.owners.retired_contributor_settled registered
    (groups.symm ▸ contributes) uncancelled retired
  rw [occurrence] at settled
  obtain ⟨event, member, included⟩ := List.mem_flatMap.mp (List.mem_reverse.mp settled)
  cases event with
  | taskSuccess task result =>
      have same : task = .executionGroup address := (List.mem_singleton.mp included).symm
      subst task
      refine ⟨result.value, ?_⟩
      rcases frame.accounted (.executionGroup address) result member owners producer payload known
          ref contributes uncancelled with emitted | ⟨node, found, stored, owns, live⟩
      · exact emitted
      · exact False.elim (retired.2 live)
  | taskFailure | groupFailure | streamItems | streamSuccess | streamFailure =>
      cases included

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
