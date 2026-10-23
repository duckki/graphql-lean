import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialStartupSourceFrames
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SuccessfulOwnerReplay

/-! Successful-owner accounting retains the actual startup state and source-ledger slice. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- No source success has been consumed during initial synchronous activation. -/
theorem ExecutedWork.initialStartup_ownerPublicationFrame {work parents}
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (startup : InitialStartup) (matched : startup.MatchesWork work)
    : OwnerPublicationFrame
        (State.initialize (Work.fromExecution work) startup) work parents []
        [] :=
  ⟨generated.initialStartup_uncancelledReplayFrame canonical startup matched, .empty _ _⟩

/-- Every actual startup batch/FIFO cut interprets the original shared closure-ledger slice.
Its queue is initialized with synchronous availability. The source-handler ledger excludes
notification-only forwarding, which changes neither task state nor object-value prefixes.
-/
theorem ExecutedWork.startup_ownerPublicationFrame_atBatchPrefix
    {work parents batches published} (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (startup : InitialStartup) (matched : startup.MatchesWork work)
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches startup = true)
    (covered
      : ((State.initialize (Work.fromExecution work) startup)).BatchClosuresCovered
          batches published)
    (earlier : List (List GraphEvent)) (batch : List GraphEvent)
    (later : List (List GraphEvent)) (fifo : List GraphEvent)
    (partition : batches = earlier ++ batch :: later) (fifoPrefix : fifo.IsPrefix batch)
    : let initial := (State.initialize (Work.fromExecution work) startup)
      let current := initial.replayBatches earlier
      let available := GraphEvent.availableFailures batch
      let offset :=
        ((initial.rawBatches earlier).2.flatMap WorkQueueEvent.objectValues).length
      let count :=
        ((current.rawEventReplay fifo available).2.flatMap
          WorkQueueEvent.objectValues).length
      OwnerPublicationFrame (current.replayGraphEvents fifo available) work parents
        (earlier.flatten ++ fifo) (published.take (offset + count)) := by
  let initial := (State.initialize (Work.fromExecution work) startup)
  let current := initial.replayBatches earlier
  let available := GraphEvent.availableFailures batch
  let offset := ((initial.rawBatches earlier).2.flatMap WorkQueueEvent.objectValues).length
  let count := ((current.handleGraphEvents batch).2.flatMap WorkQueueEvent.objectValues).length
  let localCount := ((current.rawEventReplay fifo available).2.flatMap
    WorkQueueEvent.objectValues).length
  have batchStarts : initial.batchesStarted (earlier ++ batch :: later) = true := by
    rw [← partition, ← inputsStartedWithStartup_eq_batchesStarted]
    exact started
  rw [State.batchesStarted_append, Bool.and_eq_true] at batchStarts
  have priorValid : ValidGraphEvents work earlier.flatten := valid.prefix
    ⟨(batch :: later).flatten, by simp [partition]⟩
  have priorLedger := State.BatchClosuresCovered.prefix earlier (batch :: later)
    (partition ▸ covered)
  have beforeFrame :=
    (generated.initialStartup_ownerPublicationFrame canonical startup matched).rawBatches
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

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
