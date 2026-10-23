import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupStreamOrigins
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupSourceEventFrames
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupStreamCompletion
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ProducedStreamNoticeCoverage

/-! Root and item-produced startup streams are completely noticed and closed at termination. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Every successful source item announces every structural stream it generates.
Witness: recover the exact active item handler, derive its local complete notice, and
retain that notice through the earlier and later raw output segments. No completion,
output admission, or cancellation premise is supplied.
-/
theorem ExecutedWork.startup_itemProducedStream_rawNotice
    {work inputs node dependencies address index} (generated : ExecutedWork work)
    (startup : InitialStartup) (matched : startup.MatchesWork work)
    (valid : ValidGraphEvents work (List.flatten inputs))
    (started : inputsStarted work inputs startup = true)
    (known : NodeAt work node .stream dependencies (some (.item address index)))
    (success
      : Occurrence.item address index ∈ inputs.flatten.flatMap GraphEvent.successes)
    : node.ref
      ∈ (((State.initialize (Work.fromExecution work) startup)).rawBatches
          inputs).2.flatMap
          rawStreamNoticeRefs := by
  obtain ⟨before, stream, items, item, after, same, selected, identity⟩ :=
    valid.itemSuccess_input success
  have received : GraphEvent.streamItems stream items ∈ inputs.flatten := by
    rw [same]
    exact List.mem_append_right _ List.mem_cons_self
  obtain ⟨batch, included, member⟩ := List.mem_flatten.mp received
  obtain ⟨earlier, later, split⟩ := List.mem_iff_append.mp included
  obtain ⟨fifo, tail, batchEq⟩ := List.mem_iff_append.mp member
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  obtain ⟨localValid, _, _, _⟩ := generated.startup_uncancelledFrames_atBatchEvent startup matched
      canonical valid
    started earlier batch later fifo (.streamItems stream items) tail split batchEq
  obtain ⟨prior, matching, fresh⟩ := validGraphEvents_last localValid
  let initial := (State.initialize (Work.fromExecution work) startup)
  let available := GraphEvent.availableFailures batch
  let boundary := initial.replayBatches earlier
  let current := boundary.replayGraphEvents fifo available
  have starts := split ▸ started
  rw [inputsStartedWithStartup_eq_batchesStarted, State.batchesStarted_append, Bool.and_eq_true]
      at starts
  obtain ⟨running, batchAccepted, _⟩ := boundary.batchesStarted_cons batch later starts.2
  have batchValid : ValidGraphEvents work (earlier.flatten ++ batch) :=
    valid.prefix ⟨later.flatten, by simp [split, List.append_assoc]⟩
  have accepted : current.acceptsGraphEvent (.streamItems stream items) = true :=
    State.acceptsBatch_streamItems_live batchValid batchAccepted ⟨tail, by simp [batchEq]⟩
  have origins := generated.startup_batchPrefix_streamProducersSeen startup earlier fifo available
      prior
  have absent := (origins.cacheTaskFailures available).freshProducer_streamAbsent generated
    (identity.symm ▸ known) (fresh.2.2.1 item.occurrence (List.mem_map_of_mem selected))
  have active : (current.cacheTaskFailures available).rootStreams.contains stream.ref = true := by
    have cacheRoots := congrArg State.rootStreams (current.cacheTaskFailures_frame available)
    rw [cacheRoots]
    exact accepted
  have noticed := State.streamItems_fresh_notice stream items active selected
    (matching.itemChildStreams_complete selected (identity.symm ▸ known)) absent available
  have atHandler : node.ref ∈
      (current.handleGraphEvent (.streamItems stream items) available).2.1.flatMap
        rawStreamNoticeRefs := noticed
  have inBatch : node.ref ∈ (boundary.rawEventReplay batch available).2.flatMap
      rawStreamNoticeRefs := by
    rw [batchEq, State.rawEventReplay_append _ _ _ available]
    dsimp only
    rw [State.rawEventReplay_cons _ _ _ available, List.flatMap_append,
      List.flatMap_append, State.rawEventReplay_state _ fifo available]
    exact List.mem_append_right _ (List.mem_append_left _ atHandler)
  have forwarded : node.ref ∈ (boundary.handleGraphEvents batch).2.flatMap rawStreamNoticeRefs := by
    rw [State.handleGraphEvents_eq_rawEventReplay]
    simp only [running, Bool.false_eq_true, ↓reduceIte]
    split <;> simp only [List.flatMap_append]
    · exact List.mem_append_left _ inBatch
    · exact inBatch
  rw [split, State.rawBatches_append]
  dsimp only
  rw [State.rawBatches_state, State.rawBatches, List.flatMap_append, List.flatMap_append]
  exact List.mem_append_right _ (List.mem_append_left _ forwarded)

namespace ConformancePlan

/-- A successful item's structural child stream appears in the actual canonical notices.
Witness: complete raw item notices and exact normalization; source start laws supply the
active handler. No independent publication matching or failure witness is chosen.
-/
theorem startup_itemProducedStream_noticed {work inputs} {w : Witness}
    {node dependencies address index} (generated : ExecutedWork work)
    (startup : InitialStartup) (matched : startup.MatchesWork work)
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (history
      : let initial := State.initialize (Work.fromExecution work) startup
        w.events = initial.nonterminalAtoms inputs)
    (known : NodeAt work node .stream dependencies (some (.item address index)))
    (success
      : Occurrence.item address index ∈ inputs.flatten.flatMap GraphEvent.successes)
    : node.ref ∈ w.events.flatMap streamNoticeRefs := by
  rw [Witness.startup_streamNotices_eq_raw startup valid history]
  exact generated.startup_itemProducedStream_rawNotice startup matched valid started known
    success

/-- Every producer-free structural stream completes when actual replay terminates.
Witness: inverse initialization supplies its notice; the existing concrete completion
inventory forces its closure. Empty streams are included without an item-existence premise.
-/
theorem startup_terminal_rootStream_completed {work inputs} {w : Witness}
    {node dependencies} (startup : InitialStartup)
    (valid : ValidGraphEvents work inputs.flatten)
    (_started : inputsStarted work inputs startup = true)
    (history
      : let initial := State.initialize (Work.fromExecution work) startup
        w.events = initial.nonterminalAtoms inputs)
    (ended
      : let initial := State.initialize (Work.fromExecution work) startup
        (initial.runNormalized inputs).1.terminated = true)
    (known : NodeAt work node .stream dependencies none)
    : node.ref ∈ completedRefs w.events :=
  startup_streamNoticeRefs_terminalCompleted startup valid history ended
    (List.mem_append_left _ (NodeAt.stream_initial_notice known))

/-- Every child stream of a successful source item completes at actual termination.
Witness: complete item notice coverage and terminal stream tracking on the same history.
This includes a child whose producing outer stream later fails.
-/
theorem startup_terminal_itemProducedStream_completed {work inputs} {w : Witness}
    {node dependencies address index}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (matched : startup.MatchesWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (history
      : let initial := State.initialize (Work.fromExecution work) startup
        w.events = initial.nonterminalAtoms inputs)
    (ended
      : let initial := State.initialize (Work.fromExecution work) startup
        (initial.runNormalized inputs).1.terminated = true)
    (known : NodeAt work node .stream dependencies (some (.item address index)))
    (success
      : Occurrence.item address index ∈ inputs.flatten.flatMap GraphEvent.successes)
    : node.ref ∈ completedRefs w.events :=
  startup_streamNoticeRefs_terminalCompleted startup valid history ended
    (List.mem_append_right _
      (startup_itemProducedStream_noticed generated startup matched valid started history
        known success))

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
