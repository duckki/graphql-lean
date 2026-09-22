import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ImmediateStreamCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ProducedTaskRegistration
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CanonicalStreamCompletion

/-! Successful source items announce every immediate structural child stream. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Generated producer identity prevents an earlier registry collision
-----------------------------------------------------------------------------------------

/-- A fresh item input carries each of that item's structural child streams as a notice.
Witness: inverse lowering supplies the stream; generated producer uniqueness excludes
an old registration, and complete item batching retains its key in the leading carrier.
-/
theorem ExecutedWork.streamItems_child_notice
    {work before stream items child dependencies} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work before)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (fresh : (GraphEvent.streamItems stream items).Fresh before)
    (active
      : ((State.initialize (Work.fromExecution work)).replayGraphEvents
          before).rootStreams.contains
          stream.key
        = true)
    {item : StreamItem} (selected : item ∈ items)
    (known : NodeAt work child .stream dependencies (some item.occurrence))
    : child.key
      ∈ (((State.initialize (Work.fromExecution work)).replayGraphEvents
            before).streamItems
          stream items).2.flatMap
          rawStreamNoticeKeys := by
  apply State.streamItems_fresh_notice stream items active selected
    (matching.itemChildStreams_complete selected known)
  exact (createWorkQueue_replay_streamProducersSeen valid).freshProducer_streamAbsent
    generated known (fresh.2.2.1 item.occurrence (List.mem_map_of_mem selected))

/-- Every successful source item announces every structural stream it generates.
Witness: recover the exact active item handler, derive its local complete notice, and
retain that notice through the earlier and later raw output segments. No completion,
output admission, or cancellation premise is supplied.
-/
theorem ExecutedWork.itemProducedStream_rawNotice
    {work events node dependencies address index} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work events)
    (started : (State.initialize (Work.fromExecution work)).acceptsBatch events = true)
    (known : NodeAt work node .stream dependencies (some (.item address index)))
    (success : Occurrence.item address index ∈ events.flatMap GraphEvent.successes)
    : node.key
      ∈ ((State.initialize (Work.fromExecution work)).rawEventReplay events).2.flatMap
          rawStreamNoticeKeys := by
  obtain ⟨before, stream, items, item, after, same, selected, identity⟩ :=
    valid.itemSuccess_input success
  have earlier : (before ++ [GraphEvent.streamItems stream items]).IsPrefix events :=
    ⟨after, by simp [same, List.append_assoc]⟩
  have localLaws := valid.atPrefix earlier
  have active := State.acceptsBatch_atPrefix (State.initialize (Work.fromExecution work))
    before (.streamItems stream items) after (same ▸ started)
  have noticed := generated.streamItems_child_notice
    (valid.prefix (before := before) ⟨.streamItems stream items :: after, same.symm⟩)
    localLaws.1 localLaws.2.1 active selected (identity.symm ▸ known)
  simp only [same, State.rawEventReplay_append, State.rawEventReplay_cons, List.flatMap_append,
    State.rawEventReplay_state]
  exact List.mem_append_right _ (List.mem_append_left _ noticed)

namespace ConformancePlan

-----------------------------------------------------------------------------------------
-- The same notices survive normalization on the canonical witness
-----------------------------------------------------------------------------------------

/-- The canonical nonterminal witness has exactly the raw replay's stream-notice keys.
Witness: actual started replay, nonempty item carriers, and notice-preserving normalization.
-/
theorem Witness.streamNotices_eq_raw {work inputs} {w : Witness}
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    : w.events.flatMap streamNoticeKeys
      = ((initialQueue work).rawEventReplay inputs.flatten).2.flatMap
          rawStreamNoticeKeys := by
  rw [history, createWorkQueue_nonterminalAtoms_flattened inputs started,
    atomicStreamNotices _ _
      ((initialQueue work).rawEventReplay_nonemptyValues inputs.flatten valid.nonemptyItems)]

/-- A successful item's structural child stream appears in the actual canonical notices.
Witness: complete raw item notices and exact normalization; source start laws supply the
active handler. No independent publication matching or failure witness is chosen.
-/
theorem itemProducedStream_noticed {work inputs} {w : Witness}
    {node dependencies address index} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (known : NodeAt work node .stream dependencies (some (.item address index)))
    (success
      : Occurrence.item address index ∈ inputs.flatten.flatMap GraphEvent.successes)
    : node.key ∈ w.events.flatMap streamNoticeKeys := by
  rw [Witness.streamNotices_eq_raw valid started history]
  have accepted : (initialQueue work).batchesStarted inputs = true := by
    rwa [← inputsStarted_eq_batchesStarted]
  exact generated.itemProducedStream_rawNotice valid
    ((initialQueue work).batchesStarted_acceptsBatch inputs accepted) known success

/-- Every producer-free structural stream completes when actual replay terminates.
Witness: inverse initialization supplies its notice; the existing concrete completion
inventory forces its closure. Empty streams are included without an item-existence premise.
-/
theorem terminal_rootStream_completed {work inputs} {w : Witness} {node dependencies}
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (ended : ((initialQueue work).runNormalized inputs).1.terminated = true)
    (known : NodeAt work node .stream dependencies none)
    : node.key ∈ completedKeys w.events :=
  streamNoticeKeys_terminalCompleted valid started history ended
    (List.mem_append_left _ (NodeAt.stream_initial_notice known))

/-- Every child stream of a successful source item completes at actual termination.
Witness: complete item notice coverage and terminal stream tracking on the same history.
This includes a child whose producing outer stream later fails.
-/
theorem terminal_itemProducedStream_completed {work inputs} {w : Witness}
    {node dependencies address index}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (ended : ((initialQueue work).runNormalized inputs).1.terminated = true)
    (known : NodeAt work node .stream dependencies (some (.item address index)))
    (success
      : Occurrence.item address index ∈ inputs.flatten.flatMap GraphEvent.successes)
    : node.key ∈ completedKeys w.events :=
  streamNoticeKeys_terminalCompleted valid started history ended
    (List.mem_append_right _
      (itemProducedStream_noticed generated valid started history known success))

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
