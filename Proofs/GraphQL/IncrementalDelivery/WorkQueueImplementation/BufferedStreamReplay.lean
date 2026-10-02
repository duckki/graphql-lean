import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.BufferedStreamItemHandlers
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StoredLinkReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.BufferedCarrierReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.AcceptedFailureHealth

/-! Every generated replay continuation conserves protected buffered child streams. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- All handler premises are derived at the actual source prefix
-----------------------------------------------------------------------------------------

/-- Generated replay supplies the internal facts for buffered-stream conservation.
Witness: source-valid stored provenance, pending accounting, and derived stored/child-link
invariants. The caller provides no publication ledger or admitted-output hypothesis.
-/
theorem ExecutedWork.handleGraphEvent_bufferedStreamsConserved {work before event}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work before)
    (started : (State.initialize (Work.fromExecution work)).acceptsBatch before = true)
    (matching : event.MatchesWork work) (fresh : event.Fresh before)
    : let queue := (State.initialize (Work.fromExecution work)).replayGraphEvents before
      queue.BufferedStreamsConserved (queue.handleGraphEvent event).2
        (queue.handleGraphEvent event).1 := by
  have accounted := (createWorkQueue_pendingAccounting work).replayGraphEvents
    (before := []) generated before valid started
  have links := generated.replayGraphEvents_storedTaskLinks before valid started
  have children := (createWorkQueue_childStreamInventory (Work.fromExecution work)).rawEventReplay before
  rw [State.rawEventReplay_state] at children
  obtain ⟨_, _, inventory⟩ := createWorkQueue_rawEventReplay_publications valid
  rw [State.rawEventReplay_state] at inventory
  exact State.handleGraphEvent_bufferedStreamsConserved accounted links children
    (inventory.stored.mono (fun _ _ source => source.1))
    (GraphEvent.taskSettlements_subsetIdentities before) event matching fresh

/-- Every source continuation releases or retains each protected earlier buffered stream.
Witness: compose the actual per-handler certificates in source order, retaining exact
lookups and the monotonically growing cancellation history across each boundary.
-/
theorem ExecutedWork.replayGraphEvents_bufferedStreamsConserved {work before events}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work (before ++ events))
    (started
      : (State.initialize (Work.fromExecution work)).acceptsBatch (before ++ events)
        = true)
    : let queue := (State.initialize (Work.fromExecution work)).replayGraphEvents before
      queue.BufferedStreamsConserved (queue.rawEventReplay events).2
        (queue.replayGraphEvents events) := by
  induction events generalizing before with
  | nil => exact .refl _
  | cons event rest ih =>
      have initial : before.IsPrefix (before ++ event :: rest) := List.prefix_append _ _
      have step : (before ++ [event]).IsPrefix (before ++ event :: rest) := ⟨rest, by simp⟩
      obtain ⟨matching, fresh, _⟩ := valid.atPrefix step
      have first := generated.handleGraphEvent_bufferedStreamsConserved (valid.prefix initial)
        (State.acceptsBatch_prefix started) matching fresh
      have later := ih (before := before ++ [event])
        (by simpa only [List.append_assoc, List.singleton_append] using valid)
        (by simpa only [List.append_assoc, List.singleton_append] using started)
      rw [State.replayGraphEvents_append] at later
      simpa only [State.rawEventReplay_cons, State.rawEventReplay_state,
        State.replayGraphEvents, List.foldl_cons]
        using first.append later (State.replayGraphEvents_cancelledGroups_subset _ rest)

/-- An accepted success conserves its prepared streams through every later input.
Witness: derive the first handler's prepared certificate and compose it with ordinary
continuation conservation, without replacing the actual child-bearing task lookup.
-/
theorem ExecutedWork.success_conservesBufferedStreams
    {work before occurrence result after node} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work (before ++ .taskSuccess occurrence result :: after))
    (started
      : (State.initialize (Work.fromExecution work)).acceptsBatch
          (before ++ .taskSuccess occurrence result :: after)
        = true)
    (found
      : ((State.initialize (Work.fromExecution work)).replayGraphEvents before).taskNode?
          occurrence
        = some node)
    (healthy
      : ((State.initialize (Work.fromExecution work)).replayGraphEvents
          before).taskHasHealthyOwner
          node.task
        = true)
    : let queue := (State.initialize (Work.fromExecution work)).replayGraphEvents before
      let prepared :=
        ((queue.putTaskNode { node with value := some result.value }).maybeIntegrateWork
          result.work (some occurrence)).1
      prepared.BufferedStreamsConserved
        (queue.rawEventReplay (.taskSuccess occurrence result :: after)).2
        (queue.replayGraphEvents (.taskSuccess occurrence result :: after)) := by
  have prior := valid.prefix (List.prefix_append before _)
  have priorStarted := State.acceptsBatch_prefix (before := before) started
  have accounted := (createWorkQueue_pendingAccounting work).replayGraphEvents
    (before := []) generated before prior priorStarted
  have links := generated.replayGraphEvents_storedTaskLinks before prior priorStarted
  have children := (createWorkQueue_childStreamInventory (Work.fromExecution work)).rawEventReplay before
  rw [State.rawEventReplay_state] at children
  have boundary : (before ++ [GraphEvent.taskSuccess occurrence result]).IsPrefix
      (before ++ .taskSuccess occurrence result :: after) := ⟨after, by simp⟩
  have fresh := (valid.atPrefix boundary).2.1
  have first := State.taskSuccess_preparedBufferedStreams (result := result)
    accounted links children found healthy
    (fun member => fresh.2.2.1 occurrence List.mem_cons_self
      (GraphEvent.taskSettlements_subsetIdentities before member))
  have later := generated.replayGraphEvents_bufferedStreamsConserved
    (before := before ++ [.taskSuccess occurrence result]) (events := after)
    (by simpa only [List.append_assoc, List.singleton_append] using valid)
    (by simpa only [List.append_assoc, List.singleton_append] using started)
  rw [State.replayGraphEvents_append] at later
  simpa only [State.rawEventReplay_cons, State.rawEventReplay_state,
    State.replayGraphEvents, List.foldl_cons, State.handleGraphEvent]
    using first.append later (State.replayGraphEvents_cancelledGroups_subset _ after)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
