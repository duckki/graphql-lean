import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamRegistrationOrigins
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupStreamNoticeMetadata
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupRawBatches

/-! Startup stream registration retains actual consumed producer identities at host/FIFO cuts. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- A matched source input preserves old stream origins and supplies each new producer. -/
theorem State.StreamsSatisfy.producerSeen_handleGraphEvent {queue work before event}
    (origins
      : State.StreamsSatisfy queue
          (StreamProducerSeen work (before.flatMap (fun input => input.identities.1))))
    (matching : event.MatchesWork work) (available : List (Occurrence × Nat))
    : (queue.handleGraphEvent event available).1.StreamsSatisfy
        (StreamProducerSeen work
          ((before ++ [event]).flatMap (fun input => input.identities.1))) := by
  have old : queue.StreamsSatisfy (StreamProducerSeen work
      ((before ++ [event]).flatMap (fun input => input.identities.1))) := by
    intro stream member
    apply (origins stream member).mono
    simp only [List.flatMap_append, List.flatMap_singleton]
    exact List.subset_append_left _ _
  apply old.handleGraphEvent event (available := available)
  have new := matching.childStreams_producerSeen
  have included : event.identities.1.Subset
      ((before ++ [event]).flatMap (fun input => input.identities.1)) := by
    simp only [List.flatMap_append, List.flatMap_singleton]
    exact List.subset_append_right _ _
  cases event with
  | taskSuccess occurrence result =>
      exact fun stream member => (new stream member).mono included
  | streamItems stream items => exact fun item member child supplied =>
      (new item member child supplied).mono included
  | taskFailure | streamSuccess | streamFailure | groupFailure => trivial

/-- Fixed-snapshot source replay retains exact consumed producer identities. -/
theorem State.StreamsSatisfy.producerSeen_replayGraphEvents {queue work before}
    (origins
      : State.StreamsSatisfy queue
          (StreamProducerSeen work (before.flatMap (fun input => input.identities.1))))
    (events : List GraphEvent) (matching : ∀ event ∈ events, event.MatchesWork work)
    (available : List (Occurrence × Nat))
    : (queue.replayGraphEvents events available).StreamsSatisfy
        (StreamProducerSeen work
          ((before ++ events).flatMap (fun input => input.identities.1))) := by
  induction events generalizing queue before with
  | nil =>
      simpa only [State.replayGraphEvents, List.foldl_nil, List.append_nil] using origins
  | cons event rest ih =>
      have next := origins.producerSeen_handleGraphEvent (matching event List.mem_cons_self)
          available
      have dispatched : (queue.dispatchGraphEvent event available).1.StreamsSatisfy
          (StreamProducerSeen work ((before ++ [event]).flatMap (fun input => input.identities.1))) := next
      simpa only [State.replayGraphEvents, List.foldl_cons, List.append_assoc,
        List.singleton_append] using ih dispatched
          (fun entry member => matching entry (List.mem_cons_of_mem _ member))

/-- The host wrapper changes no stream-origin evidence when it changes termination. -/
theorem State.StreamsSatisfy.producerSeen_handleGraphEvents {queue work before}
    (origins
      : State.StreamsSatisfy queue
          (StreamProducerSeen work (before.flatMap (fun input => input.identities.1))))
    (events : List GraphEvent) (matching : ∀ event ∈ events, event.MatchesWork work)
    : (queue.handleGraphEvents events).1.StreamsSatisfy
        (StreamProducerSeen work
          ((before ++ events).flatMap (fun input => input.identities.1))) := by
  cases ended : queue.terminated with
  | true =>
      intro stream member
      have old : stream ∈ queue.streams := by
        simpa only [State.handleGraphEvents, ended, ↓reduceIte] using member
      apply (origins stream old).mono
      rw [List.flatMap_append]
      exact List.subset_append_left _ _
  | false =>
      have next := origins.producerSeen_replayGraphEvents events matching
        (GraphEvent.availableFailures events)
      obtain ⟨terminal, same⟩ := queue.handleGraphEvents_stateCore events ended
      rw [same]
      exact next

/-- Real host-batch state transitions retain origins without flattening cache snapshots. -/
theorem State.StreamsSatisfy.producerSeen_rawBatches {queue work before}
    (origins
      : State.StreamsSatisfy queue
          (StreamProducerSeen work (before.flatMap (fun input => input.identities.1))))
    (batches : List (List GraphEvent))
    (matching : ∀ event ∈ batches.flatten, event.MatchesWork work)
    : (queue.rawBatches batches).1.StreamsSatisfy
        (StreamProducerSeen work
          ((before ++ batches.flatten).flatMap (fun input => input.identities.1))) := by
  induction batches generalizing queue before with
  | nil => simpa only [State.rawBatches, List.flatten_nil, List.append_nil] using origins
  | cons batch rest ih =>
      have next := origins.producerSeen_handleGraphEvents batch
        (fun event member => matching event (List.mem_append_left _ member))
      simpa only [State.rawBatches, List.flatten_cons, List.append_assoc] using ih next
        (fun event member => matching event (List.mem_append_right _ member))

/-- Registered startup streams have producers in the actual earlier host/FIFO inputs. -/
theorem ExecutedWork.startup_batchPrefix_streamProducersSeen {work}
    (_generated : ExecutedWork work) (startup : InitialStartup)
    (earlier : List (List GraphEvent)) (fifo : List GraphEvent)
    (available : List (Occurrence × Nat))
    (valid : ValidGraphEvents work (earlier.flatten ++ fifo))
    : (((State.initialize (Work.fromExecution work) startup).replayBatches
          earlier).replayGraphEvents
        fifo available).StreamsSatisfy
        (StreamProducerSeen work
          ((earlier.flatten ++ fifo).flatMap (fun input => input.identities.1))) := by
  have initial : (State.initialize (Work.fromExecution work) startup).StreamsSatisfy
      (StreamProducerSeen work (([] : List GraphEvent).flatMap (fun input => input.identities.1)))
          := by
    intro stream member
    rw [State.initializeWithStartup_streams] at member
    exact createWorkQueue_replay_streamProducersSeen (.nil : ValidGraphEvents work []) [] stream
        member
  have first := initial.producerSeen_rawBatches earlier
    (fun event member => valid.event_matches (List.mem_append_left _ member))
  rw [State.rawBatches_state] at first
  simp only [List.nil_append] at first
  exact first.producerSeen_replayGraphEvents fifo
    (fun event member => valid.event_matches (List.mem_append_right _ member)) available

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
