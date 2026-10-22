import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupRetiredHealth
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialStartupPublicationFrames
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupStreamNoticeMetadata
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupStreamAnnouncements
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ObjectStreamSupportReplay

/-! Startup replay retains actual successful support for object-produced streams. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Initial stream roots have no object producer, independently of cached task failures. -/
theorem ExecutedWork.initialStartup_objectStreamReplayFrame {work parents}
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (startup : InitialStartup) (matched : startup.MatchesWork work)
    : ObjectStreamReplayFrame
        (State.initialize (Work.fromExecution work) startup) work parents
        [] := by
  refine ⟨generated.initialStartup_uncancelledReplayFrame canonical startup matched,
    ⟨[], State.initializeWithStartup_publicationInventory _ startup⟩,
    State.initializeWithStartup_childStreamsSettled _ startup,
    State.initializeWithStartup_childStreamsMatchWork _ startup _, ?_, ?_⟩
  · intro stream member
    rw [State.initializeWithStartup_streams] at member
    exact ⟨[], none, (createWorkQueue_initialStreams_nodeAt work).1 stream member⟩
  · intro stream dependencies address known active
    have initial := State.initializeWithStartup_streamRoots (Work.fromExecution work) startup active
    rw [State.initializeWithStartup_initialStreams] at initial
    cases generated.initialStream_producerNone known initial

/-- Successful stream support follows the actual whole-batch cache and FIFO prefix.
Initial failure notifications stay outside the consumed-source coordinate.
-/
theorem ExecutedWork.startup_objectStreamFrame_atBatchPrefix {work : Execution.Work}
    {parents : Nat → NodeRefs} (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (startup : InitialStartup) (matched : startup.MatchesWork work)
    (earlier : List (List GraphEvent)) (batch : List GraphEvent)
    (later : List (List GraphEvent)) (fifo : List GraphEvent)
    (valid : ValidGraphEvents work (earlier ++ batch :: later).flatten)
    (started : inputsStarted work (earlier ++ batch :: later) startup = true)
    (prefixOfBatch : fifo.IsPrefix batch)
    : ObjectStreamReplayFrame
        ((((State.initialize (Work.fromExecution work) startup)).replayBatches
            earlier).replayGraphEvents
          fifo (GraphEvent.availableFailures batch))
        work parents (earlier.flatten ++ fifo) := by
  let initial := (State.initialize (Work.fromExecution work) startup)
  have checked : initial.batchesStarted (earlier ++ batch :: later) = true := by
    rwa [← inputsStartedWithStartup_eq_batchesStarted]
  rw [State.batchesStarted_append, Bool.and_eq_true] at checked
  have validEarlier : ValidGraphEvents work earlier.flatten :=
    valid.prefix ⟨(batch :: later).flatten, by simp [List.flatten_append]⟩
  have before :=
    (generated.initialStartup_objectStreamReplayFrame canonical startup matched).runNormalized
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
