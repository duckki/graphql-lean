import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialStartupRetirement
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialStartupReplay

/-! Source-valid startup replay derives accounting frames at actual batch and FIFO cuts. -/

namespace GraphQL.IncrementalDelivery.EventSource
open ReferenceWorkQueue

/-- Every startup-admitted source licenses its initial cache independently of output. -/
theorem ValidFor.cachedMatches {work startup}
    {source : EventSource (List GraphEvent)} (valid : source.ValidFor work startup)
    : startup.MatchesWork work :=
  valid.1

/-- An admitted startup input has matching fresh outcomes and the actual start discipline. -/
theorem ValidFor.admittedProperties {work startup}
    {source : EventSource (List GraphEvent)}
    (valid : source.ValidFor work startup) {inputs}
    (admitted : source.admissible inputs)
    : ValidGraphEvents work inputs.flatten
      ∧ inputsStarted work inputs startup = true := by
  have checked := valid.2.2.2.2 inputs admitted
  exact ⟨checked.1, checked.2.1⟩

end GraphQL.IncrementalDelivery.EventSource

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Initial synchronous activation establishes all cancellation-aware source certificates.
Cached failures remain separate from the empty consumed-notification history.
-/
theorem ExecutedWork.initialStartup_uncancelledReplayFrame {work parents}
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (startup : InitialStartup) (matched : startup.MatchesWork work)
    : UncancelledReplayFrame
        (State.initialize (Work.fromExecution work) startup) work parents
        [] := by
  exact ⟨
    generated.initialStartup_uncancelledRetiredMarkers canonical startup,
    State.initializeWithStartup_uncancelledTaskAccounting work generated startup,
    generated.initialStartup_parentCutFrame canonical startup,
    generated.initialStartup_rootReplayFrame canonical startup,
    State.initializeWithStartup_taskOwnerFrame work startup,
    State.initializeWithStartup_pendingAccounting work generated.declarations startup,
    State.initializeWithStartup_regionInventory work startup,
    State.initializeWithStartup_taskRejections _ startup _
      (fun occurrence errors member => (matched.2 occurrence errors member).1),
    (by intro occurrence impossible; cases impossible),
    State.initializeWithStartup_cancellationsRetired work generated startup,
    State.initializeWithStartup_producerRegistrationAccounting work startup,
    (State.initializeWithStartup_producerOrder work startup).1,
    (State.initializeWithStartup_producerOrder work startup).2
  ⟩

/-- Actual startup replay preserves the complete frame at each consumed batch boundary. -/
theorem ExecutedWork.startup_runNormalized_frame {work parents}
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (startup : InitialStartup) (matched : startup.MatchesWork work)
    (inputs : List (List GraphEvent)) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    : let initial := State.initialize (Work.fromExecution work) startup
      UncancelledReplayFrame (initial.runNormalized inputs).1
        work parents inputs.flatten := by
  let initial := State.initialize (Work.fromExecution work) startup
  have initialFrame := generated.initialStartup_uncancelledReplayFrame canonical startup matched
  have replayed :=
    initialFrame.runNormalized (before := []) generated canonical inputs valid
      (by rwa [inputsStartedWithStartup_eq_batchesStarted] at started)
  rw [State.runNormalized_replayBatches] at replayed
  dsimp only
  rw [State.runNormalized_replayBatches]
  exact replayed

/-- Whole-batch cache snapshots and FIFO prefixes retain their distinct source cuts. -/
theorem ExecutedWork.startup_uncancelledFrame_atBatchPrefix {work : Execution.Work}
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
    : UncancelledReplayFrame
        (((State.initialize (Work.fromExecution work) startup).replayBatches
            earlier).replayGraphEvents
          fifo (GraphEvent.availableFailures batch))
        work parents (earlier.flatten ++ fifo) := by
  let initial := (State.initialize (Work.fromExecution work) startup)
  have checked : initial.batchesStarted (earlier ++ batch :: later) = true := by
    rwa [← inputsStartedWithStartup_eq_batchesStarted]
  rw [State.batchesStarted_append, Bool.and_eq_true] at checked
  have validEarlier : ValidGraphEvents work earlier.flatten :=
    valid.prefix ⟨(batch :: later).flatten, by simp [List.flatten_append]⟩
  have initialFrame := generated.initialStartup_uncancelledReplayFrame canonical startup matched
  have before := initialFrame.runNormalized (before := []) generated canonical earlier
    validEarlier checked.1
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

/-- Every admitted startup-aware source derives its frame without output-accounting premises. -/
theorem ExecutedWork.startup_source_frame {work parents startup}
    {source : EventSource (List GraphEvent)} (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (valid : source.ValidFor work startup) {inputs}
    (admitted : source.admissible inputs)
    : let initial := State.initialize (Work.fromExecution work) startup
      UncancelledReplayFrame (initial.runNormalized inputs).1
        work parents inputs.flatten := by
  have checked := valid.admittedProperties admitted
  exact generated.startup_runNormalized_frame canonical startup valid.cachedMatches inputs
    checked.1 checked.2

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
