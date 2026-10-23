import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.HandlerFailureSources
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PublicationReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NormalizedPublications

/-! Aggregate group reporting follows actual FIFO dispatch and retained pending notices. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- A matched batch preserves the internal source-reporting frame with full availability. -/
theorem State.FailureSourceFrame.handleGraphEvents {queue : State} {work inputs}
    (frame : queue.FailureSourceFrame work inputs) (events : List GraphEvent)
    (included : events.Subset inputs) (sources : ∀ event ∈ inputs, event.MatchesWork work)
    : (queue.handleGraphEvents events).1.FailureSourceFrame work inputs :=
  ⟨
    frame.rejections.handleGraphEvents events (fun _ _ member => included member),
    frame.unique.handleGraphEvents events,
    frame.sound.handleGraphEvents events,
    frame.matching.handleGraphEvents events
      (fun event member => sources event (included member)),
    frame.started.handleGraphEvents events
  ⟩

/-- Raw FIFO replay preserves queued causes and every emitted aggregate report. -/
theorem State.FailureSourceFrame.rawEventReplay_sources {queue : State}
    {work inputs} (frame : queue.FailureSourceFrame work inputs)
    (queued : queue.QueuedFailureSources work inputs)
    (events : List GraphEvent) (included : events.Subset inputs)
    (sources : ∀ event ∈ inputs, event.MatchesWork work)
    (available : List (Occurrence × Nat))
    (licensed
      : ∀ occurrence errors,
          (occurrence, errors) ∈ available
          → GraphEvent.taskFailure occurrence errors ∈ inputs)
    : (queue.rawEventReplay events available).1.QueuedFailureSources work inputs
      ∧ (∀ group errors,
          WorkQueueEvent.groupFailure group errors
            ∈ (queue.rawEventReplay events available).2
          → GroupFailureSources work inputs group.ref errors) := by
  induction events generalizing queue with
  | nil => exact ⟨queued, by simp [State.rawEventReplay]⟩
  | cons event rest ih =>
      have received := included List.mem_cons_self
      have current := frame.dispatchGraphEvent_sources queued received sources available licensed
      have later := ih
        (frame.dispatchGraphEvent received (sources event received) available licensed)
        current.1 (fun _ member => included (List.mem_cons_of_mem _ member))
      rw [State.rawEventReplay_cons queue event rest available]
      refine ⟨later.1, ?_⟩
      intro group errors member
      exact (List.mem_append.mp member).elim (current.2 group errors) (later.2 group errors)

/-- Whole-batch failure availability licenses reports before later FIFO notifications.
Queued reports retain the causes recorded at enqueue time, including across batches. -/
theorem State.FailureSourceFrame.handleGraphEvents_sources {queue : State} {work inputs}
    (frame : queue.FailureSourceFrame work inputs)
    (queued : queue.QueuedFailureSources work inputs) (events : List GraphEvent)
    (included : events.Subset inputs) (sources : ∀ event ∈ inputs, event.MatchesWork work)
    : (queue.handleGraphEvents events).1.QueuedFailureSources work inputs
      ∧ (∀ group errors,
          WorkQueueEvent.groupFailure group errors ∈ (queue.handleGraphEvents events).2
          → GroupFailureSources work inputs group.ref errors) := by
  have licensed : ∀ occurrence errors,
      (occurrence, errors) ∈ GraphEvent.availableFailures events
      → GraphEvent.taskFailure occurrence errors ∈ inputs := by
    intro occurrence errors member
    obtain ⟨event, received, same⟩ := List.mem_filterMap.mp member
    cases event <;> simp only [Option.some.injEq, reduceCtorEq, Prod.mk.injEq] at same
    obtain ⟨rfl, rfl⟩ := same
    exact included received
  have raw := frame.rawEventReplay_sources queued events included sources
    (GraphEvent.availableFailures events) licensed
  rw [State.handleGraphEvents_eq_rawEventReplay]
  split
  · exact ⟨queued, by simp⟩
  · dsimp only
    split
    · refine ⟨raw.1, ?_⟩
      intro group errors emitted
      apply raw.2 group errors
      simpa only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] using emitted
    · exact raw

/-- Publisher normalization copies failed group closures without changing their payloads.
Witness: all other raw constructors emit only values or their own control constructor.
-/
theorem IncrementalPublisher.handleWorkQueueEvent_groupFailure_mem
    (publisher : IncrementalPublisher) (event : WorkQueueEvent) {group errors}
    : Execution.WorkQueueEvent.groupFailure group errors
        ∈ (publisher.handleWorkQueueEvent event).2
      ↔ event = .groupFailure group errors := by
  cases event <;> simp [IncrementalPublisher.handleWorkQueueEvent, eq_comm]

/-- A normalized failed group closure occurred in that exact raw queue batch.
Witness: eventwise publisher replay and unchanged failure descriptors and counts.
-/
theorem IncrementalPublisher.normalizeBatch_groupFailure_mem
    (publisher : IncrementalPublisher) (events : List WorkQueueEvent) {group errors}
    : Execution.WorkQueueEvent.groupFailure group errors
        ∈ (publisher.normalizeBatch events).2
      ↔ Execution.WorkQueueEvent.groupFailure group errors ∈ events := by
  induction events generalizing publisher with
  | nil => simp [IncrementalPublisher.normalizeBatch]
  | cons event rest ih =>
      rw [IncrementalPublisher.normalizeBatch_cons]
      simp only [List.mem_append, publisher.handleWorkQueueEvent_groupFailure_mem,
        ih, List.mem_cons]
      constructor <;> intro member
      · exact member.imp Eq.symm id
      · exact member.imp Eq.symm id

/-- Publisher replay keeps every aggregate group report from its actual source batch.
Witness: actual host batches preserve the reporting frame, while normalization copies the
reported descriptor and total without creating any group failure.
-/
theorem State.FailureSourceFrame.runNormalized_sources {queue : State} {work inputs}
    (frame : queue.FailureSourceFrame work inputs)
    (queued : queue.QueuedFailureSources work inputs) (batches : List (List GraphEvent))
    (included : batches.flatten.Subset inputs)
    (sources : ∀ event ∈ inputs, event.MatchesWork work)
    : ∀ group errors,
        WorkQueueEvent.groupFailure group errors ∈ (queue.runNormalized batches).2.flatten
        → GroupFailureSources work inputs group.ref errors := by
  have loop (remaining : List (List GraphEvent)) (known : remaining.flatten.Subset inputs)
      (acc : NormalizedAcc) (prior : acc.1.FailureSourceFrame work inputs)
      (pending : acc.1.QueuedFailureSources work inputs)
      (reported : ∀ group errors, WorkQueueEvent.groupFailure group errors ∈ acc.2.2.flatten
        → GroupFailureSources work inputs group.ref errors)
      : ∀ group errors, WorkQueueEvent.groupFailure group errors
          ∈ (remaining.foldl normalizedStep acc).2.2.flatten
          → GroupFailureSources work inputs group.ref errors := by
    induction remaining generalizing acc with
    | nil => exact reported
    | cons batch rest ih =>
        have current : batch.Subset inputs :=
          fun _ member => known (List.mem_append_left rest.flatten member)
        have next : (normalizedStep acc batch).1.FailureSourceFrame work inputs := by
          rw [normalizedStep_queue]
          exact prior.handleGraphEvents batch current sources
        have batchSources := prior.handleGraphEvents_sources pending batch current sources
        have pendingNext : (normalizedStep acc batch).1.QueuedFailureSources work inputs := by
          rw [normalizedStep_queue]
          exact batchSources.1
        apply ih (fun _ member => known (List.mem_append_right batch member))
          (normalizedStep acc batch) next pendingNext
        intro group errors member
        rw [normalizedStep_flatten] at member
        rcases List.mem_append.mp member with old | new
        · exact reported group errors old
        · exact batchSources.2 group errors
            ((acc.2.1.normalizeBatch_groupFailure_mem _).mp new)
  exact loop batches included
    (queue, { active := queue.initialGroups ++ queue.initialStreams }, []) frame queued
    (by simp)

/-- Every actual normalized group failure sums distinct contributing source rejections.
Only source matching is needed for this provenance direction; admission, accepted starts
and failure-cut licensing remain separate obligations.
-/
theorem createWorkQueue_runNormalized_groupFailure_sources {work : Execution.Work}
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    {group errors}
    (reported
      : WorkQueueEvent.groupFailure group errors
        ∈ ((State.initialize (Work.fromExecution work)).runNormalized batches).2.flatten)
    : GroupFailureSources work batches.flatten group.ref errors := by
  have initial : (State.initialize (Work.fromExecution work)).FailureSourceFrame work
      batches.flatten :=
    ⟨createWorkQueue_taskRejections _ _, createWorkQueue_taskMembershipsUnique _,
      createWorkQueue_groupMembershipSound _, createWorkQueue_fromSpec_registeredTasksMatch work,
      createWorkQueue_startedTasksRegistered _⟩
  have queued : (State.initialize (Work.fromExecution work)).QueuedFailureSources work
      batches.flatten := by
    intro failure member
    simp only [State.initialize_groupFailureEvents, List.not_mem_nil] at member
  exact initial.runNormalized_sources queued batches (List.Subset.refl _)
    (fun event member => valid.eachMatches member) group errors reported

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
