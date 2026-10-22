import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RetiredHealthReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamReleaseOwnerReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SuccessfulRetirement

/-! Actual source boundaries derive healthy, uncancelled retirement for success carriers. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Replay discharges every local health-frame premise before the next source handler
-----------------------------------------------------------------------------------------

/-- Every successful carrier of the next handler is healthy at that source boundary.
Witness: actual replay supplies exact errors and healthy ancestry; strengthened success
and item handlers retain those facts with their output. Other handlers cannot emit a
successful group carrier. No output admission or extra internal-state premise is assumed.
-/
theorem ExecutedWork.replayGraphEvents_next_successfulGroupsHealthy
    {work before event} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work (before ++ [event]))
    (started
      : State.eventsStarted [] (State.initialize (Work.fromExecution work)) before = true)
    : SuccessfulGroupsHealthy work
        ((State.initialize (Work.fromExecution work)).objectFailureContributions
          (before ++ [event]))
        (((State.initialize (Work.fromExecution work)).replayGraphEvents
            before).handleGraphEvent
          event).2.1 := by
  let queue := (State.initialize (Work.fromExecution work)).replayGraphEvents before
  let failed := (State.initialize (Work.fromExecution work)).objectFailureContributions before
  have priorValid := valid.prefix (List.prefix_append before [event])
  have source := valid.eachMatches (List.mem_append_right before List.mem_cons_self)
  have health := generated.replayGraphEvents_retiredHealth before priorValid started
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have ledger : queue.OwnerAccounting work parents before :=
    generated.replayGraphEvents_ownerAccounting_of_eachAccepted canonical priorValid (by
      intro past next earlier
      obtain ⟨after, same⟩ := earlier
      apply State.eventsStarted_atPrefix _ past next after
      simpa only [← same, List.append_assoc, List.singleton_append] using started)
  have counts := (createWorkQueue_retainedFailures (Work.fromExecution work) work
    ).replayGraphEvents (before := []) (createWorkQueue_pendingAccounting work generated.declarations)
      generated (by intro _ member; cases member) before priorValid started
  simp only [List.append_nil] at counts
  rw [← State.objectFailureContributions_eq_of_accepts _ before [] started] at counts
  have successes := (createWorkQueue_pendingAccounting work generated.declarations).replayGraphEvents_successes
    (before := []) generated before priorValid started
  have included : failed.Subset (GraphEvent.failureSettlements before) :=
    ((State.initialize (Work.fromExecution work)).objectFailureContributions_sublist before).subset
  have fresh := (validGraphEvents_last valid).2.2
  have failedKnown : ∀ occurrence ∈ failed,
      ∃ owners producer payload,
        TaskAt work occurrence owners producer payload ∧ payload.failure.isSome = true := by
    intro occurrence member
    obtain ⟨owners, producer, path, errors, known⟩ :=
      priorValid.failureSettlements_known occurrence
        (((State.initialize (Work.fromExecution work)).objectFailureContributions_sublist before
          ).subset member)
    exact ⟨owners, producer, _, known, rfl⟩
  rw [State.objectFailureContributions_append]
  cases event with
  | taskSuccess occurrence result =>
      exact (queue.taskSuccess_releaseHealth health.1 health.2.1 generated ledger.groups
        ledger.childLinks canonical counts failedKnown source successes priorValid included
          fresh).2.2
  | streamItems stream items =>
      exact (queue.streamItems_releaseHealth health.1 health.2.1 generated ledger.groups
        ledger.childLinks canonical counts failedKnown source successes.refs successes.sound
          successes.matching successes.registration.live successes.pending
            (fun occurrence settled recorded => priorValid.succeeds_not_failureSettlements
              (priorValid.groupSettlements_succeed settled) (included recorded))).2.2
  | taskFailure occurrence errors =>
      exact .of_noGroupSuccess (queue.taskFailure_noGroupSuccess occurrence errors)
  | streamSuccess stream =>
      apply SuccessfulGroupsHealthy.of_noGroupSuccess
      intro group groups streams member
      simp only [State.handleGraphEvent, State.streamSuccess] at member
      split at member <;> simp at member
  | streamFailure stream errors =>
      apply SuccessfulGroupsHealthy.of_noGroupSuccess
      intro group groups streams member
      simp only [State.handleGraphEvent, State.streamFailure] at member
      split at member <;> simp at member
  | groupFailure notice =>
      apply SuccessfulGroupsHealthy.of_noGroupSuccess
      intro group groups streams member
      simp only [State.handleGraphEvent, State.groupFailure] at member
      split at member
      · cases member
      · split at member <;> simp at member

/-- An actual successful carrier retires its known group healthy and uncancelled.
Witness: local carrier health rules out supported cancellation; independent closure
accounting supplies retirement in the post-handler state. All premises come from the
source laws and actual queue replay, including carriers emitted by recursive draining.
-/
theorem ExecutedWork.replayGraphEvents_successfulCarrier_retiredHealthy
    {work before event group groups streams} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work (before ++ [event]))
    (started
      : State.eventsStarted [] (State.initialize (Work.fromExecution work)) before = true)
    (carrier
      : Execution.WorkQueueEvent.groupSuccess group groups streams
        ∈ (((State.initialize (Work.fromExecution work)).replayGraphEvents
              before).handleGraphEvent
            event).2.1)
    : let queue :=
        (State.initialize (Work.fromExecution work)).replayGraphEvents (before ++ [event])
      ∃ dependencies,
        GroupRecordAt work group dependencies
        ∧ queue.RetiredGroup group.ref
        ∧ ¬GroupRecordInvalidated work
            ((State.initialize (Work.fromExecution work)).objectFailureContributions
              (before ++ [event])) group.ref
        ∧ group.ref ∉ queue.cancelledGroups := by
  obtain ⟨dependencies, known, healthy⟩ :=
    generated.replayGraphEvents_next_successfulGroupsHealthy valid started
      group groups streams carrier
  have priorValid := valid.prefix (List.prefix_append before [event])
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have ledger := generated.replayGraphEvents_ownerAccounting_of_eachAccepted canonical
    priorValid (by
      intro past next earlier
      obtain ⟨after, same⟩ := earlier
      apply State.eventsStarted_atPrefix _ past next after
      simpa only [← same, List.append_assoc, List.singleton_append] using started)
  have pending := (createWorkQueue_pendingGroupFailures (Work.fromExecution work)).replayGraphEvents
    (createWorkQueue_liveGroupsRegistered _) before
  have retired := ((State.dispatchGraphEvent_closureAccounting ledger.pending.liveGroups
    pending event).2.closed group.ref
      (List.mem_flatMap.mpr ⟨.groupSuccess group groups streams, carrier,
        List.mem_cons_self⟩)).1
  refine ⟨dependencies, known, ?_, healthy, ?_⟩
  · rwa [State.replayGraphEvents_append]
  · exact (generated.replayGraphEvents_cancelledRecordsSupported _ valid).healthy_not_mem healthy

-----------------------------------------------------------------------------------------
-- A successful carrier remains healthy and uncancelled after arbitrary later source inputs
-----------------------------------------------------------------------------------------

/-- Every normalized successful carrier retires a group that stays healthy and uncancelled.
Witness: recover its actual handler boundary, certify that closure, and apply retired-record
health stability to all later started inputs. Independent closure and cancellation replay
transport the certificate to the final normalized state, regardless of batching.
-/
theorem ExecutedWork.runNormalized_successfulCarrier_retiredHealthy
    {work batches group groups streams} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    (carrier
      : Execution.WorkQueueEvent.groupSuccess group groups streams
        ∈ ((State.initialize (Work.fromExecution work)).runNormalized batches).2.flatten)
    : let queue := ((State.initialize (Work.fromExecution work)).runNormalized batches).1
      ∃ dependencies,
        GroupRecordAt work group dependencies
        ∧ queue.RetiredGroup group.ref
        ∧ ¬GroupRecordInvalidated work
            ((State.initialize
                (Work.fromExecution work)).admittedObjectFailureContributionsForBatches
              batches)
            group.ref
        ∧ group.ref ∉ queue.cancelledGroups := by
  obtain ⟨dependencies, known, retired⟩ :=
    generated.runNormalized_successfulGroupRetirements valid started carrier
  exact ⟨dependencies, known, retired.retired,
    (generated.runNormalized_retiredHealth batches valid started).1 group dependencies
      known retired.retired retired.uncancelled, retired.uncancelled⟩

/-- Every group-carried stream has a derived uncancelled, retired contributing dependency.
Witness: exact release ownership identifies the carrier as a dependency; actual successful
closure health proves its uncancelledness even after later source failures. No supplied
supporting ref, queue-state invariant, or output-admission hypothesis is required.
-/
theorem ExecutedWork.runNormalized_streamHealthyDependency
    {work batches group groups streams stream dependencies producer}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    (carrier
      : Execution.WorkQueueEvent.groupSuccess group groups streams
        ∈ ((State.initialize (Work.fromExecution work)).runNormalized batches).2.flatten)
    (released : stream ∈ streams)
    (known : NodeAt work stream .stream dependencies producer)
    : group.ref ∈ dependencies
      ∧ ((State.initialize (Work.fromExecution work)).runNormalized
          batches).1.RetiredGroup
          group.ref
      ∧ group.ref
        ∉ ((State.initialize (Work.fromExecution work)).runNormalized
            batches).1.cancelledGroups := by
  obtain ⟨_, _, retired, _, uncancelled⟩ :=
    generated.runNormalized_successfulCarrier_retiredHealthy valid started carrier
  exact ⟨createWorkQueue_runNormalized_streamReleaseDependencies generated batches
    (fun _ member => valid.eachMatches member) group groups streams carrier stream released
      dependencies producer known, retired, uncancelled⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
