import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RetiredHealthReplay

/-! Source laws derive notice-ancestor health without an output-admission premise. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- The accepted source prefix supplies every local health-frame premise
-----------------------------------------------------------------------------------------

/-- Every carried group notice has healthy ancestry at its eventwise handler boundary.
Witness: started generated replay supplies exact errors and retired/root ancestry. The
success and item handlers preserve notice ancestry; other handlers emit no group notices.
Health uses this handler's accepted failure inventory, not a possibly later source prefix.
-/
theorem ExecutedWork.replayGraphEvents_next_noticeAncestorsHealthy
    {work before event} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work (before ++ [event]))
    (started
      : State.eventsStarted [] (State.initialize (Work.fromExecution work)) before = true)
    : GroupNoticeAncestorsHealthy work
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
  rw [← State.objectFailureContributions_eq_of_accepts
    (State.initialize (Work.fromExecution work)) before [] started] at counts
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
        (included member)
    exact ⟨owners, producer, _, known, rfl⟩
  rw [State.objectFailureContributions_append]
  cases event with
  | taskSuccess occurrence result =>
      exact queue.taskSuccess_noticeAncestorHealth health.1 health.2.1 generated ledger.groups
        ledger.childLinks canonical counts failedKnown source successes priorValid included fresh
  | streamItems stream items =>
      exact queue.streamItems_noticeAncestorHealth health.1 health.2.1 generated ledger.groups
        ledger.childLinks canonical counts failedKnown source successes.refs successes.sound
        successes.matching successes.registration.live successes.pending
        (fun occurrence settled recorded => priorValid.succeeds_not_failureSettlements
          (priorValid.groupSettlements_succeed settled) (included recorded))
  | taskFailure occurrence errors =>
      change GroupNoticeAncestorsHealthy work _ (queue.taskFailure occurrence errors).2
      apply GroupNoticeAncestorsHealthy.of_noNotices
      intro output member
      cases output with
      | groupSuccess group groups streams =>
          exact False.elim (queue.taskFailure_noGroupSuccess occurrence errors group groups
            streams member)
      | streamValues stream values groups streams =>
          have impossible : stream.ref ∈
              (queue.taskFailure occurrence errors).2.flatMap rawStreamReferenceRefs :=
            List.mem_flatMap.mpr ⟨_, member, List.mem_cons_self⟩
          rw [State.taskFailure_streamReferences] at impossible
          cases impossible
      | groupValues | groupFailure | streamSuccess | streamFailure | workQueueTermination
        =>
          rfl
  | streamSuccess stream =>
      change GroupNoticeAncestorsHealthy work _ (queue.streamSuccess stream).2
      by_cases active : stream.ref ∈ queue.rootStreams <;>
        simp [State.streamSuccess, active, GroupNoticeAncestorsHealthy, rawGroupNoticeRefs]
  | streamFailure stream errors =>
      change GroupNoticeAncestorsHealthy work _ (queue.streamFailure stream errors).2
      by_cases active : stream.ref ∈ queue.rootStreams <;>
        simp [State.streamFailure, active, GroupNoticeAncestorsHealthy, rawGroupNoticeRefs]
  | groupFailure notice =>
      apply GroupNoticeAncestorsHealthy.of_noNotices
      intro output member
      change output ∈ (queue.groupFailure notice).2 at member
      unfold State.groupFailure at member
      split at member
      · cases member
      · split at member <;> simp_all [rawGroupNoticeRefs]

-----------------------------------------------------------------------------------------
-- Concrete ancestor cancellation is excluded at the same source boundary
-----------------------------------------------------------------------------------------

/-- A noticed group's complete defer ancestry is uninvalidated and uncancelled.
Witness: the actual handler's notice certificate applies to its known record; independent
replay cancellation support excludes every ancestor ref from the concrete cancelled set.
This does not yet assert semantic producer readiness or task accounting for those refs.
-/
theorem ExecutedWork.noticeAncestor_healthy_uncancelled
    {work before event output child dependencies ref} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work (before ++ [event]))
    (started
      : State.eventsStarted [] (State.initialize (Work.fromExecution work)) before = true)
    (emitted
      : output
        ∈ (((State.initialize (Work.fromExecution work)).replayGraphEvents
              before).handleGraphEvent
            event).2.1)
    (noticed : child.ref ∈ rawGroupNoticeRefs output)
    (known : GroupRecordAt work child dependencies) (ancestor : ref ∈ dependencies)
    : ¬GroupRecordInvalidated work
        ((State.initialize (Work.fromExecution work)).objectFailureContributions
          (before ++ [event])) ref
      ∧ ref
        ∉ ((State.initialize (Work.fromExecution work)).replayGraphEvents
            (before ++ [event])).cancelledGroups := by
  have healthy := generated.replayGraphEvents_next_noticeAncestorsHealthy valid started
    child.ref (List.mem_flatMap.mpr ⟨output, emitted, noticed⟩)
    child dependencies known rfl ref ancestor
  exact ⟨healthy,
    (generated.replayGraphEvents_cancelledRecordsSupported _ valid).healthy_not_mem healthy⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
