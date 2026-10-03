import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RetiredHealthReplay

/-! Source laws derive notice-ancestor health without an output-admission premise. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- The accepted source prefix supplies every local health-frame premise
-----------------------------------------------------------------------------------------

/-- Every actual carried group notice has healthy ancestry at its source-handler boundary.
Witness: started generated replay supplies exact errors and retired/root ancestry. The
success and item handlers preserve notice ancestry; other handlers emit no group notices.
Health uses this handler's accepted failure inventory, not a possibly later source prefix.
-/
theorem ExecutedWork.replayGraphEvents_next_noticeAncestorsHealthy
    {work before event} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work (before ++ [event]))
    (started : (State.initialize (Work.fromExecution work)).acceptsBatch before = true)
    : GroupNoticeAncestorsHealthy work
        ((State.initialize (Work.fromExecution work)).objectFailureContributions
          (before ++ [event]))
        (((State.initialize (Work.fromExecution work)).replayGraphEvents
            before).handleGraphEvent
          event).2 := by
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
      apply State.acceptsBatch_atPrefix _ past next after
      simpa only [← same, List.append_assoc, List.singleton_append] using started)
  have counts := (createWorkQueue_groupErrorAccounting (Work.fromExecution work) work
    ).replayGraphEvents (before := []) (createWorkQueue_pendingAccounting work)
      generated before priorValid started
  simp only [List.append_nil] at counts
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
      exact queue.taskSuccess_noticeAncestorHealth health.1 health.2.1 generated ledger.groups
        ledger.childLinks canonical counts failedKnown source
  | streamItems stream items =>
      exact queue.streamItems_noticeAncestorHealth health.1 health.2.1 generated ledger.groups
        ledger.childLinks canonical counts failedKnown source
  | taskFailure occurrence errors =>
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
      simp only [State.handleGraphEvent, State.streamSuccess]
      split <;> simp [GroupNoticeAncestorsHealthy, rawGroupNoticeRefs]
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> simp [GroupNoticeAncestorsHealthy, rawGroupNoticeRefs]

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
    (started : (State.initialize (Work.fromExecution work)).acceptsBatch before = true)
    (emitted
      : output
        ∈ (((State.initialize (Work.fromExecution work)).replayGraphEvents
              before).handleGraphEvent
            event).2)
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
