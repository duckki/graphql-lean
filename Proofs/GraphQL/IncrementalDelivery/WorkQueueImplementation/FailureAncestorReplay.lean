import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RetiredHealthReplay

/-! Actual generated source boundaries certify ancestry of failed group completions. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Every failed completion has healthy ancestry at its actual source-handler boundary.
Witness: success and item drains carry the joint health frame; a fresh rejection cannot
newly invalidate any retired ancestor of the active owners it closes.
-/
theorem ExecutedWork.replayGraphEvents_next_failureAncestorsHealthy
    {work before event} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work (before ++ [event]))
    (started : (State.initialize (Work.fromExecution work)).acceptsBatch before = true)
    : GroupFailureAncestorsHealthy work
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
  have counts := (createWorkQueue_retainedFailures (Work.fromExecution work) work
    ).replayGraphEvents (before := []) (createWorkQueue_pendingAccounting work)
      generated (by intro _ member; cases member) before priorValid started
  simp only [List.append_nil] at counts
  have successes := (createWorkQueue_pendingAccounting work).replayGraphEvents_successes
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
  have frame : ReleaseHealth.HealthFrame queue work parents failed :=
    ⟨ledger.groups, ledger.childLinks, counts, health.1, health.2.1,
      successes.refs, successes.sound, successes.matching⟩
  have afterRoots := generated.replayGraphEvents_next_rootAncestorsHealthy valid started
  rw [State.objectFailureContributions_append] at afterRoots ⊢
  cases event with
  | taskSuccess occurrence result =>
      exact (frame.taskSuccess successes generated canonical priorValid included source fresh).2.2.2
  | streamItems stream items =>
      exact frame.streamItems_failureAncestorHealth generated canonical failedKnown source
  | taskFailure occurrence errors =>
      exact queue.taskFailure_failureAncestorHealth afterRoots occurrence errors
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess]
      split <;> exact .of_noFailures (by simp)
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> exact .of_noFailures (by simp)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
