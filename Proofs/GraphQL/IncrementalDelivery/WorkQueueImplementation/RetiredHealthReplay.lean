import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RetiredHealthHandlers

/-! Generated started replay supplies the health guard's historical missing-parent premise. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Independent accounting and structural replay close the joint health induction
-----------------------------------------------------------------------------------------

/-- Valid started replay has healthy uncancelled retirements, healthy root ancestry, and
justified missing-parent boundaries. Witness: a joint health/parent-registry induction;
independent source accounting supplies exact errors and accepted-inventory ownership at
each prefix. Fresh failures cannot reach protected retired ancestors, and all success/item
handlers preserve the certificates without requiring released children themselves healthy.
-/
theorem ExecutedWork.replayGraphEvents_retiredHealth {work : Execution.Work}
    (generated : ExecutedWork work) (events : List GraphEvent)
    (valid : ValidGraphEvents work events)
    (started : (State.initialize (Work.fromExecution work)).acceptsBatch events = true)
    : let queue := (State.initialize (Work.fromExecution work)).replayGraphEvents events
      let failed :=
        (State.initialize (Work.fromExecution work)).objectFailureContributions events
      queue.UncancelledRetiredHealthy work failed
      ∧ queue.RootAncestorsHealthy work failed
      ∧ queue.MissingParentAncestorsHealthy work failed := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have replay
      : let queue := (State.initialize (Work.fromExecution work)).replayGraphEvents events
        let failed := (State.initialize (Work.fromExecution work)).objectFailureContributions events
        queue.UncancelledRetiredHealthy work failed
        ∧ queue.RootAncestorsHealthy work failed
        ∧ queue.ParentRegistryClosed parents := by
    induction valid with
    | nil =>
        exact ⟨.of_empty _ _, .of_empty _ _, createWorkQueue_parentRegistryClosed canonical⟩
    | @append before event valid matching fresh ready ih =>
        have priorStarted := State.acceptsBatch_prefix started
        have prior := ih priorStarted
        let queue := (State.initialize (Work.fromExecution work)).replayGraphEvents before
        let failed := (State.initialize (Work.fromExecution work)).objectFailureContributions before
        have accepted : queue.acceptsGraphEvent event = true := by
          apply State.acceptsBatch_atPrefix _ before event []
          simpa only [List.append_nil] using started
        have acceptedAt : ∀ past next, (past ++ [next]).IsPrefix before →
            ((State.initialize (Work.fromExecution work)).replayGraphEvents past).acceptsGraphEvent
              next = true := by
          intro past next earlier
          obtain ⟨after, same⟩ := earlier
          apply State.acceptsBatch_atPrefix (State.initialize (Work.fromExecution work)) past next after
          simpa only [← same, List.append_assoc, List.singleton_append] using priorStarted
        have ledger : queue.OwnerAccounting work parents before :=
          generated.replayGraphEvents_ownerAccounting_of_eachAccepted canonical valid acceptedAt
        have same := generated.failureInventories_groupInvalidated_iff
          before valid priorStarted
        have owners : queue.HealthyRegisteredTaskAccounting work
            (GraphEvent.taskSettlements before) failed := ledger.owners.congr_failures same
        have counts := (createWorkQueue_groupErrorAccounting (Work.fromExecution work) work
          ).replayGraphEvents (before := []) (createWorkQueue_pendingAccounting work)
            generated before valid priorStarted
        simp only [List.append_nil] at counts
        have failedKnown : ∀ occurrence ∈ failed,
            ∃ owners producer payload,
              TaskAt work occurrence owners producer payload ∧ payload.failure.isSome = true := by
          intro occurrence member
          obtain ⟨owners, producer, path, errors, known⟩ :=
            valid.failureSettlements_known occurrence
              (((State.initialize (Work.fromExecution work)).objectFailureContributions_sublist before
                ).subset member)
          exact ⟨owners, producer, _, known, rfl⟩
        have structural := generated.replayGraphEvents_structuralRetirement before
          (fun _ member => valid.eachMatches member)
        have registry := prior.2.2.handleGraphEvent ledger.pending.liveGroups
          ledger.pending.taskGroups event matching canonical
        have health
            : (queue.handleGraphEvent event).1.UncancelledRetiredHealthy work
                (queue.objectFailureContribution event ++ failed)
              ∧ (queue.handleGraphEvent event).1.RootAncestorsHealthy work
                (queue.objectFailureContribution event ++ failed) := by
          cases event with
          | taskSuccess occurrence result =>
              exact queue.taskSuccess_retiredHealth prior.1 prior.2.1 generated ledger.groups
                ledger.childLinks canonical counts failedKnown matching
          | streamItems stream items =>
              exact queue.streamItems_retiredHealth prior.1 prior.2.1 generated ledger.groups
                ledger.childLinks canonical counts failedKnown matching
          | streamSuccess stream =>
              change (queue.streamSuccess stream).1.UncancelledRetiredHealthy work failed
                ∧ (queue.streamSuccess stream).1.RootAncestorsHealthy work failed
              unfold State.streamSuccess
              split <;> exact ⟨prior.1, prior.2.1⟩
          | streamFailure stream errors =>
              change (queue.streamFailure stream errors).1.UncancelledRetiredHealthy work failed
                ∧ (queue.streamFailure stream errors).1.RootAncestorsHealthy work failed
              unfold State.streamFailure
              split <;> exact ⟨prior.1, prior.2.1⟩
          | taskFailure occurrence errors =>
              cases found : queue.taskNode? occurrence with
              | none => simp [State.acceptsGraphEvent, found] at accepted
              | some node =>
                  cases guarded : queue.taskHasHealthyOwner node.task with
                  | false =>
                      have roots : (queue.taskFailure occurrence errors).1.RootAncestorsHealthy
                          work failed := fun key active =>
                        prior.2.1 key (queue.taskFailure_rootsSubset occurrence errors active)
                      simpa only [State.objectFailureContribution, found, guarded,
                        Bool.false_eq_true, ↓reduceIte, List.nil_append,
                        State.handleGraphEvent, queue, failed]
                        using And.intro (prior.1.taskFailure occurrence errors) roots
                  | true =>
                      obtain ⟨member, occurrenceEq⟩ := State.taskNode?_some found
                      have registered := ledger.pending.started node member
                      have known := ledger.pending.matching node.task registered
                      have unsettled
                          : node.task.occurrence ∉ GraphEvent.taskSettlements before := by
                        rw [occurrenceEq]
                        exact fun member => fresh.2.2.1 occurrence List.mem_cons_self
                          (GraphEvent.taskSettlements_subsetIdentities before member)
                      have retired := prior.1.cons_fresh structural.2 generated owners registered
                        known unsettled
                      have protectedRoots := prior.2.1.append_fresh structural.1 generated owners
                        registered known unsettled
                      have roots
                          : queue.RootAncestorsHealthy work (node.task.occurrence :: failed) := by
                        intro key active record dependencies descriptor sameKey ancestor member
                          invalid
                        exact protectedRoots key active record dependencies descriptor sameKey
                          ancestor member (invalid.mono (by
                            intro token included
                            rcases List.mem_cons.mp included with rfl | old
                            · exact List.mem_append_right _ List.mem_cons_self
                            · exact List.mem_append_left _ old))
                      have nextRoots
                          : (queue.taskFailure occurrence errors).1.RootAncestorsHealthy work
                              (node.task.occurrence :: failed) := fun key active =>
                        roots key (queue.taskFailure_rootsSubset occurrence errors active)
                      simpa only [State.objectFailureContribution, found, guarded,
                        ↓reduceIte, List.singleton_append, occurrenceEq,
                        State.handleGraphEvent, queue, failed]
                        using And.intro (retired.taskFailure occurrence errors) nextRoots
        rw [State.replayGraphEvents_append, State.objectFailureContributions_append]
        simpa only [State.objectFailureContributions, List.nil_append]
          using And.intro health.1 ⟨health.2, registry⟩
  have acceptedAt
      : ∀ past next, (past ++ [next]).IsPrefix events →
          ((State.initialize (Work.fromExecution work)).replayGraphEvents past).acceptsGraphEvent next
            = true := by
    intro past next earlier
    obtain ⟨after, same⟩ := earlier
    apply State.acceptsBatch_atPrefix (State.initialize (Work.fromExecution work)) past next after
    simpa only [← same, List.append_assoc, List.singleton_append] using started
  have ledger :=
    generated.replayGraphEvents_ownerAccounting_of_eachAccepted canonical valid acceptedAt
  exact ⟨
    replay.1,
    replay.2.1,
    replay.1.missingParent generated ledger.canonical canonical
      (fun node member parent parentEq =>
        replay.2.2.parent_registered ledger.pending.liveGroups
          ledger.canonical member parentEq)
  ⟩

/-- Actual normalized host batches retain both health certificates and the guard boundary.
Witness: the executable start law flattens to accepted sequential replay; batching changes
only the terminal flag, which none of the three state predicates inspects.
-/
theorem ExecutedWork.runNormalized_retiredHealth {work : Execution.Work}
    (generated : ExecutedWork work) (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    : let queue := ((State.initialize (Work.fromExecution work)).runNormalized batches).1
      let failed :=
        (State.initialize (Work.fromExecution work)).objectFailureContributions
          batches.flatten
      queue.UncancelledRetiredHealthy work failed
      ∧ queue.RootAncestorsHealthy work failed
      ∧ queue.MissingParentAncestorsHealthy work failed := by
  have accepts := (State.initialize (Work.fromExecution work)).batchesStarted_acceptsBatch batches
    (by rwa [← inputsStarted_eq_batchesStarted])
  have health := generated.replayGraphEvents_retiredHealth batches.flatten valid accepts
  obtain ⟨terminated, same⟩ := createWorkQueue_runNormalized_stateCore started
  rw [same]
  exact health

/-- The health guard is sound on every valid started generated replay, including absent
successfully retired parents. Witness: the joint replay theorem now supplies the only
historical premise of the earlier finite-parent-walk reflection theorem.
-/
theorem ExecutedWork.replayGraphEvents_groupIsHealthy_recordUninvalidated
    {work : Execution.Work} (generated : ExecutedWork work) (events : List GraphEvent)
    (valid : ValidGraphEvents work events)
    (started : (State.initialize (Work.fromExecution work)).acceptsBatch events = true)
    {key : Nat}
    (healthy
      : ((State.initialize (Work.fromExecution work)).replayGraphEvents
          events).groupIsHealthy
          key
        = true)
    : ¬GroupRecordInvalidated work
        ((State.initialize (Work.fromExecution work)).objectFailureContributions events)
        key :=
  createWorkQueue_replayGraphEvents_groupIsHealthy_recordUninvalidated generated valid
    started (generated.replayGraphEvents_retiredHealth events valid started).2.2 healthy

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
