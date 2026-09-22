import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.OwnerReplayClosure

/-! Source failures and accepted failures have the same group-invalidation closure. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Invalidation equivalence is preserved when both ledgers record the same settlement
-----------------------------------------------------------------------------------------

/-- Equivalent group-invalidation closures stay equivalent after adding the same failure.
Witness: a use of the new token is copied directly; each old direct cause is translated
by the supplied equivalence, then the same defer dependencies propagate it.
-/
theorem groupInvalidated_cons_congr {work : Execution.Work}
    {before after : List Occurrence}
    (same : ∀ key, GroupInvalidated work before key ↔ GroupInvalidated work after key)
    (occurrence : Occurrence) (key : Nat)
    : GroupInvalidated work (occurrence :: before) key
      ↔ GroupInvalidated work (occurrence :: after) key := by
  have transfer {left right : List Occurrence}
      (translate : ∀ key, GroupInvalidated work left key → GroupInvalidated work right key)
      {key : Nat} (failure : GroupInvalidated work (occurrence :: left) key)
      : GroupInvalidated work (occurrence :: right) key := by
    induction failure with
    | @task task owners key known owner member =>
        rcases List.mem_cons.mp member with latest | earlier
        · exact .task known owner (List.mem_cons.mpr (.inl latest))
        · exact (translate key (.task known owner earlier)).mono
            (fun _ member => List.mem_cons_of_mem _ member)
    | groupDependency known member _ ih => exact .groupDependency known member ih
  exact ⟨transfer (fun key => (same key).mp), transfer (fun key => (same key).mpr)⟩

/-- Group-invalidation equivalence also covers taskless registration records.
Witness: translate direct failed-owner causes using group equivalence, then reuse each
record-ancestry step. Taskless records need no fictitious contributor descriptor.
-/
theorem groupRecordInvalidated_congr {work : Execution.Work}
    {before after : List Occurrence}
    (same : ∀ key, GroupInvalidated work before key ↔ GroupInvalidated work after key)
    (key : Nat)
    : GroupRecordInvalidated work before key ↔ GroupRecordInvalidated work after key := by
  have transfer {left right : List Occurrence}
      (translate : ∀ key, GroupInvalidated work left key → GroupInvalidated work right key)
      {key : Nat} (failure : GroupRecordInvalidated work left key)
      : GroupRecordInvalidated work right key := by
    induction failure with
    | task known owner member =>
        exact (translate _ (.task known owner member)).toRecordInvalidated
    | ancestor known member _ ih => exact .ancestor known member ih
  exact ⟨transfer (fun key => (same key).mp), transfer (fun key => (same key).mpr)⟩

-----------------------------------------------------------------------------------------
-- Ignored source failures add no new invalidated owners during generated started replay
-----------------------------------------------------------------------------------------

/-- Full source failures and guard-accepted object failures invalidate exactly the same
groups during valid started replay. Witness: an accepted failure extends both ledgers;
the proved owner ledger shows that an ignored failure's owners were already invalidated.
This equates causal group health, not failure tokens, error counts, or ordered cut evidence.
-/
theorem ExecutedWork.failureInventories_groupInvalidated_iff_of_eachAccepted
    {work : Execution.Work} (generated : ExecutedWork work) {events : List GraphEvent}
    (valid : ValidGraphEvents work events)
    (acceptedAt
      : ∀ before event,
          (before ++ [event]).IsPrefix events
          → ((State.initialize (Work.fromExecution work)).replayGraphEvents
              before).acceptsGraphEvent
              event
            = true)
    : ∀ key,
        GroupInvalidated work (GraphEvent.failureSettlements events) key
        ↔ GroupInvalidated work
            ((State.initialize (Work.fromExecution work)).objectFailureContributions
              events)
            key := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  induction valid with
  | nil => intro key; rfl
  | @append before event valid matching fresh ready ih =>
      have prefixAccepted := fun past next (earlier : (past ++ [next]).IsPrefix before) =>
        acceptedAt past next (earlier.trans (List.prefix_append before [event]))
      have prior := ih prefixAccepted
      have accepted := acceptedAt before event (List.prefix_refl _)
      intro key
      rw [GraphEvent.failureSettlements_append, State.objectFailureContributions_append]
      simp only [State.objectFailureContributions, List.nil_append]
      cases event with
      | taskSuccess | streamItems | streamSuccess | streamFailure => exact prior key
      | taskFailure occurrence errors =>
          let queue := (State.initialize (Work.fromExecution work)).replayGraphEvents before
          change queue.acceptsGraphEvent (.taskFailure occurrence errors) = true at accepted
          change GroupInvalidated work (occurrence :: GraphEvent.failureSettlements before) key
            ↔ GroupInvalidated work
              (queue.objectFailureContribution (.taskFailure occurrence errors)
                ++ (State.initialize (Work.fromExecution work)).objectFailureContributions before) key
          have ledger : queue.OwnerAccounting work parents before :=
            generated.replayGraphEvents_ownerAccounting_of_eachAccepted canonical valid
              prefixAccepted
          cases found : queue.taskNode? occurrence with
          | none => simp [State.acceptsGraphEvent, found] at accepted
          | some node =>
              cases guarded : queue.taskHasHealthyOwner node.task with
              | true =>
                  simpa only [GraphEvent.groupFailures, State.objectFailureContribution,
                    found, guarded, ↓reduceIte, List.singleton_append]
                    using groupInvalidated_cons_congr prior occurrence key
              | false =>
                  obtain ⟨member, same⟩ := State.taskNode?_some found
                  have registered := ledger.pending.started node member
                  obtain ⟨_, payload, producer, _, known⟩ :=
                    (ledger.pending.matching node.task registered).1
                  have unsettled : node.task.occurrence ∉ GraphEvent.taskSettlements before := by
                    rw [same]
                    exact fun member => fresh.2.2.1 occurrence List.mem_cons_self
                      (GraphEvent.taskSettlements_subsetIdentities before member)
                  have redundant := ledger.owners.rejectedTask_invalidation_iff
                    ledger.pending.matching ledger.supported ledger.cancelled generated
                    (ledger.toHealthyCounterAccounting.descriptors canonical)
                    registered unsettled ⟨producer, payload, known⟩ guarded key
                  rw [same] at redundant
                  simpa only [GraphEvent.groupFailures, State.objectFailureContribution,
                    found, guarded, Bool.false_eq_true, ↓reduceIte, List.singleton_append,
                    List.nil_append]
                    using redundant.trans (prior key)

/-- Valid source events accepted by the start checker have equivalent failure closures.
Witness: executable prefix acceptance supplies the eventwise induction's only start law.
-/
theorem ExecutedWork.failureInventories_groupInvalidated_iff
    {work : Execution.Work} (generated : ExecutedWork work) (events : List GraphEvent)
    (valid : ValidGraphEvents work events)
    (started : (State.initialize (Work.fromExecution work)).acceptsBatch events = true)
    (key : Nat)
    : GroupInvalidated work (GraphEvent.failureSettlements events) key
      ↔ GroupInvalidated work
          ((State.initialize (Work.fromExecution work)).objectFailureContributions events)
          key := by
  apply generated.failureInventories_groupInvalidated_iff_of_eachAccepted valid _ key
  intro before event earlier
  obtain ⟨after, same⟩ := earlier
  apply State.acceptsBatch_atPrefix _ before event after
  simpa only [← same, List.append_assoc, List.singleton_append] using started

/-- Started normalized inputs have the same group-invalidation closure in both inventories.
Witness: batch start discipline gives every actual sequential-prefix acceptance.
-/
theorem ExecutedWork.runNormalized_failureInventories_groupInvalidated_iff
    {work : Execution.Work} (generated : ExecutedWork work)
    (batches : List (List GraphEvent)) (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true) (key : Nat)
    : GroupInvalidated work (GraphEvent.failureSettlements batches.flatten) key
      ↔ GroupInvalidated work
          ((State.initialize (Work.fromExecution work)).objectFailureContributions
            batches.flatten)
          key :=
  generated.failureInventories_groupInvalidated_iff_of_eachAccepted valid
    (inputsStarted_eachAccepted work batches started) key

-----------------------------------------------------------------------------------------
-- Transfer the checked owner and pending ledgers without equating failure tokens
-----------------------------------------------------------------------------------------

/-- Equivalent invalidation closures transport registered healthy-owner accounting.
Witness: health under the target inventory excludes the equivalent source invalidation.
The actual queue, settlement ledger, owner node, and task membership are unchanged.
-/
theorem State.HealthyRegisteredTaskAccounting.congr_failures {queue : State}
    {work settled before after}
    (prior : queue.HealthyRegisteredTaskAccounting work settled before)
    (same : ∀ key, GroupInvalidated work before key ↔ GroupInvalidated work after key)
    : queue.HealthyRegisteredTaskAccounting work settled after := by
  intro task member fresh key contributes healthy
  exact prior task member fresh key contributes (fun failed => healthy ((same key).mp failed))

/-- Equivalent invalidation closures transport exact healthy pending counts.
Witness: the same live group is healthy in both inventories; no counter or count filter
is modified and no failure occurrence is reclassified as an error contribution.
-/
theorem State.HealthyPendingTracks.congr_failures {queue : State}
    {work settled before after} (prior : queue.HealthyPendingTracks work settled before)
    (same : ∀ key, GroupInvalidated work before key ↔ GroupInvalidated work after key)
    : queue.HealthyPendingTracks work settled after := by
  intro node member healthy
  exact prior node member (fun failed => healthy ((same node.group.node.key).mp failed))

/-- Valid started sequential replay retains owners and exact counters under accepted
object failures. Witness: full-source owner replay transported by failure-closure
equivalence. All source task outcomes remain in the settlement ledger, including ignored
ones; only the causal-health inventory is projected to accepted failures.
-/
theorem ExecutedWork.replayGraphEvents_acceptedOwnerAccounting_of_eachAccepted
    {work : Execution.Work} (generated : ExecutedWork work) {events : List GraphEvent}
    (valid : ValidGraphEvents work events)
    (acceptedAt
      : ∀ before event,
          (before ++ [event]).IsPrefix events
          → ((State.initialize (Work.fromExecution work)).replayGraphEvents
              before).acceptsGraphEvent
              event
            = true)
    : let queue := (State.initialize (Work.fromExecution work)).replayGraphEvents events
      let settled := GraphEvent.taskSettlements events
      let failed :=
        (State.initialize (Work.fromExecution work)).objectFailureContributions events
      queue.HealthyRegisteredTaskAccounting work settled failed
      ∧ queue.HealthyPendingTracks work settled failed := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have ledger := generated.replayGraphEvents_ownerAccounting_of_eachAccepted
    canonical valid acceptedAt
  have same := generated.failureInventories_groupInvalidated_iff_of_eachAccepted valid acceptedAt
  exact ⟨ledger.owners.congr_failures same, ledger.healthy.congr_failures same⟩

/-- Started normalized replay likewise has accepted-inventory ownership and exact counts.
Witness: normalized source-ledger replay and the same proved invalidation equivalence.
No missing-parent health or output-admission premise is assumed.
-/
theorem ExecutedWork.runNormalized_acceptedOwnerAccounting {work : Execution.Work}
    (generated : ExecutedWork work) (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    : let queue := ((State.initialize (Work.fromExecution work)).runNormalized batches).1
      let settled := GraphEvent.taskSettlements batches.flatten
      let failed :=
        (State.initialize (Work.fromExecution work)).objectFailureContributions
          batches.flatten
      queue.HealthyRegisteredTaskAccounting work settled failed
      ∧ queue.HealthyPendingTracks work settled failed := by
  obtain ⟨_, _, ledger⟩ := generated.runNormalized_ownerAccounting_of_started batches valid started
  have same := generated.runNormalized_failureInventories_groupInvalidated_iff batches valid started
  exact ⟨ledger.owners.congr_failures same, ledger.healthy.congr_failures same⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
