import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.AcceptedFailureEquivalence

/-! A healthy retired record stays healthy through later valid started source events. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- A fresh registered failure cannot reach a retired healthy record or its ancestors
-----------------------------------------------------------------------------------------

/-- Adding a fresh registered failure preserves a healthy retired record.
Witness: flatten the possible cause to a contributing owner of the record or its full
ancestry. That owner is retired; healthy-owner accounting therefore makes the supposedly
fresh contributing task already settled. Older causes contradict the prior health.
-/
theorem State.RetiredGroup.healthy_cons_fresh {queue : State}
    {work settled failed node dependencies}
    (retired : queue.RetiredGroup node.key)
    (ancestors : queue.AncestorsRetired work node.key)
    (generated : ExecutedWork work) (known : GroupRecordAt work node dependencies)
    (healthy : ¬GroupRecordInvalidated work failed node.key)
    (accounted : queue.HealthyRegisteredTaskAccounting work settled failed)
    {task : Task} (registered : task ∈ queue.tasks)
    (matching : TaskMatches work task) (fresh : task.occurrence ∉ settled)
    : ¬GroupRecordInvalidated work (task.occurrence :: failed) node.key := by
  intro invalid
  obtain ⟨occurrence, owners, owner, descriptor, recorded, contributes, inChain⟩ :=
    (generated.groupRecordInvalidated_iff known).mp invalid
  rcases List.mem_cons.mp recorded with same | old
  · subst occurrence
    obtain ⟨producer, payload, structural⟩ := descriptor
    obtain ⟨⟨address, actualPayload, actualProducer, _, actual⟩, _⟩ := matching
    have contributor : owner ∈ task.groups.map Execution.DeliveryNode.key :=
      (structural.unique actual).1 ▸ contributes
    have ownerRetired : queue.RetiredGroup owner := by
      rcases List.mem_cons.mp inChain with same | ancestor
      · exact same ▸ retired
      · exact ancestors node dependencies known rfl owner ancestor
          task.occurrence owners ⟨producer, payload, structural⟩ contributes
    have ownerHealthy : ¬GroupInvalidated work failed owner := by
      intro failedOwner
      rcases List.mem_cons.mp inChain with same | ancestor
      · exact healthy (same ▸ failedOwner.toRecordInvalidated)
      · exact healthy (.ancestor known ancestor failedOwner.toRecordInvalidated)
    exact fresh (accounted.retired_contributor_settled registered contributor
      ownerHealthy ownerRetired)
  · exact healthy ((generated.groupRecordInvalidated_iff known).mpr
      ⟨occurrence, owners, owner, descriptor, old, contributes, inChain⟩)

-----------------------------------------------------------------------------------------
-- Every future prefix reuses the independently proved actual owner ledger
-----------------------------------------------------------------------------------------

/-- Source-ledger health of a protected retired record survives every started continuation.
Witness: induct over valid source events after the supplied prefix; retirement persists
through all handlers, while each new failure uses the current proved owner ledger.
No output admission or missing-parent-health premise enters this induction.
-/
private theorem ExecutedWork.retiredRecord_sourceHealth_stable
    {work : Execution.Work} (generated : ExecutedWork work) {events : List GraphEvent}
    (valid : ValidGraphEvents work events)
    (acceptedAt
      : ∀ before event,
          (before ++ [event]).IsPrefix events
          → ((State.initialize (Work.fromExecution work)).replayGraphEvents
              before).acceptsGraphEvent
              event
            = true)
    {node dependencies} (known : GroupRecordAt work node dependencies)
    {before : List GraphEvent} (earlier : before.IsPrefix events)
    (retired
      : ((State.initialize (Work.fromExecution work)).replayGraphEvents
          before).RetiredGroup
          node.key)
    (ancestors
      : ((State.initialize (Work.fromExecution work)).replayGraphEvents
          before).AncestorsRetired
          work node.key)
    (healthy
      : ¬GroupRecordInvalidated work (GraphEvent.failureSettlements before) node.key)
    : let queue := (State.initialize (Work.fromExecution work)).replayGraphEvents events
      queue.RetiredGroup node.key
      ∧ queue.AncestorsRetired work node.key
      ∧ ¬GroupRecordInvalidated work (GraphEvent.failureSettlements events) node.key := by
  induction valid generalizing before with
  | nil =>
      obtain rfl := List.eq_nil_of_prefix_nil earlier
      exact ⟨retired, ancestors, healthy⟩
  | @append previous event valid matching fresh ready ih =>
      rcases List.prefix_concat_iff.mp earlier with same | shorter
      · subst before
        exact ⟨retired, ancestors, healthy⟩
      · have prefixAccepted := fun past next (included : (past ++ [next]).IsPrefix previous) =>
          acceptedAt past next (included.trans (List.prefix_append previous [event]))
        obtain ⟨oldRetired, oldAncestors, oldHealthy⟩ :=
          ih prefixAccepted shorter retired ancestors healthy
        have nextRetired := oldRetired.handleGraphEvent event
        have nextAncestors := oldAncestors.mono
          (fun _ retired => retired.handleGraphEvent event)
        rw [State.replayGraphEvents_append]
        refine ⟨nextRetired, nextAncestors, ?_⟩
        rw [GraphEvent.failureSettlements_append]
        cases event with
        | taskSuccess | streamItems | streamSuccess | streamFailure => exact oldHealthy
        | taskFailure occurrence errors =>
            let queue := (State.initialize (Work.fromExecution work)).replayGraphEvents previous
            have accepted := acceptedAt previous (.taskFailure occurrence errors)
              (List.prefix_refl _)
            change queue.acceptsGraphEvent (.taskFailure occurrence errors) = true at accepted
            obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
            have ledger : queue.OwnerAccounting work parents previous :=
              generated.replayGraphEvents_ownerAccounting_of_eachAccepted canonical valid
                prefixAccepted
            cases found : queue.taskNode? occurrence with
            | none => simp [State.acceptsGraphEvent, found] at accepted
            | some taskNode =>
                obtain ⟨member, same⟩ := State.taskNode?_some found
                have registered := ledger.pending.started taskNode member
                have unsettled
                    : taskNode.task.occurrence ∉ GraphEvent.taskSettlements previous := by
                  rw [same]
                  exact fun member => fresh.2.2.1 occurrence List.mem_cons_self
                    (GraphEvent.taskSettlements_subsetIdentities previous member)
                have safe := oldRetired.healthy_cons_fresh oldAncestors generated known
                  oldHealthy ledger.owners registered
                  (ledger.pending.matching taskNode.task registered) unsettled
                simpa only [GraphEvent.groupFailures, List.singleton_append, same]
                  using safe

/-- Once a generated record retires healthy, every valid started continuation keeps it
healthy under accepted failures. Witness: derive its ancestor-retirement certificate,
transport health to the source ledger, apply the continuation induction, then transport
back. Later child registration and arbitrary success/failure interleavings are included.
-/
theorem ExecutedWork.retiredRecord_health_stable_of_eachAccepted
    {work : Execution.Work} (generated : ExecutedWork work) {events : List GraphEvent}
    (valid : ValidGraphEvents work events)
    (acceptedAt
      : ∀ before event,
          (before ++ [event]).IsPrefix events
          → ((State.initialize (Work.fromExecution work)).replayGraphEvents
              before).acceptsGraphEvent
              event
            = true)
    {node dependencies} (known : GroupRecordAt work node dependencies)
    {before : List GraphEvent} (earlier : before.IsPrefix events)
    (retired
      : ((State.initialize (Work.fromExecution work)).replayGraphEvents
          before).RetiredGroup
          node.key)
    (healthy
      : ¬GroupRecordInvalidated work
          ((State.initialize (Work.fromExecution work)).objectFailureContributions before)
          node.key)
    : ¬GroupRecordInvalidated work
        ((State.initialize (Work.fromExecution work)).objectFailureContributions events)
        node.key := by
  have priorValid := valid.prefix earlier
  have priorAccepted := fun past next (included : (past ++ [next]).IsPrefix before) =>
    acceptedAt past next (included.trans earlier)
  have ancestry := generated.replayGraphEvents_healthyRetiredAncestors before priorValid
    node.key retired healthy
  have sameBefore := groupRecordInvalidated_congr
    (generated.failureInventories_groupInvalidated_iff_of_eachAccepted priorValid priorAccepted)
    node.key
  have durable := generated.retiredRecord_sourceHealth_stable valid acceptedAt known
    earlier retired ancestry (fun invalid => healthy (sameBefore.mp invalid))
  have sameAfter := groupRecordInvalidated_congr
    (generated.failureInventories_groupInvalidated_iff_of_eachAccepted valid acceptedAt) node.key
  exact fun invalid => durable.2.2 (sameAfter.mpr invalid)

/-- The executable source start checker supplies all continuation acceptance premises.
Witness: restrict batch acceptance to each concrete source prefix and apply stability.
-/
theorem ExecutedWork.retiredRecord_health_stable
    {work : Execution.Work} (generated : ExecutedWork work) {events : List GraphEvent}
    (valid : ValidGraphEvents work events)
    (started : (State.initialize (Work.fromExecution work)).acceptsBatch events = true)
    {node dependencies} (known : GroupRecordAt work node dependencies)
    {before : List GraphEvent} (earlier : before.IsPrefix events)
    (retired
      : ((State.initialize (Work.fromExecution work)).replayGraphEvents
          before).RetiredGroup
          node.key)
    (healthy
      : ¬GroupRecordInvalidated work
          ((State.initialize (Work.fromExecution work)).objectFailureContributions before)
          node.key)
    : ¬GroupRecordInvalidated work
        ((State.initialize (Work.fromExecution work)).objectFailureContributions events)
        node.key := by
  apply generated.retiredRecord_health_stable_of_eachAccepted valid _ known earlier retired healthy
  intro past event included
  obtain ⟨after, same⟩ := included
  apply State.acceptsBatch_atPrefix _ past event after
  simpa only [← same, List.append_assoc, List.singleton_append] using started

/-- Arbitrary started host batching retains the same retired-record health guarantee.
Witness: flattening supplies every actual sequential-prefix acceptance; no response
batching choice changes the accepted failure inventory used by this certificate.
-/
theorem ExecutedWork.runNormalized_retiredRecord_health_stable {work : Execution.Work}
    (generated : ExecutedWork work) (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true) {node dependencies}
    (known : GroupRecordAt work node dependencies) {before : List GraphEvent}
    (earlier : before.IsPrefix batches.flatten)
    (retired
      : ((State.initialize (Work.fromExecution work)).replayGraphEvents
          before).RetiredGroup
          node.key)
    (healthy
      : ¬GroupRecordInvalidated work
          ((State.initialize (Work.fromExecution work)).objectFailureContributions before)
          node.key)
    : ¬GroupRecordInvalidated work
        ((State.initialize (Work.fromExecution work)).objectFailureContributions
          batches.flatten)
        node.key :=
  generated.retiredRecord_health_stable_of_eachAccepted valid
    (inputsStarted_eachAccepted work batches started) known earlier retired healthy

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
