import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialStartupSourceFrames
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialStartupReportingAvailability

/-! Retired-source health accounts for initial observations without consuming them. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Registered failed computations cannot invalidate uncancelled successful retirements.
The failure list is independent of the consumed notification ledger. Registration and the
fixed failed outcome exclude a consumed success, including for initial cached rejections.
-/
theorem UncancelledReplayFrame.retiredHealth_ofRegisteredFailures
    {queue work parents before} (frame : UncancelledReplayFrame queue work parents before)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    {failed : List Occurrence}
    (registered
      : ∀ occurrence ∈ failed,
          ∃ task ∈ queue.tasks,
            task.occurrence = occurrence
            ∧ task.occurrence ∉ GraphEvent.groupSettlements before)
    : queue.UncancelledRetiredHealthy work failed
      ∧ queue.RootAncestorsHealthy work failed
      ∧ queue.MissingParentAncestorsHealthy work failed := by
  have retiredHealth : queue.UncancelledRetiredHealthy work
      failed := by
    intro node dependencies known retired uncancelled
    have loop (causes : List Occurrence)
        (included : causes.Subset failed)
        : ¬GroupRecordInvalidated work causes node.ref := by
      induction causes with
      | nil => exact fun invalid => invalid.nonempty rfl
      | cons occurrence rest ih =>
          obtain ⟨task, registered, same, fresh⟩ :=
            registered occurrence (included List.mem_cons_self)
          have healthy := ih (fun _ member => included (List.mem_cons_of_mem _ member))
          have enlarged := retired.healthy_cons_fresh_of_uncancelledAccounting
            (frame.roots.retired node.ref retired uncancelled) uncancelled
            (frame.markers node.ref retired uncancelled node dependencies known rfl)
            generated known healthy frame.owners registered
            (frame.pending.matching task registered) fresh
          simpa only [same] using enlarged
    exact loop _ (List.Subset.refl _)
  refine ⟨
    retiredHealth,
    ?_,
    retiredHealth.missingParent generated frame.parent.fields canonical
      (fun node member parent parentEq =>
        frame.parent.closed.parent_registered frame.parent.live frame.parent.fields member
          parentEq)
  ⟩
  intro ref active node dependencies known sameRef ancestor member invalid
  obtain ⟨liveNode, live, liveRef⟩ := List.mem_map.mp (frame.roots.live.present ref active)
  have ancestorMarkers := frame.markers.live_record_ancestors frame.parent.safe
    frame.parent.fields frame.parent.closed frame.parent.live canonical known
    ⟨liveNode, live, liveRef.trans sameRef.symm⟩
  have excludes {target} (failure : GroupRecordInvalidated work
      failed target) : target ∈ dependencies → False := by
    induction failure with
    | @task occurrence owners target descriptor contributes recorded =>
        intro inChain
        obtain ⟨task, registered, same, fresh⟩ := registered occurrence recorded
        obtain ⟨producer, payload, taskKnown⟩ := descriptor
        obtain ⟨⟨_, _, _, _, actual⟩, _⟩ := frame.pending.matching task registered
        rw [same] at actual
        have taskContributes : target ∈ task.groups.map Execution.DeliveryNode.ref :=
          (taskKnown.unique actual).1 ▸ contributes
        have retired := frame.roots.live.roots ref active node dependencies known sameRef
          target inChain occurrence owners ⟨producer, payload, taskKnown⟩ contributes
        have uncancelled := ancestorMarkers target inChain occurrence owners
          ⟨producer, payload, taskKnown⟩ contributes
        exact fresh (frame.owners.retired_contributor_settled registered taskContributes
          uncancelled retired)
    | @ancestor other otherDependencies target descriptor included failure ih =>
        intro inChain
        exact ih ((generated.groupRecordAncestors_trans known descriptor inChain) included)
  exact excludes invalid member

/-- Every supplied initial failure remains a registered unsuccessful root computation.
This uses permanent registration, not a claim that its callback was consumed or started.
-/
theorem UncancelledReplayFrame.initialFailures_registeredFresh
    {queue work parents before startup}
    (frame : UncancelledReplayFrame queue work parents before)
    (matched : InitialStartup.MatchesWork startup work)
    (valid : ValidGraphEvents work before)
    : ∀ occurrence ∈ startup.failures.map Prod.fst,
        ∃ task ∈ queue.tasks,
          task.occurrence = occurrence
          ∧ task.occurrence ∉ GraphEvent.groupSettlements before := by
  intro occurrence supplied
  obtain ⟨⟨other, errors⟩, member, same⟩ := List.mem_map.mp supplied
  dsimp only at same
  subst other
  obtain ⟨owners, path, known⟩ := InitialStartup.matched_rootFailure matched member
  obtain ⟨address, rfl⟩ := known.object_occurrence
  obtain ⟨task, registered, identity, _⟩ := frame.producerRegistrations.root_registered known
  refine ⟨task, registered, identity, ?_⟩
  intro success
  obtain ⟨otherOwners, producer, payload, descriptor, succeeds⟩ :=
    valid.groupSettlements_succeed (identity ▸ success)
  have exactPayload := (known.unique descriptor).2.2
  subst payload
  simp [Payload.failure] at succeeds

/-- Both initial cache availability and consumed task failures preserve retired health.
No initial observation is inserted into the source history or assumed to have started.
-/
theorem UncancelledReplayFrame.retiredHealth_withInitialFailures
    {queue work parents before startup}
    (frame : UncancelledReplayFrame queue work parents before)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (matched : InitialStartup.MatchesWork startup work)
    (valid : ValidGraphEvents work before)
    : let failed := startup.failures.map Prod.fst ++ GraphEvent.failureSettlements before
      queue.UncancelledRetiredHealthy work failed
      ∧ queue.RootAncestorsHealthy work failed
      ∧ queue.MissingParentAncestorsHealthy work failed := by
  apply frame.retiredHealth_ofRegisteredFailures generated canonical
  intro occurrence member
  rcases List.mem_append.mp member with initial | consumed
  · exact frame.initialFailures_registeredFresh matched valid occurrence initial
  · obtain ⟨task, registered, identity⟩ := frame.failures occurrence consumed
    obtain ⟨owners, producer, path, errors, known⟩ :=
      valid.failureSettlements_known occurrence consumed
    refine ⟨task, registered, identity, ?_⟩
    intro success
    obtain ⟨otherOwners, birth, payload, descriptor, succeeds⟩ :=
      valid.groupSettlements_succeed (identity ▸ success)
    have exactPayload := (known.unique descriptor).2.2
    subst payload
    simp [Payload.failure] at succeeds

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
