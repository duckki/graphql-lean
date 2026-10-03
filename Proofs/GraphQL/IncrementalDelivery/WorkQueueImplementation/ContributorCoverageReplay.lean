import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ContributorFailureCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ContributorStreamCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.AcceptedFailureEquivalence

/-! Actual generated replay keeps every healthy live registered contributor root-covered. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Derive every handler premise from generated work and the existing source laws
-----------------------------------------------------------------------------------------

/-- Every valid started source prefix covers its healthy live permanent contributors.
Witness: joint coverage/parent-registry induction over actual handlers. Independent replay
theorems supply counters, accepted failures, cancellation support, complete links, and
region freshness; emitted-event admission is never assumed.
-/
theorem ExecutedWork.replayGraphEvents_healthyContributorsCovered {work : Execution.Work}
    (generated : ExecutedWork work) (events : List GraphEvent)
    (valid : ValidGraphEvents work events)
    (started : (State.initialize (Work.fromExecution work)).acceptsBatch events = true)
    : let initial := State.initialize (Work.fromExecution work)
      (initial.replayGraphEvents events).HealthyContributorsCovered work
        (initial.objectFailureContributions events) := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have initialRegistered := createWorkQueue_registration work
  have initialLinks := createWorkQueue_parentLinksComplete (Work.fromExecution work) parents
    (fun _ member => workFromSpec_groups_parentCanonical Located.root canonical member)
  have joint : let initial := State.initialize (Work.fromExecution work)
      let queue := initial.replayGraphEvents events
      queue.HealthyContributorsCovered work (initial.objectFailureContributions events)
      ∧ queue.ParentRegistryClosed parents ∧ queue.ChildGroupsUnique := by
    induction valid with
    | nil =>
        exact ⟨generated.initial_healthyContributorsCovered,
          createWorkQueue_parentRegistryClosed canonical, createWorkQueue_childGroupsUnique _⟩
    | @append before event valid matching fresh ready ih =>
        have priorStarted := State.acceptsBatch_prefix started
        have prior := ih priorStarted
        let initial := State.initialize (Work.fromExecution work)
        let queue := initial.replayGraphEvents before
        let failed := initial.objectFailureContributions before
        have acceptedAt : ∀ past next, (past ++ [next]).IsPrefix before →
            (initial.replayGraphEvents past).acceptsGraphEvent next = true := by
          intro past next earlier
          obtain ⟨after, same⟩ := earlier
          apply State.acceptsBatch_atPrefix initial past next after
          simpa only [← same, List.append_assoc, List.singleton_append] using priorStarted
        have ledger := generated.replayGraphEvents_ownerAccounting_of_eachAccepted
          canonical valid acceptedAt
        have accepted := generated.replayGraphEvents_acceptedOwnerAccounting_of_eachAccepted
          valid acceptedAt
        have complete := initialLinks.replayGraphEvents (createWorkQueue_groupRefsUnique _)
          initialRegistered.1 initialRegistered.2 (createWorkQueue_parentRegistryClosed canonical)
          before (fun _ member => valid.eachMatches member) canonical
        have cancelled := generated.replayGraphEvents_cancelledRecordsSupported before valid
        have forest := State.RemovalForest.of_generated generated prior.2.2
          ledger.childLinks ledger.groups canonical
        have nextRegistry := prior.2.1.handleGraphEvent ledger.pending.liveGroups
          ledger.pending.taskGroups event matching canonical
        have nextChildren := prior.2.2.handleGraphEvent event
        dsimp only
        rw [State.replayGraphEvents_append, State.objectFailureContributions_append]
        refine ⟨?_, nextRegistry, nextChildren⟩
        change (queue.handleGraphEvent event).1.HealthyContributorsCovered work
          (queue.objectFailureContributions [event] ++ failed)
        simp only [State.objectFailureContributions, List.nil_append]
        cases event with
        | taskSuccess occurrence result =>
            apply prior.1.taskSuccess accepted.1 accepted.2 ledger.pending.matching generated
              ledger.groups (generated.replayGraphEvents_healthyRetiredAncestors before valid)
              cancelled complete ledger.pending.refs ledger.pending.liveGroups
              ledger.pending.taskGroups ledger.pending.started prior.2.1 prior.2.2
              ledger.childLinks canonical ?_ matching
            exact fun member => fresh.2.2.1 occurrence List.mem_cons_self
              (GraphEvent.taskSettlements_subsetIdentities before member)
        | taskFailure occurrence errors =>
            exact (prior.1.taskFailure ledger.pending.refs forest ledger.pending.taskGroups
              occurrence errors).mono_failures (List.subset_append_right _ _)
        | streamItems stream items =>
            exact prior.1.streamItems (createWorkQueue_replay_regionInventory valid)
              generated complete ledger.pending.refs ledger.pending.liveGroups
              ledger.pending.taskGroups prior.2.1 cancelled ledger.groups prior.2.2
              ledger.childLinks canonical matching fresh.1
              (fun item member => fresh.2.2.1 item.occurrence (List.mem_map_of_mem member))
        | streamSuccess stream => exact prior.1.streamSuccess stream
        | streamFailure stream errors => exact prior.1.streamFailure stream errors
  exact joint.1

-----------------------------------------------------------------------------------------
-- Normalized replay and the terminal live-group consequence
-----------------------------------------------------------------------------------------

/-- Every normalized source prefix retains the same healthy contributor coverage.
Witness: start discipline relates batched execution to raw replay, changing only the done
flag; group records, active roots, and the accepted-failure inventory are shared.
-/
theorem ExecutedWork.runNormalized_healthyContributorsCovered {work : Execution.Work}
    (generated : ExecutedWork work) (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    : let initial := State.initialize (Work.fromExecution work)
      (initial.runNormalized batches).1.HealthyContributorsCovered work
        (initial.objectFailureContributions batches.flatten) := by
  have accepts := (State.initialize (Work.fromExecution work)).batchesStarted_acceptsBatch batches
    (by rwa [← inputsStarted_eq_batchesStarted])
  have covered := generated.replayGraphEvents_healthyContributorsCovered
    batches.flatten valid accepts
  obtain ⟨terminated, same⟩ := createWorkQueue_runNormalized_stateCore started
  dsimp only
  rw [same]
  intro task member ref contributes healthy live
  obtain ⟨root, active, path⟩ := covered task member ref contributes healthy live
  exact ⟨
    root,
    active,
    path.of_groupNodes_eq
      (queue :=
        (State.initialize (Work.fromExecution work)).replayGraphEvents batches.flatten)
      rfl
  ⟩

/-- No healthy registered contributor can remain live when normalized replay has no roots.
Witness: replay coverage would supply an active root for any surviving contributor.
This closes the latent-live-group case, not yet the never-registered work or stream cases.
-/
theorem ExecutedWork.runNormalized_no_stranded_contributor {work : Execution.Work}
    (generated : ExecutedWork work) (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    : let initial := State.initialize (Work.fromExecution work)
      let queue := (initial.runNormalized batches).1
      queue.rootGroups = []
      → ∀ task ∈ queue.tasks,
        ∀ ref ∈ task.groups.map Execution.DeliveryNode.ref,
          ¬GroupInvalidated work (initial.objectFailureContributions batches.flatten) ref
          → queue.groupNode? ref = none := by
  intro initial queue empty task member ref contributes healthy
  cases found : queue.groupNode? ref with
  | none => rfl
  | some node =>
      obtain ⟨root, active, _⟩ := generated.runNormalized_healthyContributorsCovered
        batches valid started task member ref contributes healthy ⟨node, found⟩
      rw [empty] at active
      cases active

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
