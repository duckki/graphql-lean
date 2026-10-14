import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.LiveContributorStreamCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ReferenceReplay

/-! Generated replay derives root coverage for failed as well as healthy live contributors. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Derive every local coverage premise at the same actual source prefix
-----------------------------------------------------------------------------------------

/-- Every valid started raw prefix covers all live permanent contributors.
Witness: joint coverage/registration/topology induction. Independent replay supplies parent
safety, successful-retirement health, and accepted-failure ownership at that exact prefix.
No emitted-history admission or caller-supplied coverage invariant is assumed.
-/
theorem ExecutedWork.replayGraphEvents_liveContributorsCovered {work : Execution.Work}
    (generated : ExecutedWork work) (events : List GraphEvent)
    (valid : ValidGraphEvents work events)
    (started : (State.initialize (Work.fromExecution work)).acceptsBatch events = true)
    : ((State.initialize (Work.fromExecution work)).replayGraphEvents
        events).LiveContributorsCovered := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have initialRegistered := createWorkQueue_registration work
  have initialLinks := createWorkQueue_parentLinksComplete (Work.fromExecution work) parents
    (fun _ member => workFromSpec_groups_parentCanonical Located.root canonical member)
  have joint : let queue := (State.initialize (Work.fromExecution work)).replayGraphEvents events
      queue.LiveContributorsCovered ∧ queue.ParentRegistryClosed parents ∧ queue.ChildGroupsUnique := by
    induction valid with
    | nil =>
        exact ⟨generated.initial_liveContributorsCovered,
          createWorkQueue_parentRegistryClosed canonical, createWorkQueue_childGroupsUnique _⟩
    | @append before event valid matching fresh ready ih =>
        have priorStarted := State.acceptsBatch_prefix started
        have prior := ih priorStarted
        let initial := State.initialize (Work.fromExecution work)
        let queue := initial.replayGraphEvents before
        have acceptedAt : ∀ past next, (past ++ [next]).IsPrefix before →
            (initial.replayGraphEvents past).acceptsGraphEvent next = true := by
          intro past next earlier
          obtain ⟨after, same⟩ := earlier
          apply State.acceptsBatch_atPrefix initial past next after
          simpa only [← same, List.append_assoc, List.singleton_append] using priorStarted
        have ledger := generated.replayGraphEvents_ownerAccounting_of_eachAccepted canonical valid acceptedAt
        have accepted := generated.replayGraphEvents_acceptedOwnerAccounting_of_eachAccepted valid acceptedAt
        have complete := initialLinks.replayGraphEvents (createWorkQueue_groupRefsUnique _)
          initialRegistered.1 initialRegistered.2 (createWorkQueue_parentRegistryClosed canonical)
          before (fun _ member => valid.eachMatches member) canonical
        have safe := generated.replayGraphEvents_liveParentsUncancelled before
          (fun _ member => valid.eachMatches member)
        have retirement := generated.replayGraphEvents_structuralRetirement before
          (fun _ member => valid.eachMatches member)
        have health := generated.replayGraphEvents_retiredHealth before valid priorStarted
        have forest := State.RemovalForest.of_generated generated prior.2.2 ledger.childLinks ledger.groups canonical
        have nextRegistry := prior.2.1.handleGraphEvent ledger.pending.liveGroups
          ledger.pending.taskGroups event matching canonical
        have nextChildren := prior.2.2.handleGraphEvent event
        rw [State.replayGraphEvents_append]
        refine ⟨?_, nextRegistry, nextChildren⟩
        change (queue.handleGraphEvent event).1.LiveContributorsCovered
        cases event with
        | taskSuccess occurrence result =>
            exact prior.1.taskSuccess accepted.1 ledger.pending.matching generated ledger.groups
              retirement.2 health.1 safe ledger.canonical complete ledger.pending.refs
              ledger.pending.liveGroups ledger.pending.taskGroups ledger.pending.started prior.2.1
              prior.2.2 ledger.childLinks canonical
              (fun member => fresh.2.2.1 occurrence List.mem_cons_self
                (GraphEvent.taskSettlements_subsetIdentities before member)) matching
        | taskFailure occurrence errors =>
            exact prior.1.taskFailure ledger.pending.refs forest ledger.pending.taskGroups occurrence errors
        | streamItems stream items =>
            exact prior.1.streamItems (createWorkQueue_replay_regionInventory valid) generated
              complete ledger.pending.refs ledger.pending.liveGroups ledger.pending.taskGroups
              prior.2.1 safe ledger.canonical ledger.groups prior.2.2 ledger.childLinks canonical
              matching fresh.1
              (fun item member => fresh.2.2.1 item.occurrence (List.mem_map_of_mem member))
        | streamSuccess stream =>
            change (queue.streamSuccess stream).1.LiveContributorsCovered
            unfold State.streamSuccess
            split
            · intro task member key contributes live
              obtain ⟨root, active, path⟩ := prior.1 task member key contributes live
              exact ⟨root, active, path.of_groupNodes_eq (queue := queue) rfl⟩
            · exact prior.1
        | streamFailure stream errors =>
            change (queue.streamFailure stream errors).1.LiveContributorsCovered
            unfold State.streamFailure
            split
            · intro task member key contributes live
              obtain ⟨root, active, path⟩ := prior.1 task member key contributes live
              exact ⟨root, active, path.of_groupNodes_eq (queue := queue) rfl⟩
            · exact prior.1
  exact joint.1

-----------------------------------------------------------------------------------------
-- Batch normalization and terminal record clearing preserve the same coverage target
-----------------------------------------------------------------------------------------

/-- Normalized replay covers every surviving contributor without a health premise. -/
theorem ExecutedWork.runNormalized_liveContributorsCovered {work : Execution.Work}
    (generated : ExecutedWork work) (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    : ((State.initialize (Work.fromExecution work)).runNormalized
        batches).1.LiveContributorsCovered := by
  have accepts := (State.initialize (Work.fromExecution work)).batchesStarted_acceptsBatch batches
    (by rwa [← inputsStarted_eq_batchesStarted])
  have covered := generated.replayGraphEvents_liveContributorsCovered batches.flatten valid accepts
  obtain ⟨terminated, same⟩ := createWorkQueue_runNormalized_stateCore started
  rw [same]
  intro task member key contributes live
  obtain ⟨root, active, path⟩ := covered task member key contributes live
  exact ⟨
    root,
    active,
    path.of_groupNodes_eq
      (queue :=
        (State.initialize (Work.fromExecution work)).replayGraphEvents batches.flatten)
      rfl
  ⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement

/-- Whole-replay live contributor coverage target, independent of acquired-resource inventory. -/
def GeneratedLiveContributorCoverage : Prop :=
  ∀ work inputs,
    ReferenceWorkQueue.ExecutedWork work
    → ReferenceWorkQueue.ValidGraphEvents work inputs.flatten
    → ReferenceWorkQueue.inputsStarted work inputs = true
    → ((State.initialize work).runNormalized inputs).1.queue.LiveContributorsCovered

/-- Exact reference replay and terminal clearing discharge whole-replay contributor coverage. -/
theorem GeneratedLiveContributorCoverage_holds : GeneratedLiveContributorCoverage := by
  intro work inputs generated valid started
  rw [State.runNormalized_initialize work inputs generated valid started]
  simp only [State.fromReference]
  split
  · intro task member
    simp [State.clearRecords] at member
  · exact generated.runNormalized_liveContributorsCovered inputs valid started

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
