import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ContributorFailureCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ContributorStreamCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.AcceptedFailureEquivalence

/-! Actual generated replay keeps every healthy live registered contributor root-covered. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

private theorem State.HealthyContributorsCovered.withGroupFailures {queue work failed}
    (covered : State.HealthyContributorsCovered queue work failed)
    (notices : List GroupFailureEvent)
    : ({queue with groupFailureEvents := notices}).HealthyContributorsCovered work
        failed := by
  intro task registered ref contributes healthy survives
  obtain ⟨root, active, path⟩ := covered task registered ref contributes healthy survives
  exact ⟨root, active, State.LiveDescendant.of_groupNodes_eq (queue := queue) (next := {queue with groupFailureEvents := notices}) rfl path⟩

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
    (started
      : State.eventsStarted [] (State.initialize (Work.fromExecution work)) events = true)
    : let initial := State.initialize (Work.fromExecution work)
      (initial.replayGraphEvents events).HealthyContributorsCovered work
        (initial.objectFailureContributions events) := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have initialRegistered := createWorkQueue_registration work generated.declarations
  have initialLinks := createWorkQueue_parentLinksComplete (Work.fromExecution work) parents
    (fun _ member => workFromSpec_groups_parentCanonical_root canonical member)
  have joint : let initial := State.initialize (Work.fromExecution work)
      let queue := initial.replayGraphEvents events
      queue.HealthyContributorsCovered work (initial.objectFailureContributions events)
      ∧ queue.ParentRegistryClosed parents ∧ queue.ChildGroupsUnique := by
    induction valid with
    | nil =>
        exact ⟨generated.initial_healthyContributorsCovered,
          createWorkQueue_parentRegistryClosed canonical generated.declarations, createWorkQueue_childGroupsUnique _⟩
    | @append before event valid matching fresh ready ih =>
        have priorStarted := State.eventsStarted_prefix started
        have prior := ih priorStarted
        let initial := State.initialize (Work.fromExecution work)
        let queue := initial.replayGraphEvents before
        let failed := initial.objectFailureContributions before
        have acceptedAt : ∀ past next, (past ++ [next]).IsPrefix before →
            (initial.replayGraphEvents past).acceptsGraphEvent next = true := by
          intro past next earlier
          obtain ⟨after, same⟩ := earlier
          apply State.eventsStarted_atPrefix initial past next after
          simpa only [← same, List.append_assoc, List.singleton_append] using priorStarted
        have ledger := generated.replayGraphEvents_ownerAccounting_of_eachAccepted
          canonical valid acceptedAt
        have accepted := generated.replayGraphEvents_acceptedOwnerAccounting_of_eachAccepted
          valid acceptedAt
        have complete := initialLinks.replayGraphEvents (createWorkQueue_groupRefsUnique _)
          initialRegistered.1 initialRegistered.2 (State.initialize_registrationFrame generated.declarations)
          (createWorkQueue_parentRegistryClosed canonical generated.declarations)
          before (fun _ member => valid.eachMatches member) canonical
        have cancelled := generated.replayGraphEvents_cancelledRecordsSupported before valid
        have caches : queue.CachedFailuresSupported work failed := by
          have replayed := (createWorkQueue_cachedFailuresSupported
            (Work.fromExecution work) work []).replayGraphEvents_contributions
            (createWorkQueue_startedTasksRegistered _)
            (createWorkQueue_fromSpec_registeredTasksMatch work) before
            (fun _ member => valid.eachMatches member)
          simpa only [List.append_nil] using replayed
        have forest := State.RemovalForest.of_generated generated prior.2.2
          ledger.childLinks ledger.groups canonical
        have nextRegistry := prior.2.1.handleGraphEvent ledger.pending.liveGroups
          ledger.pending.taskGroups ledger.pending.registration event matching canonical
        have nextChildren := prior.2.2.handleGraphEvent event
        dsimp only
        rw [State.replayGraphEvents_append, State.objectFailureContributions_append]
        refine ⟨?_, nextRegistry, nextChildren⟩
        have handled : (queue.handleGraphEvent event).1.HealthyContributorsCovered work
            (queue.objectFailureContributions [event] ++ failed) := by
          simp only [State.objectFailureContributions, List.nil_append]
          cases event with
          | taskSuccess occurrence result =>
              apply prior.1.taskSuccess accepted.1 accepted.2 ledger.pending.matching generated
                ledger.groups (generated.replayGraphEvents_healthyRetiredAncestors before valid)
                cancelled complete ledger.pending.refs ledger.pending.liveGroups
                ledger.pending.taskGroups ledger.pending.registration ledger.pending.started prior.2.1 prior.2.2
                ledger.childLinks canonical ?_ matching
              exact fun member => fresh.2.2.1 occurrence List.mem_cons_self
                (GraphEvent.taskSettlements_subsetIdentities before member)
          | taskFailure occurrence errors =>
              exact (prior.1.taskFailure ledger.pending.refs forest ledger.pending.taskGroups
                occurrence errors).mono_failures (List.subset_append_right _ _)
          | streamItems stream items =>
              exact prior.1.streamItems (createWorkQueue_replay_regionInventory valid)
                generated ledger.pending.registration complete ledger.pending.refs ledger.pending.liveGroups
                ledger.pending.taskGroups prior.2.1 cancelled ledger.groups prior.2.2
                ledger.childLinks caches ledger.pending.started ledger.pending.matching
                ledger.pending.sound canonical matching fresh.1
                (fun item member => fresh.2.2.1 item.occurrence (List.mem_map_of_mem member))
          | groupFailure failure =>
              simp only [State.handleGraphEvent, State.groupFailure, State.objectFailureContribution]
              split
              · exact prior.1
              · split
                · exact prior.1.withGroupFailures _
                · exact prior.1
          | streamSuccess stream => exact prior.1.streamSuccess stream
          | streamFailure stream errors => exact prior.1.streamFailure stream errors
        change (queue.dispatchGraphEvent event).1.HealthyContributorsCovered work
          (queue.objectFailureContributions [event] ++ failed)
        simpa only [State.dispatchGraphEvent, State.enqueueGroupFailures]
          using handled.withGroupFailures
            ((queue.handleGraphEvent event).1.groupFailureEvents
              ++ (queue.handleGraphEvent event).2.2)
  exact joint.1

-----------------------------------------------------------------------------------------
-- Normalized replay and the terminal live-group consequence
-----------------------------------------------------------------------------------------

private structure CoverageReplayFrame (queue : State) (work : Execution.Work)
    (parents : Nat → NodeRefs) (before : List GraphEvent) (failed : List Occurrence)
    : Prop where
  owners : queue.OwnerAccountingInInventory work parents before failed
  live : queue.LiveGroupsRegistered
  roots : queue.RootAncestorsRetired work
  retired : queue.UncancelledRetiredAncestors work
  regions : queue.RegionInventory work (before.flatMap (fun event => event.identities.1))
  covered : queue.HealthyContributorsCovered work failed
  complete : queue.ParentLinksComplete parents
  closed : queue.ParentRegistryClosed parents
  children : queue.ChildGroupsUnique

private theorem CoverageReplayFrame.weakenFailures {queue work parents before old next}
    (prior : CoverageReplayFrame queue work parents before old)
    (included : old.Subset next)
    : CoverageReplayFrame queue work parents before next :=
  ⟨
    prior.owners.weakenFailures included,
    prior.live,
    prior.roots,
    prior.retired,
    prior.regions,
    prior.covered.mono_failures included,
    prior.complete,
    prior.closed,
    prior.children
  ⟩

private theorem CoverageReplayFrame.cacheTaskFailures {queue work parents before failed}
    (prior : CoverageReplayFrame queue work parents before failed)
    (available : List (Occurrence × Nat))
    (recorded
      : ∀ occurrence errors, (occurrence, errors) ∈ available → occurrence ∈ failed)
    : CoverageReplayFrame (queue.cacheTaskFailures available) work parents before
        failed := by
  have coverage := queue.cacheTaskFailures_registration prior.live prior.owners.pending.taskGroups
    available
  have covered : (queue.cacheTaskFailures available).HealthyContributorsCovered work failed := by
    intro task member ref contributes healthy live
    rw [State.cacheTaskFailures_tasks] at member
    have beforeLive : ∃ node, queue.groupNode? ref = some node := by
      simpa only [State.groupNode?, State.cacheTaskFailures_groupNodes] using live
    obtain ⟨root, active, path⟩ := prior.covered task member ref contributes healthy beforeLive
    exact ⟨
      root,
      by rwa [State.cacheTaskFailures_rootGroups],
      path.of_groupNodes_eq (queue.cacheTaskFailures_groupNodes available)
    ⟩
  have complete : (queue.cacheTaskFailures available).ParentLinksComplete parents := by
    simpa only [State.ParentLinksComplete, State.cacheTaskFailures_groupNodes]
      using prior.complete
  refine ⟨prior.owners.cacheTaskFailures available recorded, coverage.1, ?_,
    prior.retired.cacheTaskFailures available, prior.regions.cacheTaskFailures available,
    covered, complete,
    prior.closed.of_sameRegistry (queue.cacheTaskFailures_registeredGroups available),
    prior.children.cacheTaskFailures available⟩
  intro ref active
  rw [State.cacheTaskFailures_rootGroups] at active
  exact (prior.roots ref active).mono
    (fun _ retired => retired.cacheTaskFailures available)

private theorem CoverageReplayFrame.handleGraphEvent {queue work parents before failed}
    (prior : CoverageReplayFrame queue work parents before failed)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (generated : ExecutedWork work) (valid : ValidGraphEvents work before)
    (event : GraphEvent) (matching : event.MatchesWork work) (fresh : event.Fresh before)
    (tracked
      : ∀ occurrence result,
          event = .taskSuccess occurrence result
          → queue.StartedTaskDisposition occurrence
            ∧ ∃ task ∈ queue.tasks, task.occurrence = occurrence)
    (available : List (Occurrence × Nat))
    (recorded
      : ∀ occurrence errors, (occurrence, errors) ∈ available → occurrence ∈ failed)
    (notified
      : ∀ occurrence errors,
          event = .taskFailure occurrence errors → (occurrence, errors) ∈ available)
    : CoverageReplayFrame (queue.handleGraphEvent event available).1 work parents
        (before ++ [event]) failed := by
  let current := queue.cacheTaskFailures available
  have cached := prior.cacheTaskFailures available recorded
  have ready : current.RegistrationsAvailable work failed event available := by
    cases event with
    | taskSuccess occurrence result =>
        exact State.OwnerAccountingInInventory.taskSuccess_available_of_registered
          cached.owners generated (cached.retired.healthy cached.owners.cancelled)
          matching fresh
          (by
            simpa only [current, State.cacheTaskFailures_tasks] using (tracked _ _ rfl).2)
    | streamItems stream items =>
        apply cached.regions.streamItems_available generated matching fresh.1
          (available := available)
        intro item member
        exact fresh.2.2.1 item.occurrence (List.mem_map_of_mem member)
    | taskFailure | groupFailure | streamSuccess | streamFailure => trivial
  have owners := prior.owners.handleGraphEvent_ofDisposition canonical generated valid event
    matching fresh
    available recorded notified ready (fun occurrence result same => (tracked _ _ same).1)
  have structural := queue.handleGraphEvent_structuralRetirement generated prior.owners.groups
    prior.owners.links canonical prior.live prior.owners.pending.taskGroups prior.owners.pending.registration prior.roots
    prior.retired event matching available
  have forest := State.RemovalForest.of_generated generated cached.children
    cached.owners.childLinks cached.owners.groups canonical
  have covered : (queue.handleGraphEvent event available).1.HealthyContributorsCovered
      work failed := by
    change (match event with
      | .taskSuccess occurrence result => current.taskSuccess occurrence result available
      | .taskFailure occurrence errors =>
          ((current.taskFailure occurrence errors).1, (current.taskFailure occurrence errors).2, [])
      | .groupFailure failure =>
          ((current.groupFailure failure).1, (current.groupFailure failure).2, [])
      | .streamItems stream items => current.streamItems stream items available
      | .streamSuccess stream =>
          ((current.streamSuccess stream).1, (current.streamSuccess stream).2, [])
      | .streamFailure stream errors =>
          ((current.streamFailure stream errors).1, (current.streamFailure stream errors).2, [])
      ).1.HealthyContributorsCovered work failed
    cases event with
    | taskSuccess occurrence result =>
        apply cached.covered.taskSuccess cached.owners.owners cached.owners.healthy
          cached.owners.pending.matching generated cached.owners.groups
          (cached.retired.healthy cached.owners.cancelled) cached.owners.cancelled
          cached.complete cached.owners.pending.refs cached.live cached.owners.pending.taskGroups cached.owners.pending.registration
          cached.owners.pending.started cached.closed cached.children cached.owners.childLinks
          canonical ?_ matching available
        exact fun member => fresh.2.2.1 occurrence List.mem_cons_self
          (GraphEvent.taskSettlements_subsetIdentities before member)
    | taskFailure occurrence errors =>
        exact cached.covered.taskFailure cached.owners.pending.refs forest
          cached.owners.pending.taskGroups occurrence errors
    | groupFailure failure =>
        change (current.groupFailure failure).1.HealthyContributorsCovered work failed
        unfold State.groupFailure
        split
        · exact cached.covered
        · split
          · exact cached.covered.withGroupFailures _
          · exact cached.covered
    | streamItems stream items =>
        exact cached.covered.streamItems cached.regions generated cached.owners.pending.registration cached.complete
          cached.owners.pending.refs cached.live cached.owners.pending.taskGroups cached.closed
          cached.owners.cancelled cached.owners.groups cached.children cached.owners.childLinks
          cached.owners.supported cached.owners.pending.started cached.owners.pending.matching
          cached.owners.pending.sound canonical matching fresh.1
          (fun item member => fresh.2.2.1 item.occurrence (List.mem_map_of_mem member))
          available recorded
    | streamSuccess stream => exact cached.covered.streamSuccess stream
    | streamFailure stream errors => exact cached.covered.streamFailure stream errors
  refine ⟨
    owners,
    structural.1,
    structural.2.1,
    structural.2.2,
    ?_,
    covered,
    prior.complete.handleGraphEvent prior.owners.pending.refs prior.live
      prior.owners.pending.taskGroups prior.owners.pending.registration prior.closed event
      matching canonical available,
    prior.closed.handleGraphEvent prior.live prior.owners.pending.taskGroups
      prior.owners.pending.registration event
      matching canonical available,
    prior.children.handleGraphEvent event available
  ⟩
  simpa only [List.flatMap_append, List.flatMap_singleton]
    using prior.regions.handleGraphEvent event matching available

private theorem CoverageReplayFrame.withGroupFailures {queue work parents before failed}
    (frame : CoverageReplayFrame queue work parents before failed)
    (notices : List GroupFailureEvent)
    : CoverageReplayFrame {queue with groupFailureEvents := notices} work parents before
        failed :=
  ⟨
    frame.owners.withGroupFailures notices,
    frame.live,
    frame.roots,
    frame.retired,
    ⟨
      frame.regions.regions,
      frame.regions.matching,
      frame.regions.registrations,
      frame.regions.started
    ⟩,
    frame.covered.withGroupFailures notices,
    frame.complete,
    frame.closed,
    frame.children
  ⟩

private theorem CoverageReplayFrame.dispatchGraphEvent
    {queue work parents before failed}
    (prior : CoverageReplayFrame queue work parents before failed)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (generated : ExecutedWork work) (valid : ValidGraphEvents work before)
    (event : GraphEvent) (matching : event.MatchesWork work) (fresh : event.Fresh before)
    (tracked
      : ∀ occurrence result,
          event = .taskSuccess occurrence result
          → queue.StartedTaskDisposition occurrence
            ∧ ∃ task ∈ queue.tasks, task.occurrence = occurrence)
    (available : List (Occurrence × Nat))
    (recorded
      : ∀ occurrence errors, (occurrence, errors) ∈ available → occurrence ∈ failed)
    (notified
      : ∀ occurrence errors,
          event = .taskFailure occurrence errors → (occurrence, errors) ∈ available)
    : CoverageReplayFrame (queue.dispatchGraphEvent event available).1 work parents
        (before ++ [event]) failed := by
  have next := prior.handleGraphEvent canonical generated valid event matching fresh tracked
    available recorded notified
  exact next.withGroupFailures _

private theorem CoverageReplayFrame.replayGraphEvents
    {queue work parents before failed available}
    (prior : CoverageReplayFrame queue work parents before failed)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (generated : ExecutedWork work) (events : List GraphEvent)
    (valid : ValidGraphEvents work (before ++ events))
    (accepted : State.acceptsBatch.go (fun _ => false) available queue events = true)
    (recorded
      : ∀ occurrence errors, (occurrence, errors) ∈ available → occurrence ∈ failed)
    (notified
      : ∀ occurrence errors,
          .taskFailure occurrence errors ∈ events → (occurrence, errors) ∈ available)
    : CoverageReplayFrame (queue.replayGraphEvents events available) work parents
        (before ++ events) failed := by
  apply prefix_invariant events (fun fifo =>
    CoverageReplayFrame (queue.replayGraphEvents fifo available) work parents
      (before ++ fifo) failed)
  · simpa only [State.replayGraphEvents, List.foldl_nil, List.append_nil] using prior
  · intro fifo event rest split past
    have boundary : (before ++ fifo ++ [event]).IsPrefix (before ++ events) :=
      ⟨rest, by simp [split, List.append_assoc]⟩
    obtain ⟨validBefore, matching, fresh⟩ := validGraphEvents_last (valid.prefix boundary)
    have current := past fifo (List.prefix_refl _)
    have tracked : ∀ occurrence result, event = .taskSuccess occurrence result
        → (queue.replayGraphEvents fifo available).StartedTaskDisposition occurrence
          ∧ ∃ task ∈ (queue.replayGraphEvents fifo available).tasks,
              task.occurrence = occurrence := by
      intro occurrence result same
      subst event
      obtain ⟨seen, seenPrefix, eligible⟩ := queue.acceptsBatch_go_eachAccepted events fifo
        (.taskSuccess occurrence result) available accepted ⟨rest, by simp [split]⟩
      have frame := past seen seenPrefix
      cases found : (queue.replayGraphEvents seen available).taskNode? occurrence with
      | none => simp [State.acceptsGraphEvent, found] at eligible
      | some node =>
          obtain ⟨remaining, history⟩ := seenPrefix
          have disposition := frame.owners.pending.startedTaskDisposition_atPrefix found
            frame.owners.producers frame.owners.producerOrder remaining
            (by simpa [history, List.append_assoc] using validBefore) available
          rw [← history, State.replayGraphEvents_append queue seen remaining available]
          exact ⟨
            disposition,
            node.task,
            (queue.replayGraphEvents seen available).replayGraphEvents_tasks_subset
              remaining available
              (frame.owners.pending.started node (List.mem_of_find?_eq_some found)),
            (State.taskNode?_some found).2
          ⟩
    have next := current.dispatchGraphEvent canonical generated validBefore event matching fresh
      tracked available recorded (by
        intro occurrence errors same
        exact notified _ _ (same ▸ by simp [split]))
    simpa only [State.replayGraphEvents_append, State.replayGraphEvents,
      List.foldl_append, List.foldl_cons, List.foldl_nil, List.append_assoc]
      using next

private theorem CoverageReplayFrame.withTerminated {queue work parents before failed}
    (prior : CoverageReplayFrame queue work parents before failed) (terminated : Bool)
    : CoverageReplayFrame {queue with terminated := terminated} work parents before
        failed :=
  ⟨
    prior.owners.withTerminated terminated,
    prior.live,
    prior.roots,
    prior.retired,
    prior.regions.withTerminated terminated,
    by
      intro task member ref contributes healthy live
      obtain ⟨root, active, path⟩ := prior.covered task member ref contributes healthy live
      exact ⟨root, active, path.of_groupNodes_eq (queue := queue) rfl⟩,
    prior.complete,
    prior.closed,
    prior.children
  ⟩

private theorem CoverageReplayFrame.handleGraphEvents {queue work parents before}
    (prior
      : CoverageReplayFrame queue work parents before
          (GraphEvent.failureSettlements before))
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (generated : ExecutedWork work) (events : List GraphEvent)
    (valid : ValidGraphEvents work (before ++ events))
    (running : queue.terminated = false) (accepted : queue.acceptsBatch events = true)
    : CoverageReplayFrame (queue.handleGraphEvents events).1 work parents
        (before ++ events) (GraphEvent.failureSettlements (before ++ events)) := by
  have included : (GraphEvent.failureSettlements before).Subset
      (GraphEvent.failureSettlements (before ++ events)) := by
    rw [GraphEvent.failureSettlements_append_list]
    exact List.subset_append_right _ _
  have recorded : ∀ occurrence errors,
      (occurrence, errors) ∈ GraphEvent.availableFailures events →
        occurrence ∈ GraphEvent.failureSettlements (before ++ events) := by
    intro occurrence errors member
    obtain ⟨event, inEvents, same⟩ := List.mem_filterMap.mp member
    cases event <;> simp only [Option.some.injEq, reduceCtorEq, Prod.mk.injEq] at same
    obtain ⟨rfl, rfl⟩ := same
    apply List.mem_reverse.mpr
    exact List.mem_flatMap.mpr ⟨.taskFailure _ _, List.mem_append_right before inEvents,
      by simp [GraphEvent.groupFailures]⟩
  have result := (prior.weakenFailures included).replayGraphEvents canonical generated events valid
    accepted recorded (by
      intro occurrence errors member
      exact List.mem_filterMap.mpr ⟨.taskFailure occurrence errors, member, rfl⟩)
  obtain ⟨terminal, same⟩ := queue.handleGraphEvents_stateCore events running
  rw [same]
  exact result.withTerminated terminal

private theorem CoverageReplayFrame.runNormalized {queue work parents before}
    (prior
      : CoverageReplayFrame queue work parents before
          (GraphEvent.failureSettlements before))
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (generated : ExecutedWork work) (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work (before ++ batches.flatten))
    (started : queue.batchesStarted batches = true)
    : CoverageReplayFrame (queue.runNormalized batches).1 work parents
        (before ++ batches.flatten)
        (GraphEvent.failureSettlements (before ++ batches.flatten)) := by
  rw [State.runNormalized_replayBatches]
  induction batches generalizing queue before with
  | nil => simpa [State.replayBatches] using prior
  | cons batch rest ih =>
      obtain ⟨running, accepted, restStarted⟩ := queue.batchesStarted_cons batch rest started
      have earlier : (before ++ batch).IsPrefix (before ++ (batch :: rest).flatten) :=
        ⟨rest.flatten, by simp [List.append_assoc]⟩
      have next := prior.handleGraphEvents canonical generated batch (valid.prefix earlier)
        running accepted
      have result := ih next (by simpa [List.append_assoc] using valid) restStarted
      simpa only [State.replayBatches, List.foldl_cons, List.flatten_cons,
        List.append_assoc]
        using result

/-- Actual host batches cover all healthy live contributors at their batch boundaries.
The induction shares one availability snapshot throughout each FIFO batch, then advances
its failure inventory at the batch boundary. No flattened-state bridge is used.
-/
theorem ExecutedWork.runNormalized_healthyContributorsCovered {work : Execution.Work}
    (generated : ExecutedWork work) (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    : let initial := State.initialize (Work.fromExecution work)
      (initial.runNormalized batches).1.HealthyContributorsCovered work
        (initial.admittedObjectFailureContributionsForBatches batches) := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have initial : CoverageReplayFrame (State.initialize (Work.fromExecution work)) work
      parents [] [] :=
    ⟨createWorkQueue_ownerAccounting work parents canonical generated,
      (createWorkQueue_registration work generated.declarations).1, generated.initialRootAncestorsRetired,
      generated.initialUncancelledRetirement, createWorkQueue_regionInventory work,
      generated.initial_healthyContributorsCovered,
      createWorkQueue_parentLinksComplete (Work.fromExecution work) parents
        (fun _ member => workFromSpec_groups_parentCanonical_root canonical member),
      createWorkQueue_parentRegistryClosed canonical generated.declarations, createWorkQueue_childGroupsUnique _⟩
  have result := initial.runNormalized canonical generated batches valid
    (by rwa [inputsStarted_eq_batchesStarted] at started)
  dsimp only
  rw [State.admittedObjectFailureContributionsForBatches_eq_of_started _ batches
    (by rwa [inputsStarted_eq_batchesStarted] at started)]
  exact result.covered

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
          ¬GroupInvalidated work
            (initial.admittedObjectFailureContributionsForBatches batches) ref
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
