import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ProducerSupport
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.OwnerRelease
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskRejections

/-! Healthy registered-owner accounting across executable source-event handlers. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (StreamItemValue)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Healthy contributor availability at each integration performed by one graph event.
The conformance proof must derive this from generated work and preceding queue states. -/
def State.RegistrationsAvailable (queue : State) (work : Execution.Work)
    (failed : List Occurrence) (event : GraphEvent)
    (available : List (Occurrence × Nat) := [])
    : Prop :=
  match event with
  | .taskSuccess _ result => queue.ChildGroupsAvailable work failed result.work
  | .streamItems _ items => queue.StreamRegistrationsAvailable work failed items available
  | _ => True

/-- At initialization, all registered tasks (including latent ones) have
healthy contributor memberships. This stronger base fact supplies both
started-task and future-release invariants. -/
theorem createWorkQueue_healthyRegisteredTaskAccounting (work : Execution.Work)
    (generated : ExecutedWork work)
    : (State.initialize (Work.fromExecution work)).HealthyRegisteredTaskAccounting
        work [] [] := by
  let initialWork := Work.fromExecution work
  let integrated := (({} : State).maybeIntegrateWork initialWork).1
  let newWork := (({} : State).maybeIntegrateWork initialWork).2
  let pruned := (integrated.pruneEmptyGroups newWork.newGroups).1
  let groups := (integrated.pruneEmptyGroups newWork.newGroups).2
  let roots := { newWork with newGroups := groups }
  let started := (pruned.startNewWork roots).1
  have integratedPresent : ∀ task ∈ integrated.tasks,
      ∀ ref ∈ task.groups.map Execution.DeliveryNode.ref,
        ∃ node ∈ integrated.groupNodes, node.group.node.ref = ref :=
    initialIntegration_taskGroupsPresent work generated
  have integratedLinks : integrated.InitialTaskLinks :=
    State.initialWorkTaskLinks initialWork
  have prunedLinks : pruned.InitialTaskLinks :=
    integratedLinks.pruneEmptyGroups newWork.newGroups
  have emptyUnique : ({} : State).GroupRefsUnique := by
    simp [State.GroupRefsUnique]
  have integratedUnique : integrated.GroupRefsUnique :=
    emptyUnique.maybeIntegrateWork initialWork none
  have emptyReject : ({} : State).TaskRejectionsSatisfy (fun _ _ => False) := by
    intro node member; cases member
  have prunedReject := (emptyReject.maybeIntegrateWork initialWork).pruneEmptyGroups
    newWork.newGroups
  have clean : ∀ node ∈ pruned.taskNodes, node.rejection = none := by
    intro node member
    cases rejected : node.rejection with
    | none => rfl
    | some errors => exact (prunedReject node member errors rejected).elim
  intro task taskMember _ ref contributor _
  change task ∈ started.tasks at taskMember
  have taskDef : task ∈ integrated.tasks := by
    rw [(pruned.startNewWork_groupCore roots).2.1] at taskMember
    rw [State.pruneEmptyGroups_tasks] at taskMember
    exact taskMember
  obtain ⟨node, nodeMember, nodeRef⟩ :=
    integratedPresent task taskDef ref contributor
  have nodeContributor : node.group.node.ref ∈
      task.groups.map Execution.DeliveryNode.ref := by
    rw [nodeRef]
    exact contributor
  have linked : task.occurrence ∈ node.tasks :=
    integratedLinks task taskDef node nodeMember nodeContributor
  obtain ⟨retained, retainedMember, retainedRef, _⟩ :=
    integrated.pruneEmptyGroups_preservesNonempty newWork.newGroups
      integratedUnique ⟨node, nodeMember, nodeRef, List.ne_nil_of_mem linked⟩
  have retainedContributor : retained.group.node.ref ∈
      task.groups.map Execution.DeliveryNode.ref := by
    rw [retainedRef]
    exact contributor
  have retainedLink : task.occurrence ∈ retained.tasks :=
    prunedLinks task (by rw [State.pruneEmptyGroups_tasks]; exact taskDef)
      retained retainedMember retainedContributor
  have startedMember : retained ∈ started.groupNodes := by
    rw [(pruned.startNewWork_groupCore_of_no_cached_failures roots clean).1]
    exact retainedMember
  exact ⟨retained, startedMember, retainedRef, retainedLink⟩

private structure StreamOwnerContext (queue : State) (work : Execution.Work)
    (parents : Nat → NodeRefs) (settled failed : List Occurrence)
    : Prop where
  owners : queue.HealthyRegisteredTaskAccounting work settled failed
  counts : queue.PendingBound (fun _ => True) settled
  unique : queue.GroupRefsUnique
  cached : queue.CachedFailuresSupported work failed
  edges : queue.ChildLinksCanonical parents
  groups : queue.GroupNodesMatchWork work
  cancelled : queue.CancelledRecordsSupported work failed
  tasks : queue.RegisteredTasksMatch work
  registered : queue.StartedTasksRegistered
  sound : queue.GroupMembershipSound
  registration : queue.RegistrationFrame work

/-- Stream item integration retains healthy registered owners through the final drain.
The item fold uses the supplied cache snapshot at every activation; all removal is
justified by source-supported failures and canonical child links.
-/
theorem State.HealthyRegisteredTaskAccounting.streamItems_ofPendingAccounting
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    {parents : Nat → NodeRefs}
    (accounted : queue.HealthyRegisteredTaskAccounting work settled failed)
    (counts : queue.PendingBound (fun _ => True) settled) (unique : queue.GroupRefsUnique)
    (supported : queue.CachedFailuresSupported work failed)
    (cancelled : queue.CancelledRecordsSupported work failed)
    (tasksMatch : queue.RegisteredTasksMatch work)
    (generated : ExecutedWork work)
    (links : queue.ChildLinksCanonical parents)
    (groupMatching : queue.GroupNodesMatchWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (stream : Execution.DeliveryNode) (items : List StreamItem)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (registered : queue.StartedTasksRegistered) (sound : queue.GroupMembershipSound)
    (registration : queue.RegistrationFrame work)
    (failuresAvailable : List (Occurrence × Nat) := [])
    (available : queue.StreamRegistrationsAvailable work failed items failuresAvailable)
    (recorded
      : ∀ occurrence errors,
          (occurrence, errors) ∈ failuresAvailable → occurrence ∈ failed := by
        intro occurrence errors member; cases member)
    : (queue.streamItems stream items failuresAvailable).1.HealthyRegisteredTaskAccounting
        work settled failed := by
  let step (acc : State × List Execution.DeliveryNode × List Execution.DeliveryNode
      × List StreamItemValue × List GroupFailureEvent) (item : StreamItem) :=
    let (current, groups, streams, values, failures) := acc
    let (integrated, newWork) := current.maybeIntegrateWork item.work
    let (pruned, nonempty) := integrated.pruneEmptyGroups newWork.newGroups
    let (started, queued) :=
      pruned.startNewWork { newWork with newGroups := nonempty } failuresAvailable
    (started, groups ++ nonempty, streams ++ newWork.newStreams,
      values ++ [item.value], failures ++ queued)
  let invariant (current : State) := StreamOwnerContext current work parents settled failed
  have preserve (acc) (item : StreamItem) (member : item ∈ items)
      (prior : invariant acc.1) (ready : acc.1.ChildGroupsAvailable work failed item.work)
      : invariant (step acc item).1 := by
    obtain ⟨current, groups, streams, values, failures⟩ := acc
    let integrated := current.maybeIntegrateWork item.work
    let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
    let released := { integrated.2 with newGroups := pruned.2 }
    have descriptors : ∀ group ∈ item.work.groups, ∃ dependencies,
        GroupRecordAt work group.node dependencies
        ∧ group.parent = dependencies.head? := by
      intro group groupMember
      obtain ⟨dependencies, known⟩ :=
        matching.streamItem_childGroups_recordAt member groupMember
      exact ⟨dependencies, known,
        (matching.streamItem_childGroups_parentCanonical canonical member groupMember).trans
          (congrArg List.head? (canonical _ _ known)).symm⟩
    have childTasks : ∀ task ∈ item.work.tasks, TaskMatches work task := by
      intro task taskMember
      obtain ⟨address, payload, occurrenceEq, known⟩ :=
        matching.streamItem_childTask_producer member taskMember
      exact ⟨⟨address, payload, some item.occurrence, occurrenceEq, known⟩,
        matching.streamItem_childTask_groupsExact member taskMember⟩
    have owners := prior.owners.maybeIntegrateWork prior.unique item.work none
      (by
        intro task taskMember ref contributor
        exact Or.inr (matching.streamItem_childTasksCovered generated.declarations member
          task taskMember ref contributor)) ready generated prior.registration.live descriptors
      (by
        intro group groupMember parent parentEq
        have certificate := generated.declarations.sourceStreamItem matching member
          current.registeredGroups
        rcases certificate.parents group groupMember parent parentEq with known | candidate
        · exact List.mem_append_left _ known
        · obtain ⟨candidate, included, same⟩ := candidate
          exact List.mem_append_right _ (List.mem_map.mpr ⟨candidate, included, same⟩))
    have refs := prior.unique.maybeIntegrateWork item.work none
    have caches := (prior.cached.maybeIntegrateWork item.work).pruneEmptyGroups
      integrated.2.newGroups
    have edges := (prior.edges.maybeIntegrateWork item.work
      (fun _ groupMember =>
        matching.streamItem_childGroups_parentCanonical canonical member
          groupMember)).pruneEmptyGroups
      integrated.2.newGroups
    have groupsMatch := (prior.groups.maybeIntegrateWork item.work
      (fun _ groupMember =>
        matching.streamItem_childGroups_recordAt member groupMember)).pruneEmptyGroups
      integrated.2.newGroups
    have tasks := (prior.tasks.maybeIntegrateWork item.work childTasks).pruneEmptyGroups
      integrated.2.newGroups
    have started := (prior.registered.maybeIntegrateWork item.work).pruneEmptyGroups
      integrated.2.newGroups
    have memberships := (prior.sound.maybeIntegrateWork item.work).pruneEmptyGroups
      integrated.2.newGroups
    have cancellations : pruned.1.CancelledRecordsSupported work failed := by
      simpa only [pruned, integrated, State.CancelledRecordsSupported,
        State.pruneEmptyGroups_cancelledGroups]
        using prior.cancelled.maybeIntegrateWork item.work none descriptors
    exact ⟨
      (owners.pruneNonemptyGroups refs integrated.2.newGroups).startNewWork caches started
        tasks memberships generated edges groupsMatch canonical released failuresAvailable
        recorded,
      ((prior.counts.maybeIntegrateWork item.work).pruneEmptyGroups
        integrated.2.newGroups).startNewWork
        released failuresAvailable,
      (refs.pruneEmptyGroups integrated.2.newGroups).startNewWork released
        failuresAvailable,
      caches.startNewWork_available started tasks released failuresAvailable recorded,
      edges.startNewWork released failuresAvailable,
      groupsMatch.startNewWork released failuresAvailable,
      cancellations.startNewWork caches started tasks memberships groupsMatch edges
        canonical released failuresAvailable recorded,
      tasks.startNewWork released failuresAvailable,
      started.startNewWork released failuresAvailable,
      memberships.startNewWork released failuresAvailable,
      (prior.registration.integrateStreamItem matching member failuresAvailable).1
    ⟩
  have loop (more : List StreamItem) (included : more.Subset items) (acc)
      (prior : invariant acc.1)
      (ready : acc.1.StreamRegistrationsAvailable work failed more failuresAvailable)
      : invariant (more.foldl step acc).1 := by
    induction more generalizing acc with
    | nil => exact prior
    | cons item rest ih =>
        exact ih (fun _ member => included (List.mem_cons_of_mem _ member)) _
          (preserve acc item (included List.mem_cons_self) prior ready.1) ready.2
  unfold State.streamItems
  split
  · exact accounted
  · have final := loop items (fun _ member => member) (queue, [], [], [], [])
      ⟨accounted, counts, unique, supported, links, groupMatching, cancelled, tasksMatch,
        registered, sound, registration⟩ available
    exact final.owners.drainReadyGroups final.counts final.unique final.cached final.tasks
      generated final.edges final.groups canonical final.registered final.sound failuresAvailable
      recorded

/-- Every valid started source event preserves healthy registered owners, provided new
task contributors are available at their actual integration states.
Witness: bounded source settlement counts and the full task/stream release proofs; failures
use canonical subtree cleanup. This conditional step needs no healthy-root premise.
-/
theorem State.HealthyRegisteredTaskAccounting.handleGraphEvent_matching
    {queue : State} {work : Execution.Work} {before : List GraphEvent}
    {failed : List Occurrence} {parents : Nat → NodeRefs}
    (accounted
      : queue.HealthyRegisteredTaskAccounting work (GraphEvent.taskSettlements before)
          failed)
    (pending : queue.PendingAccounting work (GraphEvent.taskSettlements before))
    (supported : queue.CachedFailuresSupported work failed)
    (cancelled : queue.CancelledRecordsSupported work failed)
    (links : queue.ChildLinksCanonical parents)
    (groupMatching : queue.GroupNodesMatchWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (generated : ExecutedWork work) (_valid : ValidGraphEvents work before)
    (event : GraphEvent) (matching : event.MatchesWork work) (fresh : event.Fresh before)
    (failuresAvailable : List (Occurrence × Nat) := [])
    (available
      : (queue.cacheTaskFailures failuresAvailable).RegistrationsAvailable work failed
          event failuresAvailable)
    (recorded
      : ∀ occurrence errors,
          (occurrence, errors) ∈ failuresAvailable → occurrence ∈ failed := by
        intro occurrence errors member; cases member)
    : (queue.handleGraphEvent event failuresAvailable).1.HealthyRegisteredTaskAccounting
        work (GraphEvent.taskSettlements (before ++ [event]))
        (event.groupFailures ++ failed) := by
  rw [GraphEvent.taskSettlements_append]
  let current := queue.cacheTaskFailures failuresAvailable
  have cached := accounted.cacheTaskFailures failuresAvailable
  have counted := pending.cacheTaskFailures failuresAvailable
  have cacheSupported := supported.cacheTaskFailures pending.started pending.matching
    failuresAvailable recorded
  have cancellations : current.CancelledRecordsSupported work failed := by
    simpa only [current, State.CancelledRecordsSupported,
      State.cacheTaskFailures_cancelledGroups]
      using cancelled
  have edges := links.cacheTaskFailures failuresAvailable
  have groups := groupMatching.cacheTaskFailures failuresAvailable
  cases event with
  | taskSuccess occurrence result =>
      cases found : current.taskNode? occurrence with
      | none =>
          change (current.taskSuccess occurrence result
            failuresAvailable).1.HealthyRegisteredTaskAccounting work
              (occurrence :: GraphEvent.taskSettlements before) failed
          simpa only [State.taskSuccess, found]
            using cached.weakenSettled
              (after := occurrence :: GraphEvent.taskSettlements before)
              (by intro task member; exact List.mem_cons_of_mem _ member)
      | some taskNode =>
          apply cached.taskSuccess_ofPendingAccounting counted cacheSupported
            cancellations edges groups canonical generated occurrence result matching
            taskNode found (failuresAvailable := failuresAvailable) (recorded := recorded)
          · exact fun member => fresh.2.2.1 occurrence (by simp [GraphEvent.identities])
              (GraphEvent.taskSettlements_subsetIdentities before member)
          · exact available
  | taskFailure occurrence errors =>
      have retained := cached.taskFailure_any generated edges groups canonical
        counted.started counted.matching occurrence errors
      exact retained.weakenSettled
        (after := occurrence :: GraphEvent.taskSettlements before)
        (by intro task member; exact List.mem_cons_of_mem _ member)
  | streamItems stream items =>
      exact cached.streamItems_ofPendingAccounting counted.pending counted.refs cacheSupported
        cancellations counted.matching generated edges groups canonical stream items matching
        counted.started counted.sound counted.registration failuresAvailable available recorded
  | streamSuccess stream =>
      change (current.streamSuccess stream).1.HealthyRegisteredTaskAccounting work
        (GraphEvent.taskSettlements before) failed
      dsimp only [State.streamSuccess, GraphEvent.recordTaskOutcome,
        GraphEvent.groupFailures, List.nil_append]
      split <;> exact cached
  | streamFailure stream errors =>
      change (current.streamFailure stream errors).1.HealthyRegisteredTaskAccounting work
        (GraphEvent.taskSettlements before) failed
      dsimp only [State.streamFailure, GraphEvent.recordTaskOutcome,
        GraphEvent.groupFailures, List.nil_append]
      split <;> exact cached
  | groupFailure notice =>
      change (current.groupFailure notice).1.HealthyRegisteredTaskAccounting work
        (GraphEvent.taskSettlements before) failed
      unfold State.groupFailure
      split
      · exact cached
      · split <;> exact cached

/-- The live-event specialization of matching registered-owner accounting. -/
theorem State.HealthyRegisteredTaskAccounting.handleGraphEvent_ofPendingAccounting
    {queue : State} {work : Execution.Work} {before : List GraphEvent}
    {failed : List Occurrence} {parents : Nat → NodeRefs}
    (accounted
      : queue.HealthyRegisteredTaskAccounting work (GraphEvent.taskSettlements before)
          failed)
    (pending : queue.PendingAccounting work (GraphEvent.taskSettlements before))
    (supported : queue.CachedFailuresSupported work failed)
    (cancelled : queue.CancelledRecordsSupported work failed)
    (links : queue.ChildLinksCanonical parents)
    (groupMatching : queue.GroupNodesMatchWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (generated : ExecutedWork work) (_valid : ValidGraphEvents work before)
    (event : GraphEvent) (matching : event.MatchesWork work) (fresh : event.Fresh before)
    (_accepted : queue.acceptsGraphEvent event = true)
    (failuresAvailable : List (Occurrence × Nat) := [])
    (available
      : (queue.cacheTaskFailures failuresAvailable).RegistrationsAvailable work failed
          event failuresAvailable)
    (recorded
      : ∀ occurrence errors,
          (occurrence, errors) ∈ failuresAvailable → occurrence ∈ failed := by
        intro occurrence errors member; cases member)
    : (queue.handleGraphEvent event failuresAvailable).1.HealthyRegisteredTaskAccounting
        work (GraphEvent.taskSettlements (before ++ [event]))
        (event.groupFailures ++ failed) :=
  accounted.handleGraphEvent_matching pending supported cancelled links groupMatching
    canonical generated _valid event matching fresh failuresAvailable available recorded

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
