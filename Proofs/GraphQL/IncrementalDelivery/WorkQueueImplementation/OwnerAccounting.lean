import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.OwnerRelease

/-! Healthy registered-owner accounting across executable source-event handlers. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (StreamItemValue)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Every item's healthy contributor keys are available at its actual integration state.
This sequential proof obligation does not constrain the public host-event semantics. -/
def State.StreamRegistrationsAvailable (queue : State) (work : Execution.Work)
    (failed : List Occurrence)
    : List StreamItem → Prop
  | [] => True
  | item :: rest =>
      queue.ChildGroupsAvailable work failed item.work
      ∧ (queue.integrateStreamItem item).StreamRegistrationsAvailable work failed rest

/-- Healthy contributor availability at each integration performed by one graph event.
The conformance proof must derive this from generated work and preceding queue states. -/
def State.RegistrationsAvailable (queue : State) (work : Execution.Work)
    (failed : List Occurrence)
    : GraphEvent → Prop
  | .taskSuccess _ result => queue.ChildGroupsAvailable work failed result.work
  | .streamItems _ items => queue.StreamRegistrationsAvailable work failed items
  | _ => True

/-- At initialization, all registered tasks (including latent ones) have
healthy contributor memberships. This stronger base fact supplies both
started-task and future-release invariants. -/
theorem createWorkQueue_healthyRegisteredTaskAccounting (work : Execution.Work)
    : (State.initialize (Work.fromExecution work)).HealthyRegisteredTaskAccounting
        work [] [] := by
  let initialWork := Work.fromExecution work
  let integrated := (({} : State).maybeIntegrateWork initialWork).1
  let newWork := (({} : State).maybeIntegrateWork initialWork).2
  let pruned := (integrated.pruneEmptyGroups newWork.newGroups).1
  let groups := (integrated.pruneEmptyGroups newWork.newGroups).2
  let roots := { newWork with newGroups := groups }
  let started := pruned.startNewWork roots
  have covered : ∀ task ∈ initialWork.tasks,
      ∀ key ∈ task.groups.map Execution.DeliveryNode.key,
        ∃ group ∈ initialWork.groups, group.node.key = key :=
    workFromSpec_immediateGroupsCoverTasks work []
  have integratedPresent : ∀ task ∈ integrated.tasks,
      ∀ key ∈ task.groups.map Execution.DeliveryNode.key,
        ∃ node ∈ integrated.groupNodes, node.group.node.key = key :=
    initialIntegration_taskGroupsPresent initialWork covered
  have integratedLinks : integrated.InitialTaskLinks :=
    State.initialWorkTaskLinks initialWork
  have prunedLinks : pruned.InitialTaskLinks :=
    integratedLinks.pruneEmptyGroups newWork.newGroups
  have emptyUnique : ({} : State).GroupKeysUnique := by
    simp [State.GroupKeysUnique]
  have integratedUnique : integrated.GroupKeysUnique :=
    emptyUnique.maybeIntegrateWork initialWork none
  intro task taskMember _ key contributor _
  change task ∈ started.tasks at taskMember
  have taskDef : task ∈ integrated.tasks := by
    rw [(pruned.startNewWork_groupCore roots).2.1] at taskMember
    rw [State.pruneEmptyGroups_tasks] at taskMember
    exact taskMember
  obtain ⟨node, nodeMember, nodeKey⟩ :=
    integratedPresent task taskDef key contributor
  have nodeContributor : node.group.node.key ∈
      task.groups.map Execution.DeliveryNode.key := by
    rw [nodeKey]
    exact contributor
  have linked : task.occurrence ∈ node.tasks :=
    integratedLinks task taskDef node nodeMember nodeContributor
  obtain ⟨retained, retainedMember, retainedKey, _⟩ :=
    integrated.pruneEmptyGroups_preservesNonempty newWork.newGroups
      integratedUnique ⟨node, nodeMember, nodeKey, List.ne_nil_of_mem linked⟩
  have retainedContributor : retained.group.node.key ∈
      task.groups.map Execution.DeliveryNode.key := by
    rw [retainedKey]
    exact contributor
  have retainedLink : task.occurrence ∈ retained.tasks :=
    prunedLinks task (by rw [State.pruneEmptyGroups_tasks]; exact taskDef)
      retained retainedMember retainedContributor
  have startedMember : retained ∈ started.groupNodes := by
    rw [(pruned.startNewWork_groupCore roots).1]
    exact retainedMember
  exact ⟨retained, startedMember, retainedKey, retainedLink⟩

/-- Stream item integration retains healthy registered owners through the final drain.
Witness: item-by-item availability, nonempty-membership pruning, and pending lower bounds
carry ownership and canonical failure metadata to the recursive-drain theorem.
-/
theorem State.HealthyRegisteredTaskAccounting.streamItems_ofPendingAccounting
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    {parents : Nat → Keys}
    (accounted : queue.HealthyRegisteredTaskAccounting work settled failed)
    (counts : queue.PendingBound (fun _ => True) settled) (unique : queue.GroupKeysUnique)
    (supported : queue.CachedFailuresSupported work failed)
    (cancelled : queue.CancelledRecordsSupported work failed)
    (tasksMatch : queue.RegisteredTasksMatch work)
    (generated : ExecutedWork work)
    (links : queue.ChildLinksCanonical parents)
    (groupMatching : queue.GroupNodesMatchWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    (stream : Execution.DeliveryNode) (items : List StreamItem)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (available : queue.StreamRegistrationsAvailable work failed items)
    : (queue.streamItems stream items).1.HealthyRegisteredTaskAccounting
        work settled failed := by
  let step (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue) (item : StreamItem) :=
    let (current, groups, streams, values) := acc
    let (integrated, newWork) := current.maybeIntegrateWork item.work
    let (pruned, nonempty) := integrated.pruneEmptyGroups newWork.newGroups
    (pruned.startNewWork { newWork with newGroups := nonempty },
      groups ++ nonempty, streams ++ newWork.newStreams, values ++ [item.value])
  let invariant (current : State) :=
    current.HealthyRegisteredTaskAccounting work settled failed ∧
      current.PendingBound (fun _ => True) settled ∧ current.GroupKeysUnique ∧
      current.CachedFailuresSupported work failed ∧ current.ChildLinksCanonical parents ∧
      current.GroupNodesMatchWork work ∧ current.CancelledRecordsSupported work failed
      ∧ current.RegisteredTasksMatch work
  have preserve (acc) (item : StreamItem) (member : item ∈ items)
      (prior : invariant acc.1) (ready : acc.1.ChildGroupsAvailable work failed item.work)
      : invariant (step acc item).1 := by
    obtain ⟨current, groups, streams, values⟩ := acc
    obtain ⟨priorOwners, priorCounts, priorUnique, priorCache, priorEdges, priorGroups,
      priorCancelled, priorTasks⟩ := prior
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
    have owners := priorOwners.maybeIntegrateWork priorUnique item.work none
      (matching.streamItem_childTasksCovered member) ready priorCancelled generated childTasks
      descriptors
    have integratedKeys := priorUnique.maybeIntegrateWork item.work none
    have integratedCounts := priorCounts.maybeIntegrateWork item.work
    have caches := priorCache.maybeIntegrateWork item.work
    have edges := priorEdges.maybeIntegrateWork item.work
      (fun _ groupMember =>
        matching.streamItem_childGroups_parentCanonical canonical member groupMember)
    have groupsMatch := priorGroups.maybeIntegrateWork item.work
      (fun _ groupMember => matching.streamItem_childGroups_recordAt member groupMember)
    have cancellations := priorCancelled.maybeIntegrateWork item.work none descriptors
    have integratedTasks := priorTasks.maybeIntegrateWork item.work childTasks
    have cancellationsPruned : pruned.1.CancelledRecordsSupported work failed := by
      simpa only [pruned, integrated, State.CancelledRecordsSupported,
        State.pruneEmptyGroups_cancelledGroups]
        using cancellations
    exact ⟨(owners.pruneNonemptyGroups integratedKeys _).startNewWork released,
      (integratedCounts.pruneEmptyGroups _).startNewWork released,
      (integratedKeys.pruneEmptyGroups _).startNewWork released,
      (caches.pruneEmptyGroups _).startNewWork released,
      (edges.pruneEmptyGroups _).startNewWork released,
      (groupsMatch.pruneEmptyGroups _).startNewWork released,
      cancellationsPruned.startNewWork released,
      (integratedTasks.pruneEmptyGroups _).startNewWork released⟩
  have loop (more : List StreamItem) (included : more.Subset items) (acc)
      (prior : invariant acc.1)
      (ready : acc.1.StreamRegistrationsAvailable work failed more)
      : invariant (more.foldl step acc).1 := by
    induction more generalizing acc with
    | nil => exact prior
    | cons item rest ih =>
        exact ih (fun _ member => included (List.mem_cons_of_mem _ member)) _
          (preserve acc item (included List.mem_cons_self) prior ready.1) ready.2
  unfold State.streamItems
  split
  · exact accounted
  · have final := loop items (fun _ member => member) (queue, [], [], [])
      ⟨accounted, counts, unique, supported, links, groupMatching, cancelled, tasksMatch⟩
      available
    apply final.1.drainReadyGroups
      (unique := final.2.2.1) (supported := final.2.2.2.1)
      (tasksMatch := final.2.2.2.2.2.2.2) (generated := generated)
      (links := final.2.2.2.2.1) (matching := final.2.2.2.2.2.1) (canonical := canonical)
    exact final.2.1

/-- Every valid started source event preserves healthy registered owners, provided new
task contributors are available at their actual integration states.
Witness: bounded source settlement counts and the full task/stream release proofs; failures
use canonical subtree cleanup. This conditional step needs no healthy-root premise.
-/
theorem State.HealthyRegisteredTaskAccounting.handleGraphEvent_ofPendingAccounting
    {queue : State} {work : Execution.Work} {before : List GraphEvent}
    {parents : Nat → Keys}
    (accounted
      : queue.HealthyRegisteredTaskAccounting work (GraphEvent.taskSettlements before)
          (GraphEvent.failureSettlements before))
    (pending : queue.PendingAccounting work (GraphEvent.taskSettlements before))
    (supported
      : queue.CachedFailuresSupported work (GraphEvent.failureSettlements before))
    (cancelled
      : queue.CancelledRecordsSupported work (GraphEvent.failureSettlements before))
    (links : queue.ChildLinksCanonical parents)
    (groupMatching : queue.GroupNodesMatchWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    (generated : ExecutedWork work) (_valid : ValidGraphEvents work before)
    (event : GraphEvent) (matching : event.MatchesWork work) (fresh : event.Fresh before)
    (accepted : queue.acceptsGraphEvent event = true)
    (available
      : queue.RegistrationsAvailable work (GraphEvent.failureSettlements before) event)
    : (queue.handleGraphEvent event).1.HealthyRegisteredTaskAccounting work
        (GraphEvent.taskSettlements (before ++ [event]))
        (GraphEvent.failureSettlements (before ++ [event])) := by
  rw [GraphEvent.taskSettlements_append, GraphEvent.failureSettlements_append]
  cases event with
  | taskSuccess occurrence result =>
      cases found : queue.taskNode? occurrence with
      | none => simp [State.acceptsGraphEvent, found] at accepted
      | some taskNode =>
          apply accounted.taskSuccess_ofPendingAccounting pending supported cancelled
            links groupMatching canonical generated occurrence result matching taskNode
            found
          · exact fun member => fresh.2.2.1 occurrence (by simp [GraphEvent.identities])
              (GraphEvent.taskSettlements_subsetIdentities before member)
          · exact available
  | taskFailure occurrence errors =>
      have retained := accounted.taskFailure_any generated links groupMatching canonical
        pending.started pending.matching occurrence errors
      exact retained.weakenSettled
        (after := occurrence :: GraphEvent.taskSettlements before)
        (by intro task member; exact List.mem_cons_of_mem _ member)
  | streamItems stream items =>
      exact accounted.streamItems_ofPendingAccounting pending.pending pending.keys supported
        cancelled pending.matching generated links groupMatching canonical stream items matching
        available
  | streamSuccess stream =>
      dsimp only [State.handleGraphEvent, State.streamSuccess, GraphEvent.recordTaskOutcome,
        GraphEvent.groupFailures, List.nil_append]
      split <;> exact accounted
  | streamFailure stream errors =>
      dsimp only [State.handleGraphEvent, State.streamFailure, GraphEvent.recordTaskOutcome,
        GraphEvent.groupFailures, List.nil_append]
      split <;> exact accounted

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
