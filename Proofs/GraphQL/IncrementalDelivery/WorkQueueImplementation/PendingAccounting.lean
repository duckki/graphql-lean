import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.UnsettledMemberships
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskSettlements

/-! Safe pending accounting across accepted task outcomes, including ignored settlements. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (StreamItemValue)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Successful and failed settlements preserve the same all-owner ledger
-----------------------------------------------------------------------------------------

/-- A successful task preserves counter bounds and links for every live owner.
Witness: permanent registration protects integration, source provenance identifies exact
ownership, and one debt per contributor justifies every interleaved flush and drain.
No root-health or healthy-only accounting assumption is required.
-/
theorem State.taskSuccess_pendingAccounting
    {queue : State} {work : Execution.Work} {settled : List Occurrence}
    (tracks : queue.PendingBound (fun _ => True) settled)
    (linked : queue.UnsettledTaskLinks settled)
    (refs : queue.GroupRefsUnique) (memberships : queue.TaskMembershipsUnique)
    (covered : queue.TaskGroupsRegistered) (sound : queue.GroupMembershipSound)
    (matching : queue.RegisteredTasksMatch work) (started : queue.StartedTasksRegistered)
    (occurrence : Occurrence) (result : TaskResult) (taskNode : TaskNode)
    (found : queue.taskNode? occurrence = some taskNode) (fresh : occurrence ∉ settled)
    (uniqueOwners : (taskNode.task.groups.map Execution.DeliveryNode.ref).Nodup)
    (childrenMatch : ∀ task ∈ result.work.tasks, TaskMatches work task)
    : (queue.taskSuccess occurrence result).1.PendingBound (fun _ => True)
        (occurrence :: settled)
      ∧ (queue.taskSuccess occurrence result).1.UnsettledTaskLinks
          (occurrence :: settled) := by
  rw [queue.taskSuccess_eq occurrence result taskNode found]
  split
  · exact ⟨tracks.ignoreTask occurrence,
      (linked.weaken (by intro item member; exact List.mem_cons_of_mem _ member)).removeSettledTask
        occurrence (by simp)⟩
  let stored := queue.putTaskNode { taskNode with value := some result.value }
  let integrated := (stored.maybeIntegrateWork result.work (some occurrence)).1
  have storedRefs : stored.GroupRefsUnique := refs
  have storedMembers : stored.TaskMembershipsUnique := memberships
  have storedCounts : stored.PendingBound (fun _ => True) settled := tracks
  have storedCovered : stored.TaskGroupsRegistered := covered
  have storedSound : stored.GroupMembershipSound := sound
  have storedMatch : stored.RegisteredTasksMatch work := matching
  have integratedLinks : integrated.UnsettledTaskLinks settled :=
    (linked.putTaskNode _).maybeIntegrateWork storedRefs storedCovered result.work
      (some occurrence)
  have integratedCounts : integrated.PendingBound (fun _ => True) settled :=
    storedCounts.maybeIntegrateWork result.work (some occurrence)
  have integratedRefs := storedRefs.maybeIntegrateWork result.work (some occurrence)
  have integratedMembers := storedMembers.maybeIntegrateWork result.work (some occurrence)
  have integratedSound := storedSound.maybeIntegrateWork result.work (some occurrence)
  have integratedMatch := storedMatch.maybeIntegrateWork result.work childrenMatch
    (some occurrence)
  have taskMember : taskNode.task ∈ integrated.tasks := by
    rw [State.maybeIntegrateWork_tasks_append]
    exact List.mem_append_left _ (started taskNode (List.mem_of_find?_eq_some found))
  have same : taskNode.task.occurrence = occurrence :=
    (occurrence_beq_iff_eq _ _).mp (List.find?_some
      (p := fun candidate : TaskNode => candidate.task.occurrence == occurrence) found)
  have owned := integratedLinks.ownedExactlyBy integratedSound integratedMatch taskMember
    (same.symm ▸ fresh)
  rw [same] at owned
  have debt : integrated.PendingDebtBound (fun _ => True) (occurrence :: settled)
      (taskNode.task.groups.map Execution.DeliveryNode.ref) :=
    integratedCounts.beginSettlement integratedMembers
      (fun node member _ => owned node member) fresh
  let invariant (current : State) :=
    current.GroupRefsUnique ∧ current.UnsettledTaskLinks (occurrence :: settled)
  have initial : invariant integrated :=
    ⟨integratedRefs, integratedLinks.weaken (by intro item member; simp [member])⟩
  have loop := successGroupFold_preservesBound (fun _ => True) (occurrence :: settled)
    invariant (fun _ valid => valid.1) (by intros; trivial)
    (fun _ node prior selected =>
      ⟨prior.1.putGroupNode _, prior.2.putGroupNodeSameTasks prior.1 node
        (List.mem_of_find?_eq_some selected) _ rfl rfl⟩)
    (fun _ node _ prior _ _ _ _ all =>
      ⟨prior.1.finishGroupSuccess node, prior.2.finishGroupSuccess node all⟩)
    taskNode.task.groups uniqueOwners (integrated, [], {}) initial debt
  let released := taskNode.task.groups.foldl successGroupStep (integrated, [], {})
  have releasedCounts : released.1.PendingBound (fun _ => True) (occurrence :: settled) := loop.2
  have activatedCounts := releasedCounts.startNewWork released.2.2
  have activatedLinks := loop.1.2.startNewWork released.2.2
  exact ⟨
    activatedCounts.drainReadyGroups,
    activatedLinks.drainReadyGroups_ofBound activatedCounts
  ⟩

/-- A failed task preserves counter bounds and all other unsettled task links.
Witness: exact registered ownership, logical settlement before membership removal,
and the active failure fold's one decrement per retained owner. Ignored failures only
remove settled memberships; neither case requires cached groups to be healthy.
-/
theorem State.taskFailure_pendingAccounting
    {queue : State} {work : Execution.Work} {settled : List Occurrence}
    (tracks : queue.PendingBound (fun _ => True) settled)
    (linked : queue.UnsettledTaskLinks settled)
    (refs : queue.GroupRefsUnique) (memberships : queue.TaskMembershipsUnique)
    (sound : queue.GroupMembershipSound) (matching : queue.RegisteredTasksMatch work)
    (started : queue.StartedTasksRegistered)
    (occurrence : Occurrence) (errors : Nat) (taskNode : TaskNode)
    (found : queue.taskNode? occurrence = some taskNode) (fresh : occurrence ∉ settled)
    (uniqueOwners : (taskNode.task.groups.map Execution.DeliveryNode.ref).Nodup)
    : (queue.taskFailure occurrence errors).1.PendingBound (fun _ => True)
        (occurrence :: settled)
      ∧ (queue.taskFailure occurrence errors).1.UnsettledTaskLinks
          (occurrence :: settled) := by
  rw [queue.taskFailure_eq occurrence errors taskNode found]
  split
  · exact ⟨tracks.ignoreTask occurrence,
      (linked.weaken (by intro item member; exact List.mem_cons_of_mem _ member)).removeSettledTask
        occurrence (by simp)⟩
  have same : taskNode.task.occurrence = occurrence :=
    (occurrence_beq_iff_eq _ _).mp (List.find?_some
      (p := fun candidate : TaskNode => candidate.task.occurrence == occurrence) found)
  have owned := linked.ownedExactlyBy sound matching
    (started taskNode (List.mem_of_find?_eq_some found)) (same.symm ▸ fresh)
  rw [same] at owned
  have debt : queue.PendingDebtBound (fun _ => True) (occurrence :: settled)
      (taskNode.task.groups.map Execution.DeliveryNode.ref) :=
    tracks.beginSettlement memberships (fun node member _ => owned node member) fresh
  have settledLinks := linked.weaken (after := occurrence :: settled)
    (by intro item member; simp [member])
  let invariant (current : State) :=
    current.GroupRefsUnique ∧ current.UnsettledTaskLinks (occurrence :: settled)
  have loop := failureGroupFold_preservesBound (fun _ => True) (occurrence :: settled)
    invariant (fun _ valid => valid.1)
    (fun _ node _ prior selected =>
      ⟨prior.1.putGroupNode _, prior.2.putGroupNodeSameTasks prior.1 node
        (List.mem_of_find?_eq_some selected) _ rfl rfl⟩)
    (fun _ ref prior => ⟨prior.1.removeGroup ref, prior.2.removeGroup ref⟩)
    errors taskNode.task.groups uniqueOwners (queue.removeTask occurrence, [])
    ⟨refs.removeTask occurrence, settledLinks.removeSettledTask occurrence (by simp)⟩
    (debt.removeTask occurrence (by simp))
  exact ⟨loop.2, loop.1.2⟩

-----------------------------------------------------------------------------------------
-- Stream integration preserves the same ledger
-----------------------------------------------------------------------------------------

/-- Stream items preserve all-owner counter bounds and unsettled links through the drain.
Witness: sequential integration maintains registry coverage at each actual item state;
child tasks extend the bounded ledger and the drain preserves its remaining links.
-/
theorem State.streamItems_pendingAccounting
    {queue : State} {settled : List Occurrence}
    (tracks : queue.PendingBound (fun _ => True) settled)
    (linked : queue.UnsettledTaskLinks settled)
    (refs : queue.GroupRefsUnique) (live : queue.LiveGroupsRegistered)
    (covered : queue.TaskGroupsRegistered) (stream : Execution.DeliveryNode)
    (items : List StreamItem)
    (allCovered
      : ∀ item ∈ items,
        ∀ task ∈ item.work.tasks,
        ∀ ref ∈ task.groups.map Execution.DeliveryNode.ref,
          ∃ group ∈ item.work.groups, group.node.ref = ref)
    : (queue.streamItems stream items).1.PendingBound (fun _ => True) settled
      ∧ (queue.streamItems stream items).1.UnsettledTaskLinks settled := by
  let step (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue) (item : StreamItem) :=
    let (current, groups, streams, values) := acc
    let (integrated, newWork) := current.maybeIntegrateWork item.work
    let (pruned, nonempty) := integrated.pruneEmptyGroups newWork.newGroups
    (pruned.startNewWork { newWork with newGroups := nonempty },
      groups ++ nonempty, streams ++ newWork.newStreams, values ++ [item.value])
  let invariant (current : State) :=
    current.PendingBound (fun _ => True) settled ∧ current.UnsettledTaskLinks settled ∧
      current.GroupRefsUnique ∧ current.LiveGroupsRegistered ∧ current.TaskGroupsRegistered
  have preserve (acc) (item : StreamItem) (member : item ∈ items)
      (prior : invariant acc.1) : invariant (step acc item).1 := by
    obtain ⟨current, groups, streams, values⟩ := acc
    let integrated := current.maybeIntegrateWork item.work
    let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
    let released := { integrated.2 with newGroups := pruned.2 }
    have counts := prior.1.maybeIntegrateWork item.work
    have links := prior.2.1.maybeIntegrateWork prior.2.2.1 prior.2.2.2.2 item.work
    have groupRefs := prior.2.2.1.maybeIntegrateWork item.work none
    have registration := current.maybeIntegrateWork_registration
      prior.2.2.2.1 prior.2.2.2.2 item.work (allCovered item member)
    have prunedRegistration := State.pruneEmptyGroups_registration
      registration.1 registration.2.1 integrated.2.newGroups
    have startedRegistration := State.startNewWork_registration
      prunedRegistration.1 prunedRegistration.2.1 released
    exact ⟨(counts.pruneEmptyGroups _).startNewWork _,
      (links.pruneEmptyGroups _).startNewWork _,
      (groupRefs.pruneEmptyGroups _).startNewWork _, startedRegistration⟩
  have loop (more : List StreamItem) (included : more.Subset items) (acc)
      (prior : invariant acc.1) : invariant (more.foldl step acc).1 := by
    induction more generalizing acc with
    | nil => exact prior
    | cons item rest ih =>
        exact ih (fun _ member => included (List.mem_cons_of_mem _ member)) _
          (preserve acc item (included List.mem_cons_self) prior)
  dsimp only [State.streamItems]
  split
  · exact ⟨tracks, linked⟩
  · have final := loop items (fun _ member => member) (queue, [], [], [])
      ⟨tracks, linked, refs, live, covered⟩
    exact ⟨final.1.drainReadyGroups, final.2.1.drainReadyGroups_ofBound final.1⟩

-----------------------------------------------------------------------------------------
-- Source-event preservation requires no healthy-owner or output-admission premise
-----------------------------------------------------------------------------------------

/-- Internal ledger for all live groups and registered unsettled tasks.
The proof-only `settled` list includes all processed successes and failures, even ignored
settlements. Counters bound unsettled memberships; failed groups may retain surplus.
Registry, provenance, and uniqueness justify exact ownership, not exact counter values.
No observable correctness is assumed.
-/
structure State.PendingAccounting (queue : State) (work : Execution.Work)
    (settled : List Occurrence)
    : Prop where
  pending : queue.PendingBound (fun _ => True) settled
  links : queue.UnsettledTaskLinks settled
  refs : queue.GroupRefsUnique
  memberships : queue.TaskMembershipsUnique
  liveGroups : queue.LiveGroupsRegistered
  taskGroups : queue.TaskGroupsRegistered
  sound : queue.GroupMembershipSound
  matching : queue.RegisteredTasksMatch work
  started : queue.StartedTasksRegistered

/-- Initial lowering establishes the all-owner ledger for arbitrary finite work.
Witness: the independently proved initialization counts, links, registry, and provenance.
-/
theorem createWorkQueue_pendingAccounting (work : Execution.Work)
    : (State.initialize (Work.fromExecution work)).PendingAccounting work [] :=
  ⟨
    createWorkQueue_pendingBound_empty _,
    createWorkQueue_unsettledTaskLinks _,
    createWorkQueue_groupRefsUnique _,
    createWorkQueue_taskMembershipsUnique _,
    (createWorkQueue_registration work).1,
    (createWorkQueue_registration work).2,
    createWorkQueue_groupMembershipSound _,
    createWorkQueue_fromSpec_registeredTasksMatch _,
    createWorkQueue_startedTasksRegistered _
  ⟩

/-- Processing a matching fresh started event preserves bounded all-owner accounting.
Witness: source freshness supplies a fresh settlement; generated contributor uniqueness
and permanent registration discharge the task and stream preservation lemmas.
-/
theorem State.PendingAccounting.handleGraphEvent {queue : State} {work : Execution.Work}
    {settled : List Occurrence} {before : List GraphEvent}
    (prior : queue.PendingAccounting work settled) (generated : ExecutedWork work)
    (included : settled.Subset (before.flatMap (fun event => event.identities.1)))
    (event : GraphEvent) (matching : event.MatchesWork work) (fresh : event.Fresh before)
    (accepted : queue.acceptsGraphEvent event = true)
    : (queue.handleGraphEvent event).1.PendingAccounting work
        (event.recordTaskOutcome settled) := by
  have registry := queue.handleGraphEvent_registration prior.liveGroups prior.taskGroups
    event matching
  have accounting : (queue.handleGraphEvent event).1.PendingBound (fun _ => True)
        (event.recordTaskOutcome settled)
      ∧ (queue.handleGraphEvent event).1.UnsettledTaskLinks
        (event.recordTaskOutcome settled) := by
    cases event with
    | taskSuccess occurrence result =>
        cases found : queue.taskNode? occurrence with
        | none => simp [State.acceptsGraphEvent, found] at accepted
        | some node =>
            apply queue.taskSuccess_pendingAccounting prior.pending prior.links prior.refs
              prior.memberships prior.taskGroups prior.sound prior.matching prior.started
              occurrence result node found
            · exact fun member => fresh.2.2.1 occurrence (by simp [GraphEvent.identities])
                (included member)
            · exact prior.matching.contributorsNodup generated
                (prior.started node (List.mem_of_find?_eq_some found))
            · intro task member
              obtain ⟨address, payload, same, known⟩ := matching.childTask_producer member
              exact ⟨⟨address, payload, some occurrence, same, known⟩,
                matching.childTask_groupsExact member⟩
    | taskFailure occurrence errors =>
        cases found : queue.taskNode? occurrence with
        | none => simp [State.acceptsGraphEvent, found] at accepted
        | some node =>
            apply queue.taskFailure_pendingAccounting prior.pending prior.links prior.refs
              prior.memberships prior.sound prior.matching prior.started occurrence errors
              node found
            · exact fun member => fresh.2.2.1 occurrence (by simp [GraphEvent.identities])
                (included member)
            · exact prior.matching.contributorsNodup generated
                (prior.started node (List.mem_of_find?_eq_some found))
    | streamItems stream items =>
        apply queue.streamItems_pendingAccounting prior.pending prior.links prior.refs
          prior.liveGroups prior.taskGroups stream items
        exact fun _ member => matching.streamItem_childTasksCovered member
    | streamSuccess stream =>
        dsimp only [State.handleGraphEvent, GraphEvent.recordTaskOutcome, State.streamSuccess]
        split <;> exact ⟨prior.pending, prior.links⟩
    | streamFailure stream errors =>
        dsimp only [State.handleGraphEvent, GraphEvent.recordTaskOutcome, State.streamFailure]
        split <;> exact ⟨prior.pending, prior.links⟩
  exact ⟨accounting.1, accounting.2, prior.refs.handleGraphEvent event,
    prior.memberships.handleGraphEvent event, registry.1, registry.2.1,
    prior.sound.handleGraphEvent event, prior.matching.handleGraphEvent event matching,
    prior.started.handleGraphEvent event⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
