import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.UnsettledMemberships
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskSettlements
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CacheEligibility
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.HealthyContributors

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
    (available : List (Occurrence × Nat) := [])
    : (queue.taskSuccess occurrence result available).1.PendingBound (fun _ => True)
        (occurrence :: settled)
      ∧ (queue.taskSuccess occurrence result available).1.UnsettledTaskLinks
          (occurrence :: settled) := by
  rw [queue.taskSuccess_eq occurrence result taskNode found available]
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
  have activatedCounts := releasedCounts.startNewWork released.2.2 available
  have activatedLinks := loop.1.2.startNewWork released.2.2 available
  exact ⟨
    activatedCounts.drainReadyGroups available,
    activatedLinks.drainReadyGroups_ofBound activatedCounts available
  ⟩

/-- A failed task preserves counter bounds and all other unsettled task links.
Witness: exact registered ownership, logical settlement before membership removal,
and the active failure fold's one decrement per retained owner. Ignored failures only
remove settled memberships; neither case requires cached groups to be healthy.
-/
theorem State.taskFailure_pendingAccounting
    {queue : State} {settled : List Occurrence}
    (tracks : queue.PendingBound (fun _ => True) settled)
    (linked : queue.UnsettledTaskLinks settled)
    (occurrence : Occurrence) (errors : Nat)
    : (queue.taskFailure occurrence errors).1.PendingBound (fun _ => True)
        (occurrence :: settled)
      ∧ (queue.taskFailure occurrence errors).1.UnsettledTaskLinks
          (occurrence :: settled) :=
  ⟨
    tracks.taskFailure occurrence errors,
    (linked.weaken (by intro task member; simp [member])).taskFailure occurrence errors
  ⟩

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
    (available : List (Occurrence × Nat) := [])
    : (queue.streamItems stream items available).1.PendingBound (fun _ => True) settled
      ∧ (queue.streamItems stream items available).1.UnsettledTaskLinks settled := by
  let step (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue × List GroupFailureEvent)
      (item : StreamItem) :=
    let (current, groups, streams, values, failures) := acc
    let (integrated, newWork) := current.maybeIntegrateWork item.work
    let (pruned, nonempty) := integrated.pruneEmptyGroups newWork.newGroups
    let (started, queued) := pruned.startNewWork { newWork with newGroups := nonempty } available
    (started, groups ++ nonempty, streams ++ newWork.newStreams,
      values ++ [item.value], failures ++ queued)
  let invariant (current : State) :=
    current.PendingBound (fun _ => True) settled ∧ current.UnsettledTaskLinks settled ∧
      current.GroupRefsUnique ∧ current.LiveGroupsRegistered ∧ current.TaskGroupsRegistered
  have preserve (acc) (item : StreamItem) (member : item ∈ items)
      (prior : invariant acc.1) : invariant (step acc item).1 := by
    obtain ⟨current, groups, streams, values, failures⟩ := acc
    let integrated := current.maybeIntegrateWork item.work
    let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
    let released := { integrated.2 with newGroups := pruned.2 }
    have counts := prior.1.maybeIntegrateWork item.work
    have links := prior.2.1.maybeIntegrateWork prior.2.2.1 prior.2.2.2.2 item.work
    have groupRefs := prior.2.2.1.maybeIntegrateWork item.work none
    have registration := current.maybeIntegrateWork_registration
      prior.2.2.2.1 prior.2.2.2.2 item.work (fun task included ref contributes => .inr (allCovered item member task included ref contributes))
    have prunedRegistration := State.pruneEmptyGroups_registration
      registration.1 registration.2.1 integrated.2.newGroups
    have startedRegistration := State.startNewWork_registration
      prunedRegistration.1 prunedRegistration.2.1 released available
    exact ⟨(counts.pruneEmptyGroups _).startNewWork _ available,
      (links.pruneEmptyGroups _).startNewWork _ available,
      (groupRefs.pruneEmptyGroups _).startNewWork _ available, startedRegistration⟩
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
  · have final := loop items (fun _ member => member) (queue, [], [], [], [])
      ⟨tracks, linked, refs, live, covered⟩
    exact ⟨final.1.drainReadyGroups available,
      final.2.1.drainReadyGroups_ofBound final.1 available⟩

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
  registration : queue.RegistrationFrame work

/-- Initial lowering establishes the all-owner ledger for arbitrary finite work.
Witness: the independently proved initialization counts, links, registry, and provenance.
-/
theorem createWorkQueue_pendingAccounting (work : Execution.Work)
    (certified : DeclarationCoverage.Certified [] work)
    : (State.initialize (Work.fromExecution work)).PendingAccounting work [] :=
  ⟨
    createWorkQueue_pendingBound_empty _,
    createWorkQueue_unsettledTaskLinks _,
    createWorkQueue_groupRefsUnique _,
    createWorkQueue_taskMembershipsUnique _,
    (createWorkQueue_registration work certified).1,
    (createWorkQueue_registration work certified).2,
    createWorkQueue_groupMembershipSound _,
    createWorkQueue_fromSpec_registeredTasksMatch _,
    createWorkQueue_startedTasksRegistered _,
    State.initialize_registrationFrame certified
  ⟩

/-- Cache exposure preserves every all-owner bookkeeping field. -/
theorem State.PendingAccounting.cacheTaskFailures {queue : State} {work : Execution.Work}
    {settled : List Occurrence} (prior : queue.PendingAccounting work settled)
    (available : List (Occurrence × Nat))
    : (queue.cacheTaskFailures available).PendingAccounting work settled :=
  ⟨
    prior.pending.cacheTaskFailures available,
    prior.links.cacheTaskFailures available,
    prior.refs.cacheTaskFailures available,
    prior.memberships.cacheTaskFailures available,
    (queue.cacheTaskFailures_registration prior.liveGroups prior.taskGroups available).1,
    (queue.cacheTaskFailures_registration prior.liveGroups prior.taskGroups available).2,
    prior.sound.cacheTaskFailures available,
    prior.matching.cacheTaskFailures available,
    prior.started.cacheTaskFailures available,
    prior.registration.cacheTaskFailures available
  ⟩

/-- Internal notice bookkeeping does not change work-accounting evidence. -/
theorem State.PendingAccounting.withGroupFailures {queue work settled}
    (prior : State.PendingAccounting queue work settled)
    (notices : List GroupFailureEvent)
    : ({ queue with groupFailureEvents := notices }).PendingAccounting work settled :=
  ⟨
    prior.pending,
    prior.links,
    prior.refs,
    prior.memberships,
    prior.liveGroups,
    prior.taskGroups,
    prior.sound,
    prior.matching,
    prior.started,
    prior.registration.withGroupFailures notices
  ⟩

/-- Termination changes no pending counter or permanent registration evidence. -/
theorem State.PendingAccounting.withTerminated {queue work settled}
    (prior : State.PendingAccounting queue work settled) (terminal : Bool)
    : ({ queue with terminated := terminal }).PendingAccounting work settled :=
  ⟨
    prior.pending,
    prior.links,
    prior.refs,
    prior.memberships,
    prior.liveGroups,
    prior.taskGroups,
    prior.sound,
    prior.matching,
    prior.started,
    prior.registration.withTerminated terminal
  ⟩

/-- Processing a matching fresh event preserves bounded all-owner accounting, even if stale.
Witness: source freshness supplies a fresh settlement; generated contributor uniqueness
and permanent registration discharge the task and stream preservation lemmas.
-/
theorem State.PendingAccounting.handleGraphEvent_ofMatching {queue : State}
    {work : Execution.Work} {settled : List Occurrence} {before : List GraphEvent}
    (prior : queue.PendingAccounting work settled) (generated : ExecutedWork work)
    (included : settled.Subset (before.flatMap (fun event => event.identities.1)))
    (event : GraphEvent) (matching : event.MatchesWork work) (fresh : event.Fresh before)
    (available : List (Occurrence × Nat) := [])
    : (queue.handleGraphEvent event available).1.PendingAccounting work
        (event.recordTaskOutcome settled) := by
  let current := queue.cacheTaskFailures available
  have cached := prior.cacheTaskFailures available
  have registry := queue.handleGraphEvent_registration prior.liveGroups prior.taskGroups
    event matching prior.registration available
  have accounting : (queue.handleGraphEvent event available).1.PendingBound (fun _ => True)
        (event.recordTaskOutcome settled)
      ∧ (queue.handleGraphEvent event available).1.UnsettledTaskLinks
        (event.recordTaskOutcome settled) := by
    cases event with
    | taskSuccess occurrence result =>
        cases found : current.taskNode? occurrence with
        | none =>
            change (current.taskSuccess occurrence result available).1.PendingBound _ _
              ∧ (current.taskSuccess occurrence result available).1.UnsettledTaskLinks _
            simp only [State.taskSuccess, found, GraphEvent.recordTaskOutcome]
            exact ⟨
              cached.pending.weakenSettled (by intro task member; simp [member]),
              cached.links.weaken (by intro task member; simp [member])
            ⟩
        | some node =>
            apply current.taskSuccess_pendingAccounting cached.pending cached.links
              cached.refs cached.memberships cached.taskGroups cached.sound
              cached.matching cached.started occurrence result node found
              (available := available)
            · exact fun member => fresh.2.2.1 occurrence (by simp [GraphEvent.identities])
                (included member)
            · exact cached.matching.contributorsNodup generated
                (cached.started node (List.mem_of_find?_eq_some found))
            · intro task member
              obtain ⟨address, payload, same, known⟩ := matching.childTask_producer member
              exact ⟨⟨address, payload, some occurrence, same, known⟩,
                matching.childTask_groupsExact member⟩
    | taskFailure occurrence errors =>
        exact current.taskFailure_pendingAccounting cached.pending cached.links occurrence errors
    | groupFailure failure =>
        dsimp only [State.handleGraphEvent, GraphEvent.recordTaskOutcome,
          GraphEvent.groupSuccesses, List.nil_append, State.groupFailure]
        split
        · exact ⟨cached.pending, cached.links⟩
        · split <;> exact ⟨cached.pending, cached.links⟩
    | streamItems stream items =>
        apply current.streamItems_pendingAccounting cached.pending cached.links cached.refs
          cached.liveGroups cached.taskGroups stream items (available := available)
        exact fun _ member => matching.streamItem_childTasksCovered generated.declarations member
    | streamSuccess stream =>
        dsimp only [State.handleGraphEvent, GraphEvent.recordTaskOutcome, State.streamSuccess]
        split <;> exact ⟨cached.pending, cached.links⟩
    | streamFailure stream errors =>
        dsimp only [State.handleGraphEvent, GraphEvent.recordTaskOutcome, State.streamFailure]
        split <;> exact ⟨cached.pending, cached.links⟩
  exact ⟨
    accounting.1,
    accounting.2,
    prior.refs.handleGraphEvent event available,
    prior.memberships.handleGraphEvent event available,
    registry.1,
    registry.2.1,
    prior.sound.handleGraphEvent event available,
    prior.matching.handleGraphEvent event matching available,
    prior.started.handleGraphEvent event available,
    (prior.registration.handleGraphEvent event matching available).1
  ⟩

/-- Dispatch realizes notice enqueue effects without changing the all-owner ledger. -/
theorem State.PendingAccounting.dispatchGraphEvent_ofMatching {queue : State}
    {work : Execution.Work} {settled : List Occurrence} {before : List GraphEvent}
    (prior : queue.PendingAccounting work settled) (generated : ExecutedWork work)
    (included : settled.Subset (before.flatMap (fun event => event.identities.1)))
    (event : GraphEvent) (matching : event.MatchesWork work) (fresh : event.Fresh before)
    (available : List (Occurrence × Nat) := [])
    : (queue.dispatchGraphEvent event available).1.PendingAccounting work
        (event.recordTaskOutcome settled) :=
  (prior.handleGraphEvent_ofMatching generated included event matching fresh
    available).withGroupFailures
    _

/-- The live-event specialization of matching-handler accounting. -/
theorem State.PendingAccounting.handleGraphEvent {queue : State} {work : Execution.Work}
    {settled : List Occurrence} {before : List GraphEvent}
    (prior : queue.PendingAccounting work settled) (generated : ExecutedWork work)
    (included : settled.Subset (before.flatMap (fun event => event.identities.1)))
    (event : GraphEvent) (matching : event.MatchesWork work) (fresh : event.Fresh before)
    (_accepted : queue.acceptsGraphEvent event = true)
    (available : List (Occurrence × Nat) := [])
    : (queue.handleGraphEvent event available).1.PendingAccounting work
        (event.recordTaskOutcome settled) :=
  prior.handleGraphEvent_ofMatching generated included event matching fresh available

/-- Processing an event preserves counters and links against successful settlements only.
Witness: failures retain their pending tokens; source freshness and contributor uniqueness
and permanent registration discharge the task and stream preservation lemmas.
-/
theorem State.PendingAccounting.handleGraphEvent_successes_ofMatching {queue : State}
    {work : Execution.Work} {settled : List Occurrence} {before : List GraphEvent}
    (prior : queue.PendingAccounting work settled) (generated : ExecutedWork work)
    (included : settled.Subset (before.flatMap (fun event => event.identities.1)))
    (event : GraphEvent) (matching : event.MatchesWork work) (fresh : event.Fresh before)
    (available : List (Occurrence × Nat) := [])
    : (queue.handleGraphEvent event available).1.PendingAccounting work
        (event.groupSuccesses ++ settled) := by
  let current := queue.cacheTaskFailures available
  have cached := prior.cacheTaskFailures available
  have registry := queue.handleGraphEvent_registration prior.liveGroups prior.taskGroups
    event matching prior.registration available
  have accounting : (queue.handleGraphEvent event available).1.PendingBound (fun _ => True)
        (event.groupSuccesses ++ settled)
      ∧ (queue.handleGraphEvent event available).1.UnsettledTaskLinks
        (event.groupSuccesses ++ settled) := by
    cases event with
    | taskSuccess occurrence result =>
        cases found : current.taskNode? occurrence with
        | none =>
            change (current.taskSuccess occurrence result available).1.PendingBound _ _
              ∧ (current.taskSuccess occurrence result available).1.UnsettledTaskLinks _
            simp only [State.taskSuccess, found, GraphEvent.groupSuccesses, List.singleton_append]
            exact ⟨
              cached.pending.weakenSettled (by intro task member; simp [member]),
              cached.links.weaken (by intro task member; simp [member])
            ⟩
        | some node =>
            apply current.taskSuccess_pendingAccounting cached.pending cached.links
              cached.refs cached.memberships cached.taskGroups cached.sound
              cached.matching cached.started occurrence result node found
              (available := available)
            · exact fun member => fresh.2.2.1 occurrence (by simp [GraphEvent.identities])
                (included member)
            · exact cached.matching.contributorsNodup generated
                (cached.started node (List.mem_of_find?_eq_some found))
            · intro task member
              obtain ⟨address, payload, same, known⟩ := matching.childTask_producer member
              exact ⟨⟨address, payload, some occurrence, same, known⟩,
                matching.childTask_groupsExact member⟩
    | taskFailure occurrence errors =>
        exact ⟨cached.pending.taskFailure_preserves occurrence errors,
          cached.links.taskFailure occurrence errors⟩
    | groupFailure failure =>
        dsimp only [State.handleGraphEvent, GraphEvent.recordTaskOutcome,
          GraphEvent.groupSuccesses, List.nil_append, State.groupFailure]
        split
        · exact ⟨cached.pending, cached.links⟩
        · split <;> exact ⟨cached.pending, cached.links⟩
    | streamItems stream items =>
        apply current.streamItems_pendingAccounting cached.pending cached.links cached.refs
          cached.liveGroups cached.taskGroups stream items (available := available)
        exact fun _ member => matching.streamItem_childTasksCovered generated.declarations member
    | streamSuccess stream =>
        dsimp only [State.handleGraphEvent, GraphEvent.groupSuccesses, State.streamSuccess]
        split <;> exact ⟨cached.pending, cached.links⟩
    | streamFailure stream errors =>
        dsimp only [State.handleGraphEvent, GraphEvent.groupSuccesses, State.streamFailure]
        split <;> exact ⟨cached.pending, cached.links⟩
  exact ⟨
    accounting.1,
    accounting.2,
    prior.refs.handleGraphEvent event available,
    prior.memberships.handleGraphEvent event available,
    registry.1,
    registry.2.1,
    prior.sound.handleGraphEvent event available,
    prior.matching.handleGraphEvent event matching available,
    prior.started.handleGraphEvent event available,
    (prior.registration.handleGraphEvent event matching available).1
  ⟩

/-- Dispatch preserves the successful-settlement ledger while retaining queued notices. -/
theorem State.PendingAccounting.dispatchGraphEvent_successes_ofMatching {queue : State}
    {work : Execution.Work} {settled : List Occurrence} {before : List GraphEvent}
    (prior : queue.PendingAccounting work settled) (generated : ExecutedWork work)
    (included : settled.Subset (before.flatMap (fun event => event.identities.1)))
    (event : GraphEvent) (matching : event.MatchesWork work) (fresh : event.Fresh before)
    (available : List (Occurrence × Nat) := [])
    : (queue.dispatchGraphEvent event available).1.PendingAccounting work
        (event.groupSuccesses ++ settled) :=
  (prior.handleGraphEvent_successes_ofMatching generated included event matching fresh
    available).withGroupFailures
    _

/-- The live-event specialization of matching-handler accounting. -/
theorem State.PendingAccounting.handleGraphEvent_successes {queue : State}
    {work : Execution.Work} {settled : List Occurrence} {before : List GraphEvent}
    (prior : queue.PendingAccounting work settled) (generated : ExecutedWork work)
    (included : settled.Subset (before.flatMap (fun event => event.identities.1)))
    (event : GraphEvent) (matching : event.MatchesWork work) (fresh : event.Fresh before)
    (_accepted : queue.acceptsGraphEvent event = true)
    (available : List (Occurrence × Nat) := [])
    : (queue.handleGraphEvent event available).1.PendingAccounting work
        (event.groupSuccesses ++ settled) :=
  prior.handleGraphEvent_successes_ofMatching generated included event matching fresh
    available

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
