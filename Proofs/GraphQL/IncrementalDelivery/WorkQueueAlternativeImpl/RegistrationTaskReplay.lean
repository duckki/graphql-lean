import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationSettlement
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationReachability
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PendingReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskProducerOrder
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedHandlerFrames

/-! Local task-success handler correspondence under the reference accounting invariant. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue
open GraphQL.IncrementalDelivery.Execution (ExecutionGroupValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics (Occurrence NodeRefs)

-----------------------------------------------------------------------------------------
-- Successful settlement retains the permanent catalogue used by delayed startTask
-----------------------------------------------------------------------------------------

private theorem finishGroupSuccess_tasks (queue : ReferenceWorkQueue.State)
    (group : ReferenceWorkQueue.GroupNode)
    : (queue.finishGroupSuccess group).1.tasks = queue.tasks := by
  have loop (tasks : List Occurrence)
      (acc : ReferenceWorkQueue.State × List ExecutionGroupValue × NodeRefs)
      : (tasks.foldl ReferenceWorkQueue.flushGroupTask acc).1.tasks = acc.1.tasks := by
    induction tasks generalizing acc with
    | nil => rfl
    | cons occurrence rest ih =>
        rw [List.foldl_cons, ih]
        unfold ReferenceWorkQueue.flushGroupTask
        split <;> rfl
  unfold ReferenceWorkQueue.State.finishGroupSuccess
  simp only
  rw [ReferenceWorkQueue.State.pruneEmptyGroups_tasks]
  change (group.tasks.foldl ReferenceWorkQueue.flushGroupTask (queue, [], [])).1.tasks = queue.tasks
  exact loop group.tasks (queue, [], [])

theorem successGroupFold_tasks (groups : List Execution.DeliveryNode)
    (acc : ReferenceWorkQueue.State × List WorkQueueEvent × ReferenceWorkQueue.NewWork)
    : (groups.foldl ReferenceWorkQueue.successGroupStep acc).1.tasks = acc.1.tasks := by
  induction groups generalizing acc with
  | nil => rfl
  | cons group rest ih =>
      rw [List.foldl_cons, ih]
      unfold ReferenceWorkQueue.successGroupStep
      dsimp only
      split
      · rfl
      · split
        · exact finishGroupSuccess_tasks _ _
        · rfl

-----------------------------------------------------------------------------------------
-- Transfer the reference decrement debt at the exact registration boundary
-----------------------------------------------------------------------------------------

/-- The actual registration state reserves every direct-owner decrement before settlement.
Witness: full scope completion reuses the reference all-owner ledger and exact ownership.
The temporary active tasks do not alter counters or catalogue provenance.
-/
theorem State.taskSuccess_registrationDebt {state : State} {work : Work}
    {settled : List Occurrence} (present : state.queue.RootGroupsPresent)
    (accounting : state.queue.PendingAccounting work settled) (occurrence : Occurrence)
    (result : ReferenceWorkQueue.TaskResult) (node : ReferenceWorkQueue.TaskNode)
    (found : state.queue.taskNode? occurrence = some node) (fresh : occurrence ∉ settled)
    (known : ∀ task ∈ result.work.tasks, ReferenceWorkQueue.TaskMatches work task)
    : let stored : State :=
        {
          state with
            queue := state.queue.putTaskNode { node with value := some result.value }
        }
      let registered := stored.maybeIntegrateWork result.work (some occurrence)
      registered.1.queue.PendingDebtBound (fun _ => True) (occurrence :: settled)
        (node.task.groups.map Execution.DeliveryNode.ref) := by
  let stored : State := { state with queue := state.queue.putTaskNode { node with value := some result.value } }
  let registered := stored.maybeIntegrateWork result.work (some occurrence)
  let prepared := (stored.queue.maybeIntegrateWork result.work (some occurrence)).1
  have storedFound := ReferenceWorkQueue.State.putTaskNode_value_lookup found result.value
  have storedReady : (stored.queue.taskNode? occurrence).isSome = true :=
    congrArg Option.isSome storedFound
  have complete := stored.maybeIntegrateWork_complete result.work present (some occurrence)
    (by intro candidate same; cases Option.some.inj same; exact storedReady)
  dsimp only at complete
  have storedMembers : stored.queue.TaskMembershipsUnique := accounting.memberships
  have storedCounts : stored.queue.PendingBound (fun _ => True) settled := accounting.pending
  have storedSound : stored.queue.GroupMembershipSound := accounting.sound
  have storedMatching : stored.queue.RegisteredTasksMatch work := accounting.matching
  have members := storedMembers.maybeIntegrateWork result.work (some occurrence)
  have counts := storedCounts.maybeIntegrateWork result.work (some occurrence)
  have links := (accounting.links.putTaskNode { node with value := some result.value }).maybeIntegrateWork
    accounting.refs accounting.taskGroups result.work (some occurrence)
  have sound := storedSound.maybeIntegrateWork result.work (some occurrence)
  have matching := storedMatching.maybeIntegrateWork result.work known (some occurrence)
  have member : node.task ∈ prepared.tasks := by
    rw [ReferenceWorkQueue.State.maybeIntegrateWork_tasks_append]
    exact List.mem_append_left _ (accounting.started node (List.mem_of_find?_eq_some found))
  have same := (ReferenceWorkQueue.State.taskNode?_some found).2
  have owned := links.ownedExactlyBy sound matching member (same.symm ▸ fresh)
  rw [same] at owned
  have debt := counts.beginSettlement members (fun current included _ => owned current included) fresh
  have projected : registrationCore registered.1.queue = registrationCore prepared := by
    have common := congrArg registrationCore complete.1
    rw [activateRegisteredTasks_nodes] at common
    exact common
  change (registrationCore registered.1.queue).PendingDebtBound (fun _ => True)
    (occurrence :: settled) (node.task.groups.map Execution.DeliveryNode.ref)
  rw [projected]
  exact debt

-----------------------------------------------------------------------------------------
-- Actual task-success handler: register, settle, start, and drain
-----------------------------------------------------------------------------------------

/-- The named success fold is definitionally the actual specialized handler's owner loop. -/
theorem State.taskSuccess_eq (state : State) (occurrence : Occurrence)
    (result : ReferenceWorkQueue.TaskResult) (node : ReferenceWorkQueue.TaskNode)
    (found : state.queue.taskNode? occurrence = some node)
    : state.taskSuccess occurrence result
      = let stored : State :=
          {
            state with
              queue := state.queue.putTaskNode { node with value := some result.value }
          }
        let registered := stored.maybeIntegrateWork result.work (some occurrence)
        let released :=
          node.task.groups.foldl ReferenceWorkQueue.successGroupStep
            (registered.1.queue, [], {})
        let started :=
          ({ registered.1 with queue := released.1 }).startNewWork released.2.2
            registered.2
        let drained := started.1.drainReadyGroups started.2
        (
          drained.1,
          released.2.1 ++ drained.2.1,
          [.adopt occurrence] ++ drained.2.2.flatMap CleanupTarget.effects
        ) := by
  simp only [State.taskSuccess, found]
  rfl

/-- The actual accepted task-success phase immediately before ready draining.
This is proof notation for the existing registration/owner/start calculation, not another
runtime pass or an output-driven cleanup observer.
-/
def taskSuccessReadyPhase (state : State) (occurrence : Occurrence)
    (result : ReferenceWorkQueue.TaskResult) (node : ReferenceWorkQueue.TaskNode)
    : State × List WorkQueueEvent × List CleanupTarget :=
  let stored : State :=
    {
      state with
        queue := state.queue.putTaskNode { node with value := some result.value }
    }
  let registered := stored.maybeIntegrateWork result.work (some occurrence)
  let released :=
    node.task.groups.foldl ReferenceWorkQueue.successGroupStep
      (registered.1.queue, [], {})
  let active :=
    ({ registered.1 with queue := released.1 }).startNewWork released.2.2 registered.2
  (active.1, released.2.1, active.2)

/-- The real pre-drain phase preserves the interruption guard. -/
theorem taskSuccessReadyPhase_stopped (state : State) (occurrence : Occurrence)
    (result : ReferenceWorkQueue.TaskResult) (node : ReferenceWorkQueue.TaskNode)
    : (taskSuccessReadyPhase state occurrence result node).1.stopped = state.stopped := by
  unfold taskSuccessReadyPhase
  rw [State.startNewWork_stopped]
  exact State.maybeIntegrateWork_stopped
    { state with queue := state.queue.putTaskNode { node with value := some result.value } }
    result.work (some occurrence)

/-- The existing registration/decrement proof identifies the exact pre-drain kernel and
wire prefix. Reusing this boundary avoids re-proving settlement commutation in resource
clients; no cleanup or desired final-state premise is required.
-/
theorem State.taskSuccess_readyProjection {state : State} {work : Work}
    {settled : List Occurrence} (generated : ReferenceWorkQueue.ExecutedWork work)
    (present : state.queue.RootGroupsPresent)
    (accounting : state.queue.PendingAccounting work settled) (occurrence : Occurrence)
    (result : ReferenceWorkQueue.TaskResult) (node : ReferenceWorkQueue.TaskNode)
    (found : state.queue.taskNode? occurrence = some node) (fresh : occurrence ∉ settled)
    (known : ∀ task ∈ result.work.tasks, ReferenceWorkQueue.TaskMatches work task)
    (childFresh : ∀ task ∈ result.work.tasks, task.occurrence ∉ occurrence :: settled)
    (running : state.stopped = false)
    : let active := taskSuccessReadyPhase state occurrence result node
      let integrated :=
        (ReferenceWorkQueue.State.maybeIntegrateWork
          (state.queue.putTaskNode { node with value := some result.value })
          result.work (some occurrence)).1
      let released :=
        node.task.groups.foldl ReferenceWorkQueue.successGroupStep (integrated, [], {})
      (active.1.queue, active.2.1)
      = (referenceTaskSuccessReady state.queue occurrence result node, released.2.1) := by

  let stored : State := { state with queue := state.queue.putTaskNode { node with value := some result.value } }
  let registered := stored.maybeIntegrateWork result.work (some occurrence)
  let released := node.task.groups.foldl ReferenceWorkQueue.successGroupStep (registered.1.queue, [], {})
  have storedFound := ReferenceWorkQueue.State.putTaskNode_value_lookup found result.value
  have storedReady : (stored.queue.taskNode? occurrence).isSome = true :=
    congrArg Option.isSome storedFound
  have complete := stored.maybeIntegrateWork_complete result.work present (some occurrence)
    (by intro candidate same; cases Option.some.inj same; exact storedReady)
  dsimp only at complete
  have registeredMatch := stored.maybeIntegrateWork_registeredTasksMatch accounting.matching
    result.work known (some occurrence)
  have unique := accounting.matching.contributorsNodup generated
    (accounting.started node (List.mem_of_find?_eq_some found))
  have keys := stored.maybeIntegrateWork_groupKeysUnique accounting.refs result.work (some occurrence)
  have debt := state.taskSuccess_registrationDebt present accounting occurrence result node found fresh known
  have activeFresh : ∀ task ∈ registered.2.activeTasks, task.occurrence ∉ occurrence :: settled := by
    intro task member
    exact childFresh task (stored.maybeIntegrateWork_activeTasks result.work (some occurrence) member)
  have commute := successGroupFold_activateRegisteredTasks (occurrence :: settled)
    registered.2.activeTasks activeFresh node.task.groups unique (registered.1.queue, [], {}) keys debt
  have catalogue := successGroupFold_tasks node.task.groups (registered.1.queue, [], {})
  have releasedMatch : released.1.RegisteredTasksMatch work := by
    intro task member
    rw [catalogue] at member
    exact registeredMatch task member
  have members : registered.2.activeTasks.Subset released.1.tasks := by
    intro task member
    rw [catalogue]
    change task ∈ (stored.maybeIntegrateWork result.work (some occurrence)).1.queue.tasks
    rw [State.maybeIntegrateWork_tasks stored result.work (some occurrence)]
    exact List.mem_append_right _ (stored.maybeIntegrateWork_activeTasks result.work (some occurrence) member)
  have actualStarts := activateRegisteredTasks_eq_startTasks releasedMatch registered.2.activeTasks members
  have ready := State.startNewWork_queue ({ registered.1 with queue := released.1 }) released.2.2
    registered.2 [] ((stored.maybeIntegrateWork_stopped result.work (some occurrence)).trans running)
  unfold completeSuccessAcc at commute
  dsimp only at commute
  rw [complete.1] at commute
  have referenceQueue := congrArg Prod.fst commute
  have referenceEvents := congrArg (fun acc : ReferenceWorkQueue.State × List WorkQueueEvent
    × ReferenceWorkQueue.NewWork => acc.2.1) commute
  have referenceRoots := congrArg (fun acc : ReferenceWorkQueue.State × List WorkQueueEvent
    × ReferenceWorkQueue.NewWork => acc.2.2) commute
  dsimp only at referenceQueue referenceEvents referenceRoots
  let active := ({ registered.1 with queue := released.1 }).startNewWork released.2.2 registered.2
  have activeQueue : active.1.queue = referenceTaskSuccessReady state.queue occurrence result node := by
    rw [ready, ← actualStarts, ← referenceQueue, ← referenceRoots]
    rfl
  exact Prod.ext activeQueue referenceEvents.symm

/-- A live task-success handler retains exactly the reference kernel and ordered wire events.
Witness: reference accounting reserves direct-owner decrements; fresh child starts commute
through every permitted flush, then catalogue coherence recovers actual delayed starts.
The premises are phase invariants/source facts, not additions to the public host contract.
-/
theorem State.taskSuccess_projection {state : State} {work : Work}
    {settled : List Occurrence} (generated : ReferenceWorkQueue.ExecutedWork work)
    (present : state.queue.RootGroupsPresent)
    (accounting : state.queue.PendingAccounting work settled) (occurrence : Occurrence)
    (result : ReferenceWorkQueue.TaskResult) (node : ReferenceWorkQueue.TaskNode)
    (found : state.queue.taskNode? occurrence = some node) (fresh : occurrence ∉ settled)
    (known : ∀ task ∈ result.work.tasks, ReferenceWorkQueue.TaskMatches work task)
    (childFresh : ∀ task ∈ result.work.tasks, task.occurrence ∉ occurrence :: settled)
    (running : state.stopped = false)
    (frames
      : ∃ parents,
          (referenceTaskSuccessReady state.queue occurrence result node).TaskOwnerFrame
            work
          ∧ (referenceTaskSuccessReady state.queue occurrence result node).RemovalForest
              parents)
    : (
        (state.taskSuccess occurrence result).1.queue,
        (state.taskSuccess occurrence result).2.1
      )
      = state.queue.taskSuccess occurrence result := by
  rw [state.taskSuccess_eq occurrence result node found,
    ReferenceWorkQueue.State.taskSuccess_eq occurrence result node found]
  let active := taskSuccessReadyPhase state occurrence result node
  have phase := state.taskSuccess_readyProjection generated present accounting
    occurrence result node found fresh known childFresh running
  have activeQueue : active.1.queue = referenceTaskSuccessReady state.queue occurrence result node :=
    congrArg Prod.fst phase
  have activeRunning : active.1.stopped = false :=
    (taskSuccessReadyPhase_stopped state occurrence result node).trans running
  obtain ⟨parents, frame, forest⟩ := frames
  have activeFrame : active.1.queue.TaskOwnerFrame work := by rw [activeQueue]; exact frame
  have activeForest : active.1.queue.RemovalForest parents := by rw [activeQueue]; exact forest
  have drain := active.1.drainReadyGroups_projection activeRunning activeFrame activeForest active.2.2
  rw [activeQueue] at drain
  have whole := congrArg (fun pair => (pair.1, active.2.1 ++ pair.2)) drain
  let integrated := (ReferenceWorkQueue.State.maybeIntegrateWork
    (state.queue.putTaskNode { node with value := some result.value })
    result.work (some occurrence)).1
  let referenceReleased := node.task.groups.foldl ReferenceWorkQueue.successGroupStep (integrated, [], {})
  have wirePrefix : active.2.1 = referenceReleased.2.1 := congrArg Prod.snd phase
  change ((active.1.drainReadyGroups active.2.2).1.queue,
      active.2.1 ++ (active.1.drainReadyGroups active.2.2).2.1) =
    ((referenceTaskSuccessReady state.queue occurrence result node).drainReadyGroups.1,
      referenceReleased.2.1 ++
        (referenceTaskSuccessReady state.queue occurrence result node).drainReadyGroups.2)
  exact whole.trans (by rw [wirePrefix])

-----------------------------------------------------------------------------------------
-- Close the local proof premises over actual accepted generated source prefixes
-----------------------------------------------------------------------------------------

/-- Generated source prefixes identify the same actual pre-drain queue used by the
handler projection. This exposes the reusable phase without imposing a cleanup premise.
-/
theorem referencePrefix_taskSuccess_readyProjection {work : Work}
    (generated : ReferenceWorkQueue.ExecutedWork work) (events : List GraphEvent)
    (occurrence : Occurrence) (result : ReferenceWorkQueue.TaskResult)
    (valid
      : ReferenceWorkQueue.ValidGraphEvents work
          (events ++ [.taskSuccess occurrence result]))
    (accepted
      : (ReferenceWorkQueue.State.initialize
          (ReferenceWorkQueue.Work.fromExecution work)).acceptsBatch
          events
        = true)
    : let queue :=
        (ReferenceWorkQueue.State.initialize
          (ReferenceWorkQueue.Work.fromExecution work)).replayGraphEvents
          events
      ∀ node,
        queue.taskNode? occurrence = some node
        → (taskSuccessReadyPhase { queue } occurrence result node).1.queue
          = referenceTaskSuccessReady queue occurrence result node := by
  obtain ⟨priorValid, matched, freshEvent⟩ := ReferenceWorkQueue.validGraphEvents_last valid
  let initial := ReferenceWorkQueue.State.initialize (ReferenceWorkQueue.Work.fromExecution work)
  let queue := initial.replayGraphEvents events
  let state : State := { queue }
  have initialAccounting : initial.PendingAccounting work
      (ReferenceWorkQueue.GraphEvent.taskSettlements []) :=
    ReferenceWorkQueue.createWorkQueue_pendingAccounting work
  have accounting := initialAccounting.replayGraphEvents generated events
    (by simpa only [List.nil_append] using priorValid) accepted
  have presence := generated.replayGraphEvents_rootsPresent events
    (fun event member => priorValid.eachMatches member)
  have fresh : occurrence ∉ ReferenceWorkQueue.GraphEvent.taskSettlements events := by
    intro settled
    exact freshEvent.2.2.1 occurrence List.mem_cons_self
      (ReferenceWorkQueue.GraphEvent.taskSettlements_subsetIdentities events settled)
  have known : ∀ task ∈ result.work.tasks, ReferenceWorkQueue.TaskMatches work task := by
    intro task member
    obtain ⟨address, payload, same, known⟩ := matched.childTask_producer member
    exact ⟨⟨address, payload, some occurrence, same, known⟩, matched.childTask_groupsExact member⟩
  have childFresh : ∀ task ∈ result.work.tasks,
      task.occurrence ∉ occurrence :: ReferenceWorkQueue.GraphEvent.taskSettlements events := by
    intro task member settled
    rcases List.mem_cons.mp settled with current | earlier
    · exact matched.childTasks_not_success member (List.mem_cons.mpr (.inl current))
    · exact matched.childTasks_unsettled priorValid freshEvent member
        (ReferenceWorkQueue.GraphEvent.taskSettlements_subsetIdentities events earlier)
  change ∀ node, queue.taskNode? occurrence = some node
    → (taskSuccessReadyPhase state occurrence result node).1.queue
      = referenceTaskSuccessReady queue occurrence result node
  intro node found
  exact congrArg Prod.fst (State.taskSuccess_readyProjection generated presence accounting
    occurrence result node found fresh known childFresh rfl)

/-- Every valid accepted generated prefix gives exact task-success handler correspondence.
Witness: replay derives the reference accounting invariant; the unchanged source contract
provides exact child descriptors and freshness before and after the settling producer.
Missing task nodes are silent on both sides. No wire-lifecycle or result-equality premise
is used to justify dispatch equality.
-/
theorem referencePrefix_taskSuccess {work : Work}
    (generated : ReferenceWorkQueue.ExecutedWork work) (events : List GraphEvent)
    (occurrence : Occurrence) (result : ReferenceWorkQueue.TaskResult)
    (valid
      : ReferenceWorkQueue.ValidGraphEvents work
          (events ++ [.taskSuccess occurrence result]))
    (accepted
      : (ReferenceWorkQueue.State.initialize
          (ReferenceWorkQueue.Work.fromExecution work)).acceptsBatch
          events
        = true)
    : let queue :=
        (ReferenceWorkQueue.State.initialize
          (ReferenceWorkQueue.Work.fromExecution work)).replayGraphEvents
          events
      let alternative := ({ queue } : State).taskSuccess occurrence result
      (alternative.1.queue, alternative.2.1) = queue.taskSuccess occurrence result := by
  obtain ⟨priorValid, matched, freshEvent⟩ := ReferenceWorkQueue.validGraphEvents_last valid
  let initial := ReferenceWorkQueue.State.initialize (ReferenceWorkQueue.Work.fromExecution work)
  let queue := initial.replayGraphEvents events
  let state : State := { queue }
  have initialAccounting : initial.PendingAccounting work
      (ReferenceWorkQueue.GraphEvent.taskSettlements []) :=
    ReferenceWorkQueue.createWorkQueue_pendingAccounting work
  have accounting := initialAccounting.replayGraphEvents generated events
    (by simpa only [List.nil_append] using priorValid) accepted
  have presence := generated.replayGraphEvents_rootsPresent events
    (fun event member => priorValid.eachMatches member)
  have fresh : occurrence ∉ ReferenceWorkQueue.GraphEvent.taskSettlements events := by
    intro settled
    exact freshEvent.2.2.1 occurrence List.mem_cons_self
      (ReferenceWorkQueue.GraphEvent.taskSettlements_subsetIdentities events settled)
  have known : ∀ task ∈ result.work.tasks, ReferenceWorkQueue.TaskMatches work task := by
    intro task member
    obtain ⟨address, payload, same, known⟩ := matched.childTask_producer member
    exact ⟨⟨address, payload, some occurrence, same, known⟩, matched.childTask_groupsExact member⟩
  have childFresh : ∀ task ∈ result.work.tasks,
      task.occurrence ∉ occurrence :: ReferenceWorkQueue.GraphEvent.taskSettlements events := by
    intro task member settled
    rcases List.mem_cons.mp settled with current | earlier
    · exact matched.childTasks_not_success member (List.mem_cons.mpr (.inl current))
    · exact matched.childTasks_unsettled priorValid freshEvent member
        (ReferenceWorkQueue.GraphEvent.taskSettlements_subsetIdentities events earlier)
  change ((state.taskSuccess occurrence result).1.queue, (state.taskSuccess occurrence result).2.1)
    = queue.taskSuccess occurrence result
  cases found : queue.taskNode? occurrence with
  | none =>
      simp only [State.taskSuccess, ReferenceWorkQueue.State.taskSuccess, state, found]
  | some node =>
      exact State.taskSuccess_projection generated presence accounting occurrence result node found
        fresh known childFresh rfl
        (referencePrefix_taskSuccess_drainFrames generated events occurrence result valid accepted node found)

end GraphQL.IncrementalDelivery.AlternativeWorkQueue
