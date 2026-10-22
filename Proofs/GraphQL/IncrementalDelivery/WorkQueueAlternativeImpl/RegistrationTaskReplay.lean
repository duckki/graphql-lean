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
  let stored : State :=
    { state with queue := state.queue.putTaskNode { node with value := some result.value } }
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
  have links :=
    (accounting.links.putTaskNode { node with value := some result.value }).maybeIntegrateWork
    accounting.refs accounting.taskGroups result.work (some occurrence)
  have sound := storedSound.maybeIntegrateWork result.work (some occurrence)
  have matching := storedMatching.maybeIntegrateWork result.work known (some occurrence)
  have member : node.task ∈ prepared.tasks := by
    rw [ReferenceWorkQueue.State.maybeIntegrateWork_tasks_append]
    exact List.mem_append_left _ (accounting.started node (List.mem_of_find?_eq_some found))
  have same := (ReferenceWorkQueue.State.taskNode?_some found).2
  have owned := links.ownedExactlyBy sound matching member (same.symm ▸ fresh)
  rw [same] at owned
  have debt := counts.beginSettlement members
    (fun current included _ => owned current included) fresh
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
    (available : List (Occurrence × Nat) := [])
    : state.taskSuccess occurrence result available
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
            registered.2 [] available
        let drained := started.1.drainReadyGroups started.2.1 available
        (
          drained.1,
          released.2.1 ++ drained.2.1,
          [.adopt occurrence] ++ drained.2.2.1.flatMap CleanupTarget.effects,
          started.2.2 ++ drained.2.2.2
        ) := by
  simp only [State.taskSuccess, found]
  rfl

/-- The actual accepted task-success phase immediately before ready draining.
This is proof notation for the existing registration/owner/start calculation, not another
runtime pass or an output-driven cleanup observer.
-/
def taskSuccessReadyPhase (state : State) (occurrence : Occurrence)
    (result : ReferenceWorkQueue.TaskResult) (node : ReferenceWorkQueue.TaskNode)
    (available : List (Occurrence × Nat) := [])
    : State
      × List WorkQueueEvent
      × List CleanupTarget
      × List ReferenceWorkQueue.GroupFailureEvent :=
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
    ({ registered.1 with queue := released.1 }).startNewWork released.2.2 registered.2 []
      available
  (active.1, released.2.1, active.2.1, active.2.2)

/-- The real pre-drain phase preserves the interruption guard. -/
theorem taskSuccessReadyPhase_stopped (state : State) (occurrence : Occurrence)
    (result : ReferenceWorkQueue.TaskResult) (node : ReferenceWorkQueue.TaskNode)
    (available : List (Occurrence × Nat) := [])
    : (taskSuccessReadyPhase state occurrence result node available).1.stopped
      = state.stopped := by
  unfold taskSuccessReadyPhase
  rw [State.startNewWork_stopped (available := available)]
  exact State.maybeIntegrateWork_stopped
    { state with queue := state.queue.putTaskNode { node with value := some result.value } }
    result.work (some occurrence)

/-- Reference owner-fold result immediately before cache-aware child activation. -/
def referenceTaskSuccessReleased (queue : ReferenceWorkQueue.State)
    (occurrence : Occurrence) (result : ReferenceWorkQueue.TaskResult)
    (node : ReferenceWorkQueue.TaskNode)
    : ReferenceWorkQueue.State × List WorkQueueEvent × ReferenceWorkQueue.NewWork :=
  let prepared :=
    ((queue.putTaskNode { node with value := some result.value }).maybeIntegrateWork
      result.work (some occurrence)).1
  node.task.groups.foldl ReferenceWorkQueue.successGroupStep (prepared, [], {})

/-- Eager completion of the delayed settlement phase is the exact reference owner fold.
Witness: scope registration installs the same permanent work, and successful-settlement
debt prevents fresh child tasks from being flushed before their delayed activation.
No startup, cache exposure, or desired final output premise is used.
-/
theorem State.taskSuccess_settlementProjection {state : State} {work : Work}
    {settled : List Occurrence} (generated : ReferenceWorkQueue.ExecutedWork work)
    (present : state.queue.RootGroupsPresent)
    (accounting : state.queue.PendingAccounting work settled) (occurrence : Occurrence)
    (result : ReferenceWorkQueue.TaskResult) (node : ReferenceWorkQueue.TaskNode)
    (found : state.queue.taskNode? occurrence = some node) (fresh : occurrence ∉ settled)
    (known : ∀ task ∈ result.work.tasks, ReferenceWorkQueue.TaskMatches work task)
    (childFresh : ∀ task ∈ result.work.tasks, task.occurrence ∉ occurrence :: settled)
    : let stored : State :=
        {
          state with
            queue := state.queue.putTaskNode { node with value := some result.value }
        }
      let registered := stored.maybeIntegrateWork result.work (some occurrence)
      let released :=
        node.task.groups.foldl ReferenceWorkQueue.successGroupStep
          (registered.1.queue, [], {})
      (activateRegisteredTasks released.1 registered.2.activeTasks, released.2)
      = referenceTaskSuccessReleased state.queue occurrence result node := by
  intro stored registered released
  have storedFound := ReferenceWorkQueue.State.putTaskNode_value_lookup found result.value
  have storedReady : (stored.queue.taskNode? occurrence).isSome = true :=
    congrArg Option.isSome storedFound
  have complete := stored.maybeIntegrateWork_complete result.work present (some occurrence)
    (by intro candidate same; cases Option.some.inj same; exact storedReady)
  dsimp only at complete
  have unique := accounting.matching.contributorsNodup generated
    (accounting.started node (List.mem_of_find?_eq_some found))
  have keys := stored.maybeIntegrateWork_groupKeysUnique accounting.refs result.work
    (some occurrence)
  have debt := state.taskSuccess_registrationDebt present accounting occurrence result
    node found fresh known
  have activeFresh
      : ∀ task ∈ registered.2.activeTasks, task.occurrence ∉ occurrence :: settled := by
    intro task member
    exact childFresh task
      (stored.maybeIntegrateWork_activeTasks result.work (some occurrence) member)
  have commute := successGroupFold_activateRegisteredTasks (occurrence :: settled)
    registered.2.activeTasks activeFresh node.task.groups unique
    (registered.1.queue, [], {}) keys debt
  unfold completeSuccessAcc at commute
  dsimp only at commute
  rw [complete.1] at commute
  exact commute.symm

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
    (startupFrames
      : ∃ parents,
          (referenceTaskSuccessReleased state.queue occurrence result
            node).1.TaskOwnerFrame
            work
          ∧ (referenceTaskSuccessReleased state.queue occurrence result
              node).1.RemovalForest
              parents)
    (available : List (Occurrence × Nat) := [])
    (unavailable
      : ∀ task ∈ result.work.tasks, task.occurrence ∉ available.map Prod.fst := by
        intro task _ member; cases member)
    : let active := taskSuccessReadyPhase state occurrence result node available
      let integrated :=
        (ReferenceWorkQueue.State.maybeIntegrateWork
          (state.queue.putTaskNode { node with value := some result.value })
          result.work (some occurrence)).1
      let released :=
        node.task.groups.foldl ReferenceWorkQueue.successGroupStep (integrated, [], {})
      (active.1.queue, active.2.1, active.2.2.2)
      = (
        referenceTaskSuccessReady state.queue occurrence result node available,
        released.2.1,
        (released.1.startNewWork released.2.2 available).2
      ) := by

  let stored : State :=
    { state with queue := state.queue.putTaskNode { node with value := some result.value } }
  let registered := stored.maybeIntegrateWork result.work (some occurrence)
  let released :=
    node.task.groups.foldl ReferenceWorkQueue.successGroupStep (registered.1.queue, [], {})
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
  have keys :=
    stored.maybeIntegrateWork_groupKeysUnique accounting.refs result.work (some occurrence)
  have debt := state.taskSuccess_registrationDebt present accounting occurrence result
    node found fresh known
  have activeFresh
      : ∀ task ∈ registered.2.activeTasks, task.occurrence ∉ occurrence :: settled := by
    intro task member
    exact childFresh task
      (stored.maybeIntegrateWork_activeTasks result.work (some occurrence) member)
  have commute := successGroupFold_activateRegisteredTasks (occurrence :: settled)
    registered.2.activeTasks activeFresh node.task.groups unique
    (registered.1.queue, [], {}) keys debt
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
    exact List.mem_append_right _
      (stored.maybeIntegrateWork_activeTasks result.work (some occurrence) member)
  have actualStarts :=
    activateRegisteredTasks_eq_startTasks releasedMatch registered.2.activeTasks members
  unfold completeSuccessAcc at commute
  dsimp only at commute
  rw [complete.1] at commute
  have referenceQueue := congrArg Prod.fst commute
  have referenceEvents := congrArg (fun acc : ReferenceWorkQueue.State × List WorkQueueEvent
    × ReferenceWorkQueue.NewWork => acc.2.1) commute
  have referenceRoots := congrArg (fun acc : ReferenceWorkQueue.State × List WorkQueueEvent
    × ReferenceWorkQueue.NewWork => acc.2.2) commute
  dsimp only at referenceQueue referenceEvents referenceRoots
  have startsEq := reference_startTasks_eq_of_unavailable released.1
    registered.2.activeTasks available (fun task member => unavailable task
      (stored.maybeIntegrateWork_activeTasks result.work (some occurrence) member))
  have preStartup : (registered.2.activeTasks.foldl
      (fun current task => current.startTask task.occurrence available) released.1)
      = (referenceTaskSuccessReleased state.queue occurrence result node).1 := by
    rw [startsEq, ← actualStarts, ← referenceQueue]
    rfl
  obtain ⟨parents, frame, forest⟩ := startupFrames
  have activeFrame : (registered.2.activeTasks.foldl
      (fun current task => current.startTask task.occurrence available)
      released.1).TaskOwnerFrame work := by
    rw [preStartup]
    exact frame
  have activeForest : (registered.2.activeTasks.foldl
      (fun current task => current.startTask task.occurrence available) released.1).RemovalForest
          parents := by
    rw [preStartup]
    exact forest
  have ready := State.startNewWork_projects ({ registered.1 with queue := released.1 })
    released.2.2 registered.2 []
    ((stored.maybeIntegrateWork_stopped result.work (some occurrence)).trans running)
    available activeFrame activeForest
  have readyQueue := congrArg Prod.fst ready
  have readyNotices := congrArg Prod.snd ready
  dsimp only at readyQueue readyNotices
  let active := ({ registered.1 with queue := released.1 }).startNewWork
    released.2.2 registered.2 [] available
  have activeQueue
      : active.1.queue
        = referenceTaskSuccessReady state.queue occurrence result node available := by
    rw [readyQueue, startsEq, ← actualStarts, ← referenceQueue, ← referenceRoots]
    rfl
  refine Prod.ext activeQueue (Prod.ext referenceEvents.symm ?_)
  change active.2.2 = _
  rw [readyNotices, startsEq, ← actualStarts, ← referenceQueue, ← referenceRoots]

private theorem reference_keys_of_cache_eq {first second : ReferenceWorkQueue.State}
    (available : List (Occurrence × Nat))
    (same : first.cacheTaskFailures available = second.cacheTaskFailures available)
    (unique : second.TaskNodeKeysUnique)
    : first.TaskNodeKeysUnique := by
  have exposed := unique.cacheTaskFailures available
  rw [← same] at exposed
  simpa only [ReferenceWorkQueue.State.TaskNodeKeysUnique,
    ReferenceWorkQueue.State.cacheTaskFailures_taskOccurrences] using exposed

private theorem reference_forest_of_cache_eq {first second : ReferenceWorkQueue.State}
    {parents : Nat → NodeRefs} (available : List (Occurrence × Nat))
    (same : first.cacheTaskFailures available = second.cacheTaskFailures available)
    (forest : second.RemovalForest parents)
    : first.RemovalForest parents := by
  have groups := congrArg ReferenceWorkQueue.State.groupNodes same
  simp only [ReferenceWorkQueue.State.cacheTaskFailures_groupNodes] at groups
  apply forest.of_subset
  rw [groups]
  exact List.Subset.refl _

/-- Cache-aware delayed startup preserves the reference task-success release phase.
Witness: exact eager settlement completion identifies the pre-startup reference queue;
cache/start congruence supplies the concrete activated relation, and ownership/forest
certificates transfer through it before fused cleanup. Both output channels remain exact.
-/
theorem State.taskSuccess_readyCacheProjection {state : State} {work : Work}
    {settled : List Occurrence} (generated : ReferenceWorkQueue.ExecutedWork work)
    (present : state.queue.RootGroupsPresent)
    (accounting : state.queue.PendingAccounting work settled)
    (unique : state.queue.TaskNodeKeysUnique) (occurrence : Occurrence)
    (result : ReferenceWorkQueue.TaskResult) (node : ReferenceWorkQueue.TaskNode)
    (found : state.queue.taskNode? occurrence = some node) (fresh : occurrence ∉ settled)
    (known : ∀ task ∈ result.work.tasks, ReferenceWorkQueue.TaskMatches work task)
    (childFresh : ∀ task ∈ result.work.tasks, task.occurrence ∉ occurrence :: settled)
    (running : state.stopped = false) (available : List (Occurrence × Nat))
    (startupFrames
      : ∃ parents,
          (referenceTaskSuccessReleased state.queue occurrence result
            node).1.TaskOwnerFrame
            work
          ∧ (referenceTaskSuccessReleased state.queue occurrence result
              node).1.RemovalForest
              parents)
    : let active := taskSuccessReadyPhase state occurrence result node available
      let released := referenceTaskSuccessReleased state.queue occurrence result node
      let reference := released.1.startNewWork released.2.2 available
      (active.1.queue.cacheTaskFailures available, active.2.1, active.2.2.2)
      = (reference.1.cacheTaskFailures available, released.2.1, reference.2) := by
  let stored : State :=
    { state with queue := state.queue.putTaskNode { node with value := some result.value } }
  let registered := stored.maybeIntegrateWork result.work (some occurrence)
  let released := node.task.groups.foldl ReferenceWorkQueue.successGroupStep
    (registered.1.queue, [], {})
  let reference := referenceTaskSuccessReleased state.queue occurrence result node
  have complete := state.taskSuccess_settlementProjection generated present accounting
    occurrence result node found fresh known childFresh
  change (activateRegisteredTasks released.1 registered.2.activeTasks, released.2) = reference
    at complete
  have referenceKeys : reference.1.TaskNodeKeysUnique :=
    (((unique.putTaskNode _).maybeIntegrateWork result.work (some occurrence)).successGroupFold
      node.task.groups)
  have initialKeys : released.1.TaskNodeKeysUnique := by
    have activatedKeys := referenceKeys
    rw [← congrArg Prod.fst complete] at activatedKeys
    exact activatedKeys.sublist ((activateRegisteredTasks_taskNodes_sublist _ _).map _)
  have registeredMatch := stored.maybeIntegrateWork_registeredTasksMatch accounting.matching
    result.work known (some occurrence)
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
    exact List.mem_append_right _
      (stored.maybeIntegrateWork_activeTasks result.work (some occurrence) member)
  have actualStarts := activateRegisteredTasks_eq_startTasks releasedMatch
    registered.2.activeTasks members
  have exposed := initialKeys.startTasks_cache_congr initialKeys available rfl
    (registered.2.activeTasks.map ReferenceWorkQueue.Task.occurrence)
  simp only [List.foldl_map] at exposed
  have completeQueue := congrArg Prod.fst complete
  dsimp only at completeQueue
  rw [← actualStarts, completeQueue] at exposed
  have activatedKeys := reference_keys_of_cache_eq available exposed referenceKeys
  obtain ⟨parents, frame, forest⟩ := startupFrames
  have actualFrame := ReferenceWorkQueue.State.TaskOwnerFrame.of_cacheTaskFailures_eq
    activatedKeys available exposed frame
  have actualForest := reference_forest_of_cache_eq available exposed forest
  have startup := State.startNewWork_projects_after_cache
    ({ registered.1 with queue := released.1 }) released.2.2 registered.2 []
    ((stored.maybeIntegrateWork_stopped result.work (some occurrence)).trans running)
    available initialKeys reference.1 referenceKeys exposed actualFrame actualForest
  have queue := congrArg Prod.fst startup
  have notices := congrArg Prod.snd startup
  have values := congrArg (fun pair : ReferenceWorkQueue.State × List WorkQueueEvent
    × ReferenceWorkQueue.NewWork => pair.2.1) complete
  have roots := congrArg (fun pair : ReferenceWorkQueue.State × List WorkQueueEvent
    × ReferenceWorkQueue.NewWork => pair.2.2) complete
  let active := ({ registered.1 with queue := released.1 }).startNewWork
    released.2.2 registered.2 [] available
  change (active.1.queue.cacheTaskFailures available, released.2.1, active.2.2)
    = ((reference.1.startNewWork reference.2.2 available).1.cacheTaskFailures available,
      reference.2.1, (reference.1.startNewWork reference.2.2 available).2)
  dsimp only [active]
  rw [roots] at queue notices ⊢
  exact Prod.ext queue (Prod.ext values notices)

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
    (startupFrames
      : ∃ parents,
          (referenceTaskSuccessReleased state.queue occurrence result
            node).1.TaskOwnerFrame
            work
          ∧ (referenceTaskSuccessReleased state.queue occurrence result
              node).1.RemovalForest
              parents)
    (frames
      : ∃ parents,
          (referenceTaskSuccessReady state.queue occurrence result node).TaskOwnerFrame
            work
          ∧ (referenceTaskSuccessReady state.queue occurrence result node).RemovalForest
              parents)
    : (
        (state.taskSuccess occurrence result).1.queue,
        (state.taskSuccess occurrence result).2.1,
        (state.taskSuccess occurrence result).2.2.2
      )
      = state.queue.taskSuccess occurrence result := by
  rw [state.taskSuccess_eq occurrence result node found,
    ReferenceWorkQueue.State.taskSuccess_eq occurrence result node found]
  let active := taskSuccessReadyPhase state occurrence result node
  have phase := state.taskSuccess_readyProjection generated present accounting
    occurrence result node found fresh known childFresh running startupFrames
  have activeQueue
      : active.1.queue = referenceTaskSuccessReady state.queue occurrence result node :=
    congrArg Prod.fst phase
  have activeRunning : active.1.stopped = false :=
    (taskSuccessReadyPhase_stopped state occurrence result node).trans running
  obtain ⟨parents, frame, forest⟩ := frames
  have activeFrame : active.1.queue.TaskOwnerFrame work := by rw [activeQueue]; exact frame
  have activeForest : active.1.queue.RemovalForest parents := by rw [activeQueue]; exact forest
  have drain := active.1.drainReadyGroups_projection activeRunning activeFrame activeForest
    active.2.2.1
  rw [activeQueue] at drain
  let released := referenceTaskSuccessReleased state.queue occurrence result node
  have wirePrefix : active.2.1 = released.2.1 := congrArg (fun value => value.2.1) phase
  have notices : active.2.2.2 = (released.1.startNewWork released.2.2).2 :=
    congrArg (fun value => value.2.2) phase
  change ((active.1.drainReadyGroups active.2.2.1).1.queue,
      active.2.1 ++ (active.1.drainReadyGroups active.2.2.1).2.1,
      active.2.2.2 ++ (active.1.drainReadyGroups active.2.2.1).2.2.2) = _
  have combined := congrArg
    (fun value : ReferenceWorkQueue.State × List WorkQueueEvent
        × List ReferenceWorkQueue.GroupFailureEvent =>
      (value.1, active.2.1 ++ value.2.1, active.2.2.2 ++ value.2.2)) drain
  exact combined.trans (by rw [wirePrefix, notices]; rfl)

/-- Task success has exact residual correspondence when its fresh children are unavailable.
Witness: only newly active child starts could expose rejections earlier than eager scope
completion. Their absence from the snapshot removes that difference before shared startup.
-/
theorem State.taskSuccess_projection_of_unavailableChildren {state : State} {work : Work}
    {settled : List Occurrence} (generated : ReferenceWorkQueue.ExecutedWork work)
    (present : state.queue.RootGroupsPresent)
    (accounting : state.queue.PendingAccounting work settled) (occurrence : Occurrence)
    (result : ReferenceWorkQueue.TaskResult) (node : ReferenceWorkQueue.TaskNode)
    (found : state.queue.taskNode? occurrence = some node) (fresh : occurrence ∉ settled)
    (known : ∀ task ∈ result.work.tasks, ReferenceWorkQueue.TaskMatches work task)
    (childFresh : ∀ task ∈ result.work.tasks, task.occurrence ∉ occurrence :: settled)
    (running : state.stopped = false) (available : List (Occurrence × Nat))
    (unavailable : ∀ task ∈ result.work.tasks, task.occurrence ∉ available.map Prod.fst)
    (startupFrames
      : ∃ parents,
          (referenceTaskSuccessReleased state.queue occurrence result
            node).1.TaskOwnerFrame
            work
          ∧ (referenceTaskSuccessReleased state.queue occurrence result
              node).1.RemovalForest
              parents)
    : (
        (state.taskSuccess occurrence result available).1.queue,
        (state.taskSuccess occurrence result available).2.1,
        (state.taskSuccess occurrence result available).2.2.2
      )
      = state.queue.taskSuccess occurrence result available := by
  let active := taskSuccessReadyPhase state occurrence result node available
  let released := referenceTaskSuccessReleased state.queue occurrence result node
  let reference := released.1.startNewWork released.2.2 available
  have phase := state.taskSuccess_readyProjection generated present accounting occurrence result
    node found fresh known childFresh running startupFrames available unavailable
  have activeQueue : active.1.queue = reference.1 := congrArg Prod.fst phase
  have wirePrefix : active.2.1 = released.2.1 := congrArg (fun value => value.2.1) phase
  have notices : active.2.2.2 = reference.2 := congrArg (fun value => value.2.2) phase
  obtain ⟨parents, frame, forest⟩ := startupFrames
  have referenceFrame : reference.1.TaskOwnerFrame work := frame.startNewWork released.2.2 available
  have referenceForest : reference.1.RemovalForest parents :=
    forest.startNewWork released.2.2 available
  have actualFrame : active.1.queue.TaskOwnerFrame work := by rw [activeQueue]; exact referenceFrame
  have actualForest : active.1.queue.RemovalForest parents := by
    rw [activeQueue]; exact referenceForest
  have activeRunning := (taskSuccessReadyPhase_stopped state occurrence result node available
    ).trans running
  have drain := active.1.drainReadyGroups_projection activeRunning actualFrame actualForest
    active.2.2.1 available
  rw [activeQueue] at drain
  rw [state.taskSuccess_eq occurrence result node found available,
    ReferenceWorkQueue.State.taskSuccess_eq occurrence result node found available]
  change ((active.1.drainReadyGroups active.2.2.1 available).1.queue,
      active.2.1 ++ (active.1.drainReadyGroups active.2.2.1 available).2.1,
      active.2.2.2 ++ (active.1.drainReadyGroups active.2.2.1 available).2.2.2) = _
  have combined := congrArg
    (fun value : ReferenceWorkQueue.State × List WorkQueueEvent
        × List ReferenceWorkQueue.GroupFailureEvent =>
      (value.1, active.2.1 ++ value.2.1, active.2.2.2 ++ value.2.2)) drain
  exact combined.trans (by rw [wirePrefix, notices]; rfl)

/-- Actual cache-aware task-success handlers agree after common exposure and in both outputs.
Witness: eager settlement completion, cache-aware release startup and fused draining compose
at their actual phase boundaries. Concrete ownership/forest certificates transfer through
the exposed-state relation; no desired output or conformance premise supplies them.
-/
theorem State.taskSuccess_cacheProjection {state : State} {work : Work}
    {settled : List Occurrence} (generated : ReferenceWorkQueue.ExecutedWork work)
    (present : state.queue.RootGroupsPresent)
    (accounting : state.queue.PendingAccounting work settled)
    (unique : state.queue.TaskNodeKeysUnique) (occurrence : Occurrence)
    (result : ReferenceWorkQueue.TaskResult) (node : ReferenceWorkQueue.TaskNode)
    (found : state.queue.taskNode? occurrence = some node) (fresh : occurrence ∉ settled)
    (known : ∀ task ∈ result.work.tasks, ReferenceWorkQueue.TaskMatches work task)
    (childFresh : ∀ task ∈ result.work.tasks, task.occurrence ∉ occurrence :: settled)
    (running : state.stopped = false) (available : List (Occurrence × Nat))
    (startupFrames
      : ∃ parents,
          (referenceTaskSuccessReleased state.queue occurrence result
            node).1.TaskOwnerFrame
            work
          ∧ (referenceTaskSuccessReleased state.queue occurrence result
              node).1.RemovalForest
              parents)
    : (
        (state.taskSuccess occurrence result available).1.queue.cacheTaskFailures
          available,
        (state.taskSuccess occurrence result available).2.1,
        (state.taskSuccess occurrence result available).2.2.2
      )
      = (
        (state.queue.taskSuccess occurrence result available).1.cacheTaskFailures
          available,
        (state.queue.taskSuccess occurrence result available).2
      ) := by
  let active := taskSuccessReadyPhase state occurrence result node available
  let released := referenceTaskSuccessReleased state.queue occurrence result node
  let reference := released.1.startNewWork released.2.2 available
  have phase := state.taskSuccess_readyCacheProjection generated present accounting unique
    occurrence result node found fresh known childFresh running available startupFrames
  have activeQueue : active.1.queue.cacheTaskFailures available
      = reference.1.cacheTaskFailures available := congrArg Prod.fst phase
  have wirePrefix : active.2.1 = released.2.1 := congrArg (fun value => value.2.1) phase
  have notices : active.2.2.2 = reference.2 := congrArg (fun value => value.2.2) phase
  have releasedKeys : released.1.TaskNodeKeysUnique :=
    (((unique.putTaskNode _).maybeIntegrateWork result.work (some occurrence)).successGroupFold
      node.task.groups)
  have referenceKeys : reference.1.TaskNodeKeysUnique :=
    releasedKeys.startNewWork released.2.2 available
  have activeKeys := reference_keys_of_cache_eq available activeQueue referenceKeys
  obtain ⟨parents, frame, forest⟩ := startupFrames
  have referenceFrame : reference.1.TaskOwnerFrame work :=
    frame.startNewWork released.2.2 available
  have referenceForest : reference.1.RemovalForest parents :=
    forest.startNewWork released.2.2 available
  have activeFrame := ReferenceWorkQueue.State.TaskOwnerFrame.of_cacheTaskFailures_eq
    activeKeys available activeQueue referenceFrame
  have activeForest := reference_forest_of_cache_eq available activeQueue referenceForest
  have activeRunning : active.1.stopped = false :=
    (taskSuccessReadyPhase_stopped state occurrence result node available).trans running
  have drain := active.1.drainReadyGroups_projects_after_cache
    activeRunning activeFrame activeForest active.2.2.1 available activeKeys reference.1
    referenceKeys activeQueue
  rw [state.taskSuccess_eq occurrence result node found available,
    ReferenceWorkQueue.State.taskSuccess_eq occurrence result node found available]
  change (((active.1.drainReadyGroups active.2.2.1 available).1.queue).cacheTaskFailures available,
      active.2.1 ++ (active.1.drainReadyGroups active.2.2.1 available).2.1,
      active.2.2.2 ++ (active.1.drainReadyGroups active.2.2.1 available).2.2.2)
    = ((reference.1.drainReadyGroups available).1.cacheTaskFailures available,
      released.2.1 ++ (reference.1.drainReadyGroups available).2.1,
      reference.2 ++ (reference.1.drainReadyGroups available).2.2)
  have combined := congrArg
    (fun value : ReferenceWorkQueue.State × List WorkQueueEvent
        × List ReferenceWorkQueue.GroupFailureEvent =>
      (value.1, active.2.1 ++ value.2.1, active.2.2.2 ++ value.2.2)) drain
  exact combined.trans (by rw [wirePrefix, notices])

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
      : ReferenceWorkQueue.State.eventsStarted []
          (ReferenceWorkQueue.State.initialize
            (ReferenceWorkQueue.Work.fromExecution work)) events
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
    ReferenceWorkQueue.createWorkQueue_pendingAccounting work generated.declarations
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
  exact congrArg Prod.fst
    (State.taskSuccess_readyProjection (state := state) generated presence accounting
      occurrence result node found fresh known childFresh rfl
      (referencePrefix_taskSuccess_startFrames generated events occurrence result valid
        accepted node found))

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
      : ReferenceWorkQueue.State.eventsStarted []
          (ReferenceWorkQueue.State.initialize
            (ReferenceWorkQueue.Work.fromExecution work)) events
        = true)
    : let queue :=
        (ReferenceWorkQueue.State.initialize
          (ReferenceWorkQueue.Work.fromExecution work)).replayGraphEvents
          events
      let alternative := ({ queue } : State).taskSuccess occurrence result
      (alternative.1.queue, alternative.2.1, alternative.2.2.2)
      = queue.taskSuccess occurrence result := by
  obtain ⟨priorValid, matched, freshEvent⟩ := ReferenceWorkQueue.validGraphEvents_last valid
  let initial := ReferenceWorkQueue.State.initialize (ReferenceWorkQueue.Work.fromExecution work)
  let queue := initial.replayGraphEvents events
  let state : State := { queue }
  have initialAccounting : initial.PendingAccounting work
      (ReferenceWorkQueue.GraphEvent.taskSettlements []) :=
    ReferenceWorkQueue.createWorkQueue_pendingAccounting work generated.declarations
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
  change ((state.taskSuccess occurrence result).1.queue,
      (state.taskSuccess occurrence result).2.1, (state.taskSuccess occurrence result).2.2.2)
    = queue.taskSuccess occurrence result
  cases found : queue.taskNode? occurrence with
  | none =>
      simp only [State.taskSuccess, ReferenceWorkQueue.State.taskSuccess, state, found]
  | some node =>
      exact State.taskSuccess_projection generated presence accounting occurrence result node found
        fresh known childFresh rfl
        (referencePrefix_taskSuccess_startFrames generated events occurrence result valid
          accepted node found)
        (referencePrefix_taskSuccess_drainFrames generated events occurrence result valid
          accepted node found)

end GraphQL.IncrementalDelivery.AlternativeWorkQueue
