import GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PendingCounts
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RootLinks
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ActiveLinks
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PendingPreservation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.UnsettledMemberships

/-! Registration-phase projection to the reference accounting kernel.

Registration deliberately does not start task nodes. Erasing the task-node store gives a
common accounting projection, not a replay invariant: stored values, held child streams,
activation and accepted settlements still require a separate bridge. Pending-count and
membership arguments can already be reused without assuming that bridge.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics (Occurrence)

-----------------------------------------------------------------------------------------
-- Phase-local accounting projection
-----------------------------------------------------------------------------------------

/-- Erase the whole task-node store: starts, stored values and held child-stream links.
Every other kernel field is retained. This proof-only accounting projection is used during
registration, not as a dispatch, publication or host-ownership invariant.
-/
def registrationCore (queue : ReferenceWorkQueue.State) : ReferenceWorkQueue.State :=
  { queue with taskNodes := [] }

/-- Proof-facing owner step shared by the two registration-loop presentations. -/
def registerOwner (task : ReferenceWorkQueue.Task)
    (queue : ReferenceWorkQueue.State) (group : Execution.DeliveryNode)
    : ReferenceWorkQueue.State :=
  match queue.groupNode? group.ref with
  | none => queue
  | some node =>
      if node.tasks.contains task.occurrence then
        queue
      else
        queue.putGroupNode
          {
            node with
              tasks := node.tasks ++ [task.occurrence], pending := node.pending + 1
          }

/-- Proof-facing spelling of the public loop, exposing its Boolean accumulators. -/
def classifyOwner (task : ReferenceWorkQueue.Task)
    (acc : ReferenceWorkQueue.State × Bool × Bool) (group : Execution.DeliveryNode)
    : ReferenceWorkQueue.State × Bool × Bool :=
  match acc.1.groupNode? group.ref with
  | none => acc
  | some node =>
      let queue :=
        if node.tasks.contains task.occurrence then
          acc.1
        else
          acc.1.putGroupNode
            {
              node with
                tasks := node.tasks ++ [task.occurrence], pending := node.pending + 1
            }
      (queue, true, acc.2.2 || queue.rootGroups.contains group.ref)

/-- Forget the classification flags for one owner-loop iteration. -/
theorem classifyOwner_core (task : ReferenceWorkQueue.Task)
    (acc : ReferenceWorkQueue.State × Bool × Bool) (group : Execution.DeliveryNode)
    : (classifyOwner task acc group).1 = registerOwner task acc.1 group := by
  unfold classifyOwner registerOwner
  split <;> rfl

/-- Forget the classification flags for the complete owner traversal. -/
theorem classifyOwners_core (task : ReferenceWorkQueue.Task)
    (owners : List Execution.DeliveryNode) (acc : ReferenceWorkQueue.State × Bool × Bool)
    : (owners.foldl (classifyOwner task) acc).1
      = owners.foldl (registerOwner task) acc.1 := by
  exact (List.foldl_hom (l := owners) (init := acc)
    (fun current : ReferenceWorkQueue.State × Bool × Bool => current.1)
    (fun current group => (classifyOwner_core task current group).symm)).symm

/-- An owner-loop iteration does not activate a root. -/
theorem registerOwner_rootGroups (task : ReferenceWorkQueue.Task)
    (queue : ReferenceWorkQueue.State) (group : Execution.DeliveryNode)
    : (registerOwner task queue group).rootGroups = queue.rootGroups := by
  unfold registerOwner
  split
  · rfl
  · split <;> rfl

/-- The complete owner traversal leaves active roots unchanged. -/
theorem registerOwners_rootGroups (task : ReferenceWorkQueue.Task)
    (groups : List Execution.DeliveryNode) (queue : ReferenceWorkQueue.State)
    : (groups.foldl (registerOwner task) queue).rootGroups = queue.rootGroups := by
  induction groups generalizing queue with
  | nil => rfl
  | cons group rest ih => rw [List.foldl_cons, ih, registerOwner_rootGroups]

/-- The alternative owner loop is exactly the old membership/counter update.
Witness: forget the two Boolean accumulators at each owner-loop step. The only old
update not retained by this projection is eager task-node insertion.
-/
theorem State.addTask_registrationCore (state : State) (task : ReferenceWorkQueue.Task)
    : registrationCore (state.addTask task).1.queue
      = registrationCore (state.queue.addTask task) := by
  let registered := { state.queue with tasks := state.queue.tasks ++ [task] }
  have fold := classifyOwners_core task task.groups (registered, false, false)
  change registrationCore
      (task.groups.foldl (classifyOwner task) (registered, false, false)).1
    = registrationCore
      (if task.groups.any (fun group =>
          (task.groups.foldl (registerOwner task) registered).rootGroups.contains group.ref)
        && ((task.groups.foldl (registerOwner task) registered).taskNode?
          task.occurrence).isNone then
        { task.groups.foldl (registerOwner task) registered with
          taskNodes := (task.groups.foldl (registerOwner task) registered).taskNodes ++ [{ task }] }
      else task.groups.foldl (registerOwner task) registered)
  rw [fold]
  split <;> rfl

/-- Registration's queue is the shared owner fold, without eager activation. -/
theorem State.addTask_ownerState (state : State) (task : ReferenceWorkQueue.Task)
    : (state.addTask task).1.queue
      = task.groups.foldl (registerOwner task)
          { state.queue with tasks := state.queue.tasks ++ [task] } :=
  classifyOwners_core task task.groups
    ({ state.queue with tasks := state.queue.tasks ++ [task] }, false, false)

/-- Registering a task never starts or alters a computation node.
Witness: the owner loop changes only group memberships and pending counters.
-/
theorem State.addTask_taskNodes (state : State) (task : ReferenceWorkQueue.Task)
    : (state.addTask task).1.queue.taskNodes = state.queue.taskNodes := by
  have step (acc : ReferenceWorkQueue.State × Bool × Bool) (group : Execution.DeliveryNode)
      : (classifyOwner task acc group).1.taskNodes = acc.1.taskNodes := by
    unfold classifyOwner
    split
    · rfl
    · split <;> rfl
  have loop (owners : List Execution.DeliveryNode)
      (acc : ReferenceWorkQueue.State × Bool × Bool)
      : (owners.foldl (classifyOwner task) acc).1.taskNodes = acc.1.taskNodes := by
    induction owners generalizing acc with
    | nil => rfl
    | cons group rest ih => rw [List.foldl_cons, ih, step]
  exact loop task.groups
    ({ state.queue with tasks := state.queue.tasks ++ [task] }, false, false)

/-- The old root-preservation theorem applies to the new registration loop.
Witness: project both sides of the accounting correspondence to their roots.
-/
theorem State.addTask_rootGroups (state : State) (task : ReferenceWorkQueue.Task)
    : (state.addTask task).1.queue.rootGroups = state.queue.rootGroups := by
  have projected := congrArg ReferenceWorkQueue.State.rootGroups
    (state.addTask_registrationCore task)
  exact projected.trans (ReferenceWorkQueue.State.addTask_rootGroups state.queue task)

/-- The catalogue update is unchanged; task projections are not additional registrations.
Witness: project the correspondence, then reuse the old append theorem.
-/
theorem State.addTask_tasks (state : State) (task : ReferenceWorkQueue.Task)
    : (state.addTask task).1.queue.tasks = state.queue.tasks ++ [task] := by
  have projected := congrArg ReferenceWorkQueue.State.tasks
    (state.addTask_registrationCore task)
  exact projected.trans (ReferenceWorkQueue.State.addTask_tasks state.queue task)

/-- With no previously active roots, registration cannot classify a task as active.
Witness: the owner loop preserves roots and accumulates only false activity tests.
-/
theorem State.addTask_not_active_of_no_roots (state : State)
    (task : ReferenceWorkQueue.Task) (empty : state.queue.rootGroups = [])
    : (state.addTask task).2 ≠ .active := by
  have step (acc : ReferenceWorkQueue.State × Bool × Bool) (group : Execution.DeliveryNode)
      (roots : acc.1.rootGroups = []) (inactive : acc.2.2 = false)
      : (classifyOwner task acc group).1.rootGroups = []
        ∧ (classifyOwner task acc group).2.2 = false := by
    have unchanged := registerOwner_rootGroups task acc.1 group
    unfold classifyOwner
    cases found : acc.1.groupNode? group.ref with
    | none => exact ⟨roots, inactive⟩
    | some node =>
        have nextRoots : (registerOwner task acc.1 group).rootGroups = [] :=
          unchanged.trans roots
        have nextActive : (acc.2.2 || (registerOwner task acc.1 group).rootGroups.contains
            group.ref) = false := by simp only [nextRoots, inactive, List.contains_nil, Bool.or_self]
        simpa only [registerOwner, found] using And.intro nextRoots nextActive
  have loop (groups : List Execution.DeliveryNode) (acc : ReferenceWorkQueue.State × Bool × Bool)
      (roots : acc.1.rootGroups = []) (inactive : acc.2.2 = false)
      : (groups.foldl (classifyOwner task) acc).2.2 = false := by
    induction groups generalizing acc with
    | nil => exact inactive
    | cons group rest ih =>
        obtain ⟨nextRoots, nextInactive⟩ := step acc group roots inactive
        exact ih _ nextRoots nextInactive
  have inactive := loop task.groups
    ({ state.queue with tasks := state.queue.tasks ++ [task] }, false, false) empty rfl
  change (if (task.groups.foldl (classifyOwner task)
      ({ state.queue with tasks := state.queue.tasks ++ [task] }, false, false)).2.2 then
        .active
      else if (task.groups.foldl (classifyOwner task)
        ({ state.queue with tasks := state.queue.tasks ++ [task] }, false, false)).2.1 then
        .registered else .rejected) ≠ TaskRegistration.active
  rw [inactive]
  simp only [Bool.false_eq_true, ↓reduceIte]
  split <;> simp

/-- An accounting-core equality plus equality of started nodes is full state equality.
Witness: restore the one erased field; all other fields were preserved exactly.
-/
theorem registrationCore_ext {left right : ReferenceWorkQueue.State}
    (core : registrationCore left = registrationCore right)
    (nodes : left.taskNodes = right.taskNodes)
    : left = right := by
  calc
    left = { registrationCore left with taskNodes := left.taskNodes } := rfl
    _ = { registrationCore right with taskNodes := right.taskNodes } := by
      rw [core, nodes]
    _ = right := rfl

/-- Registration is fully equal before any roots have been activated.
Witness: the phase projection plus absence of the reference's eager-start branch.
Unlike arbitrary replay equality, this statement applies to every raw task.
-/
theorem State.addTask_eq_reference_of_no_roots (state : State)
    (task : ReferenceWorkQueue.Task) (empty : state.queue.rootGroups = [])
    : (state.addTask task).1.queue = state.queue.addTask task := by
  apply registrationCore_ext (state.addTask_registrationCore task)
  rw [state.addTask_taskNodes task]
  let registered := { state.queue with tasks := state.queue.tasks ++ [task] }
  let current := task.groups.foldl (registerOwner task) registered
  have roots : current.rootGroups = [] :=
    (registerOwners_rootGroups task task.groups registered).trans empty
  change state.queue.taskNodes =
    (if task.groups.any (fun group => current.rootGroups.contains group.ref)
        && (current.taskNode? task.occurrence).isNone then
      { current with taskNodes := current.taskNodes ++ [{ task }] } else current).taskNodes
  have inactive : task.groups.any (fun group => current.rootGroups.contains group.ref) = false := by
    simp [roots]
  rw [inactive]
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  have projected := state.addTask_taskNodes task
  have folded := classifyOwners_core task task.groups (registered, false, false)
  change (task.groups.foldl (classifyOwner task) (registered, false, false)).1.taskNodes
    = state.queue.taskNodes at projected
  rw [folded] at projected
  exact projected.symm

private theorem registerOwner_registrationCore (task : ReferenceWorkQueue.Task)
    (queue : ReferenceWorkQueue.State) (group : Execution.DeliveryNode)
    : registrationCore (registerOwner task queue group)
      = registerOwner task (registrationCore queue) group := by
  unfold registerOwner
  change registrationCore (match queue.groupNode? group.ref with
      | none => queue
      | some node => if node.tasks.contains task.occurrence then queue
          else queue.putGroupNode
            { node with tasks := node.tasks ++ [task.occurrence], pending := node.pending + 1 })
    = match queue.groupNode? group.ref with
      | none => registrationCore queue
      | some node => if node.tasks.contains task.occurrence then registrationCore queue
          else (registrationCore queue).putGroupNode
            { node with tasks := node.tasks ++ [task.occurrence], pending := node.pending + 1 }
  cases found : queue.groupNode? group.ref with
  | none => rfl
  | some node => simp only; split <;> rfl

private theorem addTask_registrationCore (queue : ReferenceWorkQueue.State)
    (task : ReferenceWorkQueue.Task)
    : registrationCore (queue.addTask task)
      = registrationCore ((registrationCore queue).addTask task) := by
  let registered := { queue with tasks := queue.tasks ++ [task] }
  have fold := (List.foldl_hom (l := task.groups) (init := registered) registrationCore
    (fun current group => (registerOwner_registrationCore task current group).symm)).symm
  have erase (before : ReferenceWorkQueue.State)
      : registrationCore (before.addTask task)
        = registrationCore (task.groups.foldl (registerOwner task)
          { before with tasks := before.tasks ++ [task] }) := by
    unfold ReferenceWorkQueue.State.addTask
    dsimp only
    split <;> rfl
  rw [erase, erase, fold]
  have stable := (List.foldl_hom (l := task.groups) (init := registrationCore registered)
    registrationCore
    (fun current group => (registerOwner_registrationCore task current group).symm)).symm
  simpa only [registrationCore] using stable.symm

private theorem addTask_registrationCore_congr {left right : ReferenceWorkQueue.State}
    (same : registrationCore left = registrationCore right)
    (task : ReferenceWorkQueue.Task)
    : registrationCore (left.addTask task) = registrationCore (right.addTask task) := by
  exact (addTask_registrationCore left task).trans
    ((congrArg (fun queue => registrationCore (queue.addTask task)) same).trans
      (addTask_registrationCore right task).symm)

private theorem addStreams_registrationCore (queue : ReferenceWorkQueue.State)
    (streams : List ReferenceWorkQueue.Stream) (parent : Option Occurrence)
    : registrationCore (queue.addStreams streams parent).1
      = registrationCore ((registrationCore queue).addStreams streams parent).1 := by
  cases parent with
  | none => rfl
  | some occurrence =>
      unfold ReferenceWorkQueue.State.addStreams
      dsimp only
      split <;> rfl

private theorem addStreams_registrationCore_congr {left right : ReferenceWorkQueue.State}
    (same : registrationCore left = registrationCore right)
    (streams : List ReferenceWorkQueue.Stream) (parent : Option Occurrence)
    : registrationCore (left.addStreams streams parent).1
      = registrationCore (right.addStreams streams parent).1 := by
  exact (addStreams_registrationCore left streams parent).trans
    ((congrArg (fun queue => registrationCore (queue.addStreams streams parent).1) same).trans
      (addStreams_registrationCore right streams parent).symm)

/-- Complete scope registration has exactly the reference accounting projection.
Witness: the shared group registration, projected task-fold correspondence, and stream
registration's independence from task nodes after erasure. This holds for raw work too;
it does not assert equality of started nodes or returned stream-release lists.
-/
theorem State.maybeIntegrateWork_registrationCore (state : State)
    (work : ReferenceWorkQueue.Work) (parent : Option Occurrence := none)
    : registrationCore (state.maybeIntegrateWork work parent).1.queue
      = registrationCore (state.queue.maybeIntegrateWork work parent).1 := by
  let step (acc : State × List ReferenceWorkQueue.Task × List ReferenceWorkQueue.Task)
      (task : ReferenceWorkQueue.Task)
      : State × List ReferenceWorkQueue.Task × List ReferenceWorkQueue.Task :=
    let next := acc.1.addTask task
    match next.2 with
    | .active => (next.1, acc.2.1 ++ [task], acc.2.2)
    | .registered => (next.1, acc.2.1, acc.2.2)
    | .rejected => (next.1, acc.2.1, acc.2.2 ++ [task])
  have loop (tasks : List ReferenceWorkQueue.Task)
      (acc : State × List ReferenceWorkQueue.Task × List ReferenceWorkQueue.Task)
      (queue : ReferenceWorkQueue.State) (same : registrationCore acc.1.queue = registrationCore queue)
      : registrationCore (tasks.foldl step acc).1.queue
        = registrationCore (tasks.foldl ReferenceWorkQueue.State.addTask queue) := by
    induction tasks generalizing acc queue with
    | nil => exact same
    | cons task rest ih =>
        have next : registrationCore (step acc task).1.queue
            = registrationCore (queue.addTask task) := by
          have projected := acc.1.addTask_registrationCore task
          have shared := addTask_registrationCore_congr same task
          have forget : (step acc task).1 = (acc.1.addTask task).1 := by
            unfold step
            dsimp only
            split <;> rfl
          rw [forget]
          exact projected.trans shared
        exact ih (step acc task) (queue.addTask task) next
  let initial : State × List ReferenceWorkQueue.Task × List ReferenceWorkQueue.Task :=
    ({ state with queue := (state.queue.addGroups work.groups).1 }, [], [])
  have same := loop work.tasks initial (state.queue.addGroups work.groups).1 rfl
  exact addStreams_registrationCore_congr same work.streams parent

-----------------------------------------------------------------------------------------
-- Reuse the reference registration invariants
-----------------------------------------------------------------------------------------

/-- New registration preserves exact counters under the old freshness condition.
Witness: the phase projection retains the complete group-node list, so the reference
pending-count proof applies unchanged; no delayed-start premise is needed.
-/
theorem State.addTask_pendingTracks {state : State} {settled : List Occurrence}
    (tracks : state.queue.PendingTracks settled) (task : ReferenceWorkQueue.Task)
    (fresh : task.occurrence ∉ settled)
    : (state.addTask task).1.queue.PendingTracks settled := by
  change (registrationCore (state.addTask task).1.queue).PendingTracks settled
  rw [state.addTask_registrationCore task]
  exact tracks.addTask task fresh

/-- Registration cannot undercount pending work, even on unrestricted raw task input.
Witness: transfer the reference lower-bound theorem through the accounting projection.
-/
theorem State.addTask_pendingBound {state : State} {eligible settled}
    (bounded : state.queue.PendingBound eligible settled) (task : ReferenceWorkQueue.Task)
    : (state.addTask task).1.queue.PendingBound eligible settled := by
  change (registrationCore (state.addTask task).1.queue).PendingBound eligible settled
  rw [state.addTask_registrationCore task]
  exact bounded.addTask task

/-- Registration preserves unique group keys without a new uniqueness proof.
Witness: group nodes are exactly the reference registration's nodes.
-/
theorem State.addTask_groupKeysUnique {state : State}
    (unique : state.queue.GroupRefsUnique) (task : ReferenceWorkQueue.Task)
    : (state.addTask task).1.queue.GroupRefsUnique := by
  change (registrationCore (state.addTask task).1.queue).GroupRefsUnique
  rw [state.addTask_registrationCore task]
  exact unique.addTask task

/-- A task appears only once in each owner, including repeated contributor references.
Witness: transfer the old membership-uniqueness theorem, rather than reprove the loop.
-/
theorem State.addTask_taskMembershipsUnique {state : State}
    (unique : state.queue.TaskMembershipsUnique) (task : ReferenceWorkQueue.Task)
    : (state.addTask task).1.queue.TaskMembershipsUnique := by
  change (registrationCore (state.addTask task).1.queue).TaskMembershipsUnique
  rw [state.addTask_registrationCore task]
  exact unique.addTask task

/-- The newly registered task is linked to all surviving contributor nodes.
Witness: the reference link-completeness result sees the same projected group nodes.
-/
theorem State.addTask_links (state : State) (unique : state.queue.GroupRefsUnique)
    (task : ReferenceWorkQueue.Task)
    : (state.addTask task).1.queue.TaskLinkedOn task.occurrence
        (task.groups.map Execution.DeliveryNode.ref) := by
  change (registrationCore (state.addTask task).1.queue).TaskLinkedOn task.occurrence _
  rw [state.addTask_registrationCore task]
  exact state.queue.addTask_links unique task

/-- Old unsettled-task links survive registration; the new task gains its links.
Witness: both the permanent catalogue and live memberships survive the phase projection.
-/
theorem State.addTask_unsettledTaskLinks {state : State} {settled : List Occurrence}
    (linked : state.queue.UnsettledTaskLinks settled)
    (unique : state.queue.GroupRefsUnique) (task : ReferenceWorkQueue.Task)
    : (state.addTask task).1.queue.UnsettledTaskLinks settled := by
  change (registrationCore (state.addTask task).1.queue).UnsettledTaskLinks settled
  rw [state.addTask_registrationCore task]
  exact linked.addTask unique task

end GraphQL.IncrementalDelivery.AlternativeWorkQueue
