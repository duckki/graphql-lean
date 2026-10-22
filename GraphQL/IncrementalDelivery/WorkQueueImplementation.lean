import GraphQL.IncrementalDelivery.Observation

/-! A finite, pure work-queue implementation following
[GraphQL.js](https://github.com/graphql/graphql-js) at `299a279` (PR #4870).

The queue and publisher are modeled after its
`src/execution/incremental/WorkQueue.ts` and
`src/execution/incremental/IncrementalPublisher.ts` modules. See
`docs/incremental-delivery/graphql-js-correspondence.md` for the complete definition map and
`docs/incremental-delivery/implementation.md` for implementation details and modeled deviations.
The draft specification and independent WorkQueue contract remain the correctness targets;
this is not a formal refinement of the asynchronous runtime.

The spec-facing `Execution.Work` is lowered to GraphQL.js-shaped `Work`: groups, tasks,
and streams. The host supplies batches of `GraphEvent` values instead of promises and
async iterators. Work is integrated when a task or stream item succeeds, not precompiled
at initialization. `handleGraphEvents` updates explicit root/group/task bookkeeping and
emits raw queue events. `IncrementalPublisher` then selects shared-value owners and maps
those events to the spec-facing response format. Initial-envelope construction and
subsequent entry mapping reuse Execution's helpers; the queue does not allocate wire IDs.

Queue `Task` and `Stream` records retain only bookkeeping descriptors. The original
execution work remains the source of fixed outcomes and expected child work in the event
source contract.

Execution retains an ordered declaration annotation separately from task contributors.
Lowering emits nested immediate-field declarations before the enclosing plan's groups,
without sorting object identity refs. Registration retains first-time identities and
parent links; failure removal distinguishes cancelled parents from successful shells.
Raw fixtures supply declarations explicitly through their test-only builder.

Differences are localized: finite pure outcomes validate source entries; errors are counts;
tasks retain rejected computations and unpublished values while other owners survive.
Unannounced groups keep task membership until normal release or ancestor cancellation.
Group startup inspects all cached rejections before starting private tasks. Its returned
notices are enqueue effects, retained in the queue's internal-notice FIFO until the source
observes their GROUP_FAILURE dispatch among task/stream callbacks. No batch-end relocation
is performed. Available batches expose computation failures before notification dispatch;
promise microtasks, external callback enqueue timing and backpressure remain abstract.
-/

namespace GraphQL.IncrementalDelivery
namespace ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics
open GraphQL.IncrementalDelivery.Execution (
  ExecutionGroupValue StreamItemValue WorkQueueEvent)

-----------------------------------------------------------------------------------------
-- `Work` definitions: GraphQL.js WorkQueue.ts
-----------------------------------------------------------------------------------------

/-- GraphQL.js `Group`, projected to a delivery node and its immediate parent ref. -/
structure Group where
  node : Execution.DeliveryNode
  parent : Option NodeRef := none
deriving Repr

/-- GraphQL.js `Stream`; its queue is represented by later `STREAM_ITEMS` events. -/
structure Stream where
  node : Execution.DeliveryNode
deriving Repr

/-- GraphQL.js `Task`; the computation is represented by a later host graph event. -/
structure Task where
  occurrence : Occurrence
  groups : List Execution.DeliveryNode
deriving Repr

/-- GraphQL.js-shaped `Work`, with ordered group declarations, tasks, and streams.
Group declarations are separate from task contributors. Integration excludes registered refs.
Task groups remain contributor references, including references to groups no longer live.
-/
structure Work where
  groups : List Group := []
  tasks : List Task := []
  streams : List Stream := []
deriving Repr

/-- Concatenate the three collections at an execution-work `combine` boundary. -/
def Work.combine (left right : Work) : Work :=
  {
    groups := left.groups ++ right.groups
    tasks := left.tasks ++ right.tasks
    streams := left.streams ++ right.streams
  }

/-- Lower explicit group declarations independently of task contributor references.
Execution emits declarations after immediate field work and before the plan's tasks,
matching native Work.groups insertion order. Declaration annotations add no address edge.
Task contributors identify owners; only declarations supply registration candidates.
-/
def Work.fromExecution (work : Execution.Work) (address : Address := []) : Work :=
  match work with
  | .empty => {}
  | .combine left right =>
      (fromExecution left (address ++ [0])).combine (fromExecution right (address ++ [1]))
  | .declareGroups groups tasks =>
      let lowered := fromExecution tasks address
      { lowered with groups := groups.map lowerGroup ++ lowered.groups }
  | .executionGroup groups _ _ _ =>
      { tasks := [⟨.executionGroup address, groups.map Execution.DeferredFragment.node⟩] }
  | .stream node _ => { streams := [⟨node⟩] }
where
  lowerGroup (group : Execution.DeferredFragment) : Group :=
    ⟨group.node, group.ancestors.head?.map Execution.DeliveryNode.ref⟩

-----------------------------------------------------------------------------------------
-- WorkQueue `State` definitions
-----------------------------------------------------------------------------------------

/-- GraphQL.js `GroupNode`, with task membership, children, and pending accounting. -/
structure GroupNode where
  group : Group
  childGroups : NodeRefs := []
  tasks : List Occurrence := []
  pending : Nat := 0
deriving Repr

/-- Queue task bookkeeping and retained computation outcome. `value` corresponds to
GraphQL.js's task-node value; `rejection` represents the rejection retained by the task's
`Computation`, so starting another owning group can replay it.
-/
structure TaskNode where
  task : Task
  value : Option ExecutionGroupValue := none
  rejection : Option Nat := none
  childStreams : NodeRefs := []
deriving Repr

/-- The newly integrated roots returned by `maybeIntegrateWork`. -/
structure NewWork where
  newGroups : List Execution.DeliveryNode := []
  newStreams : List Execution.DeliveryNode := []
deriving Repr

/-- GraphQL.js GroupFailureEvent, with error-list cardinality instead of error objects.
Startup produces this queued notice; FIFO dispatch forwards it alongside outcome entries.
-/
structure GroupFailureEvent where
  group : Execution.DeliveryNode
  errors : Nat
deriving Repr

/-- Host observation of initial activation. A listed rejection becomes visible when its
computation starts; it is not an already consumed TASK_FAILURE notification. An empty
observation represents computations which do not reject synchronously at startup.
-/
structure InitialStartup where
  failures : List (Occurrence × Nat) := []
deriving Repr

/-- The concrete WorkQueue state machine, corresponding to GraphQL.js's closure-local
bookkeeping. `createWorkQueueForSchedule` constructs its `Execution.WorkQueue` interface
for a supplied graph-event source; clients need not know this state type.
-/
structure State where
  rootGroups : NodeRefs := []
  rootStreams : NodeRefs := []
  /-- Node references registered earlier, retained after pruning or removal.
  This Lean adapter replaces GraphQL.js's separation of new groups from references.
  -/
  registeredGroups : NodeRefs := []
  /-- Node references retired by failure, including removed and refused late descendants.
  Successful closure/pruning does not add refs here. This history prevents an absent
  failed parent from making a newly revealed descendant appear healthy.
  -/
  cancelledGroups : NodeRefs := []
  groupNodes : List GroupNode := []
  taskNodes : List TaskNode := []
  tasks : List Task := []
  streams : List Stream := []
  /-- FIFO projection of internally enqueued GROUP_FAILURE notices. Task/stream callbacks
  remain source-supplied; the source observes their interleaving with these notices.
  This stores queued events, not a per-group cache of causes.
  -/
  groupFailureEvents : List GroupFailureEvent := []
  initialGroups : List Execution.DeliveryNode := []
  initialStreams : List Execution.DeliveryNode := []
  terminated : Bool := false
deriving Repr

/-- Find a live group record by delivery ref. -/
def State.groupNode? (state : State) (ref : NodeRef) : Option GroupNode :=
  state.groupNodes.find? (fun node => node.group.node.ref == ref)

/-- Find a registered task definition by its structural occurrence. -/
def State.task? (state : State) (occurrence : Occurrence) : Option Task :=
  state.tasks.find? (fun task => task.occurrence == occurrence)

/-- Find a started task's retained outcome and child streams. -/
def State.taskNode? (state : State) (occurrence : Occurrence) : Option TaskNode :=
  state.taskNodes.find? (fun node => node.task.occurrence == occurrence)

/-- Find an integrated stream descriptor by its stable delivery ref. -/
def State.stream? (state : State) (ref : NodeRef) : Option Stream :=
  state.streams.find? (fun stream => stream.node.ref == ref)

/-- Replace one live group node. -/
def State.putGroupNode (state : State) (updated : GroupNode) : State :=
  {
    state with
      groupNodes :=
        (state.groupNodes.map
          (fun node =>
            if node.group.node.ref == updated.group.node.ref then updated else node))
  }

/-- Replace one started task node. -/
def State.putTaskNode (state : State) (updated : TaskNode) : State :=
  {
    state with
      taskNodes :=
        (state.taskNodes.map
          (fun node =>
            if node.task.occurrence == updated.task.occurrence then updated else node))
  }

/-- Preserve first encounter order when several tasks name the same group. -/
def distinctDeliveryNodes (nodes : List Execution.DeliveryNode)
    : List Execution.DeliveryNode :=
  nodes.foldl
    (fun selected node =>
      if selected.any (fun known => known.ref == node.ref) then
        selected
      else
        selected ++ [node])
    []

/-- Install one first-time group and attach its parent link, the record-update part of
GraphQL.js `addGroup`. `addGroups` visits candidate parents before calling this operation.
An absent parent prevents installation. Permanent refs prevent reinstallation after removal;
the cancellation history records refused descendants of failed parents.
-/
def State.addGroup (state : State) (group : Group) : State :=
  if state.registeredGroups.contains group.node.ref
      || (state.groupNode? group.node.ref).isSome then
    state
  else
    let registered :=
      { state with registeredGroups := state.registeredGroups ++ [group.node.ref] }
    match group.parent with
    | none => { registered with groupNodes := state.groupNodes ++ [{ group }] }
    | some parent =>
        match state.groupNode? parent with
        | none =>
            if state.cancelledGroups.contains parent then
              {
                registered with
                  cancelledGroups := state.cancelledGroups ++ [group.node.ref]
              }
            else
              registered
        | some node =>
            let current : State :=
              { registered with groupNodes := state.groupNodes ++ [{ group }] }
            let children :=
              if node.childGroups.contains group.node.ref then
                node.childGroups
              else
                node.childGroups ++ [group.node.ref]
            current.putGroupNode { node with childGroups := children }

/-- GraphQL.js `addGroups`: traverse candidates in encounter order, recursively visiting
each candidate parent before installing its child. A scope-local visited set prevents
duplicate visits; permanent registration history also permits repeated raw-fixture ancestry.
New roots and child links follow actual installation order. The recursive depth bound is
one greater than the candidate count; visited refs bound every candidate-parent chain.
-/
def State.addGroups (state : State) (groups : List Group)
    : State × List Execution.DeliveryNode :=
  let (current, newGroups, _) :=
    groups.foldl (fun acc group => go groups (groups.length + 1) acc group)
      (state, [], [])
  (current, newGroups)
where
  go (candidates : List Group)
      : Nat → State × List Execution.DeliveryNode × NodeRefs → Group
        → State × List Execution.DeliveryNode × NodeRefs
    | 0, acc, _ => acc
    | fuel + 1, (current, roots, visited), group =>
        if visited.contains group.node.ref then
          (current, roots, visited)
        else
          let visited := visited ++ [group.node.ref]
          if current.registeredGroups.contains group.node.ref
              || (current.groupNode? group.node.ref).isSome then
            (current, roots, visited)
          else
            let (current, roots, visited) :=
              match group.parent.bind
                      (fun parent =>
                        candidates.find?
                          (fun candidate => candidate.node.ref == parent)) with
              | none => (current, roots, visited)
              | some parent => go candidates fuel (current, roots, visited) parent
            let next := current.addGroup group
            let roots := if group.parent.isNone then roots ++ [group.node] else roots
            (next, roots, visited)

/-- Register a task with every contributing group and increment their pending counts. -/
def State.addTask (state : State) (task : Task) : State :=
  let registered := { state with tasks := state.tasks ++ [task] }
  let current :=
    task.groups.foldl
      (fun current group =>
        match current.groupNode? group.ref with
        | none => current
        | some node =>
            if node.tasks.contains task.occurrence then
              current
            else
              current.putGroupNode
                {
                  node with
                    tasks := node.tasks ++ [task.occurrence], pending := node.pending + 1
                })
      registered
  if task.groups.any (fun group => current.rootGroups.contains group.ref)
      && (current.taskNode? task.occurrence).isNone then
    { current with taskNodes := current.taskNodes ++ [{ task }] }
  else
    current

/-- Register streams as roots or as child streams of the producing task. -/
def State.addStreams (state : State) (streams : List Stream)
    (parentTask : Option Occurrence)
    : State × List Execution.DeliveryNode :=
  let fresh :=
    streams.foldl
      (fun selected stream =>
        if (state.stream? stream.node.ref).isSome
            || selected.any (fun known => known.node.ref == stream.node.ref) then
          selected
        else
          selected ++ [stream])
      []
  let current := { state with streams := state.streams ++ fresh }
  match parentTask with
  | none => (current, fresh.map Stream.node)
  | some occurrence =>
      match current.taskNode? occurrence with
      | none => (current, [])
      | some node =>
          let refs := fresh.map (fun stream => stream.node.ref)
          (
            current.putTaskNode { node with childStreams := node.childStreams ++ refs },
            []
          )

/-- GraphQL.js `maybeIntegrateWork`: groups, then tasks, then streams. -/
def State.maybeIntegrateWork (state : State) (work : Work)
    (parentTask : Option Occurrence := none)
    : State × NewWork :=
  let (withGroups, newGroups) := state.addGroups work.groups
  let withTasks := work.tasks.foldl State.addTask withGroups
  let (withStreams, newStreams) := withTasks.addStreams work.streams parentTask
  (withStreams, ⟨newGroups, newStreams⟩)

/-- Remove accounted group shells and promote their descendants. Zero pending tasks
alone does not imply emptiness: settled values or rejected computations still need release.
Preserve the registration order of the supplied roots and their promoted child frontiers.
Creation refs identify objects; they do not prescribe activation order.
-/
def State.pruneEmptyGroups (state : State) (groups : List Execution.DeliveryNode)
    : State × List Execution.DeliveryNode :=
  go (state.groupNodes.length + groups.length + 1) state groups []
where
  go
      : Nat → State → List Execution.DeliveryNode → List Execution.DeliveryNode
        → State × List Execution.DeliveryNode
    | 0, current, _, kept => (current, kept)
    | _ + 1, current, [], kept => (current, kept)
    | fuel + 1, current, group :: rest, kept =>
        match current.groupNode? group.ref with
        | none => go fuel current rest kept
        | some node =>
            if node.tasks.isEmpty then
              let children :=
                node.childGroups.filterMap
                  (fun ref =>
                    (current.groupNode? ref).map (fun child => child.group.node))
              let current :=
                {
                  current with
                    groupNodes :=
                      (current.groupNodes.filter
                        (fun entry => entry.group.node.ref != group.ref))
                }
              go fuel current (children ++ rest) kept
            else
              go fuel current rest (kept ++ [group])

/-- Make already available rejections visible on their started computations before FIFO
notification dispatch. The input batch supplies availability; this starts no computation.
-/
def State.cacheTaskFailures (state : State) (available : List (Occurrence × Nat))
    : State :=
  available.foldl
    (fun current (occurrence, errors) =>
      match current.taskNode? occurrence with
      | none => current
      | some node => current.putTaskNode { node with rejection := some errors }) state

/-- Start a task by recording its node; host computation remains outside Lean. -/
def State.startTask (state : State) (occurrence : Occurrence)
    (available : List (Occurrence × Nat) := [])
    : State :=
  if (state.taskNode? occurrence).isSome then
    state
  else
    match state.task? occurrence with
    | none => state
    | some task =>
        let rejection :=
          available.findSome?
            (fun (other, errors) => if other == occurrence then some errors else none)
        { state with taskNodes := state.taskNodes ++ [{ task, rejection }] }

-----------------------------------------------------------------------------------------
-- `GraphEvent` definitions
-----------------------------------------------------------------------------------------

/-- GraphQL.js `TaskResult`: a resolved value and newly generated work. -/
structure TaskResult where
  value : ExecutionGroupValue
  work : Work := {}
deriving Repr

/-- GraphQL.js `StreamItem`: occurrence is a Lean-only identity for source proofs. -/
structure StreamItem where
  occurrence : Occurrence
  value : StreamItemValue
  work : Work := {}
deriving Repr

/-- Observed GraphQL.js FIFO dispatch, including internally queued GROUP_FAILURE events.
The source supplies task/stream outcomes and observes internal notice positions. Internal
notices must match the queue's pending notice head; the source cannot manufacture them.
-/
inductive GraphEvent where
  | taskSuccess (task : Occurrence) (result : TaskResult)
  | taskFailure (task : Occurrence) (errors : Nat)
  | groupFailure (failure : GroupFailureEvent)
  | streamItems (stream : Execution.DeliveryNode) (items : List StreamItem)
  | streamSuccess (stream : Execution.DeliveryNode)
  | streamFailure (stream : Execution.DeliveryNode) (errors : Nat)
deriving Repr

-----------------------------------------------------------------------------------------
-- `GraphEvent` handlers
-----------------------------------------------------------------------------------------

/-- Drop a task's live node and its membership in all group task sets. -/
def State.removeTask (state : State) (occurrence : Occurrence) : State :=
  {
    state with
      taskNodes := state.taskNodes.filter (fun node => node.task.occurrence != occurrence)
      groupNodes :=
        state.groupNodes.map
          (fun node =>
            { node with tasks := node.tasks.filter (· != occurrence) })
  }

/-- Remove a failed group and its descendants, retaining shared tasks with other owners.
Remember removed refs so future child registration and health checks retain cancellation.
The finite ref-list loop stands in for GraphQL.js's recursive `removeGroup`.
Missing child refs do not spend the live-node budget: earlier removals may leave stale
links in a surviving parent. Termination also decreases the pending list on those steps.
-/
def State.removeGroup (state : State) (ref : NodeRef) : State :=
  let rec collect : Nat → State → NodeRefs → NodeRefs → NodeRefs
    | 0, _, _, removed => removed
    | _ + 1, _, [], removed => removed
    | fuel + 1, current, head :: rest, removed =>
        match current.groupNode? head with
        | none => collect (fuel + 1) current rest removed
        | some node => collect fuel current (node.childGroups ++ rest) (head :: removed)
    termination_by fuel _ pending _ => (fuel, pending.length)
  let removed := collect (state.groupNodes.length + 1) state [ref] []
  let retained :=
    state.groupNodes.filter (fun node => !removed.contains node.group.node.ref)
  let liveTask (node : TaskNode) : Bool :=
    node.task.groups.any
      (fun group =>
        retained.any (fun owner => owner.group.node.ref == group.ref))
  {
    state with
      cancelledGroups := state.cancelledGroups ++ removed
      groupNodes := retained
      taskNodes := state.taskNodes.filter liveTask
      rootGroups := state.rootGroups.filter (fun root => !removed.contains root)
  }

/-- Flush a completed group's stored values, remove shared-task memberships, and
promote nonempty child groups plus streams produced by those tasks.
-/
def State.finishGroupSuccess (state : State) (group : GroupNode)
    : State × List WorkQueueEvent × NewWork :=
  let (flushed, values, streams) :=
    group.tasks.foldl
      (fun (current, values, streams) occurrence =>
        match current.taskNode? occurrence with
        | none => (current, values, streams)
        | some taskNode =>
            let values :=
              match taskNode.value with
              | none => values
              | some value => values ++ [value]
            (current.removeTask occurrence, values, streams ++ taskNode.childStreams))
      (state, [], [])
  let current :=
    {
      flushed with
        groupNodes :=
          flushed.groupNodes.filter
            (fun node => node.group.node.ref != group.group.node.ref)
        rootGroups := flushed.rootGroups.filter (· != group.group.node.ref)
    }
  let children :=
    group.childGroups.filterMap
      (fun ref => (current.groupNode? ref).map (fun node => node.group.node))
  let (pruned, groups) := current.pruneEmptyGroups children
  let newStreams := streams.filterMap (fun ref => (pruned.stream? ref).map Stream.node)
  let newWork : NewWork := ⟨groups, newStreams⟩
  let valueEvents :=
    if values.isEmpty then
      []
    else
      [Execution.WorkQueueEvent.groupValues group.group.node values]
  (pruned, valueEvents ++ [.groupSuccess group.group.node groups newStreams], newWork)

/-- Close an announced failed group and cancel its remaining dependent work. -/
def State.finishGroupFailure (state : State) (group : GroupNode) (errors : Nat)
    : State × GroupFailureEvent :=
  (state.removeGroup group.group.node.ref, ⟨group.group.node, errors⟩)

/-- Inspect cached rejections before starting any private work. A failed group is
removed immediately and its aggregate notification is returned as a pushGraphEvent effect.
Pending and successful computations contribute no errors, and no other outcome is awaited.
-/
def State.startGroup (state : State) (ref : NodeRef)
    (available : List (Occurrence × Nat) := [])
    : State × List GroupFailureEvent :=
  let state := state.cacheTaskFailures available
  match state.groupNode? ref with
  | none => (state, [])
  | some node =>
      -- GraphQL.js startGroup's local errors array, projected to task-boundary counts.
      let errors :=
        node.tasks.filterMap (fun task => (state.taskNode? task).bind (·.rejection))
      if errors.isEmpty then
        (
          node.tasks.foldl (fun current task => current.startTask task available) state,
          []
        )
      else
        let (next, failure) := state.finishGroupFailure node errors.sum
        (next, [failure])

/-- Register a newly released stream as started; its iterator remains host-owned. -/
def State.startStream (state : State) (ref : NodeRef) : State :=
  if (state.stream? ref).isNone || state.rootStreams.contains ref then
    state
  else
    { state with rootStreams := state.rootStreams ++ [ref] }

/-- Announce and activate newly released group and stream roots. -/
def State.startNewWork (state : State) (newWork : NewWork)
    (available : List (Occurrence × Nat) := [])
    : State × List GroupFailureEvent :=
  let groups := newWork.newGroups.map Execution.DeliveryNode.ref
  let streams := newWork.newStreams.map Execution.DeliveryNode.ref
  let current := { state with rootGroups := state.rootGroups ++ groups }
  let (startedGroups, failures) :=
    groups.foldl
      (fun (current, failures) ref =>
        let (next, queued) := current.startGroup ref available
        (next, failures ++ queued))
      (current, [])
  (streams.foldl State.startStream startedGroups, failures)

/-- Enqueue internal notices in creation order, projecting native pushGraphEvent.
They are consumed only by matching GROUP_FAILURE inputs at their observed FIFO positions.
-/
def State.enqueueGroupFailures (state : State) (events : List GroupFailureEvent)
    : State :=
  { state with groupFailureEvents := state.groupFailureEvents ++ events }

/-- Initialize registration and activation with optional synchronous rejection visibility.
The empty startup observation is ordinary asynchronous initialization. Original initial
notices survive startup removal; queued failures await observed FIFO dispatch.
-/
def State.initialize (initialWork : Work) (startup : InitialStartup := {}) : State :=
  let (integrated, newWork) := ({} : State).maybeIntegrateWork initialWork
  let (pruned, groups) := integrated.pruneEmptyGroups newWork.newGroups
  let roots := { newWork with newGroups := groups }
  let (started, failures) := pruned.startNewWork roots startup.failures
  {
    started.enqueueGroupFailures failures with
      initialGroups := groups, initialStreams := roots.newStreams
  }

/-- A rejected computation remains attached to its task while other owners survive.
Close only active owners, as GraphQL.js `taskFailure` does. Dormant owners keep task
membership and replay the same rejection when started; failure does not decrement pending.
-/
def State.taskFailure (state : State) (occurrence : Occurrence) (errors : Nat)
    : State × List WorkQueueEvent :=
  match state.taskNode? occurrence with
  | none => (state, [])
  | some taskNode =>
      let current := state.putTaskNode { taskNode with rejection := some errors }
      taskNode.task.groups.foldl
        (fun (current, events) group =>
          match current.groupNode? group.ref with
          | none => (current, events)
          | some node =>
              if current.rootGroups.contains group.ref then
                let (next, failure) := current.finishGroupFailure node errors
                (next, events ++ [.groupFailure failure.group failure.errors])
              else
                (current, events))
        (current, [])

/-- Finish successful ready groups and inspect newly released groups before starting work.
Cached startup failures are returned separately; failures on already active groups remain
owned by their FIFO task-failure input. Each iteration removes a live group.
-/
def State.drainReadyGroups (state : State) (available : List (Occurrence × Nat) := [])
    : State × List WorkQueueEvent × List GroupFailureEvent :=
  go state.groupNodes.length state
where
  go : Nat → State → State × List WorkQueueEvent × List GroupFailureEvent
    | 0, current => (current, [], [])
    | fuel + 1, current =>
        let ready :=
          current.rootGroups.findSome?
            fun ref => do
              let node ← current.groupNode? ref
              if node.pending == 0 then
                some node
              else
                none
        match ready with
        | none => (current, [], [])
        | some node =>
            let (next, events, released) := current.finishGroupSuccess node
            let (started, failures) := next.startNewWork released available
            let (finished, later, queued) := go fuel started
            (finished, events ++ later, failures ++ queued)

/-- GraphQL.js `taskSuccess`: integrate child Work,
then decrement each surviving contributing group in one pass. Only released
groups with no pending tasks finish. Raw `GROUP_VALUES` names the triggering group.
Then activate released work, collecting cached rejections before starting new tasks.
Settlements whose task node was removed are ignored.
-/
def State.taskSuccess (state : State) (occurrence : Occurrence) (result : TaskResult)
    (available : List (Occurrence × Nat) := [])
    : State × List WorkQueueEvent × List GroupFailureEvent :=
  match state.taskNode? occurrence with
  | none => (state, [], [])
  | some taskNode =>
      let withValue := state.putTaskNode { taskNode with value := some result.value }
      let (integrated, _) := withValue.maybeIntegrateWork result.work (some occurrence)
      let (current, events, released) :=
        taskNode.task.groups.foldl
          (fun (current, events, released) group =>
            match current.groupNode? group.ref with
            | none => (current, events, released)
            | some node =>
                let node := { node with pending := node.pending - 1 }
                let current := current.putGroupNode node
                if current.rootGroups.contains group.ref && node.pending == 0 then
                  let (next, finished, newWork) := current.finishGroupSuccess node
                  (
                    next,
                    events ++ finished,
                    ⟨
                      released.newGroups ++ newWork.newGroups,
                      released.newStreams ++ newWork.newStreams
                    ⟩
                  )
                else
                  (current, events, released))
          (integrated, [], {})
      let (started, failures) := current.startNewWork released available
      let (drained, later, queued) := started.drainReadyGroups available
      (drained, events ++ later, failures ++ queued)

/-- Integrate each item result's child Work and emit one raw `STREAM_VALUES` event. -/
def State.streamItems (state : State) (stream : Execution.DeliveryNode)
    (items : List StreamItem) (available : List (Occurrence × Nat) := [])
    : State × List WorkQueueEvent × List GroupFailureEvent :=
  if !state.rootStreams.contains stream.ref then
    (state, [], [])
  else
    let (current, groups, streams, values, failures) :=
      items.foldl
        (fun (current, groups, streams, values, failures) item =>
          let (integrated, newWork) := current.maybeIntegrateWork item.work
          let (pruned, nonempty) := integrated.pruneEmptyGroups newWork.newGroups
          let (started, queued) :=
            pruned.startNewWork { newWork with newGroups := nonempty } available
          (
            started,
            groups ++ nonempty,
            streams ++ newWork.newStreams,
            values ++ [item.value],
            failures ++ queued
          ))
        (state, [], [], [], [])
    let (drained, later, queued) := current.drainReadyGroups available
    (drained, .streamValues stream values groups streams :: later, failures ++ queued)

/-- Close a started stream after its source reports exhaustion. -/
def State.streamSuccess (state : State) (stream : Execution.DeliveryNode)
    : State × List WorkQueueEvent :=
  if state.rootStreams.contains stream.ref then
    (
      { state with rootStreams := state.rootStreams.filter (· != stream.ref) },
      [.streamSuccess stream]
    )
  else
    (state, [])

/-- Close a started stream after its source reports a bubbling failure. -/
def State.streamFailure (state : State) (stream : Execution.DeliveryNode) (errors : Nat)
    : State × List WorkQueueEvent :=
  if state.rootStreams.contains stream.ref then
    (
      { state with rootStreams := state.rootStreams.filter (· != stream.ref) },
      [.streamFailure stream errors]
    )
  else
    (state, [])

/-- Failure outcomes already available in one host batch, in FIFO input order.
Their computation caches may be inspected before their notification is dispatched.
-/
def GraphEvent.availableFailures (events : List GraphEvent) : List (Occurrence × Nat) :=
  events.filterMap
    (fun event =>
      match event with
      | .taskFailure task errors => some (task, errors)
      | _ => none)

/-- Consume the next internal notice, preserving the descriptor and count actually queued.
An unmatched or out-of-order input has no output and is excluded by source admission.
-/
def State.groupFailure (state : State) (supplied : GroupFailureEvent)
    : State × List WorkQueueEvent :=
  match state.groupFailureEvents with
  | [] => (state, [])
  | first :: rest =>
      if first.group.ref == supplied.group.ref && first.errors == supplied.errors then
        (
          { state with groupFailureEvents := rest },
          [.groupFailure first.group first.errors]
        )
      else
        (state, [])

/-- Dispatch one observed FIFO entry. Computation-cache availability is independent of
notification consumption. Newly generated internal notices are enqueue effects, realized
by dispatchGraphEvent before the next supplied entry is consumed.
-/
def State.handleGraphEvent (state : State) (event : GraphEvent)
    (available : List (Occurrence × Nat) := [])
    : State × List WorkQueueEvent × List GroupFailureEvent :=
  let state := state.cacheTaskFailures available
  match event with
  | .taskSuccess task result => state.taskSuccess task result available
  | .taskFailure task errors =>
      let (next, events) := state.taskFailure task errors
      (next, events, [])
  | .groupFailure failure =>
      let (next, events) := state.groupFailure failure
      (next, events, [])
  | .streamItems stream items => state.streamItems stream items available
  | .streamSuccess stream =>
      let (next, events) := state.streamSuccess stream
      (next, events, [])
  | .streamFailure stream errors =>
      let (next, events) := state.streamFailure stream errors
      (next, events, [])

/-- Realize one handler's pushGraphEvent effects without forwarding the notices early.
The pending internal FIFO is retained across host batches and empty replay calls.
-/
def State.dispatchGraphEvent (state : State) (event : GraphEvent)
    (available : List (Occurrence × Nat) := [])
    : State × List WorkQueueEvent :=
  let (next, events, queued) := state.handleGraphEvent event available
  (next.enqueueGroupFailures queued, events)

/-- Consume supplied FIFO entries, including internal notice dispatch at its actual position.
Termination follows complete notice consumption; a cut with queued notices remains a prefix.
-/
def State.handleGraphEvents (state : State) (graphEvents : List GraphEvent)
    : State × List WorkQueueEvent :=
  if state.terminated then
    (state, [])
  else
    let available := GraphEvent.availableFailures graphEvents
    let (current, events) :=
      graphEvents.foldl
        (fun (current, events) event =>
          let (next, produced) := current.dispatchGraphEvent event available
          (next, events ++ produced))
        (state, [])
    if current.rootGroups.isEmpty
        && current.rootStreams.isEmpty
        && current.groupFailureEvents.isEmpty then
      ({ current with terminated := true }, events ++ [.workQueueTermination])
    else
      (current, events)

-----------------------------------------------------------------------------------------
-- IncrementalPublisher: GraphQL.js publisher boundary
-----------------------------------------------------------------------------------------

/-- Stored mapper IDs and live notices. Execution's shared response helpers allocate IDs;
closed IDs remain in the finite map, but only live nodes participate in owner selection.
-/
structure IncrementalPublisher where
  ids : Execution.IDState := {}
  active : List Execution.DeliveryNode := []
deriving Repr

/-- GraphQL.js `_getBestIdAndSubPath`: select the deepest live contributor. The
spec-facing mapper computes the actual ID and subPath from this selected node.
-/
def IncrementalPublisher.getBestIdAndSubPath (publisher : IncrementalPublisher)
    (initial : Execution.DeliveryNode) (value : ExecutionGroupValue)
    : Execution.DeliveryNode :=
  value.deliveryGroups.foldl
    (fun best candidate =>
      if publisher.active.any (fun node => node.ref == candidate.ref)
          && best.path.length < candidate.path.length then
        candidate
      else
        best)
    initial

/-- Handle one raw queue event. Owner normalization occurs here, not in WorkQueue. -/
def IncrementalPublisher.handleWorkQueueEvent (publisher : IncrementalPublisher)
    : WorkQueueEvent → IncrementalPublisher × List Execution.WorkQueueEvent
  | .groupValues group values =>
      let events :=
        values.map
          fun value =>
            let owner := publisher.getBestIdAndSubPath group value
            Execution.WorkQueueEvent.groupValues owner [value]
      (publisher, events)
  | .groupSuccess group groups streams =>
      (
        {
          publisher with
            active :=
              (publisher.active.filter (fun node => node.ref != group.ref))
              ++ groups
              ++ streams
        },
        [.groupSuccess group groups streams]
      )
  | .groupFailure group errors =>
      (
        {
          publisher with
            active := publisher.active.filter (fun node => node.ref != group.ref)
        },
        [.groupFailure group errors]
      )
  | .streamValues stream values groups streams =>
      (
        { publisher with active := publisher.active ++ groups ++ streams },
        [.streamValues stream values groups streams]
      )
  | .streamSuccess stream =>
      (
        {
          publisher with
            active := publisher.active.filter (fun node => node.ref != stream.ref)
        },
        [.streamSuccess stream]
      )
  | .streamFailure stream errors =>
      (
        {
          publisher with
            active := publisher.active.filter (fun node => node.ref != stream.ref)
        },
        [.streamFailure stream errors]
      )
  | .workQueueTermination => (publisher, [.workQueueTermination])

/-- Normalize a whole GraphQL.js queue batch while threading live notice state. -/
def IncrementalPublisher.normalizeBatch (publisher : IncrementalPublisher)
    (batch : List WorkQueueEvent)
    : IncrementalPublisher × List Execution.WorkQueueEvent :=
  batch.foldl
    (fun (current, events) event =>
      let (next, normalized) := current.handleWorkQueueEvent event
      (next, events ++ normalized))
    (publisher, [])

/-- GraphQL.js `_handleBatch`, reusing the spec-facing entry mapper after owner
normalization for subsequent updates. The queue never allocates or serializes wire IDs.
-/
def IncrementalPublisher.handleBatch (publisher : IncrementalPublisher)
    (batch : List WorkQueueEvent)
    : Execution.IncrementalStreamUpdateResult × IncrementalPublisher :=
  let (normalized, events) := publisher.normalizeBatch batch
  let (update, ids) := (Execution.mapWorkEventBatch events).run publisher.ids
  (update, { normalized with ids })

-----------------------------------------------------------------------------------------
-- `createWorkQueueForSchedule` interface
-----------------------------------------------------------------------------------------

/-- Replay supplied host batches through the queue and owner-selecting publisher.
Silent batches advance the queue without emitting a batch. This shared replay preserves
the publisher's ID state; wire mapping is a separate, deterministic projection.
-/
def State.runWithPublisher (queue : State) (publisher : IncrementalPublisher)
    (batches : List (List GraphEvent))
    : State × IncrementalPublisher × List (List Execution.WorkQueueEvent) :=
  batches.foldl
    (fun (queue, publisher, outputs) batch =>
      let (nextQueue, raw) := queue.handleGraphEvents batch
      if raw.isEmpty then
        (nextQueue, publisher, outputs)
      else
        let (nextPublisher, mapped) := publisher.normalizeBatch raw
        (nextQueue, nextPublisher, outputs ++ [mapped]))
    (queue, publisher, [])

/-- Project initialized queue state, including pending internal notices, to normalized batches. -/
def State.runNormalized (queue : State) (batches : List (List GraphEvent))
    : State × List (List Execution.WorkQueueEvent) :=
  let publisher : IncrementalPublisher :=
    { active := queue.initialGroups ++ queue.initialStreams }
  let (queue, _, outputs) := queue.runWithPublisher publisher batches
  (queue, outputs)

/-- Construct the shared `Execution.WorkQueue` interface from executed work and a host
source: lower the work, initialize concrete state, and expose normalized publisher output.
The existential input prefix describes a source language, not a selected future.
-/
def createWorkQueueForSchedule (work : Execution.Work)
    (source : EventSource (List GraphEvent)) (startup : InitialStartup := {})
    : Execution.WorkQueue :=
  let queue := State.initialize (Work.fromExecution work) startup
  {
    initialGroups := queue.initialGroups
    initialStreams := queue.initialStreams
    workEventStream :=
      {
        admissible :=
          fun outputs =>
            ∃ inputs, source.admissible inputs ∧ (queue.runNormalized inputs).2 = outputs
        finished :=
          fun outputs =>
            ∃ inputs,
              source.admissible inputs
              ∧ let (finalState, emitted) := queue.runNormalized inputs
                emitted = outputs ∧ finalState.terminated = true
      }
  }

-----------------------------------------------------------------------------------------
-- Incremental execution
-----------------------------------------------------------------------------------------

/-- Initialize the incremental response, concrete queue, and publisher together.
This models the initial-envelope part of GraphQL.js `buildResponse`, delegating pending
notices, root data/errors, and ID allocation to `Execution.initializeIncrementalResponse`.
This composition adds concrete queue and live-owner state; finite replay and the
optional cursor both use it.
-/
def initializeIncrementalResponse (response : Execution.Response) (work : Execution.Work)
    (startup : InitialStartup := {})
    : Execution.InitialIncrementalStreamResult × State × IncrementalPublisher :=
  let queue := State.initialize (Work.fromExecution work) startup
  let (initial, ids) :=
    Execution.initializeIncrementalResponse response queue.initialGroups
      queue.initialStreams
  (initial, queue, { ids, active := queue.initialGroups ++ queue.initialStreams })

/-- Replay observed FIFO batches and map normalized outputs through the shared mapper.
The residual queue retains undispatched internal notices, including across empty calls.
-/
def State.run (queue : State) (publisher : IncrementalPublisher)
    (inputs : List (List GraphEvent))
    : List Execution.IncrementalStreamUpdateResult × State × IncrementalPublisher :=
  let (queue, nextPublisher, batches) := queue.runWithPublisher publisher inputs
  let (updates, ids) := (batches.mapM Execution.mapWorkEventBatch).run publisher.ids
  (updates, queue, { nextPublisher with ids })

-----------------------------------------------------------------------------------------
-- GraphEvent semantics
-----------------------------------------------------------------------------------------

/-- Shared structural lookup of deferred contributors and produced child work.
Stream items have no deferred contributors. Invalid addresses, kinds, and indices fail.
-/
def taskContext? (work : Execution.Work) (occurrence : Occurrence)
    : Option (List Execution.DeliveryNode × Work) := do
  let address :=
    match occurrence with
    | .executionGroup address | .item address _ => address
  let location ← locateWork work address
  match occurrence, location.current with
  | .executionGroup _, .executionGroup groups _ _ children =>
      some
        (
          groups.map Execution.DeferredFragment.node,
          Work.fromExecution children (address ++ [0])
        )
  | .item _ index, .stream _ items =>
      let (_, children) ← items[index]?
      some ([], Work.fromExecution children (address ++ [index]))
  | _, _ => none

/-- Child work expected after a successful execution-group task. -/
def taskChildWork? (work : Execution.Work) : Occurrence → Option Work
  | occurrence@(.executionGroup _) => (taskContext? work occurrence).map Prod.snd
  | .item _ _ => none

/-- Exact contributor descriptors expected for an execution-group task. -/
def taskGroups? (work : Execution.Work)
    : Occurrence → Option (List Execution.DeliveryNode)
  | occurrence@(.executionGroup _) => (taskContext? work occurrence).map Prod.fst
  | .item _ _ => none

/-- Child work expected after one successful stream item. -/
def streamItemWork? (work : Execution.Work) : Occurrence → Option Work
  | occurrence@(.item _ _) => (taskContext? work occurrence).map Prod.snd
  | .executionGroup _ => none

/-- Task/item outcomes and group/stream closure identities in one graph event. -/
def GraphEvent.identities : GraphEvent → List Occurrence × NodeRefs
  | .taskSuccess task _ | .taskFailure task _ => ([task], [])
  | .streamItems _ items => (items.map StreamItem.occurrence, [])
  | .groupFailure failure => ([], [failure.group.ref])
  | .streamSuccess stream | .streamFailure stream _ => ([], [stream.ref])

/-- Successful task and item occurrences made available by one graph event. -/
def GraphEvent.successes : GraphEvent → List Occurrence
  | .taskSuccess task _ => [task]
  | .streamItems _ items => items.map StreamItem.occurrence
  | _ => []

/-- Items already reported for one stream in the preceding graph-event prefix. -/
def GraphEvent.itemsBefore (before : List GraphEvent) (ref : NodeRef) : List StreamItem :=
  before.flatMap
    fun event =>
      match event with
      | .streamItems stream items => if stream.ref == ref then items else []
      | _ => []

/-- Fresh task/item outcomes and nonrepeating group/stream closure notifications. -/
def GraphEvent.Fresh (before : List GraphEvent) (event : GraphEvent) : Prop :=
  let usedTasks := before.flatMap (fun prior => prior.identities.1)
  let usedStreams := before.flatMap (fun prior => prior.identities.2)
  event.identities.1.Nodup
  ∧ event.identities.2.Nodup
  ∧ (∀ task ∈ event.identities.1, task ∉ usedTasks)
  ∧ (∀ stream ∈ event.identities.2, stream ∉ usedStreams)

/-- The source event's resolved value agrees with the finite `Execution.Work` outcome. -/
def GraphEvent.MatchesWork (work : Execution.Work) : GraphEvent → Prop
  | .taskSuccess occurrence result =>
      ∃ owners producer,
        TaskAt work occurrence owners producer
          (.object result.value.path (.ok (result.value.data, result.value.errors)))
        ∧ taskGroups? work occurrence = some result.value.deliveryGroups
        ∧ taskChildWork? work occurrence = some result.work
  | .taskFailure occurrence errors =>
      ∃ owners producer path,
        TaskAt work occurrence owners producer (.object path (.error errors))
  | .groupFailure failure =>
      (∃ dependencies producer, NodeAt work failure.group .group dependencies producer)
      ∧ 0 < failure.errors
  | .streamItems stream items =>
      ∀ item ∈ items,
        ∃ owners producer,
          TaskAt work item.occurrence owners producer
            (.item stream (.ok (item.value.item, item.value.errors)))
          ∧ streamItemWork? work item.occurrence = some item.work
  | .streamSuccess stream =>
      ∃ dependencies producer, NodeAt work stream .stream dependencies producer
  | .streamFailure stream errors =>
      ∃ address items producer dependencies,
        Located work address (.stream stream items) producer dependencies
        ∧ ∃ outcome children,
            (outcome, children) ∈ items ∧ outcome.deliveryResult = .error errors

/-- Producers settle before dependent work; stream-item batches advance in order and
success follows all modeled items. Host fairness is deliberately not assumed.
-/
def GraphEvent.Ready (work : Execution.Work) (before : List GraphEvent)
    : GraphEvent → Prop
  | .taskSuccess occurrence _ | .taskFailure occurrence _ =>
      ∃ owners producer payload,
        TaskAt work occurrence owners producer payload
        ∧ ∀ source, producer = some source → source ∈ before.flatMap GraphEvent.successes
  | .groupFailure _ => True
  | .streamItems stream items =>
      ∃ address results producer dependencies,
        Located work address (.stream stream results) producer dependencies
        ∧ items ≠ []
        ∧ stream.ref ∉ before.flatMap (fun event => event.identities.2)
        ∧ (∀ source,
            producer = some source → source ∈ before.flatMap GraphEvent.successes)
        ∧ items.map StreamItem.occurrence
          = (List.range items.length).map
              (fun offset =>
                .item address
                  ((GraphEvent.itemsBefore before stream.ref).length + offset))
  | .streamSuccess stream =>
      ∃ address results producer dependencies,
        Located work address (.stream stream results) producer dependencies
        ∧ (∀ source,
            producer = some source → source ∈ before.flatMap GraphEvent.successes)
        ∧ (GraphEvent.itemsBefore before stream.ref).length = results.length
  | .streamFailure stream errors =>
      ∃ address results producer dependencies,
        Located work address (.stream stream results) producer dependencies
        ∧ (∀ source,
            producer = some source → source ∈ before.flatMap GraphEvent.successes)
        ∧ ∃ outcome children,
            results[(GraphEvent.itemsBefore before stream.ref).length]?
              = some (outcome, children)
            ∧ outcome.deliveryResult = .error errors

/-- Initial cache observations name distinct, producer-free task failures with their
actual boundary counts. They do not consume the corresponding notifications.
-/
def InitialStartup.MatchesWork (startup : InitialStartup) (work : Execution.Work)
    : Prop :=
  (startup.failures.map Prod.fst).Nodup
  ∧ ∀ occurrence errors,
      (occurrence, errors) ∈ startup.failures
      → (GraphEvent.taskFailure occurrence errors).MatchesWork work
        ∧ (GraphEvent.taskFailure occurrence errors).Ready work []

/-- Legal finite graph-event prefixes, independent of queue bookkeeping. -/
inductive ValidGraphEvents (work : Execution.Work) : List GraphEvent → Prop where
  | nil : ValidGraphEvents work []
  | append {before event}
    (valid : ValidGraphEvents work before)
    (matching : event.MatchesWork work)
    (fresh : event.Fresh before)
    (ready : event.Ready work before)
    : ValidGraphEvents work (before ++ [event])

-----------------------------------------------------------------------------------------
-- Host schedule semantics
-----------------------------------------------------------------------------------------

/-- Check current live membership of a started task or stream.
Batch admission separately retains earlier task/stream eligibility within that batch.
Internal notice dispatch requires the current queued head.
-/
def State.acceptsGraphEvent (state : State) : GraphEvent → Bool
  | .taskSuccess task _ | .taskFailure task _ => (state.taskNode? task).isSome
  | .groupFailure failure =>
      state.groupFailureEvents.head?.any
        (fun first =>
          first.group.ref == failure.group.ref && first.errors == failure.errors)
  | .streamItems stream _ | .streamSuccess stream | .streamFailure stream _ =>
      state.rootStreams.contains stream.ref

/-- Admit notifications eligible at any earlier dispatch boundary of this batch, including
entry and consumption. A task or stream can start and retire between those two boundaries
while its already queued callback remains admissible. The local predicate accumulates
eligibility only for this check; it adds no runtime state and does not cross batch boundaries.
Dispatch retains the complete batch's shared available-computation snapshot. Internal
notices always require the current queued head, regardless of earlier eligibility.
-/
def State.acceptsBatch (state : State) (batch : List GraphEvent) : Bool :=
  go (fun _ => false) (GraphEvent.availableFailures batch) state batch
where
  go (earlier : GraphEvent → Bool) (available : List (Occurrence × Nat))
      : State → List GraphEvent → Bool
    | _, [] => true
    | state, event :: rest =>
        (match event with
          | .groupFailure _ => state.acceptsGraphEvent event
          | _ => earlier event || state.acceptsGraphEvent event)
        && go (fun candidate => earlier candidate || state.acceptsGraphEvent candidate)
            available (state.dispatchGraphEvent event available).1 rest

/-- Check the host's start/stop discipline without constraining output accounting.
Each batch retains all earlier eligibility and shared cache availability through FIFO dispatch.
These boundaries must be retained by state replay.
-/
def inputsStarted (work : Execution.Work) (batches : List (List GraphEvent))
    (startup : InitialStartup := {})
    : Bool :=
  (batches.foldl
    (fun (state, valid) batch =>
      let next := (state.handleGraphEvents batch).1
      (next, valid && !state.terminated && !batch.isEmpty && state.acceptsBatch batch))
    ((State.initialize (Work.fromExecution work) startup), true)).2

end ReferenceWorkQueue

namespace EventSource

open ReferenceWorkQueue

/-- A fresh, prefix-closed graph-event source whose admitted batches match `work` and
respect the queue's start/stop requests. Fixed payloads, revealed child work, fresh
identities, producer order, and stream-item order come from `ValidGraphEvents`; start
discipline comes from `inputsStarted`. Neither initial-notice correctness, output-history
admission, nor host fairness is assumed here. Queue state determines output termination,
independently of the host source's `finished` predicate.
The flattened history checks payloads and dependencies only; batch boundaries separately
determine which task rejections are available before notification dispatch. Start eligibility
may come from any earlier dispatch boundary within the same batch, including entry and
consumption. Retirement within that batch does not invalidate a previously eligible
notification. Eligibility from earlier batches alone supplies no permission for an
otherwise stale callback. Internal notices still require current FIFO-head permission.
Startup observations must match work, and the first admitted batch includes their
actually started failures. These additional conditions are vacuous for empty startup.
-/
def ValidFor (schedule : EventSource (List GraphEvent)) (work : Execution.Work)
    (startup : InitialStartup := {})
    : Prop :=
  startup.MatchesWork work
  ∧ schedule.history = []
  ∧ schedule.admissible []
  ∧ (∀ before after,
      before.IsPrefix after → schedule.admissible after → schedule.admissible before)
  ∧ ∀ batches,
      schedule.admissible batches
      → ValidGraphEvents work batches.flatten
        ∧ inputsStarted work batches startup = true
        ∧ match batches with
          | [] => True
          | first :: _ =>
              (startup.failures.filter
                (fun failure =>
                  ((State.initialize (Work.fromExecution work) startup).taskNode?
                    failure.1).isSome)).Subset
                (GraphEvent.availableFailures first)

/-- The host input language admits another nonempty batch at every unfinished queue
prefix for `work`. This optional queue-boundary no-stall assumption is separate from
`ValidFor`; source `finished` is irrelevant. It applies even without a demonstrated
healthy unsettled task or live stream, so it is stronger than host-only responsiveness.
Finite queue nonblocking follows using the fresh-event budget, not host timing/fairness.
-/
def NonblockingFor (schedule : EventSource (List GraphEvent)) (work : Execution.Work)
    : Prop :=
  ∀ inputs,
    schedule.admissible inputs
    → ((State.initialize (Work.fromExecution work)).runNormalized inputs).1.terminated
      ≠ true
    → ∃ batch, batch ≠ [] ∧ schedule.admissible (inputs ++ [batch])

end EventSource

namespace ReferenceWorkQueue

-----------------------------------------------------------------------------------------
-- `createWorkQueueForSchedule` Conformance statement at the level of work and schedule
-----------------------------------------------------------------------------------------

/-- Work returned by pure root selection-set execution, before any queue observation.
This includes completed resolver outcomes and is not merely an execution plan.
-/
def ExecutedWork (work : Execution.Work) : Prop :=
  ∃ (ObjectRef : Type) (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variables : Execution.VariableValues) (fuel : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef) (selections : List Selection),
    ((Execution.executeRootSelectionSetCore schema resolvers variables fuel parentType
        source selections).run
      0).1.work
    = work

/-- The reference queue exposes a conforming observable interface for nonempty executed
work and a valid graph-event source. Node coherence and valid initial notices are derived
from executed work and the concrete constructor, not required from callers or the source.
Witnesses: `createWorkQueueForScheduleConforms_holds` for empty startup, and
`createWorkQueueForScheduleConformsWithStartup_holds` for source-valid startup observations.
Empty work takes the ordinary response branch and never requires a work queue.
-/
def createWorkQueueForScheduleConforms (startup : InitialStartup := {}) : Prop :=
  ∀ work schedule,
    ExecutedWork work
    → work.isEmpty = false
    → schedule.ValidFor work startup
    → (createWorkQueueForSchedule work schedule startup).Conforms work

-----------------------------------------------------------------------------------------
-- `createWorkQueueForSchedule` Nonblocking statement
-----------------------------------------------------------------------------------------

/-- Every admitted output prefix of the reference queue has a finished continuation
in the same source language, for nonempty executed work and a valid nonstalling source.
Witness: `implementationNonblocking_holds` in proofs `Nonblocking`, via the finite
fresh-event budget and exact replay composition. `schedule.NonblockingFor work` is an
explicit queue-boundary assumption; validity alone does not imply nonblocking. This
statement asserts neither host fairness nor completion of every possible host run.
-/
def ImplementationNonblocking : Prop :=
  ∀ work schedule,
    ExecutedWork work
    → work.isEmpty = false
    → schedule.ValidFor work
    → schedule.NonblockingFor work
    → (createWorkQueueForSchedule work schedule).Nonblocking

-----------------------------------------------------------------------------------------
-- Implementation correctness statement at the query level
-----------------------------------------------------------------------------------------

/-- Execute a finite incremental response from a completed root and supplied host inputs.
Return the initial result, emitted updates, and concrete termination flag. The caller has
already selected the incremental branch; input validity is specified separately. Shared
initialization and replay also power the optional cursor, without depending on that API.
-/
def replayIncrementalResponse
    (completed : Execution.Completion (List (Name × Execution.ResponseValue)))
    (inputs : List (List GraphEvent)) (startup : InitialStartup := {})
    : Execution.InitialIncrementalStreamResult
      × List Execution.IncrementalStreamUpdateResult
      × Bool :=
  let response := Execution.selectionSetResultToResponse completed.result
  let (initial, queue, publisher) :=
    initializeIncrementalResponse response completed.work startup
  let (updates, finalQueue, _) := queue.run publisher inputs
  (initial, updates, finalQueue.terminated)

/-- An admitted implementation observation of the nonempty incremental query branch.
Work is derived from execution; `schedule` must be valid for that work. A finite admitted
input history witnesses the result by direct queue/publisher replay and spec mapping.
With `complete = true`, the resulting queue must have terminated; otherwise prefixes may
be interrupted or stalled. This operational predicate assumes neither queue conformance
nor response correctness, and does not depend on the optional cursor API.
-/
def queryScheduleMatches (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variables : Execution.VariableValues) (operation : Operation) (fuel : Nat)
    (root : Execution.ResolverValue ObjectRef) (schedule : EventSource (List GraphEvent))
    (result : Execution.ExecutionObservation)
    (complete : Bool := false)
    : Prop :=
  let completed := queryCompletion schema resolvers variables operation fuel root
  Execution.rootSourceAppliesBool schema operation root = true
  ∧ completed.work.isEmpty = false
  ∧ schedule.ValidFor completed.work
  ∧ ∃ inputs,
      schedule.admissible inputs
      ∧ let (initial, updates, terminated) := replayIncrementalResponse completed inputs
        (complete = true → terminated = true) ∧ result = .incremental initial updates

/-- Every admitted implementation observation supplies the general query-correctness
premises for the reference queue constructor: query-local conformance and faithful
response observation. Complete observations also supply `queryOutcome`;
eventual host termination is not asserted. Work and initialization evidence are derived.
Witness: `implementationCorrect_holds` in proofs `CursorObservation`, via
`createWorkQueueForScheduleConforms_holds` and exact replay. The complete cursor
specialization is `ResponseStreamCursor.queryOutcome` in the same proof module.
-/
def ImplementationCorrect (schema : Schema) (operation : Operation) : Prop :=
  ∀ {ObjectRef : Type} (resolvers : Execution.Resolvers ObjectRef)
    (variables : Execution.VariableValues) (fuel : Nat)
    (root : Execution.ResolverValue ObjectRef)
    (schedule : EventSource (List GraphEvent)) (result : Execution.ExecutionObservation)
    (complete : Bool),
    let createWorkQueue := (createWorkQueueForSchedule · schedule)
    queryScheduleMatches schema resolvers variables operation fuel root schedule result
      complete
    → queryWorkQueueConforms createWorkQueue schema resolvers variables
        operation fuel root
      ∧ queryObservation createWorkQueue schema resolvers variables operation
          fuel root result complete

/-! Correctness is inherited through `ImplementationCorrect`, not restated as
implementation-specific public propositions. The following witnesses, in namespace
`Correctness` under `Proofs/GraphQL/IncrementalDelivery/Correctness/`, apply through the
implementation bridge for ordered declarations and FIFO dispatch:

* Prefixes: `deliveryIDsUnique_holds` (QueryIdentity),
  `deliveryPatchesAnnounced_holds` and `deliveryIDUsageValid_holds` (QueryIDUsage),
  `deliverySlicesDisjoint_holds` (QueryDisjointness).
* Complete outcomes: `deliveryIDsEventuallyComplete_holds` and
  `deliveryIDsCompleteExactlyOnce_holds` (QueryIdentity),
  `deliveryLifecycleValid_holds` (QueryLifecycle).
* Complete, zero-error outcomes: `mergedExecutionEquivalentToBasic_holds`
  (QueryReconstruction), `deliveredResponsePositionsEquivalentToBasic_holds` and
  `basicLeavesDeliveredExactlyOnce_holds` (QueryCoverage).

`ResponseStreamCursor.queryCorrectness` in implementation proofs `CursorCorrectness`
packages the end-to-end ID, slice, lifecycle, and reconstruction consequences. Ordinary
and invalid-root execution remain covered by the general query theorems, not this replay
bridge. `queryOutcomeExists_holds` supplies abstract finite existence; it does not assert
that an arbitrary implementation event source eventually terminates.
-/

-----------------------------------------------------------------------------------------
-- Optional executable cursor API
-----------------------------------------------------------------------------------------

/-- A direct executable cursor: graph-event batch to queue state and optional wire
update. Empty work-event batches do not produce a response event.
-/
structure ResponseStreamCursor where
  queue : State
  publisher : IncrementalPublisher

/-- Package shared response initialization as a resumable cursor. -/
def ResponseStreamCursor.initialize (response : Execution.Response)
    (work : Execution.Work) (startup : InitialStartup := {})
    : Execution.InitialIncrementalStreamResult × ResponseStreamCursor :=
  let (initial, queue, publisher) := initializeIncrementalResponse response work startup
  (initial, ⟨queue, publisher⟩)

/-- Package shared response replay as updates and a resumable cursor. All queue, publisher,
and ID handling lives in `State.run`; this wrapper only repackages its result.
-/
def ResponseStreamCursor.run (cursor : ResponseStreamCursor)
    (batches : List (List GraphEvent))
    : List Execution.IncrementalStreamUpdateResult × ResponseStreamCursor :=
  let (updates, queue, publisher) := cursor.queue.run cursor.publisher batches
  (updates, ⟨queue, publisher⟩)

/-- Consume one host batch online. Shared replay emits at most one response update;
a silent step is not a wire update and does not assert termination.
-/
def ResponseStreamCursor.step (cursor : ResponseStreamCursor) (batch : List GraphEvent)
    : Option Execution.IncrementalStreamUpdateResult × ResponseStreamCursor :=
  let (updates, next) := cursor.run [batch]
  (updates.head?, next)

end ReferenceWorkQueue
end GraphQL.IncrementalDelivery
