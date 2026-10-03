import GraphQL.IncrementalDelivery.Observation

/-! A finite, pure work-queue implementation following the GraphQL.js v17.0.1
WorkQueue architecture.

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

The execution tree repeats contributor descriptors rather than recording new declarations.
Lowering retains each contributor's full ancestor chain, including taskless defer groups,
as parent-first registration candidates. A persistent group-ref registry at integration
recovers first-time registration; removing a live group never permits a later contributor
reference to register it again.
Failure removal additionally retains cancellation refs: newly revealed descendants cannot
treat an absent failed parent as a successfully retired shell.

Differences are localized: finite pure outcomes validate host inputs; errors are counts;
unannounced groups retain failures and unpublished values until normal release or ancestor
cancellation. Released, settled groups drain after their notice carrier in the same batch.
Retained notification records do not keep fully invalidated tasks active: their later
settlements are ignored, without adding errors or integrating child work.
Neither the async runtime nor GraphQL.js's unannounced-failure bug is reproduced.
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

/-- GraphQL.js-shaped `Work`, with group, task, and stream collections. Lowering supplies
candidate registrations for contributors and their ancestors, including taskless groups;
integration excludes already registered refs. Task groups remain contributor references,
including references to groups no longer live.
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

/-- Convert immediate execution work to the GraphQL.js-shaped queue collections. Host
success events supply separately converted child work. `Execution.Work` has no separate
new-group declarations, so each contributor supplies its full ancestor chain as
parent-first registration candidates. Taskless ancestors retain
release and cancellation links without becoming task contributors. `State.addGroups`
excludes previously registered refs; `State.pruneEmptyGroups` silently promotes children
through taskless groups when released.
-/
def Work.fromExecution (work : Execution.Work) (address : Address := []) : Work :=
  match work with
  | .empty => {}
  | .combine left right =>
      (Work.fromExecution left (address ++ [0])).combine
        (Work.fromExecution right (address ++ [1]))
  | .executionGroup groups _ _ _ =>
      {
        groups :=
          groups.flatMap (fun group => groupChain (group.node :: group.ancestors))
        tasks :=
          [⟨.executionGroup address, groups.map Execution.DeferredFragment.node⟩]
      }
  | .stream node _ =>
      { streams := [⟨node⟩] }
where
  /-- Lower a nearest-first node/ancestor chain to parent-first registration candidates. -/
  groupChain : List Execution.DeliveryNode → List Group
    | [] => []
    | node :: ancestors =>
        groupChain ancestors ++ [⟨node, ancestors.head?.map Execution.DeliveryNode.ref⟩]

-----------------------------------------------------------------------------------------
-- WorkQueue `State` definitions
-----------------------------------------------------------------------------------------

/-- GraphQL.js `GroupNode`, with task/child accounting and retained notification state. -/
structure GroupNode where
  group : Group
  childGroups : NodeRefs := []
  tasks : List Occurrence := []
  pending : Nat := 0
  /-- Contributing error total awaiting announcement, unless an ancestor cancels the group. -/
  failure : Option Nat := none
deriving Repr

/-- GraphQL.js `TaskNode`, storing a resolved value until a group flushes it. -/
structure TaskNode where
  task : Task
  value : Option ExecutionGroupValue := none
  childStreams : NodeRefs := []
deriving Repr

/-- The newly integrated roots returned by `maybeIntegrateWork`. -/
structure NewWork where
  newGroups : List Execution.DeliveryNode := []
  newStreams : List Execution.DeliveryNode := []
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
  initialGroups : List Execution.DeliveryNode := []
  initialStreams : List Execution.DeliveryNode := []
  terminated : Bool := false
deriving Repr

/-- Find a group record, including retained failure notifications, by delivery ref. -/
def State.groupNode? (state : State) (ref : NodeRef) : Option GroupNode :=
  state.groupNodes.find? (fun node => node.group.node.ref == ref)

/-- A present group is healthy only when neither it nor an ancestor has failed.
An absent ancestor ends the walk only when it was not retired by failure. Cancellation
refs retain that distinction even when descendants arrive later. Cyclic raw parent links
fail closed at the finite node bound. Announcement is not required for a healthy owner.
-/
def State.groupIsHealthy (state : State) (ref : NodeRef) : Bool :=
  match state.groupNode? ref with
  | none => false
  | some node =>
      node.failure.isNone && ancestorsHealthy state.groupNodes.length node.group.parent
where
  ancestorsHealthy : Nat → Option NodeRef → Bool
    | _, none => true
    | 0, some _ => false
    | fuel + 1, some parent =>
        match state.groupNode? parent with
        | none => !state.cancelledGroups.contains parent
        | some node => node.failure.isNone && ancestorsHealthy fuel node.group.parent

/-- A shared task remains active while at least one contributing owner is healthy.
Records retained only for later notification do not keep a task active.
-/
def State.taskHasHealthyOwner (state : State) (task : Task) : Bool :=
  task.groups.any (fun group => state.groupIsHealthy group.ref)

/-- Find a registered task definition by its structural occurrence. -/
def State.task? (state : State) (occurrence : Occurrence) : Option Task :=
  state.tasks.find? (fun task => task.occurrence == occurrence)

/-- Find a started task's stored value and child streams. -/
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

/-- Register a delivery ref only once, before installing parent links or tasks.
Absence from the live node map does not make a previously registered ref new again.
An already-cancelled parent retires a fresh child immediately, retaining the child's ref
for later descendants without creating a live notification record.
-/
def State.addGroup (state : State) (group : Group) : State :=
  if state.registeredGroups.contains group.node.ref
      || (state.groupNode? group.node.ref).isSome then
    state
  else
    let registered :=
      { state with registeredGroups := state.registeredGroups ++ [group.node.ref] }
    if group.parent.any (fun parent => state.cancelledGroups.contains parent) then
      { registered with cancelledGroups := state.cancelledGroups ++ [group.node.ref] }
    else
      { registered with groupNodes := state.groupNodes ++ [{ group }] }

/-- Register only first-time groups before their tasks, attaching fresh children to their
parents. Reused contributors neither reinstall child links nor become new roots.
Children of previously cancelled parents are retired at registration. If candidates arrive
child-first, the health walk still sees the parent's retained cancellation afterward.
-/
def State.addGroups (state : State) (groups : List Group)
    : State × List Execution.DeliveryNode :=
  let fresh :=
    groups.filter
      (fun group =>
        !state.registeredGroups.contains group.node.ref
        && (state.groupNode? group.node.ref).isNone)
  let withGroups := fresh.foldl State.addGroup state
  let current :=
    fresh.foldl
      (fun current group =>
        match group.parent with
        | none => current
        | some parent =>
            match current.groupNode? parent with
            | none => current
            | some node =>
                let children :=
                  if node.childGroups.contains group.node.ref then
                    node.childGroups
                  else
                    node.childGroups ++ [group.node.ref]
                current.putGroupNode { node with childGroups := children })
      withGroups
  (
    current,
    distinctDeliveryNodes
      (fresh.filterMap
        (fun group =>
          if group.parent.isNone then
            some group.node
          else
            none))
  )

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
alone does not imply emptiness: settled values or a retained failure still need release.
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
            if node.tasks.isEmpty && node.failure.isNone then
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

/-- Start a task by recording its node; host computation remains outside Lean. -/
def State.startTask (state : State) (occurrence : Occurrence) : State :=
  if (state.taskNode? occurrence).isSome then
    state
  else
    match state.task? occurrence with
    | none => state
    | some task => { state with taskNodes := state.taskNodes ++ [{ task }] }

/-- Start a healthy group's tasks; a retained failure needs no further host work. -/
def State.startGroup (state : State) (ref : NodeRef) : State :=
  match state.groupNode? ref with
  | none => state
  | some node =>
      if node.failure.isSome then state else node.tasks.foldl State.startTask state

/-- Register a newly released stream as started; its iterator remains host-owned. -/
def State.startStream (state : State) (ref : NodeRef) : State :=
  if (state.stream? ref).isNone || state.rootStreams.contains ref then
    state
  else
    { state with rootStreams := state.rootStreams ++ [ref] }

/-- Announce and activate newly released group and stream roots. -/
def State.startNewWork (state : State) (newWork : NewWork) : State :=
  let groups := newWork.newGroups.map Execution.DeliveryNode.ref
  let streams := newWork.newStreams.map Execution.DeliveryNode.ref
  let current := { state with rootGroups := state.rootGroups ++ groups }
  let startedGroups := groups.foldl State.startGroup current
  streams.foldl State.startStream startedGroups

/-- The initialization core of GraphQL.js `createWorkQueue`, without host promises.
This constructs concrete state; `createWorkQueueForSchedule` also supplies the observable
interface.
-/
def State.initialize (initialWork : Work) : State :=
  let (integrated, newWork) := ({} : State).maybeIntegrateWork initialWork
  let (pruned, groups) := integrated.pruneEmptyGroups newWork.newGroups
  let roots := { newWork with newGroups := groups }
  let started := pruned.startNewWork roots
  { started with initialGroups := groups, initialStreams := roots.newStreams }

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

/-- GraphQL.js graph-event variants; the host owns their ordering and batch widths. -/
inductive GraphEvent where
  | taskSuccess (task : Occurrence) (result : TaskResult)
  | taskFailure (task : Occurrence) (errors : Nat)
  | streamItems (stream : Execution.DeliveryNode) (items : List StreamItem)
  | streamSuccess (stream : Execution.DeliveryNode)
  | streamFailure (stream : Execution.DeliveryNode) (errors : Nat)
deriving Repr

/-- Task, item, and stream-finalization identities in one graph event. -/
def GraphEvent.identities : GraphEvent → List Occurrence × NodeRefs
  | .taskSuccess task _ | .taskFailure task _ => ([task], [])
  | .streamItems _ items => (items.map StreamItem.occurrence, [])
  | .streamSuccess stream | .streamFailure stream _ => ([], [stream.ref])

/-- Successful task and item occurrences made available by one graph event. -/
def GraphEvent.successes : GraphEvent → List Occurrence
  | .taskSuccess task _ => [task]
  | .streamItems _ items => items.map StreamItem.occurrence
  | _ => []

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
    : State × WorkQueueEvent :=
  (state.removeGroup group.group.node.ref, .groupFailure group.group.node errors)

/-- Drain active groups that already have a failure or all their task settlements.
Call after emitting their notice carrier. Successful closure can release further settled
groups; each iteration removes a live group and creates none, bounding the finite loop.
This release-time drain refines GraphQL.js's handling of settled, unannounced groups.
-/
def State.drainReadyGroups (state : State) : State × List WorkQueueEvent :=
  go state.groupNodes.length state
where
  go : Nat → State → State × List WorkQueueEvent
    | 0, current => (current, [])
    | fuel + 1, current =>
        let ready :=
          current.rootGroups.findSome?
            fun ref => do
              let node ← current.groupNode? ref
              if node.failure.isSome || node.pending == 0 then some node else none
        match ready with
        | none => (current, [])
        | some node =>
            let (next, events) :=
              match node.failure with
              | some errors =>
                  let (next, event) := current.finishGroupFailure node errors
                  (next, [event])
              | none =>
                  let (next, events, released) := current.finishGroupSuccess node
                  (next.startNewWork released, events)
            let (finished, later) := go fuel next
            (finished, events ++ later)

/-- GraphQL.js `taskSuccess`: check task-level healthy ownership, integrate child Work,
then decrement each surviving contributing group in one pass. Only released, nonfailed
groups with no pending tasks finish. Raw `GROUP_VALUES` names the triggering group.
Then activate released work and drain outcomes settled before announcement. A late
settlement with no healthy owner only removes the cancelled task's bookkeeping;
its data, errors, and child work are ignored.
-/
def State.taskSuccess (state : State) (occurrence : Occurrence) (result : TaskResult)
    : State × List WorkQueueEvent :=
  match state.taskNode? occurrence with
  | none => (state, [])
  | some taskNode =>
      if !state.taskHasHealthyOwner taskNode.task then
        (state.removeTask occurrence, [])
      else
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
                  if current.rootGroups.contains group.ref
                      && node.pending == 0
                      && node.failure.isNone then
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
        let (drained, later) := (current.startNewWork released).drainReadyGroups
        (drained, events ++ later)

/-- Process one failed task. Announced owners emit failure immediately; unannounced
owners accumulate contributing errors until normal release or ancestor cancellation.
Remove the failed task's membership without discarding surviving owners' error outcomes.
Check healthy ownership once, before this settlement changes any owner. A fully invalidated
task adds no errors; a task with a healthy owner can still contribute to retained totals.
-/
def State.taskFailure (state : State) (occurrence : Occurrence) (errors : Nat)
    : State × List WorkQueueEvent :=
  match state.taskNode? occurrence with
  | none => (state, [])
  | some taskNode =>
      if !state.taskHasHealthyOwner taskNode.task then
        (state.removeTask occurrence, [])
      else
        let current := state.removeTask occurrence
        taskNode.task.groups.foldl
          (fun (current, events) group =>
            match current.groupNode? group.ref with
            | none => (current, events)
            | some node =>
                if current.rootGroups.contains group.ref then
                  let (next, failure) := current.finishGroupFailure node errors
                  (next, events ++ [failure])
                else
                  let node :=
                    {
                      node with
                        pending := node.pending - 1
                        failure := some (node.failure.getD 0 + errors)
                    }
                  (current.putGroupNode node, events))
          (current, [])

/-- Integrate each item result's child Work and emit one raw `STREAM_VALUES` event. -/
def State.streamItems (state : State) (stream : Execution.DeliveryNode)
    (items : List StreamItem)
    : State × List WorkQueueEvent :=
  if !state.rootStreams.contains stream.ref then
    (state, [])
  else
    let (current, groups, streams, values) :=
      items.foldl
        (fun (current, groups, streams, values) item =>
          let (integrated, newWork) := current.maybeIntegrateWork item.work
          let (pruned, nonempty) := integrated.pruneEmptyGroups newWork.newGroups
          (
            pruned.startNewWork { newWork with newGroups := nonempty },
            groups ++ nonempty,
            streams ++ newWork.newStreams,
            values ++ [item.value]
          ))
        (state, [], [], [])
    let (drained, later) := current.drainReadyGroups
    (drained, .streamValues stream values groups streams :: later)

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

/-- Dispatch one GraphQL.js graph event to the corresponding queue handler. -/
def State.handleGraphEvent (state : State) : GraphEvent → State × List WorkQueueEvent
  | .taskSuccess task result => state.taskSuccess task result
  | .taskFailure task errors => state.taskFailure task errors
  | .streamItems stream items => state.streamItems stream items
  | .streamSuccess stream => state.streamSuccess stream
  | .streamFailure stream errors => state.streamFailure stream errors

/-- The host may report only a task or stream already started by WorkQueue. -/
def State.acceptsGraphEvent (state : State) : GraphEvent → Bool
  | .taskSuccess task _ | .taskFailure task _ => (state.taskNode? task).isSome
  | .streamItems stream _ | .streamSuccess stream | .streamFailure stream _ =>
      state.rootStreams.contains stream.ref

/-- Check start eligibility sequentially inside one available graph-event batch. -/
def State.acceptsBatch : State → List GraphEvent → Bool
  | _, [] => true
  | state, event :: rest =>
      state.acceptsGraphEvent event && (state.handleGraphEvent event).1.acceptsBatch rest

/-- GraphQL.js `handleGraphEvents`: process one available batch, then terminate when
both root collections are empty. Queue event batching follows the input batches.
-/
def State.handleGraphEvents (state : State) (graphEvents : List GraphEvent)
    : State × List WorkQueueEvent :=
  if state.terminated then
    (state, [])
  else
    let (current, events) :=
      graphEvents.foldl
        (fun (current, events) event =>
          let (next, produced) := current.handleGraphEvent event
          (next, events ++ produced))
        (state, [])
    if current.rootGroups.isEmpty && current.rootStreams.isEmpty then
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

/-- Project an initialized queue onto normalized work-event batches using shared replay.
-/
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
    (source : EventSource (List GraphEvent))
    : Execution.WorkQueue :=
  let queue := State.initialize (Work.fromExecution work)
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
    : Execution.InitialIncrementalStreamResult × State × IncrementalPublisher :=
  let queue := State.initialize (Work.fromExecution work)
  let (initial, ids) :=
    Execution.initializeIncrementalResponse response queue.initialGroups
      queue.initialStreams
  let publisher : IncrementalPublisher :=
    { ids, active := queue.initialGroups ++ queue.initialStreams }
  (initial, queue, publisher)

/-- Replay supplied inputs and map their normalized batches to response updates.
`Execution.mapWorkEventBatch` maps each emitted batch using the publisher's ID state.
The residual queue and publisher retain all state needed for resumption. Queue processing
is shared with `runWithPublisher`.
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

/-- Child work expected after a successful execution-group task. -/
def taskChildWork? (work : Execution.Work) : Occurrence → Option Work
  | .executionGroup address => do
      let location ← locateWork work address
      match location.current with
      | .executionGroup _ _ _ children =>
          some (Work.fromExecution children (address ++ [0]))
      | _ => none
  | .item _ _ => none

/-- Exact contributor descriptors expected for an execution-group task. -/
def taskGroups? (work : Execution.Work)
    : Occurrence → Option (List Execution.DeliveryNode)
  | .executionGroup address => do
      let location ← locateWork work address
      match location.current with
      | .executionGroup groups _ _ _ =>
          some (groups.map Execution.DeferredFragment.node)
      | _ => none
  | .item _ _ => none

/-- Child work expected after one successful stream item. -/
def streamItemWork? (work : Execution.Work) : Occurrence → Option Work
  | .item address index => do
      let location ← locateWork work address
      match location.current with
      | .stream _ items =>
          let (_, children) ← items[index]?
          some (Work.fromExecution children (address ++ [index]))
      | _ => none
  | .executionGroup _ => none

/-- Items already reported for one stream in the preceding graph-event prefix. -/
def GraphEvent.itemsBefore (before : List GraphEvent) (ref : NodeRef) : List StreamItem :=
  before.flatMap
    fun event =>
      match event with
      | .streamItems stream items => if stream.ref == ref then items else []
      | _ => []

/-- A graph event uses fresh task/item identities and closes each stream at most once. -/
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
        ∧ ∃ children, (.error errors, children) ∈ items

/-- Producers settle before dependent work; stream-item batches advance in order and
success follows all modeled items. Host fairness is deliberately not assumed.
-/
def GraphEvent.Ready (work : Execution.Work) (before : List GraphEvent)
    : GraphEvent → Prop
  | .taskSuccess occurrence _ | .taskFailure occurrence _ =>
      ∃ owners producer payload,
        TaskAt work occurrence owners producer payload
        ∧ ∀ source, producer = some source → source ∈ before.flatMap GraphEvent.successes
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
        ∧ ∃ children,
            results[(GraphEvent.itemsBefore before stream.ref).length]?
            = some (.error errors, children)

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

/-- Check the host's start/stop discipline without constraining output accounting. -/
def inputsStarted (work : Execution.Work) (batches : List (List GraphEvent)) : Bool :=
  (batches.foldl
    (fun (state, valid) batch =>
      let next := (state.handleGraphEvents batch).1
      (next, valid && !state.terminated && !batch.isEmpty && state.acceptsBatch batch))
    (State.initialize (Work.fromExecution work), true)).2

end ReferenceWorkQueue

namespace EventSource

open ReferenceWorkQueue

/-- A fresh, prefix-closed graph-event source whose admitted batches match `work` and
respect the queue's start/stop requests. Fixed payloads, revealed child work, fresh
identities, producer order, and stream-item order come from `ValidGraphEvents`; start
discipline comes from `inputsStarted`. Neither initial-notice correctness, output-history
admission, nor host fairness is assumed here. Queue state determines output termination,
independently of the host source's `finished` predicate.
-/
def ValidFor (schedule : EventSource (List GraphEvent)) (work : Execution.Work) : Prop :=
  schedule.history = []
  ∧ schedule.admissible []
  ∧ (∀ before after,
      before.IsPrefix after → schedule.admissible after → schedule.admissible before)
  ∧ (∀ batches,
      schedule.admissible batches
      → ValidGraphEvents work batches.flatten ∧ inputsStarted work batches = true)

end EventSource

namespace ReferenceWorkQueue

/-- The reference queue exposes a conforming observable interface for nonempty executed
work and a valid graph-event source. Node coherence and valid initial notices are derived
from executed work and the concrete constructor, not required from callers or the source.
Witness: `ReferenceWorkQueue.createWorkQueueForScheduleConforms_holds`. Empty work takes
the ordinary response branch and never requires a work queue.
-/
def createWorkQueueForScheduleConforms : Prop :=
  ∀ work schedule,
    ExecutedWork work
    → work.size ≠ 0
    → schedule.ValidFor work
    → (createWorkQueueForSchedule work schedule).Conforms work

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
    (inputs : List (List GraphEvent))
    : Execution.InitialIncrementalStreamResult
      × List Execution.IncrementalStreamUpdateResult
      × Bool :=
  let response := Execution.selectionSetResultToResponse completed.result
  let (initial, queue, publisher) := initializeIncrementalResponse response completed.work
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
  ∧ completed.work.size ≠ 0
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
implementation-specific public propositions. The following witnesses are in namespace
`Correctness`, under `Proofs/GraphQL/IncrementalDelivery/Correctness/`:

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
    (work : Execution.Work)
    : Execution.InitialIncrementalStreamResult × ResponseStreamCursor :=
  let (initial, queue, publisher) := initializeIncrementalResponse response work
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
