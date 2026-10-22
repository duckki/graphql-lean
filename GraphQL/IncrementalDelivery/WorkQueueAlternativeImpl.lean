import GraphQL.IncrementalDelivery.WorkQueueImplementation

/-! Reference-backed queue with affected-work projections and inline disposal observations.

Execution.Work, counted values, graph events, lowering, and accounting records are shared
with the reference. Registration returns only newly active/rejected task projections;
activation follows whole-work handoff. Failure removal updates live ownership and collects
cleanup in the same affected-subtree walk; successful release stays shared.
Host observations describe acknowledgement, deduplicated disposal, and reader retirement,
not promises, buffer containers, executor allocation, planning caches, or native errors.

The same EventSource.ValidFor contract governs finite replay. Stop is distinct from work
termination: an interrupted reader does not manufacture a completed query.
The public conformance/replay propositions use the reference's generated-work and source
premises. Their witnesses live in Proofs; concrete host refinement remains a separate
obligation. See the porting guide for implementation choices and scope boundaries.

Group/source registration, task unlinking, empty-shell pruning, successful release,
rejection replay and publication reuse ReferenceWorkQueue. Only transitions that register
new task projections or dispose failed ownership are specialized here.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue

open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics (NodeRefs Occurrence)

-----------------------------------------------------------------------------------------
-- Shared work, graph input, and closure state
-----------------------------------------------------------------------------------------

abbrev Work := Execution.Work
abbrev ExecutionGroupValue := Execution.ExecutionGroupValue
abbrev StreamItemValue := Execution.StreamItemValue
abbrev GraphEvent := ReferenceWorkQueue.GraphEvent

/-- The shared kernel plus an interruption guard. No permanent per-item effect ledger. -/
structure State where
  /-- Root membership, group/task/source records, and failure knowledge from the shared
  kernel. Retained catalogues support finite accounting rather than prescribing containers.
  -/
  queue : ReferenceWorkQueue.State
  /-- Closed graph reader, not necessarily completed semantic work. -/
  stopped : Bool := false
deriving Repr

-----------------------------------------------------------------------------------------
-- Cleanup identities and inline operation vocabulary
-----------------------------------------------------------------------------------------

/-- Task/source cleanup identities, distinct from payload records.
Paths and wire IDs are not cleanup identities.
-/
inductive CleanupTarget where
  | task (occurrence : Occurrence)
  | stream (key : Nat)
deriving DecidableEq, BEq, Repr

/-- Ordered observations, not commands buffered until after the transition. Pending promises,
reasons and exceptional unwinding belong to the host refinement, not this vocabulary.
-/
inductive HostEffect where
  /-- Transfer the producer's exposed work after whole-work registration. -/
  | adopt (producer : Occurrence)
  /-- Acknowledge one consumed stream-item receipt, not global source completion. -/
  | acknowledge (stream : Nat)
  /-- Request cancellation of the identified computation. -/
  | abortTask (task : Occurrence)
  /-- Request cancellation of the identified source producer. -/
  | cancelSource (stream : Nat)
  /-- Abort the source's item queue after producer cancellation. -/
  | abortStreamQueue (stream : Nat)
  /-- Start response completion notification; this does not assert effect quiescence. -/
  | responseFinished
deriving Repr

/-- Deduplicate cleanup identities in first-encounter order; no persistent resource ledger. -/
def uniqueCleanupTargets (targets : List CleanupTarget) : List CleanupTarget :=
  targets.foldl
    (fun unique target =>
      if unique.contains target then unique else unique ++ [target]) []

-----------------------------------------------------------------------------------------
-- Cancellation helpers and whole-queue teardown
-----------------------------------------------------------------------------------------

/-- Pure cancelTask observation: abort identity, then held child-stream identities.
The caller deduplicates these targets and expands their operations with CleanupTarget.effects;
no callbacks run in Lean. An unstarted computation still contributes its abort identity;
an already rejected computation needs no further abort.
-/
def State.cancelTask (state : State) (occurrence : Occurrence) : List CleanupTarget :=
  let task := state.queue.taskNode? occurrence
  let abort :=
    if task.any (fun node => node.rejection.isSome) then [] else [.task occurrence]
  abort ++ task.toList.flatMap (fun node => node.childStreams.map CleanupTarget.stream)

/-- Request producer cancellation before aborting its item queue.
Temporary identity deduplication belongs to the enclosing cancellation pass.
-/
def cancelStream (key : Nat) : List HostEffect :=
  [.cancelSource key, .abortStreamQueue key]

/-- Shared cancelTask/cancelStream operation blocks. Source failure uses cancelSource alone. -/
def CleanupTarget.effects : CleanupTarget → List HostEffect
  | .task occurrence => [.abortTask occurrence]
  | .stream key => cancelStream key

/-- Task-before-child walk gathering cancellation identities.
pending is the remaining group frontier: seed one group or the ordered root forest.
Fuel totalizes malformed raw graphs.
-/
def State.cancelGroup (state : State)
    : Nat → NodeRefs → List CleanupTarget → List CleanupTarget
  | 0, _, targets => targets
  | _ + 1, [], targets => targets
  | fuel + 1, key :: rest, targets =>
      match state.queue.groupNode? key with
      | none => state.cancelGroup (fuel + 1) rest targets
      | some group =>
          let targets :=
            group.tasks.foldl
              (fun targets occurrence =>
                targets ++ state.cancelTask occurrence) targets
          state.cancelGroup fuel (group.childGroups ++ rest) targets
termination_by fuel pending _ => (fuel, pending.length)

/-- All targets requested by cancel: cancelGroup over roots, then the root stream sources. -/
def State.cleanupTargets (state : State) : List CleanupTarget :=
  let owned :=
    state.cancelGroup (state.queue.groupNodes.length + 1) state.queue.rootGroups []
  uniqueCleanupTargets (owned ++ state.queue.rootStreams.map CleanupTarget.stream)

/-- Clear queue accounting on cancellation, preserving initial notices and termination.
In particular, abrupt stop leaves terminated=false unless the work had already finished.
-/
def State.clearRecords (state : State) : State :=
  {
    queue :=
      {
        initialGroups := state.queue.initialGroups
        initialStreams := state.queue.initialStreams
        terminated := state.queue.terminated
      }
    stopped := true
  }

/-- Request cleanup and clear state on abrupt cancellation or normal graph-reader stop.
Host-owned unadmitted work and pending effects require the ownership refinement in the guide.
-/
def State.cancel (state : State) : State × List HostEffect :=
  if state.stopped then
    (state, [])
  else
    let effects := state.cleanupTargets.flatMap CleanupTarget.effects
    (state.clearRecords, effects)

-----------------------------------------------------------------------------------------
-- Registering exposed work: `addTask`, `maybeIntegrateWork`, and `startNewWork`
-----------------------------------------------------------------------------------------

/-- Classification from the task registration owner loop.
Dormant live owners still register work; removed owners do not. Active work starts only after complete registration.
-/
inductive TaskRegistration where
  | active
  | registered
  | rejected
deriving DecidableEq, BEq, Repr

/-- Released roots plus two temporary projections of this scope's tasks.
Ordinary dormant registered tasks need no returned list. These are neither whole-queue
indices nor retained histories; the caller consumes them at this integration boundary.
-/
structure IntegratedWork where
  newGroups : List Execution.DeliveryNode := []
  newStreams : List Execution.DeliveryNode := []
  activeTasks : List ReferenceWorkQueue.Task := []
  rejectedTasks : List ReferenceWorkQueue.Task := []
deriving Repr

/-- Shared release vocabulary; task projections do not enter wire notices. -/
def IntegratedWork.newWork (integrated : IntegratedWork) : ReferenceWorkQueue.NewWork :=
  ⟨integrated.newGroups, integrated.newStreams⟩

/-- Register every surviving contributor and classify the task in the same owner traversal.
No computation node is started here. The reference's permanent task catalogue is retained
as shared accounting evidence; registration does not change catalogue lifetime.
-/
def State.addTask (state : State) (task : ReferenceWorkQueue.Task)
    : State × TaskRegistration :=
  let queue := { state.queue with tasks := state.queue.tasks ++ [task] }
  let (queue, registered, active) :=
    task.groups.foldl
      (fun (current, registered, active) group =>
        match current.groupNode? group.ref with
        | none => (current, registered, active)
        | some node =>
            let current :=
              if node.tasks.contains task.occurrence then
                current
              else
                current.putGroupNode
                  {
                    node with
                      tasks := node.tasks ++ [task.occurrence],
                      pending := node.pending + 1
                  }
            (current, true, active || current.rootGroups.contains group.ref))
      (queue, false, false)
  let disposition :=
    if active then
      TaskRegistration.active
    else if registered then
      .registered
    else
      .rejected
  ({ state with queue }, disposition)

/-- Register groups, then tasks, then streams exactly once for this exposed scope.
Only active/rejected tasks are returned, in scope order; adoption and starts are separate.
-/
def State.maybeIntegrateWork (state : State) (work : ReferenceWorkQueue.Work)
    (parentTask : Option Occurrence := none)
    : State × IntegratedWork :=
  let (queue, newGroups) := state.queue.addGroups work.groups
  let (current, activeTasks, rejectedTasks) :=
    work.tasks.foldl
      (fun (current, activeTasks, rejectedTasks) task =>
        let (current, disposition) := current.addTask task
        match disposition with
        | .active => (current, activeTasks ++ [task], rejectedTasks)
        | .registered => (current, activeTasks, rejectedTasks)
        | .rejected => (current, activeTasks, rejectedTasks ++ [task]))
      ({ state with queue }, [], [])
  let (queue, newStreams) := current.queue.addStreams work.streams parentTask
  ({ current with queue }, ⟨newGroups, newStreams, activeTasks, rejectedTasks⟩)

/-- Dispose only the rejected projection, without another owner test or registration pass.
The temporary targets carry first-encounter deduplication across items in this dispatch.
An unstarted task contributes its abort identity without evaluating its latent work.
-/
def State.disposeRejectedTasks (state : State) (integrated : IntegratedWork)
    (targets : List CleanupTarget := [])
    : List CleanupTarget :=
  uniqueCleanupTargets
    (targets
      ++ integrated.rejectedTasks.flatMap (fun task => state.cancelTask task.occurrence))

/-- Install all released root/source ownership before disposal or activation. Then dispose
rejected tasks and start only newly active tasks plus tasks belonging to released roots.
Targets observe inline disposal, not commands delayed until after host computations start.
Root membership represents stream activation; native callbacks remain outside this model.
-/
def State.startNewWork (state : State) (newWork : ReferenceWorkQueue.NewWork)
    (integrated : IntegratedWork := {}) (targets : List CleanupTarget := [])
    : State × List CleanupTarget :=
  if state.stopped then
    (state, targets)
  else
    let groups := newWork.newGroups.map Execution.DeliveryNode.ref
    let queue := { state.queue with rootGroups := state.queue.rootGroups ++ groups }
    let queue :=
      newWork.newStreams.foldl (fun current stream => current.startStream stream.ref)
        queue
    let installed := { state with queue }
    let targets := installed.disposeRejectedTasks integrated targets
    let queue :=
      integrated.activeTasks.foldl (fun current task => current.startTask task.occurrence)
        queue
    let queue := groups.foldl ReferenceWorkQueue.State.startGroup queue
    ({ state with queue }, targets)

/-- Startup uses the same registration projections and activation ordering as later work.
The finite factory exposes initial notices, not initialization effects; generated initial
work has live contributors. Construction evaluates no host computations or future schedule.
-/
def State.initialize (work : Work) : State :=
  let (integrated, newWork) :=
    ({ queue := {} } : State).maybeIntegrateWork
      (ReferenceWorkQueue.Work.fromExecution work)
  let (queue, groups) := integrated.queue.pruneEmptyGroups newWork.newGroups
  let roots := { newWork.newWork with newGroups := groups }
  let (started, _) := ({ integrated with queue }).startNewWork roots newWork
  {
    started with
      queue :=
        { started.queue with initialGroups := groups, initialStreams := roots.newStreams }
  }

-----------------------------------------------------------------------------------------
-- Failure removal and last-owner disposal: `removeGroup` and `finishGroupFailure`
-----------------------------------------------------------------------------------------

/-- Remove each live owner, dispose its last-owned tasks before unlinking,
then visit its children. State and cleanup come from this one walk, not replayed registration
or a scan of final wire events. Failed-but-live co-owners still prevent disposal.

The temporary targets retain first-encounter order across the enclosing dispatch. Removed
keys accumulate in the reference's reverse-preorder bookkeeping order.
Fuel totalizes malformed graphs.
-/
def State.removeGroup (state : State) (key : Nat) (targets : List CleanupTarget := [])
    : State × List CleanupTarget :=
  let (current, removed, targets) :=
    walk (state.queue.groupNodes.length + 1) state [key] [] targets
  (
    {
      current with
        queue :=
          {
            current.queue with
              cancelledGroups := current.queue.cancelledGroups ++ removed
          }
    },
    targets
  )
where
  walk
      : Nat → State → NodeRefs → NodeRefs → List CleanupTarget
        → State × NodeRefs × List CleanupTarget
    | 0, current, _, removed, targets => (current, removed, targets)
    | _ + 1, current, [], removed, targets => (current, removed, targets)
    | fuel + 1, current, key :: rest, removed, targets =>
        match current.queue.groupNode? key with
        | none => walk (fuel + 1) current rest removed targets
        | some group =>
            let current :=
              {
                current with
                  queue :=
                    {
                      current.queue with
                        groupNodes :=
                          current.queue.groupNodes.filter
                            (fun node => node.group.node.ref != key)
                        rootGroups := current.queue.rootGroups.filter (· != key)
                    }
              }
            let (current, targets) :=
              group.tasks.foldl
                (fun (current, targets) occurrence =>
                  match current.queue.task? occurrence with
                  | none => (current, targets)
                  | some task =>
                      if task.groups.all
                          (fun owner => (current.queue.groupNode? owner.ref).isNone) then
                        let targets :=
                          uniqueCleanupTargets (targets ++ current.cancelTask occurrence)
                        (
                          { current with queue := current.queue.removeTask occurrence },
                          targets
                        )
                      else
                        (current, targets)) (current, targets)
            walk fuel current (group.childGroups ++ rest) (key :: removed) targets
  termination_by fuel _ pending _ _ => (fuel, pending.length)

/-- Close the failed wire owner using the same removal that supplies its inline cleanup. -/
def State.finishGroupFailure (state : State) (group : ReferenceWorkQueue.GroupNode)
    (errors : Nat) (targets : List CleanupTarget := [])
    : State × WorkQueueEvent × List CleanupTarget :=
  let (state, targets) := state.removeGroup group.group.node.ref targets
  (state, .groupFailure group.group.node errors, targets)

-----------------------------------------------------------------------------------------
-- Failed task settlement: `taskFailure`
-----------------------------------------------------------------------------------------

/-- Retain the computation's rejection and close active owners with inline disposal.
Dormant owners keep the task for replay when started, matching the shared reference path.
The already rejected task is not aborted again, and its child work is not adopted.
-/
def State.taskFailure (state : State) (occurrence : Occurrence) (errors : Nat)
    (targets : List CleanupTarget := [])
    : State × List WorkQueueEvent × List CleanupTarget :=
  match state.queue.taskNode? occurrence with
  | none => (state, [], targets)
  | some task =>
      let queue := state.queue.putTaskNode { task with rejection := some errors }
      task.task.groups.foldl
        (fun (current, events, targets) group =>
          match current.queue.groupNode? group.ref with
          | none => (current, events, targets)
          | some node =>
              if current.queue.rootGroups.contains group.ref then
                let (next, failure, targets) :=
                  current.finishGroupFailure node errors targets
                (next, events ++ [failure], targets)
              else
                (current, events, targets))
        ({ state with queue }, [], targets)

-----------------------------------------------------------------------------------------
-- Ready draining with shared successful release and fused failed removal
-----------------------------------------------------------------------------------------

/-- The reference readiness order and successful release rules, with cleanup carried through
each actual failed removal. Newly released task rejections use the same path as direct
failures. The temporary target prefix can include earlier registration disposal.
-/
def State.drainReadyGroups (state : State) (targets : List CleanupTarget := [])
    : State × List WorkQueueEvent × List CleanupTarget :=
  go state.queue.groupNodes.length state targets
where
  go : Nat → State → List CleanupTarget → State × List WorkQueueEvent × List CleanupTarget
    | 0, current, targets => (current, [], targets)
    | fuel + 1, current, targets =>
        let ready :=
          current.queue.rootGroups.findSome?
            fun key => do
              let node ← current.queue.groupNode? key
              if (current.queue.rejectedTask? node).isSome || node.pending == 0 then
                some node
              else
                none
        match ready with
        | none => (current, [], targets)
        | some node =>
            let (next, events, targets) :=
              match current.queue.rejectedTask? node with
              | some (occurrence, errors) => current.taskFailure occurrence errors targets
              | none =>
                  let (queue, events, released) := current.queue.finishGroupSuccess node
                  let (next, targets) :=
                    ({ current with queue }).startNewWork released {} targets
                  (next, events, targets)
            let (finished, later, targets) := go fuel next targets
            (finished, events ++ later, targets)

-----------------------------------------------------------------------------------------
-- Registration-bearing handlers: `taskSuccess` and `streamItems`
-----------------------------------------------------------------------------------------

/-- Stage and register one accepted task result, then settle its direct owners using the
shared success/release primitives. Whole-work handoff precedes rejected-task disposal and
activation. The newly active subset needs no second owner scan. Ready draining carries
failure disposal from the actual ownership transition, not a reconstructed snapshot.
-/
def State.taskSuccess (state : State) (occurrence : Occurrence)
    (result : ReferenceWorkQueue.TaskResult)
    : State × List WorkQueueEvent × List HostEffect :=
  match state.queue.taskNode? occurrence with
  | none => (state, [], [])
  | some task =>
      let state :=
        {
          state with
            queue := state.queue.putTaskNode { task with value := some result.value }
        }
      let (integrated, newWork) := state.maybeIntegrateWork result.work (some occurrence)
      let initial
          : ReferenceWorkQueue.State × List WorkQueueEvent × ReferenceWorkQueue.NewWork :=
        (integrated.queue, [], {})
      let (queue, events, released) :=
        task.task.groups.foldl
          (fun (current, events, released) group =>
            match current.groupNode? group.ref with
            | none => (current, events, released)
            | some node =>
                let node := { node with pending := node.pending - 1 }
                let current := current.putGroupNode node
                if current.rootGroups.contains group.ref && node.pending == 0 then
                  let (next, finished, roots) := current.finishGroupSuccess node
                  (
                    next,
                    events ++ finished,
                    ⟨
                      released.newGroups ++ roots.newGroups,
                      released.newStreams ++ roots.newStreams
                    ⟩
                  )
                else
                  (current, events, released)) initial
      let (started, targets) := ({ integrated with queue }).startNewWork released newWork
      let (finished, later, targets) := started.drainReadyGroups targets
      (
        finished,
        events ++ later,
        [.adopt occurrence] ++ targets.flatMap CleanupTarget.effects
      )

/-- Admit each item in FIFO order: register once, adopt, dispose rejected tasks and activate
that item's released work before the next item. Temporary cleanup identities span this
receipt; acknowledgement follows all item handoffs/disposal, including an ignored receipt.
Acknowledgement ends item consumption; the ready drain's failure cleanup follows that
receipt-consumption boundary. Wire order keeps STREAM_VALUES first.
-/
def State.streamItems (state : State) (stream : Execution.DeliveryNode)
    (items : List ReferenceWorkQueue.StreamItem)
    : State × List WorkQueueEvent × List HostEffect :=
  if !state.queue.rootStreams.contains stream.ref then
    (state, [], [.acknowledge stream.ref])
  else
    let initial
        : State
          × List Execution.DeliveryNode
          × List Execution.DeliveryNode
          × List StreamItemValue
          × List CleanupTarget
          × List HostEffect :=
      (state, [], [], [], [], [])
    let (current, groups, streams, values, targets, effects) :=
      items.foldl
        (fun (current, groups, streams, values, targets, effects) item =>
          let (integrated, newWork) := current.maybeIntegrateWork item.work
          let (queue, nonempty) := integrated.queue.pruneEmptyGroups newWork.newGroups
          let (started, nextTargets) :=
            ({ integrated with queue }).startNewWork
              { newWork.newWork with newGroups := nonempty } newWork targets
          (
            started,
            groups ++ nonempty,
            streams ++ newWork.newStreams,
            values ++ [item.value],
            nextTargets,
            effects
            ++ [.adopt item.occurrence]
            ++ (nextTargets.drop targets.length).flatMap CleanupTarget.effects
          )) initial
    let (finished, later, allTargets) := current.drainReadyGroups targets
    (
      finished,
      .streamValues stream values groups streams :: later,
      effects
      ++ [.acknowledge stream.ref]
      ++ (allTargets.drop targets.length).flatMap CleanupTarget.effects
    )

-----------------------------------------------------------------------------------------
-- Graph dispatch and FIFO batch consumption: `handleGraphEvents`
-----------------------------------------------------------------------------------------

/-- Registration handlers return inline effects; failed-task cleanup targets are expanded
at dispatch. Source closure remains shared; source failure cancels its producer without
aborting the stream Queue or cancelling already admitted descendants.
-/
def State.handleGraphEvent (state : State) (event : GraphEvent)
    : State × List WorkQueueEvent × List HostEffect :=
  match event with
  | .taskSuccess occurrence result => state.taskSuccess occurrence result
  | .taskFailure occurrence errors =>
      let (state, events, targets) := state.taskFailure occurrence errors
      (state, events, targets.flatMap CleanupTarget.effects)
  | .streamItems stream items => state.streamItems stream items
  | _ =>
      let effects :=
        match event with
        | .streamFailure stream _ =>
            if state.queue.rootStreams.contains stream.ref then
              [.cancelSource stream.ref]
            else
              []
        | _ => []
      let (queue, events) := state.queue.handleGraphEvent event
      ({ state with queue }, events, effects)

/-- Pure counterpart of closure-state updates, accumulated workQueueEvents, and inline effects.
This is a batch-fold result, not another host or wire event buffer.
-/
structure GraphBatchResult where
  state : State
  workQueueEvents : List WorkQueueEvent := []
  effects : List HostEffect := []
deriving Repr

/-- One iteration of the graph-event dispatch loop. Both registration and failure
disposal return their effects with the real reduction; there is no replayed cleanup observer.
Host effects are inline observations, not commands.
-/
def GraphBatchResult.handleGraphEvent (result : GraphBatchResult) (event : GraphEvent)
    : GraphBatchResult :=
  let (state, events, effects) := result.state.handleGraphEvent event
  {
    state
    workQueueEvents := result.workQueueEvents ++ events
    effects := result.effects ++ effects
  }

/-- Consume the available FIFO inputs into workQueueEvents.
Empty roots stop the graph source and emit WORK_QUEUE_TERMINATION; abrupt stop emits none.
The host chooses batch width, so this imposes no one-publication-per-host-event rule.
-/
def State.handleGraphEvents (state : State) (batch : List GraphEvent)
    : GraphBatchResult :=
  if state.stopped || state.queue.terminated then
    { state }
  else
    let reduced := batch.foldl GraphBatchResult.handleGraphEvent { state }
    let queue := reduced.state.queue
    if queue.rootGroups.isEmpty && queue.rootStreams.isEmpty then
      let ending := { reduced.state with queue := { queue with terminated := true } }
      let (state, cleanup) := ending.cancel
      {
        state,
        workQueueEvents := reduced.workQueueEvents ++ [.workQueueTermination],
        effects := reduced.effects ++ cleanup
      }
    else
      reduced

-----------------------------------------------------------------------------------------
-- `createWorkQueueForSchedule` interface
-----------------------------------------------------------------------------------------

/-- Finite normalized replay reuses reference owner selection. Host effects are not wire events. -/
def State.runNormalized (state : State) (batches : List (List GraphEvent))
    : State × List (List WorkQueueEvent) :=
  let publisher : ReferenceWorkQueue.IncrementalPublisher :=
    { active := state.queue.initialGroups ++ state.queue.initialStreams }
  let (state, _, outputs) :=
    batches.foldl
      (fun (state, publisher, outputs) batch =>
        let next := state.handleGraphEvents batch
        if next.workQueueEvents.isEmpty then
          (next.state, publisher, outputs)
        else
          let (publisher, events) := publisher.normalizeBatch next.workQueueEvents
          (next.state, publisher, outputs ++ [events]))
      (state, publisher, [])
  (state, outputs)

/-- Observable queue interface using the shared opaque finite source.
The schedule supplies available batches; no host promises or chosen future enter Work.
-/
def createWorkQueueForSchedule (work : Work) (schedule : EventSource (List GraphEvent))
    : Execution.WorkQueue :=
  let queue := State.initialize work
  {
    initialGroups := queue.queue.initialGroups
    initialStreams := queue.queue.initialStreams
    workEventStream :=
      {
        admissible :=
          fun outputs =>
            ∃ inputs,
              schedule.admissible inputs ∧ (queue.runNormalized inputs).2 = outputs
        finished :=
          fun outputs =>
            ∃ inputs,
              schedule.admissible inputs
              ∧ let (final, emitted) := queue.runNormalized inputs
                emitted = outputs ∧ final.queue.terminated = true
      }
  }

-----------------------------------------------------------------------------------------
-- `createWorkQueueForSchedule` conformance statement
-----------------------------------------------------------------------------------------

/-- Same independent WorkQueue contract and caller premises as the reference implementation. -/
def createWorkQueueForScheduleConforms : Prop :=
  ∀ work schedule,
    ReferenceWorkQueue.ExecutedWork work
    → work.size ≠ 0
    → schedule.ValidFor work
    → (createWorkQueueForSchedule work schedule).Conforms work

-----------------------------------------------------------------------------------------
-- Response reader: `IncrementalPublisher.buildResponse` and abrupt close
-----------------------------------------------------------------------------------------

/-- Optional finite response reader, not another queue interface. -/
structure ResponseStreamCursor where
  queue : State
  publisher : ReferenceWorkQueue.IncrementalPublisher
  finished : Bool := false
deriving Repr

/-- Mark the reader finished and clear publisher records, preserving the ID counter.
close/handleBatch enforce the once-only guard and observe the hook after this update.
-/
def ResponseStreamCursor.onWorkQueueFinished (cursor : ResponseStreamCursor)
    : ResponseStreamCursor :=
  {
    cursor with
      publisher :=
        {
          cursor.publisher with
            ids := { cursor.publisher.ids with ids := [] }, active := []
        }
      finished := true
  }

/-- Initial response and pending IDs, reused from Execution's response initializer. -/
def ResponseStreamCursor.buildResponse (response : Execution.Response) (work : Work)
    : Execution.InitialIncrementalStreamResult × ResponseStreamCursor :=
  let queue := State.initialize work
  let (initial, ids) :=
    Execution.initializeIncrementalResponse response queue.queue.initialGroups
      queue.queue.initialStreams
  let publisher : ReferenceWorkQueue.IncrementalPublisher :=
    { ids, active := queue.queue.initialGroups ++ queue.queue.initialStreams }
  (initial, ⟨queue, publisher, false⟩)

/-- Abrupt reader closure requests cancellation before response completion notification.
Reasons and asynchronous settlement are erased here.
Repeated close is silent and does not complete work.
-/
def ResponseStreamCursor.close (cursor : ResponseStreamCursor)
    : ResponseStreamCursor × List HostEffect :=
  if cursor.finished then
    (cursor, [])
  else
    let (queue, cleanup) := cursor.queue.cancel
    ({ cursor with queue }.onWorkQueueFinished, cleanup ++ [.responseFinished])

/-- Guarded response mapping through the shared publisher's handleBatch.
The guard and silent-input case wrap the mapper; they are not a second publication algorithm.
Map final notices before clearing IDs and notifying response completion.
Closed readers cannot map again.
-/
def ResponseStreamCursor.handleBatch (cursor : ResponseStreamCursor)
    (batch : List GraphEvent)
    : Option Execution.IncrementalStreamUpdateResult
      × ResponseStreamCursor
      × List HostEffect :=
  if cursor.finished then
    (none, cursor, [])
  else
    let reduced := cursor.queue.handleGraphEvents batch
    let next := { cursor with queue := reduced.state }
    if reduced.workQueueEvents.isEmpty then
      (none, next, reduced.effects)
    else
      let (update, publisher) := cursor.publisher.handleBatch reduced.workQueueEvents
      let next := { next with publisher }
      if update.hasNext then
        (some update, next, reduced.effects)
      else
        (some update, next.onWorkQueueFinished, reduced.effects ++ [.responseFinished])

-----------------------------------------------------------------------------------------
-- Response replay adapter
-----------------------------------------------------------------------------------------

/-- Finite observation of successive response-mapping calls. -/
def ResponseStreamCursor.run (cursor : ResponseStreamCursor)
    (batches : List (List GraphEvent))
    : List Execution.IncrementalStreamUpdateResult
      × ResponseStreamCursor
      × List HostEffect :=
  batches.foldl
    (fun (updates, cursor, effects) batch =>
      let (update, cursor, next) := cursor.handleBatch batch
      (updates ++ update.toList, cursor, effects ++ next))
    ([], cursor, [])

/-- Replay the same pure completion; host effects remain separate from response observation. -/
def replayIncrementalResponse
    (completed : Execution.Completion (List (Name × Execution.ResponseValue)))
    (inputs : List (List GraphEvent))
    : Execution.InitialIncrementalStreamResult
      × List Execution.IncrementalStreamUpdateResult
      × Bool :=
  let response := Execution.selectionSetResultToResponse completed.result
  let (initial, cursor) := ResponseStreamCursor.buildResponse response completed.work
  let (updates, final, _) := cursor.run inputs
  (initial, updates, final.queue.queue.terminated)

-----------------------------------------------------------------------------------------
-- Reference projection and equivalence statements (witnesses in `Proofs`)
-----------------------------------------------------------------------------------------

/-- The reference state projects unchanged while live and to empty accounting when terminated. -/
def State.fromReference (queue : ReferenceWorkQueue.State) : State :=
  let state : State := ⟨queue, false⟩
  if queue.terminated then state.clearRecords else state

/-- Exact finite replay at the shared model abstraction. No accounting/correctness premise is
added to the host: use only existing executed-work, matching, freshness, and start laws.
-/
def replayMatchesReference : Prop :=
  ∀ work inputs,
    ReferenceWorkQueue.ExecutedWork work
    → ReferenceWorkQueue.ValidGraphEvents work inputs.flatten
    → ReferenceWorkQueue.inputsStarted work inputs = true
    → let reference :=
        (ReferenceWorkQueue.State.initialize
          (ReferenceWorkQueue.Work.fromExecution work)).runNormalized
          inputs
      let alternative := (State.initialize work).runNormalized inputs
      alternative.1 = State.fromReference reference.1 ∧ alternative.2 = reference.2

/-- Transfer boundary for the reference conformance proof, not an assumed runtime bridge. -/
def createWorkQueueForScheduleMatchesReference : Prop :=
  ∀ work schedule,
    ReferenceWorkQueue.ExecutedWork work
    → work.size ≠ 0
    → schedule.ValidFor work
    → createWorkQueueForSchedule work schedule
      = ReferenceWorkQueue.createWorkQueueForSchedule work schedule

/-- Teardown/finish guarding must preserve actual response replay, not only key histories. -/
def responseReplayMatchesReference : Prop :=
  ∀ completed inputs,
    ReferenceWorkQueue.ExecutedWork completed.work
    → ReferenceWorkQueue.ValidGraphEvents completed.work inputs.flatten
    → ReferenceWorkQueue.inputsStarted completed.work inputs = true
    → replayIncrementalResponse completed inputs
      = ReferenceWorkQueue.replayIncrementalResponse completed inputs

end GraphQL.IncrementalDelivery.AlternativeWorkQueue
