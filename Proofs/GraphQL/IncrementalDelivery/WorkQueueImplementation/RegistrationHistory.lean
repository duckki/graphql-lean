import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PendingDebt
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ReadyDrain

/-! Permanent group retirement across executable queue transitions. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (
  ExecutionGroupValue StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- A retired delivery key cannot acquire a live node again
-----------------------------------------------------------------------------------------

/-- The key was registered earlier, but no live group node currently has that key. -/
def State.RetiredGroup (queue : State) (key : Nat) : Prop :=
  key ∈ queue.registeredGroups
  ∧ key ∉ queue.groupNodes.map (fun node => node.group.node.key)

/-- A preserved state predicate extends through a finite fold.
Witness: induction over the remaining inputs, threading the actual accumulator. -/
private theorem fold_preserves {α β : Type} (step : β → α → β) (property : β → Prop)
    (preserved : ∀ state item, property state → property (step state item))
    (items : List α) (state : β) (initial : property state)
    : property (items.foldl step state) := by
  induction items generalizing state with
  | nil => exact initial
  | cons item rest ih => exact ih (step state item) (preserved state item initial)

/-- A retired key has no live-node lookup result.
Witness: the absence clause rules out every matching list entry. -/
theorem State.RetiredGroup.lookup_none {queue : State} {key : Nat}
    (retired : queue.RetiredGroup key)
    : queue.groupNode? key = none := by
  apply List.find?_eq_none.mpr
  intro node member selected
  exact retired.2 (List.mem_map.mpr ⟨node, member, beq_iff_eq.mp selected⟩)

/-- Replacing group metadata preserves retired keys.
Witness: replacement preserves the exact list of live keys. -/
theorem State.RetiredGroup.putGroupNode {queue : State} {key : Nat}
    (retired : queue.RetiredGroup key) (updated : GroupNode)
    : (queue.putGroupNode updated).RetiredGroup key := by
  refine ⟨retired.1, ?_⟩
  rw [State.putGroupNode_keys]
  exact retired.2

/-- Filtering live groups cannot revive a retired key.
Witness: every retained node was already present, and registration history is unchanged. -/
private theorem State.RetiredGroup.filterGroups {queue : State} {key : Nat}
    (retired : queue.RetiredGroup key) (keep : GroupNode → Bool)
    : ({ queue with groupNodes := queue.groupNodes.filter keep } : State).RetiredGroup
        key := by
  refine ⟨retired.1, ?_⟩
  rintro member
  obtain ⟨node, kept, same⟩ := List.mem_map.mp member
  exact retired.2 (List.mem_map.mpr ⟨node, (List.mem_filter.mp kept).1, same⟩)

/-- Registration cannot recreate a retired key, even if the input repeats its descriptor.
Witness: the permanent registry rejects the same key; a different key cannot revive it. -/
theorem State.RetiredGroup.addGroup {queue : State} {key : Nat}
    (retired : queue.RetiredGroup key) (group : Group)
    : (queue.addGroup group).RetiredGroup key := by
  unfold State.addGroup
  split
  · exact retired
  · rename_i fresh
    have different : key ≠ group.node.key := by
      intro same
      have known : group.node.key ∈ queue.registeredGroups := same ▸ retired.1
      simp [known] at fresh
    split
    · exact ⟨List.mem_append_left _ retired.1, retired.2⟩
    · refine ⟨List.mem_append_left _ retired.1, ?_⟩
      simpa [List.map_append, different] using retired.2

/-- Both passes of group integration preserve retirement.
Witness: registration rejects retired keys and parent-link updates preserve live keys. -/
theorem State.RetiredGroup.addGroups {queue : State} {key : Nat}
    (retired : queue.RetiredGroup key) (groups : List Group)
    : (queue.addGroups groups).1.RetiredGroup key := by
  let fresh := groups.filter (fun group =>
    !queue.registeredGroups.contains group.node.key
      && (queue.groupNode? group.node.key).isNone)
  let linkStep (current : State) (group : Group) : State :=
    match group.parent with
    | none => current
    | some parent =>
        match current.groupNode? parent with
        | none => current
        | some node =>
            let children := if node.childGroups.contains group.node.key then
              node.childGroups else node.childGroups ++ [group.node.key]
            current.putGroupNode { node with childGroups := children }
  have linked (current : State) (group : Group) (prior : current.RetiredGroup key)
      : (linkStep current group).RetiredGroup key := by
    unfold linkStep
    split
    · exact prior
    · split
      · exact prior
      · exact prior.putGroupNode _
  change (fresh.foldl linkStep (fresh.foldl State.addGroup queue)).RetiredGroup key
  exact fold_preserves linkStep (fun current => current.RetiredGroup key) linked fresh _
    (fold_preserves State.addGroup (fun current => current.RetiredGroup key)
      (fun _ group prior => prior.addGroup group) fresh queue retired)

/-- Registering tasks updates only existing live group nodes.
Witness: every contributor update is a key-preserving replacement. -/
theorem State.RetiredGroup.addTask {queue : State} {key : Nat}
    (retired : queue.RetiredGroup key) (task : Task)
    : (queue.addTask task).RetiredGroup key := by
  let registered : State := { queue with tasks := queue.tasks ++ [task] }
  let step (current : State) (group : Execution.DeliveryNode) : State :=
    match current.groupNode? group.key with
    | none => current
    | some node =>
        if node.tasks.contains task.occurrence then current
        else current.putGroupNode
          { node with tasks := node.tasks ++ [task.occurrence], pending := node.pending + 1 }
  have preserved (current : State) (group : Execution.DeliveryNode)
      (prior : current.RetiredGroup key) : (step current group).RetiredGroup key := by
    unfold step
    split
    · exact prior
    · split
      · exact prior
      · exact prior.putGroupNode _
  let current := task.groups.foldl step registered
  have currentRetired : current.RetiredGroup key :=
    fold_preserves step (fun state => state.RetiredGroup key)
      preserved task.groups registered retired
  change (if task.groups.any (fun group => current.rootGroups.contains group.key)
      && (current.taskNode? task.occurrence).isNone then
      { current with taskNodes := current.taskNodes ++ [{ task }] }
    else current).RetiredGroup key
  split <;> exact currentRetired

/-- Stream registration changes neither group history nor live group nodes.
Witness: inspection of both root and producer-linked stream registration branches. -/
theorem State.RetiredGroup.addStreams {queue : State} {key : Nat}
    (retired : queue.RetiredGroup key) (streams : List Stream)
    (parentTask : Option Occurrence)
    : (queue.addStreams streams parentTask).1.RetiredGroup key := by
  unfold State.addStreams
  split
  · exact retired
  · dsimp
    split <;> exact retired

/-- Integrating any child work retains every retired key.
Witness: compose group, task, and stream registration preservation. -/
theorem State.RetiredGroup.maybeIntegrateWork {queue : State} {key : Nat}
    (retired : queue.RetiredGroup key) (work : Work)
    (parentTask : Option Occurrence := none)
    : (queue.maybeIntegrateWork work parentTask).1.RetiredGroup key := by
  let grouped := (queue.addGroups work.groups).1
  let tasked := work.tasks.foldl State.addTask grouped
  have taskRetired : tasked.RetiredGroup key :=
    fold_preserves State.addTask (fun state => state.RetiredGroup key)
      (fun _ task prior => prior.addTask task) work.tasks grouped (retired.addGroups _)
  exact taskRetired.addStreams work.streams parentTask

/-- Empty-shell pruning preserves permanent retirement.
Witness: induction on the actual traversal; each removal only filters live nodes. -/
theorem State.RetiredGroup.pruneEmptyGroups {queue : State} {key : Nat}
    (retired : queue.RetiredGroup key) (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.RetiredGroup key := by
  have loop (fuel : Nat) (current : State) (remaining kept : List Execution.DeliveryNode)
      (prior : current.RetiredGroup key)
      : (State.pruneEmptyGroups.go fuel current remaining kept).1.RetiredGroup key := by
    induction fuel generalizing current remaining kept with
    | zero => exact prior
    | succ fuel ih =>
        cases remaining with
        | nil => exact prior
        | cons group rest =>
            unfold State.pruneEmptyGroups.go
            split
            · exact ih _ _ _ prior
            · split
              · exact ih _ _ _ (prior.filterGroups _)
              · exact ih _ _ _ prior
  exact loop _ queue groups [] retired

/-- Starting a task does not touch group registration or live nodes.
Witness: both lookup branches only update task nodes. -/
private theorem State.RetiredGroup.startTask {queue : State} {key : Nat}
    (retired : queue.RetiredGroup key) (task : Occurrence)
    : (queue.startTask task).RetiredGroup key := by
  unfold State.startTask
  split
  · exact retired
  · split <;> exact retired

/-- Starting a group only starts its listed tasks.
Witness: task-start preservation through the group's task fold. -/
private theorem State.RetiredGroup.startGroup {queue : State} {key : Nat}
    (retired : queue.RetiredGroup key) (group : Nat)
    : (queue.startGroup group).RetiredGroup key := by
  unfold State.startGroup
  split
  · exact retired
  · split
    · exact retired
    · exact fold_preserves State.startTask (fun state => state.RetiredGroup key)
        (fun _ task prior => prior.startTask task) _ queue retired

/-- Starting a stream changes only the stream-root registry.
Witness: direct inspection of the activation branch. -/
private theorem State.RetiredGroup.startStream {queue : State} {key : Nat}
    (retired : queue.RetiredGroup key) (stream : Nat)
    : (queue.startStream stream).RetiredGroup key := by
  unfold State.startStream
  split <;> exact retired

/-- Work activation does not recreate any live group node.
Witness: group and stream activation preserve retirement through both folds. -/
theorem State.RetiredGroup.startNewWork {queue : State} {key : Nat}
    (retired : queue.RetiredGroup key) (work : NewWork)
    : (queue.startNewWork work).RetiredGroup key := by
  let current : State :=
    { queue with rootGroups := queue.rootGroups ++ work.newGroups.map Execution.DeliveryNode.key }
  have grouped := fold_preserves State.startGroup (fun state => state.RetiredGroup key)
    (fun _ group prior => prior.startGroup group)
    (work.newGroups.map Execution.DeliveryNode.key) current retired
  exact fold_preserves State.startStream (fun state => state.RetiredGroup key)
    (fun _ stream prior => prior.startStream stream)
    (work.newStreams.map Execution.DeliveryNode.key) _ grouped

-----------------------------------------------------------------------------------------
-- Publication, cancellation, and graph-event handling
-----------------------------------------------------------------------------------------

/-- Task flushing removes memberships but preserves every live group key.
Witness: the node-map update changes task lists only. -/
theorem State.RetiredGroup.removeTask {queue : State} {key : Nat}
    (retired : queue.RetiredGroup key) (task : Occurrence)
    : (queue.removeTask task).RetiredGroup key := by
  refine ⟨retired.1, ?_⟩
  simpa [State.removeTask, List.map_map] using retired.2

/-- Failure cleanup cannot revive an already retired group.
Witness: regardless of its traversal, cleanup retains only old live group nodes. -/
theorem State.RetiredGroup.removeGroup {queue : State} {key : Nat}
    (retired : queue.RetiredGroup key) (group : Nat)
    : (queue.removeGroup group).RetiredGroup key :=
  retired.filterGroups _

/-- Successful flushing and child promotion preserve retirement.
Witness: task-removal induction, removal of the completed group, then pruning. -/
theorem State.RetiredGroup.finishGroupSuccess {queue : State} {key : Nat}
    (retired : queue.RetiredGroup key) (group : GroupNode)
    : (queue.finishGroupSuccess group).1.RetiredGroup key := by
  let step (acc : State × List ExecutionGroupValue × Keys) (task : Occurrence) :=
    let (current, values, streams) := acc
    match current.taskNode? task with
    | none => (current, values, streams)
    | some taskNode =>
        let values := match taskNode.value with
          | none => values
          | some value => values ++ [value]
        (current.removeTask task, values, streams ++ taskNode.childStreams)
  have preserved (acc : State × List ExecutionGroupValue × Keys) (task : Occurrence)
      (prior : acc.1.RetiredGroup key) : (step acc task).1.RetiredGroup key := by
    obtain ⟨current, values, streams⟩ := acc
    unfold step
    dsimp only
    split
    · exact prior
    · exact prior.removeTask task
  let flushed := (group.tasks.foldl step (queue, [], [])).1
  have flushedRetired : flushed.RetiredGroup key :=
    fold_preserves step (fun acc => acc.1.RetiredGroup key)
      preserved group.tasks (queue, [], []) retired
  let current : State :=
    { flushed with
      groupNodes := flushed.groupNodes.filter
        (fun node => node.group.node.key != group.group.node.key)
      rootGroups := flushed.rootGroups.filter (· != group.group.node.key) }
  have currentRetired : current.RetiredGroup key := flushedRetired.filterGroups _
  let children := group.childGroups.filterMap
    (fun key => (current.groupNode? key).map (fun node => node.group.node))
  exact currentRetired.pruneEmptyGroups children

/-- Release-time draining cannot recreate a retired key.
Witness: both closures only remove live groups, and activation preserves registration.
-/
theorem State.RetiredGroup.drainReadyGroups {queue : State} {key : Nat}
    (retired : queue.RetiredGroup key)
    : queue.drainReadyGroups.1.RetiredGroup key := by
  apply State.drainReadyGroups_preserves (fun state => state.RetiredGroup key)
    (fun _ node prior _ _ _ _ => (prior.finishGroupSuccess node).startNewWork _)
    (fun _ node _ prior _ _ _ => prior.removeGroup node.group.node.key) retired

/-- One contributor's decrement and optional flush preserve retirement.
Witness: key-preserving metadata replacement followed by flush preservation. -/
private theorem retired_successGroupStep (acc : State × List WorkQueueEvent × NewWork)
    (group : Execution.DeliveryNode) (key : Nat) (prior : acc.1.RetiredGroup key)
    : (successGroupStep acc group).1.RetiredGroup key := by
  obtain ⟨current, events, released⟩ := acc
  unfold successGroupStep
  dsimp only
  split
  · exact prior
  · rename_i node found
    have updated := prior.putGroupNode { node with pending := node.pending - 1 }
    split
    · exact updated.finishGroupSuccess _
    · exact updated

/-- Task success cannot recreate a retired group through child work or owner settlement.
Witness: integration preservation and the actual single-pass contributor fold. -/
theorem State.RetiredGroup.taskSuccess {queue : State} {key : Nat}
    (retired : queue.RetiredGroup key) (task : Occurrence) (result : TaskResult)
    : (queue.taskSuccess task result).1.RetiredGroup key := by
  cases found : queue.taskNode? task with
  | none => simpa [State.taskSuccess, found] using retired
  | some node =>
      rw [queue.taskSuccess_eq task result node found]
      split <;> try exact retired.removeTask task
      let withValue := queue.putTaskNode { node with value := some result.value }
      have withValueRetired : withValue.RetiredGroup key := retired
      let integrated := (withValue.maybeIntegrateWork result.work (some task)).1
      have integratedRetired : integrated.RetiredGroup key :=
        withValueRetired.maybeIntegrateWork result.work (some task)
      have folded := fold_preserves successGroupStep (fun acc => acc.1.RetiredGroup key)
        (fun acc group prior => retired_successGroupStep acc group key prior)
        node.task.groups (integrated, [], {}) integratedRetired
      exact (folded.startNewWork _).drainReadyGroups

/-- Task failure preserves retirement while closing active or retaining latent owners.
Witness: task removal, group cleanup, and key-preserving error updates through the fold.
-/
theorem State.RetiredGroup.taskFailure {queue : State} {key : Nat}
    (retired : queue.RetiredGroup key) (task : Occurrence) (errors : Nat)
    : (queue.taskFailure task errors).1.RetiredGroup key := by
  let step (acc : State × List WorkQueueEvent) (group : Execution.DeliveryNode) :=
    let (current, events) := acc
    match current.groupNode? group.key with
    | none => (current, events)
    | some node =>
        if current.rootGroups.contains group.key then
          let (next, failure) := current.finishGroupFailure node errors
          (next, events ++ [failure])
        else
          (current.putGroupNode
            { node with
              pending := node.pending - 1
              failure := some (node.failure.getD 0 + errors) }, events)
  have preserved (acc : State × List WorkQueueEvent) (group : Execution.DeliveryNode)
      (prior : acc.1.RetiredGroup key) : (step acc group).1.RetiredGroup key := by
    obtain ⟨current, events⟩ := acc
    unfold step
    dsimp only
    split
    · exact prior
    · split
      · exact prior.removeGroup _
      · exact prior.putGroupNode _
  unfold State.taskFailure
  split
  · exact retired
  · split <;> try exact retired.removeTask task
    exact fold_preserves step (fun acc => acc.1.RetiredGroup key)
      preserved _ _ (retired.removeTask task)

/-- Stream-item integration cannot revive a retired key through nested work.
Witness: integrate, prune, and activate each item in its actual batch order. -/
theorem State.RetiredGroup.streamItems {queue : State} {key : Nat}
    (retired : queue.RetiredGroup key) (stream : Execution.DeliveryNode)
    (items : List StreamItem)
    : (queue.streamItems stream items).1.RetiredGroup key := by
  let step (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue) (item : StreamItem) :=
    let (current, groups, streams, values) := acc
    let (integrated, newWork) := current.maybeIntegrateWork item.work
    let (pruned, nonempty) := integrated.pruneEmptyGroups newWork.newGroups
    (pruned.startNewWork { newWork with newGroups := nonempty },
      groups ++ nonempty, streams ++ newWork.newStreams, values ++ [item.value])
  have preserved (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue) (item : StreamItem)
      (prior : acc.1.RetiredGroup key) : (step acc item).1.RetiredGroup key := by
    exact ((prior.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _
  unfold State.streamItems
  split
  · exact retired
  · exact (fold_preserves step (fun acc => acc.1.RetiredGroup key)
      preserved items (queue, [], [], []) retired).drainReadyGroups

/-- Every graph-event handler preserves retired keys, without source-law premises.
Witness: success/failure preservation; stream closures touch no group state. -/
theorem State.RetiredGroup.handleGraphEvent {queue : State} {key : Nat}
    (retired : queue.RetiredGroup key) (event : GraphEvent)
    : (queue.handleGraphEvent event).1.RetiredGroup key := by
  cases event with
  | taskSuccess task result => exact retired.taskSuccess task result
  | taskFailure task errors => exact retired.taskFailure task errors
  | streamItems stream items => exact retired.streamItems stream items
  | streamSuccess stream =>
      change (queue.streamSuccess stream).1.RetiredGroup key
      unfold State.streamSuccess
      split <;> exact retired
  | streamFailure stream errors =>
      change (queue.streamFailure stream errors).1.RetiredGroup key
      unfold State.streamFailure
      split <;> exact retired

-----------------------------------------------------------------------------------------
-- Arbitrary future batches cannot revive retired group nodes
-----------------------------------------------------------------------------------------

/-- Processing any batch preserves retirement, including termination and ignored input.
Witness: eventwise preservation; setting the terminal flag changes no group state. -/
theorem State.RetiredGroup.handleGraphEvents {queue : State} {key : Nat}
    (retired : queue.RetiredGroup key) (events : List GraphEvent)
    : (queue.handleGraphEvents events).1.RetiredGroup key := by
  let step (acc : State × List WorkQueueEvent) (event : GraphEvent) :=
    let (current, outputs) := acc
    let (next, produced) := current.handleGraphEvent event
    (next, outputs ++ produced)
  have folded := fold_preserves step (fun acc => acc.1.RetiredGroup key)
    (fun _ event prior => prior.handleGraphEvent event) events (queue, []) retired
  unfold State.handleGraphEvents
  split
  · exact retired
  · dsimp only
    split <;> exact folded

/-- Every finite normalized replay retains all initially retired keys.
Witness: batch induction through the actual queue/publisher fold. No validity, start,
generated-work, or scheduling premise is needed for this implementation invariant.
-/
theorem State.RetiredGroup.runNormalized {queue : State} {key : Nat}
    (retired : queue.RetiredGroup key) (batches : List (List GraphEvent))
    : (queue.runNormalized batches).1.RetiredGroup key := by
  let step (acc : State × IncrementalPublisher × List (List Execution.WorkQueueEvent))
      (batch : List GraphEvent) :=
    let (current, publisher, outputs) := acc
    let (next, raw) := current.handleGraphEvents batch
    if raw.isEmpty then (next, publisher, outputs)
    else
      let (publisher, mapped) := publisher.normalizeBatch raw
      (next, publisher, outputs ++ [mapped])
  have preserved (acc : State × IncrementalPublisher × List (List Execution.WorkQueueEvent))
      (batch : List GraphEvent) (prior : acc.1.RetiredGroup key)
      : (step acc batch).1.RetiredGroup key := by
    unfold step
    dsimp only
    split <;> exact prior.handleGraphEvents batch
  exact fold_preserves step (fun acc => acc.1.RetiredGroup key) preserved batches
    (queue, { active := queue.initialGroups ++ queue.initialStreams }, []) retired

/-- A retired group remains absent after every future normalized replay.
Witness: retirement preservation followed by the live-lookup characterization. -/
theorem State.RetiredGroup.never_recreated {queue : State} {key : Nat}
    (retired : queue.RetiredGroup key) (batches : List (List GraphEvent))
    : (queue.runNormalized batches).1.groupNode? key = none :=
  (retired.runNormalized batches).lookup_none

/-- A registered key with no live lookup is retired.
Witness: any group-list entry with that key would contradict the missing lookup. -/
theorem State.RetiredGroup.of_lookup_none {queue : State} {key : Nat}
    (registered : key ∈ queue.registeredGroups) (absent : queue.groupNode? key = none)
    : queue.RetiredGroup key := by
  refine ⟨registered, ?_⟩
  rintro member
  obtain ⟨node, member, same⟩ := List.mem_map.mp member
  exact (List.find?_eq_none.mp absent) node member (beq_iff_eq.mpr same)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
