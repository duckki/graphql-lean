import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PendingDebt
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ReadyDrain

/-! Permanent group retirement across executable queue transitions. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (
  ExecutionGroupValue StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- A retired delivery ref cannot acquire a live node again
-----------------------------------------------------------------------------------------

/-- The ref was registered earlier, but no live group node currently has that ref. -/
def State.RetiredGroup (queue : State) (ref : NodeRef) : Prop :=
  ref ∈ queue.registeredGroups
  ∧ ref ∉ queue.groupNodes.map (fun node => node.group.node.ref)

/-- A preserved state predicate extends through a finite fold.
Witness: induction over the remaining inputs, threading the actual accumulator. -/
private theorem fold_preserves {α β : Type} (step : β → α → β) (property : β → Prop)
    (preserved : ∀ state item, property state → property (step state item))
    (items : List α) (state : β) (initial : property state)
    : property (items.foldl step state) := by
  induction items generalizing state with
  | nil => exact initial
  | cons item rest ih => exact ih (step state item) (preserved state item initial)

/-- A retired ref has no live-node lookup result.
Witness: the absence clause rules out every matching list entry. -/
theorem State.RetiredGroup.lookup_none {queue : State} {ref : NodeRef}
    (retired : queue.RetiredGroup ref)
    : queue.groupNode? ref = none := by
  apply List.find?_eq_none.mpr
  intro node member selected
  exact retired.2 (List.mem_map.mpr ⟨node, member, beq_iff_eq.mp selected⟩)

/-- Replacing group metadata preserves retired refs.
Witness: replacement preserves the exact list of live refs. -/
theorem State.RetiredGroup.putGroupNode {queue : State} {ref : NodeRef}
    (retired : queue.RetiredGroup ref) (updated : GroupNode)
    : (queue.putGroupNode updated).RetiredGroup ref := by
  refine ⟨retired.1, ?_⟩
  rw [State.putGroupNode_refs]
  exact retired.2

/-- Filtering live groups cannot revive a retired ref.
Witness: every retained node was already present, and registration history is unchanged. -/
private theorem State.RetiredGroup.filterGroups {queue : State} {ref : NodeRef}
    (retired : queue.RetiredGroup ref) (keep : GroupNode → Bool)
    : ({ queue with groupNodes := queue.groupNodes.filter keep } : State).RetiredGroup
        ref := by
  refine ⟨retired.1, ?_⟩
  rintro member
  obtain ⟨node, kept, same⟩ := List.mem_map.mp member
  exact retired.2 (List.mem_map.mpr ⟨node, (List.mem_filter.mp kept).1, same⟩)

/-- Registration cannot recreate a retired ref, even if the input repeats its descriptor.
Witness: the permanent registry rejects the same ref; a different ref cannot revive it. -/
theorem State.RetiredGroup.addGroup {queue : State} {ref : NodeRef}
    (retired : queue.RetiredGroup ref) (group : Group)
    : (queue.addGroup group).RetiredGroup ref := by
  unfold State.addGroup
  split
  · exact retired
  · rename_i fresh
    have different : ref ≠ group.node.ref := by
      intro same
      have known : group.node.ref ∈ queue.registeredGroups := same ▸ retired.1
      simp [known] at fresh
    split
    · exact ⟨List.mem_append_left _ retired.1, retired.2⟩
    · refine ⟨List.mem_append_left _ retired.1, ?_⟩
      simpa [List.map_append, different] using retired.2

/-- Both passes of group integration preserve retirement.
Witness: registration rejects retired refs and parent-link updates preserve live refs. -/
theorem State.RetiredGroup.addGroups {queue : State} {ref : NodeRef}
    (retired : queue.RetiredGroup ref) (groups : List Group)
    : (queue.addGroups groups).1.RetiredGroup ref := by
  let fresh := groups.filter (fun group =>
    !queue.registeredGroups.contains group.node.ref
      && (queue.groupNode? group.node.ref).isNone)
  let linkStep (current : State) (group : Group) : State :=
    match group.parent with
    | none => current
    | some parent =>
        match current.groupNode? parent with
        | none => current
        | some node =>
            let children := if node.childGroups.contains group.node.ref then
              node.childGroups else node.childGroups ++ [group.node.ref]
            current.putGroupNode { node with childGroups := children }
  have linked (current : State) (group : Group) (prior : current.RetiredGroup ref)
      : (linkStep current group).RetiredGroup ref := by
    unfold linkStep
    split
    · exact prior
    · split
      · exact prior
      · exact prior.putGroupNode _
  change (fresh.foldl linkStep (fresh.foldl State.addGroup queue)).RetiredGroup ref
  exact fold_preserves linkStep (fun current => current.RetiredGroup ref) linked fresh _
    (fold_preserves State.addGroup (fun current => current.RetiredGroup ref)
      (fun _ group prior => prior.addGroup group) fresh queue retired)

/-- Registering tasks updates only existing live group nodes.
Witness: every contributor update is a ref-preserving replacement. -/
theorem State.RetiredGroup.addTask {queue : State} {ref : NodeRef}
    (retired : queue.RetiredGroup ref) (task : Task)
    : (queue.addTask task).RetiredGroup ref := by
  let registered : State := { queue with tasks := queue.tasks ++ [task] }
  let step (current : State) (group : Execution.DeliveryNode) : State :=
    match current.groupNode? group.ref with
    | none => current
    | some node =>
        if node.tasks.contains task.occurrence then current
        else current.putGroupNode
          { node with tasks := node.tasks ++ [task.occurrence], pending := node.pending + 1 }
  have preserved (current : State) (group : Execution.DeliveryNode)
      (prior : current.RetiredGroup ref) : (step current group).RetiredGroup ref := by
    unfold step
    split
    · exact prior
    · split
      · exact prior
      · exact prior.putGroupNode _
  let current := task.groups.foldl step registered
  have currentRetired : current.RetiredGroup ref :=
    fold_preserves step (fun state => state.RetiredGroup ref)
      preserved task.groups registered retired
  change (if task.groups.any (fun group => current.rootGroups.contains group.ref)
      && (current.taskNode? task.occurrence).isNone then
      { current with taskNodes := current.taskNodes ++ [{ task }] }
    else current).RetiredGroup ref
  split <;> exact currentRetired

/-- Stream registration changes neither group history nor live group nodes.
Witness: inspection of both root and producer-linked stream registration branches. -/
theorem State.RetiredGroup.addStreams {queue : State} {ref : NodeRef}
    (retired : queue.RetiredGroup ref) (streams : List Stream)
    (parentTask : Option Occurrence)
    : (queue.addStreams streams parentTask).1.RetiredGroup ref := by
  unfold State.addStreams
  split
  · exact retired
  · dsimp
    split <;> exact retired

/-- Integrating any child work retains every retired ref.
Witness: compose group, task, and stream registration preservation. -/
theorem State.RetiredGroup.maybeIntegrateWork {queue : State} {ref : NodeRef}
    (retired : queue.RetiredGroup ref) (work : Work)
    (parentTask : Option Occurrence := none)
    : (queue.maybeIntegrateWork work parentTask).1.RetiredGroup ref := by
  let grouped := (queue.addGroups work.groups).1
  let tasked := work.tasks.foldl State.addTask grouped
  have taskRetired : tasked.RetiredGroup ref :=
    fold_preserves State.addTask (fun state => state.RetiredGroup ref)
      (fun _ task prior => prior.addTask task) work.tasks grouped (retired.addGroups _)
  exact taskRetired.addStreams work.streams parentTask

/-- Empty-shell pruning preserves permanent retirement.
Witness: induction on the actual traversal; each removal only filters live nodes. -/
theorem State.RetiredGroup.pruneEmptyGroups {queue : State} {ref : NodeRef}
    (retired : queue.RetiredGroup ref) (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.RetiredGroup ref := by
  have loop (fuel : Nat) (current : State) (remaining kept : List Execution.DeliveryNode)
      (prior : current.RetiredGroup ref)
      : (State.pruneEmptyGroups.go fuel current remaining kept).1.RetiredGroup ref := by
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
private theorem State.RetiredGroup.startTask {queue : State} {ref : NodeRef}
    (retired : queue.RetiredGroup ref) (task : Occurrence)
    : (queue.startTask task).RetiredGroup ref := by
  unfold State.startTask
  split
  · exact retired
  · split <;> exact retired

/-- Starting a group only starts its listed tasks.
Witness: task-start preservation through the group's task fold. -/
private theorem State.RetiredGroup.startGroup {queue : State} {ref : NodeRef}
    (retired : queue.RetiredGroup ref) (group : Nat)
    : (queue.startGroup group).RetiredGroup ref := by
  unfold State.startGroup
  split
  · exact retired
  · split
    · exact retired
    · exact fold_preserves State.startTask (fun state => state.RetiredGroup ref)
        (fun _ task prior => prior.startTask task) _ queue retired

/-- Starting a stream changes only the stream-root registry.
Witness: direct inspection of the activation branch. -/
private theorem State.RetiredGroup.startStream {queue : State} {ref : NodeRef}
    (retired : queue.RetiredGroup ref) (stream : Nat)
    : (queue.startStream stream).RetiredGroup ref := by
  unfold State.startStream
  split <;> exact retired

/-- Work activation does not recreate any live group node.
Witness: group and stream activation preserve retirement through both folds. -/
theorem State.RetiredGroup.startNewWork {queue : State} {ref : NodeRef}
    (retired : queue.RetiredGroup ref) (work : NewWork)
    : (queue.startNewWork work).RetiredGroup ref := by
  let current : State :=
    { queue with rootGroups := queue.rootGroups ++ work.newGroups.map Execution.DeliveryNode.ref }
  have grouped := fold_preserves State.startGroup (fun state => state.RetiredGroup ref)
    (fun _ group prior => prior.startGroup group)
    (work.newGroups.map Execution.DeliveryNode.ref) current retired
  exact fold_preserves State.startStream (fun state => state.RetiredGroup ref)
    (fun _ stream prior => prior.startStream stream)
    (work.newStreams.map Execution.DeliveryNode.ref) _ grouped

-----------------------------------------------------------------------------------------
-- Publication, cancellation, and graph-event handling
-----------------------------------------------------------------------------------------

/-- Task flushing removes memberships but preserves every live group ref.
Witness: the node-map update changes task lists only. -/
theorem State.RetiredGroup.removeTask {queue : State} {ref : NodeRef}
    (retired : queue.RetiredGroup ref) (task : Occurrence)
    : (queue.removeTask task).RetiredGroup ref := by
  refine ⟨retired.1, ?_⟩
  simpa [State.removeTask, List.map_map] using retired.2

/-- Failure cleanup cannot revive an already retired group.
Witness: regardless of its traversal, cleanup retains only old live group nodes. -/
theorem State.RetiredGroup.removeGroup {queue : State} {ref : NodeRef}
    (retired : queue.RetiredGroup ref) (group : Nat)
    : (queue.removeGroup group).RetiredGroup ref :=
  retired.filterGroups _

/-- Successful flushing and child promotion preserve retirement.
Witness: task-removal induction, removal of the completed group, then pruning. -/
theorem State.RetiredGroup.finishGroupSuccess {queue : State} {ref : NodeRef}
    (retired : queue.RetiredGroup ref) (group : GroupNode)
    : (queue.finishGroupSuccess group).1.RetiredGroup ref := by
  let step (acc : State × List ExecutionGroupValue × NodeRefs) (task : Occurrence) :=
    let (current, values, streams) := acc
    match current.taskNode? task with
    | none => (current, values, streams)
    | some taskNode =>
        let values := match taskNode.value with
          | none => values
          | some value => values ++ [value]
        (current.removeTask task, values, streams ++ taskNode.childStreams)
  have preserved (acc : State × List ExecutionGroupValue × NodeRefs) (task : Occurrence)
      (prior : acc.1.RetiredGroup ref) : (step acc task).1.RetiredGroup ref := by
    obtain ⟨current, values, streams⟩ := acc
    unfold step
    dsimp only
    split
    · exact prior
    · exact prior.removeTask task
  let flushed := (group.tasks.foldl step (queue, [], [])).1
  have flushedRetired : flushed.RetiredGroup ref :=
    fold_preserves step (fun acc => acc.1.RetiredGroup ref)
      preserved group.tasks (queue, [], []) retired
  let current : State :=
    { flushed with
      groupNodes := flushed.groupNodes.filter
        (fun node => node.group.node.ref != group.group.node.ref)
      rootGroups := flushed.rootGroups.filter (· != group.group.node.ref) }
  have currentRetired : current.RetiredGroup ref := flushedRetired.filterGroups _
  let children := group.childGroups.filterMap
    (fun ref => (current.groupNode? ref).map (fun node => node.group.node))
  exact currentRetired.pruneEmptyGroups children

/-- Release-time draining cannot recreate a retired ref.
Witness: both closures only remove live groups, and activation preserves registration.
-/
theorem State.RetiredGroup.drainReadyGroups {queue : State} {ref : NodeRef}
    (retired : queue.RetiredGroup ref)
    : queue.drainReadyGroups.1.RetiredGroup ref := by
  apply State.drainReadyGroups_preserves (fun state => state.RetiredGroup ref)
    (fun _ node prior _ _ _ _ => (prior.finishGroupSuccess node).startNewWork _)
    (fun _ node _ prior _ _ _ => prior.removeGroup node.group.node.ref) retired

/-- One contributor's decrement and optional flush preserve retirement.
Witness: ref-preserving metadata replacement followed by flush preservation. -/
private theorem retired_successGroupStep (acc : State × List WorkQueueEvent × NewWork)
    (group : Execution.DeliveryNode) (ref : NodeRef) (prior : acc.1.RetiredGroup ref)
    : (successGroupStep acc group).1.RetiredGroup ref := by
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
theorem State.RetiredGroup.taskSuccess {queue : State} {ref : NodeRef}
    (retired : queue.RetiredGroup ref) (task : Occurrence) (result : TaskResult)
    : (queue.taskSuccess task result).1.RetiredGroup ref := by
  cases found : queue.taskNode? task with
  | none => simpa [State.taskSuccess, found] using retired
  | some node =>
      rw [queue.taskSuccess_eq task result node found]
      split <;> try exact retired.removeTask task
      let withValue := queue.putTaskNode { node with value := some result.value }
      have withValueRetired : withValue.RetiredGroup ref := retired
      let integrated := (withValue.maybeIntegrateWork result.work (some task)).1
      have integratedRetired : integrated.RetiredGroup ref :=
        withValueRetired.maybeIntegrateWork result.work (some task)
      have folded := fold_preserves successGroupStep (fun acc => acc.1.RetiredGroup ref)
        (fun acc group prior => retired_successGroupStep acc group ref prior)
        node.task.groups (integrated, [], {}) integratedRetired
      exact (folded.startNewWork _).drainReadyGroups

/-- Task failure preserves retirement while closing active or retaining latent owners.
Witness: task removal, group cleanup, and ref-preserving error updates through the fold.
-/
theorem State.RetiredGroup.taskFailure {queue : State} {ref : NodeRef}
    (retired : queue.RetiredGroup ref) (task : Occurrence) (errors : Nat)
    : (queue.taskFailure task errors).1.RetiredGroup ref := by
  let step (acc : State × List WorkQueueEvent) (group : Execution.DeliveryNode) :=
    let (current, events) := acc
    match current.groupNode? group.ref with
    | none => (current, events)
    | some node =>
        if current.rootGroups.contains group.ref then
          let (next, failure) := current.finishGroupFailure node errors
          (next, events ++ [failure])
        else
          (current.putGroupNode
            { node with
              pending := node.pending - 1
              failure := some (node.failure.getD 0 + errors) }, events)
  have preserved (acc : State × List WorkQueueEvent) (group : Execution.DeliveryNode)
      (prior : acc.1.RetiredGroup ref) : (step acc group).1.RetiredGroup ref := by
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
    exact fold_preserves step (fun acc => acc.1.RetiredGroup ref)
      preserved _ _ (retired.removeTask task)

/-- Stream-item integration cannot revive a retired ref through nested work.
Witness: integrate, prune, and activate each item in its actual batch order. -/
theorem State.RetiredGroup.streamItems {queue : State} {ref : NodeRef}
    (retired : queue.RetiredGroup ref) (stream : Execution.DeliveryNode)
    (items : List StreamItem)
    : (queue.streamItems stream items).1.RetiredGroup ref := by
  let step (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue) (item : StreamItem) :=
    let (current, groups, streams, values) := acc
    let (integrated, newWork) := current.maybeIntegrateWork item.work
    let (pruned, nonempty) := integrated.pruneEmptyGroups newWork.newGroups
    (pruned.startNewWork { newWork with newGroups := nonempty },
      groups ++ nonempty, streams ++ newWork.newStreams, values ++ [item.value])
  have preserved (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue) (item : StreamItem)
      (prior : acc.1.RetiredGroup ref) : (step acc item).1.RetiredGroup ref := by
    exact ((prior.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _
  unfold State.streamItems
  split
  · exact retired
  · exact (fold_preserves step (fun acc => acc.1.RetiredGroup ref)
      preserved items (queue, [], [], []) retired).drainReadyGroups

/-- Every graph-event handler preserves retired refs, without source-law premises.
Witness: success/failure preservation; stream closures touch no group state. -/
theorem State.RetiredGroup.handleGraphEvent {queue : State} {ref : NodeRef}
    (retired : queue.RetiredGroup ref) (event : GraphEvent)
    : (queue.handleGraphEvent event).1.RetiredGroup ref := by
  cases event with
  | taskSuccess task result => exact retired.taskSuccess task result
  | taskFailure task errors => exact retired.taskFailure task errors
  | streamItems stream items => exact retired.streamItems stream items
  | streamSuccess stream =>
      change (queue.streamSuccess stream).1.RetiredGroup ref
      unfold State.streamSuccess
      split <;> exact retired
  | streamFailure stream errors =>
      change (queue.streamFailure stream errors).1.RetiredGroup ref
      unfold State.streamFailure
      split <;> exact retired

-----------------------------------------------------------------------------------------
-- Arbitrary future batches cannot revive retired group nodes
-----------------------------------------------------------------------------------------

/-- Processing any batch preserves retirement, including termination and ignored input.
Witness: eventwise preservation; setting the terminal flag changes no group state. -/
theorem State.RetiredGroup.handleGraphEvents {queue : State} {ref : NodeRef}
    (retired : queue.RetiredGroup ref) (events : List GraphEvent)
    : (queue.handleGraphEvents events).1.RetiredGroup ref := by
  let step (acc : State × List WorkQueueEvent) (event : GraphEvent) :=
    let (current, outputs) := acc
    let (next, produced) := current.handleGraphEvent event
    (next, outputs ++ produced)
  have folded := fold_preserves step (fun acc => acc.1.RetiredGroup ref)
    (fun _ event prior => prior.handleGraphEvent event) events (queue, []) retired
  unfold State.handleGraphEvents
  split
  · exact retired
  · dsimp only
    split <;> exact folded

/-- Every finite normalized replay retains all initially retired refs.
Witness: batch induction through the actual queue/publisher fold. No validity, start,
generated-work, or scheduling premise is needed for this implementation invariant.
-/
theorem State.RetiredGroup.runNormalized {queue : State} {ref : NodeRef}
    (retired : queue.RetiredGroup ref) (batches : List (List GraphEvent))
    : (queue.runNormalized batches).1.RetiredGroup ref := by
  let step (acc : State × IncrementalPublisher × List (List Execution.WorkQueueEvent))
      (batch : List GraphEvent) :=
    let (current, publisher, outputs) := acc
    let (next, raw) := current.handleGraphEvents batch
    if raw.isEmpty then (next, publisher, outputs)
    else
      let (publisher, mapped) := publisher.normalizeBatch raw
      (next, publisher, outputs ++ [mapped])
  have preserved (acc : State × IncrementalPublisher × List (List Execution.WorkQueueEvent))
      (batch : List GraphEvent) (prior : acc.1.RetiredGroup ref)
      : (step acc batch).1.RetiredGroup ref := by
    unfold step
    dsimp only
    split <;> exact prior.handleGraphEvents batch
  exact fold_preserves step (fun acc => acc.1.RetiredGroup ref) preserved batches
    (queue, { active := queue.initialGroups ++ queue.initialStreams }, []) retired

/-- A retired group remains absent after every future normalized replay.
Witness: retirement preservation followed by the live-lookup characterization. -/
theorem State.RetiredGroup.never_recreated {queue : State} {ref : NodeRef}
    (retired : queue.RetiredGroup ref) (batches : List (List GraphEvent))
    : (queue.runNormalized batches).1.groupNode? ref = none :=
  (retired.runNormalized batches).lookup_none

/-- A registered ref with no live lookup is retired.
Witness: any group-list entry with that ref would contradict the missing lookup. -/
theorem State.RetiredGroup.of_lookup_none {queue : State} {ref : NodeRef}
    (registered : ref ∈ queue.registeredGroups) (absent : queue.groupNode? ref = none)
    : queue.RetiredGroup ref := by
  refine ⟨registered, ?_⟩
  rintro member
  obtain ⟨node, member, same⟩ := List.mem_map.mp member
  exact (List.find?_eq_none.mp absent) node member (beq_iff_eq.mpr same)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
