import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NormalizedPublications

/-! Task-produced streams are released with an earlier stored producer publication. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (
  ExecutionGroupValue StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Integration retains a settled producer until its child streams are attached
-----------------------------------------------------------------------------------------

/-- Registering another task preserves every successful task-node lookup.
Witness: group updates leave the task map unchanged; any new node is appended after it.
-/
theorem State.addTask_taskNode?_of_some {queue : State} {occurrence node}
    (found : queue.taskNode? occurrence = some node) (task : Task)
    : (queue.addTask task).taskNode? occurrence = some node := by
  let step (current : State) (group : Execution.DeliveryNode) : State :=
    match current.groupNode? group.key with
    | none => current
    | some groupNode =>
        if groupNode.tasks.contains task.occurrence then current
        else current.putGroupNode
          { groupNode with
            tasks := groupNode.tasks ++ [task.occurrence]
            pending := groupNode.pending + 1 }
  have unchanged (groups : List Execution.DeliveryNode) (current : State)
      : (groups.foldl step current).taskNodes = current.taskNodes := by
    induction groups generalizing current with
    | nil => rfl
    | cons group rest ih =>
        rw [List.foldl_cons, ih]
        dsimp only [step]
        split
        · rfl
        · split <;> rfl
  let current := task.groups.foldl step { queue with tasks := queue.tasks ++ [task] }
  have same : current.taskNodes = queue.taskNodes := unchanged _ _
  change (if task.groups.any (fun group => current.rootGroups.contains group.key)
      && (current.taskNode? task.occurrence).isNone then
        { current with taskNodes := current.taskNodes ++ [{ task }] }
      else current).taskNode? occurrence = some node
  split
  · change queue.taskNodes.find? _ = _ at found
    simp only [State.taskNode?, List.find?_append, same, found]
    rfl
  · simpa only [State.taskNode?, same] using found

/-- Installing a value updates the same successfully looked-up producer node.
Witness: the first matching entry remains first and is replaced with the settled node.
-/
theorem State.putTaskNode_value_lookup {queue : State} {occurrence node}
    (found : queue.taskNode? occurrence = some node) (value : ExecutionGroupValue)
    : (queue.putTaskNode { node with value := some value }).taskNode? occurrence
      = some { node with value := some value } := by
  have same := (State.taskNode?_some found).2
  change (queue.taskNodes.map (fun old =>
    if old.task.occurrence == node.task.occurrence then
      { node with value := some value } else old)).find?
        (fun candidate => candidate.task.occurrence == occurrence) = _
  rw [same]
  have loop (nodes : List TaskNode)
      (found : nodes.find? (fun candidate => candidate.task.occurrence == occurrence)
        = some node)
      : (nodes.map (fun old => if old.task.occurrence == occurrence then
          { node with value := some value } else old)).find?
          (fun candidate => candidate.task.occurrence == occurrence)
        = some { node with value := some value } := by
    induction nodes with
    | nil => cases found
    | cons head rest ih =>
        by_cases selected : (head.task.occurrence == occurrence) = true
        · simp [selected, same, (occurrence_beq_iff_eq occurrence occurrence).mpr rfl]
        · have later : rest.find?
              (fun candidate => candidate.task.occurrence == occurrence) = some node := by
            simpa [List.find?_cons, selected] using found
          simpa [List.find?_cons, selected] using ih later
  exact loop _ found

-----------------------------------------------------------------------------------------
-- Unresolved nodes never hold task-produced streams
-----------------------------------------------------------------------------------------

/-- A live task node with child streams has a stored successful producer value.
This is an implementation invariant, not an added host or scheduler-contract premise.
-/
def State.ChildStreamsSettled (queue : State) : Prop :=
  ∀ node ∈ queue.taskNodes, node.value = none → node.childStreams = []

/-- Group-node replacement leaves task nodes unchanged.
Witness: the state update touches only the group map. -/
theorem State.ChildStreamsSettled.putGroupNode {queue : State}
    (settled : queue.ChildStreamsSettled) (updated : GroupNode)
    : (queue.putGroupNode updated).ChildStreamsSettled :=
  settled

/-- Pointwise preservation lifts through the actual bookkeeping folds.
Witness: induction over the entries in their executable processing order. -/
private theorem fold_preserves {α β : Type} (property : α → Prop) (step : α → β → α)
    (preserved : ∀ state item, property state → property (step state item))
    (items : List β) (state : α) (initial : property state)
    : property (items.foldl step state) := by
  induction items generalizing state with
  | nil => exact initial
  | cons item rest ih => exact ih _ (preserved state item initial)

/-- Replacing a node preserves the invariant when the replacement satisfies it.
Witness: membership in the mapped task list is replacement or unchanged membership. -/
theorem State.ChildStreamsSettled.putTaskNode {queue : State}
    (settled : queue.ChildStreamsSettled) (updated : TaskNode)
    (allowed : updated.value = none → updated.childStreams = [])
    : (queue.putTaskNode updated).ChildStreamsSettled := by
  intro node member empty
  obtain ⟨old, oldMember, same⟩ := List.mem_map.mp member
  split at same
  · subst node
    exact allowed empty
  · subst node
    exact settled old oldMember empty

/-- Group registration cannot modify task stream links or stored values.
Witness: the exact task-map preservation equation. -/
theorem State.ChildStreamsSettled.addGroups {queue : State}
    (settled : queue.ChildStreamsSettled) (groups : List Group)
    : (queue.addGroups groups).1.ChildStreamsSettled := by
  intro node member
  rw [State.addGroups_taskNodes] at member
  exact settled node member

/-- Registering a task adds only an empty node with no child streams.
Witness: old-or-new task-node membership from the actual registration handler. -/
theorem State.ChildStreamsSettled.addTask {queue : State}
    (settled : queue.ChildStreamsSettled) (task : Task)
    : (queue.addTask task).ChildStreamsSettled := by
  intro node member empty
  rcases queue.addTask_startedOldOrNew task member with old | new
  · exact settled node old empty
  · subst node
    rfl

/-- Attaching child streams is safe when the chosen producer lookup is settled.
Witness: root streams do not change task nodes; task streams only extend that producer.
-/
theorem State.ChildStreamsSettled.addStreams {queue : State}
    (settled : queue.ChildStreamsSettled) (streams : List Stream)
    (parent : Option Occurrence)
    (ready
      : ∀ occurrence,
          parent = some occurrence
          → ∀ node, queue.taskNode? occurrence = some node → node.value ≠ none)
    : (queue.addStreams streams parent).1.ChildStreamsSettled := by
  cases parent with
  | none => exact settled
  | some occurrence =>
      simp only [State.addStreams]
      split
      · exact settled
      · rename_i node found
        apply settled.putTaskNode
        intro empty
        exact False.elim (ready occurrence rfl node found empty)

/-- Root or stream-item child integration creates no task-produced stream links.
Witness: group and task integration followed by parentless stream registration. -/
theorem State.ChildStreamsSettled.integrateRoots {queue : State}
    (settled : queue.ChildStreamsSettled) (work : Work)
    : (queue.maybeIntegrateWork work).1.ChildStreamsSettled := by
  have tasks := fold_preserves State.ChildStreamsSettled State.addTask
    (fun _ task prior => prior.addTask task) work.tasks _ (settled.addGroups work.groups)
  exact tasks.addStreams work.streams none
    (by intro occurrence impossible; cases impossible)

/-- Successful settlement installs its value before attaching any task-produced streams.
Witness: integration preserves the settled producer lookup through group/task registration.
-/
theorem State.ChildStreamsSettled.integrateSuccess {queue : State}
    (settled : queue.ChildStreamsSettled) {occurrence node}
    (found : queue.taskNode? occurrence = some node) (result : TaskResult)
    : ((queue.putTaskNode { node with value := some result.value }).maybeIntegrateWork
        result.work (some occurrence)).1.ChildStreamsSettled := by
  let stored := queue.putTaskNode { node with value := some result.value }
  let grouped := (stored.addGroups result.work.groups).1
  have storedSettled : stored.ChildStreamsSettled := settled.putTaskNode _ (by simp)
  have groupedLookup : grouped.taskNode? occurrence =
      some { node with value := some result.value } := by
    change grouped.taskNodes.find? _ = _
    rw [State.addGroups_taskNodes]
    exact State.putTaskNode_value_lookup found _
  have integrated := fold_preserves
    (fun current : State => current.ChildStreamsSettled
      ∧ current.taskNode? occurrence = some { node with value := some result.value })
    State.addTask
    (fun _ task prior => ⟨prior.1.addTask task, State.addTask_taskNode?_of_some prior.2 task⟩)
    result.work.tasks grouped ⟨storedSettled.addGroups _, groupedLookup⟩
  apply integrated.1.addStreams result.work.streams (some occurrence)
  intro other same candidate lookup
  cases same
  rw [integrated.2] at lookup
  cases lookup
  simp

-----------------------------------------------------------------------------------------
-- Bookkeeping and every graph-event handler preserve the derived invariant
-----------------------------------------------------------------------------------------

/-- Group pruning changes no task nodes.
Witness: reuse the exact task-map equation of the bounded pruning loop. -/
theorem State.ChildStreamsSettled.pruneEmptyGroups {queue : State}
    (settled : queue.ChildStreamsSettled) (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.ChildStreamsSettled := by
  intro node member
  rw [State.pruneEmptyGroups_taskNodes] at member
  exact settled node member

/-- Starting a task creates only an empty node with no stream links.
Witness: the start operation either retains the state or appends the default task node.
-/
theorem State.ChildStreamsSettled.startTask {queue : State}
    (settled : queue.ChildStreamsSettled) (occurrence : Occurrence)
    : (queue.startTask occurrence).ChildStreamsSettled := by
  unfold State.startTask
  split
  · exact settled
  · split
    · exact settled
    · intro node member empty
      rcases List.mem_append.mp member with old | new
      · exact settled node old empty
      · have same := List.mem_singleton.mp new
        subst node
        rfl

/-- Starting a group preserves the invariant through its task-start fold.
Witness: every individual start creates no producer stream links. -/
theorem State.ChildStreamsSettled.startGroup {queue : State}
    (settled : queue.ChildStreamsSettled) (key : Nat)
    : (queue.startGroup key).ChildStreamsSettled := by
  unfold State.startGroup
  split
  · exact settled
  · split
    · exact settled
    · exact fold_preserves State.ChildStreamsSettled State.startTask
        (fun _ occurrence prior => prior.startTask occurrence) _ _ settled

/-- Activating a stream does not modify any task node.
Witness: both executable branches retain the same task map. -/
theorem State.ChildStreamsSettled.startStream {queue : State}
    (settled : queue.ChildStreamsSettled) (key : Nat)
    : (queue.startStream key).ChildStreamsSettled := by
  unfold State.startStream
  split <;> exact settled

/-- Starting all released work preserves the invariant.
Witness: compose group starts and stream starts in their actual order. -/
theorem State.ChildStreamsSettled.startNewWork {queue : State}
    (settled : queue.ChildStreamsSettled) (work : NewWork)
    : (queue.startNewWork work).ChildStreamsSettled := by
  let current :=
    { queue with rootGroups := queue.rootGroups ++ work.newGroups.map Execution.DeliveryNode.key }
  have groups := fold_preserves State.ChildStreamsSettled State.startGroup
    (fun _ key prior => prior.startGroup key)
    (work.newGroups.map Execution.DeliveryNode.key) current settled
  exact fold_preserves State.ChildStreamsSettled State.startStream
    (fun _ key prior => prior.startStream key) _ _ groups

/-- Removing a failed group only filters existing task nodes.
Witness: every retained node belonged to the input task map. -/
theorem State.ChildStreamsSettled.removeGroup {queue : State}
    (settled : queue.ChildStreamsSettled) (key : Nat)
    : (queue.removeGroup key).ChildStreamsSettled :=
  fun node member => settled node (List.mem_filter.mp member).1

/-- A successful flush removes task nodes without altering surviving stream links.
Witness: the exact selected-node flush witness supplies residual map inclusion. -/
theorem State.ChildStreamsSettled.finishGroupSuccess {queue : State}
    (settled : queue.ChildStreamsSettled) (group : GroupNode)
    : (queue.finishGroupSuccess group).1.ChildStreamsSettled := by
  obtain ⟨_, _, _, _, retained, _⟩ := queue.finishGroupSuccess_publications group
  exact fun node member => settled node (retained member)

/-- Recursive draining cannot leave an unresolved task with child-stream links.
Witness: group cleanup filters task nodes, and activation creates only empty nodes.
-/
theorem State.ChildStreamsSettled.drainReadyGroups {queue : State}
    (settled : queue.ChildStreamsSettled)
    : queue.drainReadyGroups.1.ChildStreamsSettled := by
  apply State.drainReadyGroups_preserves State.ChildStreamsSettled (valid := settled)
  · intro current node prior _ _ _ _
    exact (prior.finishGroupSuccess node).startNewWork _
  · intro current node errors prior _ _ _
    exact prior.removeGroup _

/-- Task success preserves settled stream ownership through integration and release.
Witness: install the producer value, then follow the contributor fold and final drain.
-/
theorem State.ChildStreamsSettled.taskSuccess {queue : State}
    (settled : queue.ChildStreamsSettled) (occurrence : Occurrence) (result : TaskResult)
    : (queue.taskSuccess occurrence result).1.ChildStreamsSettled := by
  cases found : queue.taskNode? occurrence with
  | none => simpa only [State.taskSuccess, found] using settled
  | some node =>
      have integrated := settled.integrateSuccess found result
      have step (acc : State × List WorkQueueEvent × NewWork) (group : Execution.DeliveryNode)
          (prior : acc.1.ChildStreamsSettled)
          : (successGroupStep acc group).1.ChildStreamsSettled := by
        obtain ⟨current, events, released⟩ := acc
        dsimp only [successGroupStep]
        split
        · exact prior
        · split
          · exact (prior.putGroupNode _).finishGroupSuccess _
          · exact prior
      have processed := fold_preserves (fun acc => acc.1.ChildStreamsSettled)
        successGroupStep step node.task.groups (_, [], {}) integrated
      rw [queue.taskSuccess_eq occurrence result node found]
      split
      · exact fun node member => settled node (List.mem_filter.mp member).1
      exact (processed.startNewWork _).drainReadyGroups

/-- Task failure cannot introduce producer stream links.
Witness: failure removes its task, then filters task nodes or updates group error caches. -/
theorem State.ChildStreamsSettled.taskFailure {queue : State}
    (settled : queue.ChildStreamsSettled) (occurrence : Occurrence) (errors : Nat)
    : (queue.taskFailure occurrence errors).1.ChildStreamsSettled := by
  unfold State.taskFailure
  split
  · exact settled
  · split
    · exact fun node member => settled node (List.mem_filter.mp member).1
    apply fold_preserves
      (fun acc : State × List WorkQueueEvent => acc.1.ChildStreamsSettled)
    · intro acc group prior
      obtain ⟨current, events⟩ := acc
      dsimp only
      split
      · exact prior
      · split
        · exact prior.removeGroup _
        · exact prior
    · exact fun node member => settled node (List.mem_filter.mp member).1

/-- Item arrival registers its child streams as roots, without attaching them to tasks.
Witness: parentless integration, pruning, activation, and draining preserve settled links.
-/
theorem State.ChildStreamsSettled.streamItems {queue : State}
    (settled : queue.ChildStreamsSettled) (stream : Execution.DeliveryNode)
    (items : List StreamItem)
    : (queue.streamItems stream items).1.ChildStreamsSettled := by
  let step (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue) (item : StreamItem) :=
    let (current, groups, streams, values) := acc
    let (integrated, newWork) := current.maybeIntegrateWork item.work
    let (pruned, nonempty) := integrated.pruneEmptyGroups newWork.newGroups
    (pruned.startNewWork { newWork with newGroups := nonempty },
      groups ++ nonempty, streams ++ newWork.newStreams, values ++ [item.value])
  have folded := fold_preserves (fun acc => acc.1.ChildStreamsSettled) step
    (fun acc item prior => ((prior.integrateRoots item.work).pruneEmptyGroups _).startNewWork _)
    items (queue, [], [], []) settled
  unfold State.streamItems
  split
  · exact settled
  · exact folded.drainReadyGroups

/-- Every graph-event handler preserves the invariant, even on arbitrary host inputs.
Witness: successful settlement is the only child-stream attachment path; all other
handlers retain, create empty, or remove task nodes. -/
theorem State.ChildStreamsSettled.handleGraphEvent {queue : State}
    (settled : queue.ChildStreamsSettled) (event : GraphEvent)
    : (queue.handleGraphEvent event).1.ChildStreamsSettled := by
  cases event with
  | taskSuccess occurrence result => exact settled.taskSuccess occurrence result
  | taskFailure occurrence errors => exact settled.taskFailure occurrence errors
  | streamItems stream items => exact settled.streamItems stream items
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess]
      split <;> exact settled
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> exact settled

/-- Initialization has no unresolved task carrying child streams.
Witness: the empty task map followed by root integration, pruning, and starts. -/
theorem createWorkQueue_childStreamsSettled (work : Work)
    : (State.initialize work).ChildStreamsSettled := by
  have empty : ({} : State).ChildStreamsSettled := by simp [State.ChildStreamsSettled]
  exact ((empty.integrateRoots work).pruneEmptyGroups _).startNewWork _

/-- The real batch wrapper preserves the invariant, including absorption and termination.
Witness: the eventwise fold preserves it; the wrapper changes only the terminal flag. -/
theorem State.ChildStreamsSettled.handleGraphEvents {queue : State}
    (settled : queue.ChildStreamsSettled) (events : List GraphEvent)
    : (queue.handleGraphEvents events).1.ChildStreamsSettled := by
  have folded := fold_preserves
    (fun acc : State × List WorkQueueEvent => acc.1.ChildStreamsSettled) rawEventStep
    (fun _ event prior => prior.handleGraphEvent event) events (queue, []) settled
  rw [State.handleGraphEvents_eq_rawEventReplay]
  split
  · exact settled
  · dsimp only
    split <;> exact folded

/-- Every actual normalized replay has settled producers for its stored child streams.
Witness: unconditional preservation through every queue batch; normalization does not
change queue state. No generated-work, source-validity, or start premise is needed. -/
theorem createWorkQueue_runNormalized_childStreamsSettled (work : Work)
    (batches : List (List GraphEvent))
    : ((State.initialize work).runNormalized batches).1.ChildStreamsSettled := by
  have preserved (acc : NormalizedAcc) (batch : List GraphEvent)
      (prior : acc.1.ChildStreamsSettled)
      : (normalizedStep acc batch).1.ChildStreamsSettled := by
    rw [normalizedStep_queue]
    exact prior.handleGraphEvents batch
  exact fold_preserves (fun acc => acc.1.ChildStreamsSettled) normalizedStep preserved
    batches
    (
      State.initialize work,
      {
        active :=
          (State.initialize work).initialGroups ++ (State.initialize work).initialStreams
      },
      []
    )
    (createWorkQueue_childStreamsSettled work)

-----------------------------------------------------------------------------------------
-- A successful flush publishes the producer before announcing its child stream
-----------------------------------------------------------------------------------------

/-- Every stream released by a flush has a selected, successfully stored task producer.
Witness: the exact flush accumulates that node's child keys and value together; lookup
of the released stream recovers its key. The raw value event precedes the notice carrier.
-/
theorem State.ChildStreamsSettled.finishGroupSuccess_release {queue : State}
    (settled : queue.ChildStreamsSettled) (group : GroupNode)
    {stream : Execution.DeliveryNode}
    (released : stream ∈ (queue.finishGroupSuccess group).2.2.newStreams)
    : ∃ node ∈ queue.taskNodes,
        ∃ value values,
          node.task.occurrence ∈ group.tasks
          ∧ stream.key ∈ node.childStreams
          ∧ node.value = some value
          ∧ value ∈ values
          ∧ (queue.finishGroupSuccess group).2.1
            = [
              .groupValues group.group.node values,
              .groupSuccess group.group.node
                (queue.finishGroupSuccess group).2.2.newGroups
                (queue.finishGroupSuccess group).2.2.newStreams
            ] := by
  obtain ⟨selected, _, known, values, streams, _, _⟩ :=
    flushGroupTask_witness queue group.tasks [] []
  let flushed := group.tasks.foldl flushGroupTask (queue, [], [])
  have exactValues : flushed.2.1 = selected.filterMap TaskNode.value := values
  have exactStreams : flushed.2.2 = selected.flatMap TaskNode.childStreams := streams
  change stream ∈ flushed.2.2.filterMap
    (fun key => ((queue.finishGroupSuccess group).1.stream? key).map Stream.node) at released
  rw [exactStreams] at released
  obtain ⟨key, fromSelected, lookup⟩ := List.mem_filterMap.mp released
  obtain ⟨node, selectedNode, childKey⟩ := List.mem_flatMap.mp fromSelected
  have sameKey : stream.key = key := by
    cases found : (queue.finishGroupSuccess group).1.stream? key with
    | none => simp [found] at lookup
    | some registered =>
        have same : registered.node = stream := by simpa [found] using lookup
        rw [← same]
        exact beq_iff_eq.mp
          (List.find?_some (p := fun entry : Stream => entry.node.key == key) found)
  have hasValue : node.value ≠ none := by
    intro empty
    have noStreams := settled node (known node selectedNode).1 empty
    simp [noStreams] at childKey
  cases stored : node.value with
  | none => exact False.elim (hasValue stored)
  | some value =>
      have valueMember : value ∈ selected.filterMap TaskNode.value :=
        List.mem_filterMap.mpr ⟨node, selectedNode, stored⟩
      have nonempty : (selected.filterMap TaskNode.value).isEmpty = false := by
        cases entries : selected.filterMap TaskNode.value with
        | nil => simp [entries] at valueMember
        | cons => rfl
      refine ⟨node, (known node selectedNode).1, value, selected.filterMap TaskNode.value,
        (known node selectedNode).2, sameKey ▸ childKey, stored, valueMember, ?_⟩
      change (if flushed.2.1.isEmpty then []
        else [Execution.WorkQueueEvent.groupValues group.group.node flushed.2.1]) ++ _ = _
      rw [exactValues, nonempty]
      rfl

/-- The release witness is available after every actual normalized input prefix.
Witness: the unconditional replay invariant supplies its sole state premise; the local
flush witness identifies the stored source occurrence, not just an unrelated payload.
This does not yet identify the structural producer or prove full output admission. -/
theorem createWorkQueue_runNormalized_streamRelease (work : Work)
    (batches : List (List GraphEvent)) (group : GroupNode)
    {stream : Execution.DeliveryNode}
    (released
      : stream
        ∈ (((State.initialize work).runNormalized batches).1.finishGroupSuccess
            group).2.2.newStreams)
    : let queue := ((State.initialize work).runNormalized batches).1
      ∃ node ∈ queue.taskNodes,
        ∃ value values,
          node.task.occurrence ∈ group.tasks
          ∧ stream.key ∈ node.childStreams
          ∧ node.value = some value
          ∧ value ∈ values
          ∧ (queue.finishGroupSuccess group).2.1
            = [
              .groupValues group.group.node values,
              .groupSuccess group.group.node
                (queue.finishGroupSuccess group).2.2.newGroups
                (queue.finishGroupSuccess group).2.2.newStreams
            ] :=
  (createWorkQueue_runNormalized_childStreamsSettled work
    batches).finishGroupSuccess_release
    group released

/-- Publisher owner remapping keeps the stored producer value before its stream notice.
Witness: the flush emits values then its completion/notice carrier; normalization maps
the values in order and retains the carrier after them, regardless of owner choice.
-/
theorem State.ChildStreamsSettled.finishGroupSuccess_normalized_release {queue : State}
    (settled : queue.ChildStreamsSettled) (publisher : IncrementalPublisher)
    (group : GroupNode) {stream : Execution.DeliveryNode}
    (released : stream ∈ (queue.finishGroupSuccess group).2.2.newStreams)
    : ∃ node ∈ queue.taskNodes,
        ∃ value,
          node.task.occurrence ∈ group.tasks
          ∧ stream.key ∈ node.childStreams
          ∧ node.value = some value
          ∧ [
              Execution.WorkQueueEvent.groupValues
                (publisher.getBestIdAndSubPath group.group.node value) [value],
              .groupSuccess group.group.node
                (queue.finishGroupSuccess group).2.2.newGroups
                (queue.finishGroupSuccess group).2.2.newStreams
            ].Sublist
              (publisher.normalizeBatch (queue.finishGroupSuccess group).2.1).2 := by
  obtain ⟨node, member, value, values, task, child, stored, valueMember, output⟩ :=
    settled.finishGroupSuccess_release group released
  refine ⟨node, member, value, task, child, stored, ?_⟩
  rw [output]
  change [_, _].Sublist
    (values.map (fun value => Execution.WorkQueueEvent.groupValues
      (publisher.getBestIdAndSubPath group.group.node value) [value]) ++ [_])
  apply List.Sublist.append (l₁ := [_]) (r₁ := [_])
  · exact List.singleton_sublist.mpr (List.mem_map.mpr ⟨value, valueMember, rfl⟩)
  · exact .refl _

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
