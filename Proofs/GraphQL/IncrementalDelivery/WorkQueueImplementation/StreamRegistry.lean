import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamReferenceAtoms

/-! Stream registration retains supplied descriptors through queue bookkeeping. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (
  ExecutionGroupValue StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Group/task accounting and activation do not change the stream registry
-----------------------------------------------------------------------------------------

/-- Group registration retains the stream registry exactly.
Witness: both fresh registration and parent-linking folds touch only group fields.
-/
theorem State.addGroups_streams (queue : State) (groups : List Group)
    : (queue.addGroups groups).1.streams = queue.streams := by
  let link (current : State) (group : Group) :=
    match group.parent with
    | none => current
    | some parent =>
        match current.groupNode? parent with
        | none => current
        | some node =>
            let children := if node.childGroups.contains group.node.ref then node.childGroups
              else node.childGroups ++ [group.node.ref]
            current.putGroupNode { node with childGroups := children }
  have linked : ∀ current group, (link current group).streams = current.streams := by
    intro current group
    unfold link
    split
    · rfl
    · split <;> rfl
  have registered : ∀ current group,
      (State.addGroup current group).streams = current.streams := by
    intro current group
    unfold State.addGroup
    split
    · rfl
    · dsimp only
      split <;> rfl
  change ((groups.filter _).foldl link
    ((groups.filter _).foldl State.addGroup queue)).streams = _
  rw [fold_projection State.streams link linked,
    fold_projection State.streams State.addGroup registered]

/-- Task registration retains the stream registry exactly.
Witness: membership increments and task-node creation change no stream descriptor.
-/
theorem State.addTask_streams (queue : State) (task : Task)
    : (queue.addTask task).streams = queue.streams := by
  let step (current : State) (group : Execution.DeliveryNode) :=
    match current.groupNode? group.ref with
    | none => current
    | some node =>
        if node.tasks.contains task.occurrence then current
        else current.putGroupNode { node with
          tasks := node.tasks ++ [task.occurrence], pending := node.pending + 1 }
  have preserved : ∀ current group, (step current group).streams = current.streams := by
    intro current group
    unfold step
    split
    · rfl
    · split <;> rfl
  let current := task.groups.foldl step { queue with tasks := queue.tasks ++ [task] }
  have same : current.streams = queue.streams :=
    fold_projection State.streams step preserved _ _
  change (if _ then { current with taskNodes := current.taskNodes ++ [({ task } : TaskNode)] }
    else current).streams = _
  split <;> exact same

/-- Empty-group pruning retains stream descriptors, including inactive child streams.
Witness: every branch of the bounded traversal modifies only the group map.
-/
theorem State.pruneEmptyGroups_streams (queue : State) (groups)
    : (queue.pruneEmptyGroups groups).1.streams = queue.streams := by
  have loop (fuel : Nat) (current : State) (more kept)
      : (State.pruneEmptyGroups.go fuel current more kept).1.streams = current.streams := by
    induction fuel generalizing current more kept with
    | zero => rfl
    | succ fuel ih =>
        cases more with
        | nil => rfl
        | cons group rest =>
            simp only [State.pruneEmptyGroups.go]
            split
            · exact ih _ _ _
            · split <;> exact ih _ _ _
  exact loop _ _ _ _

/-- Successful group cleanup releases existing streams without changing their registry.
Witness: task removal, owner cleanup, and child-group pruning leave the registry untouched.
-/
theorem State.finishGroupSuccess_streams (queue : State) (group : GroupNode)
    : (queue.finishGroupSuccess group).1.streams = queue.streams := by
  have preserved : ∀ acc occurrence,
      (flushGroupTask acc occurrence).1.streams = acc.1.streams := by
    intro acc occurrence
    unfold flushGroupTask
    split <;> rfl
  have same := fold_projection (fun acc : State × List ExecutionGroupValue × NodeRefs =>
    acc.1.streams) flushGroupTask preserved group.tasks (queue, [], [])
  unfold State.finishGroupSuccess
  rw [State.pruneEmptyGroups_streams]
  exact same

/-- Starting groups and streams retains every registered stream descriptor unchanged.
Witness: group starts change task nodes; stream starts change only active root refs.
-/
theorem State.startNewWork_streams (queue : State) (work : NewWork)
    : (queue.startNewWork work).streams = queue.streams := by
  have task : ∀ current occurrence,
      (State.startTask current occurrence).streams = current.streams := by
    intro current occurrence
    unfold State.startTask
    split
    · rfl
    · split <;> rfl
  have group : ∀ current ref, (State.startGroup current ref).streams = current.streams := by
    intro current ref
    unfold State.startGroup
    split
    · rfl
    · split
      · rfl
      · exact fold_projection State.streams State.startTask task _ _
  have stream : ∀ current ref, (State.startStream current ref).streams = current.streams := by
    intro current ref
    unfold State.startStream
    split <;> rfl
  unfold State.startNewWork
  rw [fold_projection State.streams State.startStream stream,
    fold_projection State.streams State.startGroup group]

/-- Recursive draining retains the stream registry, including already-completed streams.
Witness: group cleanup and activation preserve the descriptor list in every drain step.
-/
theorem State.drainReadyGroups_streams (queue : State)
    : queue.drainReadyGroups.1.streams = queue.streams := by
  apply State.drainReadyGroups_preserves (fun current => current.streams = queue.streams)
    (valid := rfl)
  · intro current node prior _ _ _ _
    simpa only [State.startNewWork_streams, State.finishGroupSuccess_streams] using prior
  · intro current node errors prior _ _ _
    exact prior

/-- Failed tasks retain the stream registry even when removing descendant group nodes.
Witness: every contributor branch changes only group/task nodes and roots.
-/
theorem State.taskFailure_streams (queue : State) (occurrence : Occurrence) (errors : Nat)
    : (queue.taskFailure occurrence errors).1.streams = queue.streams := by
  let step (acc : State × List WorkQueueEvent) (group : Execution.DeliveryNode) :=
    match acc.1.groupNode? group.ref with
    | none => acc
    | some node =>
        if acc.1.rootGroups.contains group.ref then
          let failure := acc.1.finishGroupFailure node errors
          (failure.1, acc.2 ++ [failure.2])
        else (acc.1.putGroupNode
          { node with pending := node.pending - 1
                      failure := some (node.failure.getD 0 + errors) }, acc.2)
  have preserved : ∀ acc group, (step acc group).1.streams = acc.1.streams := by
    intro acc group
    unfold step
    split
    · rfl
    · split <;> rfl
  unfold State.taskFailure
  split
  · rfl
  · split
    · rfl
    exact fold_projection (fun acc : State × List WorkQueueEvent => acc.1.streams)
      step preserved _ _

-----------------------------------------------------------------------------------------
-- Registration and release preserve any property of supplied stream descriptors
-----------------------------------------------------------------------------------------

/-- Every stored stream descriptor satisfies `property`, independently of active status.
-/
def State.StreamsSatisfy (queue : State) (property : Execution.DeliveryNode → Prop)
    : Prop :=
  ∀ stream ∈ queue.streams, property stream.node

/-- Recursive draining preserves any property of registered stream descriptors.
Witness: the stream registry is unchanged by the complete drain.
-/
theorem State.StreamsSatisfy.drainReadyGroups {queue : State} {property}
    (known : queue.StreamsSatisfy property)
    : queue.drainReadyGroups.1.StreamsSatisfy property := by
  intro stream member
  rw [State.drainReadyGroups_streams] at member
  exact known stream member

/-- Stream integration stores and releases only supplied descriptors or existing entries.
Witness: the fresh-candidate fold is a subset of its inputs; task attachment only adds refs.
-/
theorem State.StreamsSatisfy.addStreams {queue : State} {property}
    (prior : queue.StreamsSatisfy property) (streams : List Stream)
    (parent : Option Occurrence) (supplied : ∀ stream ∈ streams, property stream.node)
    : (queue.addStreams streams parent).1.StreamsSatisfy property
      ∧ ∀ node ∈ (queue.addStreams streams parent).2, property node := by
  have fresh := freshStreams_subset queue streams
  have stored : ∀ stream ∈ queue.streams ++
      streams.foldl (fun selected stream =>
        if (queue.stream? stream.node.ref).isSome
            || selected.any (fun known => known.node.ref == stream.node.ref) then selected
        else selected ++ [stream]) [], property stream.node := by
    intro stream member
    rcases List.mem_append.mp member with old | added
    · exact prior stream old
    · exact supplied stream (fresh added)
  unfold State.addStreams
  cases parent with
  | none =>
      refine ⟨stored, ?_⟩
      intro node member
      obtain ⟨stream, selected, rfl⟩ := List.mem_map.mp member
      exact supplied stream (fresh selected)
  | some occurrence =>
      dsimp only
      split <;> exact ⟨stored, by intro node impossible; cases impossible⟩

/-- Full work integration retains descriptor properties and certifies every released stream.
Witness: group/task stages preserve the old registry, then stream registration selects only
supplied descriptors. The property may record an exact producer as well as metadata.
-/
theorem State.StreamsSatisfy.maybeIntegrateWork {queue : State} {property}
    (prior : queue.StreamsSatisfy property) (work : Work)
    (parent : Option Occurrence := none)
    (supplied : ∀ stream ∈ work.streams, property stream.node)
    : (queue.maybeIntegrateWork work parent).1.StreamsSatisfy property
      ∧ ∀ node ∈ (queue.maybeIntegrateWork work parent).2.newStreams, property node := by
  have preserved : ((work.tasks.foldl State.addTask (queue.addGroups work.groups).1)).StreamsSatisfy
      property := by
    intro stream member
    rw [fold_projection State.streams State.addTask State.addTask_streams,
      State.addGroups_streams] at member
    exact prior stream member
  exact preserved.addStreams _ _ supplied

/-- Every initialized registry entry and stream notice inherits its input descriptor property.
Witness: integrate from the empty registry, then prune/start without changing descriptors.
-/
theorem createWorkQueue_streamsSatisfy {property} (work : Work)
    (supplied : ∀ stream ∈ work.streams, property stream.node)
    : (State.initialize work).StreamsSatisfy property
      ∧ ∀ node ∈ (State.initialize work).initialStreams, property node := by
  have initial : ({} : State).StreamsSatisfy property := by
    intro stream impossible; cases impossible
  have integrated := initial.maybeIntegrateWork work none supplied
  refine ⟨?_, integrated.2⟩
  let current := ({} : State).maybeIntegrateWork work
  let pruned := current.1.pruneEmptyGroups current.2.newGroups
  intro stream member
  change stream ∈ (pruned.1.startNewWork
    { current.2 with newGroups := pruned.2 }).streams at member
  rw [State.startNewWork_streams] at member
  have same : pruned.1.streams = current.1.streams := State.pruneEmptyGroups_streams _ _
  rw [same] at member
  exact integrated.1 stream member

/-- A stream lookup returns an unchanged registered descriptor with the requested ref.
Witness: the list lookup's membership and Boolean ref-equality guarantees.
-/
theorem State.stream?_some {queue : State} {ref : NodeRef} {stream : Stream}
    (found : queue.stream? ref = some stream)
    : stream ∈ queue.streams ∧ stream.node.ref = ref := by
  exact ⟨
    List.mem_of_find?_eq_some found,
    by
      simpa using List.find?_some (p := fun stream : Stream => stream.node.ref == ref) found
  ⟩

/-- Every stream released by a group flush has a descriptor from its entry registry.
Witness: release resolves child refs by lookup; cleanup retains exactly that registry.
-/
theorem State.StreamsSatisfy.finishGroupSuccess_notices {queue : State} {property}
    (prior : queue.StreamsSatisfy property) (group : GroupNode)
    : ∀ node ∈ (queue.finishGroupSuccess group).2.2.newStreams, property node := by
  intro node member
  change node ∈ List.filterMap
    (fun ref => ((queue.finishGroupSuccess group).1.stream? ref).map Stream.node) _ at member
  obtain ⟨ref, _, found⟩ := List.mem_filterMap.mp member
  cases lookup : (queue.finishGroupSuccess group).1.stream? ref with
  | none => simp [lookup] at found
  | some stream =>
      have same : stream.node = node := by simpa [lookup] using found
      subst node
      have stored := (State.stream?_some lookup).1
      rw [State.finishGroupSuccess_streams] at stored
      exact prior stream stored

-----------------------------------------------------------------------------------------
-- Successful task and item inputs are the only sources of new registry entries
-----------------------------------------------------------------------------------------

/-- Task success retains old descriptor properties and adds only supplied child streams.
Witness: integration certifies the new registry; the contributor loop, activation, and
final drain do not change it. This remains true when no group flushes a stored value.
-/
theorem State.StreamsSatisfy.taskSuccess {queue : State} {property}
    (prior : queue.StreamsSatisfy property) (occurrence : Occurrence)
    (result : TaskResult)
    (supplied : ∀ stream ∈ result.work.streams, property stream.node)
    : (queue.taskSuccess occurrence result).1.StreamsSatisfy property := by
  have preserved : ∀ acc group,
      (successGroupStep acc group).1.streams = acc.1.streams := by
    intro acc group
    dsimp only [successGroupStep]
    split
    · rfl
    · split
      · exact State.finishGroupSuccess_streams _ _
      · rfl
  cases found : queue.taskNode? occurrence with
  | none => simpa only [State.taskSuccess, found] using prior
  | some node =>
      have installed : (queue.putTaskNode { node with value := some result.value }).StreamsSatisfy
          property := prior
      have integrated := installed.maybeIntegrateWork result.work (some occurrence) supplied
      rw [queue.taskSuccess_eq occurrence result node found]
      split
      · exact prior
      intro stream member
      rw [State.drainReadyGroups_streams, State.startNewWork_streams,
        fold_projection (fun acc : State × List WorkQueueEvent × NewWork => acc.1.streams)
          successGroupStep preserved] at member
      exact integrated.1 stream member

/-- Stream items preserve descriptor properties while integrating each item's child work.
Witness: integration certifies supplied streams; pruning, activation, and draining retain them.
-/
theorem State.StreamsSatisfy.streamItems {queue : State} {property}
    (prior : queue.StreamsSatisfy property) (stream : Execution.DeliveryNode)
    (items : List StreamItem)
    (supplied : ∀ item ∈ items, ∀ child ∈ item.work.streams, property child.node)
    : (queue.streamItems stream items).1.StreamsSatisfy property := by
  let step (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue) (item : StreamItem) :=
    let integrated := acc.1.maybeIntegrateWork item.work
    let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
    (pruned.1.startNewWork { integrated.2 with newGroups := pruned.2 },
      acc.2.1 ++ pruned.2, acc.2.2.1 ++ integrated.2.newStreams, acc.2.2.2 ++ [item.value])
  have loop (more : List StreamItem) (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue)
      (known : acc.1.StreamsSatisfy property)
      (inputs : ∀ item ∈ more, ∀ child ∈ item.work.streams, property child.node)
      : (more.foldl step acc).1.StreamsSatisfy property := by
    induction more generalizing acc with
    | nil => exact known
    | cons item rest ih =>
        apply ih
        · have integrated := known.maybeIntegrateWork item.work none
            (inputs item List.mem_cons_self)
          intro child member
          change child ∈ (State.startNewWork
            ((acc.1.maybeIntegrateWork item.work).1.pruneEmptyGroups
              (acc.1.maybeIntegrateWork item.work).2.newGroups).1 _).streams at member
          rw [State.startNewWork_streams, State.pruneEmptyGroups_streams] at member
          exact integrated.1 child member
        · intro next member
          exact inputs next (List.mem_cons_of_mem _ member)
  unfold State.streamItems
  split
  · exact prior
  · exact (loop items (queue, [], [], []) prior supplied).drainReadyGroups

/-- The child stream descriptors explicitly supplied by a host event satisfy `property`.
This is a proof projection of task/item payloads, not an additional host-source contract.
-/
def GraphEvent.ChildStreamsSatisfy (property : Execution.DeliveryNode → Prop)
    : GraphEvent → Prop
  | .taskSuccess _ result => ∀ stream ∈ result.work.streams, property stream.node
  | .streamItems _ items =>
      ∀ item ∈ items, ∀ stream ∈ item.work.streams, property stream.node
  | _ => True

/-- A handler preserves any property of its old and newly supplied stream descriptors.
Witness: only successful task/item integration adds entries; other handlers retain them.
-/
theorem State.StreamsSatisfy.handleGraphEvent {queue : State} {property}
    (prior : queue.StreamsSatisfy property) (event : GraphEvent)
    (supplied : event.ChildStreamsSatisfy property)
    : (queue.handleGraphEvent event).1.StreamsSatisfy property := by
  cases event with
  | taskSuccess occurrence result => exact prior.taskSuccess occurrence result supplied
  | taskFailure occurrence errors =>
      intro stream member
      rw [State.handleGraphEvent, State.taskFailure_streams] at member
      exact prior stream member
  | streamItems stream items => exact prior.streamItems stream items supplied
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess]
      split <;> exact prior
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> exact prior

/-- Every batch retains descriptor properties, including after termination.
Witness: the actual event replay preserves the registry invariant; terminal flag updates
and ignored post-termination inputs cannot alter its entries.
-/
theorem State.StreamsSatisfy.handleGraphEvents {queue : State} {property}
    (prior : queue.StreamsSatisfy property) (events : List GraphEvent)
    (supplied : ∀ event ∈ events, event.ChildStreamsSatisfy property)
    : (queue.handleGraphEvents events).1.StreamsSatisfy property := by
  have replay (current : State) (more : List GraphEvent)
      (known : current.StreamsSatisfy property)
      (inputs : ∀ event ∈ more, event.ChildStreamsSatisfy property)
      : (current.rawEventReplay more).1.StreamsSatisfy property := by
    induction more generalizing current with
    | nil => exact known
    | cons event rest ih =>
        rw [State.rawEventReplay_cons]
        exact ih _ (known.handleGraphEvent event (inputs event List.mem_cons_self))
          (fun next member => inputs next (List.mem_cons_of_mem _ member))
  rw [State.handleGraphEvents_eq_rawEventReplay]
  split
  · exact prior
  · dsimp only
    split <;> exact replay queue events prior supplied

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
