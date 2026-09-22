import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamReleaseMatching

/-! Stream activation comes only from explicitly released stream keys. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (ExecutionGroupValue)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Registration and group bookkeeping do not activate streams
-----------------------------------------------------------------------------------------

/-- A fold preserves a projection when every processing step preserves it.
Witness: list induction through the executable accumulator. -/
theorem fold_projection {α β γ : Type} (project : α → γ) (step : α → β → α)
    (preserved : ∀ state item, project (step state item) = project state)
    (items : List β) (state : α)
    : project (items.foldl step state) = project state := by
  induction items generalizing state with
  | nil => rfl
  | cons item rest ih => exact (ih _).trans (preserved state item)

/-- Group registration does not activate stream iterators.
Witness: candidate registration and parent-link updates touch only group fields. -/
theorem State.addGroups_rootStreams (queue : State) (groups : List Group)
    : (queue.addGroups groups).1.rootStreams = queue.rootStreams := by
  let link (current : State) (group : Group) :=
    match group.parent with
    | none => current
    | some parent =>
        match current.groupNode? parent with
        | none => current
        | some node =>
            let children := if node.childGroups.contains group.node.key then node.childGroups
              else node.childGroups ++ [group.node.key]
            current.putGroupNode { node with childGroups := children }
  have linked : ∀ current group, (link current group).rootStreams = current.rootStreams := by
    intro current group
    unfold link
    split
    · rfl
    · split <;> rfl
  have registered : ∀ current group,
      (State.addGroup current group).rootStreams = current.rootStreams := by
    intro current group
    unfold State.addGroup
    split
    · rfl
    · dsimp only
      split <;> rfl
  change ((groups.filter _).foldl link
    ((groups.filter _).foldl State.addGroup queue)).rootStreams = _
  rw [fold_projection State.rootStreams link linked,
    fold_projection State.rootStreams State.addGroup registered]

/-- Registering task memberships does not activate streams.
Witness: contributor-counter updates and optional task-node creation preserve rootStreams.
-/
theorem State.addTask_rootStreams (queue : State) (task : Task)
    : (queue.addTask task).rootStreams = queue.rootStreams := by
  let step (current : State) (group : Execution.DeliveryNode) :=
    match current.groupNode? group.key with
    | none => current
    | some node =>
        if node.tasks.contains task.occurrence then current
        else current.putGroupNode { node with
          tasks := node.tasks ++ [task.occurrence], pending := node.pending + 1 }
  have preserved : ∀ current group, (step current group).rootStreams = current.rootStreams := by
    intro current group
    unfold step
    split
    · rfl
    · split <;> rfl
  let current := task.groups.foldl step { queue with tasks := queue.tasks ++ [task] }
  have same : current.rootStreams = queue.rootStreams :=
    fold_projection State.rootStreams step preserved _ _
  change (if _ then { current with taskNodes := current.taskNodes ++ [({ task } : TaskNode)] }
    else current).rootStreams = _
  split <;> exact same

/-- Integrating child work registers streams without starting them.
Witness: group/task registration preserves active keys; addStreams only records descriptors
or attaches child keys to a task. Root activation is a separate startNewWork operation.
-/
theorem State.maybeIntegrateWork_rootStreams (queue : State) (work : Work)
    (parent : Option Occurrence := none)
    : (queue.maybeIntegrateWork work parent).1.rootStreams = queue.rootStreams := by
  have streams (current : State) (entries : List Stream) (producer : Option Occurrence)
      : (current.addStreams entries producer).1.rootStreams = current.rootStreams := by
    unfold State.addStreams
    split
    · rfl
    · dsimp only
      split <;> rfl
  unfold State.maybeIntegrateWork
  rw [streams, fold_projection State.rootStreams State.addTask State.addTask_rootStreams,
    State.addGroups_rootStreams]

/-- Pruning empty group shells leaves active stream keys unchanged.
Witness: every branch of the bounded traversal changes only the group map. -/
theorem State.pruneEmptyGroups_rootStreams (queue : State) (groups)
    : (queue.pruneEmptyGroups groups).1.rootStreams = queue.rootStreams := by
  have loop (fuel : Nat) (current : State) (more kept)
      : (State.pruneEmptyGroups.go fuel current more kept).1.rootStreams
        = current.rootStreams := by
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

/-- Flushing a group collects stream releases but does not yet activate them.
Witness: selected-task removal and empty-group pruning both preserve active stream keys.
-/
theorem State.finishGroupSuccess_rootStreams (queue : State) (group : GroupNode)
    : (queue.finishGroupSuccess group).1.rootStreams = queue.rootStreams := by
  have preserved : ∀ acc occurrence,
      (flushGroupTask acc occurrence).1.rootStreams = acc.1.rootStreams := by
    intro acc occurrence
    unfold flushGroupTask
    split <;> rfl
  have same := fold_projection (fun acc : State × List ExecutionGroupValue × Keys =>
    acc.1.rootStreams) flushGroupTask preserved group.tasks (queue, [], [])
  unfold State.finishGroupSuccess
  rw [State.pruneEmptyGroups_rootStreams]
  exact same

-----------------------------------------------------------------------------------------
-- Activation adds only the stream keys named in released work
-----------------------------------------------------------------------------------------

/-- Starting groups cannot start a stream as a side effect.
Witness: startTask changes only task nodes and startGroup folds that operation. -/
theorem State.startGroup_rootStreams (queue : State) (key : Nat)
    : (queue.startGroup key).rootStreams = queue.rootStreams := by
  have task : ∀ current occurrence,
      (State.startTask current occurrence).rootStreams = current.rootStreams := by
    intro current occurrence
    unfold State.startTask
    split
    · rfl
    · split <;> rfl
  unfold State.startGroup
  split
  · rfl
  · split
    · rfl
    · exact fold_projection State.rootStreams State.startTask task _ _

/-- Activating released work adds no stream key outside its explicit newStreams list.
Witness: group activation preserves active streams; each stream step is inert or appends
only its requested key. Descriptor existence and deduplication may suppress an addition.
-/
theorem State.startNewWork_rootStreams (queue : State) (work : NewWork)
    : (queue.startNewWork work).rootStreams.Subset
        (queue.rootStreams ++ work.newStreams.map Execution.DeliveryNode.key) := by
  have loop (keys : Keys) (current : State)
      : (keys.foldl State.startStream current).rootStreams.Subset
          (current.rootStreams ++ keys) := by
    induction keys generalizing current with
    | nil => intro key member; exact List.mem_append_left [] member
    | cons key rest ih =>
        intro stream member
        have next := ih (current.startStream key) member
        rcases List.mem_append.mp next with old | later
        · unfold State.startStream at old
          split at old
          · exact List.mem_append_left _ old
          · rcases List.mem_append.mp old with prior | added
            · exact List.mem_append_left _ prior
            · exact List.mem_append_right _ (List.mem_cons.mpr (.inl
                (List.mem_singleton.mp added)))
        · exact List.mem_append_right _ (List.mem_cons_of_mem key later)
  unfold State.startNewWork
  have included := loop (work.newStreams.map Execution.DeliveryNode.key)
    ((work.newGroups.map Execution.DeliveryNode.key).foldl State.startGroup
      { queue with
        rootGroups := queue.rootGroups ++ work.newGroups.map Execution.DeliveryNode.key })
  rw [fold_projection State.rootStreams State.startGroup State.startGroup_rootStreams] at included
  exact included

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
