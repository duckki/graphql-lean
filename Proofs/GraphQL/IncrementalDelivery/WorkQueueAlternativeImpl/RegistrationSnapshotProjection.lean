import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationNormalizedReplay

/-! The delayed registration snapshot refines the former eager proof view. Completion
adds empty computation nodes; it never changes the old buffered nodes or group metadata.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement

private abbrev Kernel := ReferenceWorkQueue.State

-----------------------------------------------------------------------------------------
-- Registration phase views are proof notation, not additional production passes
-----------------------------------------------------------------------------------------

/-- Proof-only registration phase before task settlement, or after FIFO item preparation
but before ready draining. Task success retains the real delayed task-node store. The
algorithm does not construct this view, run a second registration pass or use it to decide
cleanup; endpoint/effect witnesses must be supplied separately by actual reductions.
-/
def registrationSnapshot (queue : Kernel) (event : GraphEvent)
    (available : List (WorkQueueSemantics.Occurrence × Nat) := [])
    : Kernel :=
  match event with
  | .taskSuccess occurrence result =>
      match queue.taskNode? occurrence with
      | none => queue
      | some task =>
          let stored : State :=
            { queue := queue.putTaskNode { task with value := some result.value } }
          (stored.maybeIntegrateWork result.work (some occurrence)).1.queue
  | .streamItems stream items =>
      if queue.rootStreams.contains stream.ref then
        (items.foldl (fun acc item => streamRegistrationStep acc item available)
          ({ queue }, [], [], [], [], [], [])).1.queue
      else
        queue
  | _ => queue

/-- Reference registration before owner settlement and before the stream ready drain. -/
def eagerRegistrationSnapshot (queue : Kernel) : GraphEvent → Kernel
  | .taskSuccess occurrence result =>
      match queue.taskNode? occurrence with
      | none => queue
      | some node =>
          ((queue.putTaskNode { node with value := some result.value }).maybeIntegrateWork
            result.work (some occurrence)).1
  | .streamItems stream items =>
      if queue.rootStreams.contains stream.ref then
        queue.preparedStreamItems items
      else
        queue
  | _ => queue

/-- Preserve the whole accounting core and every actual computation record. Stream
preparation has already started its active tasks, so that branch agrees exactly.
-/
structure SnapshotProjection (queue : Kernel) (event : GraphEvent) : Prop where
  core
    : registrationCore (registrationSnapshot queue event)
      = registrationCore (eagerRegistrationSnapshot queue event)
  nodes
    : (registrationSnapshot queue event).taskNodes.Subset
        (eagerRegistrationSnapshot queue event).taskNodes
  lookup
    : ∀ occurrence node,
        (registrationSnapshot queue event).taskNode? occurrence = some node
        → (eagerRegistrationSnapshot queue event).taskNode? occurrence = some node
  buffered
    : ∀ occurrence node,
        (eagerRegistrationSnapshot queue event).taskNode? occurrence = some node
        → node.value.isSome = true
        → (registrationSnapshot queue event).taskNode? occurrence = some node
  items
    : ∀ stream items,
        event = .streamItems stream items
        → registrationSnapshot queue event = eagerRegistrationSnapshot queue event

private theorem SnapshotProjection.of_eq {queue : Kernel} {event : GraphEvent}
    (same : registrationSnapshot queue event = eagerRegistrationSnapshot queue event)
    : SnapshotProjection queue event :=
  ⟨
    congrArg registrationCore same,
    same ▸ List.Subset.refl _,
    fun _ _ found => same ▸ found,
    fun _ _ found _ => same.symm ▸ found,
    fun _ _ _ => same
  ⟩

private theorem activation_nodes_subset (queue : Kernel)
    (tasks : List ReferenceWorkQueue.Task)
    : queue.taskNodes.Subset (activateRegisteredTasks queue tasks).taskNodes := by
  induction tasks generalizing queue with
  | nil => exact List.Subset.refl _
  | cons task rest ih =>
      apply List.Subset.trans (l₂ := (activateRegisteredTask queue task).taskNodes) _ (ih _)
      unfold activateRegisteredTask
      split
      · exact List.Subset.refl _
      · exact List.subset_append_left _ _

private theorem activation_buffered_lookup {queue : Kernel} {occurrence node}
    (tasks : List ReferenceWorkQueue.Task)
    (found : (activateRegisteredTasks queue tasks).taskNode? occurrence = some node)
    (stored : node.value.isSome = true)
    : queue.taskNode? occurrence = some node := by
  induction tasks generalizing queue with
  | nil => exact found
  | cons task rest ih =>
      have next := ih (queue := activateRegisteredTask queue task) found
      unfold activateRegisteredTask at next
      split at next
      · exact next
      · change (queue.taskNodes ++ ([{ task }] : List ReferenceWorkQueue.TaskNode)).find?
          (fun candidate => candidate.task.occurrence == occurrence) = some node at next
        rw [List.find?_append] at next
        cases old : queue.taskNode? occurrence with
        | some candidate =>
            change queue.taskNodes.find? _ = some candidate at old
            rw [old] at next
            cases next
            rfl
        | none =>
            change queue.taskNodes.find? _ = none at old
            simp only [old, List.find?_cons, List.find?_nil] at next
            split at next
            · cases next
              cases stored
            · cases next

/-- The public snapshot's item fold is the actual receipt fold with metadata erased. -/
theorem registrationSnapshot_itemFold (queue : Kernel)
    (stream : Execution.DeliveryNode) (items : List ReferenceWorkQueue.StreamItem)
    (active : queue.rootStreams.contains stream.ref = true)
    (available : List (WorkQueueSemantics.Occurrence × Nat) := [])
    : registrationSnapshot queue (.streamItems stream items) available
      = (items.foldl (fun acc item => streamRegistrationStep acc item available)
          ({ queue }, [], [], [], [], [], [])).1.queue := by
  simp only [registrationSnapshot, active, ↓reduceIte]

-----------------------------------------------------------------------------------------
-- Generated source prefixes derive the projection, not a new host law
-----------------------------------------------------------------------------------------

/-- Concrete structural certificates give the delayed registration snapshot projection.
The snapshot follows the actual item fold, including cumulative cleanup targets; these
proof views add no host law or alternate production pass.
-/
theorem snapshotProjection_of_structuralFrames {queue : Kernel} {work : Work}
    {parents : Nat → WorkQueueSemantics.NodeRefs}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          ReferenceWorkQueue.GroupRecordAt work node dependencies
          → dependencies = parents node.ref)
    (roots : ReferenceWorkQueue.LiveRootFrame queue work parents)
    (retired : queue.UncancelledRetiredAncestors work)
    (owners : queue.TaskOwnerFrame work) (children : queue.ChildGroupsUnique)
    (keys : queue.TaskNodeKeysUnique) (event : GraphEvent)
    (matched : event.MatchesWork work)
    : SnapshotProjection queue event := by
  have present := roots.present
  cases event with
  | taskSuccess occurrence result =>
      cases found : queue.taskNode? occurrence with
      | none =>
          apply SnapshotProjection.of_eq
          simp only [registrationSnapshot, eagerRegistrationSnapshot, found]
      | some node =>
          let stored : State :=
            { queue := queue.putTaskNode { node with value := some result.value } }
          let integrated := stored.maybeIntegrateWork result.work (some occurrence)
          have ready : ∀ key, some occurrence = some key
              → (stored.queue.taskNode? key).isSome = true := by
            intro key same
            cases same
            change ((queue.putTaskNode { node with value := some result.value }).taskNode?
              occurrence).isSome = true
            rw [ReferenceWorkQueue.State.putTaskNode_lookup_same found
              { node with value := some result.value }
              (ReferenceWorkQueue.State.taskNode?_some found).2]
            rfl
          have complete := stored.maybeIntegrateWork_complete result.work present
            (some occurrence) ready
          dsimp only at complete
          refine ⟨?_, ?_, ?_, ?_, by intro _ _ impossible; cases impossible⟩
          all_goals simp only [registrationSnapshot, eagerRegistrationSnapshot, found]
          · exact stored.maybeIntegrateWork_registrationCore result.work (some occurrence)
          · change integrated.1.queue.taskNodes.Subset
              (stored.queue.maybeIntegrateWork result.work (some occurrence)).1.taskNodes
            rw [← complete.1]
            exact activation_nodes_subset _ _
          · intro key candidate lookup
            rw [← complete.1]
            exact activateRegisteredTasks_lookup lookup _
          · intro key candidate lookup stored
            rw [← complete.1] at lookup
            exact activation_buffered_lookup _ lookup stored
  | streamItems stream items =>
      have same : registrationSnapshot queue (.streamItems stream items)
          = eagerRegistrationSnapshot queue (.streamItems stream items) := by
        cases active : queue.rootStreams.contains stream.ref with
        | false => simp only [registrationSnapshot, eagerRegistrationSnapshot, active,
            Bool.false_eq_true, ↓reduceIte]
        | true =>
            rw [registrationSnapshot_itemFold queue stream items active]
            simp only [eagerRegistrationSnapshot, active, ↓reduceIte]
            have known : ∀ item ∈ items,
                ∀ task ∈ item.work.tasks, ReferenceWorkQueue.TaskMatches work task := by
              intro item member task supplied
              obtain ⟨address, payload, same, located⟩ :=
                matched.streamItem_childTask_producer member supplied
              exact ⟨⟨address, payload, some item.occurrence, same, located⟩,
                matched.streamItem_childTask_groupsExact member supplied⟩
            have fold := streamRegistrationFold_projection_of_unavailableChildren
              ({ queue }, [], [], [], [], [], []) items rfl known []
              (by intro item _ task _ member; cases member) (by
                intro before item after partition
                have included : before.Subset items := by
                  intro supplied member
                  rw [partition]
                  exact List.mem_append_left _ member
                have member : item ∈ items := by
                  rw [partition]
                  exact List.mem_append_right _ List.mem_cons_self
                have partialMatch : (ReferenceWorkQueue.GraphEvent.streamItems stream before
                    ).MatchesWork work := fun item member => matched item (included member)
                have preparedRoots := (roots.prepareItems retired generated canonical
                  partialMatch).1
                have preparedOwners := owners.prepareItems_of_registered roots.registered
                  roots.tasks roots.present generated.declarations partialMatch
                have preparedKeys : (queue.preparedStreamItems before).TaskNodeKeysUnique := by
                  apply ReferenceWorkQueue.State.preparedStreamItems_preserves
                    (fun current => current.TaskNodeKeysUnique) keys before []
                  intro current item _ prior
                  exact ((prior.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _
                have startup := streamItem_startFrames generated canonical roots retired owners
                  children stream items matched before included item member []
                exact ⟨preparedRoots.present, preparedOwners.matching, preparedKeys,
                  parents, startup⟩)
            exact congrArg Prod.fst fold
      exact SnapshotProjection.of_eq same
  | taskFailure | groupFailure | streamSuccess | streamFailure =>
      exact SnapshotProjection.of_eq rfl

/-- A generated raw event prefix supplies snapshot certificates without extra admission. -/
theorem referencePrefix_snapshotProjection {work : Work}
    (generated : ReferenceWorkQueue.ExecutedWork work) (events : List GraphEvent)
    (event : GraphEvent)
    (valid : ReferenceWorkQueue.ValidGraphEvents work (events ++ [event]))
    : let queue :=
        (ReferenceWorkQueue.State.initialize
          (ReferenceWorkQueue.Work.fromExecution work)).replayGraphEvents
          events
      SnapshotProjection queue event := by
  obtain ⟨earlier, matched, _⟩ := ReferenceWorkQueue.validGraphEvents_last valid
  obtain ⟨parents, canonical, owners, roots, retired⟩ :=
    generated.batchPrefix_structuralFrames [] events (by simp)
      (fun _ member => earlier.eachMatches member) []
  exact snapshotProjection_of_structuralFrames generated canonical roots retired owners
    ((ReferenceWorkQueue.createWorkQueue_childGroupsUnique
        (ReferenceWorkQueue.Work.fromExecution work)).replayGraphEvents
      events)
    ((ReferenceWorkQueue.createWorkQueue_taskNodeKeysUnique
        (ReferenceWorkQueue.Work.fromExecution work)).replayGraphEvents
      events) event matched

/-- The normalized actual state inherits the same projection; retired snapshots are empty. -/
theorem generatedSnapshot_projection {work inputs event}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (valid : ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ [event]))
    (started : ReferenceWorkQueue.inputsStarted work inputs = true)
    : SnapshotProjection ((State.initialize work).runNormalized inputs).1.queue
        event := by
  obtain ⟨earlier, _, _⟩ := ReferenceWorkQueue.validGraphEvents_last valid
  rw [State.runNormalized_initialize work inputs generated earlier started]
  simp only [State.fromReference]
  split
  · apply SnapshotProjection.of_eq
    cases event <;>
      simp only [registrationSnapshot, eagerRegistrationSnapshot, State.clearRecords,
        ReferenceWorkQueue.State.taskNode?, List.find?_nil, List.contains_nil,
        Bool.false_eq_true, ↓reduceIte]
  · obtain ⟨parents, canonical, roots, retired⟩ := generated.runNormalized_liveRootFrame inputs
      (fun _ member => earlier.eachMatches member)
    have owners := generated.runNormalized_taskOwnerFrame_of_matching inputs
      (fun _ member => earlier.eachMatches member)
    exact snapshotProjection_of_structuralFrames generated canonical roots retired owners
      ((ReferenceWorkQueue.createWorkQueue_childGroupsUnique
        (ReferenceWorkQueue.Work.fromExecution work)).runNormalized inputs)
      ((ReferenceWorkQueue.createWorkQueue_taskNodeKeysUnique
        (ReferenceWorkQueue.Work.fromExecution work)).runNormalized inputs)
      event (ReferenceWorkQueue.validGraphEvents_last valid).2.1

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue

/-- Actual delayed registration retains every existing node except the explicit stream
attachment producer. It neither inserts nor overwrites a fresh task node here.
-/
theorem State.maybeIntegrateWork_lookup_other {state : State} {occurrence node}
    (found : state.queue.taskNode? occurrence = some node)
    (work : ReferenceWorkQueue.Work)
    (producer : Option WorkQueueSemantics.Occurrence := none)
    (different : producer ≠ some occurrence := by simp)
    : (state.maybeIntegrateWork work producer).1.queue.taskNode? occurrence
      = some node := by
  have grouped : (state.queue.addGroups work.groups).1.taskNode? occurrence = some node := by
    simpa only [ReferenceWorkQueue.State.taskNode?,
      ReferenceWorkQueue.State.addGroups_taskNodes]
      using found
  let initial : State × List ReferenceWorkQueue.Task × List ReferenceWorkQueue.Task :=
    ({ state with queue := (state.queue.addGroups work.groups).1 }, [], [])
  have loop (tasks : List ReferenceWorkQueue.Task)
      (acc : State × List ReferenceWorkQueue.Task × List ReferenceWorkQueue.Task)
      (prior : acc.1.queue.taskNode? occurrence = some node)
      : (tasks.foldl registerTaskStep acc).1.queue.taskNode? occurrence = some node := by
    induction tasks generalizing acc with
    | nil => exact prior
    | cons task rest ih =>
        apply ih
        have next : (acc.1.addTask task).1.queue.taskNode? occurrence = some node := by
          change ((acc.1.addTask task).1.queue.taskNodes.find? _) = some node
          rw [State.addTask_taskNodes]
          exact prior
        unfold registerTaskStep
        dsimp only
        split <;> exact next
  have retained := loop work.tasks initial grouped
  let registered := (work.tasks.foldl registerTaskStep initial).1.queue
  change (registered.addStreams work.streams producer).1.taskNode? occurrence = some node
  cases producer with
  | none => exact retained
  | some parent =>
      simp only [ReferenceWorkQueue.State.addStreams]
      split
      · exact retained
      · rename_i owner lookup
        exact ReferenceWorkQueue.State.putTaskNode_lookup_other retained _ (by
          intro same
          exact different (congrArg some
            ((ReferenceWorkQueue.State.taskNode?_some lookup).2.symm.trans same)))

end GraphQL.IncrementalDelivery.AlternativeWorkQueue
