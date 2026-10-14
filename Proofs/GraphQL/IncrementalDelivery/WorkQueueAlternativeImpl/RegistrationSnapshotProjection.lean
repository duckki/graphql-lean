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
def registrationSnapshot (queue : Kernel) : GraphEvent → Kernel
  | .taskSuccess occurrence result =>
      match queue.taskNode? occurrence with
      | none => queue
      | some task =>
          if queue.taskHasHealthyOwner task.task then
            let stored : State :=
              { queue := queue.putTaskNode { task with value := some result.value } }
            (stored.maybeIntegrateWork result.work (some occurrence)).1.queue
          else
            queue
  | .streamItems stream items =>
      if queue.rootStreams.contains stream.ref then
        (items.foldl
          (fun current item =>
            let (integrated, newWork) := current.maybeIntegrateWork item.work
            let (queue, groups) := integrated.queue.pruneEmptyGroups newWork.newGroups
            (({ integrated with queue }).startNewWork
              { newWork.newWork with newGroups := groups } newWork).1)
          ({ queue } : State)).queue
      else
        queue
  | _ => queue

/-- Reference registration before owner settlement and before the stream ready drain. -/
def eagerRegistrationSnapshot (queue : Kernel) : GraphEvent → Kernel
  | .taskSuccess occurrence result =>
      match queue.taskNode? occurrence with
      | none => queue
      | some node =>
          if queue.taskHasHealthyOwner node.task then
            ((queue.putTaskNode
                { node with value := some result.value }).maybeIntegrateWork
              result.work (some occurrence)).1
          else
            queue
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

private theorem startNewWork_state_targets (state : State)
    (roots : ReferenceWorkQueue.NewWork) (integrated : IntegratedWork)
    (targets : List CleanupTarget)
    : (state.startNewWork roots integrated targets).1
      = (state.startNewWork roots integrated).1 := by
  unfold State.startNewWork
  split <;> rfl

/-- The public snapshot's item fold is the actual receipt fold with metadata erased. -/
theorem registrationSnapshot_itemFold (queue : Kernel)
    (stream : Execution.DeliveryNode) (items : List ReferenceWorkQueue.StreamItem)
    (active : queue.rootStreams.contains stream.ref = true)
    : registrationSnapshot queue (.streamItems stream items)
      = (items.foldl streamRegistrationStep ({ queue }, [], [], [], [], [])).1.queue := by
  simp only [registrationSnapshot, active, ↓reduceIte]
  have state := List.foldl_hom (fun acc : StreamRegistrationAcc => acc.1)
    (l := items) (init := ({ queue }, [], [], [], [], [])) (g₁ := streamRegistrationStep)
    (g₂ := fun current item =>
      let integrated := current.maybeIntegrateWork item.work
      let pruned := integrated.1.queue.pruneEmptyGroups integrated.2.newGroups
      (({ integrated.1 with queue := pruned.1 }).startNewWork
        { integrated.2.newWork with newGroups := pruned.2 } integrated.2).1)
    (by
      intro acc item
      exact (startNewWork_state_targets _ _ _ _).symm)
  exact congrArg State.queue state

-----------------------------------------------------------------------------------------
-- Generated source prefixes derive the projection, not a new host law
-----------------------------------------------------------------------------------------

/-- Delayed task registration and eager stream activation preserve the needed snapshot
information at every generated raw source prefix. No batch admission is required here.
-/
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
  let queue := (ReferenceWorkQueue.State.initialize
    (ReferenceWorkQueue.Work.fromExecution work)).replayGraphEvents events
  change SnapshotProjection queue event
  have present := generated.replayGraphEvents_rootsPresent events
    (fun event member => earlier.eachMatches member)
  cases event with
  | taskSuccess occurrence result =>
      cases found : queue.taskNode? occurrence with
      | none =>
          apply SnapshotProjection.of_eq
          simp only [registrationSnapshot, eagerRegistrationSnapshot, found]
      | some node =>
          cases healthy : queue.taskHasHealthyOwner node.task with
          | false =>
              apply SnapshotProjection.of_eq
              simp only [registrationSnapshot, eagerRegistrationSnapshot, found, healthy,
                Bool.false_eq_true, ↓reduceIte]
          | true =>
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
              all_goals simp only [registrationSnapshot, eagerRegistrationSnapshot, found,
                healthy, ↓reduceIte]
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
            exact congrArg Prod.fst (referencePrefix_streamRegistrationFold generated events
              (fun event member => earlier.eachMatches member) stream items matched)
      exact SnapshotProjection.of_eq same
  | taskFailure | streamSuccess | streamFailure =>
      exact SnapshotProjection.of_eq rfl

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
  · rename_i running
    obtain ⟨flag, same⟩ := ReferenceWorkQueue.createWorkQueue_runNormalized_stateCore started
    have flagZero : flag = false := by
      have notStopped : ((ReferenceWorkQueue.State.initialize
        (ReferenceWorkQueue.Work.fromExecution work)).runNormalized inputs).1.terminated = false := by
        simpa only [Bool.false_eq_true, not_false_eq_true, Bool.eq_false_iff]
          using running
      simpa only [same] using notStopped
    let raw := (ReferenceWorkQueue.State.initialize
      (ReferenceWorkQueue.Work.fromExecution work)).replayGraphEvents inputs.flatten
    have rawFlag : raw.terminated = false := by
      change ((ReferenceWorkQueue.State.initialize
        (ReferenceWorkQueue.Work.fromExecution work)).replayGraphEvents inputs.flatten).terminated = false
      rw [← ReferenceWorkQueue.State.rawEventReplay_state,
        ReferenceWorkQueue.State.rawEventReplay_terminated]
      exact ReferenceWorkQueue.createWorkQueue_terminated _
    have update : { raw with terminated := false } = raw := by
      rw [← rawFlag]
    rw [same]
    change SnapshotProjection { raw with terminated := flag } event
    rw [flagZero, update]
    exact referencePrefix_snapshotProjection generated inputs.flatten event valid

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
