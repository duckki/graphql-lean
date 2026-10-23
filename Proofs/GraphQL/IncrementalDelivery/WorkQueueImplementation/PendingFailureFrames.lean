import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitializationSpecialization
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamPreparation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ReadyDrain
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupFrames

/-! Only control dispatch consumes the pending internal-notice FIFO. Ordinary handlers
return enqueue effects separately and leave existing notices in place. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (ExecutionGroupValue WorkQueueEvent)
open WorkQueueSemantics (Occurrence NodeRefs)

private theorem fold_projection {α β γ : Type} (project : β → γ) (step : β → α → β)
    (preserved : ∀ current item, project (step current item) = project current)
    (items : List α) (initial : β)
    : project (items.foldl step initial) = project initial := by
  induction items generalizing initial with
  | nil => rfl
  | cons item rest ih => exact (ih _).trans (preserved initial item)

@[simp]
theorem State.putGroupNode_groupFailureEvents (queue : State) (node : GroupNode)
    : (queue.putGroupNode node).groupFailureEvents = queue.groupFailureEvents :=
  rfl

@[simp]
theorem State.putTaskNode_groupFailureEvents (queue : State) (node : TaskNode)
    : (queue.putTaskNode node).groupFailureEvents = queue.groupFailureEvents :=
  rfl

@[simp]
theorem State.removeTask_groupFailureEvents (queue : State) (task : Occurrence)
    : (queue.removeTask task).groupFailureEvents = queue.groupFailureEvents :=
  rfl

@[simp]
theorem State.removeGroup_groupFailureEvents (queue : State) (ref : NodeRef)
    : (queue.removeGroup ref).groupFailureEvents = queue.groupFailureEvents :=
  rfl

@[simp]
theorem State.addGroup_groupFailureEvents (queue : State) (group : Group)
    : (queue.addGroup group).groupFailureEvents = queue.groupFailureEvents := by
  unfold State.addGroup
  split
  · rfl
  · split
    · rfl
    · split
      · split <;> rfl
      · rfl

@[simp]
theorem State.addGroups_groupFailureEvents (queue : State) (groups : List Group)
    : (queue.addGroups groups).1.groupFailureEvents = queue.groupFailureEvents := by
  exact State.addGroups_projection State.groupFailureEvents
    State.addGroup_groupFailureEvents queue groups

@[simp]
theorem State.addTask_groupFailureEvents (queue : State) (task : Task)
    : (queue.addTask task).groupFailureEvents = queue.groupFailureEvents := by
  unfold State.addTask
  dsimp only
  split <;> apply fold_projection State.groupFailureEvents _ (by
    intro current group
    split
    · rfl
    · split <;> rfl)

@[simp]
theorem State.addStreams_groupFailureEvents (queue : State) (streams : List Stream)
    (producer : Option Occurrence)
    : (queue.addStreams streams producer).1.groupFailureEvents
      = queue.groupFailureEvents := by
  unfold State.addStreams
  dsimp only
  split
  · rfl
  · split <;> rfl

@[simp]
theorem State.maybeIntegrateWork_groupFailureEvents (queue : State) (work : Work)
    (producer : Option Occurrence := none)
    : (queue.maybeIntegrateWork work producer).1.groupFailureEvents
      = queue.groupFailureEvents := by
  simp only [State.maybeIntegrateWork, State.addStreams_groupFailureEvents]
  rw [fold_projection State.groupFailureEvents _ State.addTask_groupFailureEvents]
  exact queue.addGroups_groupFailureEvents work.groups

@[simp]
theorem State.pruneEmptyGroups_groupFailureEvents (queue : State)
    (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.groupFailureEvents
      = queue.groupFailureEvents := by
  have loop (fuel : Nat) (current : State) (remaining kept : List Execution.DeliveryNode)
      : (State.pruneEmptyGroups.go fuel current remaining kept).1.groupFailureEvents
        = current.groupFailureEvents := by
    induction fuel generalizing current remaining kept with
    | zero => rfl
    | succ fuel ih =>
        cases remaining with
        | nil => rfl
        | cons group rest =>
            simp only [State.pruneEmptyGroups.go]
            split
            · exact ih _ _ _
            · split <;> exact ih _ _ _
  exact loop _ _ _ _

@[simp]
theorem State.startTask_groupFailureEvents (queue : State) (task : Occurrence)
    (available : List (Occurrence × Nat))
    : (queue.startTask task available).groupFailureEvents = queue.groupFailureEvents := by
  unfold State.startTask
  split
  · rfl
  · split <;> rfl

@[simp]
theorem State.finishGroupSuccess_groupFailureEvents (queue : State) (group : GroupNode)
    : (queue.finishGroupSuccess group).1.groupFailureEvents
      = queue.groupFailureEvents := by
  unfold State.finishGroupSuccess
  dsimp only
  rw [State.pruneEmptyGroups_groupFailureEvents]
  exact fold_projection
    (fun acc : State × List ExecutionGroupValue × NodeRefs =>
      acc.1.groupFailureEvents)
    _
    (by
      intro acc occurrence
      rcases acc with ⟨current, values, streams⟩
      dsimp only
      split <;> rfl)
    _ _

@[simp]
theorem State.startGroup_groupFailureEvents (queue : State) (ref : NodeRef)
    (available : List (Occurrence × Nat))
    : (queue.startGroup ref available).1.groupFailureEvents
      = queue.groupFailureEvents := by
  unfold State.startGroup
  dsimp only
  split
  · exact queue.cacheTaskFailures_groupFailureEvents available
  · split
    · rw [fold_projection State.groupFailureEvents _
        (fun current task => current.startTask_groupFailureEvents task available)]
      exact queue.cacheTaskFailures_groupFailureEvents available
    · exact queue.cacheTaskFailures_groupFailureEvents available

@[simp]
theorem State.startStream_groupFailureEvents (queue : State) (ref : NodeRef)
    : (queue.startStream ref).groupFailureEvents = queue.groupFailureEvents := by
  unfold State.startStream
  split <;> rfl

@[simp]
theorem State.startNewWork_groupFailureEvents (queue : State) (work : NewWork)
    (available : List (Occurrence × Nat))
    : (queue.startNewWork work available).1.groupFailureEvents
      = queue.groupFailureEvents := by
  unfold State.startNewWork
  dsimp only
  rw [fold_projection State.groupFailureEvents _ State.startStream_groupFailureEvents]
  exact fold_projection
    (fun acc : State × List GroupFailureEvent => acc.1.groupFailureEvents) _
    (by intro acc ref; exact acc.1.startGroup_groupFailureEvents ref available) _ _

@[simp]
theorem State.taskFailure_groupFailureEvents (queue : State)
    (occurrence : Occurrence) (errors : Nat)
    : (queue.taskFailure occurrence errors).1.groupFailureEvents
      = queue.groupFailureEvents := by
  unfold State.taskFailure
  split
  · rfl
  · exact fold_projection (fun acc : State × List WorkQueueEvent => acc.1.groupFailureEvents)
      _ (by
        intro acc group
        rcases acc with ⟨current, events⟩
        dsimp only
        split
        · rfl
        · split <;> rfl) _ _

@[simp]
theorem State.drainReadyGroups_groupFailureEvents (queue : State)
    (available : List (Occurrence × Nat))
    : (queue.drainReadyGroups available).1.groupFailureEvents
      = queue.groupFailureEvents := by
  apply State.drainReadyGroups_preserves (fun current =>
    current.groupFailureEvents = queue.groupFailureEvents) (valid := rfl)
  intro current node prior _ _ _
  simpa only [State.startNewWork_groupFailureEvents,
    State.finishGroupSuccess_groupFailureEvents] using prior

@[simp]
theorem State.taskSuccess_groupFailureEvents (queue : State)
    (occurrence : Occurrence) (result : TaskResult) (available : List (Occurrence × Nat))
    : (queue.taskSuccess occurrence result available).1.groupFailureEvents
      = queue.groupFailureEvents := by
  unfold State.taskSuccess
  split
  · rfl
  · simp only [State.drainReadyGroups_groupFailureEvents, State.startNewWork_groupFailureEvents]
    rw [fold_projection (fun acc : State × List WorkQueueEvent × NewWork =>
      acc.1.groupFailureEvents) _ (by
        intro acc group
        rcases acc with ⟨current, events, released⟩
        dsimp only
        split
        · rfl
        · split
          · simp only [State.finishGroupSuccess_groupFailureEvents,
              State.putGroupNode_groupFailureEvents]
          · rfl)]
    simp only [State.maybeIntegrateWork_groupFailureEvents, State.putTaskNode_groupFailureEvents]

@[simp]
theorem State.integrateStreamItem_groupFailureEvents (queue : State) (item : StreamItem)
    (available : List (Occurrence × Nat))
    : (queue.integrateStreamItem item available).groupFailureEvents
      = queue.groupFailureEvents := by
  simp only [State.integrateStreamItem, State.startNewWork_groupFailureEvents,
    State.pruneEmptyGroups_groupFailureEvents, State.maybeIntegrateWork_groupFailureEvents]

@[simp]
theorem State.streamItems_groupFailureEvents (queue : State)
    (stream : Execution.DeliveryNode) (items : List StreamItem)
    (available : List (Occurrence × Nat))
    : (queue.streamItems stream items available).1.groupFailureEvents
      = queue.groupFailureEvents := by
  rw [queue.streamItems_eq stream items available]
  split
  · rfl
  · rw [State.drainReadyGroups_groupFailureEvents]
    apply State.preparedStreamItems_preserves (fun current =>
      current.groupFailureEvents = queue.groupFailureEvents) rfl items available
    intro current item _ prior
    simpa only [State.integrateStreamItem_groupFailureEvents] using prior

/-- Initialization without a supplied cache has no pending internal notice. -/
@[simp]
theorem State.initialize_groupFailureEvents (work : Work)
    : (State.initialize work).groupFailureEvents = [] := by
  rw [State.initialize_empty_eq_activation]
  simp only [State.startNewWork_groupFailureEvents,
    State.pruneEmptyGroups_groupFailureEvents, State.maybeIntegrateWork_groupFailureEvents]

/-- Ordinary callbacks leave existing notices in place and return new enqueue effects. -/
theorem State.handleGraphEvent_groupFailureEvents_eq (queue : State)
    (event : GraphEvent) (available : List (Occurrence × Nat))
    (ordinary : ∀ failure, event ≠ .groupFailure failure)
    : (queue.handleGraphEvent event available).1.groupFailureEvents
      = queue.groupFailureEvents := by
  cases event with
  | taskSuccess | taskFailure | streamItems =>
      simp only [State.handleGraphEvent, State.taskSuccess_groupFailureEvents,
        State.taskFailure_groupFailureEvents, State.streamItems_groupFailureEvents,
        State.cacheTaskFailures_groupFailureEvents]
  | streamSuccess =>
      simp only [State.handleGraphEvent, State.streamSuccess]
      split <;> exact queue.cacheTaskFailures_groupFailureEvents available
  | streamFailure =>
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> exact queue.cacheTaskFailures_groupFailureEvents available
  | groupFailure notice => exact (ordinary notice rfl).elim

/-- A handler can consume existing pending notices but never invents entries there.
Its new startup notices remain separate enqueue effects until dispatch realizes them. -/
theorem State.handleGraphEvent_groupFailureEvents_subset (queue : State)
    (event : GraphEvent) (available : List (Occurrence × Nat))
    : (queue.handleGraphEvent event available).1.groupFailureEvents.Subset
        queue.groupFailureEvents := by
  cases event with
  | taskSuccess | taskFailure | streamItems =>
      simp only [State.handleGraphEvent, State.taskSuccess_groupFailureEvents,
        State.taskFailure_groupFailureEvents, State.streamItems_groupFailureEvents,
        State.cacheTaskFailures_groupFailureEvents]
      exact fun _ member => member
  | streamSuccess =>
      simp only [State.handleGraphEvent, State.streamSuccess]
      split <;> intro entry member <;>
        simpa only [State.cacheTaskFailures_groupFailureEvents] using member
  | streamFailure =>
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> intro entry member <;>
        simpa only [State.cacheTaskFailures_groupFailureEvents] using member
  | groupFailure notice =>
      simp only [State.handleGraphEvent, State.groupFailure]
      split
      · exact fun _ member => by
          simpa only [State.cacheTaskFailures_groupFailureEvents] using member
      · rename_i head rest same
        split
        · intro entry member
          rw [← State.cacheTaskFailures_groupFailureEvents queue available, same]
          exact List.mem_cons_of_mem _ member
        · exact fun _ member => by
            simpa only [State.cacheTaskFailures_groupFailureEvents] using member

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
