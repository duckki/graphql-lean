import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SourceOutputBlocks
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.OutputShape
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamActivation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ReadyDrain

/-! Only the batch wrapper terminates the queue or emits its terminal marker. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (
  ExecutionGroupValue StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Registration and activation preserve the termination flag
-----------------------------------------------------------------------------------------

/-- Group registration and parent linking leave the termination flag unchanged.
Witness: both registration folds modify only group bookkeeping.
-/
theorem State.addGroups_terminated (queue : State) (groups : List Group)
    : (queue.addGroups groups).1.terminated = queue.terminated := by
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
  have linked : ∀ current group, (link current group).terminated = current.terminated := by
    intro current group
    unfold link
    split
    · rfl
    · split <;> rfl
  have registered : ∀ current group,
      (State.addGroup current group).terminated = current.terminated := by
    intro current group
    unfold State.addGroup
    split
    · rfl
    · dsimp only
      split <;> rfl
  change ((groups.filter _).foldl link
    ((groups.filter _).foldl State.addGroup queue)).terminated = _
  rw [fold_projection State.terminated link linked,
    fold_projection State.terminated State.addGroup registered]

/-- Task registration never terminates the queue.
Witness: contributor updates and optional start bookkeeping preserve the flag.
-/
theorem State.addTask_terminated (queue : State) (task : Task)
    : (queue.addTask task).terminated = queue.terminated := by
  let step (current : State) (group : Execution.DeliveryNode) :=
    match current.groupNode? group.ref with
    | none => current
    | some node =>
        if node.tasks.contains task.occurrence then current
        else current.putGroupNode { node with
          tasks := node.tasks ++ [task.occurrence], pending := node.pending + 1 }
  have preserved : ∀ current group, (step current group).terminated = current.terminated := by
    intro current group
    unfold step
    split
    · rfl
    · split <;> rfl
  let current := task.groups.foldl step { queue with tasks := queue.tasks ++ [task] }
  have same : current.terminated = queue.terminated :=
    fold_projection State.terminated step preserved _ _
  change (if _ then { current with taskNodes := current.taskNodes ++ [({ task } : TaskNode)] }
    else current).terminated = _
  split <;> exact same

/-- Child integration preserves the termination flag regardless of its work shape.
Witness: group/task registration and stream attachment modify separate state fields.
-/
theorem State.maybeIntegrateWork_terminated (queue : State) (work : Work)
    (parent : Option Occurrence := none)
    : (queue.maybeIntegrateWork work parent).1.terminated = queue.terminated := by
  have streams (current : State) (entries : List Stream) (producer : Option Occurrence)
      : (current.addStreams entries producer).1.terminated = current.terminated := by
    unfold State.addStreams
    split
    · rfl
    · dsimp only
      split <;> rfl
  unfold State.maybeIntegrateWork
  rw [streams, fold_projection State.terminated State.addTask State.addTask_terminated,
    State.addGroups_terminated]

/-- Pruning empty shells does not decide queue termination.
Witness: induction over the pruning budget; every branch retains the flag.
-/
theorem State.pruneEmptyGroups_terminated (queue : State) (groups)
    : (queue.pruneEmptyGroups groups).1.terminated = queue.terminated := by
  have loop (fuel : Nat) (current : State) (more kept)
      : (State.pruneEmptyGroups.go fuel current more kept).1.terminated
        = current.terminated := by
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

/-- Activating released groups and streams retains the termination flag.
Witness: starting tasks or roots touches only the corresponding registries.
-/
theorem State.startNewWork_terminated (queue : State) (released : NewWork)
    : (queue.startNewWork released).terminated = queue.terminated := by
  have task : ∀ current occurrence,
      (State.startTask current occurrence).terminated = current.terminated := by
    intro current occurrence
    unfold State.startTask
    split
    · rfl
    · split <;> rfl
  have group : ∀ current ref,
      (State.startGroup current ref).terminated = current.terminated := by
    intro current ref
    unfold State.startGroup
    split
    · rfl
    · split
      · rfl
      · exact fold_projection State.terminated State.startTask task _ _
  have stream : ∀ current ref,
      (State.startStream current ref).terminated = current.terminated := by
    intro current ref
    unfold State.startStream
    split <;> rfl
  unfold State.startNewWork
  rw [fold_projection State.terminated State.startStream stream,
    fold_projection State.terminated State.startGroup group]

/-- Initialization leaves termination to the first actual batch boundary, even when
all roots are already empty. Witness: integration, pruning, and activation preserve false.
-/
theorem createWorkQueue_terminated (work : Work)
    : (State.initialize work).terminated = false := by
  unfold State.initialize
  dsimp only
  rw [State.startNewWork_terminated, State.pruneEmptyGroups_terminated,
    State.maybeIntegrateWork_terminated]

-----------------------------------------------------------------------------------------
-- Individual settlements and recursive release cannot terminate the queue
-----------------------------------------------------------------------------------------

/-- Successful group release leaves termination to the enclosing batch.
Witness: flushing removes task memberships and pruning only removes group shells.
-/
theorem State.finishGroupSuccess_terminated (queue : State) (group : GroupNode)
    : (queue.finishGroupSuccess group).1.terminated = queue.terminated := by
  have preserved : ∀ acc occurrence,
      (flushGroupTask acc occurrence).1.terminated = acc.1.terminated := by
    intro acc occurrence
    unfold flushGroupTask
    split <;> rfl
  have same := fold_projection (fun acc : State × List ExecutionGroupValue × NodeRefs =>
    acc.1.terminated) flushGroupTask preserved group.tasks (queue, [], [])
  unfold State.finishGroupSuccess
  rw [State.pruneEmptyGroups_terminated]
  exact same

/-- Recursive release preserves the flag, including cached-failure removal.
Witness: the drain induction composes flag-preserving closure and activation steps.
-/
theorem State.drainReadyGroups_terminated (queue : State)
    : queue.drainReadyGroups.1.terminated = queue.terminated := by
  apply State.drainReadyGroups_preserves (fun current => current.terminated = queue.terminated)
  · intro current node same _ _ _ _
    rw [State.startNewWork_terminated, State.finishGroupSuccess_terminated]
    exact same
  · intro current node errors same _ _ _
    exact same
  · rfl

/-- Task success cannot terminate mid-batch, even when it drains every active group.
Witness: the owner fold and final drain preserve the flag; ignored outcomes only remove
task bookkeeping.
-/
theorem State.taskSuccess_terminated (queue : State) (occurrence : Occurrence)
    (result : TaskResult)
    : (queue.taskSuccess occurrence result).1.terminated = queue.terminated := by
  have preserved : ∀ acc group,
      (successGroupStep acc group).1.terminated = acc.1.terminated := by
    intro acc group
    obtain ⟨current, events, released⟩ := acc
    dsimp only [successGroupStep]
    split
    · rfl
    · split
      · exact State.finishGroupSuccess_terminated _ _
      · rfl
  cases found : queue.taskNode? occurrence with
  | none => simp [State.taskSuccess, found]
  | some node =>
      rw [queue.taskSuccess_eq occurrence result node found]
      split
      · rfl
      · dsimp only
        rw [State.drainReadyGroups_terminated, State.startNewWork_terminated,
          fold_projection (fun acc : State × List WorkQueueEvent × NewWork =>
            acc.1.terminated) successGroupStep preserved]
        exact State.maybeIntegrateWork_terminated _ _ (some occurrence)

/-- Failed task settlement retains the flag for accepted, cached, and ignored outcomes.
Witness: owner processing either removes a subtree or updates its retained failure.
-/
theorem State.taskFailure_terminated (queue : State) (occurrence : Occurrence)
    (errors : Nat)
    : (queue.taskFailure occurrence errors).1.terminated = queue.terminated := by
  let step (acc : State × List WorkQueueEvent) (group : Execution.DeliveryNode) :=
    match acc.1.groupNode? group.ref with
    | none => acc
    | some node =>
        if acc.1.rootGroups.contains group.ref then
          let (next, failure) := acc.1.finishGroupFailure node errors
          (next, acc.2 ++ [failure])
        else (acc.1.putGroupNode
          { node with pending := node.pending - 1
                      failure := some (node.failure.getD 0 + errors) }, acc.2)
  have preserved : ∀ acc group, (step acc group).1.terminated = acc.1.terminated := by
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
    · exact fold_projection (fun acc : State × List WorkQueueEvent => acc.1.terminated)
        step preserved _ _

/-- Stream item integration and child release retain the termination flag.
Witness: each item registers/prunes/activates work before the flag-preserving drain.
-/
theorem State.streamItems_terminated (queue : State) (stream : Execution.DeliveryNode)
    (items : List StreamItem)
    : (queue.streamItems stream items).1.terminated = queue.terminated := by
  let step (acc : State × List Execution.DeliveryNode × List Execution.DeliveryNode
      × List StreamItemValue) (item : StreamItem) :=
    let integrated := acc.1.maybeIntegrateWork item.work
    let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
    (pruned.1.startNewWork { integrated.2 with newGroups := pruned.2 },
      acc.2.1 ++ pruned.2, acc.2.2.1 ++ integrated.2.newStreams,
      acc.2.2.2 ++ [item.value])
  have preserved : ∀ acc item, (step acc item).1.terminated = acc.1.terminated := by
    intro acc item
    dsimp only [step]
    rw [State.startNewWork_terminated, State.pruneEmptyGroups_terminated,
      State.maybeIntegrateWork_terminated]
  unfold State.streamItems
  split
  · rfl
  · dsimp only
    rw [State.drainReadyGroups_terminated]
    exact fold_projection (fun acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue => acc.1.terminated)
      step preserved _ _

/-- Every individual source handler preserves the termination flag without host premises.
Witness: the task/item proofs and direct stream-closure state updates.
-/
theorem State.handleGraphEvent_terminated (queue : State) (event : GraphEvent)
    : (queue.handleGraphEvent event).1.terminated = queue.terminated := by
  cases event with
  | taskSuccess occurrence result => exact queue.taskSuccess_terminated occurrence result
  | taskFailure occurrence errors => exact queue.taskFailure_terminated occurrence errors
  | streamItems stream items => exact queue.streamItems_terminated stream items
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess]
      split <;> rfl
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> rfl

/-- Eventwise replay cannot terminate between supplied batch boundaries.
Witness: induction through the actual handler sequence, preserving the incoming flag.
-/
theorem State.rawEventReplay_terminated (queue : State) (events : List GraphEvent)
    : (queue.rawEventReplay events).1.terminated = queue.terminated := by
  induction events generalizing queue with
  | nil => rfl
  | cons event rest ih =>
      rw [State.rawEventReplay_cons]
      exact (ih _).trans (queue.handleGraphEvent_terminated event)

-----------------------------------------------------------------------------------------
-- Handlers and publisher normalization cannot invent a terminal marker
-----------------------------------------------------------------------------------------

/-- A group flush emits optional values and one group completion, never termination.
Witness: the exact selected-publication output equation.
-/
theorem State.finishGroupSuccess_noTermination (queue : State) (group : GroupNode)
    : Execution.WorkQueueEvent.workQueueTermination
      ∉ (queue.finishGroupSuccess group).2.1 := by
  obtain ⟨selected, _, _, events, _, _⟩ := queue.finishGroupSuccess_publications group
  rw [events]
  split <;> simp

/-- Recursive release emits only group values and closures.
Witness: induction on its budget, combining each closure with the remaining drain.
-/
theorem State.drainReadyGroups_noTermination (queue : State)
    : Execution.WorkQueueEvent.workQueueTermination ∉ queue.drainReadyGroups.2 := by
  have loop (fuel : Nat) (current : State)
      : Execution.WorkQueueEvent.workQueueTermination ∉ (State.drainReadyGroups.go fuel current).2 := by
    induction fuel generalizing current with
    | zero => simp [State.drainReadyGroups.go]
    | succ fuel ih =>
        unfold State.drainReadyGroups.go
        dsimp only
        split
        · simp
        · rename_i node selected
          cases cached : node.failure with
          | none =>
              simpa only [List.mem_append, not_or]
                using And.intro (current.finishGroupSuccess_noTermination node) (ih _)
          | some errors =>
              simpa [State.finishGroupFailure]
                using ih (current.removeGroup node.group.node.ref)
  exact loop _ queue

/-- Successful task settlement cannot emit a terminal marker during owner release.
Witness: each flush and the final drain exclude termination; ignored tasks emit nothing.
-/
theorem State.taskSuccess_noTermination (queue : State) (occurrence : Occurrence)
    (result : TaskResult)
    : Execution.WorkQueueEvent.workQueueTermination
      ∉ (queue.taskSuccess occurrence result).2 := by
  have loop (groups : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent × NewWork)
      (prior : Execution.WorkQueueEvent.workQueueTermination ∉ acc.2.1)
      : Execution.WorkQueueEvent.workQueueTermination ∉ (groups.foldl successGroupStep acc).2.1 := by
    induction groups generalizing acc with
    | nil => exact prior
    | cons group rest ih =>
        apply ih
        obtain ⟨current, events, released⟩ := acc
        dsimp only [successGroupStep]
        split
        · exact prior
        · split
          · simpa only [List.mem_append, not_or]
              using And.intro prior (State.finishGroupSuccess_noTermination _ _)
          · exact prior
  cases found : queue.taskNode? occurrence with
  | none => simp [State.taskSuccess, found]
  | some node =>
      rw [queue.taskSuccess_eq occurrence result node found]
      split
      · simp
      · simpa only [List.mem_append, not_or]
          using And.intro (loop _ (_, [], {}) (by simp))
            (State.drainReadyGroups_noTermination _)

/-- Failure settlement emits group failure notices only, not queue termination.
Witness: induction through announced closures and latent error-cache updates.
-/
theorem State.taskFailure_noTermination (queue : State) (occurrence : Occurrence)
    (errors : Nat)
    : Execution.WorkQueueEvent.workQueueTermination
      ∉ (queue.taskFailure occurrence errors).2 := by
  let step (acc : State × List WorkQueueEvent) (group : Execution.DeliveryNode) :=
    match acc.1.groupNode? group.ref with
    | none => acc
    | some node =>
        if acc.1.rootGroups.contains group.ref then
          let (next, failure) := acc.1.finishGroupFailure node errors
          (next, acc.2 ++ [failure])
        else (acc.1.putGroupNode
          { node with pending := node.pending - 1
                      failure := some (node.failure.getD 0 + errors) }, acc.2)
  have loop (groups : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent)
      (prior : Execution.WorkQueueEvent.workQueueTermination ∉ acc.2)
      : Execution.WorkQueueEvent.workQueueTermination ∉ (groups.foldl step acc).2 := by
    induction groups generalizing acc with
    | nil => exact prior
    | cons group rest ih =>
        apply ih
        unfold step
        split
        · exact prior
        · split
          · simpa [State.finishGroupFailure] using prior
          · exact prior
  unfold State.taskFailure
  split
  · simp
  · split
    · simp
    · exact loop _ (_, []) (by simp)

/-- No source-handler output contains queue termination, regardless of event validity.
Witness: task proofs, a stream-value carrier followed by group draining, and stream
closures.
-/
theorem State.handleGraphEvent_noTermination (queue : State) (event : GraphEvent)
    : Execution.WorkQueueEvent.workQueueTermination
      ∉ (queue.handleGraphEvent event).2 := by
  cases event with
  | taskSuccess occurrence result =>
      exact queue.taskSuccess_noTermination occurrence result
  | taskFailure occurrence errors =>
      exact queue.taskFailure_noTermination occurrence errors
  | streamItems stream items =>
      simp only [State.handleGraphEvent, State.streamItems]
      split
      · simp
      · simp only [List.mem_cons, reduceCtorEq, false_or]
        exact State.drainReadyGroups_noTermination _
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess]
      split <;> simp
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> simp

/-- Eventwise replay has no terminal marker until the batch wrapper runs.
Witness: concatenate the handler-level exclusions along the actual replay.
-/
theorem State.rawEventReplay_noTermination (queue : State) (events : List GraphEvent)
    : Execution.WorkQueueEvent.workQueueTermination
      ∉ (queue.rawEventReplay events).2 := by
  induction events generalizing queue with
  | nil => simp [State.rawEventReplay]
  | cons event rest ih =>
      rw [State.rawEventReplay_cons]
      simpa only [List.mem_append, not_or]
        using And.intro (queue.handleGraphEvent_noTermination event) (ih _)

/-- Publisher normalization contains termination exactly when its input does.
Witness: constructor inspection; owner remapping changes only value events.
-/
theorem IncrementalPublisher.handleWorkQueueEvent_termination_mem
    (publisher : IncrementalPublisher) (event : WorkQueueEvent)
    : Execution.WorkQueueEvent.workQueueTermination
        ∈ (publisher.handleWorkQueueEvent event).2
      ↔ event = .workQueueTermination := by
  cases event <;> simp [IncrementalPublisher.handleWorkQueueEvent]

/-- Whole-batch normalization preserves and reflects terminal-marker membership.
Witness: the eventwise normalization equation and the single-event equivalence.
-/
theorem IncrementalPublisher.normalizeBatch_termination_mem
    (publisher : IncrementalPublisher) (events : List WorkQueueEvent)
    : Execution.WorkQueueEvent.workQueueTermination ∈ (publisher.normalizeBatch events).2
      ↔ Execution.WorkQueueEvent.workQueueTermination ∈ events := by
  induction events generalizing publisher with
  | nil => simp [IncrementalPublisher.normalizeBatch]
  | cons event rest ih =>
      rw [IncrementalPublisher.normalizeBatch_cons]
      simp only [List.mem_append, IncrementalPublisher.handleWorkQueueEvent_termination_mem,
        ih, List.mem_cons, eq_comm]

/-- Splitting value payloads into atoms preserves and reflects termination.
Witness: value atoms cannot be terminal, while each control constructor is unchanged.
-/
theorem publicationAtoms_termination_mem (event : Execution.WorkQueueEvent)
    : Execution.WorkQueueEvent.workQueueTermination ∈ publicationAtoms event
      ↔ event = .workQueueTermination := by
  cases event with
  | streamValues stream values groups streams =>
      have absent : Execution.WorkQueueEvent.workQueueTermination ∉
          streamPublicationAtoms stream groups streams values := by
        induction values using streamPublicationAtoms.induct with
        | case1 => simp [streamPublicationAtoms]
        | case2 => simp [streamPublicationAtoms]
        | case3 value next rest ih => simpa [streamPublicationAtoms] using ih
      simpa only [publicationAtoms, reduceCtorEq, iff_false] using absent
  | _ => simp [publicationAtoms]

/-- Atom expansion of a complete event list introduces no new terminal marker.
Witness: list membership in the flat map and the single-event equivalence.
-/
theorem publicationAtoms_list_termination_mem (events : List Execution.WorkQueueEvent)
    : Execution.WorkQueueEvent.workQueueTermination ∈ events.flatMap publicationAtoms
      ↔ Execution.WorkQueueEvent.workQueueTermination ∈ events := by
  simp only [List.mem_flatMap, publicationAtoms_termination_mem]
  simp

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
