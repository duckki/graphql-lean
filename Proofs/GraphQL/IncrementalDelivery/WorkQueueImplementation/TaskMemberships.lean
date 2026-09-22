import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PendingPreservation

/-! Unique task membership across graph-event handling. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (
  ExecutionGroupValue StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Flushing a task filters group membership lists, so it preserves their
duplicate-free property.
-/
theorem State.TaskMembershipsUnique.removeTask {queue : State}
    (unique : queue.TaskMembershipsUnique) (occurrence : Occurrence)
    : (queue.removeTask occurrence).TaskMembershipsUnique := by
  intro node member
  change node ∈ queue.groupNodes.map
    (fun prior => { prior with tasks := prior.tasks.filter (· != occurrence) })
    at member
  obtain ⟨prior, priorMember, same⟩ := List.mem_map.mp member
  subst node
  exact (unique prior priorMember).filter _

/-- Cancelling a failed group retains a filtered subset of group nodes and
does not alter the retained task membership lists.
-/
theorem State.TaskMembershipsUnique.removeGroup {queue : State}
    (unique : queue.TaskMembershipsUnique) (key : Nat)
    : (queue.removeGroup key).TaskMembershipsUnique := by
  intro node member
  exact unique node (List.mem_filter.mp member).1

/-- Failing a group uses only the group-removal path. -/
theorem State.TaskMembershipsUnique.finishGroupFailure {queue : State}
    (unique : queue.TaskMembershipsUnique) (group : GroupNode) (errors : Nat)
    : (queue.finishGroupFailure group errors).1.TaskMembershipsUnique := by
  exact unique.removeGroup group.group.node.key

/-- Successful group flushing only removes task memberships and group shells.
The fold witness handles shared tasks removed from all their co-owners.
-/
theorem State.TaskMembershipsUnique.finishGroupSuccess {queue : State}
    (unique : queue.TaskMembershipsUnique) (group : GroupNode)
    : (queue.finishGroupSuccess group).1.TaskMembershipsUnique := by
  let step (acc : State × List ExecutionGroupValue × Keys)
      (occurrence : Occurrence) : State × List ExecutionGroupValue × Keys :=
    let (current, values, streams) := acc
    match current.taskNode? occurrence with
    | none => (current, values, streams)
    | some taskNode =>
        let values :=
          match taskNode.value with
          | none => values
          | some value => values ++ [value]
        (current.removeTask occurrence, values, streams ++ taskNode.childStreams)
  have stepUnique (acc : State × List ExecutionGroupValue × Keys)
      (occurrence : Occurrence) (currentUnique : acc.1.TaskMembershipsUnique)
      : (step acc occurrence).1.TaskMembershipsUnique := by
    obtain ⟨current, values, streams⟩ := acc
    dsimp only [step]
    split
    · exact currentUnique
    · exact currentUnique.removeTask occurrence
  have foldUnique (tasks : List Occurrence) :
      ∀ acc : State × List ExecutionGroupValue × Keys,
        acc.1.TaskMembershipsUnique → (tasks.foldl step acc).1.TaskMembershipsUnique := by
    induction tasks with
    | nil => intro acc currentUnique; exact currentUnique
    | cons occurrence rest ih =>
        intro acc currentUnique
        exact ih (step acc occurrence) (stepUnique acc occurrence currentUnique)
  let flushed := (group.tasks.foldl step (queue, [], [])).1
  have flushedUnique : flushed.TaskMembershipsUnique :=
    foldUnique group.tasks (queue, [], []) unique
  let current : State :=
    { flushed with
        groupNodes := flushed.groupNodes.filter
          (fun node => node.group.node.key != group.group.node.key)
        rootGroups := flushed.rootGroups.filter (· != group.group.node.key) }
  have currentUnique : current.TaskMembershipsUnique := by
    intro node member
    exact flushedUnique node (List.mem_filter.mp member).1
  let children := group.childGroups.filterMap
    (fun key => (current.groupNode? key).map (fun node => node.group.node))
  change (current.pruneEmptyGroups children).1.TaskMembershipsUnique
  exact currentUnique.pruneEmptyGroups children

/-- Draining ready roots preserves duplicate-free task memberships through
each success flush, failure removal, and child activation.
-/
theorem State.TaskMembershipsUnique.drainReadyGroups {queue : State}
    (unique : queue.TaskMembershipsUnique)
    : queue.drainReadyGroups.1.TaskMembershipsUnique := by
  apply State.drainReadyGroups_preserves State.TaskMembershipsUnique
    (valid := unique)
  · intro current node currentUnique _ _ _ _
    exact (currentUnique.finishGroupSuccess node).startNewWork _
  · intro current node errors currentUnique _ _ _
    exact currentUnique.finishGroupFailure node errors

/-- Closing a stream changes only its started-root registry. -/
theorem State.TaskMembershipsUnique.streamSuccess {queue : State}
    (unique : queue.TaskMembershipsUnique) (stream : Execution.DeliveryNode)
    : (queue.streamSuccess stream).1.TaskMembershipsUnique := by
  unfold State.streamSuccess
  split <;> exact unique

/-- Failing a stream likewise changes only its started-root registry. -/
theorem State.TaskMembershipsUnique.streamFailure {queue : State}
    (unique : queue.TaskMembershipsUnique) (stream : Execution.DeliveryNode)
    (errors : Nat)
    : (queue.streamFailure stream errors).1.TaskMembershipsUnique := by
  unfold State.streamFailure
  split <;> exact unique

/-- Successful stream-item integration preserves duplicate-free group tasks. -/
theorem State.TaskMembershipsUnique.streamItems {queue : State}
    (unique : queue.TaskMembershipsUnique) (stream : Execution.DeliveryNode)
    (items : List StreamItem)
    : (queue.streamItems stream items).1.TaskMembershipsUnique := by
  let step (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue)
      (item : StreamItem) :=
    let (current, groups, streams, values) := acc
    let (integrated, newWork) := current.maybeIntegrateWork item.work
    let (pruned, nonempty) := integrated.pruneEmptyGroups newWork.newGroups
    (
      pruned.startNewWork { newWork with newGroups := nonempty },
      groups ++ nonempty,
      streams ++ newWork.newStreams,
      values ++ [item.value]
    )
  have stepUnique (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue)
      (item : StreamItem) (currentUnique : acc.1.TaskMembershipsUnique)
      : (step acc item).1.TaskMembershipsUnique := by
    obtain ⟨current, groups, streams, values⟩ := acc
    exact ((currentUnique.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _
  have foldUnique (more : List StreamItem) :
      ∀ acc : State × List Execution.DeliveryNode
        × List Execution.DeliveryNode × List StreamItemValue,
        acc.1.TaskMembershipsUnique → (more.foldl step acc).1.TaskMembershipsUnique := by
    induction more with
    | nil => intro acc currentUnique; exact currentUnique
    | cons item rest ih =>
        intro acc currentUnique
        exact ih (step acc item) (stepUnique acc item currentUnique)
  dsimp only [State.streamItems]
  split
  · exact unique
  · exact (foldUnique items (queue, [], [], []) unique).drainReadyGroups

/-- Task failure removes the failed task's memberships, closes announced owners,
and retains latent owners without introducing duplicate memberships.
-/
theorem State.TaskMembershipsUnique.taskFailure {queue : State}
    (unique : queue.TaskMembershipsUnique) (occurrence : Occurrence) (errors : Nat)
    : (queue.taskFailure occurrence errors).1.TaskMembershipsUnique := by
  let step (acc : State × List WorkQueueEvent)
      (group : Execution.DeliveryNode) : State × List WorkQueueEvent :=
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
  have stepUnique (acc : State × List WorkQueueEvent)
      (group : Execution.DeliveryNode)
      (currentUnique : acc.1.TaskMembershipsUnique)
      : (step acc group).1.TaskMembershipsUnique := by
    obtain ⟨current, events⟩ := acc
    change (match current.groupNode? group.key with
      | none => (current, events)
      | some node =>
          if current.rootGroups.contains group.key then
            let (next, failure) := current.finishGroupFailure node errors
            (next, events ++ [failure])
          else
            (current.putGroupNode
              { node with
                  pending := node.pending - 1
                  failure := some (node.failure.getD 0 + errors) }, events)).1.TaskMembershipsUnique
    cases found : current.groupNode? group.key with
    | none => exact currentUnique
    | some node =>
        by_cases started : current.rootGroups.contains group.key = true
        · simp only [started, ite_true]
          exact currentUnique.finishGroupFailure node errors
        · simp only [started]
          apply currentUnique.putGroupNode
          exact currentUnique node (List.mem_of_find?_eq_some found)
  have foldUnique (groups : List Execution.DeliveryNode) :
      ∀ acc : State × List WorkQueueEvent,
        acc.1.TaskMembershipsUnique → (groups.foldl step acc).1.TaskMembershipsUnique := by
    induction groups with
    | nil => intro acc currentUnique; exact currentUnique
    | cons group rest ih =>
        intro acc currentUnique
        exact ih (step acc group) (stepUnique acc group currentUnique)
  unfold State.taskFailure
  split
  · exact unique
  · rename_i taskNode found
    split <;> try exact unique.removeTask occurrence
    let current := queue.removeTask occurrence
    have currentUnique : current.TaskMembershipsUnique := unique.removeTask occurrence
    change (taskNode.task.groups.foldl step (current, [])).1.TaskMembershipsUnique
    exact foldUnique taskNode.task.groups (current, []) currentUnique

/-- Successful task handling changes task values, integrates child work,
decrements pending counters, flushes completed groups, and starts new roots.
Each stage preserves duplicate-free group membership lists.
-/
theorem State.TaskMembershipsUnique.taskSuccess {queue : State}
    (unique : queue.TaskMembershipsUnique) (occurrence : Occurrence)
    (result : TaskResult)
    : (queue.taskSuccess occurrence result).1.TaskMembershipsUnique := by
  let settleStep (current : State) (group : Execution.DeliveryNode) : State :=
    match current.groupNode? group.key with
    | none => current
    | some node => current.putGroupNode { node with pending := node.pending - 1 }
  have settleUnique (current : State) (group : Execution.DeliveryNode)
      (currentUnique : current.TaskMembershipsUnique)
      : (settleStep current group).TaskMembershipsUnique := by
    unfold settleStep
    split
    · exact currentUnique
    · rename_i node found
      apply currentUnique.putGroupNode
      exact currentUnique node (List.mem_of_find?_eq_some found)
  let releaseStep (acc : State × List WorkQueueEvent × NewWork)
      (group : Execution.DeliveryNode) : State × List WorkQueueEvent × NewWork :=
    let (current, events, released) := acc
    match current.groupNode? group.key with
    | none => (current, events, released)
    | some node =>
        let node := { node with pending := node.pending - 1 }
        let current := current.putGroupNode node
        if current.rootGroups.contains group.key && node.pending == 0
            && node.failure.isNone then
          let (next, finished, newWork) := current.finishGroupSuccess node
          (
            next,
            events ++ finished,
            ⟨
              released.newGroups ++ newWork.newGroups,
              released.newStreams ++ newWork.newStreams
            ⟩
          )
        else
          (current, events, released)
  have releaseUnique (acc : State × List WorkQueueEvent × NewWork)
      (group : Execution.DeliveryNode) (currentUnique : acc.1.TaskMembershipsUnique)
      : (releaseStep acc group).1.TaskMembershipsUnique := by
    obtain ⟨current, events, released⟩ := acc
    dsimp only [releaseStep]
    split
    · exact currentUnique
    · rename_i node found
      have decremented : (current.putGroupNode
          { node with pending := node.pending - 1 }).TaskMembershipsUnique := by
        simpa only [settleStep, found] using settleUnique current group currentUnique
      split
      · exact decremented.finishGroupSuccess _
      · exact decremented
  have releaseFold (groups : List Execution.DeliveryNode) :
      ∀ acc : State × List WorkQueueEvent × NewWork,
        acc.1.TaskMembershipsUnique → (groups.foldl releaseStep acc).1.TaskMembershipsUnique := by
    induction groups with
    | nil => intro acc currentUnique; exact currentUnique
    | cons group rest ih =>
        intro acc currentUnique
        exact ih (releaseStep acc group) (releaseUnique acc group currentUnique)
  unfold State.taskSuccess
  split
  · exact unique
  · rename_i taskNode found
    split <;> try exact unique.removeTask occurrence
    let withValue := queue.putTaskNode { taskNode with value := some result.value }
    have withValueUnique : withValue.TaskMembershipsUnique := unique
    let integrated := (withValue.maybeIntegrateWork result.work (some occurrence)).1
    have integratedUnique : integrated.TaskMembershipsUnique :=
      withValueUnique.maybeIntegrateWork result.work (some occurrence)
    let finished := taskNode.task.groups.foldl releaseStep (integrated, [], {})
    have finishedUnique : finished.1.TaskMembershipsUnique :=
      releaseFold taskNode.task.groups (integrated, [], {}) integratedUnique
    change (finished.1.startNewWork finished.2.2).drainReadyGroups.1.TaskMembershipsUnique
    exact (finishedUnique.startNewWork finished.2.2).drainReadyGroups

/-- Every single host graph event preserves duplicate-free live group tasks. -/
theorem State.TaskMembershipsUnique.handleGraphEvent {queue : State}
    (unique : queue.TaskMembershipsUnique) (event : GraphEvent)
    : (queue.handleGraphEvent event).1.TaskMembershipsUnique := by
  cases event with
  | taskSuccess occurrence result => exact unique.taskSuccess occurrence result
  | taskFailure occurrence errors => exact unique.taskFailure occurrence errors
  | streamItems stream items => exact unique.streamItems stream items
  | streamSuccess stream => exact unique.streamSuccess stream
  | streamFailure stream errors => exact unique.streamFailure stream errors

/-- The entire available host batch preserves unique task memberships. -/
theorem State.TaskMembershipsUnique.handleGraphEvents {queue : State}
    (unique : queue.TaskMembershipsUnique) (batch : List GraphEvent)
    : (queue.handleGraphEvents batch).1.TaskMembershipsUnique := by
  let step (acc : State × List WorkQueueEvent) (event : GraphEvent) :=
    let (current, outputs) := acc
    let (next, produced) := current.handleGraphEvent event
    (next, outputs ++ produced)
  have foldUnique (events : List GraphEvent) :
      ∀ acc : State × List WorkQueueEvent,
        acc.1.TaskMembershipsUnique → (events.foldl step acc).1.TaskMembershipsUnique := by
    induction events with
    | nil => intro acc currentUnique; exact currentUnique
    | cons event rest ih =>
        intro acc currentUnique
        obtain ⟨current, outputs⟩ := acc
        have nextUnique : (step (current, outputs) event).1.TaskMembershipsUnique :=
          currentUnique.handleGraphEvent event
        exact ih (step (current, outputs) event) nextUnique
  unfold State.handleGraphEvents
  split
  · exact unique
  · cases outcome : batch.foldl step (queue, []) with
    | mk current outputs =>
        have currentUnique : current.TaskMembershipsUnique := by
          have folded := foldUnique batch (queue, []) unique
          rw [outcome] at folded
          exact folded
        dsimp only
        split <;> exact currentUnique

/-- Flushing a shared value removes its task node, preventing a second queue
publication of the same occurrence. Witness: the task-node filter in `removeTask`.
-/
theorem State.removeTask_node_absent (queue : State) (occurrence : Occurrence)
    : (queue.removeTask occurrence).taskNode? occurrence = none := by
  simp [State.removeTask, State.taskNode?]
  intro node member unequal
  cases equal : (node.task.occurrence == occurrence) <;> simp_all [bne]

/-- Flushing removes the task from every group's remaining-task list, including
unannounced co-owners. Witness: the group-node map in `removeTask`.
-/
theorem State.removeTask_group_absent (queue : State) (occurrence : Occurrence)
    {node : GroupNode} (member : node ∈ (queue.removeTask occurrence).groupNodes)
    : occurrence ∉ node.tasks := by
  change node ∈
    queue.groupNodes.map
      (fun prior => { prior with tasks := prior.tasks.filter (· != occurrence) }) at member
  obtain ⟨prior, _, same⟩ := List.mem_map.mp member
  subst node
  have reflexive : (occurrence == occurrence) = true := by
    cases occurrence with
    | executionGroup address =>
        change (address == address) = true
        exact BEq.rfl
    | item address index =>
        change ((address == address) && (index == index)) = true
        simp [BEq.rfl]
  simp [bne, reflexive]

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
