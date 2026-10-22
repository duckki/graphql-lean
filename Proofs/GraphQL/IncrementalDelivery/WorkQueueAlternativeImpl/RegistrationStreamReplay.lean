import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationRelease
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationReachability
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedHandlerFrames

/-! The actual per-item registration handler projects to the reference stream handler. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue
open GraphQL.IncrementalDelivery.Execution (StreamItemValue WorkQueueEvent)

-----------------------------------------------------------------------------------------
-- Exact item-fold projection keeps notices and payload order, omitting only host effects
-----------------------------------------------------------------------------------------

/-- Proof notation for the public streamItems accumulator, including its inline effects. -/
abbrev StreamRegistrationAcc :=
  State
  × List Execution.DeliveryNode
  × List Execution.DeliveryNode
  × List StreamItemValue
  × List CleanupTarget
  × List HostEffect
  × List ReferenceWorkQueue.GroupFailureEvent

/-- Proof-facing name for the actual public per-item operation, not a replacement handler. -/
def streamRegistrationStep (acc : StreamRegistrationAcc)
    (item : ReferenceWorkQueue.StreamItem)
    (available : List (WorkQueueSemantics.Occurrence × Nat) := [])
    : StreamRegistrationAcc :=
  let (current, groups, streams, values, targets, effects, failures) := acc
  let (integrated, newWork) := current.maybeIntegrateWork item.work
  let (queue, nonempty) := integrated.queue.pruneEmptyGroups newWork.newGroups
  let (started, nextTargets, queued) :=
    ({ integrated with queue }).startNewWork
      { newWork.newWork with newGroups := nonempty } newWork targets available
  (
    started,
    groups ++ nonempty,
    streams ++ newWork.newStreams,
    values ++ [item.value],
    nextTargets,
    effects
    ++ [.adopt item.occurrence]
    ++ (nextTargets.drop targets.length).flatMap CleanupTarget.effects,
    failures ++ queued
  )

/-- Keep the queue, ordered notices and payloads; host observations have no reference field. -/
def streamRegistrationProjection (acc : StreamRegistrationAcc)
    : ReferenceWorkQueue.State
      × List Execution.DeliveryNode
      × List Execution.DeliveryNode
      × List StreamItemValue
      × List ReferenceWorkQueue.GroupFailureEvent :=
  (acc.1.queue, acc.2.1, acc.2.2.1, acc.2.2.2.1, acc.2.2.2.2.2.2)

/-- One actual item step has exactly the reference queue, releases and item metadata.
Witness: scope completion and group-only pruning preserve notices, then actual delayed
starts recover shared item activation. Rejected cleanup is retained in the actual fold.
-/
theorem streamRegistrationStep_projection {work : Work} (acc : StreamRegistrationAcc)
    (present : acc.1.queue.RootGroupsPresent)
    (matching : acc.1.queue.RegisteredTasksMatch work)
    (item : ReferenceWorkQueue.StreamItem)
    (known : ∀ task ∈ item.work.tasks, ReferenceWorkQueue.TaskMatches work task)
    (running : acc.1.stopped = false)
    (startupFrames
      : let prepared := acc.1.queue.maybeIntegrateWork item.work
        let pruned := (prepared.1.pruneEmptyGroups prepared.2.newGroups).1
        ∃ parents, pruned.TaskOwnerFrame work ∧ pruned.RemovalForest parents)
    (available : List (WorkQueueSemantics.Occurrence × Nat) := [])
    (unavailable
      : ∀ task ∈ item.work.tasks, task.occurrence ∉ available.map Prod.fst := by
        intro task _ member; cases member)
    : streamRegistrationProjection (streamRegistrationStep acc item available)
      = ReferenceWorkQueue.streamItemStep (streamRegistrationProjection acc) item
          available := by
  obtain ⟨state, groups, streams, values, targets, effects, failures⟩ := acc
  let registered := state.maybeIntegrateWork item.work
  have complete := state.maybeIntegrateWork_complete item.work present
  dsimp only at complete
  have pruning := activateRegisteredTasks_pruneEmptyGroups registered.1.queue
    registered.2.newGroups registered.2.activeTasks
  have nonempty := congrArg (fun result : ReferenceWorkQueue.State × List Execution.DeliveryNode =>
    result.2) pruning
  dsimp only at nonempty
  rw [complete.1] at nonempty
  have sameGroups := congrArg ReferenceWorkQueue.NewWork.newGroups complete.2
  have sameStreams := congrArg ReferenceWorkQueue.NewWork.newStreams complete.2
  simp only [IntegratedWork.newWork] at sameGroups sameStreams
  obtain ⟨parents, frame, forest⟩ := startupFrames
  have sameQueue := congrArg Prod.fst pruning
  have registeredMatch := state.maybeIntegrateWork_registeredTasksMatch matching item.work known
  have prunedMatch := registeredMatch.pruneEmptyGroups registered.2.newGroups
  have members : registered.2.activeTasks.Subset
      (registered.1.queue.pruneEmptyGroups registered.2.newGroups).1.tasks := by
    intro task member
    rw [ReferenceWorkQueue.State.pruneEmptyGroups_tasks]
    rw [State.maybeIntegrateWork_tasks]
    exact List.mem_append_right _ (state.maybeIntegrateWork_activeTasks item.work none member)
  rw [activateRegisteredTasks_eq_startTasks prunedMatch _ members, complete.1] at sameQueue
  dsimp only at sameQueue
  have actualFrame : (registered.2.activeTasks.foldl
      (fun current task => current.startTask task.occurrence)
      (registered.1.queue.pruneEmptyGroups registered.2.newGroups).1).TaskOwnerFrame work := by
    rw [sameQueue, sameGroups]
    exact frame
  have actualForest : (registered.2.activeTasks.foldl
      (fun current task => current.startTask task.occurrence)
      (registered.1.queue.pruneEmptyGroups registered.2.newGroups).1).RemovalForest parents := by
    rw [sameQueue, sameGroups]
    exact forest
  have projects := State.integrateStreamItem_projects present matching item known targets running
    actualFrame actualForest available unavailable
  have whole := congrArg
    (fun pair : ReferenceWorkQueue.State × List ReferenceWorkQueue.GroupFailureEvent =>
      (pair.1, groups ++ (registered.1.queue.pruneEmptyGroups registered.2.newGroups).2,
        streams ++ registered.2.newStreams, values ++ [item.value], failures ++ pair.2)) projects
  refine whole.trans ?_
  dsimp only
  rw [nonempty]
  dsimp only [registered]
  rw [sameGroups, sameStreams]
  rfl

/-- One cache-aware item step retains the exposed queue and every reference carrier field.
Witness: exact scope/pruning metadata and cache-aware fused startup retain group/stream
notices, item order and the queued aggregate separately from inline host effects.
-/
theorem streamRegistrationStep_cacheProjection {work : Work} (acc : StreamRegistrationAcc)
    (present : acc.1.queue.RootGroupsPresent)
    (matching : acc.1.queue.RegisteredTasksMatch work)
    (unique : acc.1.queue.TaskNodeKeysUnique) (item : ReferenceWorkQueue.StreamItem)
    (known : ∀ task ∈ item.work.tasks, ReferenceWorkQueue.TaskMatches work task)
    (running : acc.1.stopped = false)
    (available : List (WorkQueueSemantics.Occurrence × Nat))
    (startupFrames
      : let prepared := acc.1.queue.maybeIntegrateWork item.work
        let pruned := prepared.1.pruneEmptyGroups prepared.2.newGroups
        ∃ parents, pruned.1.TaskOwnerFrame work ∧ pruned.1.RemovalForest parents)
    : let actual :=
        streamRegistrationProjection (streamRegistrationStep acc item available)
      let reference :=
        ReferenceWorkQueue.streamItemStep (streamRegistrationProjection acc)
          item available
      (actual.1.cacheTaskFailures available, actual.2)
      = (reference.1.cacheTaskFailures available, reference.2) := by
  obtain ⟨state, groups, streams, values, targets, effects, failures⟩ := acc
  let registered := state.maybeIntegrateWork item.work
  have complete := state.maybeIntegrateWork_complete item.work present
  dsimp only at complete
  have pruning := activateRegisteredTasks_pruneEmptyGroups registered.1.queue
    registered.2.newGroups registered.2.activeTasks
  have nonempty := congrArg (fun result : ReferenceWorkQueue.State × List Execution.DeliveryNode =>
    result.2) pruning
  dsimp only at nonempty
  rw [complete.1] at nonempty
  have sameGroups := congrArg ReferenceWorkQueue.NewWork.newGroups complete.2
  have sameStreams := congrArg ReferenceWorkQueue.NewWork.newStreams complete.2
  simp only [IntegratedWork.newWork] at sameGroups sameStreams
  have projects := State.integrateStreamItem_cache_projects present matching unique item known
    targets running available startupFrames
  have whole := congrArg
    (fun pair : ReferenceWorkQueue.State × List ReferenceWorkQueue.GroupFailureEvent =>
      (pair.1, groups ++ (registered.1.queue.pruneEmptyGroups registered.2.newGroups).2,
        streams ++ registered.2.newStreams, values ++ [item.value], failures ++ pair.2)) projects
  refine whole.trans ?_
  dsimp only
  rw [nonempty]
  dsimp only [registered]
  rw [sameGroups, sameStreams]
  rfl

/-- Each actual item step preserves the reader guard. -/
theorem streamRegistrationStep_stopped (acc : StreamRegistrationAcc)
    (item : ReferenceWorkQueue.StreamItem)
    (available : List (WorkQueueSemantics.Occurrence × Nat) := [])
    : (streamRegistrationStep acc item available).1.stopped = acc.1.stopped := by
  change (({ (acc.1.maybeIntegrateWork item.work).1 with
    queue := ((acc.1.maybeIntegrateWork item.work).1.queue.pruneEmptyGroups
      (acc.1.maybeIntegrateWork item.work).2.newGroups).1 }).startNewWork _ _ _ available).1.stopped
    = acc.1.stopped
  rw [State.startNewWork_stopped _ _ _ _ available, State.maybeIntegrateWork_stopped]

/-- Every FIFO preparation prefix keeps the same interruption guard. -/
theorem streamRegistrationFold_stopped (items : List ReferenceWorkQueue.StreamItem)
    (acc : StreamRegistrationAcc)
    (available : List (WorkQueueSemantics.Occurrence × Nat) := [])
    : (items.foldl (fun acc item => streamRegistrationStep acc item available)
        acc).1.stopped
      = acc.1.stopped := by
  induction items generalizing acc with
  | nil => rfl
  | cons item rest ih =>
      rw [List.foldl_cons, ih, streamRegistrationStep_stopped _ _ available]

/-- Reference item steps preserve any common metadata tail under the same cache exposure. -/
theorem reference_streamItemStep_acc_cache_congr
    (first second
      : ReferenceWorkQueue.State
        × List Execution.DeliveryNode
        × List Execution.DeliveryNode
        × List StreamItemValue
        × List ReferenceWorkQueue.GroupFailureEvent)
    (firstKeys : first.1.TaskNodeKeysUnique) (secondKeys : second.1.TaskNodeKeysUnique)
    (available : List (WorkQueueSemantics.Occurrence × Nat))
    (same
      : (first.1.cacheTaskFailures available, first.2)
        = (second.1.cacheTaskFailures available, second.2))
    (item : ReferenceWorkQueue.StreamItem)
    : let left := ReferenceWorkQueue.streamItemStep first item available
      let right := ReferenceWorkQueue.streamItemStep second item available
      (left.1.cacheTaskFailures available, left.2)
      = (right.1.cacheTaskFailures available, right.2) := by
  obtain ⟨left, tail⟩ := first
  obtain ⟨right, other⟩ := second
  have metadata := congrArg Prod.snd same
  change tail = other at metadata
  subst other
  obtain ⟨groups, streams, values, failures⟩ := tail
  exact reference_streamItemStep_cache_congr firstKeys secondKeys available
    (congrArg Prod.fst same) item groups streams values failures

/-- Local bookkeeping needed to project one actual item startup, before its cleanup.
These are proof certificates for the reference item prefix, not runtime inventories.
-/
structure StreamItemCacheFrame (queue : ReferenceWorkQueue.State) (work : Work)
    (item : ReferenceWorkQueue.StreamItem)
    : Prop where
  present : queue.RootGroupsPresent
  matching : queue.RegisteredTasksMatch work
  keys : queue.TaskNodeKeysUnique
  startup
    : let prepared := queue.maybeIntegrateWork item.work
      let pruned := prepared.1.pruneEmptyGroups prepared.2.newGroups
      ∃ parents, pruned.1.TaskOwnerFrame work ∧ pruned.1.RemovalForest parents

/-- Common cache exposure transfers all local item certificates.
Witness: registration and pruning preserve exposed queues and release descriptors;
roots, catalogue, ownership and removal topology do not depend on rejection slots.
-/
theorem StreamItemCacheFrame.of_cache_eq {first second : ReferenceWorkQueue.State}
    {work : Work} {item : ReferenceWorkQueue.StreamItem}
    (available : List (WorkQueueSemantics.Occurrence × Nat))
    (same : first.cacheTaskFailures available = second.cacheTaskFailures available)
    (frame : StreamItemCacheFrame second work item)
    : StreamItemCacheFrame first work item := by
  have keys : first.TaskNodeKeysUnique := by
    have exposed := frame.keys.cacheTaskFailures available
    rw [← same] at exposed
    simpa only [ReferenceWorkQueue.State.TaskNodeKeysUnique,
      ReferenceWorkQueue.State.cacheTaskFailures_taskOccurrences] using exposed
  have roots := congrArg ReferenceWorkQueue.State.rootGroups same
  have groups := congrArg ReferenceWorkQueue.State.groupNodes same
  have tasks := congrArg ReferenceWorkQueue.State.tasks same
  simp only [ReferenceWorkQueue.State.cacheTaskFailures_rootGroups] at roots
  simp only [ReferenceWorkQueue.State.cacheTaskFailures_groupNodes] at groups
  simp only [ReferenceWorkQueue.State.cacheTaskFailures_tasks] at tasks
  refine ⟨?_, ?_, keys, ?_⟩
  · change ∀ ref ∈ first.rootGroups,
      ref ∈ first.groupNodes.map (fun node => node.group.node.ref)
    rw [roots, groups]
    exact frame.present
  · change ∀ task ∈ first.tasks, ReferenceWorkQueue.TaskMatches work task
    rw [tasks]
    exact frame.matching
  · let left := first.maybeIntegrateWork item.work
    let right := second.maybeIntegrateWork item.work
    have registered := reference_maybeIntegrateWork_cache_congr keys frame.keys
      available same item.work
    have registeredQueue := congrArg Prod.fst registered
    have released := congrArg Prod.snd registered
    change left.2 = right.2 at released
    have pruned := reference_pruneEmptyGroups_cache_congr
      (keys.maybeIntegrateWork item.work) (frame.keys.maybeIntegrateWork item.work)
      available registeredQueue right.2.newGroups
    have prunedQueue := congrArg Prod.fst pruned
    obtain ⟨parents, owner, forest⟩ := frame.startup
    change ∃ parents, (left.1.pruneEmptyGroups left.2.newGroups).1.TaskOwnerFrame work
      ∧ (left.1.pruneEmptyGroups left.2.newGroups).1.RemovalForest parents
    rw [released]
    have prunedKeys := (keys.maybeIntegrateWork item.work).pruneEmptyGroups right.2.newGroups
    have actualOwner := ReferenceWorkQueue.State.TaskOwnerFrame.of_cacheTaskFailures_eq
      prunedKeys available prunedQueue owner
    have topology := congrArg ReferenceWorkQueue.State.groupNodes prunedQueue
    simp only [ReferenceWorkQueue.State.cacheTaskFailures_groupNodes] at topology
    exact ⟨parents, actualOwner, forest.of_subset (by rw [topology]; exact List.Subset.refl _)⟩

/-- The complete actual item fold preserves exposed queues and all reference metadata.
Witness: induction transfers concrete reference-prefix certificates across common exposure,
then composes the local delayed-start bridge with reference item-step congruence.
-/
theorem streamRegistrationFold_cacheProjection {work : Work}
    (initial : StreamRegistrationAcc) (items : List ReferenceWorkQueue.StreamItem)
    (running : initial.1.stopped = false)
    (known
      : ∀ item ∈ items,
        ∀ task ∈ item.work.tasks, ReferenceWorkQueue.TaskMatches work task)
    (available : List (WorkQueueSemantics.Occurrence × Nat))
    (frames
      : ∀ before item after,
          items = before ++ item :: after
          → StreamItemCacheFrame
              (before.foldl
                (fun acc item => ReferenceWorkQueue.streamItemStep acc item available)
                (streamRegistrationProjection initial)).1 work item)
    : let actual :=
        streamRegistrationProjection
          (items.foldl (fun acc item => streamRegistrationStep acc item available)
            initial)
      let reference :=
        items.foldl
          (fun acc item => ReferenceWorkQueue.streamItemStep acc item available)
          (streamRegistrationProjection initial)
      (actual.1.cacheTaskFailures available, actual.2)
      = (reference.1.cacheTaskFailures available, reference.2) := by
  let referenceStep := fun acc item => ReferenceWorkQueue.streamItemStep acc item available
  let initialReference := streamRegistrationProjection initial
  have loop (remaining before : List ReferenceWorkQueue.StreamItem)
      (partition : items = before ++ remaining) (acc : StreamRegistrationAcc)
      (same : let reference := before.foldl referenceStep initialReference
        let actual := streamRegistrationProjection acc
        (actual.1.cacheTaskFailures available, actual.2)
          = (reference.1.cacheTaskFailures available, reference.2))
      (active : acc.1.stopped = false)
      : let actual := streamRegistrationProjection
          (remaining.foldl (fun acc item => streamRegistrationStep acc item available) acc)
        let reference := remaining.foldl referenceStep
          (before.foldl referenceStep initialReference)
        (actual.1.cacheTaskFailures available, actual.2)
          = (reference.1.cacheTaskFailures available, reference.2) := by
    induction remaining generalizing before acc with
    | nil => exact same
    | cons item rest ih =>
        have referenceFrame := frames before item rest partition
        have actualFrame := referenceFrame.of_cache_eq available (congrArg Prod.fst same)
        have member : item ∈ items := by
          rw [partition]
          exact List.mem_append_right _ List.mem_cons_self
        have step := streamRegistrationStep_cacheProjection acc actualFrame.present
          actualFrame.matching actualFrame.keys item (known item member) active available
          actualFrame.startup
        have referenceStepEq := reference_streamItemStep_acc_cache_congr
          (streamRegistrationProjection acc) (before.foldl referenceStep initialReference)
          actualFrame.keys referenceFrame.keys available same item
        have nextPartition : items = (before ++ [item]) ++ rest := by
          simpa only [List.append_assoc, List.singleton_append] using partition
        have next := step.trans referenceStepEq
        have later :=
          ih (before ++ [item]) nextPartition (streamRegistrationStep acc item available)
            (by
              simpa only [List.foldl_append, List.foldl_cons, List.foldl_nil] using next)
            ((streamRegistrationStep_stopped acc item available).trans active)
        simpa only [List.foldl_cons, List.foldl_append, List.foldl_nil] using later
  exact loop items [] rfl initial rfl running

/-- An item fold has exact correspondence when fresh child tasks are outside the snapshot.
Witness: each delayed child start is its ordinary eager start; the concrete prefix frame
then licenses exact startup correspondence before the next item.
-/
theorem streamRegistrationFold_projection_of_unavailableChildren {work : Work}
    (initial : StreamRegistrationAcc) (items : List ReferenceWorkQueue.StreamItem)
    (running : initial.1.stopped = false)
    (known
      : ∀ item ∈ items,
        ∀ task ∈ item.work.tasks, ReferenceWorkQueue.TaskMatches work task)
    (available : List (WorkQueueSemantics.Occurrence × Nat))
    (unavailable
      : ∀ item ∈ items,
        ∀ task ∈ item.work.tasks, task.occurrence ∉ available.map Prod.fst)
    (frames
      : ∀ before item after,
          items = before ++ item :: after
          → StreamItemCacheFrame
              (before.foldl
                (fun acc item => ReferenceWorkQueue.streamItemStep acc item available)
                (streamRegistrationProjection initial)).1 work item)
    : streamRegistrationProjection
        (items.foldl (fun acc item => streamRegistrationStep acc item available) initial)
      = items.foldl (fun acc item => ReferenceWorkQueue.streamItemStep acc item available)
          (streamRegistrationProjection initial) := by
  let referenceStep := fun acc item => ReferenceWorkQueue.streamItemStep acc item available
  let initialReference := streamRegistrationProjection initial
  have loop (remaining before : List ReferenceWorkQueue.StreamItem)
      (partition : items = before ++ remaining) (acc : StreamRegistrationAcc)
      (same : streamRegistrationProjection acc = before.foldl referenceStep initialReference)
      (active : acc.1.stopped = false)
      : streamRegistrationProjection
          (remaining.foldl (fun acc item => streamRegistrationStep acc item available) acc)
        = remaining.foldl referenceStep (before.foldl referenceStep initialReference) := by
    induction remaining generalizing before acc with
    | nil => exact same
    | cons item rest ih =>
        have frame := frames before item rest partition
        have queueEq := congrArg Prod.fst same
        change acc.1.queue = (before.foldl referenceStep initialReference).1 at queueEq
        have member : item ∈ items := by
          rw [partition]
          exact List.mem_append_right _ List.mem_cons_self
        have present : acc.1.queue.RootGroupsPresent := by rw [queueEq]; exact frame.present
        have matching : acc.1.queue.RegisteredTasksMatch work := by
          rw [queueEq]; exact frame.matching
        have step := streamRegistrationStep_projection acc present matching item (known item member)
          active (by rw [queueEq]; exact frame.startup) available (unavailable item member)
        have nextPartition : items = (before ++ [item]) ++ rest := by
          simpa only [List.append_assoc, List.singleton_append] using partition
        have next : streamRegistrationProjection (streamRegistrationStep acc item available)
            = (before ++ [item]).foldl referenceStep initialReference := by
          rw [step, same, List.foldl_append, List.foldl_cons, List.foldl_nil]
        have later := ih (before ++ [item]) nextPartition
          (streamRegistrationStep acc item available)
          next ((streamRegistrationStep_stopped acc item available).trans active)
        simpa only [List.foldl_cons, List.foldl_append, List.foldl_nil] using later
  exact loop items [] rfl initial rfl running

/-- Stream receipt has exact correspondence when its fresh child tasks are unavailable.
Witness: exact item-fold registration is followed by the same mixed successful drain;
notices, item values and queued failures retain their separate ordered channels.
-/
theorem State.streamItems_projection_of_unavailableChildren {state : State} {work : Work}
    (stream : Execution.DeliveryNode) (items : List ReferenceWorkQueue.StreamItem)
    (known
      : ∀ item ∈ items,
        ∀ task ∈ item.work.tasks, ReferenceWorkQueue.TaskMatches work task)
    (running : state.stopped = false)
    (available : List (WorkQueueSemantics.Occurrence × Nat))
    (unavailable
      : ∀ item ∈ items,
        ∀ task ∈ item.work.tasks, task.occurrence ∉ available.map Prod.fst)
    (frames
      : ∀ before item after,
          items = before ++ item :: after
          → StreamItemCacheFrame (state.queue.preparedStreamItems before available) work
              item)
    (drainFrames
      : ∃ parents,
          (state.queue.preparedStreamItems items available).TaskOwnerFrame work
          ∧ (state.queue.preparedStreamItems items available).RemovalForest parents)
    : (
        (state.streamItems stream items available).1.queue,
        (state.streamItems stream items available).2.1,
        (state.streamItems stream items available).2.2.2
      )
      = state.queue.streamItems stream items available := by
  let initial : StreamRegistrationAcc := (state, [], [], [], [], [], [])
  let acc := items.foldl (fun acc item => streamRegistrationStep acc item available) initial
  let reference := items.foldl
    (fun acc item => ReferenceWorkQueue.streamItemStep acc item available)
    (state.queue, [], [], [], [])
  have fold := streamRegistrationFold_projection_of_unavailableChildren initial items running known
    available unavailable frames
  have queueEq : acc.1.queue = reference.1 := congrArg Prod.fst fold
  obtain ⟨parents, frame, forest⟩ := drainFrames
  have actualFrame : acc.1.queue.TaskOwnerFrame work := by rw [queueEq]; exact frame
  have actualForest : acc.1.queue.RemovalForest parents := by rw [queueEq]; exact forest
  have active : acc.1.stopped = false :=
    (streamRegistrationFold_stopped items initial available).trans running
  have drain := acc.1.drainReadyGroups_projection active actualFrame actualForest
    acc.2.2.2.2.1 available
  rw [queueEq] at drain
  have projection : state.streamItems stream items available =
      if !state.queue.rootStreams.contains stream.ref then
        (state, [], [.acknowledge stream.ref], [])
      else
        let drained := acc.1.drainReadyGroups acc.2.2.2.2.1 available
        (drained.1,
          .streamValues stream acc.2.2.2.1 acc.2.1 acc.2.2.1 :: drained.2.1,
          acc.2.2.2.2.2.1 ++ [.acknowledge stream.ref] ++
            (drained.2.2.1.drop acc.2.2.2.2.1.length).flatMap CleanupTarget.effects,
          acc.2.2.2.2.2.2 ++ drained.2.2.2) := rfl
  rw [projection, ReferenceWorkQueue.State.streamItems_eq state.queue stream items available]
  split
  · rfl
  · have combined := congrArg
      (fun value : ReferenceWorkQueue.State × List WorkQueueEvent
          × List ReferenceWorkQueue.GroupFailureEvent =>
        (value.1, .streamValues stream acc.2.2.2.1 acc.2.1 acc.2.2.1 :: value.2.1,
          acc.2.2.2.2.2.2 ++ value.2.2)) drain
    have metadata := congrArg Prod.snd fold
    have sameGroups := congrArg (fun value => value.1) metadata
    have sameStreams := congrArg (fun value => value.2.1) metadata
    have sameValues := congrArg (fun value => value.2.2.1) metadata
    have sameFailures := congrArg (fun value => value.2.2.2) metadata
    change acc.2.1 = reference.2.1 at sameGroups
    change acc.2.2.1 = reference.2.2.1 at sameStreams
    change acc.2.2.2.1 = reference.2.2.2.1 at sameValues
    change acc.2.2.2.2.2.2 = reference.2.2.2.2 at sameFailures
    exact combined.trans (by rw [sameGroups, sameStreams, sameValues, sameFailures])

/-- Stream receipt preserves the reference queue after exposure and both output channels.
Witness: the actual item fold preserves all carrier metadata, and ownership/forest
certificates transfer to its final queue before the cache-aware fused drain.
-/
theorem State.streamItems_cacheProjection {state : State} {work : Work}
    (unique : state.queue.TaskNodeKeysUnique)
    (stream : Execution.DeliveryNode) (items : List ReferenceWorkQueue.StreamItem)
    (known
      : ∀ item ∈ items,
        ∀ task ∈ item.work.tasks, ReferenceWorkQueue.TaskMatches work task)
    (running : state.stopped = false)
    (available : List (WorkQueueSemantics.Occurrence × Nat))
    (frames
      : ∀ before item after,
          items = before ++ item :: after
          → StreamItemCacheFrame (state.queue.preparedStreamItems before available) work
              item)
    (drainFrames
      : ∃ parents,
          (state.queue.preparedStreamItems items available).TaskOwnerFrame work
          ∧ (state.queue.preparedStreamItems items available).RemovalForest parents)
    : (
        (state.streamItems stream items available).1.queue.cacheTaskFailures available,
        (state.streamItems stream items available).2.1,
        (state.streamItems stream items available).2.2.2
      )
      = (
        (state.queue.streamItems stream items available).1.cacheTaskFailures available,
        (state.queue.streamItems stream items available).2
      ) := by
  let initial : StreamRegistrationAcc := (state, [], [], [], [], [], [])
  let acc := items.foldl (fun acc item => streamRegistrationStep acc item available) initial
  let reference := items.foldl
    (fun acc item => ReferenceWorkQueue.streamItemStep acc item available)
    (state.queue, [], [], [], [])
  have fold := streamRegistrationFold_cacheProjection initial items running known available frames
  have queueEq : acc.1.queue.cacheTaskFailures available
      = reference.1.cacheTaskFailures available := congrArg Prod.fst fold
  have referenceKeys : reference.1.TaskNodeKeysUnique := by
    apply ReferenceWorkQueue.State.preparedStreamItems_preserves
      (fun current => current.TaskNodeKeysUnique) unique items available
    intro current item _ prior
    let integrated := current.maybeIntegrateWork item.work
    let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
    exact ((prior.maybeIntegrateWork item.work).pruneEmptyGroups
      integrated.2.newGroups).startNewWork { integrated.2 with newGroups := pruned.2 } available
  have actualKeys : acc.1.queue.TaskNodeKeysUnique := by
    have exposed := referenceKeys.cacheTaskFailures available
    rw [← queueEq] at exposed
    simpa only [ReferenceWorkQueue.State.TaskNodeKeysUnique,
      ReferenceWorkQueue.State.cacheTaskFailures_taskOccurrences] using exposed
  obtain ⟨parents, frame, forest⟩ := drainFrames
  have actualFrame := ReferenceWorkQueue.State.TaskOwnerFrame.of_cacheTaskFailures_eq
    actualKeys available queueEq frame
  have topology := congrArg ReferenceWorkQueue.State.groupNodes queueEq
  simp only [ReferenceWorkQueue.State.cacheTaskFailures_groupNodes] at topology
  have actualForest := forest.of_subset (by rw [topology]; exact List.Subset.refl _)
  have active : acc.1.stopped = false :=
    (streamRegistrationFold_stopped items initial available).trans running
  have drain := acc.1.drainReadyGroups_projects_after_cache active actualFrame actualForest
    acc.2.2.2.2.1 available actualKeys reference.1 referenceKeys queueEq
  have projection : state.streamItems stream items available =
      if !state.queue.rootStreams.contains stream.ref then
        (state, [], [.acknowledge stream.ref], [])
      else
        let drained := acc.1.drainReadyGroups acc.2.2.2.2.1 available
        (drained.1,
          .streamValues stream acc.2.2.2.1 acc.2.1 acc.2.2.1 :: drained.2.1,
          acc.2.2.2.2.2.1 ++ [.acknowledge stream.ref] ++
            (drained.2.2.1.drop acc.2.2.2.2.1.length).flatMap CleanupTarget.effects,
          acc.2.2.2.2.2.2 ++ drained.2.2.2) := rfl
  rw [projection, ReferenceWorkQueue.State.streamItems_eq state.queue stream items available]
  split
  · rfl
  · have combined := congrArg
      (fun value : ReferenceWorkQueue.State × List WorkQueueEvent
          × List ReferenceWorkQueue.GroupFailureEvent =>
        (value.1, .streamValues stream acc.2.2.2.1 acc.2.1 acc.2.2.1 :: value.2.1,
          acc.2.2.2.2.2.2 ++ value.2.2)) drain
    have metadata := congrArg Prod.snd fold
    have sameGroups := congrArg (fun value => value.1) metadata
    have sameStreams := congrArg (fun value => value.2.1) metadata
    have sameValues := congrArg (fun value => value.2.2.1) metadata
    have sameFailures := congrArg (fun value => value.2.2.2) metadata
    change acc.2.1 = reference.2.1 at sameGroups
    change acc.2.2.1 = reference.2.2.1 at sameStreams
    change acc.2.2.2.1 = reference.2.2.2.1 at sameValues
    change acc.2.2.2.2.2.2 = reference.2.2.2.2 at sameFailures
    exact combined.trans (by rw [sameGroups, sameStreams, sameValues, sameFailures])

-----------------------------------------------------------------------------------------
-- Required phase invariants are derived from generated reference prefixes
-----------------------------------------------------------------------------------------

private theorem matchedItem_tasks {work : Work} {stream items}
    (matched : (ReferenceWorkQueue.GraphEvent.streamItems stream items).MatchesWork work)
    {item : ReferenceWorkQueue.StreamItem} (member : item ∈ items)
    : ∀ task ∈ item.work.tasks, ReferenceWorkQueue.TaskMatches work task := by
  intro task taskMember
  obtain ⟨address, payload, same, known⟩ :=
    matched.streamItem_childTask_producer member taskMember
  exact ⟨⟨address, payload, some item.occurrence, same, known⟩,
    matched.streamItem_childTask_groupsExact member taskMember⟩

private theorem preparedItems_registeredTasksMatch {queue : ReferenceWorkQueue.State}
    {work : Work} (matching : queue.RegisteredTasksMatch work)
    (items : List ReferenceWorkQueue.StreamItem)
    (known
      : ∀ item ∈ items,
        ∀ task ∈ item.work.tasks, ReferenceWorkQueue.TaskMatches work task)
    : (queue.preparedStreamItems items).RegisteredTasksMatch work := by
  apply ReferenceWorkQueue.State.preparedStreamItems_preserves
    (fun current => current.RegisteredTasksMatch work) matching items []
  intro current item member prior
  let integrated := current.maybeIntegrateWork item.work
  have registration := prior.maybeIntegrateWork item.work (known item member)
  have pruned := registration.pruneEmptyGroups integrated.2.newGroups
  exact pruned.startNewWork { integrated.2 with
    newGroups := (integrated.1.pruneEmptyGroups integrated.2.newGroups).2 }

/-- Every item prefix of a matching generated receipt supplies the phase invariants.
Witness: reuse the reference's actual pre-drain live-root frame and catalogue preservation.
No new host premise is needed, even for empty prefixes or ignored source receipts.
-/
theorem referencePrefix_preparedItems_invariants {work : Work}
    (generated : ReferenceWorkQueue.ExecutedWork work) (events : List GraphEvent)
    (matching : ∀ event ∈ events, event.MatchesWork work)
    (stream : Execution.DeliveryNode) (items : List ReferenceWorkQueue.StreamItem)
    (matched : (ReferenceWorkQueue.GraphEvent.streamItems stream items).MatchesWork work)
    (earlier : List ReferenceWorkQueue.StreamItem) (included : earlier.Subset items)
    : let queue :=
        (ReferenceWorkQueue.State.initialize
          (ReferenceWorkQueue.Work.fromExecution work)).replayGraphEvents
          events
      (queue.preparedStreamItems earlier).RootGroupsPresent
      ∧ (queue.preparedStreamItems earlier).RegisteredTasksMatch work := by
  have prefixMatch : (ReferenceWorkQueue.GraphEvent.streamItems stream earlier).MatchesWork work :=
    fun item member => matched item (included member)
  obtain ⟨parents, canonical, frame⟩ := generated.streamItems_prepared_liveRootFrame matching
    prefixMatch (generated.replayGraphEvents_rootsPresent events matching)
  exact ⟨frame.present, preparedItems_registeredTasksMatch
    (referencePrefix_registeredTasksMatch events matching) earlier
    (fun item member => matchedItem_tasks matched (included member))⟩

-----------------------------------------------------------------------------------------
-- Complete actual receipt projection and the shared ready drain
-----------------------------------------------------------------------------------------

/-- The complete actual item fold has exactly the reference queue, notices and values.
Witness: at each prefix derive live roots/provenance from generated reference preparation,
then apply the local step bridge. The actual adoption/disposal accumulator is not replaced.
-/
theorem referencePrefix_streamRegistrationFold {work : Work}
    (generated : ReferenceWorkQueue.ExecutedWork work) (events : List GraphEvent)
    (matching : ∀ event ∈ events, event.MatchesWork work)
    (valid : ReferenceWorkQueue.ValidGraphEvents work events)
    (accepted
      : ReferenceWorkQueue.State.eventsStarted []
          (ReferenceWorkQueue.State.initialize
            (ReferenceWorkQueue.Work.fromExecution work))
          events
        = true)
    (stream : Execution.DeliveryNode) (items : List ReferenceWorkQueue.StreamItem)
    (matched : (ReferenceWorkQueue.GraphEvent.streamItems stream items).MatchesWork work)
    : let queue :=
        (ReferenceWorkQueue.State.initialize
          (ReferenceWorkQueue.Work.fromExecution work)).replayGraphEvents
          events
      streamRegistrationProjection
        (items.foldl streamRegistrationStep ({ queue }, [], [], [], [], [], []))
      = items.foldl ReferenceWorkQueue.streamItemStep (queue, [], [], [], []) := by
  let queue := (ReferenceWorkQueue.State.initialize
    (ReferenceWorkQueue.Work.fromExecution work)).replayGraphEvents events
  let initial : ReferenceWorkQueue.State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue
      × List ReferenceWorkQueue.GroupFailureEvent := (queue, [], [], [], [])
  have loop (remaining : List ReferenceWorkQueue.StreamItem)
      (earlier : List ReferenceWorkQueue.StreamItem) (partition : items = earlier ++ remaining)
      (acc : StreamRegistrationAcc)
      (same
        : streamRegistrationProjection acc
          = earlier.foldl ReferenceWorkQueue.streamItemStep initial)
      (running : acc.1.stopped = false)
      : streamRegistrationProjection (remaining.foldl streamRegistrationStep acc)
        = remaining.foldl ReferenceWorkQueue.streamItemStep
            (earlier.foldl ReferenceWorkQueue.streamItemStep initial) := by
    induction remaining generalizing earlier acc with
    | nil => exact same
    | cons item rest ih =>
        have included : earlier.Subset items := by
          intro earlier member
          rw [partition]
          exact List.mem_append_left _ member
        obtain ⟨present, registered⟩ := referencePrefix_preparedItems_invariants generated events
          matching stream items matched earlier included
        have queueEq : acc.1.queue = queue.preparedStreamItems earlier := congrArg Prod.fst same
        have member : item ∈ items := by
          rw [partition]
          exact List.mem_append_right _ List.mem_cons_self
        have step := streamRegistrationStep_projection acc (queueEq ▸ present)
          (queueEq ▸ registered) item (matchedItem_tasks matched member) running (by
            rw [queueEq]
            exact referencePrefix_streamItem_startFrames generated events valid accepted
              stream items matched earlier included item member)
        have nextPartition : items = (earlier ++ [item]) ++ rest := by
          simpa only [List.append_assoc, List.singleton_append] using partition
        have next : streamRegistrationProjection (streamRegistrationStep acc item)
            = (earlier ++ [item]).foldl ReferenceWorkQueue.streamItemStep initial := by
          rw [step, same, List.foldl_append, List.foldl_cons, List.foldl_nil]
        have later := ih (earlier ++ [item]) nextPartition (streamRegistrationStep acc item)
          next ((streamRegistrationStep_stopped acc item).trans running)
        simpa only [List.foldl_cons, List.foldl_append, List.foldl_nil] using later
  exact loop items [] rfl ({ queue }, [], [], [], [], [], []) rfl rfl

/-- The generated live stream handler has exactly the reference kernel and wire events.
Witness: project its actual item fold, derive the prepared owner/forest frame and apply
the actual mixed-drain projection.
This proves no equality with the old host-effect ordering.
-/
theorem referencePrefix_streamItems {work : Work}
    (generated : ReferenceWorkQueue.ExecutedWork work) (events : List GraphEvent)
    (matching : ∀ event ∈ events, event.MatchesWork work)
    (valid : ReferenceWorkQueue.ValidGraphEvents work events)
    (accepted
      : ReferenceWorkQueue.State.eventsStarted []
          (ReferenceWorkQueue.State.initialize
            (ReferenceWorkQueue.Work.fromExecution work)) events
        = true)
    (stream : Execution.DeliveryNode) (items : List ReferenceWorkQueue.StreamItem)
    (matched : (ReferenceWorkQueue.GraphEvent.streamItems stream items).MatchesWork work)
    : let queue :=
        (ReferenceWorkQueue.State.initialize
          (ReferenceWorkQueue.Work.fromExecution work)).replayGraphEvents
          events
      let alternative := ({ queue } : State).streamItems stream items
      (alternative.1.queue, alternative.2.1, alternative.2.2.2)
      = queue.streamItems stream items := by
  let queue := (ReferenceWorkQueue.State.initialize
    (ReferenceWorkQueue.Work.fromExecution work)).replayGraphEvents events
  change ((({ queue } : State).streamItems stream items).1.queue,
    (({ queue } : State).streamItems stream items).2.1,
    (({ queue } : State).streamItems stream items).2.2.2) = queue.streamItems stream items
  have fold := referencePrefix_streamRegistrationFold generated events matching valid accepted
    stream items matched
  dsimp only at fold
  have projection
      : ({ queue } : State).streamItems stream items =
        if !queue.rootStreams.contains stream.ref then
          ({ queue }, [], [.acknowledge stream.ref], [])
        else
          let acc := items.foldl streamRegistrationStep ({ queue }, [], [], [], [], [], [])
          let drained := acc.1.drainReadyGroups acc.2.2.2.2.1
          (drained.1,
            .streamValues stream acc.2.2.2.1 acc.2.1 acc.2.2.1 :: drained.2.1,
            acc.2.2.2.2.2.1 ++ [.acknowledge stream.ref] ++
              (drained.2.2.1.drop acc.2.2.2.2.1.length).flatMap CleanupTarget.effects,
            acc.2.2.2.2.2.2 ++ drained.2.2.2) := rfl
  rw [projection, ReferenceWorkQueue.State.streamItems_eq]
  split
  · rfl
  · let acc := items.foldl streamRegistrationStep ({ queue }, [], [], [], [], [], [])
    have queueEq : acc.1.queue = queue.preparedStreamItems items := congrArg Prod.fst fold
    obtain ⟨parents, frame, forest⟩ := referencePrefix_streamItems_drainFrames
      generated events valid accepted stream items matched
    have actualFrame : acc.1.queue.TaskOwnerFrame work := by rw [queueEq]; exact frame
    have actualForest : acc.1.queue.RemovalForest parents := by rw [queueEq]; exact forest
    have running : acc.1.stopped = false := by
      have loop (more : List ReferenceWorkQueue.StreamItem)
          (initial : StreamRegistrationAcc)
          : (more.foldl streamRegistrationStep initial).1.stopped
            = initial.1.stopped := by
        induction more generalizing initial with
        | nil => rfl
        | cons item rest ih => rw [List.foldl_cons, ih, streamRegistrationStep_stopped]
      exact loop items ({ queue }, [], [], [], [], [], [])
    have drain := acc.1.drainReadyGroups_projection running actualFrame actualForest acc.2.2.2.2.1
    have actual := congrArg
      (fun value : ReferenceWorkQueue.State × List WorkQueueEvent
          × List ReferenceWorkQueue.GroupFailureEvent =>
        (value.1, .streamValues stream acc.2.2.2.1 acc.2.1 acc.2.2.1 :: value.2.1,
          acc.2.2.2.2.2.2 ++ value.2.2)) drain
    have full := congrArg
      (fun prepared : ReferenceWorkQueue.State × List Execution.DeliveryNode
          × List Execution.DeliveryNode × List StreamItemValue
          × List ReferenceWorkQueue.GroupFailureEvent =>
        (prepared.1.drainReadyGroups.1,
          .streamValues stream prepared.2.2.2.1 prepared.2.1 prepared.2.2.1
            :: prepared.1.drainReadyGroups.2.1,
          prepared.2.2.2.2 ++ prepared.1.drainReadyGroups.2.2)) fold
    exact actual.trans full

end GraphQL.IncrementalDelivery.AlternativeWorkQueue
