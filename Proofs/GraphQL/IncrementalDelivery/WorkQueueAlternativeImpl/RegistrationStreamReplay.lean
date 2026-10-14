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

/-- Proof-facing name for the actual public per-item operation, not a replacement handler. -/
def streamRegistrationStep (acc : StreamRegistrationAcc)
    (item : ReferenceWorkQueue.StreamItem)
    : StreamRegistrationAcc :=
  let (current, groups, streams, values, targets, effects) := acc
  let (integrated, newWork) := current.maybeIntegrateWork item.work
  let (queue, nonempty) := integrated.queue.pruneEmptyGroups newWork.newGroups
  let (started, nextTargets) :=
    ({ integrated with queue }).startNewWork
      { newWork.newWork with newGroups := nonempty } newWork targets
  (
    started,
    groups ++ nonempty,
    streams ++ newWork.newStreams,
    values ++ [item.value],
    nextTargets,
    effects
    ++ [.adopt item.occurrence]
    ++ (nextTargets.drop targets.length).flatMap CleanupTarget.effects
  )

/-- Keep the queue, ordered notices and payloads; host observations have no reference field. -/
def streamRegistrationProjection (acc : StreamRegistrationAcc)
    : ReferenceWorkQueue.State
      × List Execution.DeliveryNode
      × List Execution.DeliveryNode
      × List StreamItemValue :=
  (acc.1.queue, acc.2.1, acc.2.2.1, acc.2.2.2.1)

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
    : streamRegistrationProjection (streamRegistrationStep acc item)
      = ReferenceWorkQueue.streamItemStep (streamRegistrationProjection acc) item := by
  obtain ⟨state, groups, streams, values, targets, effects⟩ := acc
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
  have queue := State.integrateStreamItem_queue present matching item known targets running
  dsimp only at queue
  apply Prod.ext
  · exact queue
  · change (groups ++ (registered.1.queue.pruneEmptyGroups registered.2.newGroups).2,
        streams ++ registered.2.newStreams, values ++ [item.value]) = _
    rw [nonempty]
    dsimp only [registered]
    rw [sameGroups, sameStreams]
    rfl

/-- Each actual item step preserves the reader guard. -/
theorem streamRegistrationStep_stopped (acc : StreamRegistrationAcc)
    (item : ReferenceWorkQueue.StreamItem)
    : (streamRegistrationStep acc item).1.stopped = acc.1.stopped := by
  change (({ (acc.1.maybeIntegrateWork item.work).1 with
    queue := ((acc.1.maybeIntegrateWork item.work).1.queue.pruneEmptyGroups
      (acc.1.maybeIntegrateWork item.work).2.newGroups).1 }).startNewWork _ _ _).1.stopped
    = acc.1.stopped
  rw [State.startNewWork_stopped, State.maybeIntegrateWork_stopped]

/-- Every FIFO preparation prefix keeps the same interruption guard. -/
theorem streamRegistrationFold_stopped (items : List ReferenceWorkQueue.StreamItem)
    (acc : StreamRegistrationAcc)
    : (items.foldl streamRegistrationStep acc).1.stopped = acc.1.stopped := by
  induction items generalizing acc with
  | nil => rfl
  | cons item rest ih => rw [List.foldl_cons, ih, streamRegistrationStep_stopped]

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
    (fun current => current.RegisteredTasksMatch work) matching items
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
    (stream : Execution.DeliveryNode) (items : List ReferenceWorkQueue.StreamItem)
    (matched : (ReferenceWorkQueue.GraphEvent.streamItems stream items).MatchesWork work)
    : let queue :=
        (ReferenceWorkQueue.State.initialize
          (ReferenceWorkQueue.Work.fromExecution work)).replayGraphEvents
          events
      streamRegistrationProjection
        (items.foldl streamRegistrationStep ({ queue }, [], [], [], [], []))
      = items.foldl ReferenceWorkQueue.streamItemStep (queue, [], [], []) := by
  let queue := (ReferenceWorkQueue.State.initialize
    (ReferenceWorkQueue.Work.fromExecution work)).replayGraphEvents events
  let initial : ReferenceWorkQueue.State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue := (queue, [], [], [])
  have loop (remaining : List ReferenceWorkQueue.StreamItem)
      (earlier : List ReferenceWorkQueue.StreamItem) (partition : items = earlier ++ remaining)
      (acc : StreamRegistrationAcc)
      (same : streamRegistrationProjection acc = earlier.foldl ReferenceWorkQueue.streamItemStep initial)
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
          (queueEq ▸ registered) item (matchedItem_tasks matched member) running
        have nextPartition : items = (earlier ++ [item]) ++ rest := by
          simpa only [List.append_assoc, List.singleton_append] using partition
        have next : streamRegistrationProjection (streamRegistrationStep acc item)
            = (earlier ++ [item]).foldl ReferenceWorkQueue.streamItemStep initial := by
          rw [step, same, List.foldl_append, List.foldl_cons, List.foldl_nil]
        have later := ih (earlier ++ [item]) nextPartition (streamRegistrationStep acc item)
          next ((streamRegistrationStep_stopped acc item).trans running)
        simpa only [List.foldl_cons, List.foldl_append, List.foldl_nil] using later
  exact loop items [] rfl ({ queue }, [], [], [], [], []) rfl rfl

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
      : (ReferenceWorkQueue.State.initialize
          (ReferenceWorkQueue.Work.fromExecution work)).acceptsBatch
          events
        = true)
    (stream : Execution.DeliveryNode) (items : List ReferenceWorkQueue.StreamItem)
    (matched : (ReferenceWorkQueue.GraphEvent.streamItems stream items).MatchesWork work)
    : let queue :=
        (ReferenceWorkQueue.State.initialize
          (ReferenceWorkQueue.Work.fromExecution work)).replayGraphEvents
          events
      let alternative := ({ queue } : State).streamItems stream items
      (alternative.1.queue, alternative.2.1) = queue.streamItems stream items := by
  let queue := (ReferenceWorkQueue.State.initialize
    (ReferenceWorkQueue.Work.fromExecution work)).replayGraphEvents events
  change ((({ queue } : State).streamItems stream items).1.queue,
    (({ queue } : State).streamItems stream items).2.1) = queue.streamItems stream items
  have fold := referencePrefix_streamRegistrationFold generated events matching stream items matched
  dsimp only at fold
  have projection
      : ({ queue } : State).streamItems stream items =
        if !queue.rootStreams.contains stream.ref then
          ({ queue }, [], [.acknowledge stream.ref])
        else
          let acc := items.foldl streamRegistrationStep ({ queue }, [], [], [], [], [])
          let drained := acc.1.drainReadyGroups acc.2.2.2.2.1
          (drained.1,
            .streamValues stream acc.2.2.2.1 acc.2.1 acc.2.2.1 :: drained.2.1,
            acc.2.2.2.2.2 ++ [.acknowledge stream.ref] ++
              (drained.2.2.drop acc.2.2.2.2.1.length).flatMap CleanupTarget.effects) := rfl
  rw [projection, ReferenceWorkQueue.State.streamItems_eq]
  split
  · rfl
  · let acc := items.foldl streamRegistrationStep ({ queue }, [], [], [], [], [])
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
      exact loop items ({ queue }, [], [], [], [], [])
    have drain := acc.1.drainReadyGroups_projection running actualFrame actualForest acc.2.2.2.2.1
    have actual := congrArg (fun pair => (pair.1,
      .streamValues stream acc.2.2.2.1 acc.2.1 acc.2.2.1 :: pair.2)) drain
    have full := congrArg (fun prepared : ReferenceWorkQueue.State × List Execution.DeliveryNode
        × List Execution.DeliveryNode × List StreamItemValue =>
          (prepared.1.drainReadyGroups.1,
            .streamValues stream prepared.2.2.2 prepared.2.1 prepared.2.2.1
              :: prepared.1.drainReadyGroups.2)) fold
    exact actual.trans full

end GraphQL.IncrementalDelivery.AlternativeWorkQueue
