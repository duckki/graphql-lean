import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupFailureSources
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PendingFailureFrames

/-! Actual handlers retain task-local provenance and return aggregate startup sources. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Stored internal notices retain their distinct available contributing causes.
This proposition is proof evidence, independent of task-node lifetime. -/
def State.QueuedFailureSources (queue : State) (work : Execution.Work)
    (inputs : List GraphEvent)
    : Prop :=
  ∀ failure ∈ queue.groupFailureEvents,
    GroupFailureSources work inputs failure.group.ref failure.errors

/-- Later source availability retains the same notice explanation. -/
theorem State.QueuedFailureSources.weaken {queue work before after}
    (queued : State.QueuedFailureSources queue work before)
    (included : before.Subset after)
    : queue.QueuedFailureSources work after :=
  fun failure member => (queued failure member).weaken included

/-- Consuming one pending head leaves the remaining notice explanations intact. -/
theorem State.QueuedFailureSources.handleGraphEvent {queue work inputs}
    (queued : State.QueuedFailureSources queue work inputs) (event : GraphEvent)
    (available : List (Occurrence × Nat))
    : (queue.handleGraphEvent event available).1.QueuedFailureSources work inputs :=
  fun failure member =>
    queued failure
      (queue.handleGraphEvent_groupFailureEvents_subset event available member)

/-- Internal registration and rejection evidence for aggregate source reporting.
The source list may contain failures whose FIFO notification has not yet been consumed.
-/
structure State.FailureSourceFrame (queue : State) (work : Execution.Work)
    (inputs : List GraphEvent)
    : Prop where
  rejections
    : queue.TaskRejectionsSatisfy
        (fun occurrence errors =>
          GraphEvent.taskFailure occurrence errors ∈ inputs)
  unique : queue.TaskMembershipsUnique
  sound : queue.GroupMembershipSound
  matching : queue.RegisteredTasksMatch work
  started : queue.StartedTasksRegistered

private theorem State.FailureSourceFrame.maybeIntegrateWork {queue : State} {work inputs}
    (frame : queue.FailureSourceFrame work inputs) (more : Work)
    (known : ∀ task ∈ more.tasks, TaskMatches work task)
    (producer : Option Occurrence := none)
    : (queue.maybeIntegrateWork more producer).1.FailureSourceFrame work inputs :=
  ⟨
    frame.rejections.maybeIntegrateWork more producer,
    frame.unique.maybeIntegrateWork more producer,
    frame.sound.maybeIntegrateWork more producer,
    frame.matching.maybeIntegrateWork more known producer,
    frame.started.maybeIntegrateWork more producer
  ⟩

private theorem State.FailureSourceFrame.pruneEmptyGroups {queue : State} {work inputs}
    (frame : queue.FailureSourceFrame work inputs) (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.FailureSourceFrame work inputs :=
  ⟨
    frame.rejections.pruneEmptyGroups groups,
    frame.unique.pruneEmptyGroups groups,
    frame.sound.pruneEmptyGroups groups,
    frame.matching.pruneEmptyGroups groups,
    frame.started.pruneEmptyGroups groups
  ⟩

private theorem State.FailureSourceFrame.finishGroupSuccess {queue : State} {work inputs}
    (frame : queue.FailureSourceFrame work inputs) (group : GroupNode)
    : (queue.finishGroupSuccess group).1.FailureSourceFrame work inputs :=
  ⟨
    frame.rejections.finishGroupSuccess group,
    frame.unique.finishGroupSuccess group,
    frame.sound.finishGroupSuccess group,
    frame.matching.finishGroupSuccess group,
    frame.started.finishGroupSuccess group
  ⟩

private theorem State.FailureSourceFrame.successGroupFold {queue : State} {work inputs}
    (frame : queue.FailureSourceFrame work inputs) (groups : List Execution.DeliveryNode)
    : (groups.foldl successGroupStep (queue, [], {})).1.FailureSourceFrame work
        inputs := by
  have loop (remaining : List Execution.DeliveryNode)
      (acc : State × List WorkQueueEvent × NewWork)
      (prior : acc.1.FailureSourceFrame work inputs)
      : (remaining.foldl successGroupStep acc).1.FailureSourceFrame work inputs := by
    induction remaining generalizing acc with
    | nil => exact prior
    | cons group rest ih =>
        simp only [List.foldl_cons, successGroupStep]
        split
        · exact ih _ prior
        · rename_i node found
          have member := List.mem_of_find?_eq_some found
          have updated
              : (acc.1.putGroupNode { node with pending := node.pending - 1 }).FailureSourceFrame
                  work inputs :=
            ⟨prior.rejections.putGroupNode _,
              prior.unique.putGroupNode _ (prior.unique node member),
              prior.sound.putGroupNode _ (prior.sound node member), prior.matching.putGroupNode _,
              prior.started.putGroupNode _⟩
          split
          · exact ih _ (updated.finishGroupSuccess _)
          · exact ih _ updated
  exact loop groups (queue, [], {}) frame

private theorem State.FailureSourceFrame.startNewWork {queue : State} {work inputs}
    (frame : queue.FailureSourceFrame work inputs) (released : NewWork)
    (available : List (Occurrence × Nat))
    (licensed
      : ∀ occurrence errors,
          (occurrence, errors) ∈ available
          → GraphEvent.taskFailure occurrence errors ∈ inputs)
    : (queue.startNewWork released available).1.FailureSourceFrame work inputs :=
  ⟨
    frame.rejections.startNewWork released available licensed,
    frame.unique.startNewWork released available,
    frame.sound.startNewWork released available,
    frame.matching.startNewWork released available,
    frame.started.startNewWork released available
  ⟩

/-- A successful task handler forwards only source-backed aggregate startup reports.
Witness: prepared registration and the owner fold preserve task-local provenance; initial
release and recursive draining each report their own distinct cached member failures.
-/
theorem State.FailureSourceFrame.taskSuccess_sources {queue : State}
    {work inputs occurrence result} (frame : queue.FailureSourceFrame work inputs)
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (sources : ∀ event ∈ inputs, event.MatchesWork work)
    (available : List (Occurrence × Nat))
    (licensed
      : ∀ occurrence errors,
          (occurrence, errors) ∈ available
          → GraphEvent.taskFailure occurrence errors ∈ inputs)
    : ∀ failure ∈ (queue.taskSuccess occurrence result available).2.2,
        GroupFailureSources work inputs failure.group.ref failure.errors := by
  cases found : queue.taskNode? occurrence with
  | none => simp [State.taskSuccess, found]
  | some node =>
      rw [queue.taskSuccess_eq occurrence result node found available]
      have member := List.mem_of_find?_eq_some found
      let stored := queue.putTaskNode { node with value := some result.value }
      have value : stored.FailureSourceFrame work inputs :=
        ⟨frame.rejections.putTaskNode _ (frame.rejections node member), frame.unique, frame.sound,
          frame.matching, frame.started.putTaskNode _ (frame.started node member)⟩
      have children : ∀ task ∈ result.work.tasks, TaskMatches work task := by
        intro task member
        obtain ⟨address, payload, same, known⟩ := matching.childTask_producer member
        exact ⟨⟨address, payload, some occurrence, same, known⟩,
          matching.childTask_groupsExact member⟩
      have prepared := value.maybeIntegrateWork result.work children (some occurrence)
      let released := node.task.groups.foldl successGroupStep
        ((stored.maybeIntegrateWork result.work (some occurrence)).1, [], {})
      have owners := prepared.successGroupFold node.task.groups
      have first := released.1.startNewWork_failure_sources owners.rejections owners.unique
        owners.sound owners.matching sources released.2.2 available licensed
      have activated := owners.startNewWork released.2.2 available licensed
      have later := State.drainReadyGroups_go_failure_sources activated.rejections activated.unique
        activated.sound activated.matching sources
        (released.1.startNewWork released.2.2 available).1.groupNodes.length available licensed
      intro failure reported
      exact (List.mem_append.mp reported).elim (first failure) (later failure)

private theorem State.FailureSourceFrame.preparedItems_sources {queue : State}
    {work inputs stream items} (frame : queue.FailureSourceFrame work inputs)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (sources : ∀ event ∈ inputs, event.MatchesWork work)
    (available : List (Occurrence × Nat))
    (licensed
      : ∀ occurrence errors,
          (occurrence, errors) ∈ available
          → GraphEvent.taskFailure occurrence errors ∈ inputs)
    : (queue.preparedStreamItems items available).FailureSourceFrame work inputs
      ∧ ∀ failure ∈
          (items.foldl (fun acc item => streamItemStep acc item available)
            (queue, [], [], [], [])).2.2.2.2,
          GroupFailureSources work inputs failure.group.ref failure.errors := by
  have loop (remaining : List StreamItem) (included : remaining.Subset items)
      (acc : State × List Execution.DeliveryNode × List Execution.DeliveryNode
        × List Execution.StreamItemValue × List GroupFailureEvent)
      (prior : acc.1.FailureSourceFrame work inputs)
      (reported : ∀ failure ∈ acc.2.2.2.2,
        GroupFailureSources work inputs failure.group.ref failure.errors)
      : (remaining.foldl (fun acc item => streamItemStep acc item available)
            acc).1.FailureSourceFrame
          work inputs
        ∧ ∀ failure ∈ (remaining.foldl (fun acc item => streamItemStep acc item available)
            acc).2.2.2.2,
            GroupFailureSources work inputs failure.group.ref failure.errors := by
    induction remaining generalizing acc with
    | nil => exact ⟨prior, reported⟩
    | cons item rest ih =>
        let integrated := acc.1.maybeIntegrateWork item.work
        let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
        let released := { integrated.2 with newGroups := pruned.2 }
        have children : ∀ task ∈ item.work.tasks, TaskMatches work task := by
          intro task member
          obtain ⟨address, payload, same, known⟩ := matching.streamItem_childTask_producer
            (included List.mem_cons_self) member
          exact ⟨⟨address, payload, some item.occurrence, same, known⟩,
            matching.streamItem_childTask_groupsExact (included List.mem_cons_self) member⟩
        have prepared := (prior.maybeIntegrateWork item.work children).pruneEmptyGroups
          integrated.2.newGroups
        have first := pruned.1.startNewWork_failure_sources prepared.rejections prepared.unique
          prepared.sound prepared.matching sources released available licensed
        apply ih (fun _ member => included (List.mem_cons_of_mem _ member))
          (streamItemStep acc item available)
          (prepared.startNewWork released available licensed)
        intro failure member
        exact (List.mem_append.mp member).elim (reported failure) (first failure)
  exact loop items (List.Subset.refl _) (queue, [], [], [], []) frame (by simp)

/-- Stream-item preparation and ready release retain exact aggregate failure sources. -/
theorem State.FailureSourceFrame.streamItems_sources {queue : State}
    {work inputs stream items} (frame : queue.FailureSourceFrame work inputs)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (sources : ∀ event ∈ inputs, event.MatchesWork work)
    (available : List (Occurrence × Nat))
    (licensed
      : ∀ occurrence errors,
          (occurrence, errors) ∈ available
          → GraphEvent.taskFailure occurrence errors ∈ inputs)
    : ∀ failure ∈ (queue.streamItems stream items available).2.2,
        GroupFailureSources work inputs failure.group.ref failure.errors := by
  rw [queue.streamItems_eq stream items available]
  split
  · simp
  · have prepared := frame.preparedItems_sources matching sources available licensed
    have later := State.drainReadyGroups_go_failure_sources prepared.1.rejections prepared.1.unique
      prepared.1.sound prepared.1.matching sources
      (queue.preparedStreamItems items available).groupNodes.length available licensed
    intro failure member
    exact (List.mem_append.mp member).elim (prepared.2 failure) (later failure)

/-- A matching dispatched input preserves the reporting frame at its actual cache snapshot. -/
theorem State.FailureSourceFrame.handleGraphEvent {queue : State} {work inputs event}
    (frame : queue.FailureSourceFrame work inputs) (received : event ∈ inputs)
    (matching : event.MatchesWork work) (available : List (Occurrence × Nat))
    (licensed
      : ∀ occurrence errors,
          (occurrence, errors) ∈ available
          → GraphEvent.taskFailure occurrence errors ∈ inputs)
    : (queue.handleGraphEvent event available).1.FailureSourceFrame work inputs :=
  ⟨
    frame.rejections.handleGraphEvent event (fun _ _ same => same ▸ received) available
      licensed,
    frame.unique.handleGraphEvent event available,
    frame.sound.handleGraphEvent event available,
    frame.matching.handleGraphEvent event matching available,
    frame.started.handleGraphEvent event available
  ⟩

/-- Both handler output channels retain exact aggregate contributing source failures.
Immediate task failures use a singleton inventory; queued startup failures retain every
distinct cached member cause collected before private work could start.
-/
theorem State.FailureSourceFrame.handleGraphEvent_sources {queue : State}
    {work inputs event} (frame : queue.FailureSourceFrame work inputs)
    (queued : queue.QueuedFailureSources work inputs)
    (received : event ∈ inputs) (sources : ∀ event ∈ inputs, event.MatchesWork work)
    (available : List (Occurrence × Nat))
    (licensed
      : ∀ occurrence errors,
          (occurrence, errors) ∈ available
          → GraphEvent.taskFailure occurrence errors ∈ inputs)
    : (∀ group errors,
        WorkQueueEvent.groupFailure group errors
          ∈ (queue.handleGraphEvent event available).2.1
        → GroupFailureSources work inputs group.ref errors)
      ∧ ∀ failure ∈ (queue.handleGraphEvent event available).2.2,
          GroupFailureSources work inputs failure.group.ref failure.errors := by
  have cached : (queue.cacheTaskFailures available).FailureSourceFrame work inputs :=
    ⟨frame.rejections.cacheTaskFailures available licensed,
      frame.unique.cacheTaskFailures available, frame.sound.cacheTaskFailures available,
      frame.matching.cacheTaskFailures available, frame.started.cacheTaskFailures available⟩
  constructor
  · intro group errors emitted
    rcases queue.handleGraphEvent_groupFailure_origin event available emitted with
      immediate | forwarded
    · obtain ⟨occurrence, task, same, found, owner⟩ := immediate
      subst event
      obtain ⟨owners, producer, path, failed⟩ := sources _ received
      obtain ⟨⟨_, _, _, _, known⟩, _⟩ := cached.matching task.task
        (cached.started task (List.mem_of_find?_eq_some found))
      have identity := (State.taskNode?_some found).2
      rw [identity] at known
      exact (GroupFailureSourceCause.single received failed ((known.unique failed).1 ▸ owner)).sources
    · obtain ⟨supplied, rest, _, head⟩ := forwarded
      exact queued ⟨group, errors⟩ (by rw [head]; exact List.mem_cons_self)
  · cases event with
    | taskSuccess occurrence result =>
        exact cached.taskSuccess_sources (sources _ received) sources available licensed
    | streamItems stream items =>
        exact cached.streamItems_sources (sources _ received) sources available licensed
    | taskFailure | streamSuccess | streamFailure | groupFailure =>
        simp [State.handleGraphEvent]

/-- Realizing startup enqueue effects preserves the reporting frame. -/
theorem State.FailureSourceFrame.dispatchGraphEvent {queue work inputs event}
    (frame : State.FailureSourceFrame queue work inputs) (received : event ∈ inputs)
    (matching : event.MatchesWork work) (available : List (Occurrence × Nat))
    (licensed
      : ∀ occurrence errors,
          (occurrence, errors) ∈ available
          → GraphEvent.taskFailure occurrence errors ∈ inputs)
    : (queue.dispatchGraphEvent event available).1.FailureSourceFrame work inputs := by
  have next := frame.handleGraphEvent received matching available licensed
  exact ⟨next.rejections, next.unique, next.sound, next.matching, next.started⟩

/-- FIFO dispatch preserves queued aggregate causes and explains emitted group reports. -/
theorem State.FailureSourceFrame.dispatchGraphEvent_sources {queue work inputs event}
    (frame : State.FailureSourceFrame queue work inputs)
    (queued : queue.QueuedFailureSources work inputs) (received : event ∈ inputs)
    (sources : ∀ event ∈ inputs, event.MatchesWork work)
    (available : List (Occurrence × Nat))
    (licensed
      : ∀ occurrence errors,
          (occurrence, errors) ∈ available
          → GraphEvent.taskFailure occurrence errors ∈ inputs)
    : (queue.dispatchGraphEvent event available).1.QueuedFailureSources work inputs
      ∧ (∀ group errors,
          WorkQueueEvent.groupFailure group errors
            ∈ (queue.dispatchGraphEvent event available).2
          → GroupFailureSources work inputs group.ref errors) := by
  have reported := frame.handleGraphEvent_sources queued received sources available licensed
  refine ⟨?_, reported.1⟩
  intro failure member
  rcases List.mem_append.mp member with earlier | fresh
  · exact queued.handleGraphEvent event available failure earlier
  · exact reported.2 failure fresh

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
