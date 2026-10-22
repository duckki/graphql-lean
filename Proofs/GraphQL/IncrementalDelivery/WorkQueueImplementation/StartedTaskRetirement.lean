import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PendingReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamPreparation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskProducerOrder
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskIntegrationLookups
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskMembershipIntegration
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PendingAccounting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskLookupUpdates

/-! A previously started computation remains present or has no remaining task memberships.
This proof evidence tracks existing records, without adding a runtime start ledger.
-/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open WorkQueueSemantics (Occurrence NodeRefs)

/-- A known started occurrence is still represented, or has been globally unlinked. -/
def State.StartedTaskDisposition (queue : State) (occurrence : Occurrence) : Prop :=
  (∃ node, queue.taskNode? occurrence = some node) ∨ queue.TaskMembershipAbsent occurrence

/-- The queue metadata needed to track a started occurrence through last-owner removal. -/
structure State.StartedTaskFrame (queue : State) (work : Execution.Work)
    (occurrence : Occurrence)
    : Prop where
  disposition : queue.StartedTaskDisposition occurrence
  sound : queue.GroupMembershipSound
  registered : queue.StartedTasksRegistered
  matching : queue.RegisteredTasksMatch work

/-- A missing computation in this frame has no live membership anywhere. -/
theorem State.StartedTaskDisposition.absent {queue : State} {occurrence}
    (prior : queue.StartedTaskDisposition occurrence)
    (missing : queue.taskNode? occurrence = none)
    : queue.TaskMembershipAbsent occurrence := by
  rcases prior with ⟨node, found⟩ | absent
  · rw [missing] at found
    cases found
  · exact absent

theorem State.StartedTaskDisposition.putTaskNode {queue : State} {occurrence}
    (prior : queue.StartedTaskDisposition occurrence) (updated : TaskNode)
    : (queue.putTaskNode updated).StartedTaskDisposition occurrence := by
  rcases prior with ⟨node, found⟩ | absent
  · left
    by_cases same : updated.task.occurrence = occurrence
    · exact ⟨updated, State.putTaskNode_lookup_same found updated same⟩
    · exact ⟨node, State.putTaskNode_lookup_other found updated same⟩
  · exact .inr (absent.putTaskNode updated)

theorem State.StartedTaskDisposition.removeTask {queue : State} {occurrence}
    (prior : queue.StartedTaskDisposition occurrence) (removed : Occurrence)
    : (queue.removeTask removed).StartedTaskDisposition occurrence := by
  by_cases same : occurrence = removed
  · exact .inr (same ▸ queue.removeTask_membershipAbsent removed)
  · rcases prior with ⟨node, found⟩ | absent
    · exact .inl ⟨node, by rwa [queue.removeTask_lookup_other same]⟩
    · exact .inr (absent.removeTask removed)

theorem State.StartedTaskDisposition.cacheTaskFailures {queue : State} {occurrence}
    (prior : queue.StartedTaskDisposition occurrence)
    (available : List (Occurrence × Nat))
    : (queue.cacheTaskFailures available).StartedTaskDisposition occurrence := by
  unfold State.cacheTaskFailures
  induction available generalizing queue with
  | nil => exact prior
  | cons entry rest ih =>
      apply ih
      dsimp only [List.foldl_cons]
      split
      · exact prior
      · exact prior.putTaskNode _

theorem State.StartedTaskDisposition.startTask {queue : State} {occurrence}
    (prior : queue.StartedTaskDisposition occurrence) (started : Occurrence)
    (available : List (Occurrence × Nat))
    : (queue.startTask started available).StartedTaskDisposition occurrence := by
  rcases prior with ⟨node, found⟩ | absent
  · left
    refine ⟨node, ?_⟩
    unfold State.startTask
    split
    · exact found
    · split
      · exact found
      · change (queue.taskNodes ++ _).find? _ = some node
        rw [List.find?_append]
        change (queue.taskNode? occurrence).or _ = some node
        simp [found]
  · right
    intro node member
    rw [State.startTask_groupNodes] at member
    exact absent node member

/-- Losing a started node in subtree removal leaves no surviving contributing membership. -/
theorem State.StartedTaskFrame.removeGroup {queue : State} {work occurrence}
    (frame : queue.StartedTaskFrame work occurrence) (ref : Nat)
    : (queue.removeGroup ref).StartedTaskFrame work occurrence := by
  refine ⟨?_, frame.sound.removeGroup ref, frame.registered.removeGroup ref,
    frame.matching.removeGroup ref⟩
  rcases frame.disposition with ⟨node, found⟩ | absent
  · cases missing : (queue.removeGroup ref).taskNode? occurrence with
    | some retained => exact .inl ⟨retained, missing⟩
    | none =>
        right
        intro owner live listed
        have oldMember := (List.mem_filter.mp live).1
        have key := (State.taskNode?_some found).2
        have contributes := frame.sound.startedOwner frame.registered frame.matching
          (List.mem_of_find?_eq_some found) oldMember (key.symm ▸ listed)
        obtain ⟨contributor, member, same⟩ := List.mem_map.mp contributes
        have kept : node ∈ (queue.removeGroup ref).taskNodes := by
          change node ∈ queue.taskNodes.filter (fun task => task.task.groups.any
            (fun group => (queue.removeGroup ref).groupNodes.any
              (fun current => current.group.node.ref == group.ref)))
          refine List.mem_filter.mpr ⟨List.mem_of_find?_eq_some found, ?_⟩
          exact List.any_eq_true.mpr ⟨contributor, member,
            List.any_eq_true.mpr ⟨owner, live, by simp [same]⟩⟩
        exact List.find?_eq_none.mp missing node kept
          ((occurrence_beq_iff_eq _ _).mpr key)
  · exact .inr (absent.removeGroup ref)

/-- Cache exposure retains a started occurrence's representation or global unlinking. -/
theorem State.StartedTaskFrame.cacheTaskFailures {queue : State} {work occurrence}
    (frame : queue.StartedTaskFrame work occurrence) (available : List (Occurrence × Nat))
    : (queue.cacheTaskFailures available).StartedTaskFrame work occurrence :=
  ⟨
    frame.disposition.cacheTaskFailures available,
    frame.sound.cacheTaskFailures available,
    frame.registered.cacheTaskFailures available,
    frame.matching.cacheTaskFailures available
  ⟩

theorem State.StartedTaskFrame.startTask {queue : State} {work occurrence}
    (frame : queue.StartedTaskFrame work occurrence) (started : Occurrence)
    (available : List (Occurrence × Nat))
    : (queue.startTask started available).StartedTaskFrame work occurrence :=
  ⟨
    frame.disposition.startTask started available,
    frame.sound.startTask started available,
    frame.registered.startTask started available,
    frame.matching.startTask started available
  ⟩

theorem State.StartedTaskDisposition.pruneEmptyGroups {queue : State} {occurrence}
    (prior : queue.StartedTaskDisposition occurrence) (groups)
    : (queue.pruneEmptyGroups groups).1.StartedTaskDisposition occurrence := by
  rcases prior with ⟨node, found⟩ | absent
  · left
    refine ⟨node, ?_⟩
    simpa only [State.taskNode?, State.pruneEmptyGroups_taskNodes] using found
  · exact .inr (absent.pruneEmptyGroups groups)

theorem State.StartedTaskDisposition.flushGroupTasks {queue : State} {occurrence}
    (prior : queue.StartedTaskDisposition occurrence) (tasks : List Occurrence)
    (values : List Execution.ExecutionGroupValue) (streams : NodeRefs)
    : (tasks.foldl flushGroupTask (queue, values, streams)).1.StartedTaskDisposition
        occurrence := by
  induction tasks generalizing queue values streams with
  | nil => exact prior
  | cons task rest ih =>
      simp only [List.foldl_cons, flushGroupTask]
      split
      · exact ih prior _ _
      · exact ih (prior.removeTask task) _ _

theorem State.StartedTaskDisposition.finishGroupSuccess {queue : State} {occurrence}
    (prior : queue.StartedTaskDisposition occurrence) (group : GroupNode)
    : (queue.finishGroupSuccess group).1.StartedTaskDisposition occurrence := by
  have flushed := prior.flushGroupTasks group.tasks [] []
  let values := group.tasks.foldl flushGroupTask (queue, [], [])
  let current : State := { values.1 with
    groupNodes := values.1.groupNodes.filter
      (fun node => node.group.node.ref != group.group.node.ref)
    rootGroups := values.1.rootGroups.filter (· != group.group.node.ref) }
  have filtered : current.StartedTaskDisposition occurrence := by
    rcases flushed with found | absent
    · exact .inl found
    · exact .inr (fun node member => absent node (List.mem_filter.mp member).1)
  exact filtered.pruneEmptyGroups _

theorem State.StartedTaskFrame.finishGroupSuccess {queue : State} {work occurrence}
    (frame : queue.StartedTaskFrame work occurrence) (group : GroupNode)
    : (queue.finishGroupSuccess group).1.StartedTaskFrame work occurrence :=
  ⟨
    frame.disposition.finishGroupSuccess group,
    frame.sound.finishGroupSuccess group,
    frame.registered.finishGroupSuccess group,
    frame.matching.finishGroupSuccess group
  ⟩

/-- Cached group startup cannot leave an earlier started task as an unstarted membership. -/
theorem State.StartedTaskFrame.startGroup {queue : State} {work occurrence}
    (frame : queue.StartedTaskFrame work occurrence) (ref : Nat)
    (available : List (Occurrence × Nat))
    : (queue.startGroup ref available).1.StartedTaskFrame work occurrence := by
  have cached := frame.cacheTaskFailures available
  unfold State.startGroup
  dsimp only
  split
  · exact cached
  · rename_i node found
    split
    · have loop (tasks : List Occurrence) (current : State)
          (prior : current.StartedTaskFrame work occurrence)
          : (tasks.foldl (fun q task => q.startTask task available)
              current).StartedTaskFrame work occurrence := by
        induction tasks generalizing current with
        | nil => exact prior
        | cons task rest ih => exact ih _ (prior.startTask task available)
      exact loop node.tasks _ cached
    · change ((queue.cacheTaskFailures available).removeGroup
        node.group.node.ref).StartedTaskFrame work occurrence
      rw [State.groupNode?_ref found]
      exact cached.removeGroup ref

/-- Both successful and failing newly released groups preserve this started-task frame. -/
theorem State.StartedTaskFrame.startNewWork {queue : State} {work occurrence}
    (frame : queue.StartedTaskFrame work occurrence) (released : NewWork)
    (available : List (Occurrence × Nat))
    : (queue.startNewWork released available).1.StartedTaskFrame work occurrence := by
  let step (acc : State × List GroupFailureEvent) (ref : Nat) :=
    let next := acc.1.startGroup ref available
    (next.1, acc.2 ++ next.2)
  have groups (refs : NodeRefs) (acc : State × List GroupFailureEvent)
      (prior : acc.1.StartedTaskFrame work occurrence)
      : (refs.foldl step acc).1.StartedTaskFrame work occurrence := by
    induction refs generalizing acc with
    | nil => exact prior
    | cons ref rest ih => exact ih _ (prior.startGroup ref available)
  have streams (refs : NodeRefs) (current : State)
      (prior : current.StartedTaskFrame work occurrence)
      : (refs.foldl State.startStream current).StartedTaskFrame work occurrence := by
    induction refs generalizing current with
    | nil => exact prior
    | cons ref rest ih =>
        apply ih
        unfold State.startStream
        split
        · exact prior
        · exact ⟨prior.disposition, prior.sound, prior.registered, prior.matching⟩
  exact streams _ _ (groups _ _
    ⟨frame.disposition, frame.sound, frame.registered, frame.matching⟩)

/-- Success-only draining preserves representation or global membership retirement. -/
theorem State.StartedTaskFrame.drainReadyGroups_go {queue : State} {work occurrence}
    (frame : queue.StartedTaskFrame work occurrence) (fuel : Nat)
    (available : List (Occurrence × Nat))
    : (State.drainReadyGroups.go available fuel queue).1.StartedTaskFrame work
        occurrence := by
  induction fuel generalizing queue with
  | zero => exact frame
  | succ fuel ih =>
      unfold State.drainReadyGroups.go
      dsimp only
      split
      · exact frame
      · rename_i node selected
        exact ih ((frame.finishGroupSuccess node).startNewWork _ available)

theorem State.StartedTaskFrame.putExistingTaskNode {queue : State} {work occurrence node}
    (frame : queue.StartedTaskFrame work occurrence) (member : node ∈ queue.taskNodes)
    (updated : TaskNode) (same : updated.task = node.task)
    : (queue.putTaskNode updated).StartedTaskFrame work occurrence :=
  ⟨
    frame.disposition.putTaskNode updated,
    frame.sound,
    frame.registered.putTaskNode updated (same ▸ frame.registered node member),
    frame.matching
  ⟩

theorem State.StartedTaskFrame.putGroupNode {queue : State} {work occurrence node}
    (frame : queue.StartedTaskFrame work occurrence) (member : node ∈ queue.groupNodes)
    (updated : GroupNode) (same : updated.tasks = node.tasks)
    (key : updated.group.node.ref = node.group.node.ref)
    : (queue.putGroupNode updated).StartedTaskFrame work occurrence := by
  refine ⟨?_, frame.sound.putGroupNode updated ?_, frame.registered.putGroupNode updated,
    frame.matching.putGroupNode updated⟩
  · rcases frame.disposition with found | absent
    · exact .inl found
    · exact .inr (absent.putGroupNode updated (same ▸ absent node member))
  · intro task listed
    rw [same] at listed
    simpa only [key] using frame.sound node member task listed

/-- Fresh integration cannot leave a retired occurrence as an unstarted membership. -/
theorem State.StartedTaskFrame.maybeIntegrateWork {queue : State} {work occurrence}
    (frame : queue.StartedTaskFrame work occurrence) (incoming : Work)
    (known : ∀ task ∈ incoming.tasks, TaskMatches work task)
    (fresh : ∀ task ∈ incoming.tasks, occurrence ≠ task.occurrence)
    (producer : Option Occurrence := none)
    : (queue.maybeIntegrateWork incoming producer).1.StartedTaskFrame work
        occurrence := by
  refine ⟨?_, frame.sound.maybeIntegrateWork incoming producer,
    frame.registered.maybeIntegrateWork incoming producer,
    frame.matching.maybeIntegrateWork incoming known producer⟩
  rcases frame.disposition with ⟨node, found⟩ | absent
  · left
    by_cases same : producer = some occurrence
    · subst producer
      obtain ⟨next, lookup, _, _⟩ := State.maybeIntegrateWork_lookup_producer found incoming
      exact ⟨next, lookup⟩
    · exact ⟨node, State.maybeIntegrateWork_lookup_other found incoming producer same⟩
  · exact .inr (absent.maybeIntegrateWork incoming fresh producer)

theorem State.StartedTaskFrame.pruneEmptyGroups {queue : State} {work occurrence}
    (frame : queue.StartedTaskFrame work occurrence) (groups)
    : (queue.pruneEmptyGroups groups).1.StartedTaskFrame work occurrence :=
  ⟨
    frame.disposition.pruneEmptyGroups groups,
    frame.sound.pruneEmptyGroups groups,
    frame.registered.pruneEmptyGroups groups,
    frame.matching.pruneEmptyGroups groups
  ⟩

theorem State.StartedTaskFrame.successGroupFold {queue : State} {work occurrence}
    (frame : queue.StartedTaskFrame work occurrence)
    (groups : List Execution.DeliveryNode) (events : List Execution.WorkQueueEvent)
    (released : NewWork)
    : (groups.foldl successGroupStep (queue, events, released)).1.StartedTaskFrame
        work occurrence := by
  induction groups generalizing queue events released with
  | nil => exact frame
  | cons group rest ih =>
      simp only [List.foldl_cons, successGroupStep]
      split
      · exact ih frame _ _
      · rename_i node found
        have updated := frame.putGroupNode (List.mem_of_find?_eq_some found)
          {node with pending := node.pending - 1} rfl rfl
        split
        · exact ih (updated.finishGroupSuccess _) _ _
        · exact ih updated _ _

/-- A successful callback preserves the started-task frame, including its ignored branch. -/
theorem State.StartedTaskFrame.taskSuccess {queue : State} {work occurrence}
    (frame : queue.StartedTaskFrame work occurrence) (source : Occurrence)
    (result : TaskResult) (known : ∀ task ∈ result.work.tasks, TaskMatches work task)
    (fresh : ∀ task ∈ result.work.tasks, occurrence ≠ task.occurrence)
    (available : List (Occurrence × Nat))
    : (queue.taskSuccess source result available).1.StartedTaskFrame work occurrence := by
  cases found : queue.taskNode? source with
  | none => simpa only [State.taskSuccess, found] using frame
  | some node =>
      rw [queue.taskSuccess_eq source result node found available]
      have stored := frame.putExistingTaskNode (List.mem_of_find?_eq_some found)
        {node with value := some result.value} rfl
      have prepared := stored.maybeIntegrateWork result.work known fresh (some source)
      exact ((prepared.successGroupFold node.task.groups [] {}).startNewWork _ available)
        |>.drainReadyGroups_go _ available

/-- Failure either retires the occurrence's memberships or retains its computation. -/
theorem State.StartedTaskFrame.taskFailure {queue : State} {work occurrence}
    (frame : queue.StartedTaskFrame work occurrence) (source : Occurrence) (errors : Nat)
    : (queue.taskFailure source errors).1.StartedTaskFrame work occurrence := by
  cases found : queue.taskNode? source with
  | none => simpa only [State.taskFailure, found] using frame
  | some node =>
      rw [queue.taskFailure_eq source errors node found]
      apply failureGroupFold_preserves (fun current => current.StartedTaskFrame work occurrence)
        (fun _ ref prior => prior.removeGroup ref)
      exact frame.putExistingTaskNode (List.mem_of_find?_eq_some found)
        {node with rejection := some errors} rfl

/-- Each item integrates fresh tasks before subsequent cached startup and ready draining. -/
theorem State.StartedTaskFrame.streamItems {queue : State} {work occurrence stream items}
    (frame : queue.StartedTaskFrame work occurrence)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (fresh : ∀ item ∈ items, ∀ task ∈ item.work.tasks, occurrence ≠ task.occurrence)
    (available : List (Occurrence × Nat))
    : (queue.streamItems stream items available).1.StartedTaskFrame work occurrence := by
  rw [queue.streamItems_eq stream items available]
  split
  · exact frame
  · apply State.StartedTaskFrame.drainReadyGroups_go (available := available)
    apply State.preparedStreamItems_preserves (fun q => q.StartedTaskFrame work occurrence)
      frame items available
    intro current item member prior
    have known : ∀ task ∈ item.work.tasks, TaskMatches work task := by
      intro task listed
      obtain ⟨address, payload, same, descriptor⟩ :=
        matching.streamItem_childTask_producer member listed
      exact ⟨⟨address, payload, some item.occurrence, same, descriptor⟩,
        matching.streamItem_childTask_groupsExact member listed⟩
    exact ((prior.maybeIntegrateWork item.work known (fresh item member)).pruneEmptyGroups _)
      |>.startNewWork _ available

/-- A fresh matching input cannot resurrect any previously registered tracked occurrence. -/
theorem State.StartedTaskFrame.handleGraphEvent {queue : State} {work occurrence event}
    (frame : queue.StartedTaskFrame work occurrence) (matching : event.MatchesWork work)
    (fresh : ∀ child ∈ event.childTasks, occurrence ≠ child.occurrence)
    (available : List (Occurrence × Nat))
    : (queue.handleGraphEvent event available).1.StartedTaskFrame work occurrence := by
  have cached := frame.cacheTaskFailures available
  cases event with
  | taskSuccess source result =>
      apply cached.taskSuccess source result _ fresh available
      intro task member
      obtain ⟨address, payload, same, descriptor⟩ := matching.childTask_producer member
      exact ⟨⟨address, payload, some source, same, descriptor⟩,
        matching.childTask_groupsExact member⟩
  | groupFailure failure =>
      change ((queue.cacheTaskFailures available).groupFailure failure).1.StartedTaskFrame work occurrence
      unfold State.groupFailure
      split
      · exact cached
      · split
        · exact ⟨cached.disposition, cached.sound, cached.registered, cached.matching⟩
        · exact cached
  | taskFailure source errors => exact cached.taskFailure source errors
  | streamItems stream items =>
      exact cached.streamItems matching
        (fun item member task listed => fresh task (List.mem_flatMap.mpr ⟨item, member, listed⟩))
        available
  | streamSuccess stream =>
      change ((queue.cacheTaskFailures available).streamSuccess stream).1.StartedTaskFrame
        work occurrence
      unfold State.streamSuccess
      split
      · exact ⟨cached.disposition, cached.sound, cached.registered, cached.matching⟩
      · exact cached
  | streamFailure stream errors =>
      change ((queue.cacheTaskFailures available).streamFailure stream errors).1.StartedTaskFrame
        work occurrence
      unfold State.streamFailure
      split
      · exact ⟨cached.disposition, cached.sound, cached.registered, cached.matching⟩
      · exact cached

/-- Retaining enqueue effects changes no started-task or membership evidence. -/
theorem State.StartedTaskFrame.dispatchGraphEvent {queue : State} {work occurrence event}
    (frame : queue.StartedTaskFrame work occurrence) (matching : event.MatchesWork work)
    (fresh : ∀ child ∈ event.childTasks, occurrence ≠ child.occurrence)
    (available : List (Occurrence × Nat))
    : (queue.dispatchGraphEvent event available).1.StartedTaskFrame work occurrence := by
  have next := frame.handleGraphEvent matching fresh available
  exact ⟨next.disposition, next.sound, next.registered, next.matching⟩

/-- Initialization of a tracked started occurrence uses only existing pending metadata. -/
theorem State.PendingAccounting.startedTaskFrame {queue : State}
    {work settled occurrence node} (ledger : queue.PendingAccounting work settled)
    (found : queue.taskNode? occurrence = some node)
    : queue.StartedTaskFrame work occurrence :=
  ⟨.inl ⟨node, found⟩, ledger.sound, ledger.started, ledger.matching⟩

/-- A valid continuation preserves retirement of an already registered started occurrence.
Producer provenance and source freshness exclude re-registering its identity. No source
acceptance, output accounting, or permanent runtime start ledger is assumed.
-/
theorem State.StartedTaskFrame.replayGraphEvents {queue : State} {work occurrence before}
    (frame : queue.StartedTaskFrame work occurrence)
    (registered : occurrence ∈ queue.tasks.map Task.occurrence)
    (ready : TaskProducersSucceeded work queue.tasks before)
    (ordered : ProducerOrder work (queue.tasks.map Task.occurrence))
    (events : List GraphEvent) (valid : ValidGraphEvents work (before ++ events))
    (available : List (Occurrence × Nat))
    : (queue.replayGraphEvents events available).StartedTaskFrame work occurrence := by
  induction events generalizing queue before with
  | nil => exact frame
  | cons event rest ih =>
      have earlier : (before ++ [event]).IsPrefix (before ++ event :: rest) := ⟨rest, by simp⟩
      obtain ⟨priorValid, matching, fresh⟩ := validGraphEvents_last (valid.prefix earlier)
      have next := frame.dispatchGraphEvent matching (by
        intro child member same
        exact matching.childTask_not_registered ready fresh member (same ▸ registered)) available
      have source := State.dispatchGraphEvent_producerOrder ready ordered
        priorValid matching fresh available
      apply ih next _ source.1 source.2
        (by simpa only [List.append_assoc, List.singleton_append] using valid)
      obtain ⟨task, member, same⟩ := List.mem_map.mp registered
      exact List.mem_map.mpr
        ⟨task, queue.handleGraphEvent_tasks_subset event available member, same⟩

/-- A callback initially eligible in a batch remains represented or globally unlinked at
any FIFO prefix, including before a notification that has become stale.
-/
theorem State.PendingAccounting.startedTaskDisposition_atPrefix
    {queue : State} {work settled before occurrence node}
    (ledger : queue.PendingAccounting work settled)
    (found : queue.taskNode? occurrence = some node)
    (ready : TaskProducersSucceeded work queue.tasks before)
    (ordered : ProducerOrder work (queue.tasks.map Task.occurrence))
    (events : List GraphEvent) (valid : ValidGraphEvents work (before ++ events))
    (available : List (Occurrence × Nat))
    : (queue.replayGraphEvents events available).StartedTaskDisposition occurrence := by
  have registered := List.mem_map_of_mem
    (f := Task.occurrence) (ledger.started node (List.mem_of_find?_eq_some found))
  rw [(State.taskNode?_some found).2] at registered
  exact ((ledger.startedTaskFrame found).replayGraphEvents registered ready ordered
    events valid available).disposition

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
