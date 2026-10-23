import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitializationSpecialization
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskLinkDispositionHandlers
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.BufferedOwnerRetention
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartedTaskAnnouncements
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RootPresenceReplay

/-! Live-owner existence for every computation record, including unfinished tasks.
Membership-based pruning/release retention is reused; no stored-value, healthy-owner,
wire-observation or cleanup-endpoint premise substitutes for this existence fact.
-/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open WorkQueueSemantics (Occurrence NodeRefs)
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)

-----------------------------------------------------------------------------------------
-- Owner existence is independent of completion and activation status
-----------------------------------------------------------------------------------------

def State.TaskOwnersPresent (queue : State) : Prop :=
  ∀ node ∈ queue.taskNodes,
    ∃ key ∈ node.task.groups.map Execution.DeliveryNode.ref,
      key ∈ queue.groupNodes.map (fun group => group.group.node.ref)

theorem State.TaskOwnersPresent.putGroupNode {queue : State}
    (owners : queue.TaskOwnersPresent) (updated : GroupNode)
    : (queue.putGroupNode updated).TaskOwnersPresent := by
  intro node member
  rw [State.putGroupNode_refs]
  exact owners node member

theorem State.TaskOwnersPresent.putTaskNode {queue : State}
    (owners : queue.TaskOwnersPresent) (updated : TaskNode)
    (allowed
      : ∃ key ∈ updated.task.groups.map Execution.DeliveryNode.ref,
          key ∈ queue.groupNodes.map (fun group => group.group.node.ref))
    : (queue.putTaskNode updated).TaskOwnersPresent := by
  intro node member
  obtain ⟨old, oldMember, same⟩ := List.mem_map.mp member
  split at same
  · subst node
    exact allowed
  · subst node
    exact owners old oldMember

theorem State.TaskOwnersPresent.removeTask {queue : State}
    (owners : queue.TaskOwnersPresent) (occurrence : Occurrence)
    : (queue.removeTask occurrence).TaskOwnersPresent := by
  intro node member
  obtain ⟨key, contributes, present⟩ := owners node (List.mem_filter.mp member).1
  exact ⟨
    key,
    contributes,
    by simpa only [State.removeTask, List.map_map, Function.comp_def] using present
  ⟩

theorem State.TaskOwnersPresent.removeGroup (queue : State) (key : Nat)
    : (queue.removeGroup key).TaskOwnersPresent := by
  intro node member
  obtain ⟨owner, contributes, present⟩ := List.any_eq_true.mp (List.mem_filter.mp member).2
  obtain ⟨group, retained, same⟩ := List.any_eq_true.mp present
  exact ⟨owner.ref, List.mem_map_of_mem contributes,
    List.mem_map.mpr ⟨group, retained, beq_iff_eq.mp same⟩⟩

-----------------------------------------------------------------------------------------
-- Registration retains existing owners and justifies newly started records
-----------------------------------------------------------------------------------------

theorem State.TaskOwnersPresent.addGroups {queue : State}
    (owners : queue.TaskOwnersPresent) (groups : List Group)
    : (queue.addGroups groups).1.TaskOwnersPresent := by
  intro node member
  rw [State.addGroups_taskNodes] at member
  obtain ⟨key, contributes, present⟩ := owners node member
  exact ⟨key, contributes, queue.addGroups_includesRefs groups key present⟩

theorem State.TaskOwnersPresent.addTask {queue : State}
    (owners : queue.TaskOwnersPresent) (roots : queue.RootGroupsPresent) (task : Task)
    : (queue.addTask task).TaskOwnersPresent := by
  intro node member
  rcases queue.addTask_startedOldOrRootOwner task member with
    old | ⟨same, owner, contributes, active⟩
  · obtain ⟨key, contributes, present⟩ := owners node old
    exact ⟨key, contributes, queue.addTask_includesRefs task key present⟩
  · subst node
    exact ⟨owner.ref, List.mem_map_of_mem contributes,
      queue.addTask_includesRefs task owner.ref (roots owner.ref active)⟩

theorem State.TaskOwnersPresent.addStreams {queue : State}
    (owners : queue.TaskOwnersPresent) (streams : List Stream)
    (producer : Option Occurrence := none)
    : (queue.addStreams streams producer).1.TaskOwnersPresent := by
  cases producer with
  | none => exact owners
  | some occurrence =>
      unfold State.addStreams
      dsimp only
      split
      · exact owners
      · rename_i node found
        apply State.TaskOwnersPresent.putTaskNode
        · exact owners
        · exact owners node (List.mem_of_find?_eq_some found)

theorem State.TaskOwnersPresent.maybeIntegrateWork {queue : State}
    (owners : queue.TaskOwnersPresent) (roots : queue.RootGroupsPresent) (incoming : Work)
    (producer : Option Occurrence := none)
    : (queue.maybeIntegrateWork incoming producer).1.TaskOwnersPresent := by
  have rootGroups (current : State) (present : current.RootGroupsPresent) (groups : List Group)
      : (current.addGroups groups).1.RootGroupsPresent := by
    intro key member
    rw [State.addGroups_rootGroups] at member
    exact current.addGroups_includesRefs groups key (present key member)
  have rootTask (current : State) (present : current.RootGroupsPresent) (task : Task)
      : (current.addTask task).RootGroupsPresent := by
    intro key member
    rw [State.addTask_rootGroups] at member
    exact current.addTask_includesRefs task key (present key member)
  have loop (tasks : List Task) (current : State) (prior : current.TaskOwnersPresent)
      (present : current.RootGroupsPresent)
      : (tasks.foldl State.addTask current).TaskOwnersPresent := by
    induction tasks generalizing current with
    | nil => exact prior
    | cons task rest ih =>
        exact ih _ (prior.addTask present task) (rootTask current present task)
  exact (loop incoming.tasks _ (owners.addGroups incoming.groups)
    (rootGroups queue roots incoming.groups)).addStreams incoming.streams producer

-----------------------------------------------------------------------------------------
-- Complete links prevent pruning or flushing a retained record's live owners
-----------------------------------------------------------------------------------------

theorem State.TaskOwnersPresent.pruneEmptyGroups {queue : State}
    (owners : queue.TaskOwnersPresent) (disposition : queue.TaskLinkDisposition)
    (registered : queue.StartedTasksRegistered) (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.TaskOwnersPresent := by
  intro node member
  have old : node ∈ queue.taskNodes := by rwa [State.pruneEmptyGroups_taskNodes] at member
  obtain ⟨key, contributes, present⟩ := owners node old
  exact ⟨key, contributes, State.pruneEmptyGroups_linkedOwner_present
    (disposition.startedLinks registered old) contributes present groups⟩

theorem State.TaskOwnersPresent.finishGroupSuccess {queue : State}
    (owners : queue.TaskOwnersPresent) (disposition : queue.TaskLinkDisposition)
    (registered : queue.StartedTasksRegistered) (group : GroupNode)
    (live : group ∈ queue.groupNodes)
    : (queue.finishGroupSuccess group).1.TaskOwnersPresent := by
  intro node member
  have old := (queue.finishGroupSuccess_retained_unlisted group member).1
  obtain ⟨key, contributes, present⟩ := owners node old
  exact ⟨key, contributes, State.finishGroupSuccess_linkedOwner_present group live
    (disposition.startedLinks registered old) member contributes present⟩

/-- Exposing cached failures preserves each computation's owner metadata. -/
theorem State.TaskOwnersPresent.cacheTaskFailures {queue : State}
    (owners : queue.TaskOwnersPresent) (available : List (Occurrence × Nat))
    : (queue.cacheTaskFailures available).TaskOwnersPresent := by
  induction available generalizing queue with
  | nil => exact owners
  | cons entry rest ih =>
      simp only [State.cacheTaskFailures, List.foldl_cons]
      split
      · exact ih owners
      · rename_i node found
        exact ih (owners.putTaskNode _ (owners node (List.mem_of_find?_eq_some found)))

/-- A newly started computation is supported by the live group requesting it. -/
private theorem State.TaskOwnersPresent.startLinkedTask {queue : State} {work}
    (owners : queue.TaskOwnersPresent) (sound : queue.GroupMembershipSound)
    (registered : queue.StartedTasksRegistered)
    (matching : queue.RegisteredTasksMatch work) (chosen : Occurrence) (group : GroupNode)
    (live : group ∈ queue.groupNodes) (listed : chosen ∈ group.tasks)
    (available : List (Occurrence × Nat))
    : (queue.startTask chosen available).TaskOwnersPresent := by
  have newOwner (node : TaskNode) (member : node ∈ (queue.startTask chosen available).taskNodes)
      (same : node.task.occurrence = chosen)
      : ∃ key ∈ node.task.groups.map Execution.DeliveryNode.ref,
          key ∈ (queue.startTask chosen available).groupNodes.map (fun g => g.group.node.ref) := by
    have groupLive : group ∈ (queue.startTask chosen available).groupNodes := by
      rwa [State.startTask_groupNodes]
    exact ⟨group.group.node.ref,
      (sound.startTask chosen available).startedOwner (registered.startTask chosen available)
        (matching.startTask chosen available) member groupLive (same.symm ▸ listed),
      List.mem_map_of_mem groupLive⟩
  intro node member
  have started := member
  unfold State.startTask at member
  split at member
  · simpa only [State.startTask_groupNodes] using owners node member
  · split at member
    · simpa only [State.startTask_groupNodes] using owners node member
    · rename_i task found
      rcases List.mem_append.mp member with old | fresh
      · simpa only [State.startTask_groupNodes] using owners node old
      · obtain rfl := List.mem_singleton.mp fresh
        exact newOwner _ started ((occurrence_beq_iff_eq _ _).mp
          (List.find?_some (p := fun task : Task => task.occurrence == chosen) found))

/-- Healthy startup retains owners; failed startup removes unsupported computations. -/
theorem State.TaskOwnersPresent.startGroup {queue : State} {work : Execution.Work}
    (owners : queue.TaskOwnersPresent) (sound : queue.GroupMembershipSound)
    (registered : queue.StartedTasksRegistered)
    (matching : queue.RegisteredTasksMatch work) (ref : Nat)
    (available : List (Occurrence × Nat) := [])
    : (queue.startGroup ref available).1.TaskOwnersPresent := by
  have tasks (more : List Occurrence) (group : GroupNode) (current : State)
      (prior : current.TaskOwnersPresent) (valid : current.GroupMembershipSound)
      (known : current.StartedTasksRegistered) (matched : current.RegisteredTasksMatch work)
      (live : group ∈ current.groupNodes) (listed : more.Subset group.tasks)
      : (more.foldl (fun current task => current.startTask task available)
          current).TaskOwnersPresent := by
    induction more generalizing current with
    | nil => exact prior
    | cons task rest ih =>
        exact ih _
          (prior.startLinkedTask valid known matched task group live
            (listed List.mem_cons_self) available)
          (valid.startTask task available) (known.startTask task available)
          (matched.startTask task available) (by rwa [State.startTask_groupNodes])
          (fun _ member => listed (List.mem_cons_of_mem _ member))
  unfold State.startGroup
  dsimp only
  split
  · exact owners.cacheTaskFailures available
  · rename_i group found
    split
    · exact tasks _ group _ (owners.cacheTaskFailures available)
        (sound.cacheTaskFailures available) (registered.cacheTaskFailures available)
        (matching.cacheTaskFailures available) (List.mem_of_find?_eq_some found)
        (List.Subset.refl _)
    · exact State.TaskOwnersPresent.removeGroup _ _

/-- Activation follows each actual startup state, including immediate group removal. -/
theorem State.TaskOwnersPresent.startNewWork {queue : State} {work : Execution.Work}
    (owners : queue.TaskOwnersPresent) (sound : queue.GroupMembershipSound)
    (registered : queue.StartedTasksRegistered)
    (matching : queue.RegisteredTasksMatch work) (released : NewWork)
    (available : List (Occurrence × Nat) := [])
    : (queue.startNewWork released available).1.TaskOwnersPresent := by
  have groups (more : NodeRefs) (acc : State × List GroupFailureEvent)
      (prior : acc.1.TaskOwnersPresent) (valid : acc.1.GroupMembershipSound)
      (known : acc.1.StartedTasksRegistered) (matched : acc.1.RegisteredTasksMatch work)
      : (more.foldl (fun (current, failures) ref =>
          let (next, queued) := current.startGroup ref available
          (next, failures ++ queued)) acc).1.TaskOwnersPresent := by
    induction more generalizing acc with
    | nil => exact prior
    | cons ref rest ih =>
        exact ih _ (prior.startGroup valid known matched ref available)
          (valid.startGroup ref available) (known.startGroup ref available)
          (matched.startGroup ref available)
  have streams (more : NodeRefs) (current : State) (prior : current.TaskOwnersPresent)
      : (more.foldl State.startStream current).TaskOwnersPresent := by
    induction more generalizing current with
    | nil => exact prior
    | cons ref rest ih =>
        apply ih
        unfold State.startStream
        split <;> exact prior
  exact streams _ _ (groups _ _ owners sound registered matching)

-----------------------------------------------------------------------------------------
-- Non-registering release carries one compatible owner and membership frame
-----------------------------------------------------------------------------------------

/-- Minimal reference metadata needed during draining; independent of pending debt and
host/resource histories. Every field concerns the same concrete queue endpoint.
-/
structure State.TaskOwnerFrame (queue : State) (work : Execution.Work) : Prop where
  owners : queue.TaskOwnersPresent
  disposition : queue.TaskLinkDisposition
  keys : queue.GroupRefsUnique
  registered : queue.StartedTasksRegistered
  matching : queue.RegisteredTasksMatch work
  sound : queue.GroupMembershipSound

theorem State.TaskOwnerFrame.startNewWork {queue : State} {work : Execution.Work}
    (frame : queue.TaskOwnerFrame work) (released : NewWork)
    (available : List (Occurrence × Nat) := [])
    : (queue.startNewWork released available).1.TaskOwnerFrame work :=
  ⟨
    frame.owners.startNewWork frame.sound frame.registered frame.matching released
      available,
    frame.disposition.startNewWork released available,
    frame.keys.startNewWork released available,
    frame.registered.startNewWork released available,
    frame.matching.startNewWork released available,
    frame.sound.startNewWork released available
  ⟩

theorem State.TaskOwnerFrame.finishGroupSuccess {queue : State} {work : Execution.Work}
    (frame : queue.TaskOwnerFrame work) (group : GroupNode)
    (live : group ∈ queue.groupNodes)
    : (queue.finishGroupSuccess group).1.TaskOwnerFrame work :=
  ⟨
    frame.owners.finishGroupSuccess frame.disposition frame.registered group live,
    frame.disposition.finishGroupSuccess group,
    frame.keys.finishGroupSuccess group,
    frame.registered.finishGroupSuccess group,
    frame.matching.finishGroupSuccess group,
    frame.sound.finishGroupSuccess group
  ⟩

theorem State.TaskOwnerFrame.removeGroup {queue : State} {work : Execution.Work}
    (frame : queue.TaskOwnerFrame work) (key : Nat)
    : (queue.removeGroup key).TaskOwnerFrame work :=
  ⟨
    State.TaskOwnersPresent.removeGroup queue key,
    frame.disposition.removeGroup key,
    frame.keys.removeGroup key,
    frame.registered.removeGroup key,
    frame.matching.removeGroup key,
    frame.sound.removeGroup key
  ⟩

/-- Rejection replay retains live owners through the task update and owner removals. -/
theorem State.TaskOwnerFrame.taskFailure {queue : State} {work : Execution.Work}
    (frame : queue.TaskOwnerFrame work) (occurrence : Occurrence) (errors : Nat)
    : (queue.taskFailure occurrence errors).1.TaskOwnerFrame work := by
  cases found : queue.taskNode? occurrence with
  | none => simpa only [State.taskFailure, found] using frame
  | some task =>
      have member := List.mem_of_find?_eq_some found
      rw [queue.taskFailure_eq occurrence errors task found]
      apply failureGroupFold_preserves (fun current => current.TaskOwnerFrame work)
        (fun _ ref prior => prior.removeGroup ref)
      exact ⟨frame.owners.putTaskNode _ (frame.owners task member),
        frame.disposition.putTaskNode _, frame.keys,
        frame.registered.putTaskNode _ (frame.registered task member), frame.matching, frame.sound⟩

theorem State.TaskOwnerFrame.drainReadyGroups {queue : State} {work : Execution.Work}
    (frame : queue.TaskOwnerFrame work) (available : List (Occurrence × Nat) := [])
    : (queue.drainReadyGroups available).1.TaskOwnerFrame work :=
  State.drainReadyGroups_preserves (fun current => current.TaskOwnerFrame work)
    (valid := frame)
    (fun _ group prior live _ _ =>
      (prior.finishGroupSuccess group live).startNewWork _ available)

theorem State.TaskOwnerFrame.removeTask {queue : State} {work : Execution.Work}
    (frame : queue.TaskOwnerFrame work) (occurrence : Occurrence)
    : (queue.removeTask occurrence).TaskOwnerFrame work :=
  ⟨
    frame.owners.removeTask occurrence,
    frame.disposition.removeTask occurrence,
    frame.keys.removeTask occurrence,
    frame.registered.removeTask occurrence,
    frame.matching.removeTask occurrence,
    frame.sound.removeTask occurrence
  ⟩

theorem State.TaskOwnerFrame.putGroupNodeSameTasks {queue : State} {work : Execution.Work}
    (frame : queue.TaskOwnerFrame work) (node : GroupNode)
    (present : node ∈ queue.groupNodes) (updated : GroupNode)
    (sameKey : updated.group.node.ref = node.group.node.ref)
    (sameTasks : updated.tasks = node.tasks)
    : (queue.putGroupNode updated).TaskOwnerFrame work := by
  refine ⟨frame.owners.putGroupNode updated,
    frame.disposition.putGroupNodeSameTasks frame.keys node present updated sameKey sameTasks,
    frame.keys.putGroupNode updated, frame.registered.putGroupNode updated,
    frame.matching.putGroupNode updated, ?_⟩
  apply frame.sound.putGroupNode
  intro occurrence member
  rw [sameTasks] at member
  rw [sameKey]
  exact frame.sound node present occurrence member

theorem State.TaskOwnerFrame.successFold {queue : State} {work : Execution.Work}
    (frame : queue.TaskOwnerFrame work) (groups : List Execution.DeliveryNode)
    (events : List WorkQueueEvent) (released : NewWork)
    : (groups.foldl successGroupStep (queue, events, released)).1.TaskOwnerFrame
        work := by
  induction groups generalizing queue events released with
  | nil => exact frame
  | cons group rest ih =>
      simp only [List.foldl_cons, successGroupStep]
      split
      · exact ih frame _ _
      · rename_i node found
        let updated := { node with pending := node.pending - 1 }
        have changed := frame.putGroupNodeSameTasks node (List.mem_of_find?_eq_some found)
          updated rfl rfl
        split
        · apply ih _ _ _
          exact changed.finishGroupSuccess updated (List.mem_map.mpr
            ⟨node, List.mem_of_find?_eq_some found, by simp [updated]⟩)
        · exact ih changed _ _

theorem State.TaskOwnerFrame.pruneEmptyGroups {queue : State} {work : Execution.Work}
    (frame : queue.TaskOwnerFrame work) (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.TaskOwnerFrame work :=
  ⟨
    frame.owners.pruneEmptyGroups frame.disposition frame.registered groups,
    frame.disposition.pruneEmptyGroups groups,
    frame.keys.pruneEmptyGroups groups,
    frame.registered.pruneEmptyGroups groups,
    frame.matching.pruneEmptyGroups groups,
    frame.sound.pruneEmptyGroups groups
  ⟩

theorem State.TaskOwnerFrame.maybeIntegrateWork {queue : State} {work : Execution.Work}
    (frame : queue.TaskOwnerFrame work) (roots : queue.RootGroupsPresent)
    (registered : queue.TaskGroupsRegistered) (incoming : Work)
    (known : ∀ task ∈ incoming.tasks, TaskMatches work task)
    (producer : Option Occurrence := none)
    : (queue.maybeIntegrateWork incoming producer).1.TaskOwnerFrame work :=
  ⟨
    frame.owners.maybeIntegrateWork roots incoming producer,
    frame.disposition.maybeIntegrateWork frame.keys registered frame.matching incoming
      known producer,
    frame.keys.maybeIntegrateWork incoming producer,
    frame.registered.maybeIntegrateWork incoming producer,
    frame.matching.maybeIntegrateWork incoming known producer,
    frame.sound.maybeIntegrateWork incoming producer
  ⟩

theorem State.TaskOwnerFrame.putExistingTaskNode {queue : State} {work : Execution.Work}
    (frame : queue.TaskOwnerFrame work) (node : TaskNode)
    (member : node ∈ queue.taskNodes) (updated : TaskNode)
    (sameTask : updated.task = node.task)
    : (queue.putTaskNode updated).TaskOwnerFrame work := by
  refine ⟨frame.owners.putTaskNode updated (sameTask ▸ frame.owners node member),
    frame.disposition.putTaskNode updated, frame.keys,
    frame.registered.putTaskNode updated (sameTask ▸ frame.registered node member),
    frame.matching, frame.sound⟩

set_option maxHeartbeats 800000 in
theorem createWorkQueue_taskOwnerFrame (work : Execution.Work)
    : (State.initialize (Work.fromExecution work)).TaskOwnerFrame work := by
  rw [State.initialize_empty_eq_activation]
  let initial := Work.fromExecution work
  let integrated := (({} : State).maybeIntegrateWork initial).1
  let newWork := (({} : State).maybeIntegrateWork initial).2
  let pruned := (integrated.pruneEmptyGroups newWork.newGroups).1
  let groups := (integrated.pruneEmptyGroups newWork.newGroups).2
  let roots := { newWork with newGroups := groups }
  have empty : ({} : State).TaskOwnerFrame work := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [State.TaskOwnersPresent,
      State.TaskLinkDisposition, State.GroupRefsUnique, State.StartedTasksRegistered,
      State.RegisteredTasksMatch, State.GroupMembershipSound]
  have known : ∀ task ∈ initial.tasks, TaskMatches work task := by
    intro task member
    obtain ⟨address, payload, occurrenceEq, located⟩ :=
      workFromSpec_tasks_taskAt WorkQueueSemantics.Located.root member
    exact ⟨⟨address, payload, none, occurrenceEq, located⟩,
      workFromSpec_tasks_groupsExact WorkQueueSemantics.Located.root member⟩
  have prepared := empty.maybeIntegrateWork (by intro key member; cases member)
    (by intro task member; cases member) initial known
  have finished := (prepared.pruneEmptyGroups newWork.newGroups).startNewWork roots
  exact ⟨finished.owners, finished.disposition, finished.keys, finished.registered,
    finished.matching, finished.sound⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
