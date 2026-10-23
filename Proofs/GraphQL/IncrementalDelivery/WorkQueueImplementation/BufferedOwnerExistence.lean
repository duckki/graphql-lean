import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.BufferedOwnerRetention
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskOwnerHandlers
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StoredLinkReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamPreparation

/-! Live-owner existence for stored task records, independently of alternative replay.
These reference-kernel invariants are reusable premises for actual queue refinements.
-/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)

-----------------------------------------------------------------------------------------
-- A stored value has a live owner, not necessarily a healthy or already active one
-----------------------------------------------------------------------------------------

/-- Every buffered node has at least one live contributing group.
This proof-side invariant neither requires health nor constructs a native resource lease.
-/
def State.BufferedOwnersPresent (queue : State) : Prop :=
  ∀ node ∈ queue.taskNodes,
    node.value.isSome = true
    → ∃ key ∈ node.task.groups.map Execution.DeliveryNode.ref,
        key ∈ queue.groupNodes.map (fun group => group.group.node.ref)

private theorem State.BufferedOwnersPresent.putGroupNode {queue : State}
    (owners : queue.BufferedOwnersPresent) (updated : GroupNode)
    : (queue.putGroupNode updated).BufferedOwnersPresent := by
  intro node member stored
  rw [State.putGroupNode_refs]
  exact owners node member stored

theorem State.BufferedOwnersPresent.putTaskNode {queue : State}
    (owners : queue.BufferedOwnersPresent) (updated : TaskNode)
    (allowed
      : updated.value.isSome = true
        → ∃ key ∈ updated.task.groups.map Execution.DeliveryNode.ref,
            key ∈ queue.groupNodes.map (fun group => group.group.node.ref))
    : (queue.putTaskNode updated).BufferedOwnersPresent := by
  intro node member stored
  obtain ⟨old, oldMember, same⟩ := List.mem_map.mp member
  split at same
  · subst node; exact allowed stored
  · subst node; exact owners old oldMember stored

private theorem State.BufferedOwnersPresent.removeTask {queue : State}
    (owners : queue.BufferedOwnersPresent) (occurrence : Occurrence)
    : (queue.removeTask occurrence).BufferedOwnersPresent := by
  intro node member stored
  obtain ⟨key, contributes, present⟩ := owners node (List.mem_filter.mp member).1 stored
  refine ⟨key, contributes, ?_⟩
  simpa only [State.removeTask, List.map_map, Function.comp_def] using present

private theorem State.BufferedOwnersPresent.addGroups {queue : State}
    (owners : queue.BufferedOwnersPresent) (groups : List Group)
    : (queue.addGroups groups).1.BufferedOwnersPresent := by
  intro node member stored
  rw [State.addGroups_taskNodes] at member
  obtain ⟨key, contributes, present⟩ := owners node member stored
  exact ⟨key, contributes, queue.addGroups_includesRefs groups key present⟩

private theorem State.BufferedOwnersPresent.addTask {queue : State}
    (owners : queue.BufferedOwnersPresent) (task : Task)
    : (queue.addTask task).BufferedOwnersPresent := by
  intro node member stored
  rcases queue.addTask_startedOldOrNew task member with old | new
  · obtain ⟨key, contributes, present⟩ := owners node old stored
    exact ⟨key, contributes, queue.addTask_includesRefs task key present⟩
  · subst node; cases stored

private theorem State.BufferedOwnersPresent.addStreams {queue : State}
    (owners : queue.BufferedOwnersPresent) (streams : List Stream)
    (producer : Option Occurrence)
    : (queue.addStreams streams producer).1.BufferedOwnersPresent := by
  cases producer with
  | none => exact owners
  | some occurrence =>
      simp only [State.addStreams]
      split
      · exact owners
      · rename_i node found
        apply owners.putTaskNode
        exact owners node (List.mem_of_find?_eq_some found)

theorem State.BufferedOwnersPresent.integrate {queue : State}
    (owners : queue.BufferedOwnersPresent) (work : Work)
    (producer : Option Occurrence := none)
    : (queue.maybeIntegrateWork work producer).1.BufferedOwnersPresent := by
  have loop (tasks : List Task) (current : State) (prior : current.BufferedOwnersPresent)
      : (tasks.foldl State.addTask current).BufferedOwnersPresent := by
    induction tasks generalizing current with
    | nil => exact prior
    | cons task rest ih => exact ih _ (prior.addTask task)
  exact (loop work.tasks _ (owners.addGroups work.groups)).addStreams work.streams
    producer

-----------------------------------------------------------------------------------------
-- Pruning and successful release cannot silently erase the last buffered membership
-----------------------------------------------------------------------------------------

private theorem State.BufferedOwnersPresent.prune {queue : State}
    (owners : queue.BufferedOwnersPresent) (links : queue.StoredTaskLinks)
    (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.BufferedOwnersPresent := by
  intro node member stored
  have old : node ∈ queue.taskNodes := by rwa [State.pruneEmptyGroups_taskNodes] at member
  obtain ⟨key, contributes, present⟩ := owners node old stored
  exact ⟨
    key,
    contributes,
    State.pruneEmptyGroups_bufferedOwner_present links old stored contributes present
      groups
  ⟩

private theorem State.BufferedOwnersPresent.startTask {queue : State}
    (owners : queue.BufferedOwnersPresent) (occurrence : Occurrence)
    (available : List (Occurrence × Nat))
    : (queue.startTask occurrence available).BufferedOwnersPresent := by
  unfold State.startTask
  split
  · exact owners
  · split
    · exact owners
    · intro node member stored
      rcases List.mem_append.mp member with old | new
      · exact owners node old stored
      · obtain rfl := List.mem_singleton.mp new
        cases stored

private theorem State.BufferedOwnersPresent.removeGroup (queue : State) (key : Nat)
    : (queue.removeGroup key).BufferedOwnersPresent := by
  intro node member _stored
  have live := (List.mem_filter.mp member).2
  obtain ⟨group, contributes, present⟩ := List.any_eq_true.mp live
  obtain ⟨owner, retained, same⟩ := List.any_eq_true.mp present
  exact ⟨group.ref, List.mem_map_of_mem contributes,
    List.mem_map.mpr ⟨owner, retained, beq_iff_eq.mp same⟩⟩

/-- Cached rejection exposure preserves every buffered task's live owner metadata. -/
theorem State.BufferedOwnersPresent.cacheTaskFailures {queue : State}
    (owners : queue.BufferedOwnersPresent) (available : List (Occurrence × Nat))
    : (queue.cacheTaskFailures available).BufferedOwnersPresent := by
  induction available generalizing queue with
  | nil => exact owners
  | cons entry rest ih =>
      simp only [State.cacheTaskFailures, List.foldl_cons]
      split
      · exact ih owners
      · rename_i node found
        exact ih (owners.putTaskNode _ (owners node (List.mem_of_find?_eq_some found)))

private theorem State.BufferedOwnersPresent.startGroup {queue : State}
    (owners : queue.BufferedOwnersPresent) (key : Nat)
    (available : List (Occurrence × Nat))
    : (queue.startGroup key available).1.BufferedOwnersPresent := by
  have tasks (more : List Occurrence) (current : State) (prior : current.BufferedOwnersPresent)
      : (more.foldl (fun current task => current.startTask task available)
          current).BufferedOwnersPresent := by
    induction more generalizing current with
    | nil => exact prior
    | cons task rest ih => exact ih _ (prior.startTask task available)
  unfold State.startGroup
  dsimp only
  split
  · exact owners.cacheTaskFailures available
  · split
    · exact tasks _ _ (owners.cacheTaskFailures available)
    · exact State.BufferedOwnersPresent.removeGroup _ _

private theorem State.BufferedOwnersPresent.start {queue : State}
    (owners : queue.BufferedOwnersPresent) (released : NewWork)
    (available : List (Occurrence × Nat))
    : (queue.startNewWork released available).1.BufferedOwnersPresent := by
  have groups (keys : NodeRefs) (acc : State × List GroupFailureEvent)
      (prior : acc.1.BufferedOwnersPresent)
      : (keys.foldl (fun (current, failures) ref =>
          let (next, queued) := current.startGroup ref available
          (next, failures ++ queued)) acc).1.BufferedOwnersPresent := by
    induction keys generalizing acc with
    | nil => exact prior
    | cons key rest ih => exact ih _ (prior.startGroup key available)
  have streams (keys : NodeRefs) (current : State) (prior : current.BufferedOwnersPresent)
      : (keys.foldl State.startStream current).BufferedOwnersPresent := by
    induction keys generalizing current with
    | nil => exact prior
    | cons key rest ih =>
        apply ih
        unfold State.startStream
        split <;> exact prior
  exact streams _ _ (groups _ _ owners)

theorem State.BufferedOwnersPresent.prepareItems {queue : State}
    {work settled stream items} (owners : queue.BufferedOwnersPresent)
    (links : queue.StoredTaskLinks) (accounted : queue.PendingAccounting work settled)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : (queue.preparedStreamItems items available).BufferedOwnersPresent
      ∧ (queue.preparedStreamItems items available).StoredTaskLinks := by
  let property (current : State) := current.BufferedOwnersPresent ∧ current.StoredTaskLinks
    ∧ current.GroupRefsUnique ∧ current.RegistrationFrame work
  have step (current : State) (item : StreamItem) (member : item ∈ items)
      (prior : property current) : property (current.integrateStreamItem item available) := by
    have context := prior.2.2.2
    have prepared := prior.1.integrate item.work
    have preparedLinks := prior.2.1.maybeIntegrateWork prior.2.2.1 context.tasks context.started
      item.work
    exact ⟨(prepared.prune preparedLinks _).start _ available,
      (preparedLinks.pruneEmptyGroups _).startNewWork _ available,
      ((prior.2.2.1.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _ available,
      (context.integrateStreamItem matching member available).1⟩
  have initial : property queue := ⟨owners, links, accounted.refs, accounted.registration⟩
  have prepared := State.preparedStreamItems_preserves property initial items available step
  exact ⟨prepared.1, prepared.2.1⟩

/-- Live owners of every started task also cover the subset with buffered values. -/
theorem State.TaskOwnersPresent.buffered {queue : State}
    (owners : queue.TaskOwnersPresent)
    : queue.BufferedOwnersPresent :=
  fun node member _ => owners node member

/-- Actual source replay retains a live owner for every stored value.
Witness: the stronger started-task owner frame is derived from the same generated work,
valid inputs, and accepted starts; no executable health guard supplies this fact.
-/
theorem ExecutedWork.replayGraphEvents_bufferedOwnersPresent {work : Execution.Work}
    (generated : ExecutedWork work) (events : List GraphEvent)
    (valid : ValidGraphEvents work events)
    (accepted : (State.initialize (Work.fromExecution work)).acceptsBatch events = true)
    : ((State.initialize (Work.fromExecution work)).replayGraphEvents
        events).BufferedOwnersPresent :=
  (generated.replayGraphEvents_taskOwnerFrame events valid accepted).owners.buffered

/-- Normalized replay supplies the same live-owner evidence for stored values. -/
theorem ExecutedWork.runNormalized_bufferedOwnersPresent {work : Execution.Work}
    (generated : ExecutedWork work) (inputs : List (List GraphEvent))
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    : ((State.initialize (Work.fromExecution work)).runNormalized
        inputs).1.BufferedOwnersPresent :=
  (generated.runNormalized_taskOwnerFrame inputs valid started).owners.buffered

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
