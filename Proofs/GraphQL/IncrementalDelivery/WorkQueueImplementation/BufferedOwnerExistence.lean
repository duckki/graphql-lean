import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.BufferedOwnerRetention
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
    : (queue.startTask occurrence).BufferedOwnersPresent := by
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

private theorem State.BufferedOwnersPresent.startGroup {queue : State}
    (owners : queue.BufferedOwnersPresent) (key : Nat)
    : (queue.startGroup key).BufferedOwnersPresent := by
  unfold State.startGroup
  split
  · exact owners
  · split
    · exact owners
    · have loop (tasks : List Occurrence) (current : State) (prior : current.BufferedOwnersPresent)
          : (tasks.foldl State.startTask current).BufferedOwnersPresent := by
        induction tasks generalizing current with
        | nil => exact prior
        | cons task rest ih => exact ih _ (prior.startTask task)
      exact loop _ _ owners

private theorem State.BufferedOwnersPresent.start {queue : State}
    (owners : queue.BufferedOwnersPresent) (released : NewWork)
    : (queue.startNewWork released).BufferedOwnersPresent := by
  have groups (keys : NodeRefs) (current : State) (prior : current.BufferedOwnersPresent)
      : (keys.foldl State.startGroup current).BufferedOwnersPresent := by
    induction keys generalizing current with
    | nil => exact prior
    | cons key rest ih => exact ih _ (prior.startGroup key)
  have streams (keys : NodeRefs) (current : State) (prior : current.BufferedOwnersPresent)
      : (keys.foldl State.startStream current).BufferedOwnersPresent := by
    induction keys generalizing current with
    | nil => exact prior
    | cons key rest ih =>
        apply ih
        unfold State.startStream
        split <;> exact prior
  exact streams _ _ (groups _ _ owners)

private theorem State.BufferedOwnersPresent.removeGroup (queue : State) (key : Nat)
    : (queue.removeGroup key).BufferedOwnersPresent := by
  intro node member _stored
  have live := (List.mem_filter.mp member).2
  obtain ⟨group, contributes, present⟩ := List.any_eq_true.mp live
  obtain ⟨owner, retained, same⟩ := List.any_eq_true.mp present
  exact ⟨group.ref, List.mem_map_of_mem contributes,
    List.mem_map.mpr ⟨owner, retained, beq_iff_eq.mp same⟩⟩

private theorem State.BufferedOwnersPresent.flush {queue : State}
    (owners : queue.BufferedOwnersPresent) (links : queue.StoredTaskLinks)
    (group : GroupNode) (live : group ∈ queue.groupNodes)
    : (queue.finishGroupSuccess group).1.BufferedOwnersPresent := by
  intro node member stored
  obtain ⟨old, _⟩ := queue.finishGroupSuccess_retained_unlisted group member
  obtain ⟨key, contributes, present⟩ := owners node old stored
  exact ⟨key, contributes,
    State.finishGroupSuccess_bufferedOwner_present links group live member stored contributes present⟩

private theorem State.BufferedOwnersPresent.drain {queue : State}
    (owners : queue.BufferedOwnersPresent) (links : queue.StoredTaskLinks)
    : queue.drainReadyGroups.1.BufferedOwnersPresent := by
  have both : queue.BufferedOwnersPresent ∧ queue.StoredTaskLinks := ⟨owners, links⟩
  exact (State.drainReadyGroups_preserves
    (fun current => current.BufferedOwnersPresent ∧ current.StoredTaskLinks) (valid := both)
    (fun current group prior live _ _ _ =>
      ⟨(prior.1.flush prior.2 group live).start _,
        (prior.2.finishGroupSuccess group).startNewWork _⟩)
    (fun current group errors prior _ _ _ =>
      ⟨State.BufferedOwnersPresent.removeGroup current group.group.node.ref,
        prior.2.removeGroup group.group.node.ref⟩)).1

-----------------------------------------------------------------------------------------
-- Fresh successful storage supplies its initial owner before any contributor closes
-----------------------------------------------------------------------------------------

/-- An actually healthy supporter is a live contributor, independently of task start. -/
theorem taskHasHealthyOwner_present {queue : State} {task : Task}
    (healthy : queue.taskHasHealthyOwner task = true)
    : ∃ key ∈ task.groups.map Execution.DeliveryNode.ref,
        key ∈ queue.groupNodes.map (fun group => group.group.node.ref) := by
  obtain ⟨group, contributes, healthy⟩ := List.any_eq_true.mp healthy
  cases found : queue.groupNode? group.ref with
  | none => simp [State.groupIsHealthy, found] at healthy
  | some owner =>
      exact ⟨group.ref, List.mem_map_of_mem contributes,
        List.mem_map.mpr ⟨owner, List.mem_of_find?_eq_some found, State.groupNode?_ref found⟩⟩

private theorem State.BufferedOwnersPresent.successFold {queue : State}
    (owners : queue.BufferedOwnersPresent) (links : queue.StoredTaskLinks)
    (keys : queue.GroupRefsUnique) (groups : List Execution.DeliveryNode)
    (events : List WorkQueueEvent) (released : NewWork)
    : (groups.foldl successGroupStep
        (queue, events, released)).1.BufferedOwnersPresent := by
  induction groups generalizing queue events released with
  | nil => exact owners
  | cons group rest ih =>
      simp only [List.foldl_cons, successGroupStep]
      split
      · exact ih owners links keys _ _
      · rename_i node found
        have changedLinks := links.putGroupNodeSameTasks keys node
          (List.mem_of_find?_eq_some found) { node with pending := node.pending - 1 } rfl rfl
        have changedOwners := owners.putGroupNode { node with pending := node.pending - 1 }
        have changedKeys := keys.putGroupNode { node with pending := node.pending - 1 }
        split
        · apply ih _ (changedLinks.finishGroupSuccess _) (changedKeys.finishGroupSuccess _) _ _
          exact changedOwners.flush changedLinks _ (List.mem_map.mpr
            ⟨node, List.mem_of_find?_eq_some found, by simp⟩)
        · exact ih changedOwners changedLinks changedKeys _ _

private theorem State.BufferedOwnersPresent.taskSuccess {queue : State} {work settled}
    (owners : queue.BufferedOwnersPresent) (links : queue.StoredTaskLinks)
    (accounted : queue.PendingAccounting work settled)
    (occurrence : Occurrence) (result : TaskResult) (fresh : occurrence ∉ settled)
    : (queue.taskSuccess occurrence result).1.BufferedOwnersPresent := by
  cases found : queue.taskNode? occurrence with
  | none => simpa only [State.taskSuccess, found] using owners
  | some node =>
      cases healthy : queue.taskHasHealthyOwner node.task with
      | false =>
          simpa [State.taskSuccess, found, healthy] using owners.removeTask occurrence
      | true =>
          have known := State.taskNode?_some found
          have registered := accounted.started node known.1
          have installed := owners.putTaskNode { node with value := some result.value }
            (fun _ => taskHasHealthyOwner_present healthy)
          have installedLinks := links.putTaskNode { node with value := some result.value }
            (fun _ => accounted.links node.task registered (known.2.symm ▸ fresh))
          have installedStarted := accounted.started.putTaskNode
            { node with value := some result.value } registered
          have preparedLinks := installedLinks.maybeIntegrateWork accounted.refs
            accounted.taskGroups installedStarted result.work (some occurrence)
          have installedKeys : (queue.putTaskNode
              { node with value := some result.value }).GroupRefsUnique := accounted.refs
          have preparedKeys := installedKeys.maybeIntegrateWork result.work (some occurrence)
          have prepared := installed.integrate result.work (some occurrence)
          have folded := prepared.successFold preparedLinks preparedKeys node.task.groups [] {}
          have foldedLinks := preparedLinks.successGroupFold preparedKeys node.task.groups [] {}
          rw [queue.taskSuccess_eq occurrence result node found]
          simp only [healthy, Bool.not_true, Bool.false_eq_true, ite_false]
          exact (folded.start _).drain (foldedLinks.startNewWork _)

private theorem State.BufferedOwnersPresent.taskFailure {queue : State}
    (owners : queue.BufferedOwnersPresent) (occurrence : Occurrence) (errors : Nat)
    : (queue.taskFailure occurrence errors).1.BufferedOwnersPresent := by
  have loop (groups : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent)
      (prior : acc.1.BufferedOwnersPresent)
      : (groups.foldl (failureGroupStep errors) acc).1.BufferedOwnersPresent := by
    induction groups generalizing acc with
    | nil => exact prior
    | cons group rest ih =>
        apply ih
        dsimp only [failureGroupStep]
        split
        · exact prior
        · split
          · exact State.BufferedOwnersPresent.removeGroup _ _
          · exact prior.putGroupNode _
  unfold State.taskFailure
  split
  · exact owners
  · split
    · exact owners.removeTask occurrence
    · exact loop _ _ (owners.removeTask occurrence)

theorem State.BufferedOwnersPresent.prepareItems {queue : State}
    {work settled stream items} (owners : queue.BufferedOwnersPresent)
    (links : queue.StoredTaskLinks) (accounted : queue.PendingAccounting work settled)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    : (queue.preparedStreamItems items).BufferedOwnersPresent
      ∧ (queue.preparedStreamItems items).StoredTaskLinks := by
  let property (current : State) := current.BufferedOwnersPresent ∧ current.StoredTaskLinks
    ∧ current.GroupRefsUnique ∧ current.LiveGroupsRegistered ∧ current.TaskGroupsRegistered
    ∧ current.StartedTasksRegistered
  have step (current : State) (item : StreamItem) (member : item ∈ items)
      (prior : property current) : property (current.integrateStreamItem item) := by
    have prepared := prior.1.integrate item.work
    have preparedLinks := prior.2.1.maybeIntegrateWork prior.2.2.1 prior.2.2.2.2.1
      prior.2.2.2.2.2 item.work
    have registration := current.integrateStreamItem_registration prior.2.2.2.1
      prior.2.2.2.2.1 matching member
    exact ⟨(prepared.prune preparedLinks _).start _,
      (preparedLinks.pruneEmptyGroups _).startNewWork _,
      ((prior.2.2.1.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _,
      registration.1, registration.2.1,
      ((prior.2.2.2.2.2.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _⟩
  have initial : property queue := ⟨owners, links, accounted.refs, accounted.liveGroups,
    accounted.taskGroups, accounted.started⟩
  have prepared := State.preparedStreamItems_preserves property initial items step
  exact ⟨prepared.1, prepared.2.1⟩

private theorem State.BufferedOwnersPresent.streamItems {queue : State}
    {work settled stream items} (owners : queue.BufferedOwnersPresent)
    (links : queue.StoredTaskLinks) (accounted : queue.PendingAccounting work settled)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    : (queue.streamItems stream items).1.BufferedOwnersPresent := by
  have prepared := owners.prepareItems links accounted matching
  rw [queue.streamItems_eq stream items]
  split
  · exact owners
  · exact prepared.1.drain prepared.2

-----------------------------------------------------------------------------------------
-- Derive the invariant throughout the exact generated source history
-----------------------------------------------------------------------------------------

/-- Fresh matching input preserves live owners of every stored buffer. -/
theorem State.BufferedOwnersPresent.handleGraphEvent {queue : State} {work before}
    (owners : queue.BufferedOwnersPresent) (links : queue.StoredTaskLinks)
    (accounted : queue.PendingAccounting work (GraphEvent.taskSettlements before))
    (event : GraphEvent) (matching : event.MatchesWork work) (fresh : event.Fresh before)
    : (queue.handleGraphEvent event).1.BufferedOwnersPresent := by
  cases event with
  | taskSuccess occurrence result =>
      exact owners.taskSuccess links accounted occurrence result
        (fun member => fresh.2.2.1 occurrence List.mem_cons_self
          (GraphEvent.taskSettlements_subsetIdentities before member))
  | taskFailure occurrence errors => exact owners.taskFailure occurrence errors
  | streamItems stream items => exact owners.streamItems links accounted matching
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess]
      split <;> exact owners
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> exact owners

private theorem State.BufferedOwnersPresent.replay {queue : State} {work before}
    (owners : queue.BufferedOwnersPresent) (links : queue.StoredTaskLinks)
    (accounted : queue.PendingAccounting work (GraphEvent.taskSettlements before))
    (generated : ExecutedWork work) (events : List GraphEvent)
    (valid : ValidGraphEvents work (before ++ events))
    (accepted : queue.acceptsBatch events = true)
    : (queue.replayGraphEvents events).BufferedOwnersPresent := by
  induction events generalizing queue before with
  | nil => exact owners
  | cons event rest ih =>
      have earlier : (before ++ [event]).IsPrefix (before ++ event :: rest) :=
        ⟨rest, by simp⟩
      obtain ⟨_, matching, fresh⟩ := validGraphEvents_last (valid.prefix earlier)
      have accepts : queue.acceptsGraphEvent event = true
          ∧ (queue.handleGraphEvent event).1.acceptsBatch rest = true := by
        simpa only [State.acceptsBatch, Bool.and_eq_true] using accepted
      have included := GraphEvent.taskSettlements_subsetIdentities before
      have nextOwners := owners.handleGraphEvent links accounted event matching fresh
      have nextLinks := links.handleGraphEvent accounted included event matching fresh
      have next := accounted.handleGraphEvent generated included event matching fresh accepts.1
      rw [← GraphEvent.taskSettlements_append] at next
      exact ih nextOwners nextLinks next
        (by simpa only [List.append_assoc, List.singleton_append] using valid) accepts.2

private theorem initial_bufferedOwners (work : Work)
    : (State.initialize work).BufferedOwnersPresent := by
  intro node member stored
  have empty := createWorkQueue_storedValues work (fun _ _ => False)
  cases value : node.value with
  | none => simp [value] at stored
  | some payload => exact (empty node member payload value).elim

/-- All generated stored values have a live owner after any valid started replay prefix.
Witness: healthy installation starts with a live owner, successful flushing preserves any
surviving buffered membership, and failure filtering explicitly retains a live contributor.
-/
theorem ExecutedWork.replayGraphEvents_bufferedOwnersPresent {work : Execution.Work}
    (generated : ExecutedWork work) (events : List GraphEvent)
    (valid : ValidGraphEvents work events)
    (accepted : (State.initialize (Work.fromExecution work)).acceptsBatch events = true)
    : ((State.initialize (Work.fromExecution work)).replayGraphEvents
        events).BufferedOwnersPresent :=
  (initial_bufferedOwners (Work.fromExecution work)).replay (before := [])
    (createWorkQueue_storedTaskLinks _) (createWorkQueue_pendingAccounting work) generated
    events valid accepted

/-- Normalized batches preserve the same raw buffer-owner evidence. -/
theorem ExecutedWork.runNormalized_bufferedOwnersPresent {work : Execution.Work}
    (generated : ExecutedWork work) (inputs : List (List GraphEvent))
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    : ((State.initialize (Work.fromExecution work)).runNormalized
        inputs).1.BufferedOwnersPresent := by
  have accepted := (State.initialize (Work.fromExecution work)).batchesStarted_acceptsBatch inputs
    (by rwa [← inputsStarted_eq_batchesStarted])
  have replayed := (initial_bufferedOwners (Work.fromExecution work)).replay
    (before := []) (createWorkQueue_storedTaskLinks _) (createWorkQueue_pendingAccounting work)
    generated inputs.flatten valid accepted
  obtain ⟨terminal, same⟩ := createWorkQueue_runNormalized_stateCore started
  rw [same]
  exact replayed

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
