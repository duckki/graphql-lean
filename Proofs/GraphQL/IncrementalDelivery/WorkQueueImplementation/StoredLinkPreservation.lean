import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StoredTaskLinks
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PendingAccounting

/-! Source handlers preserve buffered memberships through permanent registration. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Registration protects old contributor refs, even when their records have retired
-----------------------------------------------------------------------------------------

/-- Installing a value preserves buffered links when its task already has those links.
Witness: replaced nodes use the supplied memberships; unchanged nodes retain their links.
No uniqueness of the mutable task map is required.
-/
theorem State.StoredTaskLinks.putTaskNode {queue : State} (linked : queue.StoredTaskLinks)
    (updated : TaskNode)
    (allowed
      : updated.value.isSome = true
        → queue.TaskLinkedOn updated.task.occurrence
            (updated.task.groups.map Execution.DeliveryNode.ref))
    : (queue.putTaskNode updated).StoredTaskLinks := by
  intro node member stored
  obtain ⟨old, oldMember, same⟩ := List.mem_map.mp member
  split at same
  · subst node
    exact allowed stored
  · subst node
    exact linked old oldMember stored

/-- Counter/cache updates preserve buffered links when the selected memberships stay fixed.
Witness: the unique-ref replacement theorem for each stored task's links.
-/
theorem State.StoredTaskLinks.putGroupNodeSameTasks {queue : State}
    (linked : queue.StoredTaskLinks) (unique : queue.GroupRefsUnique)
    (node : GroupNode) (member : node ∈ queue.groupNodes)
    (updated : GroupNode) (sameRef : updated.group.node.ref = node.group.node.ref)
    (sameTasks : updated.tasks = node.tasks)
    : (queue.putGroupNode updated).StoredTaskLinks := by
  intro task present stored
  exact (linked task present stored).putGroupNodeSameTasks unique node member updated
    sameRef sameTasks

/-- Group registration cannot recreate an absent contributor of a buffered task.
Witness: started-task registration and permanent contributor coverage protect every old
ref; the group-registration operation leaves the stored task map unchanged.
-/
theorem State.StoredTaskLinks.addGroups {queue : State} (linked : queue.StoredTaskLinks)
    (unique : queue.GroupRefsUnique) (registered : queue.TaskGroupsRegistered)
    (started : queue.StartedTasksRegistered) (groups : List Group)
    : (queue.addGroups groups).1.StoredTaskLinks := by
  intro node member stored
  rw [State.addGroups_taskNodes] at member
  exact (linked node member stored).addRegisteredGroups unique
    (fun _ contributor => registered node.task (started node member) _ contributor) groups

/-- Task registration preserves all buffered memberships and adds only empty task nodes.
Witness: old-or-new node inversion and per-task preservation of existing links.
-/
theorem State.StoredTaskLinks.addTask {queue : State} (linked : queue.StoredTaskLinks)
    (unique : queue.GroupRefsUnique) (task : Task)
    : (queue.addTask task).StoredTaskLinks := by
  intro node member stored
  rcases queue.addTask_startedOldOrNew task member with old | new
  · exact (linked node old stored).addTask unique task
  · subst node
    cases stored

/-- Child-stream registration changes neither the producer's task nor its buffered value.
Witness: only child-stream refs are appended to the selected task node.
-/
theorem State.StoredTaskLinks.addStreams {queue : State} (linked : queue.StoredTaskLinks)
    (streams : List Stream) (producer : Option Occurrence)
    : (queue.addStreams streams producer).1.StoredTaskLinks := by
  cases producer with
  | none => exact linked
  | some occurrence =>
      simp only [State.addStreams]
      split
      · exact linked
      · rename_i node found
        apply linked.putTaskNode
        exact linked node (List.mem_of_find?_eq_some found)

/-- Integrating newly generated work preserves buffered links to every surviving owner.
Witness: protected group registration, empty-node task integration, and child-stream links.
Permanent registry coverage, not live-owner existence, protects earlier contributors.
-/
theorem State.StoredTaskLinks.maybeIntegrateWork {queue : State}
    (linked : queue.StoredTaskLinks) (unique : queue.GroupRefsUnique)
    (registered : queue.TaskGroupsRegistered) (started : queue.StartedTasksRegistered)
    (work : Work) (producer : Option Occurrence := none)
    : (queue.maybeIntegrateWork work producer).1.StoredTaskLinks := by
  have loop (tasks : List Task) (current : State) (prior : current.StoredTaskLinks)
      (refs : current.GroupRefsUnique)
      : (tasks.foldl State.addTask current).StoredTaskLinks := by
    induction tasks generalizing current with
    | nil => exact prior
    | cons task rest ih => exact ih _ (prior.addTask refs task) (refs.addTask task)
  exact (loop work.tasks _ (linked.addGroups unique registered started work.groups)
    (unique.addGroups work.groups)).addStreams work.streams producer

-----------------------------------------------------------------------------------------
-- Successful storage and the single-pass contributor fold
-----------------------------------------------------------------------------------------

/-- The actual single-pass success fold preserves buffered memberships.
Witness: retain unique group refs alongside links across counter updates and complete
flushes. This invariant needs no successful-settlement count or owner-health premise.
-/
theorem State.StoredTaskLinks.successGroupFold {queue : State}
    (linked : queue.StoredTaskLinks) (unique : queue.GroupRefsUnique)
    (groups : List Execution.DeliveryNode) (events : List WorkQueueEvent)
    (released : NewWork)
    : (groups.foldl successGroupStep (queue, events, released)).1.StoredTaskLinks := by
  induction groups generalizing queue events released with
  | nil => exact linked
  | cons group rest ih =>
      simp only [List.foldl_cons, successGroupStep]
      split
      · exact ih linked unique _ _
      · rename_i node found
        have updated := linked.putGroupNodeSameTasks unique node
          (List.mem_of_find?_eq_some found) { node with pending := node.pending - 1 } rfl rfl
        split
        · exact ih (updated.finishGroupSuccess _)
            ((unique.putGroupNode _).finishGroupSuccess _) _ _
        · exact ih updated (unique.putGroupNode _) _ _

/-- The successful handler's drain-entry state inherits buffered links from fresh storage.
Witness: unsettled memberships justify storing the new value; protected child integration,
the contributor fold, and activation preserve the links before recursive draining begins.
-/
theorem State.StoredTaskLinks.taskSuccess_release {queue : State} {work settled}
    (linked : queue.StoredTaskLinks) (accounted : queue.PendingAccounting work settled)
    (occurrence : Occurrence) (result : TaskResult) (node : TaskNode)
    (found : queue.taskNode? occurrence = some node) (fresh : occurrence ∉ settled)
    : let stored := queue.putTaskNode { node with value := some result.value }
      let integrated := (stored.maybeIntegrateWork result.work (some occurrence)).1
      let released := node.task.groups.foldl successGroupStep (integrated, [], {})
      (released.1.startNewWork released.2.2).StoredTaskLinks := by
  have known := State.taskNode?_some found
  have registered := accounted.started node known.1
  have taskLinks := accounted.links node.task registered (known.2.symm ▸ fresh)
  have installed := linked.putTaskNode { node with value := some result.value }
    (fun _ => taskLinks)
  have started := accounted.started.putTaskNode
    { node with value := some result.value } registered
  have integrated := installed.maybeIntegrateWork accounted.refs accounted.taskGroups
    started result.work (some occurrence)
  have refs : (queue.putTaskNode { node with value := some result.value }).GroupRefsUnique :=
    accounted.refs
  have flushed := integrated.successGroupFold
    (refs.maybeIntegrateWork result.work (some occurrence)) node.task.groups [] {}
  exact flushed.startNewWork _

/-- Fresh successful settlement preserves buffered links through its full handler.
Witness: the release-state theorem followed by recursive draining; ignored successes
remove the settled task without installing a value.
-/
theorem State.StoredTaskLinks.taskSuccess {queue : State} {work settled}
    (linked : queue.StoredTaskLinks) (accounted : queue.PendingAccounting work settled)
    (occurrence : Occurrence) (result : TaskResult) (fresh : occurrence ∉ settled)
    : (queue.taskSuccess occurrence result).1.StoredTaskLinks := by
  cases found : queue.taskNode? occurrence with
  | none => simpa only [State.taskSuccess, found] using linked
  | some node =>
      have released := linked.taskSuccess_release accounted occurrence result node found fresh
      rw [queue.taskSuccess_eq occurrence result node found]
      split
      · exact linked.removeTask occurrence
      · exact released.drainReadyGroups

-----------------------------------------------------------------------------------------
-- Failed task processing and stream inputs do not install buffered object values
-----------------------------------------------------------------------------------------

/-- Failure processing preserves every surviving buffered membership.
Witness: removal drops the failed occurrence; each owner either retires or keeps its
memberships while accumulating a cached error. This also covers ignored late failures.
-/
theorem State.StoredTaskLinks.taskFailure {queue : State} (linked : queue.StoredTaskLinks)
    (unique : queue.GroupRefsUnique) (occurrence : Occurrence) (errors : Nat)
    : (queue.taskFailure occurrence errors).1.StoredTaskLinks := by
  let step (acc : State × List WorkQueueEvent) (group : Execution.DeliveryNode)
      : State × List WorkQueueEvent :=
    match acc.1.groupNode? group.ref with
    | none => acc
    | some node =>
        if acc.1.rootGroups.contains group.ref then
          (acc.1.removeGroup node.group.node.ref,
            acc.2 ++ [.groupFailure node.group.node errors])
        else
          (acc.1.putGroupNode
            { node with
              pending := node.pending - 1
              failure := some (node.failure.getD 0 + errors) }, acc.2)
  have loop (groups : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent)
      (prior : acc.1.StoredTaskLinks) (refs : acc.1.GroupRefsUnique)
      : (groups.foldl step acc).1.StoredTaskLinks := by
    induction groups generalizing acc with
    | nil => exact prior
    | cons group rest ih =>
        apply ih
        · unfold step
          split
          · exact prior
          · rename_i node found
            split
            · exact prior.removeGroup _
            · exact prior.putGroupNodeSameTasks refs node (List.mem_of_find?_eq_some found)
                _ rfl rfl
        · unfold step
          split
          · exact refs
          · split
            · exact refs.removeGroup _
            · exact refs.putGroupNode _
  unfold State.taskFailure
  split
  · exact linked
  · split
    · exact linked.removeTask occurrence
    · exact loop _ _ (linked.removeTask occurrence) (unique.removeTask occurrence)

/-- Sequential stream-item integration preserves buffered object memberships.
Witness: carry permanent registration and unique refs through each actual integration
state; pruning, activation, and the final drain preserve the buffered-only links.
-/
theorem State.StoredTaskLinks.streamItems {queue : State}
    (linked : queue.StoredTaskLinks) (unique : queue.GroupRefsUnique)
    (live : queue.LiveGroupsRegistered) (covered : queue.TaskGroupsRegistered)
    (started : queue.StartedTasksRegistered) (stream : Execution.DeliveryNode)
    (items : List StreamItem)
    (allCovered
      : ∀ item ∈ items,
        ∀ task ∈ item.work.tasks,
        ∀ ref ∈ task.groups.map Execution.DeliveryNode.ref,
          ∃ group ∈ item.work.groups, group.node.ref = ref)
    : (queue.streamItems stream items).1.StoredTaskLinks := by
  let step (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue) (item : StreamItem) :=
    let (current, groups, streams, values) := acc
    let (integrated, newWork) := current.maybeIntegrateWork item.work
    let (pruned, nonempty) := integrated.pruneEmptyGroups newWork.newGroups
    (pruned.startNewWork { newWork with newGroups := nonempty },
      groups ++ nonempty, streams ++ newWork.newStreams, values ++ [item.value])
  let invariant (current : State) :=
    current.StoredTaskLinks ∧ current.GroupRefsUnique ∧ current.LiveGroupsRegistered
      ∧ current.TaskGroupsRegistered ∧ current.StartedTasksRegistered
  have preserve (acc) (item : StreamItem) (member : item ∈ items)
      (prior : invariant acc.1) : invariant (step acc item).1 := by
    obtain ⟨current, groups, streams, values⟩ := acc
    have links := prior.1.maybeIntegrateWork prior.2.1 prior.2.2.2.1 prior.2.2.2.2 item.work
    have refs := prior.2.1.maybeIntegrateWork item.work none
    have registration := current.maybeIntegrateWork_registration prior.2.2.1 prior.2.2.2.1
      item.work (allCovered item member)
    have pruned := State.pruneEmptyGroups_registration registration.1 registration.2.1
      (current.maybeIntegrateWork item.work).2.newGroups
    have activated := State.startNewWork_registration pruned.1 pruned.2.1
      { (current.maybeIntegrateWork item.work).2 with
        newGroups := ((current.maybeIntegrateWork item.work).1.pruneEmptyGroups
          (current.maybeIntegrateWork item.work).2.newGroups).2 }
    have registered := prior.2.2.2.2.maybeIntegrateWork item.work none
    exact ⟨(links.pruneEmptyGroups _).startNewWork _,
      (refs.pruneEmptyGroups _).startNewWork _, activated.1, activated.2,
      (registered.pruneEmptyGroups _).startNewWork _⟩
  have loop (more : List StreamItem) (included : more.Subset items) (acc)
      (prior : invariant acc.1) : invariant (more.foldl step acc).1 := by
    induction more generalizing acc with
    | nil => exact prior
    | cons item rest ih =>
        exact ih (fun _ member => included (List.mem_cons_of_mem _ member)) _
          (preserve acc item (included List.mem_cons_self) prior)
  unfold State.streamItems
  split
  · exact linked
  · exact (loop items (fun _ member => member) (queue, [], [], [])
      ⟨linked, unique, live, covered, started⟩).1.drainReadyGroups

-----------------------------------------------------------------------------------------
-- Event-level interface and initialization
-----------------------------------------------------------------------------------------

/-- A fresh matching source event preserves buffered links under internal queue accounting.
Witness: success converts unsettled memberships; failures only filter/update memberships;
stream arrivals use generated contributor coverage. No observable admission is assumed.
-/
theorem State.StoredTaskLinks.handleGraphEvent {queue : State} {work settled before}
    (linked : queue.StoredTaskLinks) (accounted : queue.PendingAccounting work settled)
    (included : settled.Subset (before.flatMap (fun event => event.identities.1)))
    (event : GraphEvent) (matching : event.MatchesWork work) (fresh : event.Fresh before)
    : (queue.handleGraphEvent event).1.StoredTaskLinks := by
  cases event with
  | taskSuccess occurrence result =>
      exact linked.taskSuccess accounted occurrence result
        (fun member =>
          fresh.2.2.1 occurrence (by simp [GraphEvent.identities]) (included member))
  | taskFailure occurrence errors =>
      exact linked.taskFailure accounted.refs occurrence errors
  | streamItems stream items =>
      exact linked.streamItems accounted.refs accounted.liveGroups accounted.taskGroups
        accounted.started stream items
        (fun _ member => matching.streamItem_childTasksCovered member)
  | streamSuccess stream =>
      dsimp only [State.handleGraphEvent, State.streamSuccess]
      split <;> exact linked
  | streamFailure stream errors =>
      dsimp only [State.handleGraphEvent, State.streamFailure]
      split <;> exact linked

/-- Initialization satisfies buffered links because it installs no resolved object value.
Witness: the unconditional initial stored-value theorem with the false payload predicate.
-/
theorem createWorkQueue_storedTaskLinks (work : Work)
    : (State.initialize work).StoredTaskLinks := by
  intro node member stored
  have empty := createWorkQueue_storedValues work (fun _ _ => False)
  cases value : node.value with
  | none => simp [value] at stored
  | some payload => exact (empty node member payload value).elim

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
