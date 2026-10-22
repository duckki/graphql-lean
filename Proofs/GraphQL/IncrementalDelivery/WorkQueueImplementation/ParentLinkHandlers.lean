import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ParentLinkUpdates
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PublishedMemberships
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamPreparation

/-! Concrete settlement handlers preserve complete live canonical parent links. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (
  ExecutionGroupValue StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Closure and recursive draining only remove records or change task memberships
-----------------------------------------------------------------------------------------

/-- Flushing shared tasks retains every live canonical parent edge.
Witness: each successful lookup removes memberships without changing the child topology.
-/
theorem State.ParentLinksComplete.flushGroupTasks {queue : State} {parents}
    (complete : queue.ParentLinksComplete parents) (tasks : List Occurrence)
    (values : List ExecutionGroupValue) (streams : NodeRefs)
    : (tasks.foldl flushGroupTask (queue, values, streams)).1.ParentLinksComplete
        parents := by
  induction tasks generalizing queue values streams with
  | nil => exact complete
  | cons occurrence rest ih =>
      simp only [List.foldl_cons, flushGroupTask]
      split
      · exact ih complete _ _
      · exact ih (complete.removeTask occurrence) _ _

/-- Successful closure keeps all canonical edges between surviving live groups.
Witness: flush task memberships, filter the closed group, then prune taskless shells.
-/
theorem State.ParentLinksComplete.finishGroupSuccess {queue : State} {parents}
    (complete : queue.ParentLinksComplete parents) (group : GroupNode)
    : (queue.finishGroupSuccess group).1.ParentLinksComplete parents := by
  have flushed := complete.flushGroupTasks group.tasks [] []
  let afterFlush := (group.tasks.foldl flushGroupTask (queue, [], [])).1
  let current : State :=
    { afterFlush with
      groupNodes := afterFlush.groupNodes.filter
        (fun node => node.group.node.ref != group.group.node.ref)
      rootGroups := afterFlush.rootGroups.filter (· != group.group.node.ref) }
  have filtered : current.ParentLinksComplete parents :=
    flushed.of_subset (fun _ member => (List.mem_filter.mp member).1)
  exact filtered.pruneEmptyGroups _

/-- Failed closure keeps canonical edges between survivors outside the removed subtree.
Witness: failure closure delegates to the checked record-filtering removal operation.
-/
theorem State.ParentLinksComplete.finishGroupFailure {queue : State} {parents}
    (complete : queue.ParentLinksComplete parents) (group : GroupNode) (errors : Nat)
    : (queue.finishGroupFailure group errors).1.ParentLinksComplete parents :=
  complete.removeGroup group.group.node.ref

/-- Failed tasks retain complete parent links through task update and owner removal. -/
theorem State.ParentLinksComplete.taskFailure {queue : State} {parents}
    (complete : queue.ParentLinksComplete parents)
    (occurrence : Occurrence) (errors : Nat)
    : (queue.taskFailure occurrence errors).1.ParentLinksComplete parents := by
  cases found : queue.taskNode? occurrence with
  | none => simpa only [State.taskFailure, found] using complete
  | some node =>
      rw [queue.taskFailure_eq occurrence errors node found]
      exact failureGroupFold_preserves (fun current => current.ParentLinksComplete parents)
        (fun _ ref prior => prior.removeGroup ref) _ _ _ complete

/-- Every bounded mixed drain preserves complete live canonical parent links.
Witness: both closure branches preserve completeness, as does child activation.
-/
theorem State.ParentLinksComplete.drainReadyGroups {queue : State} {parents}
    (complete : queue.ParentLinksComplete parents)
    (available : List (Occurrence × Nat) := [])
    : (queue.drainReadyGroups available).1.ParentLinksComplete parents :=
  State.drainReadyGroups_preserves (fun state => state.ParentLinksComplete parents)
    (available := available)
    (fun _ node prior _ _ _ => (prior.finishGroupSuccess node).startNewWork _ available)
    complete

-----------------------------------------------------------------------------------------
-- Object settlements integrate children, update counts, and close contributing groups
-----------------------------------------------------------------------------------------

/-- Successful task handling retains complete links after child integration and release.
Witness: canonical child registration establishes its new edges; unique-ref counter
updates, the original single-pass owner fold, and the final drain preserve them.
-/
theorem State.ParentLinksComplete.taskSuccess {queue : State} {parents}
    (complete : queue.ParentLinksComplete parents) (unique : queue.GroupRefsUnique)
    (registered : queue.LiveGroupsRegistered)
    (closed : queue.ParentRegistryClosed parents) (occurrence : Occurrence)
    (result : TaskResult)
    (canonical
      : ∀ group ∈ result.work.groups, group.parent = (parents group.node.ref).head?)
    (available : List (Occurrence × Nat) := [])
    : (queue.taskSuccess occurrence result available).1.ParentLinksComplete parents := by
  let property (current : State) := current.GroupRefsUnique ∧ current.ParentLinksComplete parents
  have step (acc : State × List WorkQueueEvent × NewWork) (group : Execution.DeliveryNode)
      (prior : property acc.1) : property (successGroupStep acc group).1 := by
    obtain ⟨current, events, released⟩ := acc
    dsimp only [successGroupStep]
    split
    · exact prior
    · rename_i node found
      have updated : property (current.putGroupNode { node with pending := node.pending - 1 }) :=
        ⟨prior.1.putGroupNode _,
          prior.2.putGroupNode prior.1 found _ rfl (List.Subset.refl _)⟩
      split
      · exact ⟨updated.1.finishGroupSuccess _, updated.2.finishGroupSuccess _⟩
      · exact updated
  have loop (groups : List Execution.DeliveryNode)
      (acc : State × List WorkQueueEvent × NewWork) (prior : property acc.1)
      : property (groups.foldl successGroupStep acc).1 := by
    induction groups generalizing acc with
    | nil => exact prior
    | cons group rest ih => exact ih _ (step acc group prior)
  cases found : queue.taskNode? occurrence with
  | none => simpa [State.taskSuccess, found] using complete
  | some node =>
      rw [queue.taskSuccess_eq occurrence result node found available]
      let stored := queue.putTaskNode { node with value := some result.value }
      have storedComplete : stored.ParentLinksComplete parents := complete
      have storedUnique : stored.GroupRefsUnique := unique
      have integrated := storedComplete.maybeIntegrateWork storedUnique registered closed
        result.work canonical (some occurrence)
      have folded := (loop node.task.groups (_, [], {})
        ⟨storedUnique.maybeIntegrateWork result.work (some occurrence), integrated⟩).2
      exact (folded.startNewWork _ available).drainReadyGroups available

-----------------------------------------------------------------------------------------
-- Stream items use the same registration invariant at each actual integration boundary
-----------------------------------------------------------------------------------------

/-- Integrating one matched stream item preserves complete canonical parent links.
Witness: register its child work, prune empty shells, then activate the surviving frontier.
-/
theorem State.ParentLinksComplete.integrateStreamItem {queue : State} {parents}
    (complete : queue.ParentLinksComplete parents) (unique : queue.GroupRefsUnique)
    (registered : queue.LiveGroupsRegistered)
    (closed : queue.ParentRegistryClosed parents) (item : StreamItem)
    (canonical
      : ∀ group ∈ item.work.groups, group.parent = (parents group.node.ref).head?)
    (available : List (Occurrence × Nat) := [])
    : (queue.integrateStreamItem item available).ParentLinksComplete parents :=
  ((complete.maybeIntegrateWork unique registered closed item.work
      canonical).pruneEmptyGroups
    _).startNewWork
    _ available

/-- A matched stream-item batch retains complete links at every item boundary and afterward.
Witness: thread permanent registration and ref uniqueness alongside completeness, using
the independent registry-preservation theorems before the final mixed drain.
-/
theorem State.ParentLinksComplete.streamItems {queue : State} {work parents}
    (complete : queue.ParentLinksComplete parents) (unique : queue.GroupRefsUnique)
    (_live : queue.LiveGroupsRegistered) (_tasks : queue.TaskGroupsRegistered)
    (frame : queue.RegistrationFrame work)
    (closed : queue.ParentRegistryClosed parents) (stream : Execution.DeliveryNode)
    (items : List StreamItem)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (available : List (Occurrence × Nat) := [])
    : (queue.streamItems stream items available).1.ParentLinksComplete parents := by
  let step := fun acc item => streamItemStep acc item available
  let property (current : State) := current.GroupRefsUnique ∧ current.RegistrationFrame work ∧ current.ParentRegistryClosed parents
    ∧ current.ParentLinksComplete parents
  have loop (more : List StreamItem) (included : more.Subset items)
      (acc : State × List Execution.DeliveryNode
        × List Execution.DeliveryNode × List StreamItemValue × List GroupFailureEvent)
      (prior : property acc.1) : property (more.foldl step acc).1 := by
    induction more generalizing acc with
    | nil => exact prior
    | cons item rest ih =>
        have member := included List.mem_cons_self
        have registry := prior.2.2.1.integrateStreamItem prior.2.1.live prior.2.1.tasks
          prior.2.1 matching member canonical available
        have covered := prior.2.2.2.integrateStreamItem prior.1 prior.2.1.live prior.2.2.1 item
          (fun _ group => matching.streamItem_childGroups_parentCanonical canonical member group)
          available
        have refs : (acc.1.integrateStreamItem item available).GroupRefsUnique :=
          ((prior.1.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _ available
        exact ih (fun _ inRest => included (List.mem_cons_of_mem _ inRest)) _
          ⟨refs, (prior.2.1.integrateStreamItem matching member available).1, registry, covered⟩
  unfold State.streamItems
  split
  · exact complete
  · exact (loop items (fun _ member => member) (queue, [], [], [], [])
      ⟨unique, frame, closed, complete⟩).2.2.2.drainReadyGroups available

/-- Every matched event preserves complete live canonical parent links.
Witness: the checked object/item handlers; stream termination only changes stream state.
No event-admission, output-correctness, or retirement premise is needed for this invariant.
-/
theorem State.ParentLinksComplete.handleGraphEvent {queue : State} {work parents}
    (complete : queue.ParentLinksComplete parents) (unique : queue.GroupRefsUnique)
    (live : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (frame : queue.RegistrationFrame work)
    (closed : queue.ParentRegistryClosed parents) (event : GraphEvent)
    (matching : event.MatchesWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (available : List (Occurrence × Nat) := [])
    : (queue.handleGraphEvent event available).1.ParentLinksComplete parents := by
  have cachedComplete : (queue.cacheTaskFailures available).ParentLinksComplete parents :=
    complete.of_subset (by rw [State.cacheTaskFailures_groupNodes]; exact List.Subset.refl _)
  have cachedUnique := unique.cacheTaskFailures available
  have cachedReg := queue.cacheTaskFailures_registration live tasks available
  have cachedClosed := closed.of_sameRegistry (queue.cacheTaskFailures_registeredGroups available)
  cases event with
  | taskSuccess occurrence result =>
      exact cachedComplete.taskSuccess cachedUnique cachedReg.1 cachedClosed occurrence result
        (fun _ member => matching.taskChildGroups_parentCanonical canonical member) available
  | taskFailure occurrence errors => exact cachedComplete.taskFailure occurrence errors
  | streamItems stream items =>
      exact cachedComplete.streamItems cachedUnique cachedReg.1 cachedReg.2
        (frame.cacheTaskFailures available) cachedClosed stream items matching canonical available
  | streamSuccess stream =>
      change State.ParentLinksComplete
        ((queue.cacheTaskFailures available).streamSuccess stream).1 parents
      unfold State.streamSuccess
      split <;> exact cachedComplete
  | streamFailure stream errors =>
      change State.ParentLinksComplete
        ((queue.cacheTaskFailures available).streamFailure stream errors).1 parents
      unfold State.streamFailure
      split <;> exact cachedComplete

  | groupFailure failure =>
      simp only [State.handleGraphEvent, State.groupFailure]
      split
      · exact cachedComplete
      · split <;> exact cachedComplete

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
