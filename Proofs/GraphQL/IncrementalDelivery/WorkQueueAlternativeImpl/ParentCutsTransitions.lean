import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ParentCutsRegistration
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RemovalCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamPreparation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.DrainNormalForm
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.IntegrationPathCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureDescendants
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ParentLinkUpdates

/-! Live-parent cancellation safety across accounting updates and failure removal. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (ExecutionGroupValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Accounting updates and successful retirement preserve parent safety
-----------------------------------------------------------------------------------------

theorem State.LiveParentsUncancelled.of_subset {queue next : State}
    (safe : queue.LiveParentsUncancelled)
    (nodes : next.groupNodes.Subset queue.groupNodes)
    (cancelled : next.cancelledGroups = queue.cancelledGroups)
    : next.LiveParentsUncancelled := by
  intro node member parent same
  rw [cancelled]
  exact safe node (nodes member) parent same

theorem State.LiveParentsUncancelled.removeTask {queue : State}
    (safe : queue.LiveParentsUncancelled) (occurrence : Occurrence)
    : (queue.removeTask occurrence).LiveParentsUncancelled :=
  safe.map _ (by intro node; rfl)

theorem State.LiveParentsUncancelled.addTask {queue : State}
    (safe : queue.LiveParentsUncancelled) (task : Task)
    : (queue.addTask task).LiveParentsUncancelled := by
  let step (current : State) (group : Execution.DeliveryNode) : State :=
    match current.groupNode? group.ref with
    | none => current
    | some node =>
        if node.tasks.contains task.occurrence then current
        else current.putGroupNode
          { node with tasks := node.tasks ++ [task.occurrence], pending := node.pending + 1 }
  have loop (more : List Execution.DeliveryNode) (current : State)
      (safe : current.LiveParentsUncancelled)
      : (more.foldl step current).LiveParentsUncancelled := by
    induction more generalizing current with
    | nil => exact safe
    | cons group rest ih =>
        apply ih
        unfold step
        split
        · exact safe
        · rename_i node found
          split
          · exact safe
          · exact safe.putGroupNode _ (safe node (List.mem_of_find?_eq_some found))
  let current := task.groups.foldl step { queue with tasks := queue.tasks ++ [task] }
  have registered := loop task.groups { queue with tasks := queue.tasks ++ [task] } safe
  change (if task.groups.any (fun group => current.rootGroups.contains group.ref)
      && (current.taskNode? task.occurrence).isNone then
      { current with taskNodes := current.taskNodes ++ [{ task }] }
    else current).LiveParentsUncancelled
  split <;> exact registered

theorem State.LiveParentsUncancelled.addStreams {queue : State}
    (safe : queue.LiveParentsUncancelled) (streams : List Stream)
    (parentTask : Option Occurrence)
    : (queue.addStreams streams parentTask).1.LiveParentsUncancelled := by
  unfold State.addStreams
  split
  · exact safe
  · dsimp only
    split <;> exact safe

theorem State.LiveParentsUncancelled.maybeIntegrateWork {queue : State} {source parents}
    (safe : queue.LiveParentsUncancelled) (live : queue.LiveGroupsRegistered)
    (closed : queue.ParentRegistryClosed parents)
    (fields : queue.GroupParentsCanonical parents) (work : Work)
    (canonical : ∀ group ∈ work.groups, group.parent = (parents group.node.ref).head?)
    (cancelled : queue.CancellationsRetired) (generated : ExecutedWork source)
    (known
      : ∀ group ∈ work.groups,
          ∃ dependencies, GroupRecordAt source group.node dependencies)
    (ancestry
      : ∀ node dependencies,
          GroupRecordAt source node dependencies → dependencies = parents node.ref)
    (covered : work.ParentsCovered queue.registeredGroups)
    (parentTask : Option Occurrence := none)
    : (queue.maybeIntegrateWork work parentTask).1.LiveParentsUncancelled := by
  have loop (tasks : List Task) (current : State) (safe : current.LiveParentsUncancelled)
      : (tasks.foldl State.addTask current).LiveParentsUncancelled := by
    induction tasks generalizing current with
    | nil => exact safe
    | cons task rest ih => exact ih _ (safe.addTask task)
  exact (loop work.tasks _
          (safe.addGroups live closed fields cancelled work.groups generated known
            canonical ancestry covered))
  |>.addStreams work.streams parentTask

theorem State.LiveParentsUncancelled.pruneEmptyGroups {queue : State}
    (safe : queue.LiveParentsUncancelled) (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.LiveParentsUncancelled :=
  safe.of_subset (queue.pruneEmptyGroups_groupNodes_sublist groups).subset
    (queue.pruneEmptyGroups_cancelledGroups groups)

theorem State.LiveParentsUncancelled.finishGroupSuccess {queue : State}
    (safe : queue.LiveParentsUncancelled) (group : GroupNode)
    : (queue.finishGroupSuccess group).1.LiveParentsUncancelled := by
  have flush (tasks : List Occurrence) (acc : State × List ExecutionGroupValue × NodeRefs)
      (safe : acc.1.LiveParentsUncancelled)
      : (tasks.foldl flushGroupTask acc).1.LiveParentsUncancelled := by
    induction tasks generalizing acc with
    | nil => exact safe
    | cons task rest ih =>
        apply ih
        simp only [flushGroupTask]
        split
        · exact safe
        · exact safe.removeTask task
  let flushed := (group.tasks.foldl flushGroupTask (queue, [], [])).1
  have after : flushed.LiveParentsUncancelled := flush group.tasks (queue, [], []) safe
  let filtered : State := { flushed with
    groupNodes := flushed.groupNodes.filter
      (fun node => node.group.node.ref != group.group.node.ref)
    rootGroups := flushed.rootGroups.filter (· != group.group.node.ref) }
  have kept : filtered.LiveParentsUncancelled := after.of_subset List.filter_sublist.subset rfl
  exact kept.pruneEmptyGroups _

-----------------------------------------------------------------------------------------
-- Failure removal covers a live child whenever it collects that child's parent
-----------------------------------------------------------------------------------------

/-- Complete links and the finite forest prevent removal from leaving an orphan child. -/
theorem State.LiveParentsUncancelled.removeGroup {queue : State} {parents}
    (safe : queue.LiveParentsUncancelled) (unique : queue.GroupRefsUnique)
    (fields : queue.GroupParentsCanonical parents)
    (complete : queue.ParentLinksComplete parents) (forest : queue.RemovalForest parents)
    (root : Nat)
    : (queue.removeGroup root).LiveParentsUncancelled := by
  intro child kept parent parentEq cancelled
  have live := (List.mem_filter.mp kept).1
  rcases List.mem_append.mp cancelled with old | removed
  · exact safe child live parent parentEq old
  · have path : queue.LiveDescendant root parent :=
      (State.removeGroup_collect_mem_iff forest).mp removed
    obtain ⟨parentNode, found⟩ := path.target_present
    have parentKey := State.groupNode?_ref found
    have linked : child.group.node.ref ∈ parentNode.childGroups :=
      complete child live parentNode (List.mem_of_find?_eq_some found)
        (by rw [← fields child live, parentKey]; exact parentEq)
    have below : queue.LiveDescendant parent child.group.node.ref :=
      .child found linked (.self (unique.groupNode?_of_mem live))
    have gone := (State.removeGroup_liveDescendant_absent forest (path.trans below)).1
    have present := (unique.removeGroup root).groupNode?_of_mem kept
    simp [gone] at present

/-- Startup either preserves group structure or removes the entire failed subtree. -/
theorem State.LiveParentsUncancelled.startGroup {queue : State} {parents}
    (safe : queue.LiveParentsUncancelled) (unique : queue.GroupRefsUnique)
    (fields : queue.GroupParentsCanonical parents)
    (complete : queue.ParentLinksComplete parents) (forest : queue.RemovalForest parents)
    (ref : Nat) (available : List (Occurrence × Nat) := [])
    : (queue.startGroup ref available).1.LiveParentsUncancelled := by
  have included : (queue.cacheTaskFailures available).groupNodes.Subset queue.groupNodes := by
    rw [State.cacheTaskFailures_groupNodes]
    exact List.Subset.refl _
  have cached := safe.of_subset included (queue.cacheTaskFailures_cancelledGroups available)
  have tasks (more : List Occurrence) (current : State)
      (prior : current.LiveParentsUncancelled)
      : (more.foldl (fun current task => current.startTask task available)
          current).LiveParentsUncancelled := by
    induction more generalizing current with
    | nil => exact prior
    | cons task rest ih =>
        apply ih
        change (current.startTask task available).LiveParentsUncancelled
        unfold State.startTask
        split
        · exact prior
        · split <;> exact prior
  unfold State.startGroup
  dsimp only
  split
  · exact cached
  · split
    · exact tasks _ _ cached
    · exact cached.removeGroup (unique.cacheTaskFailures available)
        (fields.cacheTaskFailures available) (complete.of_subset included)
        (forest.of_subset included) _

/-- Complete parent links retain parent safety throughout the actual startup fold. -/
theorem State.LiveParentsUncancelled.startNewWork {queue : State} {parents}
    (safe : queue.LiveParentsUncancelled) (unique : queue.GroupRefsUnique)
    (fields : queue.GroupParentsCanonical parents)
    (complete : queue.ParentLinksComplete parents) (forest : queue.RemovalForest parents)
    (released : NewWork) (available : List (Occurrence × Nat) := [])
    : (queue.startNewWork released available).1.LiveParentsUncancelled := by
  have groups (more : NodeRefs) (acc : State × List GroupFailureEvent)
      (prior : acc.1.LiveParentsUncancelled) (included : acc.1.groupNodes.Sublist queue.groupNodes)
      : (more.foldl (fun (current, failures) ref =>
          let (next, queued) := current.startGroup ref available
          (next, failures ++ queued)) acc).1.LiveParentsUncancelled := by
    induction more generalizing acc with
    | nil => exact prior
    | cons ref rest ih =>
        have next := prior.startGroup (List.Nodup.sublist (included.map _) unique)
          (fun node member => fields node (included.subset member))
          (complete.of_subset included.subset) (forest.of_subset included.subset) ref available
        exact ih _ next ((acc.1.startGroup_groupNodes_sublist ref available).trans included)
  have streams (more : NodeRefs) (current : State) (prior : current.LiveParentsUncancelled)
      : (more.foldl State.startStream current).LiveParentsUncancelled := by
    induction more generalizing current with
    | nil => exact prior
    | cons ref rest ih =>
        apply ih
        unfold State.startStream
        split <;> exact prior
  exact streams _ _ (groups _ _ safe (List.Sublist.refl _))

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
