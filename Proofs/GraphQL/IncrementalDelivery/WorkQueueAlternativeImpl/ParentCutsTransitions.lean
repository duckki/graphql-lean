import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ParentCutsRegistration
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RemovalCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamPreparation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.DrainNormalForm
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.IntegrationPathCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureDescendants

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

theorem State.LiveParentsUncancelled.maybeIntegrateWork {queue : State} {parents}
    (safe : queue.LiveParentsUncancelled) (live : queue.LiveGroupsRegistered)
    (closed : queue.ParentRegistryClosed parents)
    (fields : queue.GroupParentsCanonical parents) (work : Work)
    (canonical : ∀ group ∈ work.groups, group.parent = (parents group.node.ref).head?)
    (ordered : ParentsBefore [] work.groups) (parentTask : Option Occurrence := none)
    : (queue.maybeIntegrateWork work parentTask).1.LiveParentsUncancelled := by
  have loop (tasks : List Task) (current : State) (safe : current.LiveParentsUncancelled)
      : (tasks.foldl State.addTask current).LiveParentsUncancelled := by
    induction tasks generalizing current with
    | nil => exact safe
    | cons task rest ih => exact ih _ (safe.addTask task)
  exact (loop work.tasks _
          (safe.addGroups live closed fields work.groups canonical ordered))
  |>.addStreams work.streams parentTask

theorem State.LiveParentsUncancelled.pruneEmptyGroups {queue : State}
    (safe : queue.LiveParentsUncancelled) (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.LiveParentsUncancelled :=
  safe.of_subset (queue.pruneEmptyGroups_groupNodes_sublist groups).subset
    (queue.pruneEmptyGroups_cancelledGroups groups)

theorem State.LiveParentsUncancelled.startNewWork {queue : State}
    (safe : queue.LiveParentsUncancelled) (released : NewWork)
    : (queue.startNewWork released).LiveParentsUncancelled :=
  safe.of_subset
    (by rw [(queue.startNewWork_groupCore released).1]; exact List.Subset.refl _)
    (queue.startNewWork_cancelledGroups released)

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
    groupNodes := flushed.groupNodes.filter (fun node => node.group.node.ref != group.group.node.ref)
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

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
