import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.DrainValueCoverage

/-! Buffered values retain memberships through activation and mixed recursive draining. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (ExecutionGroupValue)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Buffered memberships are weaker than requiring links for every started task
-----------------------------------------------------------------------------------------

/-- Every value-bearing live task in `queue` is linked to each surviving contributor.
This internal proof invariant covers latent as well as active groups. It makes no claim
that an absent contributor is cancelled or that an unsettled task has produced a value.
-/
def State.StoredTaskLinks (queue : State) : Prop :=
  ∀ node ∈ queue.taskNodes,
    node.value.isSome = true
    → queue.TaskLinkedOn node.task.occurrence
        (node.task.groups.map Execution.DeliveryNode.ref)

/-- Full live-task links imply the buffered-only obligation.
Witness: ignore the stored-value restriction while reusing each task's memberships.
-/
theorem State.StoredTaskLinks.of_all {queue : State}
    (linked
      : ∀ node ∈ queue.taskNodes,
          queue.TaskLinkedOn node.task.occurrence
            (node.task.groups.map Execution.DeliveryNode.ref))
    : queue.StoredTaskLinks :=
  fun node member _ => linked node member

/-- Removing an occurrence preserves every remaining buffered task's memberships.
Witness: the task filter excludes that occurrence; all other task links survive removal.
-/
theorem State.StoredTaskLinks.removeTask {queue : State} (linked : queue.StoredTaskLinks)
    (occurrence : Occurrence)
    : (queue.removeTask occurrence).StoredTaskLinks := by
  intro node member stored
  obtain ⟨old, different⟩ := State.removeTask_node member
  exact (linked node old stored).removeOtherTask occurrence different

/-- Failed-group cleanup retains the memberships of every surviving buffered value.
Witness: both live maps are filtered, and surviving groups keep their task lists.
-/
theorem State.StoredTaskLinks.removeGroup {queue : State} (linked : queue.StoredTaskLinks)
    (ref : NodeRef)
    : (queue.removeGroup ref).StoredTaskLinks := by
  intro node member stored
  exact (linked node (List.mem_filter.mp member).1 stored).removeGroup ref

/-- Empty-group pruning changes no buffered node and only removes contributor records.
Witness: the exact task-map equation and existing per-task membership preservation.
-/
theorem State.StoredTaskLinks.pruneEmptyGroups {queue : State}
    (linked : queue.StoredTaskLinks) (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.StoredTaskLinks := by
  intro node member stored
  rw [State.pruneEmptyGroups_taskNodes] at member
  exact (linked node member stored).pruneEmptyGroups groups

-----------------------------------------------------------------------------------------
-- Activation creates no new value-bearing task
-----------------------------------------------------------------------------------------

/-- Starting a task preserves buffered memberships, even for raw duplicate descriptors.
Witness: an existing buffered node keeps its links; a newly appended empty node cannot
satisfy the stored-value premise.
-/
theorem State.StoredTaskLinks.startTask {queue : State} (linked : queue.StoredTaskLinks)
    (occurrence : Occurrence)
    : (queue.startTask occurrence).StoredTaskLinks := by
  have old (node : TaskNode) (member : node ∈ queue.taskNodes) (stored : node.value.isSome = true)
      : (queue.startTask occurrence).TaskLinkedOn node.task.occurrence
          (node.task.groups.map Execution.DeliveryNode.ref) :=
    (linked node member stored).startTask occurrence
  intro node member stored
  unfold State.startTask at member
  split at member
  · exact old node member stored
  · split at member
    · exact old node member stored
    · rcases List.mem_append.mp member with prior | added
      · exact old node prior stored
      · obtain rfl := List.mem_singleton.mp added
        cases stored

/-- Group activation preserves buffered memberships through every task start.
Witness: induction over the group's actual membership list, including duplicate entries.
-/
theorem State.StoredTaskLinks.startGroup {queue : State} (linked : queue.StoredTaskLinks)
    (ref : NodeRef)
    : (queue.startGroup ref).StoredTaskLinks := by
  unfold State.startGroup
  split
  · exact linked
  · split
    · exact linked
    · have loop (tasks : List Occurrence) (current : State) (prior : current.StoredTaskLinks)
          : (tasks.foldl State.startTask current).StoredTaskLinks := by
        induction tasks generalizing current with
        | nil => exact prior
        | cons task rest ih => exact ih _ (prior.startTask task)
      exact loop _ queue linked

/-- Starting a stream leaves both membership maps unchanged. Witness: branch reduction.
-/
theorem State.StoredTaskLinks.startStream {queue : State} (linked : queue.StoredTaskLinks)
    (ref : NodeRef)
    : (queue.startStream ref).StoredTaskLinks := by
  unfold State.startStream
  split <;> exact linked

/-- Released-work activation preserves buffered links without any release-link callback.
Witness: new roots do not change group/task maps, and both activation folds preserve the
buffered-only invariant. No obligation is imposed on newly started empty nodes.
-/
theorem State.StoredTaskLinks.startNewWork {queue : State}
    (linked : queue.StoredTaskLinks) (released : NewWork)
    : (queue.startNewWork released).StoredTaskLinks := by
  have loop (step : State → Nat → State)
      (preserves : ∀ current ref, current.StoredTaskLinks → (step current ref).StoredTaskLinks)
      (refs : NodeRefs) (current : State) (prior : current.StoredTaskLinks)
      : (refs.foldl step current).StoredTaskLinks := by
    induction refs generalizing current with
    | nil => exact prior
    | cons ref rest ih => exact ih _ (preserves _ _ prior)
  unfold State.startNewWork
  apply loop State.startStream (fun _ ref prior => prior.startStream ref)
  exact loop State.startGroup (fun _ ref prior => prior.startGroup ref) _ _ linked

-----------------------------------------------------------------------------------------
-- Successful flushing and failed cleanup preserve the same buffered-link invariant
-----------------------------------------------------------------------------------------

/-- A successful flush preserves all surviving buffered task links.
Witness: each selected occurrence is removed globally; the closing group and empty shells
are then filtered. This proof needs neither settled-task counts nor output admission.
-/
theorem State.StoredTaskLinks.finishGroupSuccess {queue : State}
    (linked : queue.StoredTaskLinks) (group : GroupNode)
    : (queue.finishGroupSuccess group).1.StoredTaskLinks := by
  have loop (tasks : List Occurrence) (acc : State × List ExecutionGroupValue × NodeRefs)
      (prior : acc.1.StoredTaskLinks)
      : (tasks.foldl flushGroupTask acc).1.StoredTaskLinks := by
    induction tasks generalizing acc with
    | nil => exact prior
    | cons task rest ih =>
        apply ih
        unfold flushGroupTask
        split
        · exact prior
        · exact prior.removeTask task
  let flushed := (group.tasks.foldl flushGroupTask (queue, [], [])).1
  have flushedLinks : flushed.StoredTaskLinks := loop group.tasks (queue, [], []) linked
  let current :=
    { flushed with
      groupNodes := flushed.groupNodes.filter
        (fun node => node.group.node.ref != group.group.node.ref)
      rootGroups := flushed.rootGroups.filter (· != group.group.node.ref) }
  have currentLinks : current.StoredTaskLinks := by
    intro node member stored owner live contributes
    exact flushedLinks node member stored owner (List.mem_filter.mp live).1 contributes
  exact currentLinks.pruneEmptyGroups _

/-- Every bounded mixed drain prefix retains buffered links from its input state.
Witness: induction over actual cached failures and successful flush/activation steps.
Later coverage can therefore use the actual closure boundary without assuming its links.
-/
theorem State.StoredTaskLinks.drainReadyGroups_go {queue : State}
    (linked : queue.StoredTaskLinks) (fuel : Nat)
    : (State.drainReadyGroups.go fuel queue).1.StoredTaskLinks := by
  induction fuel generalizing queue with
  | zero => exact linked
  | succ fuel ih =>
      unfold State.drainReadyGroups.go
      dsimp only
      split
      · exact linked
      · rename_i group selected
        cases cached : group.failure with
        | none => exact ih ((linked.finishGroupSuccess group).startNewWork _)
        | some errors => exact ih (linked.removeGroup group.group.node.ref)

/-- The full implementation drain preserves buffered memberships.
Witness: specialize the bounded-prefix induction to its live-node budget.
-/
theorem State.StoredTaskLinks.drainReadyGroups {queue : State}
    (linked : queue.StoredTaskLinks)
    : queue.drainReadyGroups.1.StoredTaskLinks :=
  linked.drainReadyGroups_go queue.groupNodes.length

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
