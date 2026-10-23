import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CachedFailureCleanup
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupHealth
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PendingBoundPreservation

/-! Healthy registered-task accounting through the full recursive release-time drain. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (ExecutionGroupValue)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Which node properties survive release and activation?
-----------------------------------------------------------------------------------------

/-- Pruning preserves any property of each surviving node.
Witness: induction over the pruning budget; its only node mutation is filtering.
-/
theorem State.pruneEmptyGroups_nodeProperty (predicate : GroupNode → Prop)
    {queue : State} (valid : ∀ node ∈ queue.groupNodes, predicate node)
    (groups : List Execution.DeliveryNode)
    : ∀ node ∈ (queue.pruneEmptyGroups groups).1.groupNodes, predicate node := by
  have loop (fuel : Nat) (current : State) (todo kept : List Execution.DeliveryNode)
      (currentValid : ∀ node ∈ current.groupNodes, predicate node)
      : ∀ node ∈ (State.pruneEmptyGroups.go fuel current todo kept).1.groupNodes,
          predicate node := by
    induction fuel generalizing current todo kept with
    | zero => exact currentValid
    | succ fuel ih =>
        cases todo with
        | nil => exact currentValid
        | cons group rest =>
            unfold State.pruneEmptyGroups.go
            split
            · exact ih _ _ _ currentValid
            · split
              · exact ih _ _ _ (fun node member =>
                  currentValid node (List.mem_filter.mp member).1)
              · exact ih _ _ _ currentValid
  exact loop _ queue groups [] valid

/-- Successful release preserves node properties stable under membership removal.
Witness: the task-flush fold, closing-ref filter, and descendant-pruning induction.
-/
theorem State.finishGroupSuccess_nodeProperty (predicate : GroupNode → Prop)
    (remove
      : ∀ node occurrence,
          predicate node
          → predicate { node with tasks := node.tasks.filter (· != occurrence) })
    {queue : State} (valid : ∀ node ∈ queue.groupNodes, predicate node)
    (group : GroupNode)
    : ∀ node ∈ (queue.finishGroupSuccess group).1.groupNodes, predicate node := by
  let step (acc : State × List ExecutionGroupValue × NodeRefs) (occurrence : Occurrence) :=
    let (current, values, streams) := acc
    match current.taskNode? occurrence with
    | none => (current, values, streams)
    | some taskNode =>
        let values := match taskNode.value with
          | none => values
          | some value => values ++ [value]
        (current.removeTask occurrence, values, streams ++ taskNode.childStreams)
  have foldValid (tasks : List Occurrence) :
      ∀ acc : State × List ExecutionGroupValue × NodeRefs,
        (∀ node ∈ acc.1.groupNodes, predicate node)
          → ∀ node ∈ (tasks.foldl step acc).1.groupNodes, predicate node := by
    induction tasks with
    | nil => intro acc currentValid; exact currentValid
    | cons occurrence rest ih =>
        intro acc currentValid
        apply ih
        obtain ⟨current, values, streams⟩ := acc
        dsimp only [step]
        split
        · exact currentValid
        · intro node member
          obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
          exact remove old occurrence (currentValid old oldMember)
  let flushed := (group.tasks.foldl step (queue, [], [])).1
  have flushedValid : ∀ node ∈ flushed.groupNodes, predicate node :=
    foldValid group.tasks (queue, [], []) valid
  let current : State :=
    { flushed with
      groupNodes := flushed.groupNodes.filter
        (fun node => node.group.node.ref != group.group.node.ref)
      rootGroups := flushed.rootGroups.filter (· != group.group.node.ref) }
  have currentValid : ∀ node ∈ current.groupNodes, predicate node :=
    fun node member => flushedValid node (List.mem_filter.mp member).1
  exact State.pruneEmptyGroups_nodeProperty predicate currentValid _

/-- Filtering memberships cannot increase the number of unsettled tasks.
Witness: filtered-list sublist monotonicity, without uniqueness or settlement premises.
-/
theorem unsettledCount_filter_le (tasks settled : List Occurrence)
    (selected : Occurrence → Bool)
    : unsettledCount (tasks.filter selected) settled ≤ unsettledCount tasks settled := by
  classical
  unfold unsettledCount
  have sub : (tasks.filter selected).Sublist tasks := List.filter_sublist
  exact (sub.filter _).length_le

-----------------------------------------------------------------------------------------
-- Healthy owners survive every recursive drain step
-----------------------------------------------------------------------------------------

/-- The full drain retains every unsettled task's healthy registered owners.
Witness: zero-counter lower bounds justify successful flushes; cached-failure provenance
and canonical child links justify failed cleanup. The induction permits transient failed
roots and needs neither exact pending totals nor health of every active group.
These are internal state premises, not new source or scheduler-contract assumptions.
-/
theorem State.HealthyRegisteredTaskAccounting.drainReadyGroups
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    {parents : Nat → NodeRefs}
    (accounted : queue.HealthyRegisteredTaskAccounting work settled failed)
    (bounded : queue.PendingBound (fun _ => True) settled)
    (unique : queue.GroupRefsUnique)
    (supported : queue.CachedFailuresSupported work failed)
    (tasksMatch : queue.RegisteredTasksMatch work)
    (generated : ExecutedWork work)
    (links : queue.ChildLinksCanonical parents)
    (matching : queue.GroupNodesMatchWork work)
    (canonical
      : ∀ group dependencies,
          GroupRecordAt work group dependencies → dependencies = parents group.ref)
    (registered : queue.StartedTasksRegistered) (sound : queue.GroupMembershipSound)
    (available : List (Occurrence × Nat) := [])
    (recorded
      : ∀ occurrence errors, (occurrence, errors) ∈ available → occurrence ∈ failed := by
        intro occurrence errors member; cases member)
    : (queue.drainReadyGroups available).1.HealthyRegisteredTaskAccounting work settled
        failed := by
  let invariant (current : State) :=
    current.HealthyRegisteredTaskAccounting work settled failed ∧
      current.PendingBound (fun _ => True) settled ∧ current.GroupRefsUnique ∧
      current.CachedFailuresSupported work failed ∧ current.RegisteredTasksMatch work ∧
      current.ChildLinksCanonical parents ∧ current.GroupNodesMatchWork work ∧
      current.StartedTasksRegistered ∧ current.GroupMembershipSound
  have initial : invariant queue :=
    ⟨accounted, bounded, unique, supported, tasksMatch, links, matching, registered, sound⟩
  have final := State.drainReadyGroups_preserves invariant
    (available := available) (valid := initial) (by
    intro current node valid member active zero
    have all := valid.2.1.allSettled member trivial zero
    have released := valid.1.finishSettledGroupSuccess valid.2.2.1 node member all
    have releasedBound := valid.2.1.finishGroupSuccess node all
    have releasedUnique := valid.2.2.1.finishGroupSuccess node
    have releasedSupport := valid.2.2.2.1.finishGroupSuccess node
    have releasedTasks := valid.2.2.2.2.1.finishGroupSuccess node
    have releasedLinks := valid.2.2.2.2.2.1.finishGroupSuccess node
    have releasedMatch := valid.2.2.2.2.2.2.1.finishGroupSuccess node
    have releasedRegistered := valid.2.2.2.2.2.2.2.1.finishGroupSuccess node
    have releasedSound := valid.2.2.2.2.2.2.2.2.finishGroupSuccess node
    exact ⟨released.startNewWork releasedSupport releasedRegistered releasedTasks releasedSound
        generated releasedLinks releasedMatch canonical _ available recorded,
      releasedBound.startNewWork _ available, releasedUnique.startNewWork _ available,
      releasedSupport.startNewWork_available releasedRegistered releasedTasks _ available recorded,
      releasedTasks.startNewWork _ available, releasedLinks.startNewWork _ available,
      releasedMatch.startNewWork _ available,
      releasedRegistered.startNewWork _ available, releasedSound.startNewWork _ available⟩)
  exact final.1

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
