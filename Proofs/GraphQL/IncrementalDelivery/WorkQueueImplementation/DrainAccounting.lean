import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CachedFailureCleanup
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.HealthyRegistration

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
Witness: the task-flush fold, closing-key filter, and descendant-pruning induction.
-/
theorem State.finishGroupSuccess_nodeProperty (predicate : GroupNode → Prop)
    (remove
      : ∀ node occurrence,
          predicate node
          → predicate { node with tasks := node.tasks.filter (· != occurrence) })
    {queue : State} (valid : ∀ node ∈ queue.groupNodes, predicate node)
    (group : GroupNode)
    : ∀ node ∈ (queue.finishGroupSuccess group).1.groupNodes, predicate node := by
  let step (acc : State × List ExecutionGroupValue × Keys) (occurrence : Occurrence) :=
    let (current, values, streams) := acc
    match current.taskNode? occurrence with
    | none => (current, values, streams)
    | some taskNode =>
        let values := match taskNode.value with
          | none => values
          | some value => values ++ [value]
        (current.removeTask occurrence, values, streams ++ taskNode.childStreams)
  have foldValid (tasks : List Occurrence) :
      ∀ acc : State × List ExecutionGroupValue × Keys,
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
        (fun node => node.group.node.key != group.group.node.key)
      rootGroups := flushed.rootGroups.filter (· != group.group.node.key) }
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
    {parents : Nat → Keys}
    (accounted : queue.HealthyRegisteredTaskAccounting work settled failed)
    (bounded : queue.PendingBound (fun _ => True) settled)
    (unique : queue.GroupKeysUnique)
    (supported : queue.CachedFailuresSupported work failed)
    (tasksMatch : queue.RegisteredTasksMatch work)
    (generated : ExecutedWork work)
    (links : queue.ChildLinksCanonical parents)
    (matching : queue.GroupNodesMatchWork work)
    (canonical
      : ∀ group dependencies,
          GroupRecordAt work group dependencies → dependencies = parents group.key)
    : queue.drainReadyGroups.1.HealthyRegisteredTaskAccounting work settled failed := by
  let properties (node : GroupNode) : Prop :=
    unsettledCount node.tasks settled ≤ node.pending ∧
      (∀ child ∈ node.childGroups, (parents child).head? = some node.group.node.key) ∧
      ∃ dependencies, GroupRecordAt work node.group.node dependencies
  have removeProperties (node : GroupNode) (occurrence : Occurrence)
      (valid : properties node)
      : properties { node with tasks := node.tasks.filter (· != occurrence) } :=
    ⟨Nat.le_trans (unsettledCount_filter_le node.tasks settled _) valid.1, valid.2⟩
  let invariant (current : State) : Prop :=
    current.HealthyRegisteredTaskAccounting work settled failed ∧
      current.GroupKeysUnique ∧ current.CachedFailuresSupported work failed ∧
      (∀ node ∈ current.groupNodes, properties node) ∧ current.RegisteredTasksMatch work
  have initial : invariant queue :=
    ⟨accounted, unique, supported, (fun node member =>
      ⟨bounded node member trivial, links node member, matching node member⟩), tasksMatch⟩
  have final := State.drainReadyGroups_preserves invariant (by
    intro current node valid member _ _ zero
    have bound : current.PendingBound (fun _ => True) settled :=
      fun candidate present _ => (valid.2.2.2.1 candidate present).1
    have released := valid.1.finishSettledGroupSuccess valid.2.1 node member
      (bound.allSettled member trivial zero)
    refine ⟨released.startNewWork _,
      (valid.2.1.finishGroupSuccess node).startNewWork _,
      (valid.2.2.1.finishGroupSuccess node).startNewWork _, ?_,
      (valid.2.2.2.2.finishGroupSuccess node).startNewWork _⟩
    intro other present
    rw [(State.startNewWork_groupCore _ _).1] at present
    exact State.finishGroupSuccess_nodeProperty properties removeProperties
      valid.2.2.2.1 node other present) (by
    intro current node errors valid member _ cached
    have currentLinks : current.ChildLinksCanonical parents :=
      fun candidate present => (valid.2.2.2.1 candidate present).2.1
    have currentMatch : current.GroupNodesMatchWork work :=
      fun candidate present => (valid.2.2.2.1 candidate present).2.2
    refine ⟨valid.1.finishCachedGroupFailure valid.2.2.1 valid.2.2.2.2 generated
      currentLinks currentMatch
      canonical member cached, valid.2.1.removeGroup _,
      valid.2.2.1.removeGroup _, ?_, valid.2.2.2.2.removeGroup _⟩
    intro other present
    exact valid.2.2.2.1 other (List.mem_filter.mp present).1) initial
  exact final.1

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
