import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RetiredRecordHealth

/-! Successful release installs durable health certificates for newly retired records. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (ExecutionGroupValue)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Taskless pruning establishes health before recording each successful retirement
-----------------------------------------------------------------------------------------

/-- Pruning retains healthy uncancelled retirements and healthy ancestry of released groups.
Witness: the shared health traversal proves every removed record healthy; filtering then
installs that record's certificate without altering earlier retired records' health.
-/
theorem State.UncancelledRetiredHealthy.pruneEmptyGroups {queue : State}
    {work failed parents} (prior : queue.UncancelledRetiredHealthy work failed)
    (generated : ExecutedWork work) (matching : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (counts : queue.RetainedFailures work failed)
    (failedKnown
      : ∀ occurrence ∈ failed,
          ∃ owners producer payload,
            TaskAt work occurrence owners producer payload
            ∧ payload.failure.isSome = true)
    (groups : List Execution.DeliveryNode)
    (healthy : ∀ group ∈ groups, GroupAncestorsHealthy work failed group.ref)
    : (queue.pruneEmptyGroups groups).1.UncancelledRetiredHealthy work failed
      ∧ ∀ group ∈ (queue.pruneEmptyGroups groups).2,
          GroupAncestorsHealthy work failed group.ref :=
  State.pruneEmptyGroups_health_preserves generated matching links canonical counts
    failedKnown groups healthy
    (fun current => current.UncancelledRetiredHealthy work failed)
    (fun _ _ _ _ safe invariant => invariant.filter_parent safe) prior

-----------------------------------------------------------------------------------------
-- Successful closure preserves earlier certificates and installs the closing parent's
-----------------------------------------------------------------------------------------

/-- Closing a group with nonfailed memberships preserves retired-record health and
certifies every released child's ancestry. Witness: retained failures and healthy ancestry
prove the parent's health; safe flushing and taskless pruning preserve the certificate.
-/
theorem State.UncancelledRetiredHealthy.finishGroupSuccess {queue : State}
    {work failed parents} (prior : queue.UncancelledRetiredHealthy work failed)
    (generated : ExecutedWork work) (matching : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (counts : queue.RetainedFailures work failed)
    (failedKnown
      : ∀ occurrence ∈ failed,
          ∃ owners producer payload,
            TaskAt work occurrence owners producer payload
            ∧ payload.failure.isSome = true)
    {group : GroupNode} (member : group ∈ queue.groupNodes)
    (notFailed : ∀ occurrence ∈ group.tasks, occurrence ∉ failed)
    (ancestors : GroupAncestorsHealthy work failed group.group.node.ref)
    : (queue.finishGroupSuccess group).1.UncancelledRetiredHealthy work failed
      ∧ ∀ child ∈ (queue.finishGroupSuccess group).2.2.newGroups,
          GroupAncestorsHealthy work failed child.ref := by
  obtain ⟨dependencies, parentKnown⟩ := matching group member
  have parentHealthy := counts.recordHealthy_of_ancestors generated member notFailed
    parentKnown ancestors failedKnown
  let step (acc : State × List ExecutionGroupValue × NodeRefs) (occurrence : Occurrence) :=
    let (current, values, streams) := acc
    match current.taskNode? occurrence with
    | none => (current, values, streams)
    | some taskNode =>
        let values := match taskNode.value with
          | none => values
          | some value => values ++ [value]
        (current.removeTask occurrence, values, streams ++ taskNode.childStreams)
  let property (current : State) := current.GroupNodesMatchWork work
    ∧ current.ChildLinksCanonical parents ∧ current.RetainedFailures work failed
    ∧ current.UncancelledRetiredHealthy work failed
  have loop (more : List Occurrence) (safe : ∀ occurrence ∈ more, occurrence ∉ failed)
      (acc : State × List ExecutionGroupValue × NodeRefs) (invariant : property acc.1) : property (more.foldl step acc).1 := by
    induction more generalizing acc with
    | nil => exact invariant
    | cons occurrence rest ih =>
        apply ih (fun other member => safe other (List.mem_cons_of_mem _ member))
        obtain ⟨current, values, streams⟩ := acc
        dsimp only [step]
        split
        · exact invariant
        · exact ⟨invariant.1.removeTask occurrence, invariant.2.1.removeTask occurrence,
            invariant.2.2.1.removeTask occurrence (safe occurrence List.mem_cons_self), invariant.2.2.2.removeTask occurrence⟩
  let flushed := (group.tasks.foldl step (queue, [], [])).1
  have metadata : property flushed := loop group.tasks notFailed (queue, [], [])
    ⟨matching, links, counts, prior⟩
  let current : State := { flushed with
    groupNodes := flushed.groupNodes.filter
      (fun node => node.group.node.ref != group.group.node.ref)
    rootGroups := flushed.rootGroups.filter (· != group.group.node.ref) }
  have currentHealth : current.UncancelledRetiredHealthy work failed :=
    metadata.2.2.2.filter_parent parentHealthy
  have currentMatching : current.GroupNodesMatchWork work :=
    fun node kept => metadata.1 node (List.mem_filter.mp kept).1
  have currentLinks : current.ChildLinksCanonical parents :=
    fun node kept => metadata.2.1 node (List.mem_filter.mp kept).1
  have currentCounts : current.RetainedFailures work failed :=
    metadata.2.2.1.filterGroups _
  let children := group.childGroups.filterMap
    (fun ref => (current.groupNode? ref).map (fun node => node.group.node))
  have childAncestors : ∀ child ∈ children, GroupAncestorsHealthy work failed child.ref := by
    intro child included
    obtain ⟨ref, linked, selected⟩ := List.mem_filterMap.mp included
    cases found : current.groupNode? ref with
    | none => simp [found] at selected
    | some node =>
        have same : node.group.node = child := by simpa [found] using selected
        obtain ⟨childDependencies, childKnown⟩ :=
          currentMatching node (List.mem_of_find?_eq_some found)
        have head : childDependencies.head? = some group.group.node.ref := by
          rw [canonical _ _ childKnown, State.groupNode?_ref found]
          exact links group member ref linked
        exact same
        ▸ GroupAncestorsHealthy.child generated childKnown parentKnown head parentHealthy
  exact currentHealth.pruneEmptyGroups generated currentMatching currentLinks canonical
    currentCounts failedKnown children childAncestors

-----------------------------------------------------------------------------------------
-- Active-root ancestry and retired health survive the entire recursive release drain
-----------------------------------------------------------------------------------------

/-- Draining jointly preserves healthy root ancestry and healthy uncancelled retirement.
Witness: successful closure installs a healthy retirement and certifies child ancestry;
rejection replay marks new retirements cancelled. Rejected released children remain
allowed, because root ancestry says nothing about a root's own outcome.
-/
theorem State.UncancelledRetiredHealthy.drainReadyGroups {queue : State}
    {work failed parents} (prior : queue.UncancelledRetiredHealthy work failed)
    (generated : ExecutedWork work) (matching : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (counts : queue.RetainedFailures work failed)
    (failedKnown
      : ∀ occurrence ∈ failed,
          ∃ owners producer payload,
            TaskAt work occurrence owners producer payload
            ∧ payload.failure.isSome = true)
    (roots : queue.RootAncestorsHealthy work failed)
    (sound : queue.GroupMembershipSound) (tasks : queue.RegisteredTasksMatch work)
    : queue.drainReadyGroups.1.UncancelledRetiredHealthy work failed
      ∧ queue.drainReadyGroups.1.RootAncestorsHealthy work failed := by
  let property (current : State) := current.GroupNodesMatchWork work
    ∧ current.ChildLinksCanonical parents ∧ current.RetainedFailures work failed
    ∧ current.UncancelledRetiredHealthy work failed ∧ current.RootAncestorsHealthy work failed
    ∧ current.GroupMembershipSound ∧ current.RegisteredTasksMatch work
  have result : property queue.drainReadyGroups.1 := by
    apply State.drainReadyGroups_preserves property
      (valid := ⟨matching, links, counts, prior, roots, sound, tasks⟩)
    · intro current node invariant member active unrejected _
      obtain ⟨matched, linked, retained, retired, rooted, members, registered⟩ := invariant
      have notFailed := retained.unrejected_tasks_notFailed members registered member unrejected
      have closed := retired.finishGroupSuccess generated matched linked canonical retained
        failedKnown member notFailed (rooted _ active)
      have surviving : (current.finishGroupSuccess node).1.RootAncestorsHealthy work failed :=
        fun ref included => rooted ref (current.finishGroupSuccess_rootsSubset node included)
      exact ⟨(matched.finishGroupSuccess node).startNewWork _,
        (linked.finishGroupSuccess node).startNewWork _,
        (retained.finishGroupSuccess node notFailed).startNewWork _,
        closed.1.startNewWork _, surviving.startNewWork _ closed.2,
        (members.finishGroupSuccess node).startNewWork _,
        (registered.finishGroupSuccess node).startNewWork _⟩
    · intro current node occurrence errors invariant _ _ _
      obtain ⟨matched, linked, retained, retired, rooted, members, registered⟩ := invariant
      exact ⟨matched.taskFailure occurrence errors, linked.taskFailure occurrence errors,
        retained.taskFailure_preserves occurrence errors,
        retired.taskFailure_preserves occurrence errors,
        fun ref included => rooted ref (current.taskFailure_rootsSubset occurrence errors included),
        members.taskFailure occurrence errors, registered.taskFailure occurrence errors⟩
  exact ⟨result.2.2.2.1, result.2.2.2.2.1⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
