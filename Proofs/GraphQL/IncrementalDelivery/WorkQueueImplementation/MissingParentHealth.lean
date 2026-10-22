import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupAncestorHealth

/-! Historical health through successful closure and ready rejection replay. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (ExecutionGroupValue)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Successful closure flushes memberships and then uses the same pruning argument
-----------------------------------------------------------------------------------------

/-- Successful closure preserves the missing-parent boundary and healthy release ancestry.
Witness: positive exact error totals justify the uncached closing record; flushing keeps
all other caches and parent links, then taskless pruning transports its healthy ancestry.
This does not require the released children themselves to be healthy.
-/
theorem State.MissingParentAncestorsHealthy.finishGroupSuccess {queue : State}
    {work failed parents} (prior : queue.MissingParentAncestorsHealthy work failed)
    (generated : ExecutedWork work) (matching : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (fields : queue.GroupParentsCanonical parents)
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
    : (queue.finishGroupSuccess group).1.MissingParentAncestorsHealthy work failed
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
    ∧ current.ChildLinksCanonical parents ∧ current.GroupParentsCanonical parents
    ∧ current.RetainedFailures work failed
    ∧ current.MissingParentAncestorsHealthy work failed
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
            invariant.2.2.1.removeTask occurrence, invariant.2.2.2.1.removeTask occurrence (safe occurrence List.mem_cons_self),
            invariant.2.2.2.2.removeTask occurrence⟩
  let flushed := (group.tasks.foldl step (queue, [], [])).1
  have metadata : property flushed := loop group.tasks notFailed (queue, [], [])
    ⟨matching, links, fields, counts, prior⟩
  let current : State := { flushed with
    groupNodes := flushed.groupNodes.filter
      (fun node => node.group.node.ref != group.group.node.ref)
    rootGroups := flushed.rootGroups.filter (· != group.group.node.ref) }
  have currentBoundary : current.MissingParentAncestorsHealthy work failed :=
    metadata.2.2.2.2.filter_parent generated metadata.2.2.1 canonical parentKnown parentHealthy
  have currentMatching : current.GroupNodesMatchWork work :=
    fun node kept => metadata.1 node (List.mem_filter.mp kept).1
  have currentLinks : current.ChildLinksCanonical parents :=
    fun node kept => metadata.2.1 node (List.mem_filter.mp kept).1
  have currentParents : current.GroupParentsCanonical parents :=
    fun node kept => metadata.2.2.1 node (List.mem_filter.mp kept).1
  have currentCounts : current.RetainedFailures work failed :=
    metadata.2.2.2.1.filterGroups _
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
  exact currentBoundary.pruneEmptyGroups generated currentMatching currentLinks
    currentParents canonical currentCounts failedKnown children childAncestors

-----------------------------------------------------------------------------------------
-- Release-time draining retains ancestor health without assuming every root is healthy
-----------------------------------------------------------------------------------------

/-- All active group refs have healthy full ancestry under `failed`; their own caches
may contain failures waiting to be drained. This is an internal proof invariant.
-/
def State.RootAncestorsHealthy (queue : State) (work : Execution.Work)
    (failed : List Occurrence)
    : Prop :=
  ∀ ref ∈ queue.rootGroups, GroupAncestorsHealthy work failed ref

/-- With no accepted failures, every root's ancestry is healthy.
Witness: every invalidation derivation requires a failure token.
-/
theorem State.RootAncestorsHealthy.of_empty (queue : State) (work : Execution.Work)
    : queue.RootAncestorsHealthy work [] := by
  intro ref active node dependencies known same ancestor member invalid
  exact invalid.nonempty rfl

/-- A fresh failure preserves healthy root ancestry when its contributors have retired.
Witness: root retirement and registered-owner accounting rule out a new contribution to
each protected ancestor. This concerns the inventory extension before handler mutation.
-/
theorem State.RootAncestorsHealthy.append_fresh {queue : State} {work settled failed}
    (healthy : queue.RootAncestorsHealthy work failed)
    (retired : queue.RootAncestorsRetired work) (generated : ExecutedWork work)
    (accounted : queue.HealthyRegisteredTaskAccounting work settled failed)
    {task : Task} (registered : task ∈ queue.tasks)
    (matching : TaskMatches work task) (fresh : task.occurrence ∉ settled)
    : queue.RootAncestorsHealthy work (failed ++ [task.occurrence]) := by
  intro ref active node dependencies known same
  exact (same.symm ▸ retired ref active).healthy_append_fresh generated known
    (healthy ref active node dependencies known same) accounted registered matching fresh

/-- Activation changes no live record, cache, or cancellation marker.
Witness: the exact group-core and cancellation equations preserve the missing boundary.
-/
theorem State.MissingParentAncestorsHealthy.startNewWork {queue : State} {work failed}
    (prior : queue.MissingParentAncestorsHealthy work failed) (released : NewWork)
    : (queue.startNewWork released).MissingParentAncestorsHealthy work failed := by
  intro node member dependencies known parent parentEq missing uncancelled
  rw [(queue.startNewWork_groupCore released).1] at member
  have wasMissing : queue.groupNode? parent = none := by
    simpa only [State.groupNode?, (queue.startNewWork_groupCore released).1] using missing
  rw [State.startNewWork_cancelledGroups] at uncancelled
  exact prior node member dependencies known parent parentEq wasMissing
    uncancelled

/-- Activating children preserves healthy root ancestry when their release certifies it.
Witness: the root-ref list is the old roots followed by the newly released group refs.
-/
theorem State.RootAncestorsHealthy.startNewWork {queue : State} {work failed}
    (roots : queue.RootAncestorsHealthy work failed) (released : NewWork)
    (children : ∀ child ∈ released.newGroups, GroupAncestorsHealthy work failed child.ref)
    : (queue.startNewWork released).RootAncestorsHealthy work failed := by
  intro ref member
  rw [(queue.startNewWork_groupCore released).2.2] at member
  rcases List.mem_append.mp member with old | new
  · exact roots ref old
  · obtain ⟨child, included, rfl⟩ := List.mem_map.mp new
    exact children child included

/-- Draining preserves the missing-parent boundary and healthy root ancestry together.
Witness: successful closure proves its released children's ancestry before activation;
cached failure removes groups and marks every newly missing parent cancelled. A failed
newly announced child is permitted by the invariant and handled by the failure branch.
-/
theorem State.MissingParentAncestorsHealthy.drainReadyGroups {queue : State}
    {work failed parents} (prior : queue.MissingParentAncestorsHealthy work failed)
    (generated : ExecutedWork work) (matching : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (fields : queue.GroupParentsCanonical parents)
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
    : queue.drainReadyGroups.1.MissingParentAncestorsHealthy work failed
      ∧ queue.drainReadyGroups.1.RootAncestorsHealthy work failed := by
  let property (current : State) := current.GroupNodesMatchWork work
    ∧ current.ChildLinksCanonical parents ∧ current.GroupParentsCanonical parents
    ∧ current.RetainedFailures work failed
    ∧ current.MissingParentAncestorsHealthy work failed
    ∧ current.RootAncestorsHealthy work failed
    ∧ current.GroupMembershipSound ∧ current.RegisteredTasksMatch work
  have result : property queue.drainReadyGroups.1 := by
    apply State.drainReadyGroups_preserves property
      (valid := ⟨matching, links, fields, counts, prior, roots, sound, tasks⟩)
    · intro current node invariant member active unrejected _
      obtain ⟨matched, linked, parentsKnown, retained, missing, rooted, members, registered⟩ :=
        invariant
      have notFailed := retained.unrejected_tasks_notFailed members registered member unrejected
      have closed := missing.finishGroupSuccess generated matched linked parentsKnown canonical
        retained failedKnown member notFailed (rooted _ active)
      have surviving : (current.finishGroupSuccess node).1.RootAncestorsHealthy work failed :=
        fun ref included => rooted ref (current.finishGroupSuccess_rootsSubset node included)
      exact ⟨(matched.finishGroupSuccess node).startNewWork _,
        (linked.finishGroupSuccess node).startNewWork _,
        (parentsKnown.finishGroupSuccess node).startNewWork _,
        (retained.finishGroupSuccess node notFailed).startNewWork _,
        closed.1.startNewWork _, surviving.startNewWork _ closed.2,
        (members.finishGroupSuccess node).startNewWork _,
        (registered.finishGroupSuccess node).startNewWork _⟩
    · intro current node occurrence errors invariant _ _ _
      obtain ⟨matched, linked, parentsKnown, retained, missing, rooted, members, registered⟩ :=
        invariant
      have unchanged : (current.taskFailure occurrence errors).1.RootAncestorsHealthy work failed := by
        cases found : current.taskNode? occurrence with
        | none => simpa [State.taskFailure, found] using rooted
        | some task =>
            rw [current.taskFailure_eq occurrence errors task found]
            exact failureGroupFold_preserves
              (fun state => state.RootAncestorsHealthy work failed)
              (fun state ref valid key included => valid key
                (state.removeGroup_rootsSubset ref included))
              errors task.task.groups _ rooted
      exact ⟨
        matched.taskFailure occurrence errors,
        linked.taskFailure occurrence errors,
        parentsKnown.taskFailure occurrence errors,
        retained.taskFailure_preserves occurrence errors,
        missing.taskFailure_preserves occurrence errors,
        unchanged,
        members.taskFailure occurrence errors,
        registered.taskFailure occurrence errors
      ⟩
  exact ⟨result.2.2.2.2.1, result.2.2.2.2.2.1⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
