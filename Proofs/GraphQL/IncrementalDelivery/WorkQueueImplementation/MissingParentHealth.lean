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
      (acc : State × List ExecutionGroupValue × NodeRefs) (invariant : property acc.1)
      : property (more.foldl step acc).1 := by
    induction more generalizing acc with
    | nil => exact invariant
    | cons occurrence rest ih =>
        apply ih (fun other member => safe other (List.mem_cons_of_mem _ member))
        obtain ⟨current, values, streams⟩ := acc
        dsimp only [step]
        split
        · exact invariant
        · exact ⟨invariant.1.removeTask occurrence, invariant.2.1.removeTask occurrence,
            invariant.2.2.1.removeTask occurrence,
            invariant.2.2.2.1.removeTask occurrence (safe occurrence List.mem_cons_self),
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

/-- Cache exposure changes no missing-parent health boundary. -/
theorem State.MissingParentAncestorsHealthy.cacheTaskFailures {queue : State}
    {work failed} (prior : queue.MissingParentAncestorsHealthy work failed)
    (available : List (Occurrence × Nat))
    : (queue.cacheTaskFailures available).MissingParentAncestorsHealthy work failed := by
  intro node member dependencies known parent parentEq missing uncancelled
  rw [State.cacheTaskFailures_groupNodes] at member
  rw [State.groupNode?, State.cacheTaskFailures_groupNodes] at missing
  rw [State.cacheTaskFailures_cancelledGroups] at uncancelled
  exact prior node member dependencies known parent parentEq missing uncancelled

/-- Starting a task changes no parent record or cancellation marker. -/
theorem State.MissingParentAncestorsHealthy.startTask {queue : State} {work failed}
    (prior : queue.MissingParentAncestorsHealthy work failed) (occurrence : Occurrence)
    (available : List (Occurrence × Nat) := [])
    : (queue.startTask occurrence available).MissingParentAncestorsHealthy work
        failed := by
  unfold State.startTask
  split
  · exact prior
  · split <;> exact prior

/-- Startup removal cancels every newly missing parent; other starts preserve the boundary. -/
theorem State.MissingParentAncestorsHealthy.startGroup {queue : State} {work failed}
    (prior : queue.MissingParentAncestorsHealthy work failed) (ref : NodeRef)
    (available : List (Occurrence × Nat) := [])
    : (queue.startGroup ref available).1.MissingParentAncestorsHealthy work failed := by
  have cached := prior.cacheTaskFailures available
  unfold State.startGroup
  dsimp only
  split
  · exact cached
  · split
    · have loop (tasks : List Occurrence) (current : State)
          (valid : current.MissingParentAncestorsHealthy work failed)
          : (tasks.foldl (fun current task => current.startTask task available)
              current).MissingParentAncestorsHealthy work failed := by
        induction tasks generalizing current with
        | nil => exact valid
        | cons task rest ih => exact ih _ (valid.startTask task available)
      exact loop _ _ cached
    · exact cached.removeGroup _

/-- Activation preserves health certificates through immediate failed-group removal. -/
theorem State.MissingParentAncestorsHealthy.startNewWork {queue : State} {work failed}
    (prior : queue.MissingParentAncestorsHealthy work failed) (released : NewWork)
    (available : List (Occurrence × Nat) := [])
    : (queue.startNewWork released available).1.MissingParentAncestorsHealthy work
        failed := by
  have groups (refs : NodeRefs) (acc : State × List GroupFailureEvent)
      (valid : acc.1.MissingParentAncestorsHealthy work failed)
      : (refs.foldl
          (fun (current, failures) ref =>
            let (next, queued) := current.startGroup ref available
            (next, failures ++ queued))
          acc).1.MissingParentAncestorsHealthy
          work failed := by
    induction refs generalizing acc with
    | nil => exact valid
    | cons ref rest ih => exact ih _ (valid.startGroup ref available)
  have streams (refs : NodeRefs) (current : State)
      (valid : current.MissingParentAncestorsHealthy work failed)
      : (refs.foldl State.startStream current).MissingParentAncestorsHealthy work failed := by
    induction refs generalizing current with
    | nil => exact valid
    | cons ref rest ih =>
        apply ih
        unfold State.startStream
        split <;> exact valid
  unfold State.startNewWork
  exact streams _ _ (groups _ _ prior)

/-- Activating children preserves healthy root ancestry when their release certifies it.
Witness: the root-ref list is the old roots followed by the newly released group refs.
-/
theorem State.RootAncestorsHealthy.startNewWork {queue : State} {work failed}
    (roots : queue.RootAncestorsHealthy work failed) (released : NewWork)
    (children : ∀ child ∈ released.newGroups, GroupAncestorsHealthy work failed child.ref)
    (available : List (Occurrence × Nat) := [])
    : (queue.startNewWork released available).1.RootAncestorsHealthy work failed := by
  intro ref member
  have old := (queue.startNewWork_groupCore released available).2.2.subset member
  rcases List.mem_append.mp old with old | new
  · exact roots ref old
  · obtain ⟨child, included, rfl⟩ := List.mem_map.mp new
    exact children child included

/-- Successful counter debt excludes failed memberships from every ready flush.
Witness: the drain threads that bound and missing-parent health through startup removal;
there is no rejected-active-group branch in the release-time drain.
-/
theorem State.MissingParentAncestorsHealthy.drainReadyGroups {queue : State}
    {work failed parents settled}
    (prior : queue.MissingParentAncestorsHealthy work failed)
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
    (roots : queue.RootAncestorsHealthy work failed) (sound : queue.GroupMembershipSound)
    (tasks : queue.RegisteredTasksMatch work)
    (bounded : queue.PendingBound (fun _ => True) settled)
    (disjoint : ∀ occurrence ∈ settled, occurrence ∉ failed)
    (available : List (Occurrence × Nat) := [])
    : (queue.drainReadyGroups available).1.MissingParentAncestorsHealthy work failed
      ∧ (queue.drainReadyGroups available).1.RootAncestorsHealthy work failed := by
  let property (current : State) := current.GroupNodesMatchWork work
    ∧ current.ChildLinksCanonical parents ∧ current.GroupParentsCanonical parents
    ∧ current.RetainedFailures work failed
    ∧ current.MissingParentAncestorsHealthy work failed
    ∧ current.RootAncestorsHealthy work failed
    ∧ current.GroupMembershipSound ∧ current.RegisteredTasksMatch work
    ∧ current.PendingBound (fun _ => True) settled
  have result : property (queue.drainReadyGroups available).1 := by
    apply State.drainReadyGroups_preserves property (available := available)
      (valid := ⟨matching, links, fields, counts, prior, roots, sound, tasks, bounded⟩)
    intro current node invariant member active zero
    obtain ⟨matched, linked, parentsKnown, retained, missing, rooted, members,
      registered, pending⟩ := invariant
    have all := pending.allSettled member trivial zero
    have notFailed := fun occurrence member => disjoint occurrence (all occurrence member)
    have closed := missing.finishGroupSuccess generated matched linked parentsKnown canonical
      retained failedKnown member notFailed (rooted _ active)
    have surviving : (current.finishGroupSuccess node).1.RootAncestorsHealthy work failed :=
      fun ref included => rooted ref (current.finishGroupSuccess_rootsSubset node included)
    exact ⟨(matched.finishGroupSuccess node).startNewWork _ available,
      (linked.finishGroupSuccess node).startNewWork _ available,
      (parentsKnown.finishGroupSuccess node).startNewWork _ available,
      (retained.finishGroupSuccess node notFailed).startNewWork _ available,
      closed.1.startNewWork _ available, surviving.startNewWork _ closed.2 available,
      (members.finishGroupSuccess node).startNewWork _ available,
      (registered.finishGroupSuccess node).startNewWork _ available,
      (pending.finishGroupSuccess node all).startNewWork _ available⟩
  exact ⟨result.2.2.2.2.1, result.2.2.2.2.2.1⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
