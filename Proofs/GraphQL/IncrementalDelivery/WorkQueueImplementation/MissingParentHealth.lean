import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.AcceptedFailureEquivalence
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.MissingParentRetirement

/-! Preserve the guard's historical health boundary through successful group removal. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (ExecutionGroupValue)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- An active or promoted record may have a failure, but its ancestors must be healthy
-----------------------------------------------------------------------------------------

/-- All full registration ancestors of `ref` are healthy under `failed` in `work`.
The record itself may already have a cached failure; this is weaker than root health.
-/
def GroupAncestorsHealthy (work : Execution.Work) (failed : List Occurrence)
    (ref : NodeRef)
    : Prop :=
  ∀ node dependencies,
    GroupRecordAt work node dependencies
    → node.ref = ref
    → ∀ ancestor ∈ dependencies, ¬GroupRecordInvalidated work failed ancestor

/-- One generated record's ancestry establishes the ref-wide ancestor certificate.
Witness: canonical generated dependencies identify every other record with the same ref.
-/
theorem GroupAncestorsHealthy.of_record {work failed node dependencies}
    (generated : ExecutedWork work) (known : GroupRecordAt work node dependencies)
    (healthy : ∀ ancestor ∈ dependencies, ¬GroupRecordInvalidated work failed ancestor)
    : GroupAncestorsHealthy work failed node.ref := by
  intro other otherDependencies descriptor same
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have equal : otherDependencies = dependencies := by
    rw [canonical _ _ descriptor, canonical _ _ known, same]
  simpa only [equal] using healthy

/-- A child of a healthy parent has healthy ancestors, even if the child itself failed.
Witness: the exact generated chain contains that parent and its own ancestors; a failed
ancestor would invalidate the parent. This also covers taskless intermediate records.
-/
theorem GroupAncestorsHealthy.child
    {work failed child childDependencies parent parentDependencies}
    (generated : ExecutedWork work)
    (childKnown : GroupRecordAt work child childDependencies)
    (parentKnown : GroupRecordAt work parent parentDependencies)
    (head : childDependencies.head? = some parent.ref)
    (healthy : ¬GroupRecordInvalidated work failed parent.ref)
    : GroupAncestorsHealthy work failed child.ref := by
  apply GroupAncestorsHealthy.of_record generated childKnown
  rw [generated.groupRecordAncestryChain childKnown parentKnown head]
  intro ancestor member invalid
  rcases List.mem_cons.mp member with same | earlier
  · exact healthy (same ▸ invalid)
  · exact healthy (.ancestor parentKnown earlier invalid)

/-- Exact cache totals and healthy ancestors make an uncached record healthy.
Witness: generated positive failure counts rule out direct failed contributors; the
ancestor certificate rules out every inherited cause. No guard-soundness premise is used.
-/
theorem State.GroupErrorAccounting.recordHealthy_of_ancestors
    {queue : State} {work failed} {node : GroupNode}
    (counts : queue.GroupErrorAccounting work failed) (generated : ExecutedWork work)
    (member : node ∈ queue.groupNodes) (uncached : node.failure = none)
    {dependencies} (known : GroupRecordAt work node.group.node dependencies)
    (ancestors : GroupAncestorsHealthy work failed node.group.node.ref)
    (failedKnown
      : ∀ occurrence ∈ failed,
          ∃ owners producer payload,
            TaskAt work occurrence owners producer payload
            ∧ payload.failure.isSome = true)
    : ¬GroupRecordInvalidated work failed node.group.node.ref := by
  intro invalid
  rcases generated.groupRecordInvalidated_causes known invalid with
    ⟨occurrence, owners, ⟨producer, payload, task⟩, owner, recorded⟩
    | ⟨ancestor, member, failure⟩
  · obtain ⟨otherOwners, otherProducer, otherPayload, otherTask, fails⟩ :=
      failedKnown occurrence recorded
    exact counts.uncached_noFailedContributor generated member uncached otherTask fails
      ((task.unique otherTask).1 ▸ owner) recorded
  · exact ancestors _ _ known rfl ancestor member failure

-----------------------------------------------------------------------------------------
-- A healthy parent can disappear without losing its child's historical guard evidence
-----------------------------------------------------------------------------------------

/-- Removing a healthy parent preserves the absent-parent health boundary.
Witness: an old missing parent retains its evidence; a newly missing parent supplies
the complete healthy ancestry through its generated registration chain.
-/
theorem State.MissingParentAncestorsHealthy.filter_parent {queue : State}
    {work failed parents} (prior : queue.MissingParentAncestorsHealthy work failed)
    (generated : ExecutedWork work) (fields : queue.GroupParentsCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    {removed : Execution.DeliveryNode} {parentDependencies}
    (parentKnown : GroupRecordAt work removed parentDependencies)
    (healthy : ¬GroupRecordInvalidated work failed removed.ref)
    : ({
        queue with
          groupNodes :=
            queue.groupNodes.filter (fun node => node.group.node.ref != removed.ref)
      }).MissingParentAncestorsHealthy
        work failed := by
  intro node included uncached dependencies known parent parentEq missing uncancelled
  have oldMember := (List.mem_filter.mp included).1
  by_cases same : parent = removed.ref
  · have head : dependencies.head? = some removed.ref := by
      rw [canonical _ _ known, ← fields node oldMember, parentEq, same]
    exact (GroupAncestorsHealthy.child generated known parentKnown head healthy)
      _ _ known rfl
  · have wasMissing : queue.groupNode? parent = none := by
      cases found : queue.groupNode? parent with
      | none => rfl
      | some old =>
          have ref := State.groupNode?_ref found
          have retained : old ∈ queue.groupNodes.filter
              (fun node => node.group.node.ref != removed.ref) :=
            List.mem_filter.mpr ⟨List.mem_of_find?_eq_some found, by simp [ref, same]⟩
          exact False.elim
            (List.find?_eq_none.mp missing old retained (beq_iff_eq.mpr ref))
    exact prior node oldMember uncached dependencies known parent parentEq
      wasMissing uncancelled

/-- Task-membership removal does not change any absent-parent health boundary.
Witness: live refs, group descriptors, caches, and cancellation markers are unchanged.
-/
theorem State.MissingParentAncestorsHealthy.removeTask {queue : State} {work failed}
    (prior : queue.MissingParentAncestorsHealthy work failed) (occurrence : Occurrence)
    : (queue.removeTask occurrence).MissingParentAncestorsHealthy work failed := by
  intro node member uncached dependencies known parent parentEq missing uncancelled
  obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
  have wasMissing : queue.groupNode? parent = none := by
    rw [State.groupNode?_eq_none_iff] at missing ⊢
    simpa only [State.removeTask, List.map_map, Function.comp_def] using missing
  exact prior old oldMember uncached dependencies known parent parentEq
    wasMissing uncancelled

-----------------------------------------------------------------------------------------
-- Taskless pruning proves each removed parent's health before releasing its children
-----------------------------------------------------------------------------------------

/-- Pruning preserves any invariant stable under removing a healthy record, and gives
released records healthy ancestry. Witness: exact cache totals justify each uncached
removal, while generated child chains propagate health. The callback shares this traversal
between the missing-parent boundary and global retired-record health.
-/
theorem State.pruneEmptyGroups_health_preserves {queue : State} {work failed parents}
    (generated : ExecutedWork work) (matching : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (counts : queue.GroupErrorAccounting work failed)
    (failedKnown
      : ∀ occurrence ∈ failed,
          ∃ owners producer payload,
            TaskAt work occurrence owners producer payload
            ∧ payload.failure.isSome = true)
    (groups : List Execution.DeliveryNode)
    (healthy : ∀ group ∈ groups, GroupAncestorsHealthy work failed group.ref)
    (property : State → Prop)
    (preserved
      : ∀ current node,
          current.GroupNodesMatchWork work
          → node ∈ current.groupNodes
          → ¬GroupRecordInvalidated work failed node.group.node.ref
          → property current
          → property
              {
                current with
                  groupNodes :=
                    current.groupNodes.filter
                      (fun entry => entry.group.node.ref != node.group.node.ref)
              })
    (initial : property queue)
    : property (queue.pruneEmptyGroups groups).1
      ∧ ∀ group ∈ (queue.pruneEmptyGroups groups).2,
          GroupAncestorsHealthy work failed group.ref := by
  have loop (fuel : Nat) (current : State) (remaining kept : List Execution.DeliveryNode)
      (invariant : property current)
      (matched : current.GroupNodesMatchWork work)
      (linked : current.ChildLinksCanonical parents)
      (accounted : current.GroupErrorAccounting work failed)
      (pending : ∀ group ∈ remaining, GroupAncestorsHealthy work failed group.ref)
      (done : ∀ group ∈ kept, GroupAncestorsHealthy work failed group.ref)
      : property (State.pruneEmptyGroups.go fuel current remaining kept).1
        ∧ ∀ group ∈ (State.pruneEmptyGroups.go fuel current remaining kept).2,
            GroupAncestorsHealthy work failed group.ref := by
    induction fuel generalizing current remaining kept with
    | zero => exact ⟨invariant, done⟩
    | succ fuel ih =>
        cases remaining with
        | nil => exact ⟨invariant, done⟩
        | cons group rest =>
            unfold State.pruneEmptyGroups.go
            split
            · exact ih _ _ _ invariant matched linked accounted
                (fun next member => pending next (List.mem_cons_of_mem _ member)) done
            · rename_i node found
              split
              · rename_i empty
                have member := List.mem_of_find?_eq_some found
                have ref := State.groupNode?_ref found
                obtain ⟨dependencies, record⟩ := matched node member
                have parentHealthy := accounted.recordHealthy_of_ancestors generated member
                  (Option.isNone_iff_eq_none.mp (Bool.and_eq_true_iff.mp empty).2)
                  record (ref.symm ▸ pending group List.mem_cons_self) failedKnown
                have nextProperty := preserved current node matched member parentHealthy invariant
                rw [ref] at nextProperty
                apply ih _ _ _ nextProperty
                  (fun next kept => matched next (List.mem_filter.mp kept).1)
                  (fun next kept => linked next (List.mem_filter.mp kept).1)
                  ⟨fun next kept => accounted.live next (List.mem_filter.mp kept).1,
                    accounted.fresh⟩ _ done
                intro child included
                rcases List.mem_append.mp included with descendant | tail
                · obtain ⟨childRef, childMember, selected⟩ := List.mem_filterMap.mp descendant
                  cases childFound : current.groupNode? childRef with
                  | none => simp [childFound] at selected
                  | some childNode =>
                      have same : childNode.group.node = child := by
                        simpa [childFound] using selected
                      obtain ⟨childDependencies, childRecord⟩ :=
                        matched childNode (List.mem_of_find?_eq_some childFound)
                      have head : childDependencies.head? = some node.group.node.ref := by
                        rw [canonical _ _ childRecord, State.groupNode?_ref childFound]
                        exact linked node member childRef childMember
                      exact same
                      ▸ GroupAncestorsHealthy.child generated childRecord record
                          head parentHealthy
                · exact pending child (List.mem_cons_of_mem _ tail)
              · apply ih _ _ _ invariant matched linked accounted
                  (fun next member => pending next (List.mem_cons_of_mem _ member))
                intro next member
                rcases List.mem_append.mp member with earlier | latest
                · exact done next earlier
                · exact (List.mem_singleton.mp latest) ▸ pending group List.mem_cons_self
  exact loop _ queue groups [] initial matching links counts healthy
    (by intro group member; cases member)

/-- Pruning preserves absent-parent health and healthy release ancestry.
Witness: instantiate the shared health traversal with canonical parents and the
single-parent removal theorem; retained records may themselves have cached failures.
-/
theorem State.MissingParentAncestorsHealthy.pruneEmptyGroups {queue : State}
    {work failed parents} (prior : queue.MissingParentAncestorsHealthy work failed)
    (generated : ExecutedWork work) (matching : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (fields : queue.GroupParentsCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (counts : queue.GroupErrorAccounting work failed)
    (failedKnown
      : ∀ occurrence ∈ failed,
          ∃ owners producer payload,
            TaskAt work occurrence owners producer payload
            ∧ payload.failure.isSome = true)
    (groups : List Execution.DeliveryNode)
    (healthy : ∀ group ∈ groups, GroupAncestorsHealthy work failed group.ref)
    : (queue.pruneEmptyGroups groups).1.MissingParentAncestorsHealthy work failed
      ∧ ∀ group ∈ (queue.pruneEmptyGroups groups).2,
          GroupAncestorsHealthy work failed group.ref := by
  have result := State.pruneEmptyGroups_health_preserves generated matching links canonical
    counts failedKnown groups healthy
    (fun current => current.GroupParentsCanonical parents
      ∧ current.MissingParentAncestorsHealthy work failed) (by
        intro current node matched member safe invariant
        obtain ⟨dependencies, known⟩ := matched node member
        exact ⟨fun other kept => invariant.1 other (List.mem_filter.mp kept).1,
          invariant.2.filter_parent generated invariant.1 canonical known safe⟩)
    ⟨fields, prior⟩
  exact ⟨result.1.2, result.2⟩

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
    (counts : queue.GroupErrorAccounting work failed)
    (failedKnown
      : ∀ occurrence ∈ failed,
          ∃ owners producer payload,
            TaskAt work occurrence owners producer payload
            ∧ payload.failure.isSome = true)
    {group : GroupNode} (member : group ∈ queue.groupNodes)
    (uncached : group.failure = none)
    (ancestors : GroupAncestorsHealthy work failed group.group.node.ref)
    : (queue.finishGroupSuccess group).1.MissingParentAncestorsHealthy work failed
      ∧ ∀ child ∈ (queue.finishGroupSuccess group).2.2.newGroups,
          GroupAncestorsHealthy work failed child.ref := by
  obtain ⟨dependencies, parentKnown⟩ := matching group member
  have parentHealthy := counts.recordHealthy_of_ancestors generated member uncached
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
    ∧ current.GroupErrorAccounting work failed
    ∧ current.MissingParentAncestorsHealthy work failed
  have loop (more : List Occurrence) (acc : State × List ExecutionGroupValue × NodeRefs)
      (invariant : property acc.1) : property (more.foldl step acc).1 := by
    induction more generalizing acc with
    | nil => exact invariant
    | cons occurrence rest ih =>
        apply ih
        obtain ⟨current, values, streams⟩ := acc
        dsimp only [step]
        split
        · exact invariant
        · exact ⟨invariant.1.removeTask occurrence, invariant.2.1.removeTask occurrence,
            invariant.2.2.1.removeTask occurrence, invariant.2.2.2.1.removeTask occurrence,
            invariant.2.2.2.2.removeTask occurrence⟩
  let flushed := (group.tasks.foldl step (queue, [], [])).1
  have metadata : property flushed := loop group.tasks (queue, [], [])
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
  have currentCounts : current.GroupErrorAccounting work failed :=
    ⟨fun node kept => metadata.2.2.2.1.live node (List.mem_filter.mp kept).1,
      metadata.2.2.2.1.fresh⟩
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
  intro node member uncached dependencies known parent parentEq missing uncancelled
  rw [(queue.startNewWork_groupCore released).1] at member
  have wasMissing : queue.groupNode? parent = none := by
    simpa only [State.groupNode?, (queue.startNewWork_groupCore released).1] using missing
  rw [State.startNewWork_cancelledGroups] at uncancelled
  exact prior node member uncached dependencies known parent parentEq wasMissing
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
    (counts : queue.GroupErrorAccounting work failed)
    (failedKnown
      : ∀ occurrence ∈ failed,
          ∃ owners producer payload,
            TaskAt work occurrence owners producer payload
            ∧ payload.failure.isSome = true)
    (roots : queue.RootAncestorsHealthy work failed)
    : queue.drainReadyGroups.1.MissingParentAncestorsHealthy work failed
      ∧ queue.drainReadyGroups.1.RootAncestorsHealthy work failed := by
  let property (current : State) := current.GroupNodesMatchWork work
    ∧ current.ChildLinksCanonical parents ∧ current.GroupParentsCanonical parents
    ∧ current.GroupErrorAccounting work failed
    ∧ current.MissingParentAncestorsHealthy work failed
    ∧ current.RootAncestorsHealthy work failed
  have result : property queue.drainReadyGroups.1 := by
    apply State.drainReadyGroups_preserves property
      (valid := ⟨matching, links, fields, counts, prior, roots⟩)
    · intro current node invariant member active uncached _
      have closed := invariant.2.2.2.2.1.finishGroupSuccess generated invariant.1
        invariant.2.1 invariant.2.2.1 canonical invariant.2.2.2.1 failedKnown
        member uncached (invariant.2.2.2.2.2 _ active)
      have retained : (current.finishGroupSuccess node).1.RootAncestorsHealthy work failed :=
        fun ref included => invariant.2.2.2.2.2 ref
          (current.finishGroupSuccess_rootsSubset node included)
      exact ⟨(invariant.1.finishGroupSuccess node).startNewWork _,
        (invariant.2.1.finishGroupSuccess node).startNewWork _,
        (invariant.2.2.1.finishGroupSuccess node).startNewWork _,
        (invariant.2.2.2.1.finishGroupSuccess node).startNewWork _,
        closed.1.startNewWork _, retained.startNewWork _ closed.2⟩
    · intro current node errors invariant _ _ _
      exact ⟨invariant.1.removeGroup _, invariant.2.1.removeGroup _,
        invariant.2.2.1.removeGroup _, invariant.2.2.2.1.removeGroup _,
        invariant.2.2.2.2.1.removeGroup _,
        fun ref included => invariant.2.2.2.2.2 ref
          (current.removeGroup_rootsSubset _ included)⟩
  exact result.2.2.2.2

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
