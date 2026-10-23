import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.WorkDeclarations
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureRetentionSettlement
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RetiredAncestorHealth
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.MissingParentRetirement

/-! Preserve historical ancestor health through task removal and taskless pruning. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (ExecutionGroupValue)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- An active or promoted record may have a failure, but its ancestors must be healthy
-----------------------------------------------------------------------------------------

/-- All full registration ancestors of `ref` are healthy under `failed` in `work`.
The record itself may retain a rejected task; its own outcome is independent.
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

/-- Healthy ancestry and nonfailed memberships make a live record healthy.
Witness: retention lists every direct failed contributor; the membership certificate
excludes it. The ancestor certificate excludes every inherited cause.
-/
theorem State.RetainedFailures.recordHealthy_of_ancestors
    {queue : State} {work failed} {node : GroupNode}
    (counts : queue.RetainedFailures work failed) (generated : ExecutedWork work)
    (member : node ∈ queue.groupNodes)
    (notFailed : ∀ occurrence ∈ node.tasks, occurrence ∉ failed)
    {dependencies} (known : GroupRecordAt work node.group.node dependencies)
    (ancestors : GroupAncestorsHealthy work failed node.group.node.ref)
    (_failedKnown
      : ∀ occurrence ∈ failed,
          ∃ owners producer payload,
            TaskAt work occurrence owners producer payload
            ∧ payload.failure.isSome = true)
    : ¬GroupRecordInvalidated work failed node.group.node.ref := by
  intro invalid
  rcases generated.groupRecordInvalidated_causes known invalid with
    ⟨occurrence, owners, ⟨producer, payload, task⟩, owner, recorded⟩
    | ⟨ancestor, member, failure⟩
  · exact notFailed occurrence
      (counts.retained occurrence recorded owners ⟨producer, payload, task⟩ node member owner).1
      recorded
  · exact ancestors _ _ known rfl ancestor member failure

-----------------------------------------------------------------------------------------
-- A healthy parent can disappear without losing its child's historical ancestry evidence
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
  intro node included dependencies known parent parentEq missing uncancelled
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
    exact prior node oldMember dependencies known parent parentEq
      wasMissing uncancelled

/-- Task-membership removal does not change any absent-parent health boundary.
Witness: live refs, group descriptors and cancellation markers are unchanged.
-/
theorem State.MissingParentAncestorsHealthy.removeTask {queue : State} {work failed}
    (prior : queue.MissingParentAncestorsHealthy work failed) (occurrence : Occurrence)
    : (queue.removeTask occurrence).MissingParentAncestorsHealthy work failed := by
  intro node member dependencies known parent parentEq missing uncancelled
  obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
  have wasMissing : queue.groupNode? parent = none := by
    rw [State.groupNode?_eq_none_iff] at missing ⊢
    simpa only [State.removeTask, List.map_map, Function.comp_def] using missing
  exact prior old oldMember dependencies known parent parentEq
    wasMissing uncancelled

-----------------------------------------------------------------------------------------
-- Taskless pruning proves each removed parent's health before releasing its children
-----------------------------------------------------------------------------------------

/-- Pruning preserves any invariant stable under removing a healthy record, and gives
released records healthy ancestry. Witness: retention excludes failed contributors of
an empty task list, while generated child chains propagate health. The callback shares this
traversal
between the missing-parent boundary and global retired-record health.
-/
theorem State.pruneEmptyGroups_health_preserves {queue : State} {work failed parents}
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
      (accounted : current.RetainedFailures work failed)
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
                  (by
                    intro occurrence listed
                    have noTasks : node.tasks = [] := List.isEmpty_iff.mp empty
                    simp [noTasks] at listed)
                  record (ref.symm ▸ pending group List.mem_cons_self) failedKnown
                have nextProperty := preserved current node matched member parentHealthy invariant
                rw [ref] at nextProperty
                apply ih _ _ _ nextProperty
                  (fun next kept => matched next (List.mem_filter.mp kept).1)
                  (fun next kept => linked next (List.mem_filter.mp kept).1)
                  (accounted.filterGroups _) _ done
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
  have result := loop (queue.groupNodes.length + groups.length + 1) queue groups [] initial
    matching links counts healthy (by intro group member; cases member)
  refine ⟨result.1, ?_⟩
  intro group member
  exact result.2 group (by simpa only [State.pruneEmptyGroups] using member)

/-- Pruning preserves absent-parent health and healthy release ancestry.
Witness: instantiate the shared health traversal with canonical parents and the
single-parent removal theorem; retained records may themselves contain rejected tasks.
-/
theorem State.MissingParentAncestorsHealthy.pruneEmptyGroups {queue : State}
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

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
