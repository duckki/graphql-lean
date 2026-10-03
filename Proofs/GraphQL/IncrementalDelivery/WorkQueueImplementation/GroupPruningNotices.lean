import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupSupportSettlement
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GeneratedDescriptors

/-! Pruned notice frontiers retain exact contributor descriptors and actual contents. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (ExecutionGroupValue)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Following a taskless ancestor's child links preserves notice metadata
-----------------------------------------------------------------------------------------

/-- Pruning inherits a ref property only along actually traversed empty, error-free shells.
Witness: the finite traversal preserves the property of remaining and kept candidates.
Removed records come from the original queue, and child lookup retains the linked ref.
Unrelated live records need not satisfy the property; this isolates the local induction
needed for causal readiness and freshness of promoted notices.
-/
theorem State.pruneEmptyGroups_inheritedNoticeProperty {queue : State}
    {property : Nat → Prop}
    (inherited
      : ∀ node ∈ queue.groupNodes,
          property node.group.node.ref
          → node.tasks = []
          → node.failure = none
          → ∀ child ∈ queue.groupNodes,
              child.group.node.ref ∈ node.childGroups → property child.group.node.ref)
    (groups : List Execution.DeliveryNode)
    (candidates : ∀ group ∈ groups, property group.ref)
    : ∀ group ∈ (queue.pruneEmptyGroups groups).2, property group.ref := by
  have loop (fuel : Nat) (current : State) (remaining kept : List Execution.DeliveryNode)
      (records : current.groupNodes.Subset queue.groupNodes)
      (pending : ∀ group ∈ remaining, property group.ref)
      (retained : ∀ group ∈ kept, property group.ref)
      : ∀ group ∈ (State.pruneEmptyGroups.go fuel current remaining kept).2,
          property group.ref := by
    induction fuel generalizing current remaining kept with
    | zero => exact retained
    | succ fuel ih =>
        cases remaining with
        | nil => exact retained
        | cons group rest =>
            have tail := fun node member => pending node (List.mem_cons_of_mem _ member)
            unfold State.pruneEmptyGroups.go
            split
            · exact ih _ _ _ records tail retained
            · rename_i node found
              split
              · rename_i empty
                have gate : node.tasks = [] ∧ node.failure = none := by
                  simpa only [Bool.and_eq_true, List.isEmpty_iff,
                    Option.isNone_iff_eq_none]
                    using empty
                have atNode : property node.group.node.ref :=
                  (State.groupNode?_ref found).symm ▸ pending group List.mem_cons_self
                have childProperty := inherited node (records (List.mem_of_find?_eq_some found))
                  atNode gate.1 gate.2
                apply ih
                · intro record member
                  exact records (List.mem_filter.mp member).1
                · intro candidate member
                  rcases List.mem_append.mp member with promoted | old
                  · obtain ⟨ref, member, selected⟩ := List.mem_filterMap.mp promoted
                    cases lookup : current.groupNode? ref with
                    | none => simp [lookup] at selected
                    | some child =>
                        have same : child.group.node = candidate := by simpa [lookup] using selected
                        rw [← same]
                        exact childProperty child
                          (records (List.mem_of_find?_eq_some lookup))
                          ((State.groupNode?_ref lookup).symm ▸ member)
                  · exact tail candidate old
                · exact retained
              · apply ih _ _ _ records tail
                intro candidate member
                rcases List.mem_append.mp member with old | new
                · exact retained candidate old
                · obtain rfl := List.mem_singleton.mp new
                  exact pending _ List.mem_cons_self
  exact loop _ queue groups [] (List.Subset.refl _) candidates (by simp)

/-- Pruning preserves descriptor properties through both kept roots and promoted children.
Witness: remaining and kept candidates satisfy `property`; newly promoted descriptors
come from actual group-record lookups. Only the registry shrinks, including at fuel zero.
-/
theorem State.pruneEmptyGroups_noticeProperty {queue : State}
    {property : Execution.DeliveryNode → Prop}
    (registered : ∀ node ∈ queue.groupNodes, property node.group.node)
    (groups : List Execution.DeliveryNode) (candidates : ∀ group ∈ groups, property group)
    : ∀ group ∈ (queue.pruneEmptyGroups groups).2, property group := by
  have loop (fuel : Nat) (current : State)
      (remaining kept : List Execution.DeliveryNode)
      (records : ∀ node ∈ current.groupNodes, property node.group.node)
      (pending : ∀ group ∈ remaining, property group)
      (retained : ∀ group ∈ kept, property group)
      : ∀ group ∈ (State.pruneEmptyGroups.go fuel current remaining kept).2,
          property group := by
    induction fuel generalizing current remaining kept with
    | zero => exact retained
    | succ fuel ih =>
        cases remaining with
        | nil => exact retained
        | cons group rest =>
            have tail := fun node member => pending node (List.mem_cons_of_mem _ member)
            unfold State.pruneEmptyGroups.go
            split
            · exact ih _ _ _ records tail retained
            · split
              · apply ih
                · intro node member
                  exact records node (List.mem_filter.mp member).1
                · intro candidate member
                  rcases List.mem_append.mp member with promoted | old
                  · obtain ⟨ref, _, found⟩ := List.mem_filterMap.mp promoted
                    cases lookup : current.groupNode? ref with
                    | none => simp [lookup] at found
                    | some node =>
                        have same : node.group.node = candidate := by simpa [lookup] using found
                        exact same ▸ records node (List.mem_of_find?_eq_some lookup)
                  · exact tail candidate old
                · exact retained
              · apply ih _ _ _ records tail
                intro node member
                rcases List.mem_append.mp member with old | new
                · exact retained node old
                · obtain rfl := List.mem_singleton.mp new
                  exact pending _ List.mem_cons_self
  exact loop _ queue groups [] registered candidates (by simp)

/-- Every pruned notice retains its exact contributor-or-ancestor registration descriptor.
Witness: instantiate descriptor preservation with the fixed-work record relation.
This alone does not assert that the retained descriptor has a contributing task.
-/
theorem State.GroupNodesMatchWork.pruneEmptyGroups_notices {queue : State} {work}
    (registered : queue.GroupNodesMatchWork work) (groups : List Execution.DeliveryNode)
    (candidates : ∀ group ∈ groups, ∃ dependencies, GroupRecordAt work group dependencies)
    : ∀ group ∈ (queue.pruneEmptyGroups groups).2,
        ∃ dependencies, GroupRecordAt work group dependencies :=
  queue.pruneEmptyGroups_noticeProperty
    (property := fun node => ∃ dependencies, GroupRecordAt work node dependencies)
    registered groups candidates

-----------------------------------------------------------------------------------------
-- The pruning gate excludes ancestor-only shells from actual notices
-----------------------------------------------------------------------------------------

/-- A retained notice denotes a real work node and still has tasks or a cached failure.
Witness: descriptor preservation includes promoted children; contributor-ref support
excludes taskless shells, and generated descriptor coherence identifies the exact node.
The concrete post-pruning contents are retained for the remaining accounting bridge.
-/
theorem State.pruneEmptyGroups_noticeContents {queue : State} {work}
    (generated : ExecutedWork work) (unique : queue.GroupRefsUnique)
    (registered : queue.GroupNodesMatchWork work)
    (supported
      : queue.GroupRefSupport
          (fun ref => ∃ dependencies, NodeHasDependencies work ref .group dependencies))
    (groups : List Execution.DeliveryNode)
    (candidates : ∀ group ∈ groups, ∃ dependencies, GroupRecordAt work group dependencies)
    {group : Execution.DeliveryNode} (noticed : group ∈ (queue.pruneEmptyGroups groups).2)
    : (∃ dependencies producer, NodeAt work group .group dependencies producer)
      ∧ ∃ node,
          (queue.pruneEmptyGroups groups).1.groupNode? group.ref = some node
          ∧ node.group.node = group
          ∧ (node.tasks ≠ [] ∨ node.failure.isSome = true) := by
  obtain ⟨recordDependencies, record⟩ :=
    registered.pruneEmptyGroups_notices groups candidates group noticed
  have known := generated.record_contributor record
    ((supported.pruneEmptyGroups groups).2 group noticed)
  obtain ⟨node, member, sameRef, contents⟩ :=
    queue.pruneEmptyGroups_keptContents groups unique group.ref (List.mem_map_of_mem noticed)
  obtain ⟨dependencies, nodeRecord⟩ :=
    (registered.pruneEmptyGroups groups) node member
  refine ⟨known, node, ?_, ?_, ?_⟩
  · simpa only [sameRef] using (unique.pruneEmptyGroups groups).groupNode?_of_mem member
  · obtain ⟨_, _, located⟩ := known
    exact generated.record_eq_node nodeRecord located sameRef
  · by_cases empty : node.tasks = []
    · right
      cases failure : node.failure with
      | none => simp [empty, failure] at contents
      | some count => rfl
    · exact .inl empty

-----------------------------------------------------------------------------------------
-- A successful flush passes its exact post-removal frontier through the same gate
-----------------------------------------------------------------------------------------

/-- A group-success carrier releases only real nodes with retained tasks or cached errors.
Witness: the actual task-removal fold preserves ref uniqueness, registry provenance, and
contributor support. Its child lookups supply candidate descriptors; the pruning theorem
then covers both direct children and descendants promoted through empty ancestor shells.
-/
theorem State.finishGroupSuccess_noticeContents {queue : State} {work}
    (generated : ExecutedWork work) (unique : queue.GroupRefsUnique)
    (registered : queue.GroupNodesMatchWork work)
    (supported
      : queue.GroupRefSupport
          (fun ref => ∃ dependencies, NodeHasDependencies work ref .group dependencies))
    (group : GroupNode) {child : Execution.DeliveryNode}
    (noticed : child ∈ (queue.finishGroupSuccess group).2.2.newGroups)
    : (∃ dependencies producer, NodeAt work child .group dependencies producer)
      ∧ ∃ node,
          (queue.finishGroupSuccess group).1.groupNode? child.ref = some node
          ∧ node.group.node = child
          ∧ (node.tasks ≠ [] ∨ node.failure.isSome = true) := by
  have loop (tasks : List Occurrence) (acc : State × List ExecutionGroupValue × NodeRefs)
      (refs : acc.1.GroupRefsUnique) (records : acc.1.GroupNodesMatchWork work)
      (contents : acc.1.GroupRefSupport
        (fun ref => ∃ dependencies, NodeHasDependencies work ref .group dependencies))
      : (tasks.foldl flushGroupTask acc).1.GroupRefsUnique
        ∧ (tasks.foldl flushGroupTask acc).1.GroupNodesMatchWork work
        ∧ (tasks.foldl flushGroupTask acc).1.GroupRefSupport
          (fun ref => ∃ dependencies, NodeHasDependencies work ref .group dependencies) := by
    induction tasks generalizing acc with
    | nil => exact ⟨refs, records, contents⟩
    | cons occurrence rest ih =>
        simp only [List.foldl_cons, flushGroupTask]
        split
        · exact ih acc refs records contents
        · exact ih _ (refs.removeTask occurrence) (records.removeTask occurrence)
            (contents.removeTask occurrence)
  let flushed := group.tasks.foldl flushGroupTask (queue, [], [])
  obtain ⟨flushedRefs, flushedRecords, flushedContents⟩ :=
    loop group.tasks (queue, [], []) unique registered supported
  let current : State := { flushed.1 with
    groupNodes := flushed.1.groupNodes.filter
      (fun node => node.group.node.ref != group.group.node.ref)
    rootGroups := flushed.1.rootGroups.filter (· != group.group.node.ref) }
  let children := group.childGroups.filterMap
    (fun ref => (current.groupNode? ref).map (fun node => node.group.node))
  have refs : current.GroupRefsUnique := by
    change ((flushed.1.groupNodes.filter
      (fun node => node.group.node.ref != group.group.node.ref)).map
        (fun node => node.group.node.ref)).Nodup
    have kept : ((flushed.1.groupNodes.map (fun node => node.group.node.ref)).filter
        (fun ref => ref != group.group.node.ref)).Nodup := flushedRefs.filter _
    simpa only [List.filter_map, Function.comp_def] using kept
  have records : current.GroupNodesMatchWork work :=
    fun node member => flushedRecords node (List.mem_filter.mp member).1
  have contents : current.GroupRefSupport
      (fun ref => ∃ dependencies, NodeHasDependencies work ref .group dependencies) :=
    ⟨fun node member => flushedContents.contents node (List.mem_filter.mp member).1,
      fun ref member => flushedContents.roots ref (List.mem_filter.mp member).1⟩
  have candidates : ∀ child ∈ children,
      ∃ dependencies, GroupRecordAt work child dependencies := by
    intro child member
    obtain ⟨ref, _, found⟩ := List.mem_filterMap.mp member
    cases lookup : current.groupNode? ref with
    | none => simp [lookup] at found
    | some node =>
        have same : node.group.node = child := by simpa [lookup] using found
        exact same ▸ records node (List.mem_of_find?_eq_some lookup)
  exact current.pruneEmptyGroups_noticeContents generated refs records contents children
    candidates noticed

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
