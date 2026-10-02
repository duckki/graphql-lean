import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.AncestorCertificates
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PromotionPaths
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RecordInvalidation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupPublication
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupPruningNotices
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupClosureAccounting

/-! Protected roots cannot be removed by pruning another supported group's descendants. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (ExecutionGroupValue)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Stored child paths follow full generated ancestry, including taskless intermediate nodes
-----------------------------------------------------------------------------------------

/-- A stored live path starts at the target itself or one of its full defer ancestors.
Witness: every edge names the child's immediate parent; generated transitivity composes
those edges through registration records, including taskless intermediate shells.
-/
theorem State.LiveDescendant.ancestor_or_self {queue : State} {work parents root target}
    (path : queue.LiveDescendant root target) (generated : ExecutedWork work)
    (records : queue.GroupNodesMatchWork work) (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    {node dependencies} (known : GroupRecordAt work node dependencies)
    (same : node.key = target)
    : root = target ∨ root ∈ dependencies := by
  induction path with
  | self found => exact .inl rfl
  | @child root owner child target found linked below ih =>
      obtain ⟨childNode, childFound⟩ := below.found
      obtain ⟨childDependencies, childKnown⟩ := records childNode
        (List.mem_of_find?_eq_some childFound)
      have head : childDependencies.head? = some root := by
        rw [canonical _ _ childKnown, State.groupNode?_key childFound]
        exact (links owner (List.mem_of_find?_eq_some found) child linked).trans
          (congrArg some (State.groupNode?_key found))
      have member : root ∈ childDependencies := by
        cases childDependencies with
        | nil => cases head
        | cons first rest =>
            have equal := Option.some.inj head
            simp [equal]
      apply Or.inr
      rcases ih same with equal | ancestor
      · have equalDependencies : childDependencies = dependencies := by
          rw [canonical _ _ childKnown, canonical _ _ known,
            State.groupNode?_key childFound, same, equal]
        exact equalDependencies ▸ member
      · exact generated.groupRecordAncestors_trans known childKnown
          ((State.groupNode?_key childFound).symm ▸ ancestor) member

/-- A supported live ancestor cannot reach a distinct ancestor-protected target.
Witness: a nontrivial path makes its contributing starting key a retired ancestor of the
target, contradicting the starting lookup. Intermediate records need not have tasks.
-/
theorem State.AncestorsRetired.supported_path_eq {queue : State}
    {work parents root target} (protectedRoot : queue.AncestorsRetired work target)
    (generated : ExecutedWork work) (records : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    (path : queue.LiveDescendant root target) {occurrence owners}
    (task : TaskHasOwners work occurrence owners) (contributes : root ∈ owners)
    : root = target := by
  obtain ⟨node, found⟩ := path.found
  have endFound : ∀ {first last}, queue.LiveDescendant first last →
      ∃ entry, queue.groupNode? last = some entry := by
    intro first last steps
    induction steps with
    | self found => exact ⟨_, found⟩
    | child _ _ _ ih => exact ih
  obtain ⟨targetNode, atTarget⟩ := endFound path
  obtain ⟨dependencies, known⟩ := records targetNode (List.mem_of_find?_eq_some atTarget)
  rcases path.ancestor_or_self generated records links canonical known
      (State.groupNode?_key atTarget) with same | ancestor
  · exact same
  · have retired := protectedRoot targetNode.group.node dependencies known
      (State.groupNode?_key atTarget) root ancestor occurrence owners task contributes
    exact False.elim (retired.2 (List.mem_map.mpr
      ⟨node, List.mem_of_find?_eq_some found, State.groupNode?_key found⟩))

-----------------------------------------------------------------------------------------
-- Pruning can remove only a key reachable from its supplied frontier
-----------------------------------------------------------------------------------------

/-- Pruning preserves a live key outside every candidate's original live subtree.
Witness: follow the shrinking queue with retained edge provenance. A removed candidate
cannot be the protected key; any promoted child path would extend to an excluded old
candidate path. This argument does not require every intermediate shell to contribute.
-/
theorem State.pruneEmptyGroups_preserves_outside {queue : State} {key : Nat}
    (live : key ∈ queue.groupNodes.map (fun node => node.group.node.key))
    (groups : List Execution.DeliveryNode)
    (outside : ∀ group ∈ groups, ¬queue.LiveDescendant group.key key)
    : key
      ∈ (queue.pruneEmptyGroups groups).1.groupNodes.map
          (fun node => node.group.node.key) := by
  have loop (fuel : Nat) (current : State) (remaining kept : List Execution.DeliveryNode)
      (edges : current.GroupEdgesFrom queue)
      (present : key ∈ current.groupNodes.map (fun node => node.group.node.key))
      (excluded : ∀ group ∈ remaining, ¬queue.LiveDescendant group.key key)
      : key ∈ (State.pruneEmptyGroups.go fuel current remaining kept).1.groupNodes.map
          (fun node => node.group.node.key) := by
    induction fuel generalizing current remaining kept with
    | zero => exact present
    | succ fuel ih =>
        cases remaining with
        | nil => exact present
        | cons group rest =>
            have tail := fun next member => excluded next (List.mem_cons_of_mem _ member)
            unfold State.pruneEmptyGroups.go
            split
            · exact ih _ _ _ edges present tail
            · rename_i node found
              have different : key ≠ group.key := by
                intro equal
                apply excluded group List.mem_cons_self
                rw [equal]
                exact edges.liveDescendant (.self found)
              split
              · refine ih _ _ _
                  ((current.filterKeys_groupEdgesFrom (· != group.key)).trans edges) ?_ ?_
                · obtain ⟨entry, member, same⟩ := List.mem_map.mp present
                  exact List.mem_map.mpr ⟨entry,
                    List.mem_filter.mpr ⟨member, by simp [same, different]⟩, same⟩
                · intro candidate member path
                  rcases List.mem_append.mp member with child | old
                  · obtain ⟨childKey, linked, selected⟩ := List.mem_filterMap.mp child
                    cases childFound : current.groupNode? childKey with
                    | none => simp [childFound] at selected
                    | some childNode =>
                        have same : childNode.group.node = candidate := by
                          simpa [childFound] using selected
                        have keyEq := (congrArg Execution.DeliveryNode.key same).symm.trans
                          (State.groupNode?_key childFound)
                        obtain ⟨original, originalFound, childEq⟩ := edges _ _ found
                        exact excluded group List.mem_cons_self
                          (.child originalFound (childEq ▸ linked) (keyEq ▸ path))
                  · exact tail candidate old path
              · exact ih _ _ _ edges present tail
  exact loop _ queue groups [] (.refl queue) live outside

-----------------------------------------------------------------------------------------
-- An actual successful closure preserves unrelated protected roots and pending releases
-----------------------------------------------------------------------------------------

/-- Successful flushing preserves every live key outside the closing group's subtree.
Witness: flushing changes only task memberships; the own-key filter cannot remove the
target, and every pruning candidate is a stored child of the actual closing descriptor.
-/
theorem State.finishGroupSuccess_preserves_outside {queue : State} {key : Nat}
    (live : key ∈ queue.groupNodes.map (fun node => node.group.node.key))
    {group : GroupNode} (found : queue.groupNode? group.group.node.key = some group)
    (outside : ¬queue.LiveDescendant group.group.node.key key)
    : key
      ∈ (queue.finishGroupSuccess group).1.groupNodes.map
          (fun node => node.group.node.key) := by
  have different : key ≠ group.group.node.key := by
    intro same
    exact outside (same.symm ▸ State.LiveDescendant.self found)
  have loop (tasks : List Occurrence) (acc : State × List ExecutionGroupValue × Keys)
      (edges : acc.1.GroupEdgesFrom queue)
      (keys : acc.1.groupNodes.map (fun node => node.group.node.key)
        = queue.groupNodes.map (fun node => node.group.node.key))
      : (tasks.foldl flushGroupTask acc).1.GroupEdgesFrom queue
        ∧ (tasks.foldl flushGroupTask acc).1.groupNodes.map (fun node => node.group.node.key)
          = queue.groupNodes.map (fun node => node.group.node.key) := by
    induction tasks generalizing acc with
    | nil => exact ⟨edges, keys⟩
    | cons occurrence rest ih =>
        rw [List.foldl_cons]
        unfold flushGroupTask
        split
        · exact ih _ edges keys
        · exact ih _ ((acc.1.removeTask_groupEdgesFrom occurrence).trans edges)
            (by simpa only [State.removeTask, List.map_map, Function.comp_def] using keys)
  let flushed := (group.tasks.foldl flushGroupTask (queue, [], [])).1
  obtain ⟨edges, keys⟩ := loop group.tasks (queue, [], []) (.refl queue) rfl
  let current : State := { flushed with
    groupNodes := flushed.groupNodes.filter
      (fun node => node.group.node.key != group.group.node.key)
    rootGroups := flushed.rootGroups.filter (· != group.group.node.key) }
  have currentEdges : current.GroupEdgesFrom queue :=
    (flushed.filterKeys_groupEdgesFrom (· != group.group.node.key)).trans edges
  have present : key ∈ current.groupNodes.map (fun node => node.group.node.key) := by
    obtain ⟨node, member, same⟩ := List.mem_map.mp (keys.symm ▸ live)
    exact List.mem_map.mpr ⟨node,
      List.mem_filter.mpr ⟨member, by simp [same, different]⟩, same⟩
  apply State.pruneEmptyGroups_preserves_outside present
  change ∀ candidate ∈ group.childGroups.filterMap
      (fun child => (current.groupNode? child).map (fun node => node.group.node)),
    ¬current.LiveDescendant candidate.key key
  intro candidate member path
  obtain ⟨child, linked, selected⟩ := List.mem_filterMap.mp member
  cases lookup : current.groupNode? child with
  | none => simp [lookup] at selected
  | some node =>
      have same : node.group.node = candidate := by simpa [lookup] using selected
      have keyEq := (congrArg Execution.DeliveryNode.key same).symm.trans
        (State.groupNode?_key lookup)
      exact outside (.child found linked (keyEq ▸ currentEdges.liveDescendant path))

/-- Closing a supported group preserves each different live ancestor-protected key.
Witness: a path from that contributing group would contradict the target's retired
ancestry; the outside-subtree preservation theorem then protects the live record.
-/
theorem State.AncestorsRetired.supported_finishGroupSuccess_present
    {queue : State} {work parents key}
    (protectedRoot : queue.AncestorsRetired work key)
    (generated : ExecutedWork work) (records : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    (live : key ∈ queue.groupNodes.map (fun node => node.group.node.key))
    {group : GroupNode} (found : queue.groupNode? group.group.node.key = some group)
    {occurrence owners} (task : TaskHasOwners work occurrence owners)
    (contributes : group.group.node.key ∈ owners) (different : group.group.node.key ≠ key)
    : key
      ∈ (queue.finishGroupSuccess group).1.groupNodes.map
          (fun node => node.group.node.key) :=
  State.finishGroupSuccess_preserves_outside live found
    (fun path =>
      different
        (protectedRoot.supported_path_eq generated records links canonical
          path task contributes))

/-- A supported active group's closure preserves every other active root's live record.
Witness: root support supplies a real contributor for the closing key; the exact root
filter excludes that key, and retirement protection preserves every surviving root.
-/
theorem State.RootGroupsPresent.supported_finishGroupSuccess {queue : State}
    {work parents} (present : queue.RootGroupsPresent) (generated : ExecutedWork work)
    (roots : queue.RootAncestorsRetired work) (records : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    (support
      : queue.GroupKeySupport
          (fun key => ∃ dependencies, NodeHasDependencies work key .group dependencies))
    {group : GroupNode} (found : queue.groupNode? group.group.node.key = some group)
    (active : group.group.node.key ∈ queue.rootGroups)
    : (queue.finishGroupSuccess group).1.RootGroupsPresent := by
  obtain ⟨dependencies, node, producer, known, same⟩ := support.roots _ active
  obtain ⟨occurrence, owners, payload, task, contributes⟩ := known.group_task
  intro key member
  rw [queue.finishGroupSuccess_rootGroups group] at member
  obtain ⟨old, different⟩ := List.mem_filter.mp member
  apply (roots key old).supported_finishGroupSuccess_present generated records links canonical
    (present key old) found ⟨producer, payload, task⟩ (same ▸ contributes)
  intro equal
  simp [equal] at different

/-- A newly released group cannot already be a protected active root.
Witness: its stored release path starts at the supported closing group. An old root's
retirement certificate forces equality, but the closing key is absent after the flush.
Taskless intermediate records are permitted along that path.
-/
theorem State.finishGroupSuccess_supported_release_inactive
    {queue : State} {work parents} (generated : ExecutedWork work)
    (keys : queue.GroupKeysUnique) (roots : queue.RootAncestorsRetired work)
    (records : queue.GroupNodesMatchWork work) (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    (support
      : queue.GroupKeySupport
          (fun key => ∃ dependencies, NodeHasDependencies work key .group dependencies))
    (registered : queue.LiveGroupsRegistered)
    {group : GroupNode} (found : queue.groupNode? group.group.node.key = some group)
    (active : group.group.node.key ∈ queue.rootGroups)
    {child} (noticed : child ∈ (queue.finishGroupSuccess group).2.2.newGroups)
    : child.key ∉ queue.rootGroups := by
  intro old
  obtain ⟨dependencies, node, producer, known, same⟩ := support.roots _ active
  obtain ⟨occurrence, owners, payload, task, contributes⟩ := known.group_task
  have path := State.finishGroupSuccess_released_descendant found noticed
  have equal := (roots child.key old).supported_path_eq generated records links canonical
    path ⟨producer, payload, task⟩ (same ▸ contributes)
  obtain ⟨_, retained, lookup, _, _⟩ :=
    queue.finishGroupSuccess_noticeContents generated keys records support group noticed
  have retired := queue.finishGroupSuccess_retires group
    (registered group (List.mem_of_find?_eq_some found))
  have absent := retired.lookup_none
  rw [equal, lookup] at absent
  contradiction

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
