import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ChildUniqueness

/-! Taskless-shell pruning retains a duplicate-free group-notice frontier. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Lookup filters stale child links without changing their refs
-----------------------------------------------------------------------------------------

/-- Child lookup only removes refs from the supplied list; it never changes their order.
Witness: each successful group lookup returns its requested ref, and failed lookups vanish.
-/
theorem State.childDescriptors_refs_sublist (queue : State) (refs : NodeRefs)
    : ((refs.filterMap
          (fun ref => (queue.groupNode? ref).map (fun node => node.group.node))).map
        Execution.DeliveryNode.ref).Sublist
        refs := by
  induction refs with
  | nil => simp
  | cons ref rest ih =>
      cases found : queue.groupNode? ref with
      | none => simpa [found] using ih.cons ref
      | some node =>
          simpa [found, State.groupNode?_ref found] using ih.cons_cons ref

/-- Every looked-up child descriptor retains its original ref and live record.
Witness: invert filterMap and the successful lookup; stale links contribute no descriptor.
-/
theorem State.childDescriptors_member {queue : State} {refs : NodeRefs}
    {child : Execution.DeliveryNode}
    (member
      : child
        ∈ refs.filterMap
            (fun ref => (queue.groupNode? ref).map (fun node => node.group.node)))
    : child.ref ∈ refs ∧ ∃ node ∈ queue.groupNodes, node.group.node = child := by
  obtain ⟨ref, linked, selected⟩ := List.mem_filterMap.mp member
  cases found : queue.groupNode? ref with
  | none => simp [found] at selected
  | some node =>
      have same : node.group.node = child := by simpa [found] using selected
      exact ⟨same ▸ State.groupNode?_ref found ▸ linked,
        node, List.mem_of_find?_eq_some found, same⟩

-----------------------------------------------------------------------------------------
-- A candidate frontier has no incoming edge from any remaining live group
-----------------------------------------------------------------------------------------

/-- No live group in `queue` has a stored edge into the candidate/kept list `groups`.
This local traversal fact is independent of tasks, failures, source events, and admission.
-/
def State.GroupFrontier (queue : State) (groups : List Execution.DeliveryNode) : Prop :=
  ∀ child ∈ groups, ∀ parent ∈ queue.groupNodes, child.ref ∉ parent.childGroups

/-- Removing the parent of looked-up children makes those children frontier candidates.
Witness: canonical links give each child a single parent ref, and that ref is filtered out.
No acyclicity or task-bearing premise is needed for intermediate shell records.
-/
theorem State.ChildLinksCanonical.children_frontier {queue : State} {parents}
    (links : queue.ChildLinksCanonical parents) {node : GroupNode}
    (present : node ∈ queue.groupNodes)
    : let children :=
        node.childGroups.filterMap
          (fun ref => (queue.groupNode? ref).map (fun child => child.group.node))
      ({
            queue with
              groupNodes :=
                queue.groupNodes.filter
                  (fun entry => entry.group.node.ref != node.group.node.ref)
          }
        : State).GroupFrontier
        children := by
  intro children child member other live incoming
  have original := List.mem_filter.mp live
  have parent := links node present child.ref (State.childDescriptors_member member).1
  have otherParent := links other original.1 child.ref incoming
  have same : other.group.node.ref = node.group.node.ref :=
    Option.some.inj (otherParent.symm.trans parent)
  have different : other.group.node.ref ≠ node.group.node.ref := by
    simpa only [bne_iff_ne] using original.2
  exact different same

-----------------------------------------------------------------------------------------
-- Pruning maintains a duplicate-free frontier through every internal work-list step
-----------------------------------------------------------------------------------------

/-- Pruning a unique incoming-free frontier returns unique group-notice refs.
Witness: live child lists are unique, and no child being promoted can already be pending
or kept, since its current parent would be an incoming edge. Canonical parent refs make
the promoted children incoming-free after that parent is removed. Missing links are skipped.
-/
theorem State.pruneEmptyGroups_unique_frontier {queue : State} {parents groups}
    (links : queue.ChildLinksCanonical parents) (children : queue.ChildGroupsUnique)
    (frontier : queue.GroupFrontier groups)
    (unique : (groups.map Execution.DeliveryNode.ref).Nodup)
    : ((queue.pruneEmptyGroups groups).2.map Execution.DeliveryNode.ref).Nodup := by
  have loop (fuel : Nat) (current : State) (remaining kept : List Execution.DeliveryNode)
      (links : current.ChildLinksCanonical parents) (children : current.ChildGroupsUnique)
      (frontier : current.GroupFrontier (remaining ++ kept))
      (unique : ((remaining ++ kept).map Execution.DeliveryNode.ref).Nodup)
      : ((State.pruneEmptyGroups.go fuel current remaining kept).2.map
          Execution.DeliveryNode.ref).Nodup := by
    induction fuel generalizing current remaining kept with
    | zero =>
        change (kept.map Execution.DeliveryNode.ref).Nodup
        exact (List.nodup_append.mp (by simpa only [List.map_append] using unique)).2.1
    | succ fuel ih =>
        cases remaining with
        | nil =>
            change (kept.map Execution.DeliveryNode.ref).Nodup
            simpa only [List.nil_append] using unique
        | cons group rest =>
            have tailUnique : ((rest ++ kept).map Execution.DeliveryNode.ref).Nodup :=
              (List.nodup_cons.mp unique).2
            have tailFrontier : current.GroupFrontier (rest ++ kept) :=
              fun child member => frontier child (List.mem_cons_of_mem group member)
            unfold State.pruneEmptyGroups.go
            split
            · exact ih current rest kept links children tailFrontier tailUnique
            · rename_i node found
              have present := List.mem_of_find?_eq_some found
              have same := State.groupNode?_ref found
              split
              · let promoted := node.childGroups.filterMap (fun ref =>
                  (current.groupNode? ref).map (fun child => child.group.node))
                let next : State := { current with
                  groupNodes := current.groupNodes.filter
                    (fun entry => entry.group.node.ref != group.ref) }
                have nextLinks : next.ChildLinksCanonical parents :=
                  fun entry member => links entry (List.mem_filter.mp member).1
                have nextChildren : next.ChildGroupsUnique :=
                  fun entry member => children entry (List.mem_filter.mp member).1
                have promotedUnique : (promoted.map Execution.DeliveryNode.ref).Nodup :=
                  (current.childDescriptors_refs_sublist node.childGroups).nodup
                    (children node present)
                have promotedFrontier : next.GroupFrontier promoted := by
                  have result := links.children_frontier present
                  simpa only [same] using result
                apply ih next (promoted ++ rest) kept nextLinks nextChildren
                · intro child member parent live
                  rcases List.mem_append.mp (show child ∈ promoted ++ (rest ++ kept)
                    from by simpa only [List.append_assoc] using member) with newly | previous
                  · exact promotedFrontier child newly parent live
                  · exact tailFrontier child previous parent (List.mem_filter.mp live).1
                · rw [List.append_assoc, List.map_append]
                  apply List.nodup_append.mpr
                  refine ⟨promotedUnique, tailUnique, ?_⟩
                  intro ref newRef old oldRef sameRef
                  obtain ⟨child, member, childRef⟩ := List.mem_map.mp newRef
                  obtain ⟨other, included, otherRef⟩ := List.mem_map.mp oldRef
                  have linked := (State.childDescriptors_member member).1
                  exact tailFrontier other included node present
                    ((childRef.trans (sameRef.trans otherRef.symm)) ▸ linked)
              · apply ih current rest (kept ++ [group]) links children
                · intro child member
                  have included : child ∈ group :: (rest ++ kept) := by
                    simpa only [List.mem_append, List.mem_singleton, List.mem_cons,
                      List.not_mem_nil, or_false, false_or, or_assoc, or_left_comm,
                      or_comm]
                      using member
                  exact frontier child included
                · have reordered := (List.perm_append_singleton group.ref
                    ((rest ++ kept).map Execution.DeliveryNode.ref)).nodup_iff.mpr
                      unique
                  simpa only [List.map_append, List.map_singleton, List.append_assoc]
                    using reordered
  exact loop _ queue groups [] links children (by simpa using frontier)
    (by simpa using unique)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
