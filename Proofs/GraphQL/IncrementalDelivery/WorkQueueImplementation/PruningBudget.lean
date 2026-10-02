import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PrunedFrontierUniqueness
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureDescendants

/-! A live, unique pruning frontier cannot exhaust the implementation's traversal budget. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- The pending and retained frontier uses distinct live records
-----------------------------------------------------------------------------------------

/-- `remaining` and `kept` form a distinct, live, incoming-free frontier in `queue`.
The canonical `parents` map separates child branches without requiring task-bearing shells.
-/
private structure PruningFrontier (queue : State) (parents : Nat → Keys)
    (remaining kept : List Execution.DeliveryNode)
    : Prop where
  links : queue.ChildLinksCanonical parents
  children : queue.ChildGroupsUnique
  frontier : queue.GroupFrontier (remaining ++ kept)
  unique : ((remaining ++ kept).map Execution.DeliveryNode.key).Nodup
  live : ∀ group ∈ remaining ++ kept, ∃ node, queue.groupNode? group.key = some node

/-- Distinct retained keys cannot outnumber the queue's live records.
Witness: their lookup keys form a duplicate-free subset of the live key list.
-/
private theorem PruningFrontier.kept_le {queue parents remaining kept}
    (frame : PruningFrontier queue parents remaining kept)
    : kept.length ≤ queue.groupNodes.length := by
  have unique : (kept.map Execution.DeliveryNode.key).Nodup :=
    (List.nodup_append.mp (by simpa only [List.map_append] using frame.unique)).2.1
  have included : (kept.map Execution.DeliveryNode.key).Subset
      (queue.groupNodes.map (fun node => node.group.node.key)) := by
    intro key member
    obtain ⟨group, listed, same⟩ := List.mem_map.mp member
    obtain ⟨node, found⟩ := frame.live group (List.mem_append_right _ listed)
    exact List.mem_map.mpr ⟨node, List.mem_of_find?_eq_some found,
      (State.groupNode?_key found).trans same⟩
  simpa only [List.length_map] using unique.length_le_of_subset included

/-- Retaining the head only rotates the same certified frontier.
Witness: membership and key uniqueness are preserved by the rotation permutation.
-/
private theorem PruningFrontier.keep {queue parents group rest kept}
    (frame : PruningFrontier queue parents (group :: rest) kept)
    : PruningFrontier queue parents rest (kept ++ [group]) := by
  have members : ∀ child, child ∈ rest ++ (kept ++ [group]) ↔ child ∈ group :: (rest ++ kept) := by
    intro child
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    grind
  refine ⟨frame.links, frame.children, ?_, ?_, ?_⟩
  · intro child member; exact frame.frontier child ((members child).mp member)
  · have reordered := (List.perm_append_singleton group.key
      ((rest ++ kept).map Execution.DeliveryNode.key)).nodup_iff.mpr frame.unique
    simpa only [List.map_append, List.map_singleton, List.append_assoc] using reordered
  · intro child member; exact frame.live child ((members child).mp member)

/-- Pruning the head promotes a distinct live frontier and strictly removes a record.
Witness: canonical child links exclude collisions with the old frontier; successful
lookups supply live children, and incoming-freedom excludes the removed key from all of them.
-/
private theorem PruningFrontier.prune {queue parents group rest kept node}
    (frame : PruningFrontier queue parents (group :: rest) kept)
    (found : queue.groupNode? group.key = some node)
    : let promoted :=
        node.childGroups.filterMap
          (fun key => (queue.groupNode? key).map (fun child => child.group.node))
      let next : State :=
        {
          queue with
            groupNodes :=
              (queue.groupNodes.filter (fun entry => entry.group.node.key != group.key))
        }
      PruningFrontier next parents (promoted ++ rest) kept
      ∧ next.groupNodes.length < queue.groupNodes.length := by
  intro promoted next
  have present := List.mem_of_find?_eq_some found
  have same := State.groupNode?_key found
  have tailUnique : ((rest ++ kept).map Execution.DeliveryNode.key).Nodup :=
    (List.nodup_cons.mp frame.unique).2
  have tailFrontier : queue.GroupFrontier (rest ++ kept) :=
    fun child member => frame.frontier child (List.mem_cons_of_mem group member)
  have promotedUnique : (promoted.map Execution.DeliveryNode.key).Nodup :=
    (queue.childDescriptors_keys_sublist node.childGroups).nodup (frame.children node present)
  have promotedFrontier : next.GroupFrontier promoted := by
    simpa only [same] using frame.links.children_frontier present
  have retained {key other} (different : key ≠ group.key)
      (lookup : queue.groupNode? key = some other)
      : next.groupNode? key = some other := by
    change (queue.groupNodes.filter (fun entry => entry.group.node.key != group.key)).find?
      (fun entry => entry.group.node.key == key) = some other
    rw [State.groupNode?_filterKeys queue (fun key => key != group.key)]
    simpa [different] using lookup
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact fun entry member => frame.links entry (List.mem_filter.mp member).1
  · exact fun entry member => frame.children entry (List.mem_filter.mp member).1
  · intro child member parent live
    rcases List.mem_append.mp (show child ∈ promoted ++ (rest ++ kept)
      from by simpa only [List.append_assoc] using member) with newly | previous
    · exact promotedFrontier child newly parent live
    · exact tailFrontier child previous parent (List.mem_filter.mp live).1
  · rw [List.append_assoc, List.map_append]
    refine List.nodup_append.mpr ⟨promotedUnique, tailUnique, ?_⟩
    intro key newKey old oldKey sameKey
    obtain ⟨child, member, childKey⟩ := List.mem_map.mp newKey
    obtain ⟨other, included, otherKey⟩ := List.mem_map.mp oldKey
    exact tailFrontier other included node present
      ((childKey.trans (sameKey.trans otherKey.symm)) ▸
        (State.childDescriptors_member member).1)
  · intro child member
    rcases List.mem_append.mp (show child ∈ promoted ++ (rest ++ kept)
      from by simpa only [List.append_assoc] using member) with newly | previous
    · obtain ⟨linked, other, member, equal⟩ := State.childDescriptors_member newly
      have different : child.key ≠ group.key := by
        intro equal
        exact frame.frontier group List.mem_cons_self node present (equal ▸ linked)
      cases lookup : queue.groupNode? child.key with
      | none =>
          have absent := List.find?_eq_none.mp lookup other member
          simp [equal] at absent
      | some actual => exact ⟨actual, retained different lookup⟩
    · obtain ⟨other, lookup⟩ := frame.live child (List.mem_cons_of_mem _ previous)
      have different : child.key ≠ group.key := by
        intro equal
        exact (List.nodup_cons.mp frame.unique).1
          (List.mem_map.mpr ⟨child, previous, equal⟩)
      exact ⟨other, retained different lookup⟩
  · have bound := List.length_filter_le
      (fun entry : GroupNode => entry.group.node.key != group.key) queue.groupNodes
    have strict : next.groupNodes.length ≠ queue.groupNodes.length := by
      intro equal
      have kept := List.length_filter_eq_length_iff.mp equal node present
      simp [same] at kept
    change next.groupNodes.length ≤ queue.groupNodes.length at bound
    omega

-----------------------------------------------------------------------------------------
-- Extra fuel cannot change the result because the supplied budget cannot truncate
-----------------------------------------------------------------------------------------

/-- Any sufficient budget produces the same pruning result with arbitrary extra fuel.
Witness: removing a live shell decreases the map size; retaining a shell increases the
kept count. The invariant `live count < fuel + kept count` excludes fuel exhaustion.
-/
private theorem PruningFrontier.fuel_add {queue parents remaining kept fuel}
    (frame : PruningFrontier queue parents remaining kept)
    (enough : queue.groupNodes.length < fuel + kept.length) (extra : Nat)
    : State.pruneEmptyGroups.go (fuel + extra) queue remaining kept
      = State.pruneEmptyGroups.go fuel queue remaining kept := by
  induction fuel generalizing queue remaining kept with
  | zero => have bound := frame.kept_le; omega
  | succ fuel ih =>
      cases remaining with
      | nil => simp [State.pruneEmptyGroups.go, Nat.succ_add]
      | cons group rest =>
          obtain ⟨node, found⟩ := frame.live group List.mem_cons_self
          simp only [Nat.succ_add, State.pruneEmptyGroups.go, found]
          split
          · have next := frame.prune found
            exact ih next.1 (by have smaller := next.2; omega)
          · apply ih frame.keep
            simp only [List.length_append, List.length_singleton]
            omega

/-- Pruning a live unique frontier is independent of any additional traversal budget.
Witness: initial empty retained list and the checked concrete frontier invariant. Thus
taskless chains and branching cannot consume the budget before all candidates are handled.
-/
theorem State.pruneEmptyGroups_budget_complete {queue : State} {parents groups}
    (links : queue.ChildLinksCanonical parents) (children : queue.ChildGroupsUnique)
    (frontier : queue.GroupFrontier groups)
    (unique : (groups.map Execution.DeliveryNode.key).Nodup)
    (live : ∀ group ∈ groups, ∃ node, queue.groupNode? group.key = some node)
    (extra : Nat)
    : State.pruneEmptyGroups.go (queue.groupNodes.length + groups.length + 1 + extra)
        queue groups []
      = queue.pruneEmptyGroups groups := by
  apply PruningFrontier.fuel_add (parents := parents)
  · exact ⟨links, children, by simpa using frontier,
      by simpa using unique, by simpa using live⟩
  · simp only [List.length_nil]; omega

-----------------------------------------------------------------------------------------
-- Every surviving descendant remains covered by a retained frontier root
-----------------------------------------------------------------------------------------

/-- A pruning continuation cannot introduce a live record.
Witness: its only live-map mutation filters out the selected empty shell.
-/
private theorem prune_go_subset (fuel : Nat) (queue : State) (remaining kept)
    : (State.pruneEmptyGroups.go fuel queue remaining kept).1.groupNodes.Subset
        queue.groupNodes := by
  induction fuel generalizing queue remaining kept with
  | zero => exact List.Subset.refl _
  | succ fuel ih =>
      cases remaining with
      | nil => exact List.Subset.refl _
      | cons group rest =>
          unfold State.pruneEmptyGroups.go
          split
          · exact ih _ _ _
          · split
            · exact (ih _ _ _).trans (fun _ member => (List.mem_filter.mp member).1)
            · exact ih _ _ _

/-- Removing an incoming-free vertex preserves every path starting at a different key.
Witness: the first lookup survives, and no stored child edge can enter the removed key.
-/
theorem State.LiveDescendant.filter_frontier {queue : State} {root target removed : Nat}
    (path : queue.LiveDescendant root target)
    (different : root ≠ removed)
    (frontier : ∀ node ∈ queue.groupNodes, removed ∉ node.childGroups)
    : ({
            queue with
              groupNodes :=
                (queue.groupNodes.filter (fun node => node.group.node.key != removed))
          }
        : State).LiveDescendant
        root target := by
  induction path with
  | @self key node found =>
      apply State.LiveDescendant.self
      change (queue.groupNodes.filter (fun node => node.group.node.key != removed)).find?
        (fun node => node.group.node.key == key) = _
      rw [State.groupNode?_filterKeys queue (fun key => key != removed)]
      simpa [different] using found
  | @child key node child target found linked below ih =>
      have lookup : ({ queue with groupNodes := (queue.groupNodes.filter
          (fun node => node.group.node.key != removed)) } : State).groupNode? key = some node := by
        change (queue.groupNodes.filter (fun node => node.group.node.key != removed)).find?
          (fun node => node.group.node.key == key) = _
        rw [State.groupNode?_filterKeys queue (fun key => key != removed)]
        simpa [different] using found
      exact .child lookup linked (ih (fun equal =>
        frontier node (List.mem_of_find?_eq_some found) (equal ▸ linked)))

/-- Sufficient pruning preserves a covering frontier for every surviving descendant.
Witness: a removed candidate is replaced by its live children; unrelated paths survive
incoming-free filtering. The budget invariant excludes the only truncating branch.
-/
private theorem PruningFrontier.covers {queue parents remaining kept fuel target}
    (frame : PruningFrontier queue parents remaining kept)
    (enough : queue.groupNodes.length < fuel + kept.length)
    (covered : ∃ root ∈ remaining ++ kept, queue.LiveDescendant root.key target)
    (survives
      : ∃ node,
          (State.pruneEmptyGroups.go fuel queue remaining kept).1.groupNode? target
          = some node)
    : ∃ root ∈ (State.pruneEmptyGroups.go fuel queue remaining kept).2,
        (State.pruneEmptyGroups.go fuel queue remaining kept).1.LiveDescendant root.key
          target := by
  induction fuel generalizing queue remaining kept with
  | zero => have bound := frame.kept_le; omega
  | succ fuel ih =>
      cases remaining with
      | nil => exact covered
      | cons group rest =>
          obtain ⟨node, found⟩ := frame.live group List.mem_cons_self
          simp only [State.pruneEmptyGroups.go, found] at survives ⊢
          split
          · rename_i empty
            simp only [empty, ↓reduceIte] at survives
            let promoted := node.childGroups.filterMap
              (fun key => (queue.groupNode? key).map (fun child => child.group.node))
            let next : State :=
              { queue with groupNodes := (queue.groupNodes.filter
                  (fun entry => entry.group.node.key != group.key)) }
            have nextFrame := frame.prune found
            have different : target ≠ group.key := by
              obtain ⟨live, lookup⟩ := survives
              have included := prune_go_subset fuel next (promoted ++ rest) kept
                (List.mem_of_find?_eq_some lookup)
              have retained := (List.mem_filter.mp included).2
              have same := State.groupNode?_key lookup
              simpa only [bne_iff_ne, same] using retained
            have noIncoming := frame.frontier group List.mem_cons_self
            apply ih nextFrame.1 (by have smaller := nextFrame.2; omega) ?_ survives
            obtain ⟨root, member, path⟩ := covered
            by_cases same : root.key = group.key
            · rw [same] at path
              cases path with
              | self lookup => exact False.elim (different rfl)
              | @child key parent child target lookup linked below =>
                  have parentEq : parent = node := Option.some.inj (lookup.symm.trans found)
                  subst parent
                  obtain ⟨childNode, childFound⟩ := below.found
                  have childKey := State.groupNode?_key childFound
                  have candidate : childNode.group.node ∈ promoted :=
                    List.mem_filterMap.mpr ⟨child, linked, by simp [childFound]⟩
                  refine ⟨childNode.group.node,
                    List.mem_append_left kept (List.mem_append_left rest candidate), ?_⟩
                  rw [childKey]
                  exact below.filter_frontier
                    (fun equal =>
                      noIncoming node (List.mem_of_find?_eq_some found) (equal ▸ linked))
                    noIncoming
            · have tail : root ∈ rest ++ kept := by
                rcases List.mem_cons.mp member with equal | member
                · exact False.elim (same (congrArg Execution.DeliveryNode.key equal))
                · exact member
              refine ⟨root, ?_, path.filter_frontier same noIncoming⟩
              simpa only [List.append_assoc] using List.mem_append_right promoted tail
          · rename_i nonempty
            simp only [nonempty] at survives
            apply ih frame.keep (by simp only [List.length_append, List.length_singleton]; omega)
              ?_ survives
            obtain ⟨root, member, path⟩ := covered
            refine ⟨root, ?_, path⟩
            simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
            grind

/-- Every surviving descendant of a pruning input remains below an actual returned notice.
Witness: complete frontier traversal and live-path transport through taskless shell removal.
This is the converse coverage direction needed for terminal accounting, not just notice origin.
-/
theorem State.pruneEmptyGroups_surviving_descendant {queue : State}
    {parents groups target} (links : queue.ChildLinksCanonical parents)
    (children : queue.ChildGroupsUnique) (frontier : queue.GroupFrontier groups)
    (unique : (groups.map Execution.DeliveryNode.key).Nodup)
    (live : ∀ group ∈ groups, ∃ node, queue.groupNode? group.key = some node)
    (covered : ∃ root ∈ groups, queue.LiveDescendant root.key target)
    (survives : ∃ node, (queue.pruneEmptyGroups groups).1.groupNode? target = some node)
    : ∃ root ∈ (queue.pruneEmptyGroups groups).2,
        (queue.pruneEmptyGroups groups).1.LiveDescendant root.key target := by
  apply PruningFrontier.covers (parents := parents) (survives := survives)
  · exact ⟨links, children, by simpa using frontier,
      by simpa using unique, by simpa using live⟩
  · simp only [List.length_nil]; omega
  · simpa using covered

-----------------------------------------------------------------------------------------
-- Surviving roots also keep their original descendant paths
-----------------------------------------------------------------------------------------

/-- A surviving path root retains its entire path through a certified pruning traversal.
Witness: every removed candidate is incoming-free, so removing a different root cannot
break the path. Endpoint survival excludes deletion of its own root at every iteration.
-/
private theorem PruningFrontier.paths {queue parents remaining kept fuel root target}
    (frame : PruningFrontier queue parents remaining kept)
    (path : queue.LiveDescendant root target)
    (survives
      : ∃ node,
          (State.pruneEmptyGroups.go fuel queue remaining kept).1.groupNode? root
          = some node)
    : (State.pruneEmptyGroups.go fuel queue remaining kept).1.LiveDescendant root
        target := by
  induction fuel generalizing queue remaining kept with
  | zero => exact path
  | succ fuel ih =>
      cases remaining with
      | nil => exact path
      | cons group rest =>
          obtain ⟨node, found⟩ := frame.live group List.mem_cons_self
          simp only [State.pruneEmptyGroups.go, found] at survives ⊢
          split
          · rename_i empty
            simp only [empty, ↓reduceIte] at survives
            let promoted := node.childGroups.filterMap
              (fun key => (queue.groupNode? key).map (fun child => child.group.node))
            let next : State :=
              { queue with groupNodes := (queue.groupNodes.filter
                  (fun entry => entry.group.node.key != group.key)) }
            have different : root ≠ group.key := by
              obtain ⟨live, lookup⟩ := survives
              have included := prune_go_subset fuel next (promoted ++ rest) kept
                (List.mem_of_find?_eq_some lookup)
              have retained := (List.mem_filter.mp included).2
              simpa only [bne_iff_ne, State.groupNode?_key lookup] using retained
            exact ih (frame.prune found).1
              (path.filter_frontier different (frame.frontier group List.mem_cons_self))
              survives
          · rename_i nonempty
            simp only [nonempty] at survives
            exact ih frame.keep path survives

/-- Pruning preserves every old path whose starting group survives.
Witness: the same live unique frontier invariant used for complete pruning coverage;
incoming-free shell removals cannot cut into a path from a different surviving root.
-/
theorem State.LiveDescendant.pruneEmptyGroups {queue : State} {parents groups root target}
    (path : queue.LiveDescendant root target)
    (links : queue.ChildLinksCanonical parents) (children : queue.ChildGroupsUnique)
    (frontier : queue.GroupFrontier groups)
    (unique : (groups.map Execution.DeliveryNode.key).Nodup)
    (live : ∀ group ∈ groups, ∃ node, queue.groupNode? group.key = some node)
    (survives : ∃ node, (queue.pruneEmptyGroups groups).1.groupNode? root = some node)
    : (queue.pruneEmptyGroups groups).1.LiveDescendant root target := by
  apply PruningFrontier.paths (parents := parents) (path := path) (survives := survives)
  exact ⟨
    links,
    children,
    by simpa using frontier,
    by simpa using unique,
    by simpa using live
  ⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
