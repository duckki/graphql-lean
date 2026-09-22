import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PromotionPaths

/-! Live-path transport using the already-derived finite removal forest. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Single-vertex filters preserve paths that cannot pass through the removed key
-----------------------------------------------------------------------------------------

/-- Removing a key outside the path's possible ancestors preserves the whole path.
Witness: the removed key cannot equal any path vertex, since the remaining suffix would
then witness the excluded descendant relation. No forest assumption is needed here.
-/
theorem State.LiveDescendant.filter_outside {queue : State} {root target removed}
    (path : queue.LiveDescendant root target)
    (outside : ¬queue.LiveDescendant removed target)
    : ({
            queue with
              groupNodes :=
                (queue.groupNodes.filter (fun node => node.group.node.key != removed))
          }
        : State).LiveDescendant
        root target := by
  induction path with
  | @self key node found =>
      have different : key ≠ removed := fun same => outside (same ▸ .self found)
      apply State.LiveDescendant.self
      change (queue.groupNodes.filter (fun node => node.group.node.key != removed)).find?
        (fun node => node.group.node.key == key) = some node
      rw [State.groupNode?_filterKeys queue (fun key => key != removed)]
      simpa [different] using found
  | @child key node child target found linked below ih =>
      have different : key ≠ removed :=
        fun same => outside (same ▸ State.LiveDescendant.child found linked below)
      apply State.LiveDescendant.child (node := node)
      · change (queue.groupNodes.filter (fun node => node.group.node.key != removed)).find?
          (fun node => node.group.node.key == key) = some node
        rw [State.groupNode?_filterKeys queue (fun key => key != removed)]
        simpa [different] using found
      · exact linked
      · exact ih outside

/-- Removing a smaller key preserves every path in an increasing live forest.
Witness: each child edge increases the key, so all later vertices remain above the filter.
-/
theorem State.LiveDescendant.filter_lower {queue : State} {parents root target removed}
    (path : queue.LiveDescendant root target) (forest : queue.RemovalForest parents)
    (lower : removed < root)
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
        (fun node => node.group.node.key == key) = some node
      rw [State.groupNode?_filterKeys queue (fun key => key != removed)]
      simpa [Nat.ne_of_gt lower] using found
  | @child key node child target found linked below ih =>
      obtain ⟨next, nextFound⟩ := below.found
      have step := forest.increasing (List.mem_of_find?_eq_some found)
        (List.mem_of_find?_eq_some nextFound) (State.groupNode?_key nextFound ▸ linked)
      rw [State.groupNode?_key found, State.groupNode?_key nextFound] at step
      apply State.LiveDescendant.child (node := node)
      · change (queue.groupNodes.filter (fun node => node.group.node.key != removed)).find?
          (fun node => node.group.node.key == key) = some node
        rw [State.groupNode?_filterKeys queue (fun key => key != removed)]
        simpa [Nat.ne_of_gt lower] using found
      · exact linked
      · exact ih (Nat.lt_trans lower step)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
