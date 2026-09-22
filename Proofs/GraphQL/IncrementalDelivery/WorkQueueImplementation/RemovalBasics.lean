import GraphQL.IncrementalDelivery.WorkQueueImplementation

/-! Root removal facts independent of healthy accounting and generated-work metadata. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Removal traversal never forgets a key already accumulated.
Witness: induction on the live-node budget and stale-key frontier.
-/
theorem State.removeGroup_collect_retains
    (fuel : Nat) (queue : State) (pending removed : Keys)
    : removed.Subset (State.removeGroup.collect fuel queue pending removed) := by
  induction fuel generalizing pending removed with
  | zero => simp only [State.removeGroup.collect]; intro key member; exact member
  | succ fuel ih =>
      induction pending generalizing removed with
      | nil => simp only [State.removeGroup.collect]; intro key member; exact member
      | cons head rest tailIH =>
          intro key member
          unfold State.removeGroup.collect
          cases found : queue.groupNode? head with
          | none => exact tailIH removed member
          | some node =>
              exact ih (node.childGroups ++ rest) (head :: removed) (by simp [member])

/-- Every newly collected removal key names a node present before traversal.
Witness: the collector appends a key only after a successful live-node lookup. -/
theorem State.removeGroup_collect_mem (fuel : Nat) (queue : State)
    (pending removed : Keys) {key : Nat}
    (member : key ∈ State.removeGroup.collect fuel queue pending removed)
    : key ∈ removed ∨ ∃ node ∈ queue.groupNodes, node.group.node.key = key := by
  induction fuel generalizing pending removed with
  | zero => exact Or.inl (by simpa only [State.removeGroup.collect] using member)
  | succ fuel ih =>
      induction pending generalizing removed with
      | nil => exact Or.inl (by simpa only [State.removeGroup.collect] using member)
      | cons head rest tailIH =>
          unfold State.removeGroup.collect at member
          cases found : queue.groupNode? head with
          | none => exact tailIH removed (by simpa only [found] using member)
          | some node =>
              have next := ih (node.childGroups ++ rest) (head :: removed)
                (by simpa only [found] using member)
              rcases next with old | live
              · rcases List.mem_cons.mp old with same | old
                · subst key
                  exact Or.inr ⟨node, List.mem_of_find?_eq_some found,
                    beq_iff_eq.mp (List.find?_some
                      (p := fun candidate : GroupNode => candidate.group.node.key == head)
                      found)⟩
                · exact Or.inl old
              · exact Or.inr live

/-- Removing a group clears its own live lookup, including an already missing key.
Witness: a found root enters the removal accumulator immediately, and all equal keys
are filtered out. No forest or descendant-coverage premise is needed for the root.
-/
theorem State.removeGroup_ownGroupAbsent (queue : State) (key : Nat)
    : (queue.removeGroup key).groupNode? key = none := by
  apply List.find?_eq_none.mpr
  intro node member selected
  let removed := State.removeGroup.collect (queue.groupNodes.length + 1) queue [key] []
  change node ∈ queue.groupNodes.filter
    (fun node => !removed.contains node.group.node.key) at member
  obtain ⟨old, kept⟩ := List.mem_filter.mp member
  cases found : queue.groupNode? key with
  | none => exact (List.find?_eq_none.mp found) node old selected
  | some root =>
      have same : node.group.node.key = key := beq_iff_eq.mp selected
      have absent : key ∉ removed := by simpa [same] using kept
      apply absent
      unfold removed
      simp only [State.removeGroup.collect, found, List.append_nil]
      exact State.removeGroup_collect_retains queue.groupNodes.length queue
        root.childGroups [key] (by simp)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
