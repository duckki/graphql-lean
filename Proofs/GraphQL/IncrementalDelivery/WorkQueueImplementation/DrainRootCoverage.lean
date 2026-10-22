import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupClosureCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.DrainNormalForm

/-! Successful draining with cached-failure startup preserves surviving group coverage. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Compose the actual recursive mixed drain, retaining exact live paths
-----------------------------------------------------------------------------------------

/-- Every old root-covered group that survives a mixed drain remains root-covered.
Witness: a single concrete invariant combines forest preservation, edge provenance, and
coverage. Success promotes surviving descendants; failure removes subtrees atomically.
No event-admission, settled-value, or host-progress premise is needed.
-/
theorem State.drainReadyGroups_root_coverage {queue : State} {parents}
    (unique : queue.GroupRefsUnique) (forest : queue.RemovalForest parents)
    (available : List (Occurrence × Nat) := [])
    : ∀ target,
        (∃ root ∈ queue.rootGroups, queue.LiveDescendant root target)
        → (∃ node, (queue.drainReadyGroups available).1.groupNode? target = some node)
        → ∃ root ∈ (queue.drainReadyGroups available).1.rootGroups,
            (queue.drainReadyGroups available).1.LiveDescendant root target := by
  let property (current : State) := current.GroupRefsUnique ∧ current.RemovalForest parents
    ∧ ∀ target,
      (∃ root ∈ queue.rootGroups, queue.LiveDescendant root target)
      → (∃ node, current.groupNode? target = some node)
      → ∃ root ∈ current.rootGroups, current.LiveDescendant root target
  have result :=
    State.drainReadyGroups_preserves property (available := available)
      (fun current node prior member _ _ => by
        let released := current.finishGroupSuccess node
        refine ⟨(prior.1.finishGroupSuccess node).startNewWork _ available,
          (prior.2.1.finishGroupSuccess node).startNewWork _ available, ?_⟩
        intro target covered survives
        have retained : ∃ child, released.1.groupNode? target = some child :=
          State.groupNode?_exists_before_subset
            (released.1.startNewWork_groupNodes_sublist released.2.2 available).subset survives
        obtain ⟨child, found⟩ := retained
        obtain ⟨old, oldFound, _⟩ :=
          (current.finishGroupSuccess_descendants node).1 _ _ found
        exact State.finishGroupSuccess_root_coverage prior.2.1
          (prior.1.groupNode?_of_mem member) (prior.2.2 target covered ⟨old, oldFound⟩)
          available survives)
      (show property queue from ⟨unique, forest, fun _ covered _ => covered⟩)
  exact result.2.2

/-- Empty post-drain roots rule out every previously covered surviving live group.
Witness: the generic drain coverage theorem would otherwise produce an actual root ref.
This is concrete endpoint coverage, not yet accounting for never-integrated spec work.
-/
theorem State.drainReadyGroups_no_stranded_group {queue : State} {parents target}
    (unique : queue.GroupRefsUnique) (forest : queue.RemovalForest parents)
    (available : List (Occurrence × Nat) := [])
    (empty : (queue.drainReadyGroups available).1.rootGroups = [])
    (covered : ∃ root ∈ queue.rootGroups, queue.LiveDescendant root target)
    : (queue.drainReadyGroups available).1.groupNode? target = none := by
  cases found : (queue.drainReadyGroups available).1.groupNode? target with
  | none => rfl
  | some node =>
      obtain ⟨root, member, _⟩ :=
        State.drainReadyGroups_root_coverage unique forest available target
        covered ⟨node, found⟩
      rw [empty] at member
      cases member

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
