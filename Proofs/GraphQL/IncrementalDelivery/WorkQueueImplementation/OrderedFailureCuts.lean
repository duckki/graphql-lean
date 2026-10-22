import GraphQL.IncrementalDelivery.WorkQueueSemantics

/-! Ordered finite cut inventories retain their original output positions. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Merge candidate cuts without moving any unbatched output index
-----------------------------------------------------------------------------------------

/-- Merge object and stream candidates by output index, retaining both input orders.
Object candidates precede stream candidates at equal indices. This is a proof-side
inventory construction, not an implementation scheduling policy or a licensed witness.
-/
def interleaveFailureCuts (objects streams : FailureCuts) : FailureCuts :=
  objects.merge streams (fun left right => left.1 ≤ right.1)

/-- The merge retains precisely both candidate lists, with their original cut positions.
Witness: the standard merge permutation followed by append commutation.
-/
theorem interleaveFailureCuts_partition (objects streams : FailureCuts)
    : (interleaveFailureCuts objects streams).Perm (streams ++ objects) :=
  (List.merge_perm_append _).trans (List.perm_append_comm)

/-- Merging two ordered candidate lists retains nondecreasing cut positions.
Witness: the standard sorted-merge theorem for the total transitive order on indices.
-/
theorem interleaveFailureCuts_ordered {objects streams : FailureCuts}
    (objectOrder : objects.Pairwise (fun left right => left.1 ≤ right.1))
    (streamOrder : streams.Pairwise (fun left right => left.1 ≤ right.1))
    : (interleaveFailureCuts objects streams).Pairwise
        (fun left right => left.1 ≤ right.1) := by
  have trans (left middle right : Nat × Occurrence)
      : decide (left.1 ≤ middle.1) = true → decide (middle.1 ≤ right.1) = true →
          decide (left.1 ≤ right.1) = true := by
    simp only [decide_eq_true_eq]
    exact Nat.le_trans
  have total (left right : Nat × Occurrence)
      : (decide (left.1 ≤ right.1) || decide (right.1 ≤ left.1)) = true := by
    simpa only [Bool.or_eq_true, decide_eq_true_eq] using Nat.le_total left.1 right.1
  simpa only [interleaveFailureCuts, decide_eq_true_eq]
    using List.pairwise_merge trans total objects streams
      (by simpa only [decide_eq_true_eq] using objectOrder)
      (by simpa only [decide_eq_true_eq] using streamOrder)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
