import Proofs.GraphQL.IncrementalDelivery.Correctness.BasicPositions

/-! Position coverage suffices for exactly-once basic leaves; its premise remains separate.
-/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution

/-- The public leaf-once statement follows from position coverage. Witness: coverage
is an occurrence-preserving permutation, while basic execution has unique leaf paths.
This implication does not establish its public coverage premise.
-/
theorem basicLeavesDeliveredExactlyOnce_of_positions {schema : Schema}
    {operation : Operation}
    (coverage : deliveredResponsePositionsEquivalentToBasic schema operation)
    : basicLeavesDeliveredExactlyOnce schema operation := by
  intro ObjectRef resolvers variables fuel source result observed zero
  obtain ⟨slices, delivered, perm⟩ :=
    coverage resolvers variables fuel source result observed zero false
  have unique := BasicPositions.executeQueryWithFuel_nodup schema resolvers variables
    operation.eraseIncrementalDirectives fuel source false
  refine ⟨slices, delivered, ?_⟩
  intro path member
  have atMost := List.nodup_iff_count.mp unique path
  have atLeast := List.count_pos_iff.mpr member
  rw [perm.count_eq]
  omega

end GraphQL.IncrementalDelivery.Correctness
