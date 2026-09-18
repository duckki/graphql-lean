import Proofs.GraphQL.IncrementalDelivery.Correctness.SourceExecutionReconstruction
import Proofs.GraphQL.IncrementalDelivery.Correctness.BasicPositions

/-! Basic-response uniqueness discharges the internal cursor-seed guard. Thus
successful actual mixed execution supplies typed reconstruction and its exact
payload-seeded source offsets in a single witness.
-/

namespace GraphQL.IncrementalDelivery.Correctness.SourceReconstruction

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open TypedResponse

/-- Successful root execution reconstructs typed basic entries with their actual cursor
seeds. Witness: the mutual execution theorem and basic-response position uniqueness.
-/
theorem executeRoot_seeded_success (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (parentType : Name)
    (source : ResolverValue ObjectRef) (selections : List Selection) (state : Nat)
    : let completed :=
        ((executeRootSelectionSetCore schema resolvers variables fuel parentType source
            selections).run
          state).1
      CompletionSuccess completed
      → ∃ data slices,
          GraphQL.Execution.executeCollectedFields schema resolvers variables fuel
              parentType source
              (GraphQL.Execution.collectFields schema variables parentType source
                (SelectionSet.eraseIncrementalDirectives selections))
            = .ok (data, 0)
          ∧ WorkEntries completed.work slices
          ∧ (result (fields []) completed.result ++ slices.flatten).Perm (fields [] data)
          ∧ MixedPaths.WorkCursorSeed
              (MixedPaths.resultCursors (ResponsePositions.fieldCursors [])
                completed.result)
              completed.work (entryPaths slices) := by
  dsimp only
  intro hs
  obtain ⟨data, slices, hd, hw, hp, hseed⟩ :=
    (executeRoot_seeded schema resolvers variables fuel parentType source selections state).reconstruct hs
  refine ⟨data, slices, hd, hw, hp, hseed ?_⟩
  apply (hp.map Prod.fst).nodup_iff.mpr
  have hn := BasicPositions.rootResponse_nodup schema resolvers variables fuel parentType source
    (SelectionSet.eraseIncrementalDirectives selections) true
  simp only [GraphQL.Execution.executeRootSelectionSet, hd,
    GraphQL.Execution.selectionSetResultToResponse, ResponsePositions.value,
    ↓reduceIte, List.singleton_append, List.nodup_cons] at hn
  simpa only [fields_paths, source_fields_eq_positions] using hn.2

end GraphQL.IncrementalDelivery.Correctness.SourceReconstruction
