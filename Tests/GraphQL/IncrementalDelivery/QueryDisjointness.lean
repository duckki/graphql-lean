import Proofs.GraphQL.IncrementalDelivery.Correctness.QueryDisjointness

/-! The public disjointness witness has no validation, success, or completion premise. -/

namespace GraphQL.IncrementalDelivery.Tests.QueryDisjointness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Correctness

/-- The public proposition is inhabited for all schemas and raw operations. -/
example (schema : Schema) (operation : Operation)
    : deliverySlicesDisjoint schema operation :=
  deliverySlicesDisjoint_holds schema operation

/-- Flattened uniqueness is exactly the former internal/pairwise formulation;
both directions follow from the standard pairwise-flatten decomposition.
-/
example (slices : List (List ResponsePath))
    : slices.flatten.Nodup
      ↔ (∀ slice ∈ slices, slice.Nodup)
        ∧ slices.Pairwise (fun left right => ∀ path ∈ left, path ∉ right) := by
  constructor
  · intro unique
    obtain ⟨each, apart⟩ := List.pairwise_flatten.mp unique
    exact ⟨each, apart.imp
      (fun separated path left right => separated path left path right rfl)⟩
  · rintro ⟨each, apart⟩
    apply List.pairwise_flatten.mpr
    refine ⟨each, apart.imp ?_⟩
    intro left right separated a ha b hb equal
    subst b
    exact separated a ha hb

/-- The public statement now supplies global uniqueness directly, in either path mode. -/
example {ObjectRef : Type} {schema : Schema} {resolvers : Resolvers ObjectRef}
    {variables : VariableValues} {operation : Operation} {fuel : Nat}
    {source : ResolverValue ObjectRef} {result : QueryResult}
    (observed : queryObservation schema resolvers variables operation fuel source result)
    (containers : Bool)
    : ∃ slices, result.DeliversSlices containers slices ∧ slices.flatten.Nodup :=
  deliverySlicesDisjoint_holds schema operation
    resolvers variables fuel source result containers observed

/-- Arbitrary query prefixes retain a globally unique container-inclusive position list;
the observation may be interrupted, and its total error count need not be zero.
-/
example {ObjectRef : Type} {schema : Schema} {resolvers : Resolvers ObjectRef}
    {variables : VariableValues} {operation : Operation} {fuel : Nat}
    {source : ResolverValue ObjectRef} {result : QueryResult}
    (observed : queryObservation schema resolvers variables operation fuel source result)
    : ∃ slices, result.DeliversSlices true slices ∧ slices.flatten.Nodup :=
  queryObservation_disjoint_positions observed

/-- Container-free leaf slices inherit disjointness under the same unrestricted prefix
premise, independently of the complete basic-response coverage theorem.
-/
example {ObjectRef : Type} {schema : Schema} {resolvers : Resolvers ObjectRef}
    {variables : VariableValues} {operation : Operation} {fuel : Nat}
    {source : ResolverValue ObjectRef} {result : QueryResult}
    (observed : queryObservation schema resolvers variables operation fuel source result)
    : ∃ slices, result.DeliversSlices false slices ∧ slices.flatten.Nodup := by
  obtain ⟨slices, decoded, unique⟩ := queryObservation_disjoint_positions observed
  exact Semantics.deliversSlices_leaves_nodup decoded unique

end GraphQL.IncrementalDelivery.Tests.QueryDisjointness
