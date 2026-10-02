import Proofs.GraphQL.IncrementalDelivery.Semantics.ExecutedMixedPaths
import Proofs.GraphQL.IncrementalDelivery.Semantics.ExecutedCursorSeeds
import Proofs.GraphQL.IncrementalDelivery.Semantics.ExecutedMixedOwners

/-! Exact prepared-work certificates for disjointness and subsequent wire decoding.
These witnesses concern source work; QueryDisjointness connects them to observed delivery.
-/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics

mutual
  /-- The proof projection agrees with public value positions, by structural descent. -/
  theorem source_value_eq_positions (containers : Bool) (path : ResponsePath)
      (data : ResponseValue)
      : DeliveryPaths.value containers path data
        = ResponsePositions.value containers path data := by
    cases data with
    | null | scalar _ => rfl
    | object data =>
        simp [DeliveryPaths.value, ResponsePositions.value, source_fields_eq_positions]
    | list data =>
        simp [DeliveryPaths.value, ResponsePositions.value, source_items_eq_positions]

  /-- Field projections agree by concatenating their recursively equal value positions. -/
  theorem source_fields_eq_positions (containers : Bool) (path : ResponsePath)
      (data : List (Name × ResponseValue))
      : DeliveryPaths.fields containers path data
        = ResponsePositions.fields containers path data := by
    cases data with
    | nil => rfl
    | cons head rest =>
        simp [DeliveryPaths.fields, ResponsePositions.fields, source_value_eq_positions,
          source_fields_eq_positions]

  /-- Item projections agree with identical increasing indices, by list descent. -/
  theorem source_items_eq_positions (containers : Bool) (path : ResponsePath)
      (index : Nat) (data : List ResponseValue)
      : DeliveryPaths.items containers path index data
        = ResponsePositions.items containers path index data := by
    cases data with
    | nil => rfl
    | cons head rest =>
        simp [DeliveryPaths.items, ResponsePositions.items, source_value_eq_positions,
          source_items_eq_positions]
end

/-- A seeded field completion supplies disjoint initial/future positions and the exact
list cursors introduced by its initial response. Witness: include the unique root
container (or null root) alongside the existing field-ownership certificate.
-/
theorem root_positions_of_seeded {completed : Completion (List (Name × ResponseValue))}
    (seeded
      : MixedPaths.SeedOwnsCompletion (DeliveryPaths.fields true [])
          (ResponsePositions.fieldCursors []) (fun path => path ≠ []) completed)
    : ∃ slices,
        MixedPaths.WorkCursorSeed
          (ResponsePositions.listCursors []
            (selectionSetResultToResponse completed.result).data) completed.work slices
        ∧ (ResponsePositions.value true []
              (selectionSetResultToResponse completed.result).data
            ++ slices.flatten).Nodup := by
  obtain ⟨slices, seed, owns⟩ := seeded
  refine ⟨slices, ?_, ?_⟩
  · cases h : completed.result
    <;> simpa [MixedPaths.resultCursors, h, selectionSetResultToResponse,
      GraphQL.Execution.selectionSetResultToResponse, ResponsePositions.listCursors]
      using seed
  · cases h : completed.result with
    | error errors =>
        simp only [h, DeliveryPaths.result, List.nil_append] at owns
        simpa [h, selectionSetResultToResponse,
          GraphQL.Execution.selectionSetResultToResponse, ResponsePositions.value]
          using List.nodup_cons.mpr ⟨fun member => owns.2 [] member rfl, owns.1⟩
    | ok pair =>
        rcases pair with ⟨data, errors⟩
        simp only [h, DeliveryPaths.result, source_fields_eq_positions] at owns
        simpa [h, selectionSetResultToResponse,
          GraphQL.Execution.selectionSetResultToResponse, ResponsePositions.value]
          using List.nodup_cons.mpr ⟨fun member => owns.2 [] member rfl, owns.1⟩

/-- Every actual mixed root execution has disjoint source positions with coherent
cursor seeds. Witness: the checked execution induction, at any initial key supply.
-/
theorem executeRoot_source_positions (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (parentType : Name)
    (source : ResolverValue ObjectRef) (selections : List Selection) (state : Nat)
    : let completed :=
        ((executeRootSelectionSetCore schema resolvers variables fuel parentType source
            selections).run
          state).1
      ∃ slices,
        MixedPaths.WorkCursorSeed
          (ResponsePositions.listCursors []
            (selectionSetResultToResponse completed.result).data) completed.work slices
        ∧ (ResponsePositions.value true []
              (selectionSetResultToResponse completed.result).data
            ++ slices.flatten).Nodup :=
  root_positions_of_seeded
    (MixedPaths.executeRoot_seeded_fields schema resolvers variables fuel parentType
      source selections state)

end GraphQL.IncrementalDelivery.Correctness
