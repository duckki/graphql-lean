import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ScheduledKeyRegions
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ScheduledSiblingRefinement
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.CutKeySupply

/-! Supply premises derived for actual recursively cut child actions. The comparison
driver continues all siblings but keeps the same recursive child policy; it is not the
original public eager executor. General inter-policy key-map construction remains open.
These bounds let the existing atomic scope-witness constructor apply to real recursive
field/list scopes without assuming output monotonicity. -/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.ScheduledExecution

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
  (id_pure_eq id_bind_eq id_map_eq run_bind run_map)
open ScheduledErrors

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

variable {ObjectRef : Type}

theorem fieldActions_monotone (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (parentType : Name)
    (source : ResolverValue ObjectRef) (fields : CollectedFieldsMap)
    (path : ResponsePath) (usages : List Nat) (context : DeferMap) (floor : Nat)
    (inherited : ∀ key ∈ context.flatMap Semantics.RefRoles.fragmentRefs, key < floor)
    : MonotoneAbove floor
        (fieldActions schema resolvers variables fuel parentType source fields path usages
          context) := by
  intro action member supply above
  obtain ⟨⟨name, group⟩, _, rfl⟩ := List.mem_map.mp member
  exact (executeResponseField_regions schema resolvers variables fuel
    parentType source name group path usages context supply
    (fun key member => Nat.lt_of_lt_of_le (inherited key member) above)).monotone

theorem listActions_monotone (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (itemType : TypeRef)
    (fields : List FieldDetails) (values : List (ResolverValue ObjectRef))
    (path : ResponsePath) (index : Nat) (usages : List Nat) (context : DeferMap)
    (floor : Nat)
    (inherited : ∀ key ∈ context.flatMap Semantics.RefRoles.fragmentRefs, key < floor)
    : MonotoneAbove floor
        (listActions schema resolvers variables fuel itemType fields path usages context
          values index) := by
  induction values generalizing index with
  | nil => intro action member; cases member
  | cons value rest ih =>
      intro action member supply above
      simp only [listActions, List.mem_cons] at member
      rcases member with rfl | member
      · exact (completeValue_regions schema resolvers variables fuel
          itemType fields value (path ++ [.index index]) usages context false supply
          (fun key member => Nat.lt_of_lt_of_le (inherited key member) above)).monotone
      · exact ih (index + 1) action member supply above

-----------------------------------------------------------------------------------------
-- Checked constructor: derive one injective map and its boundary from the same cut
-----------------------------------------------------------------------------------------

/-- One actual recursive field scope constructs its allocation-gap extension to the
all-sibling driver using the same recursively cut children, not public eager execution. -/
theorem executeCollectedFields_cut_supply (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (parentType : Name) (source : ResolverValue ObjectRef) (fields : CollectedFieldsMap)
    (path : ResponsePath) (usages : List Nat) (context : DeferMap) (supply : Nat)
    (inherited : ∀ key ∈ context.flatMap Semantics.RefRoles.fragmentRefs, key < supply)
    : SupplyExtension supply
        ((executeCollectedFields schema resolvers variables fuel parentType source fields
            path usages context).run
          supply).2
        ((executeActions List.append []
            (fieldActions schema resolvers variables fuel parentType source fields path
              usages context)).run
          supply).2 := by
  have constructed := cutSupplyExtension_holds _
    (fieldActions schema resolvers variables fuel parentType source fields path usages context)
    supply (fieldActions_monotone schema resolvers variables fuel parentType source fields
      path usages context supply inherited)
  simpa only [executeCollectedFields_actions, cutActions, run_bind, StateT.run_pure,
    id_pure_eq, executeActions_observed] using constructed

/-- The same construction at a recursive ordinary/initial list-item scope. -/
theorem completeListValue_cut_supply (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (itemType : TypeRef)
    (fields : List FieldDetails) (values : List (ResolverValue ObjectRef))
    (path : ResponsePath) (index : Nat) (usages : List Nat) (context : DeferMap)
    (supply : Nat)
    (inherited : ∀ key ∈ context.flatMap Semantics.RefRoles.fragmentRefs, key < supply)
    : SupplyExtension supply
        ((completeListValue schema resolvers variables fuel itemType fields values path
            index usages context).run
          supply).2
        ((executeActions List.cons []
            (listActions schema resolvers variables fuel itemType fields path usages
              context values index)).run
          supply).2 := by
  have constructed := cutSupplyExtension_holds _
    (listActions schema resolvers variables fuel itemType fields path usages context values index)
    supply (listActions_monotone schema resolvers variables fuel itemType fields values
      path index usages context supply inherited)
  simpa only [completeListValue_actions, cutActions, run_bind, StateT.run_pure,
    id_pure_eq, executeActions_observed] using constructed

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.ScheduledExecution
