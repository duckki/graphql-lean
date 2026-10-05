import Proofs.GraphQL.IncrementalDelivery.Correctness.DeferredFailureCoverage

/-! Root collection and partition permutation preserve failure-aware response coverage. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open Semantics

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

/-- Root coverage follows from local field-result agreement in the generated plan.
Witness: exact collection erasure, field-result permutation including errors, and the
actual plan executor's partition coverage. Field ordering is not an additional premise;
`collected` and `next` are the witnessed outputs of the real collection action.
The remaining mixed comparison concerns partial nested field results, not root grouping.
-/
theorem executeRootSelectionSetCore_partition_coverage (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (parentType : Name) (source : ResolverValue ObjectRef) (selections : List Selection)
    (state : NodeRef) (collected : FieldCollection) (next : NodeRef)
    (collection
      : (collectFields schema variables parentType source selections).run state
        = (collected, next))
    (immediate
      : ∀ supply,
          ((executeCollectedFields schema resolvers variables fuel parentType source
              (buildExecutionPlan collected.collectedFieldsMap).collectedFieldsMap [] []
              (getNewDeferMap collected.newDeferUsages [] [])).run
            supply).1.result
          = GraphQL.Execution.executeCollectedFields schema resolvers variables fuel
              parentType source
              (eraseGroups
                (buildExecutionPlan collected.collectedFieldsMap).collectedFieldsMap))
    (deferred
      : ∀ partition ∈
          (buildExecutionPlan collected.collectedFieldsMap).newCollectedFieldsMaps,
          ∀ supply,
            ((executeExecutionGroup schema resolvers variables fuel parentType source
                partition.2 [] partition.1
                (getNewDeferMap collected.newDeferUsages [] [])).run
              supply).1.result
            = GraphQL.Execution.executeCollectedFields schema resolvers variables fuel
                parentType source (eraseGroups partition.2))
    (containers : Bool)
    : let completed :=
        ((executeRootSelectionSetCore schema resolvers variables fuel parentType
            source selections).run
          state).1
      PreparedResponseCovers
        (GraphQL.Execution.selectionSetResultToResponse
          (GraphQL.Execution.executeRootSelectionSet schema resolvers variables fuel
            parentType source (SelectionSet.eraseIncrementalDirectives selections))).data
        (selectionSetResultToResponse completed.result) completed.work containers := by
  have erased := collectFields_erase schema variables parentType source selections none state
  rw [collection] at erased
  have ordinary : GraphQL.Execution.executeRootSelectionSet schema resolvers variables fuel
      parentType source (SelectionSet.eraseIncrementalDirectives selections)
      = GraphQL.Execution.executeCollectedFields schema resolvers variables fuel parentType
          source (eraseGroups collected.collectedFieldsMap) := by
    simp only [GraphQL.Execution.executeRootSelectionSet, ← erased]
  have equivalent := TypedResponse.basicFields_perm_withErrors schema resolvers variables fuel
    parentType source (buildExecutionPlan_erasure_perm collected.collectedFieldsMap []).symm
  have planErasure (plan : ExecutionPlan) : eraseGroups (executionPlanGroups plan)
      = eraseGroups plan.collectedFieldsMap
        ++ plan.newCollectedFieldsMaps.flatMap (fun partition => eraseGroups partition.2) := by
    simp [eraseGroups, executionPlanGroups, List.map_flatMap]
  rw [planErasure] at equivalent
  dsimp only
  simp only [executeRootSelectionSetCore, run_bind, collection]
  rw [ordinary]
  exact executeExecutionPlan_equivalent_coverage schema resolvers variables fuel
    parentType source collected.newDeferUsages
    (buildExecutionPlan collected.collectedFieldsMap) [] [] next containers _ equivalent
    immediate deferred

end GraphQL.IncrementalDelivery.Correctness
