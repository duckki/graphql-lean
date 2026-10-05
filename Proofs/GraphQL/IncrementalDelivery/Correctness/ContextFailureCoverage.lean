import Proofs.GraphQL.IncrementalDelivery.Correctness.DeferredFailureCoverage
import Proofs.GraphQL.IncrementalDelivery.Semantics.ContextCompletion

/-! Failure-aware coverage for deferred plain bodies, without field-result assumptions. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open Semantics

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

-----------------------------------------------------------------------------------------
-- Uniform inherited contexts discharge the local execution comparisons
-----------------------------------------------------------------------------------------

/-- Plain bodies within each inherited defer context satisfy actual plan coverage.
Witness: ordinary field completion in each well-formed context supplies the local result
equations required by the partition theorem. Nullable and bubbling errors remain allowed.
Shared partitions with differing inherited contexts still require a mixed comparison.
-/
theorem executeExecutionPlan_context_coverage (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (parentType : Name) (source : ResolverValue ObjectRef)
    (newDeferUsages : List DeferUsage) (plan : ExecutionPlan)
    (context : Option DeferUsage) (deferMap : DeferMap) (state : NodeRef)
    (containers : Bool) (valid : ContextWellFormed context)
    (initial : GroupsInContext context plan.collectedFieldsMap)
    (deferred
      : ∀ partition ∈ plan.newCollectedFieldsMaps,
          ∃ context,
            ContextWellFormed context
            ∧ partition.1 = contextRefs context
            ∧ GroupsInContext context partition.2)
    : let completed :=
        ((executeExecutionPlan schema resolvers variables fuel parentType
            source newDeferUsages plan [] (contextRefs context) deferMap).run
          state).1
      PreparedResponseCovers
        (GraphQL.Execution.selectionSetResultToResponse
          (GraphQL.Execution.executeCollectedFields schema resolvers variables fuel
            parentType source
            (eraseGroups plan.collectedFieldsMap
              ++ plan.newCollectedFieldsMaps.flatMap
                  (fun partition => eraseGroups partition.2)))).data
        (selectionSetResultToResponse completed.result) completed.work containers := by
  apply executeExecutionPlan_partition_coverage schema resolvers variables fuel parentType
    source newDeferUsages plan (contextRefs context) deferMap state containers
  · intro next
    exact (executeCollectedFields_inContext context valid
      (getNewDeferMap newDeferUsages [] deferMap) schema resolvers variables fuel parentType
      source plan.collectedFieldsMap initial [] next).2.1
  · intro partition member next
    obtain ⟨context, valid, refs, fields⟩ := deferred partition member
    simp only [executeExecutionGroup, refs]
    exact (executeCollectedFields_inContext context valid
      (getNewDeferMap newDeferUsages [] deferMap) schema resolvers variables fuel parentType
      source partition.2 fields [] next).2.1

-----------------------------------------------------------------------------------------
-- A single active root defer with an arbitrary plain selection body
-----------------------------------------------------------------------------------------

private theorem singleDefer_collection (schema : Schema) (variables : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectRef) (children : List Selection)
    (plain : SelectionsPlain children) (label : Option InputValue) (state : NodeRef)
    : let usage : DeferUsage := { ref := state, label := directiveLabel? label }
      let collected :=
        (collectFields schema variables parentType source children (some usage)).run
          (state + 1)
      (collectFields schema variables parentType source
        [.inlineFragment none [.defer (.boolean true) label] children]).run
        state
      = ({ collected.1 with newDeferUsages := [usage] }, state + 1) := by
  dsimp only
  have context := collectFields_inContext schema variables parentType source children plain
    (some { ref := state, label := directiveLabel? label }) (state + 1)
  obtain ⟨supply, notices, fields⟩ := context
  simp [collectFields, collectSelection, selectionDirectivesAllowBool,
    directiveAllowsSelectionBool, activeDefer?, GraphQL.Execution.inputValueBoolean?,
    InputValue.staticBoolean?, freshNodeRef, FieldCollection.append,
    CollectedFieldsMap.merge, notices, supply]

/-- A single active root defer with a plain body covers its ordinary response positions.
Witness: context-preserving collection, the actual deferred plan, and its checked
partition coverage. Objects, lists, aliases, fuel failures, and all counted errors are
allowed within the body; nested incremental directives are excluded by `plain`.
-/
theorem preparedResponseCovers_singleDefer (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (parentType : Name) (source : ResolverValue ObjectRef) (children : List Selection)
    (plain : SelectionsPlain children) (label : Option InputValue) (state : NodeRef)
    (containers : Bool)
    : let selections := [.inlineFragment none [.defer (.boolean true) label] children]
      let completed :=
        ((executeRootSelectionSetCore schema resolvers variables fuel parentType
            source selections).run
          state).1
      PreparedResponseCovers
        (GraphQL.Execution.selectionSetResultToResponse
          (GraphQL.Execution.executeRootSelectionSet schema resolvers variables fuel
            parentType source (SelectionSet.eraseIncrementalDirectives selections))).data
        (selectionSetResultToResponse completed.result) completed.work containers := by
  let usage : DeferUsage := { ref := state, label := directiveLabel? label }
  let collected := (collectFields schema variables parentType source children (some usage)).run
    (state + 1)
  have context := collectFields_inContext schema variables parentType source children plain
    (some usage) (state + 1)
  have fields : GroupsInContext (some usage) collected.1.collectedFieldsMap := context.2.2
  have valid : ContextWellFormed (some usage) := by simp [ContextWellFormed, usage]
  have erased := collectFields_erase schema variables parentType source children (some usage)
    (state + 1)
  have root := singleDefer_collection schema variables parentType source children plain label
    state
  dsimp only
  simp only [executeRootSelectionSetCore, run_bind, root]
  change PreparedResponseCovers _
    (selectionSetResultToResponse
      ((executeExecutionPlan schema resolvers variables fuel parentType source [usage]
          (buildExecutionPlan collected.1.collectedFieldsMap)).run (state + 1)).1.result)
    ((executeExecutionPlan schema resolvers variables fuel parentType source [usage]
      (buildExecutionPlan collected.1.collectedFieldsMap)).run (state + 1)).1.work containers
  have ordinary : GraphQL.Execution.executeRootSelectionSet schema resolvers variables fuel
      parentType source (SelectionSet.eraseIncrementalDirectives
        [.inlineFragment none [.defer (.boolean true) label] children])
      = GraphQL.Execution.executeCollectedFields schema resolvers variables fuel parentType
          source (eraseGroups collected.1.collectedFieldsMap) := by
    rw [show eraseGroups collected.1.collectedFieldsMap = _ from erased]
    simp [GraphQL.Execution.executeRootSelectionSet, SelectionSet.eraseIncrementalDirectives,
      Selection.eraseIncrementalDirectives, DirectiveApplication.eraseIncremental?,
      GraphQL.Execution.collectFields, GraphQL.Execution.collectSelection,
      List.filterMap_cons, List.filterMap_nil, GraphQL.Execution.selectionDirectivesAllowBool,
      GraphQL.Execution.mergeExecutableGroups]
  rw [ordinary]
  by_cases empty : collected.1.collectedFieldsMap = []
  · have covered := executeExecutionPlan_context_coverage schema resolvers variables fuel
      parentType source [usage] {} none [] (state + 1) containers
      (by simp [ContextWellFormed]) (by intro group member; simp at member)
      (by intro partition member; simp at member)
    simpa [empty, buildExecutionPlan, eraseGroups, contextRefs] using covered
  · have plan := buildExecutionPlan_deferred usage valid collected.1.collectedFieldsMap fields
      empty
    rw [plan]
    have covered := executeExecutionPlan_context_coverage schema resolvers variables fuel
      parentType source [usage] { newCollectedFieldsMaps :=
        [([usage.ref], collected.1.collectedFieldsMap)] } none [] (state + 1) containers
      (by simp [ContextWellFormed]) (by intro group member; simp at member)
      (by
        intro partition member
        simp only [List.mem_singleton] at member
        subst partition
        exact ⟨some usage, valid, rfl, fields⟩)
    simpa [eraseGroups, contextRefs] using covered

-----------------------------------------------------------------------------------------
-- Client-facing coverage for the single-root-defer syntax fragment
-----------------------------------------------------------------------------------------

/-- The public failure-aware coverage statement holds for a single active root defer
whose body is plain. Witness: `preparedResponseCovers_singleDefer`, followed by the actual
query-observation reduction. This quantifies over all resolvers, inputs, fuel, and
conforming complete observations, not just a selected successful execution or schedule.
The unrestricted nested/shared incremental statement remains a separate obligation.
-/
theorem ResponsePositionsDeliveredOrFailed_of_singleDefer (schema : Schema)
    (operation : Operation) (children : List Selection) (label : Option InputValue)
    (shape
      : operation.selectionSet
        = [.inlineFragment none [.defer (.boolean true) label] children])
    (plain : SelectionsPlain children)
    : ResponsePositionsDeliveredOrFailed schema operation := by
  apply ResponsePositionsDeliveredOrFailed_of_preparedComparison schema operation
  intro ObjectRef resolvers variables fuel source
  dsimp only
  intro _ applies _ containers
  have covered := preparedResponseCovers_singleDefer schema resolvers
    (coerceVariableValues operation variables) fuel (operation.rootType schema) source
    children plain label 0 containers
  have ordinary : GraphQL.Execution.executeQueryWithFuel schema resolvers variables
      operation.eraseIncrementalDirectives fuel source
      = GraphQL.Execution.selectionSetResultToResponse
          (GraphQL.Execution.executeRootSelectionSet schema resolvers
            (coerceVariableValues operation variables) fuel (operation.rootType schema)
            source (SelectionSet.eraseIncrementalDirectives operation.selectionSet)) := by
    have root : GraphQL.Execution.rootSourceAppliesBool schema
        operation.eraseIncrementalDirectives source = true := applies
    simp only [GraphQL.Execution.executeQueryWithFuel, root, ↓reduceIte]
    rfl
  rw [ordinary, shape]
  exact covered

end GraphQL.IncrementalDelivery.Correctness
