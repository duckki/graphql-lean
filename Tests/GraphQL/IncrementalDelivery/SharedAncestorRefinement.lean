import Proofs.GraphQL.IncrementalDelivery.Semantics.SharedAncestorExecution
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Recursive refinement checks, distinct from the definition-only public snapshots.
The exact root target has no generated-context, successful-execution, or host assumptions.
Raw inconsistent plan inputs remain outside its domain. -/

namespace GraphQL.IncrementalDelivery.Tests.SharedAncestorRefinement

open GraphQL.IncrementalDelivery.Execution

namespace Optimized
export Semantics.SharedAncestorExecution (
  executeRootSelectionSetCore executeExecutionPlan
)
end Optimized

example : Semantics.SharedAncestorExecution.RootExecutionExact :=
  Semantics.SharedAncestorExecution.rootExecutionExact_holds

example (ObjectRef : Type) (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (parentType : Name)
    (source : ResolverValue ObjectRef) (selections : List Selection) (state : Nat)
    : (Optimized.executeRootSelectionSetCore schema resolvers variables fuel parentType
        source selections).run
        state
      = (executeRootSelectionSetCore schema resolvers variables fuel parentType source
          selections).run
          state :=
  Semantics.SharedAncestorExecution.rootExecutionExact_holds ObjectRef schema resolvers
    variables fuel parentType source selections state

example (ObjectRef : Type) (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (parentType : Name)
    (source : ResolverValue ObjectRef) (selections : List Selection)
    : Optimized.executeRootSelectionSetCore schema resolvers variables fuel parentType
        source selections
      = executeRootSelectionSetCore schema resolvers variables fuel parentType source
          selections :=
  Semantics.SharedAncestorExecution.executeRootSelectionSetCore_eq schema resolvers
    variables fuel parentType source selections

private def scenarios : List (List Selection) :=
  [
    [defer
      [defer
        [field "users"
          [defer [field "name", defer [field "age"] (some "age")] (some "name")]]]],
    [
      defer [field "user" [defer [field "name"]]],
      defer [field "user" [defer [field "age"]]]
    ],
    [defer
      [field "users" [defer [field "name", defer [field "age"]]]
        [.stream (.boolean true) (some (.string "users")) (.int 1)]]],
    [defer
      [field "users"
        [defer [field "name", field "values" [] [.stream (.boolean true) none (.int 0)]]]
        [.stream (.boolean true) none (.int 0)]]],
    [defer [defer [field "user" [defer [field "required"], defer [field "name"]]]]],
    [field "required", defer [field "users" [defer [field "name"]]]],
    [field "missing", defer [field "a"]],
    [defer [field "empty" [] [.stream (.boolean true) none (.int 0)]]],
    [defer
      [field "users" [defer [field "name"]] [.stream (.boolean true) none (.int 2)]]],
    [defer
      [field "users" [defer [field "name"]] [.stream (.boolean true) none (.int 3)]]],
    [defer [field "strict" [] [.stream (.boolean true) none (.int 0)]]],
    [defer [field "strict" [] [.stream (.boolean true) none (.int 2)]]],
    [defer
      [field "users" [defer [field "name"]] [.stream (.boolean true) none (.int (-1))]]],
    [defer
      [.inlineFragment none [.include (.variable "enabled")]
        [defer [field "user" [defer [field "name"]]]]]]
  ]

private def agrees (selections : List Selection) (fuel state : Nat)
    (variables : VariableValues := [])
    : Bool :=
  same
    ((Optimized.executeRootSelectionSetCore schema resolvers variables fuel "Query"
        (.object "Query" 0) selections).run
      state)
    ((executeRootSelectionSetCore schema resolvers variables fuel "Query"
        (.object "Query" 0) selections).run
      state)

/- The actual optimized code, not only the theorem, retains all work-tree association. -/
#guard
  scenarios.all
    (fun selections =>
      [0, 3, 30].all
        (fun fuel => [0, 17].all (fun state => agrees selections fuel state)))

#guard
  scenarios.all
    (fun selections =>
      [false, true].all
        (fun enabled => agrees selections 30 17 [("enabled", .boolean enabled)]))

private def chain : Nat → List Selection
  | 0 => [field "user" [defer [field "name"]]]
  | depth + 1 => [defer (chain depth)]

#guard [1, 2, 8, 32].all (fun depth => agrees (chain depth) 30 20)

/- Construction equality cannot be claimed for arbitrary raw plan arguments. -/
private def inconsistent : List DeferUsage :=
  [{ ref := 1, ancestors := [0] }, { ref := 0 }, { ref := 2, ancestors := [1, 0] }]

private def rawPlan : ExecutionPlan := { newCollectedFieldsMaps := [([2], [])] }

private def firstAncestors : Work → List Nat
  | .combine .empty (.combine (.executionGroup (fragment :: _) _ _ _) .empty) =>
      fragment.ancestors.map DeliveryNode.ref
  | _ => []

example
    : (Optimized.executeExecutionPlan schema resolvers [] 5 "Query" (.object "Query" 0)
        inconsistent rawPlan [] [] []).run
        0
      ≠ (executeExecutionPlan schema resolvers [] 5 "Query" (.object "Query" 0)
          inconsistent rawPlan).run
          0 := by
  intro equal
  have impossible := congrArg (fun output => firstAncestors output.1.work) equal
  simp [Semantics.SharedAncestorExecution.executeExecutionPlan,
    Semantics.SharedAncestorExecution.executeCollectedFields,
    Semantics.SharedAncestorExecution.collectExecutionGroups,
    Semantics.SharedAncestorConstruction.getNewDeferMapShared,
    Semantics.SharedAncestorConstruction.sharedDeferAncestors,
    executeExecutionPlan, executeCollectedFields, collectExecutionGroups, executeExecutionGroup,
    getNewDeferMap, lookupDeferredFragment?, rawPlan, inconsistent, firstAncestors,
    Completion.pure, StateT.run_pure, Semantics.id_pure_eq] at impossible

#print axioms Semantics.SharedAncestorExecution.planRefinement_holds
#print axioms Semantics.SharedAncestorExecution.rootExecutionExact_holds
#print axioms Semantics.SharedAncestorExecution.executeRootSelectionSetCore_eq

end GraphQL.IncrementalDelivery.Tests.SharedAncestorRefinement
