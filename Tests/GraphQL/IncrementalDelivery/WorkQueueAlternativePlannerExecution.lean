import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.PlannerExecution
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Whole recursive executor substitution: full completion, work and supply, not only
reconstructed data. Contexts and optimized planning are derived in this same execution.
-/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.PlannerExecution.Tests

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Tests
open GraphQL.IncrementalDelivery.Semantics

example : PlannerExecution.RootExecutionExact := PlannerExecution.rootExecutionExact_holds
example : PlannerExecution.PlanRefinement := PlannerExecution.planRefinement_holds

example (ObjectRef : Type) (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (parentType : Name)
    (source : ResolverValue ObjectRef) (selections : List Selection) (state : Nat)
    : (PlannerExecution.executeRootSelectionSetCore schema resolvers variables fuel
        parentType source selections).run
        state
      = (Execution.executeRootSelectionSetCore schema resolvers variables fuel parentType
          source selections).run
          state :=
  PlannerExecution.rootExecutionExact_holds ObjectRef schema resolvers variables fuel
    parentType source selections state

private def optimized (selections : List Selection) (state : Nat := 0) (fuel : Nat := 30)
    (variables : VariableValues := [])
    : Completion (List (Name × ResponseValue)) × Nat :=
  (PlannerExecution.executeRootSelectionSetCore schema resolvers variables fuel "Query"
    (.object "Query" (0 : Nat)) selections).run
    state

private def original (selections : List Selection) (state : Nat := 0) (fuel : Nat := 30)
    (variables : VariableValues := [])
    : Completion (List (Name × ResponseValue)) × Nat :=
  (Execution.executeRootSelectionSetCore schema resolvers variables fuel "Query"
    (.object "Query" (0 : Nat)) selections).run
    state

private def inherited : List Selection :=
  [defer [defer [field "users" [defer [field "name", defer [field "age"]]]]]]

private def shared : List Selection :=
  [
    defer [field "user" [defer [field "name"]]],
    defer [field "user" [defer [field "age"]]]
  ]

private def streamed : List Selection :=
  [defer
    [field "users" [defer [field "name", defer [field "age"]]]
      [.stream (.boolean true) (some (.string "users")) (.int 1)]]]

private def failed : List Selection :=
  [defer [defer [field "user" [defer [field "required"], defer [field "name"]]]]]

-- Full Repr snapshots include every descriptor, ancestry, pure outcome and work branch.
#guard
  [inherited, shared, streamed, failed].all
    (fun selections => same (optimized selections) (original selections))
#guard (optimized inherited).2 == 6
#guard (optimized shared).2 == 4
#guard (optimized streamed).2 == 6
#guard (optimized failed).2 == 4

-- Immediate domination, repeated aliases, disallowed directives, empty stream boundary,
-- nested lists, ordinary/empty execution, and exhausted fuel use the same recursive target.
private def boundaries : List (List Selection) :=
  [
    [],
    [field "a"],
    [field "a", defer [field "a"], field "a"],
    [defer [field "b"] none (.variable "enabled")],
    [field "users" [defer [field "name"]] [.stream (.boolean true) none (.int 2)]],
    [field "empty" [] [.stream (.boolean true) none (.int 0)]],
    [field "matrix"],
    [field "strict" [] [.stream (.boolean true) none (.int 0)]],
    [field "required"],
    [defer [field "required"], defer [field "b"]],
    [
      field "a" [] [] (some "x"),
      defer [field "a" [] [] (some "x")],
      defer [field "b" [] [] (some "y")]
    ]
  ]

#guard
  boundaries.all
    (fun selections => same (optimized selections 17) (original selections 17))
#guard
  boundaries.all
    (fun selections => same (optimized selections 17 0) (original selections 17 0))
#guard
  boundaries.all
    (fun selections => same (optimized selections 17 2) (original selections 17 2))
#guard
  same (optimized boundaries[3] 17 30 [("enabled", .boolean false)])
    (original boundaries[3] 17 30 [("enabled", .boolean false)])

-- Equality of the action licenses any unchanged wrapper/factory, not only this fixture.
example (wrap : StateM Nat (Completion (List (Name × ResponseValue))) → α)
    (selections : List Selection)
    : wrap
        (PlannerExecution.executeRootSelectionSetCore schema resolvers [] 30 "Query"
          (.object "Query" (0 : Nat)) selections)
      = wrap
          (Execution.executeRootSelectionSetCore schema resolvers [] 30 "Query"
            (.object "Query" (0 : Nat)) selections) := by
  rw [PlannerExecution.executeRootSelectionSetCore_eq]

#print axioms PlannerExecution.rootExecutionExact_holds
#print axioms PlannerExecution.planRefinement_holds
#print axioms PlannerExecution.executeRootSelectionSetCore_eq
#print axioms PlannerExecution.completeValue_refines
#print axioms PlannerExecution.completeStreamItems_refines

end
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.PlannerExecution.Tests
