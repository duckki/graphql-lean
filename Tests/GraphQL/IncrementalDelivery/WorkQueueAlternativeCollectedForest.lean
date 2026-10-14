import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.CollectedForestPlanning
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Actual collection derives all forest/planning premises; raw inconsistent ancestry
does not receive that guarantee. No endpoint plan-equality assumption appears in the root.
-/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.CollectedForestPlanning.Tests

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open GraphQL.IncrementalDelivery.Tests
open Ancestry ParentChains

example : GeneratedPlanning := GeneratedPlanning_holds
example : RootCollectedPlanning := RootCollectedPlanning_holds

private def selections : List Selection :=
  [defer [defer [field "a"], field "b"], defer [field "a"], field "c", defer [field "c"]]

private def groups : CollectedFieldsMap :=
  ((collectFields schema [] "Query" (.object "Query" (0 : Nat)) selections none).run
    0).1.collectedFieldsMap

-- Shared response keys are merged before planning; an immediate occurrence dominates c.
#guard groups.map Prod.fst == ["a", "b", "c"]
#guard (forest groups).keys == [0, 1, 2, 3]
#guard
  (OrderedForestAssembly.discovered (contexts groups) (domain groups) groups).nodes
  == [1, 0, 2, 3]

example : buildPlan groups [] = buildExecutionPlan groups [] :=
  (RootCollectedPlanning_holds Nat schema [] "Query" (.object "Query" 0) selections 0
    []).2.2

-- Arbitrary supply offsets, directives and empty/raw selection sets need no validation premise.
example (selections : List Selection) (variables : VariableValues) (state : Nat)
    (parent : List Nat)
    : let collected :=
        (collectFields schema variables "Query" (.object "Query" (0 : Nat)) selections
          none).run
          state
      buildPlan collected.1.collectedFieldsMap parent
      = buildExecutionPlan collected.1.collectedFieldsMap parent :=
  (RootCollectedPlanning_holds Nat schema variables "Query" (.object "Query" 0) selections
    state parent).2.2

private def inconsistent : Assignment := fun key => if key = 2 then [1, 0] else []

-- The older transitive-membership invariant alone cannot justify ordered parent links.
example : Valid inconsistent 3 := by
  intro key bound ancestor present
  by_cases eq : key = 2
  · subst key
    simp [inconsistent] at present
    rcases present with rfl | rfl <;> simp [inconsistent, List.Subset]
  · simp [inconsistent, eq] at present

example : ¬ Chains inconsistent 3 := by
  intro chains
  have := (chains 2 (by omega) [] 1 [0] (by simp [inconsistent])).2
  simp [inconsistent] at this

example : buildPlan [] [] = buildExecutionPlan [] [] := rfl

#print axioms RootCollectedPlanning_holds
#print axioms GeneratedPlanning_holds
#print axioms subfields_planning
#print axioms collectFields_chains
#print axioms collectSubfields_chains

end
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.CollectedForestPlanning.Tests
