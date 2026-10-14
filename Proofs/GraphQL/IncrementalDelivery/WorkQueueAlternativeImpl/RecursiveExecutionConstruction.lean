import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RecursivePlanComposition
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RecursiveListComposition

/-! Constructed recursive correspondence between the proof-only sibling-cut policy
and original eager execution. Fuel induction closes object, deferred-plan, list and
stream-item children; structural type induction closes non-null wrapping at the same
fuel. The one final witness is constructed from actual executions, not assumed related
outputs. This is pure finite execution refinement, not native async-history refinement. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.ScheduledWork

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open GraphQL.IncrementalDelivery.Semantics.RefRegions
open KeyRenaming ScheduledErrors

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

-----------------------------------------------------------------------------------------
-- Close all actual value children by fuel and type structure
-----------------------------------------------------------------------------------------

theorem valueRunConstruction_holds (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat)
    : ValueRunConstruction schema resolvers variables fuel := by
  induction fuel using Nat.strongRecOn with
  | ind fuel smaller =>
      cases fuel with
      | zero =>
          intro fieldType fields value path usages context allowStream keys left right
            supplies _ _ _
          exact ⟨
            keys,
            by simpa only [ScheduledExecution.completeValue, Execution.completeValue,
              Completion.error] using pureResult_run supplies (.error 1)
          ⟩
      | succ fuel =>
          have values := smaller fuel (Nat.lt_succ_self _)
          have scopes := fieldScope_run_of_values schema resolvers variables fuel
            (smaller (fuel - 1) (by omega))
          have plans := plan_run_of_fields schema resolvers variables fuel scopes
          intro fieldType
          induction fieldType with
          | named typeName =>
              intro fields value path usages context allowStream keys left right supplies
                ordered usageBound contextBound
              cases value with
              | null =>
                  exact ⟨
                    keys,
                    by
                      simpa only [ScheduledExecution.completeValue,
                        Execution.completeValue, Completion.pure]
                        using pureResult_run (α := ResponseValue) supplies
                          (.ok (.null, 0))
                  ⟩
              | scalar scalar =>
                  simp only [ScheduledExecution.completeValue, Execution.completeValue]
                  split
                  · exact ⟨keys, pureResult_run supplies _⟩
                  · exact ⟨keys, pureResult_run supplies _⟩
              | object runtimeType reference =>
                  exact object_run_of_plan schema resolvers variables fuel plans typeName
                    runtimeType reference fields path usages context allowStream keys left right
                    supplies ordered usageBound contextBound
              | list items =>
                  exact ⟨
                    keys,
                    by
                      simpa only [ScheduledExecution.completeValue,
                        Execution.completeValue, Completion.error]
                        using pureResult_run supplies (.error 1)
                  ⟩
          | list inner _ =>
              intro fields value path usages context allowStream keys left right supplies
                ordered usageBound contextBound
              cases value with
              | null =>
                  exact ⟨
                    keys,
                    by
                      simpa only [ScheduledExecution.completeValue,
                        Execution.completeValue, Completion.pure]
                        using pureResult_run (α := ResponseValue) supplies
                          (.ok (.null, 0))
                  ⟩
              | scalar scalar =>
                  exact ⟨
                    keys,
                    by
                      simpa only [ScheduledExecution.completeValue,
                        Execution.completeValue, Completion.error]
                        using pureResult_run supplies (.error 1)
                  ⟩
              | object runtimeType reference =>
                  exact ⟨
                    keys,
                    by
                      simpa only [ScheduledExecution.completeValue,
                        Execution.completeValue, Completion.error]
                        using pureResult_run supplies (.error 1)
                  ⟩
              | list items =>
                  simpa only [ScheduledExecution.completeValue, Execution.completeValue]
                    using listWithStream_run_of_values schema resolvers variables fuel
                      values inner fields items path usages context allowStream keys left
                      right supplies ordered usageBound contextBound
          | nonNull inner typeChild =>
              intro fields value path usages context allowStream keys left right supplies
                ordered usageBound contextBound
              obtain ⟨next, completed⟩ := typeChild fields value path usages context allowStream
                keys left right supplies ordered usageBound contextBound
              exact ⟨
                next,
                by simpa only [ScheduledExecution.completeValue, Execution.completeValue,
                  run_bind, StateT.run_pure, id_pure_eq] using completed.nonNull
              ⟩

-----------------------------------------------------------------------------------------
-- Field and plan roots now construct children without any recursive relation premise
-----------------------------------------------------------------------------------------

theorem fieldScopeRunConstruction_holds (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    : FieldScopeRunConstruction schema resolvers variables fuel :=
  fieldScope_run_of_values schema resolvers variables fuel
    (valueRunConstruction_holds schema resolvers variables (fuel - 1))

theorem planRunConstruction_holds (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat)
    : PlanRunConstruction schema resolvers variables fuel :=
  plan_run_of_fields schema resolvers variables fuel
    (fieldScopeRunConstruction_holds schema resolvers variables fuel)

-----------------------------------------------------------------------------------------
-- Original root collection supplies every input invariant for the full execution
-----------------------------------------------------------------------------------------

/-- Arbitrary finite root execution constructs one compatible injective key map.
No literal resolver restriction, output correspondence, or independent per-child map
is a premise. Public execution still eagerly aggregates all executed sibling errors. -/
def RecursiveExecutionConstruction : Prop :=
  ∀ (ObjectRef : Type) (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) fuel parentType (source : ResolverValue ObjectRef)
    selections keys left right,
    SupplyMap keys left right
    → ∃ next,
        RunRefines keys next left right
          ((ScheduledExecution.executeRootSelectionSetCore schema resolvers variables fuel
              parentType source selections).run
            left)
          ((Execution.executeRootSelectionSetCore schema resolvers variables fuel
              parentType source selections).run
            right)

theorem recursiveExecutionConstruction_holds : RecursiveExecutionConstruction := by
  intro ObjectRef schema resolvers variables fuel parentType source selections keys left right supplies
  let collected := (collectFields schema variables parentType source selections).run left
  have collectedKeys := collectFields_refs schema variables parentType source selections none left (by simp [UsageBefore])
  have plannedBefore := build_plan_before collected.1.collectedFieldsMap [] collectedKeys.2.1
  have contextBound := mapRefs_new_bound [] collected.1.newDeferUsages [] collected.2 (by simp)
    (fun usage member => (collectedKeys.2.2 usage member).2.1)
  obtain ⟨next, planned⟩ := planRunConstruction_holds schema resolvers variables fuel
    parentType source collected.1.newDeferUsages (buildExecutionPlan collected.1.collectedFieldsMap [])
    [] [] [] keys collected.2 (keys collected.2) (supplies.advance collectedKeys.1)
    plannedBefore.1 plannedBefore.2 (by simp) contextBound
  have collectedMapped := collectFields_maps keys schema variables parentType source
    selections none left supplies.fresh
  simp only [Option.map_none] at collectedMapped
  rw [supplies.boundary] at collectedMapped
  have plannedMapped := build_plan supplies.injective collected.1.collectedFieldsMap ([] : List Nat)
  simp only [List.map_nil] at plannedMapped
  simp only [ScheduledExecution.executeRootSelectionSetCore, Execution.executeRootSelectionSetCore,
    run_bind, collectedMapped, collection]
  rw [plannedMapped]
  refine ⟨next, ⟨?_, planned.supplies,
    Nat.le_trans collectedKeys.1 planned.scheduledMonotone,
    Nat.le_trans (supplies.orderedBoundary collectedKeys.1) planned.eagerMonotone,
    planned.bounded, planned.completion⟩⟩
  intro key earlier
  exact planned.compatible key (Nat.lt_of_lt_of_le earlier collectedKeys.1)

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.ScheduledWork
