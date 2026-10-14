import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.CutPlanComposition
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.CutListComposition
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.PairedOriginCoverage

/-! Constructed reached-cut derivations for arbitrary finite recursive execution. Fuel
and type induction close every value/field/object/defer/stream child. Original
collection supplies metadata invariants at the root; desired output correspondence
is never a premise. Recording histories are constructed separately from this derivation. -/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.OriginAccounting

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open GraphQL.IncrementalDelivery.Semantics.RefRegions
open ScheduledWork KeyRenaming

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

theorem valueCutConstruction_holds (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat)
    : ValueCutConstruction schema resolvers variables fuel := by
  induction fuel using Nat.strongRecOn with
  | ind fuel smaller =>
      cases fuel with
      | zero => exact valueCut_zero schema resolvers variables
      | succ fuel =>
          have values := smaller fuel (Nat.lt_succ_self _)
          have scopes := fields_cuts_of_values schema resolvers variables fuel
            (smaller (fuel - 1) (by omega))
          have plans := plan_cuts_of_fields schema resolvers variables fuel scopes
          intro fieldType
          induction fieldType with
          | named name =>
              intro fields source path usages context allowStream route keys left right supplies
                ordered usageBound contextBound
              cases source with
              | null =>
                  simpa only [RecordedExecution.completeValue, EagerRecordedExecution.completeValue,
                    StateT.run_pure, id_pure_eq] using CompletionCutTrace.pure ResponseValue.null
              | scalar scalar =>
                  simp only [RecordedExecution.completeValue, EagerRecordedExecution.completeValue]
                  split
                  · simpa only [StateT.run_pure, id_pure_eq] using CompletionCutTrace.fault route (.error 1)
                  · simpa only [StateT.run_pure, id_pure_eq] using CompletionCutTrace.pure (ResponseValue.scalar scalar)
              | object runtimeType reference =>
                  exact object_cuts_of_plan schema resolvers variables fuel plans name runtimeType reference
                    fields path usages context allowStream route keys left right supplies ordered usageBound contextBound
              | list items =>
                  simpa only [RecordedExecution.completeValue, EagerRecordedExecution.completeValue,
                    StateT.run_pure, id_pure_eq] using CompletionCutTrace.fault route (.error 1)
          | list inner _ =>
              intro fields source path usages context allowStream route keys left right supplies
                ordered usageBound contextBound
              cases source with
              | null =>
                  simpa only [RecordedExecution.completeValue, EagerRecordedExecution.completeValue,
                    StateT.run_pure, id_pure_eq] using CompletionCutTrace.pure ResponseValue.null
              | scalar scalar =>
                  simpa only [RecordedExecution.completeValue, EagerRecordedExecution.completeValue,
                    StateT.run_pure, id_pure_eq] using CompletionCutTrace.fault route (.error 1)
              | object runtimeType reference =>
                  simpa only [RecordedExecution.completeValue, EagerRecordedExecution.completeValue,
                    StateT.run_pure, id_pure_eq] using CompletionCutTrace.fault route (.error 1)
              | list items =>
                  simpa only [RecordedExecution.completeValue,
                    EagerRecordedExecution.completeValue]
                    using listWithStream_cuts_of_values schema resolvers variables fuel
                      values inner fields items path usages context allowStream
                      (route ++ [0]) keys left right supplies ordered usageBound
                      contextBound
          | nonNull inner child =>
              intro fields source path usages context allowStream route keys left right supplies
                ordered usageBound contextBound
              have completed := child fields source path usages context allowStream (route ++ [0]) keys left right
                supplies ordered usageBound contextBound
              simpa only [RecordedExecution.completeValue, EagerRecordedExecution.completeValue,
                run_bind, StateT.run_pure, id_pure_eq] using completed.nonNull route

theorem fieldCutConstruction_holds (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat)
    : FieldCutConstruction schema resolvers variables fuel :=
  fields_cuts_of_values schema resolvers variables fuel
    (valueCutConstruction_holds schema resolvers variables (fuel - 1))

theorem planCutConstruction_holds (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat)
    : PlanCutConstruction schema resolvers variables fuel :=
  plan_cuts_of_fields schema resolvers variables fuel
    (fieldCutConstruction_holds schema resolvers variables fuel)

theorem root_cut_trace (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (parentType : Name)
    (source : ResolverValue ObjectRef) (selections : List Selection) (route : List Nat)
    (keys : Nat → Nat) (left right : Nat) (supplies : SupplyMap keys left right)
    : CompletionCutTrace
        ((RecordedExecution.executeRootSelectionSetCore schema resolvers variables fuel
            parentType source selections route).run
          left).1
        ((EagerRecordedExecution.executeRootSelectionSetCore schema resolvers variables
            fuel parentType source selections route).run
          right).1 := by
  let collected := (collectFields schema variables parentType source selections).run left
  have collectedKeys := collectFields_refs schema variables parentType source selections none left (by simp [UsageBefore])
  have plannedBefore := build_plan_before collected.1.collectedFieldsMap [] collectedKeys.2.1
  have contextBound := mapRefs_new_bound [] collected.1.newDeferUsages [] collected.2 (by simp)
    (fun usage member => (collectedKeys.2.2 usage member).2.1)
  have child := planCutConstruction_holds schema resolvers variables fuel parentType source
    collected.1.newDeferUsages (buildExecutionPlan collected.1.collectedFieldsMap []) [] [] [] route
    keys collected.2 (keys collected.2) (supplies.advance collectedKeys.1)
    plannedBefore.1 plannedBefore.2 (by simp) contextBound
  have collectedMapped := collectFields_maps keys schema variables parentType source selections none left supplies.fresh
  simp only [Option.map_none] at collectedMapped
  rw [supplies.boundary] at collectedMapped
  have plannedMapped := build_plan supplies.injective collected.1.collectedFieldsMap ([] : List Nat)
  simp only [List.map_nil] at plannedMapped
  simp only [RecordedExecution.executeRootSelectionSetCore, EagerRecordedExecution.executeRootSelectionSetCore,
    run_bind, collectedMapped, collection]
  rw [plannedMapped]
  simpa only [List.map_nil, collected] using child

/-- General actual root cut derivation, with arbitrary object-valued resolvers, deferred
groups and streamed objects. The caller supplies only the original compatible starts. -/
def RecursiveCutConstruction : Prop :=
  ∀ (ObjectRef : Type) (schema : Schema) (resolvers : Resolvers ObjectRef) variables fuel
    parentType (source : ResolverValue ObjectRef) selections route keys left right,
    SupplyMap keys left right
    → CompletionCutTrace
        ((RecordedExecution.executeRootSelectionSetCore schema resolvers variables fuel
            parentType source selections route).run
          left).1
        ((EagerRecordedExecution.executeRootSelectionSetCore schema resolvers variables
            fuel parentType source selections route).run
          right).1

theorem recursiveCutConstruction_holds : RecursiveCutConstruction := by
  intro ObjectRef schema resolvers variables fuel parentType source selections route keys left right supplies
  exact root_cut_trace schema resolvers variables fuel parentType source selections route keys left right supplies

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.OriginAccounting
