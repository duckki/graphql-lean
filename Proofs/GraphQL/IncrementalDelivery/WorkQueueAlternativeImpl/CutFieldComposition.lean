import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.CutTraceInterfaces
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.OriginFieldComposition

/-! Actual field cut derivations from recursive value derivations. A constructed
head map advances both actual supplies and preserves inherited metadata for the
tail. Only the actual fatal head branch adds a skipped sibling cone. -/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.OriginAccounting

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open ScheduledWork KeyRenaming

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

theorem responseField_cuts_of_values (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (children : ValueCutConstruction schema resolvers variables (fuel - 1))
    (parentType : Name) (source : ResolverValue ObjectRef) (name : Name)
    (fields : List FieldDetails) (path : ResponsePath) (usages : List Nat)
    (context : DeferMap) (route : List Nat) (keys : Nat → Nat) (left right : Nat)
    (supplies : SupplyMap keys left right)
    (ordered : ∀ details ∈ fields, UsageBefore left details.deferUsage)
    (usageBound : ∀ key ∈ usages, key < left)
    (contextBound : ∀ key ∈ context.flatMap RefRoles.fragmentRefs, key < left)
    : CompletionCutTrace
        ((RecordedExecution.executeResponseField schema resolvers variables fuel
            parentType source name fields path usages context route).run
          left).1
        ((EagerRecordedExecution.executeResponseField schema resolvers variables fuel
            parentType source name (fields.map (field keys)) path (usages.map keys)
            (context.map (fragment keys)) route).run
          right).1 := by
  cases fuel with
  | zero =>
      simpa only [RecordedExecution.executeResponseField, EagerRecordedExecution.executeResponseField,
        StateT.run_pure, id_pure_eq] using CompletionCutTrace.fault route (.error 1)
  | succ fuel =>
      simp only [Nat.add_sub_cancel] at children
      cases fields with
      | nil =>
          simpa only [RecordedExecution.executeResponseField, EagerRecordedExecution.executeResponseField,
            List.map_nil, StateT.run_pure, id_pure_eq] using CompletionCutTrace.fault route (.error 1)
      | cons head tail =>
          simp only [RecordedExecution.executeResponseField, EagerRecordedExecution.executeResponseField,
            List.map_cons, field]
          split
          · simp_all only [StateT.run_pure, id_pure_eq]
            exact CompletionCutTrace.fault _ _
          · rename_i definition lookupEq
            simp_all only
            split
            · simp_all only [StateT.run_pure, id_pure_eq]
              exact CompletionCutTrace.fault _ _
            · rename_i arguments argumentsEq
              simp_all only
              split
              · simp_all only [StateT.run_pure, id_pure_eq]
                exact CompletionCutTrace.fault _ _
              · rename_i resolved resolvedEq
                simp_all only
                have child := children definition.outputType (head :: tail) resolved
                  (path ++ [.field name]) usages context true (route ++ [0]) keys left right
                  supplies ordered usageBound contextBound
                simpa only [List.map_cons, field, run_bind, StateT.run_pure, id_pure_eq]
                  using child.map (fun value => [(name, value)])

theorem fields_cuts_of_values (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat)
    (children : ValueCutConstruction schema resolvers variables (fuel - 1))
    : FieldCutConstruction schema resolvers variables fuel := by
  intro parentType source fields
  induction fields with
  | nil =>
      intro path usages context route keys left right supplies ordered usageBound contextBound
      simpa only [RecordedExecution.executeCollectedFields,
        EagerRecordedExecution.executeCollectedFields, KeyRenaming.fields, List.map_nil,
        StateT.run_pure, id_pure_eq]
        using CompletionCutTrace.pure ([] : List (Name × ResponseValue))
  | cons entry rest ih =>
      intro path usages context route keys left right supplies ordered usageBound contextBound
      obtain ⟨name, group⟩ := entry
      have head := responseField_cuts_of_values schema resolvers variables fuel children parentType
        source name group path usages context (route ++ [0]) keys left right supplies
        (ordered (name, group) (by simp)) usageBound contextBound
      obtain ⟨middle, mapped⟩ := field_mapped_run schema resolvers variables fuel parentType source name
        group path usages context (route ++ [0]) keys left right supplies
        (ordered (name, group) (by simp)) usageBound contextBound
      dsimp only [eraseCompletionRun] at mapped
      simp only [RecordedExecution.executeCollectedFields, EagerRecordedExecution.executeCollectedFields,
        KeyRenaming.fields, List.map_cons, run_bind]
      cases outcome
            : ((RecordedExecution.executeResponseField schema resolvers variables fuel
                  parentType source name group path usages context (route ++ [0])).run
                left).1.report.outcome with
      | error errors =>
          simp only [StateT.run_pure, id_pure_eq]
          have known := CompletionCutTrace.fatal_cut List.append id
            (((EagerRecordedExecution.executeCollectedFields schema resolvers variables fuel parentType
              source (KeyRenaming.fields keys rest) path (usages.map keys) (context.map (fragment keys))
              (route ++ [1])).run
              ((EagerRecordedExecution.executeResponseField schema resolvers variables fuel parentType
                source name (group.map (field keys)) path (usages.map keys) (context.map (fragment keys))
                (route ++ [0])).run right).2).1)
            route head.1 outcome (field_fatal_positive schema resolvers variables fuel parentType source name group
              path usages context (route ++ [0]) left errors outcome)
            (executeResponseField_origins schema resolvers variables fuel parentType source name group
              path usages context (route ++ [0]) left).left
            (EagerScopes.executeCollectedFields_origins schema resolvers variables fuel parentType source
              (KeyRenaming.fields keys rest) path (usages.map keys) (context.map (fragment keys))
              (route ++ [1])
              ((EagerRecordedExecution.executeResponseField schema resolvers variables fuel parentType source name
                (group.map (field keys)) path (usages.map keys) (context.map (fragment keys))
                (route ++ [0])).run right).2).left
          rw [RecordedCompletion.map_id_of_empty (responseField_fatal_empty schema resolvers variables fuel
            parentType source name group path usages context (route ++ [0]) left errors outcome)] at known
          simpa only [KeyRenaming.fields] using known
      | ok value =>
          have restBefore : FieldsBefore left rest :=
            fun entry member => ordered entry (List.mem_cons_of_mem _ member)
          have tail := ih path usages context (route ++ [1]) middle _ _ mapped.supplies
            (restBefore.mono mapped.scheduledMonotone)
            (fun key member => Nat.lt_of_lt_of_le (usageBound key member) mapped.scheduledMonotone)
            (fun key member => Nat.lt_of_lt_of_le (contextBound key member) mapped.scheduledMonotone)
          rw [fields_prefix rest restBefore.below mapped.compatible,
            context_prefix context contextBound mapped.compatible,
            List.map_congr_left (fun key member => mapped.compatible key (usageBound key member))] at tail
          simpa only [run_bind, StateT.run_pure, id_pure_eq, KeyRenaming.fields]
            using head.combine List.append tail

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.OriginAccounting
