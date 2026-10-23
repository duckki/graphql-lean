import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.OriginRecursiveInterfaces

/-! Actual field origin coverage from recursive value coverage. A constructed
head map advances both actual supplies and preserves inherited metadata for the
tail. Fatal cuts retain head identities and discard future Work on both sides. -/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.OriginAccounting

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open ScheduledWork KeyRenaming

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

theorem RecordedCompletion.map_fatal_empty (f : α → β) (completed : RecordedCompletion α)
    (errors : Nat) (fatal : (completed.map f).report.outcome = .error errors)
    : (completed.map f).work = .empty := by
  cases outcome : completed.report.outcome <;>
    simp_all [RecordedCompletion.map, Report.map]

theorem responseField_fatal_empty (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (parentType : Name)
    (source : ResolverValue ObjectRef) (name : Name) (fields : List FieldDetails)
    (path : ResponsePath) (usages : List Nat) (context : DeferMap) (route : List Nat)
    (supply : Nat)
    : ∀ errors,
        ((RecordedExecution.executeResponseField schema resolvers variables fuel
            parentType source name fields path usages context route).run
            supply).1.report.outcome
          = .error errors
        → ((RecordedExecution.executeResponseField schema resolvers variables fuel
              parentType source name fields path usages context route).run
            supply).1.work
          = .empty := by
  cases fuel with
  | zero => simp [RecordedExecution.executeResponseField, RecordedCompletion.fault]
  | succ fuel =>
      cases fields with
      | nil => simp [RecordedExecution.executeResponseField, RecordedCompletion.fault]
      | cons head tail =>
          simp only [RecordedExecution.executeResponseField]
          split
          · simp [RecordedCompletion.fault]
          · split
            · simp [RecordedCompletion.fault]
            · split
              · simp [RecordedCompletion.fault]
              · simp only [run_bind, StateT.run_pure, id_pure_eq]
                exact fun errors fatal => RecordedCompletion.map_fatal_empty _ _ errors fatal

theorem RecordedCompletion.map_id_of_empty {completed : RecordedCompletion α}
    (empty : completed.work = .empty) (fatal : completed.report.outcome = .error errors)
    : completed.map id = completed := by
  obtain ⟨⟨outcome, origins, accounts⟩, work, cause⟩ := completed
  simp_all [RecordedCompletion.map, Report.map]

theorem responseField_origins_of_values (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (children : ValueOriginsConstruction schema resolvers variables (fuel - 1))
    (parentType : Name) (source : ResolverValue ObjectRef) (name : Name)
    (fields : List FieldDetails) (path : ResponsePath) (usages : List Nat)
    (context : DeferMap) (route : List Nat) (keys : Nat → Nat) (left right : Nat)
    (supplies : SupplyMap keys left right)
    (ordered : ∀ details ∈ fields, UsageBefore left details.deferUsage)
    (usageBound : ∀ key ∈ usages, key < left)
    (contextBound : ∀ key ∈ context.flatMap RefRoles.fragmentRefs, key < left)
    : CompletionOriginsRefine
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
        StateT.run_pure, id_pure_eq] using CompletionOriginsRefine.fault route (.error 1)
  | succ fuel =>
      simp only [Nat.add_sub_cancel] at children
      cases fields with
      | nil =>
          simpa only [RecordedExecution.executeResponseField, EagerRecordedExecution.executeResponseField,
            List.map_nil, StateT.run_pure, id_pure_eq] using CompletionOriginsRefine.fault route (.error 1)
      | cons head tail =>
          simp only [RecordedExecution.executeResponseField, EagerRecordedExecution.executeResponseField,
            List.map_cons, field]
          split
          · simp_all only [StateT.run_pure, id_pure_eq]
            exact CompletionOriginsRefine.fault _ _
          · rename_i definition lookupEq
            simp_all only
            split
            · simp_all only [StateT.run_pure, id_pure_eq]
              exact CompletionOriginsRefine.fault _ _
            · rename_i arguments argumentsEq
              simp_all only
              split
              · simp_all only [StateT.run_pure, id_pure_eq]
                exact CompletionOriginsRefine.fault _ _
              · rename_i resolved resolvedEq
                simp_all only
                have child := children definition.outputType (head :: tail) resolved
                  (path ++ [.field name]) usages context true (route ++ [0]) keys left right
                  supplies ordered usageBound contextBound
                simpa only [List.map_cons, field, run_bind, StateT.run_pure, id_pure_eq]
                  using child.map (fun value => [(name, value)])

theorem fields_origins_of_values (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat)
    (children : ValueOriginsConstruction schema resolvers variables (fuel - 1))
    : FieldOriginsConstruction schema resolvers variables fuel := by
  intro parentType source fields
  induction fields with
  | nil =>
      intro path usages context route keys left right supplies ordered usageBound contextBound
      simpa only [RecordedExecution.executeCollectedFields,
        EagerRecordedExecution.executeCollectedFields, KeyRenaming.fields, List.map_nil,
        StateT.run_pure, id_pure_eq]
        using CompletionOriginsRefine.pure ([] : List (Name × ResponseValue))
  | cons entry rest ih =>
      intro path usages context route keys left right supplies ordered usageBound contextBound
      obtain ⟨name, group⟩ := entry
      have head := responseField_origins_of_values schema resolvers variables fuel children parentType
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
          have known := CompletionOriginsRefine.fatal_cut List.append id
            (((EagerRecordedExecution.executeCollectedFields schema resolvers variables fuel parentType
              source (KeyRenaming.fields keys rest) path (usages.map keys) (context.map (fragment keys))
              (route ++ [1])).run
              ((EagerRecordedExecution.executeResponseField schema resolvers variables fuel parentType
                source name (group.map (field keys)) path (usages.map keys) (context.map (fragment keys))
                (route ++ [0])).run right).2).1)
            head.1 outcome (field_fatal_positive schema resolvers variables fuel parentType source name group
              path usages context (route ++ [0]) left errors outcome)
          rw [RecordedCompletion.map_id_of_empty (responseField_fatal_empty schema resolvers variables fuel
            parentType source name group path usages context (route ++ [0]) left errors outcome)
            outcome] at known
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
