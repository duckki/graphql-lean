import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.CutTraceInterfaces

/-! Actual ordinary-list and stream-tail cut derivations at growing mapped
supplies. Sibling cuts change origin inventories; the existing map construction
only reconciles delivery metadata. The shared fatal stream stop is not another omission. -/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.OriginAccounting

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open ScheduledWork KeyRenaming

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

theorem list_cuts_of_values (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat)
    (children : ValueCutConstruction schema resolvers variables fuel)
    (itemType : TypeRef) (fields : List FieldDetails)
    (sources : List (ResolverValue ObjectRef)) (path : ResponsePath) (index : Nat)
    (usages : List Nat) (context : DeferMap) (route : List Nat) (keys : Nat → Nat)
    (left right : Nat) (supplies : SupplyMap keys left right)
    (ordered : ∀ details ∈ fields, UsageBefore left details.deferUsage)
    (usageBound : ∀ key ∈ usages, key < left)
    (contextBound : ∀ key ∈ context.flatMap RefRoles.fragmentRefs, key < left)
    : CompletionCutTrace
        ((RecordedExecution.completeListValue schema resolvers variables fuel itemType
            fields sources path index usages context route).run
          left).1
        ((EagerRecordedExecution.completeListValue schema resolvers variables fuel
            itemType (fields.map (field keys)) sources path index (usages.map keys)
            (context.map (fragment keys)) route).run
          right).1 := by
  induction sources generalizing index route keys left right with
  | nil =>
      simpa only [RecordedExecution.completeListValue, EagerRecordedExecution.completeListValue,
        StateT.run_pure, id_pure_eq] using CompletionCutTrace.pure ([] : List ResponseValue)
  | cons source rest ih =>
      have head := children itemType fields source (path ++ [.index index]) usages context false
        (route ++ [0]) keys left right supplies ordered usageBound contextBound
      obtain ⟨middle, mapped⟩ := value_mapped_run schema resolvers variables fuel itemType fields source
        (path ++ [.index index]) usages context false (route ++ [0]) keys left right supplies ordered
        usageBound contextBound
      dsimp only [eraseCompletionRun] at mapped
      simp only [RecordedExecution.completeListValue, EagerRecordedExecution.completeListValue, run_bind]
      cases outcome
            : ((RecordedExecution.completeValue schema resolvers variables fuel itemType
                  fields source (path ++ [.index index]) usages context false
                  (route ++ [0])).run
                left).1.report.outcome with
      | error errors =>
          simp only [StateT.run_pure, id_pure_eq]
          exact CompletionCutTrace.fatal_cut List.cons (fun value => [value]) _ route head.1 outcome
            (value_fatal_positive schema resolvers variables fuel itemType fields source
              (path ++ [.index index]) usages context false (route ++ [0]) left errors outcome)
            (completeValue_origins schema resolvers variables fuel itemType fields source
              (path ++ [.index index]) usages context false (route ++ [0]) left).left
            (EagerScopes.completeListValue_origins schema resolvers variables fuel itemType
              (fields.map (field keys)) rest path (index + 1) (usages.map keys)
              (context.map (fragment keys)) (route ++ [1])
              ((EagerRecordedExecution.completeValue schema resolvers variables fuel itemType
                (fields.map (field keys)) source (path ++ [.index index]) (usages.map keys)
                (context.map (fragment keys)) false (route ++ [0])).run right).2).left
      | ok value =>
          have tail := ih (index + 1) (route ++ [1]) middle _ _ mapped.supplies
            (fun details member => usageBefore_mono _ (ordered details member) mapped.scheduledMonotone)
            (fun key member => Nat.lt_of_lt_of_le (usageBound key member) mapped.scheduledMonotone)
            (fun key member => Nat.lt_of_lt_of_le (contextBound key member) mapped.scheduledMonotone)
          rw [fieldDetails_prefix fields ordered mapped.compatible,
            context_prefix context contextBound mapped.compatible,
            List.map_congr_left (fun key member => mapped.compatible key (usageBound key member))] at tail
          simpa only [run_bind, StateT.run_pure, id_pure_eq] using head.combine List.cons tail

theorem streamItems_cuts_of_values (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat)
    (children : ValueCutConstruction schema resolvers variables fuel)
    (itemType : TypeRef) (fields : List FieldDetails)
    (sources : List (ResolverValue ObjectRef)) (path : ResponsePath) (index : Nat)
    (route : List Nat) (keys : Nat → Nat) (left right : Nat)
    (supplies : SupplyMap keys left right)
    (ordered : ∀ details ∈ fields, UsageBefore left details.deferUsage)
    : ItemsCutTrace
        ((RecordedExecution.completeStreamItems schema resolvers variables fuel itemType
            fields sources path index route).run
          left).1
        ((EagerRecordedExecution.completeStreamItems schema resolvers variables fuel
            itemType (fields.map (field keys)) sources path index route).run
          right).1 := by
  induction sources generalizing index route keys left right with
  | nil =>
      simpa only [RecordedExecution.completeStreamItems, EagerRecordedExecution.completeStreamItems,
        StateT.run_pure, id_pure_eq] using ItemsCutTrace.nil
  | cons source rest ih =>
      have head := children itemType fields source (path ++ [.index index]) [] [] false (route ++ [0])
        keys left right supplies ordered (by simp) (by simp)
      obtain ⟨middle, mapped⟩ := value_mapped_run schema resolvers variables fuel itemType fields source
        (path ++ [.index index]) [] [] false (route ++ [0]) keys left right supplies ordered (by simp) (by simp)
      simp only [List.map_nil] at head mapped
      dsimp only [eraseCompletionRun] at mapped
      have same := head.1.refines.1.1
      simp only [RecordedExecution.completeStreamItems, EagerRecordedExecution.completeStreamItems, run_bind]
      cases outcome : ((RecordedExecution.completeValue schema resolvers variables fuel itemType fields source
          (path ++ [.index index]) [] [] false (route ++ [0])).run left).1.report.outcome
      <;> cases eagerOutcome : ((EagerRecordedExecution.completeValue schema resolvers variables fuel itemType
          (fields.map (field keys)) source (path ++ [.index index]) [] [] false (route ++ [0])).run
          right).1.report.outcome
      <;> simp only [ScheduledErrors.SameData, outcome, eagerOutcome] at same
      · simp only [StateT.run_pure, id_pure_eq]
        exact .cons head.1 .empty .nil
      · have tail := ih (index + 1) (route ++ [1]) middle _ _ mapped.supplies
          (fun details member => usageBefore_mono _ (ordered details member) mapped.scheduledMonotone)
        rw [fieldDetails_prefix fields ordered mapped.compatible] at tail
        simpa only [run_bind, StateT.run_pure, id_pure_eq] using ItemsCutTrace.cons head.1 head.2 tail

theorem listWithStream_cuts_of_values (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (children : ValueCutConstruction schema resolvers variables fuel)
    (itemType : TypeRef) (fields : List FieldDetails)
    (sources : List (ResolverValue ObjectRef)) (path : ResponsePath) (usages : List Nat)
    (context : DeferMap) (allowStream : Bool) (route : List Nat) (keys : Nat → Nat)
    (left right : Nat) (supplies : SupplyMap keys left right)
    (ordered : ∀ details ∈ fields, UsageBefore left details.deferUsage)
    (usageBound : ∀ key ∈ usages, key < left)
    (contextBound : ∀ key ∈ context.flatMap RefRoles.fragmentRefs, key < left)
    : CompletionCutTrace
        ((RecordedExecution.completeListValueWithStream schema resolvers variables fuel
            itemType fields sources path usages context allowStream route).run
          left).1
        ((EagerRecordedExecution.completeListValueWithStream schema resolvers variables
            fuel itemType (fields.map (field keys)) sources path (usages.map keys)
            (context.map (fragment keys)) allowStream route).run
          right).1 := by
  simp only [RecordedExecution.completeListValueWithStream, EagerRecordedExecution.completeListValueWithStream,
    mapped_field_directives]
  split
  · simp_all only [StateT.run_pure, id_pure_eq]
    exact CompletionCutTrace.fault _ _
  · simp_all only
    have initial := list_cuts_of_values schema resolvers variables fuel children itemType fields sources
      path 0 usages context (route ++ [0]) keys left right supplies ordered usageBound contextBound
    simpa only [run_bind, StateT.run_pure, id_pure_eq] using initial.catchNull ResponseValue.list
  · rename_i usage actual
    simp only [actual]
    have initial := list_cuts_of_values schema resolvers variables fuel children itemType fields
      (sources.take usage.initialCount) path 0 usages context (route ++ [0]) keys left right supplies ordered
      usageBound contextBound
    obtain ⟨middle, mapped⟩ := list_mapped_run schema resolvers variables fuel itemType fields
      (sources.take usage.initialCount) path 0 usages context (route ++ [0]) keys left right supplies ordered
      usageBound contextBound
    dsimp only [eraseCompletionRun] at mapped
    have same := initial.1.refines.1.1
    simp only [run_bind]
    cases outcome : ((RecordedExecution.completeListValue schema resolvers variables fuel itemType fields
        (sources.take usage.initialCount) path 0 usages context (route ++ [0])).run left).1.report.outcome
    <;> cases eagerOutcome : ((EagerRecordedExecution.completeListValue schema resolvers variables fuel itemType
        (fields.map (field keys)) (sources.take usage.initialCount) path 0 (usages.map keys)
        (context.map (fragment keys)) (route ++ [0])).run right).1.report.outcome
    <;> simp only [ScheduledErrors.SameData, outcome, eagerOutcome] at same
    · simpa only [StateT.run_pure, id_pure_eq] using initial.catchNull ResponseValue.list
    · simp only
      split
      · simpa only [StateT.run_pure, id_pure_eq] using initial.catchNull ResponseValue.list
      · let cutFinish := ((RecordedExecution.completeListValue schema resolvers variables fuel itemType fields
          (sources.take usage.initialCount) path 0 usages context (route ++ [0])).run left).2
        let eagerFinish := ((EagerRecordedExecution.completeListValue schema resolvers variables fuel itemType
          (fields.map (field keys)) (sources.take usage.initialCount) path 0 (usages.map keys)
          (context.map (fragment keys)) (route ++ [0])).run right).2
        have afterBoundary : middle (cutFinish + 1) = eagerFinish + 1 := by
          simpa only [Nat.add_zero, mapped.supplies.boundary]
            using mapped.supplies.fresh 1
        have suppliesAfter := mapped.supplies.advance (Nat.le_succ cutFinish)
        rw [afterBoundary] at suppliesAfter
        have tail := streamItems_cuts_of_values schema resolvers variables fuel children itemType
          (fields.map (fun details => { details with deferUsage := none })) (sources.drop usage.initialCount)
          path usage.initialCount (route ++ [1]) middle (cutFinish + 1) (eagerFinish + 1) suppliesAfter (by
            intro details member
            obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
            simp [UsageBefore])
        have mappedFields : (fields.map (fun details => { details with deferUsage := none })).map (field middle)
            = (fields.map (field keys)).map (fun details => { details with deferUsage := none }) := by
          rw [mapped_stream_fields]
          simp [List.map_map, field, Function.comp_def]
        rw [mappedFields] at tail
        simp only [freshNodeRef, run_bind, StateT.run_get, StateT.run_set, StateT.run_pure, id_pure_eq,
          CompletionCutTrace]
        exact ⟨(initial.catchNull ResponseValue.list).1,
          .combine (initial.catchNull ResponseValue.list).2 (.stream tail)⟩

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.OriginAccounting
