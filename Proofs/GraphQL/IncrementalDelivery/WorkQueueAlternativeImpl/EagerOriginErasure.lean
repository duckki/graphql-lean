import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.EagerOriginExecutor
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.OriginErasure

/-! Exact erasure of primitive-origin annotations to unchanged public eager execution.
All sibling errors remain aggregated. Original response-field decomposition is reused;
retained Work, its association and every actual delivery-key supply are preserved. -/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.OriginAccounting

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics

namespace EagerErasure

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map
attribute [local simp] RecordedCompletion.erase_pure RecordedCompletion.erase_fault
  RecordedCompletion.erase_combine RecordedCompletion.erase_map
  RecordedCompletion.erase_catchNull RecordedCompletion.erase_nonNull
attribute [local simp] erase_result

mutual
  theorem executeCollectedFields_erases (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (parentType : Name) (source : ResolverValue ObjectRef) (fields : CollectedFieldsMap)
      (path : ResponsePath) (usages : List Nat) (context : DeferMap) (route : List Nat)
      (state : Nat)
      : eraseCompletionRun
          ((EagerRecordedExecution.executeCollectedFields schema resolvers
              variables fuel parentType source fields path usages context route).run
            state)
        = (Execution.executeCollectedFields schema resolvers variables fuel
            parentType source fields path usages context).run
            state := by
    cases fields with
    | nil => simp [EagerRecordedExecution.executeCollectedFields,
        Execution.executeCollectedFields, eraseCompletionRun]
    | cons field rest =>
        obtain ⟨name, group⟩ := field
        have head := executeResponseField_erases schema resolvers variables fuel parentType
          source name group path usages context (route ++ [0]) state
        rw [executeCollectedFields_eq]
        simp only [EagerRecordedExecution.executeCollectedFields, run_bind,
          StateT.run_pure, id_pure_eq]
        rw [← head]
        dsimp only [eraseCompletionRun]
        have tail := executeCollectedFields_erases schema resolvers variables fuel parentType
          source rest path usages context (route ++ [1])
          ((EagerRecordedExecution.executeResponseField schema resolvers variables fuel parentType
            source name group path usages context (route ++ [0])).run state).2
        rw [← tail]
        simp only [eraseCompletionRun, RecordedCompletion.erase_combine]
  termination_by (fuel, 4, 0, sizeOf fields)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals omega

  theorem executeResponseField_erases (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (parentType : Name)
      (source : ResolverValue ObjectRef) (name : Name) (fields : List FieldDetails)
      (path : ResponsePath) (usages : List Nat) (context : DeferMap) (route : List Nat)
      (state : Nat)
      : eraseCompletionRun
          ((EagerRecordedExecution.executeResponseField schema resolvers
              variables fuel parentType source name fields path usages context route).run
            state)
        = (Semantics.executeResponseField schema resolvers variables fuel
            parentType source name fields path usages context).run
            state := by
    cases fuel with
    | zero => simp [EagerRecordedExecution.executeResponseField,
        Semantics.executeResponseField, eraseCompletionRun, Completion.error]
    | succ fuel =>
        cases fields with
        | nil => simp [EagerRecordedExecution.executeResponseField,
            Semantics.executeResponseField, eraseCompletionRun, Completion.error]
        | cons field rest =>
            simp only [EagerRecordedExecution.executeResponseField,
              Semantics.executeResponseField]
            split
            · simp_all [eraseCompletionRun, Completion.error]
            · rename_i definition lookupEq
              simp_all only
              split
              · cases definition.outputType <;>
                  simp_all [eraseCompletionRun, singleFieldResult, handleFieldError,
                    TypeRef.isNonNull]
              · rename_i arguments argumentsEq
                simp_all only
                split
                · cases definition.outputType <;>
                    simp_all [eraseCompletionRun, singleFieldResult, handleFieldError,
                      TypeRef.isNonNull]
                · rename_i resolved resolvedEq
                  simp_all only
                  have child := completeValue_erases schema resolvers variables fuel
                    definition.outputType (field :: rest) resolved
                    (path ++ [.field name]) usages context true (route ++ [0]) state
                  simp only [run_bind, StateT.run_pure, id_pure_eq]
                  rw [← child]
                  simp only [eraseCompletionRun, RecordedCompletion.erase_map]
  termination_by (fuel, 3, 0, sizeOf fields)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  theorem completeValue_erases (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (fieldType : TypeRef)
      (fields : List FieldDetails) (value : ResolverValue ObjectRef)
      (path : ResponsePath) (usages : List Nat) (context : DeferMap) (allowStream : Bool)
      (route : List Nat) (state : Nat)
      : eraseCompletionRun
          ((EagerRecordedExecution.completeValue schema resolvers variables
              fuel fieldType fields value path usages context allowStream route).run
            state)
        = (Execution.completeValue schema resolvers variables fuel fieldType
            fields value path usages context allowStream).run
            state := by
    cases fuel with
    | zero => simp [EagerRecordedExecution.completeValue, Execution.completeValue,
        eraseCompletionRun, Completion.error]
    | succ fuel =>
        cases fieldType with
        | nonNull inner =>
            have child := completeValue_erases schema resolvers variables (fuel + 1) inner
              fields value path usages context allowStream (route ++ [0]) state
            simp only [EagerRecordedExecution.completeValue, Execution.completeValue,
              run_bind, StateT.run_pure, id_pure_eq]
            rw [← child]
            simp only [eraseCompletionRun, RecordedCompletion.erase_nonNull]
        | named parentType =>
            cases value with
            | null =>
                simp [EagerRecordedExecution.completeValue, Execution.completeValue,
                  eraseCompletionRun]
            | scalar scalar =>
                simp only [EagerRecordedExecution.completeValue, Execution.completeValue]
                split <;> simp [eraseCompletionRun, Completion.error]
            | list items => simp [EagerRecordedExecution.completeValue,
                Execution.completeValue, eraseCompletionRun, Completion.error]
            | object runtimeType reference =>
                simp only [EagerRecordedExecution.completeValue, Execution.completeValue]
                split
                · simp [eraseCompletionRun, Completion.error]
                · simp only [run_bind, StateT.run_pure, id_pure_eq]
                  let collected := (collectSubfields schema variables runtimeType
                    (.object runtimeType reference) fields).run state
                  have child := executeExecutionPlan_erases schema resolvers variables fuel
                    runtimeType (.object runtimeType reference) collected.1.newDeferUsages
                    (buildExecutionPlan collected.1.collectedFieldsMap usages) path usages
                    context (route ++ [0]) collected.2
                  rw [← child]
                  simp only [eraseCompletionRun, RecordedCompletion.erase_catchNull]
                  rfl
        | list inner =>
            cases value with
            | null =>
                simp [EagerRecordedExecution.completeValue, Execution.completeValue,
                  eraseCompletionRun]
            | scalar scalar => simp [EagerRecordedExecution.completeValue,
                Execution.completeValue, eraseCompletionRun, Completion.error]
            | object runtimeType reference => simp [EagerRecordedExecution.completeValue,
                Execution.completeValue, eraseCompletionRun, Completion.error]
            | list items =>
                simpa only [EagerRecordedExecution.completeValue, Execution.completeValue]
                  using completeListValueWithStream_erases schema resolvers variables fuel
                    inner fields items path usages context allowStream (route ++ [0])
                    state
  termination_by (fuel, 1, sizeOf fieldType, 0)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  theorem completeListValue_erases (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (itemType : TypeRef)
      (fields : List FieldDetails) (values : List (ResolverValue ObjectRef))
      (path : ResponsePath) (index : Nat) (usages : List Nat) (context : DeferMap)
      (route : List Nat) (state : Nat)
      : eraseCompletionRun
          ((EagerRecordedExecution.completeListValue schema resolvers variables
              fuel itemType fields values path index usages context route).run
            state)
        = (Execution.completeListValue schema resolvers variables fuel itemType
            fields values path index usages context).run
            state := by
    cases values with
    | nil =>
        simp [EagerRecordedExecution.completeListValue, Execution.completeListValue,
          eraseCompletionRun]
    | cons value rest =>
        have head := completeValue_erases schema resolvers variables fuel itemType fields
          value (path ++ [.index index]) usages context false (route ++ [0]) state
        simp only [EagerRecordedExecution.completeListValue, Execution.completeListValue,
          run_bind, StateT.run_pure, id_pure_eq]
        rw [← head]
        dsimp only [eraseCompletionRun]
        have tail := completeListValue_erases schema resolvers variables fuel itemType
          fields rest path (index + 1) usages context (route ++ [1])
          ((EagerRecordedExecution.completeValue schema resolvers variables fuel itemType fields
            value (path ++ [.index index]) usages context false (route ++ [0])).run state).2
        rw [← tail]
        simp only [eraseCompletionRun, RecordedCompletion.erase_combine]
  termination_by (fuel, 2, sizeOf itemType, sizeOf values)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals omega

  theorem completeListValueWithStream_erases (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (inner : TypeRef) (fields : List FieldDetails)
      (values : List (ResolverValue ObjectRef)) (path : ResponsePath) (usages : List Nat)
      (context : DeferMap) (allowStream : Bool) (route : List Nat) (state : Nat)
      : eraseCompletionRun
          ((EagerRecordedExecution.completeListValueWithStream schema resolvers variables
              fuel inner fields values path usages context allowStream route).run
            state)
        = (Execution.completeListValueWithStream schema resolvers variables fuel
            inner fields values path usages context allowStream).run
            state := by
    simp only [EagerRecordedExecution.completeListValueWithStream,
      Execution.completeListValueWithStream]
    split
    · simp_all [eraseCompletionRun]
    · simp_all only
      have initial := completeListValue_erases schema resolvers variables fuel inner fields
        values path 0 usages context (route ++ [0]) state
      simp only [run_bind, StateT.run_pure, id_pure_eq]
      rw [← initial]
      simp only [eraseCompletionRun, RecordedCompletion.erase_catchNull]
    · rename_i usage usageEq
      simp_all only
      have initial := completeListValue_erases schema resolvers variables fuel inner fields
        (values.take usage.initialCount) path 0 usages context (route ++ [0]) state
      simp only [run_bind]
      rw [← initial]
      dsimp only [eraseCompletionRun]
      simp only [erase_result]
      split
      · simp_all only [StateT.run_pure, id_pure_eq, eraseCompletionRun,
          RecordedCompletion.erase_catchNull]
      · rename_i initialResult initialEq
        simp_all only
        split
        · simp_all only [StateT.run_pure, id_pure_eq, eraseCompletionRun,
            RecordedCompletion.erase_catchNull]
        · simp only [run_bind, freshNodeRef, StateT.run_get, StateT.run_set,
            StateT.run_pure, id_pure_eq]
          have items := completeStreamItems_erases schema resolvers variables fuel inner
            (fields.map (fun field => { field with deferUsage := none }))
            (values.drop usage.initialCount) path usage.initialCount (route ++ [1])
            (((EagerRecordedExecution.completeListValue schema resolvers variables fuel inner fields
              (values.take usage.initialCount) path 0 usages context (route ++ [0])).run state).2 + 1)
          rw [← items]
          simp only [eraseItemsRun, RecordedCompletion.erase, RecordedWork.erase, eraseItems,
            RecordedCompletion.catchNull, Report.catchNull, Completion.catchNull, initialEq]
  termination_by (fuel, 3, 0, 0)
  decreasing_by
    all_goals simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  theorem completeStreamItems_erases (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (itemType : TypeRef)
      (fields : List FieldDetails) (values : List (ResolverValue ObjectRef))
      (path : ResponsePath) (index : Nat) (route : List Nat) (state : Nat)
      : eraseItemsRun
          ((EagerRecordedExecution.completeStreamItems schema resolvers variables
              fuel itemType fields values path index route).run
            state)
        = (Execution.completeStreamItems schema resolvers variables fuel itemType
            fields values path index).run
            state := by
    cases values with
    | nil =>
        simp [EagerRecordedExecution.completeStreamItems, Execution.completeStreamItems,
          eraseItemsRun, eraseItems]
    | cons value rest =>
        have head := completeValue_erases schema resolvers variables fuel itemType fields
          value (path ++ [.index index]) [] [] false (route ++ [0]) state
        simp only [EagerRecordedExecution.completeStreamItems, Execution.completeStreamItems,
          run_bind]
        rw [← head]
        dsimp only [eraseCompletionRun]
        simp only [erase_result]
        split
        · simp [eraseItemsRun, eraseItems, RecordedWork.erase, RecordedCompletion.outcome,
            RecordedOutcome.erase, RecordedCompletion.erase, Completion.outcome, *]
        · rename_i result resultEq
          simp_all only
          have tail := completeStreamItems_erases schema resolvers variables fuel itemType
            fields rest path (index + 1) (route ++ [1])
            ((EagerRecordedExecution.completeValue schema resolvers variables fuel itemType fields
              value (path ++ [.index index]) [] [] false (route ++ [0])).run state).2
          simp only [run_bind, StateT.run_pure, id_pure_eq]
          rw [← tail]
          simp only [eraseItemsRun, eraseItems, List.map_cons, RecordedCompletion.erase,
            RecordedCompletion.outcome, RecordedOutcome.erase, Completion.outcome, resultEq]
  termination_by (fuel, 2, sizeOf itemType, sizeOf values)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals omega

  theorem executeExecutionPlan_erases (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (parentType : Name)
      (source : ResolverValue ObjectRef) (newUsages : List DeferUsage)
      (plan : ExecutionPlan) (path : ResponsePath) (usages : List Nat)
      (context : DeferMap) (route : List Nat) (state : Nat)
      : eraseCompletionRun
          ((EagerRecordedExecution.executeExecutionPlan schema resolvers variables
              fuel parentType source newUsages plan path usages context route).run
            state)
        = (Execution.executeExecutionPlan schema resolvers variables fuel
            parentType source newUsages plan path usages context).run
            state := by
    have initial := executeCollectedFields_erases schema resolvers variables fuel parentType
      source plan.collectedFieldsMap path usages (getNewDeferMap newUsages path context)
      (route ++ [0]) state
    simp only [EagerRecordedExecution.executeExecutionPlan, Execution.executeExecutionPlan,
      run_bind]
    rw [← initial]
    dsimp only [eraseCompletionRun]
    simp only [erase_result]
    split
    · simp_all only [StateT.run_pure, id_pure_eq]
    · rename_i result resultEq
      simp_all only
      have tasks := collectExecutionGroups_erases schema resolvers variables fuel parentType
        source plan.newCollectedFieldsMaps path (getNewDeferMap newUsages path context)
        (route ++ [1])
        ((EagerRecordedExecution.executeCollectedFields schema resolvers variables fuel parentType
          source plan.collectedFieldsMap path usages (getNewDeferMap newUsages path context)
          (route ++ [0])).run state).2
      simp only [run_bind, StateT.run_pure, id_pure_eq]
      rw [← tasks]
      simp only [eraseWorkRun, RecordedCompletion.erase, RecordedWork.erase,
        resultEq]
  termination_by (fuel, 6, 0, 0)
  decreasing_by
    all_goals simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  theorem collectExecutionGroups_erases (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (parentType : Name) (source : ResolverValue ObjectRef)
      (partitions : List (List Nat × CollectedFieldsMap)) (path : ResponsePath)
      (context : DeferMap) (route : List Nat) (state : Nat)
      : eraseWorkRun
          ((EagerRecordedExecution.collectExecutionGroups schema resolvers variables
              fuel parentType source partitions path context route).run
            state)
        = (Execution.collectExecutionGroups schema resolvers variables fuel
            parentType source partitions path context).run
            state := by
    cases partitions with
    | nil => simp [EagerRecordedExecution.collectExecutionGroups,
        Execution.collectExecutionGroups, eraseWorkRun, RecordedWork.erase]
    | cons partition rest =>
        obtain ⟨usages, fields⟩ := partition
        have head := executeCollectedFields_erases schema resolvers variables fuel parentType
          source fields path usages context (route ++ [0]) state
        simp only [EagerRecordedExecution.collectExecutionGroups, Execution.collectExecutionGroups,
          Execution.executeExecutionGroup, run_bind, StateT.run_pure, id_pure_eq]
        rw [← head]
        dsimp only [eraseCompletionRun, RecordedCompletion.erase]
        have tail := collectExecutionGroups_erases schema resolvers variables fuel parentType
          source rest path context (route ++ [1])
          ((EagerRecordedExecution.executeCollectedFields schema resolvers variables fuel parentType
            source fields path usages context (route ++ [0])).run state).2
        rw [← tail]
        simp only [eraseWorkRun, RecordedWork.erase, RecordedCompletion.outcome,
          RecordedOutcome.erase, Completion.outcome]
  termination_by (fuel, 5, 0, sizeOf partitions)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals omega
end

/-- Exact arbitrary recursive root erasure, with unchanged public results, retained
work and final delivery-key supply. No output correspondence is assumed. -/
def RecursiveEagerOriginErasure : Prop :=
  ∀ (ObjectRef : Type) (schema : Schema) (resolvers : Resolvers ObjectRef)
    variables fuel parentType (source : ResolverValue ObjectRef) selections route state,
    eraseCompletionRun
      ((EagerRecordedExecution.executeRootSelectionSetCore schema resolvers
          variables fuel parentType source selections route).run
        state)
    = (Execution.executeRootSelectionSetCore schema resolvers variables fuel
        parentType source selections).run
        state

theorem recursiveEagerOriginErasure_holds : RecursiveEagerOriginErasure := by
  intro ObjectRef schema resolvers variables fuel parentType source selections route state
  simp only [EagerRecordedExecution.executeRootSelectionSetCore,
    Execution.executeRootSelectionSetCore, run_bind]
  exact executeExecutionPlan_erases schema resolvers variables fuel parentType source _ _
    [] [] [] route _

end EagerErasure

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.OriginAccounting
