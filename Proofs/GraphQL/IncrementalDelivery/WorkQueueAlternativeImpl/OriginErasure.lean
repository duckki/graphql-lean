import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.OriginExecutor
import Proofs.GraphQL.IncrementalDelivery.Semantics.Collection

/-! Exact erasure of actual recursive originating-error annotations. This proof
compares executions, including retained future work and the final delivery-key supply;
it does not assume an output relation or recover origins from aggregate counts. -/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.OriginAccounting

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics

def eraseCompletionRun (output : RecordedCompletion α × Nat) : Completion α × Nat :=
  (output.1.erase, output.2)

def eraseItems (items : List (RecordedOutcome ResponseValue × RecordedWork))
    : List (TaskOutcome ResponseValue × Work) :=
  items.map (fun item => (item.1.erase, item.2.erase))

def eraseItemsRun (output : List (RecordedOutcome ResponseValue × RecordedWork) × Nat)
    : List (TaskOutcome ResponseValue × Work) × Nat :=
  (eraseItems output.1, output.2)

def eraseWorkRun (output : RecordedWork × Nat) : Work × Nat :=
  (output.1.erase, output.2)

theorem erase_result (completed : RecordedCompletion α)
    : completed.erase.result = completed.report.outcome :=
  rfl

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
          ((RecordedExecution.executeCollectedFields schema resolvers
              variables fuel parentType source fields path usages context route).run
            state)
        = (ScheduledExecution.executeCollectedFields schema resolvers variables fuel
            parentType source fields path usages context).run
            state := by
    cases fields with
    | nil => simp [RecordedExecution.executeCollectedFields,
        ScheduledExecution.executeCollectedFields, eraseCompletionRun]
    | cons field rest =>
        obtain ⟨name, group⟩ := field
        have head := executeResponseField_erases schema resolvers variables fuel parentType
          source name group path usages context (route ++ [0]) state
        simp only [RecordedExecution.executeCollectedFields,
          ScheduledExecution.executeCollectedFields, run_bind]
        rw [← head]
        dsimp only [eraseCompletionRun]
        simp only [erase_result]
        split
        · simp_all only [StateT.run_pure, id_pure_eq]
        · simp_all only
          have tail := executeCollectedFields_erases schema resolvers variables fuel
            parentType source rest path usages context (route ++ [1])
            ((RecordedExecution.executeResponseField schema resolvers variables fuel parentType
              source name group path usages context (route ++ [0])).run state).2
          simp only [run_bind, StateT.run_pure, id_pure_eq]
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
          ((RecordedExecution.executeResponseField schema resolvers
              variables fuel parentType source name fields path usages context route).run
            state)
        = (ScheduledExecution.executeResponseField schema resolvers variables fuel
            parentType source name fields path usages context).run
            state := by
    cases fuel with
    | zero => simp [RecordedExecution.executeResponseField,
        ScheduledExecution.executeResponseField, eraseCompletionRun, Completion.error]
    | succ fuel =>
        cases fields with
        | nil => simp [RecordedExecution.executeResponseField,
            ScheduledExecution.executeResponseField, eraseCompletionRun, Completion.error]
        | cons field rest =>
            simp only [RecordedExecution.executeResponseField,
              ScheduledExecution.executeResponseField]
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
          ((RecordedExecution.completeValue schema resolvers variables
              fuel fieldType fields value path usages context allowStream route).run
            state)
        = (ScheduledExecution.completeValue schema resolvers variables fuel fieldType
            fields value path usages context allowStream).run
            state := by
    cases fuel with
    | zero => simp [RecordedExecution.completeValue, ScheduledExecution.completeValue,
        eraseCompletionRun, Completion.error]
    | succ fuel =>
        cases fieldType with
        | nonNull inner =>
            have child := completeValue_erases schema resolvers variables (fuel + 1) inner
              fields value path usages context allowStream (route ++ [0]) state
            simp only [RecordedExecution.completeValue, ScheduledExecution.completeValue,
              run_bind, StateT.run_pure, id_pure_eq]
            rw [← child]
            simp only [eraseCompletionRun, RecordedCompletion.erase_nonNull]
        | named parentType =>
            cases value with
            | null =>
                simp [RecordedExecution.completeValue, ScheduledExecution.completeValue,
                  eraseCompletionRun]
            | scalar scalar =>
                simp only [RecordedExecution.completeValue, ScheduledExecution.completeValue]
                split <;> simp [eraseCompletionRun, Completion.error]
            | list items => simp [RecordedExecution.completeValue,
                ScheduledExecution.completeValue, eraseCompletionRun, Completion.error]
            | object runtimeType reference =>
                simp only [RecordedExecution.completeValue, ScheduledExecution.completeValue]
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
                simp [RecordedExecution.completeValue, ScheduledExecution.completeValue,
                  eraseCompletionRun]
            | scalar scalar => simp [RecordedExecution.completeValue,
                ScheduledExecution.completeValue, eraseCompletionRun, Completion.error]
            | object runtimeType reference => simp [RecordedExecution.completeValue,
                ScheduledExecution.completeValue, eraseCompletionRun, Completion.error]
            | list items =>
                simpa only [RecordedExecution.completeValue,
                  ScheduledExecution.completeValue]
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
          ((RecordedExecution.completeListValue schema resolvers variables
              fuel itemType fields values path index usages context route).run
            state)
        = (ScheduledExecution.completeListValue schema resolvers variables fuel itemType
            fields values path index usages context).run
            state := by
    cases values with
    | nil =>
        simp [RecordedExecution.completeListValue, ScheduledExecution.completeListValue,
          eraseCompletionRun]
    | cons value rest =>
        have head := completeValue_erases schema resolvers variables fuel itemType fields
          value (path ++ [.index index]) usages context false (route ++ [0]) state
        simp only [RecordedExecution.completeListValue, ScheduledExecution.completeListValue,
          run_bind]
        rw [← head]
        dsimp only [eraseCompletionRun]
        simp only [erase_result]
        split
        · simp_all [eraseCompletionRun, RecordedCompletion.map, Report.map,
            RecordedCompletion.erase, RecordedWork.erase, Completion.error]
        · simp_all only
          have tail := completeListValue_erases schema resolvers variables fuel itemType
            fields rest path (index + 1) usages context (route ++ [1])
            ((RecordedExecution.completeValue schema resolvers variables fuel itemType fields
              value (path ++ [.index index]) usages context false (route ++ [0])).run state).2
          simp only [run_bind, StateT.run_pure, id_pure_eq]
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
          ((RecordedExecution.completeListValueWithStream schema resolvers variables fuel
              inner fields values path usages context allowStream route).run
            state)
        = (ScheduledExecution.completeListValueWithStream schema resolvers variables fuel
            inner fields values path usages context allowStream).run
            state := by
    simp only [RecordedExecution.completeListValueWithStream,
      ScheduledExecution.completeListValueWithStream]
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
            (((RecordedExecution.completeListValue schema resolvers variables fuel inner fields
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
          ((RecordedExecution.completeStreamItems schema resolvers variables
              fuel itemType fields values path index route).run
            state)
        = (ScheduledExecution.completeStreamItems schema resolvers variables fuel itemType
            fields values path index).run
            state := by
    cases values with
    | nil =>
        simp [RecordedExecution.completeStreamItems, ScheduledExecution.completeStreamItems,
          eraseItemsRun, eraseItems]
    | cons value rest =>
        have head := completeValue_erases schema resolvers variables fuel itemType fields
          value (path ++ [.index index]) [] [] false (route ++ [0]) state
        simp only [RecordedExecution.completeStreamItems, ScheduledExecution.completeStreamItems,
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
            ((RecordedExecution.completeValue schema resolvers variables fuel itemType fields
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
          ((RecordedExecution.executeExecutionPlan schema resolvers variables
              fuel parentType source newUsages plan path usages context route).run
            state)
        = (ScheduledExecution.executeExecutionPlan schema resolvers variables fuel
            parentType source newUsages plan path usages context).run
            state := by
    have initial := executeCollectedFields_erases schema resolvers variables fuel parentType
      source plan.collectedFieldsMap path usages (getNewDeferMap newUsages path context)
      (route ++ [0]) state
    simp only [RecordedExecution.executeExecutionPlan, ScheduledExecution.executeExecutionPlan,
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
        ((RecordedExecution.executeCollectedFields schema resolvers variables fuel parentType
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
          ((RecordedExecution.collectExecutionGroups schema resolvers variables
              fuel parentType source partitions path context route).run
            state)
        = (ScheduledExecution.collectExecutionGroups schema resolvers variables fuel
            parentType source partitions path context).run
            state := by
    cases partitions with
    | nil => simp [RecordedExecution.collectExecutionGroups,
        ScheduledExecution.collectExecutionGroups, eraseWorkRun, RecordedWork.erase]
    | cons partition rest =>
        obtain ⟨usages, fields⟩ := partition
        have head := executeCollectedFields_erases schema resolvers variables fuel parentType
          source fields path usages context (route ++ [0]) state
        simp only [RecordedExecution.collectExecutionGroups, ScheduledExecution.collectExecutionGroups,
          run_bind, StateT.run_pure, id_pure_eq]
        rw [← head]
        dsimp only [eraseCompletionRun, RecordedCompletion.erase]
        have tail := collectExecutionGroups_erases schema resolvers variables fuel parentType
          source rest path context (route ++ [1])
          ((RecordedExecution.executeCollectedFields schema resolvers variables fuel parentType
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
def RecursiveOriginErasure : Prop :=
  ∀ (ObjectRef : Type) (schema : Schema) (resolvers : Resolvers ObjectRef)
    variables fuel parentType (source : ResolverValue ObjectRef) selections route state,
    eraseCompletionRun
      ((RecordedExecution.executeRootSelectionSetCore schema resolvers
          variables fuel parentType source selections route).run
        state)
    = (ScheduledExecution.executeRootSelectionSetCore schema resolvers variables fuel
        parentType source selections).run
        state

theorem recursiveOriginErasure_holds : RecursiveOriginErasure := by
  intro ObjectRef schema resolvers variables fuel parentType source selections route state
  simp only [RecordedExecution.executeRootSelectionSetCore,
    ScheduledExecution.executeRootSelectionSetCore, run_bind]
  exact executeExecutionPlan_erases schema resolvers variables fuel parentType source _ _
    [] [] [] route _

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.OriginAccounting
