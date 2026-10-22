import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.EagerOriginErasure
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RecursiveOriginUniqueness

/-! Unique primitive origins for actual public eager execution, via exact annotations.
The same structural call cones as the cut executor separate siblings, aliases, list
items and retained future task scopes. No native recording history is asserted. -/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.OriginAccounting

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics

namespace EagerScopes

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

mutual
  theorem executeCollectedFields_origins (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (parentType : Name) (source : ResolverValue ObjectRef) (fields : CollectedFieldsMap)
      (path : ResponsePath) (usages : List Nat) (context : DeferMap) (route : List Nat)
      (state : Nat)
      : Scoped route
          ((EagerRecordedExecution.executeCollectedFields schema resolvers variables
              fuel parentType source fields path usages context route).run
            state).1.origins := by
    cases fields with
    | nil =>
        simpa only [EagerRecordedExecution.executeCollectedFields, StateT.run_pure,
          id_pure_eq]
          using pure_scoped route ([] : List (Name × ResponseValue))
    | cons field rest =>
        obtain ⟨name, group⟩ := field
        have head := executeResponseField_origins schema resolvers variables fuel parentType
          source name group path usages context (route ++ [0]) state
        have tail := executeCollectedFields_origins schema resolvers variables fuel parentType
          source rest path usages context (route ++ [1])
          ((EagerRecordedExecution.executeResponseField schema resolvers variables fuel parentType
            source name group path usages context (route ++ [0])).run state).2
        simpa only [EagerRecordedExecution.executeCollectedFields, run_bind, StateT.run_pure,
          id_pure_eq] using combine_scoped List.append _ _ route head tail
  termination_by (fuel, 4, 0, sizeOf fields)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals omega

  theorem executeResponseField_origins (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (parentType : Name)
      (source : ResolverValue ObjectRef) (name : Name) (fields : List FieldDetails)
      (path : ResponsePath) (usages : List Nat) (context : DeferMap) (route : List Nat)
      (state : Nat)
      : Scoped route
          ((EagerRecordedExecution.executeResponseField schema resolvers variables
              fuel parentType source name fields path usages context route).run
            state).1.origins := by
    cases fuel with
    | zero =>
        simpa only [EagerRecordedExecution.executeResponseField, StateT.run_pure,
          id_pure_eq]
          using fault_scoped route (.error 1 : Result (List (Name × ResponseValue)))
    | succ fuel =>
        cases fields with
        | nil =>
            simpa only [EagerRecordedExecution.executeResponseField, StateT.run_pure,
              id_pure_eq]
              using fault_scoped route (.error 1 : Result (List (Name × ResponseValue)))
        | cons field rest =>
            simp only [EagerRecordedExecution.executeResponseField]
            split
            · exact fault_scoped route _
            · rename_i definition lookupEq
              split
              · exact fault_scoped route _
              · rename_i arguments argumentsEq
                split
                · exact fault_scoped route _
                · rename_i resolved resolvedEq
                  have child := completeValue_origins schema resolvers variables fuel
                    definition.outputType (field :: rest) resolved (path ++ [.field name])
                    usages context true (route ++ [0]) state
                  simpa only [run_bind, StateT.run_pure, id_pure_eq]
                    using map_scoped (fun value => [(name, value)]) _ route child.parent
  termination_by (fuel, 3, 0, sizeOf fields)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  theorem completeValue_origins (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (fieldType : TypeRef)
      (fields : List FieldDetails) (value : ResolverValue ObjectRef)
      (path : ResponsePath) (usages : List Nat) (context : DeferMap) (allowStream : Bool)
      (route : List Nat) (state : Nat)
      : Scoped route
          ((EagerRecordedExecution.completeValue schema resolvers variables fuel
              fieldType fields value path usages context allowStream route).run
            state).1.origins := by
    cases fuel with
    | zero =>
        simpa only [EagerRecordedExecution.completeValue, StateT.run_pure, id_pure_eq]
          using fault_scoped route (.error 1 : Result ResponseValue)
    | succ fuel =>
        cases fieldType with
        | nonNull inner =>
            have child := completeValue_origins schema resolvers variables (fuel + 1) inner
              fields value path usages context allowStream (route ++ [0]) state
            simpa only [EagerRecordedExecution.completeValue, run_bind, StateT.run_pure,
              id_pure_eq]
              using nonNull_scoped _ route child
        | named parentType =>
            cases value with
            | null =>
                simpa only [EagerRecordedExecution.completeValue, StateT.run_pure,
                  id_pure_eq]
                  using pure_scoped route ResponseValue.null
            | scalar scalar =>
                simp only [EagerRecordedExecution.completeValue]
                split
                · exact fault_scoped route _
                · exact pure_scoped route _
            | list items =>
                simpa only [EagerRecordedExecution.completeValue, StateT.run_pure,
                  id_pure_eq]
                  using fault_scoped route (.error 1 : Result ResponseValue)
            | object runtimeType reference =>
                simp only [EagerRecordedExecution.completeValue]
                split
                · exact fault_scoped route _
                · let collected := (collectSubfields schema variables runtimeType
                    (.object runtimeType reference) fields).run state
                  have child := executeExecutionPlan_origins schema resolvers variables fuel
                    runtimeType (.object runtimeType reference) collected.1.newDeferUsages
                    (buildExecutionPlan collected.1.collectedFieldsMap usages) path usages
                    context (route ++ [0]) collected.2
                  simpa only [run_bind, StateT.run_pure, id_pure_eq]
                    using catchNull_scoped ResponseValue.object _ route child.parent
        | list inner =>
            cases value with
            | null =>
                simpa only [EagerRecordedExecution.completeValue, StateT.run_pure,
                  id_pure_eq]
                  using pure_scoped route ResponseValue.null
            | scalar scalar =>
                simpa only [EagerRecordedExecution.completeValue, StateT.run_pure,
                  id_pure_eq]
                  using fault_scoped route (.error 1 : Result ResponseValue)
            | object runtimeType reference =>
                simpa only [EagerRecordedExecution.completeValue,
                  StateT.run_pure, id_pure_eq] using fault_scoped route (.error 1 : Result ResponseValue)
            | list items =>
                simpa only [EagerRecordedExecution.completeValue]
                  using (completeListValueWithStream_origins schema resolvers variables
                          fuel inner fields items path usages context allowStream
                          (route ++ [0]) state).parent
  termination_by (fuel, 1, sizeOf fieldType, 0)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  theorem completeListValue_origins (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (itemType : TypeRef)
      (fields : List FieldDetails) (values : List (ResolverValue ObjectRef))
      (path : ResponsePath) (index : Nat) (usages : List Nat) (context : DeferMap)
      (route : List Nat) (state : Nat)
      : Scoped route
          ((EagerRecordedExecution.completeListValue schema resolvers variables fuel
              itemType fields values path index usages context route).run
            state).1.origins := by
    cases values with
    | nil =>
        simpa only [EagerRecordedExecution.completeListValue, StateT.run_pure, id_pure_eq]
          using pure_scoped route ([] : List ResponseValue)
    | cons value rest =>
        have head := completeValue_origins schema resolvers variables fuel itemType fields
          value (path ++ [.index index]) usages context false (route ++ [0]) state
        have tail := completeListValue_origins schema resolvers variables fuel itemType
          fields rest path (index + 1) usages context (route ++ [1])
          ((EagerRecordedExecution.completeValue schema resolvers variables fuel itemType fields
            value (path ++ [.index index]) usages context false (route ++ [0])).run state).2
        simpa only [EagerRecordedExecution.completeListValue, run_bind, StateT.run_pure,
          id_pure_eq] using combine_scoped List.cons _ _ route head tail
  termination_by (fuel, 2, sizeOf itemType, sizeOf values)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals omega

  theorem completeListValueWithStream_origins (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (inner : TypeRef) (fields : List FieldDetails)
      (values : List (ResolverValue ObjectRef)) (path : ResponsePath) (usages : List Nat)
      (context : DeferMap) (allowStream : Bool) (route : List Nat) (state : Nat)
      : Scoped route
          ((EagerRecordedExecution.completeListValueWithStream schema resolvers variables
              fuel inner fields values path usages context allowStream route).run
            state).1.origins := by
    simp only [EagerRecordedExecution.completeListValueWithStream]
    split
    · exact fault_scoped route _
    · have initial := completeListValue_origins schema resolvers variables fuel inner fields
        values path 0 usages context (route ++ [0]) state
      simpa only [run_bind, StateT.run_pure, id_pure_eq]
        using catchNull_scoped ResponseValue.list _ route initial.parent
    · rename_i usage usageEq
      have initial := completeListValue_origins schema resolvers variables fuel inner fields
        (values.take usage.initialCount) path 0 usages context (route ++ [0]) state
      simp only [run_bind]
      split
      · simpa only [StateT.run_pure, id_pure_eq]
          using catchNull_scoped ResponseValue.list _ route initial.parent
      · split
        · simpa only [StateT.run_pure, id_pure_eq]
            using catchNull_scoped ResponseValue.list _ route initial.parent
        · have items := completeStreamItems_origins schema resolvers variables fuel inner
            (fields.map (fun field => { field with deferUsage := none }))
            (values.drop usage.initialCount) path usage.initialCount (route ++ [1])
            (((EagerRecordedExecution.completeListValue schema resolvers variables fuel inner fields
              (values.take usage.initialCount) path 0 usages context (route ++ [0])).run state).2 + 1)
          simp only [run_bind, freshNodeRef, StateT.run_get, StateT.run_set,
            StateT.run_pure, id_pure_eq]
          exact appendWork_scoped _ _ route
            (catchNull_scoped ResponseValue.list _ _ initial)
            (by simpa only [RecordedWork.origins, itemOrigins] using items)
  termination_by (fuel, 3, 0, 0)
  decreasing_by
    all_goals simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  theorem completeStreamItems_origins (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (itemType : TypeRef)
      (fields : List FieldDetails) (values : List (ResolverValue ObjectRef))
      (path : ResponsePath) (index : Nat) (route : List Nat) (state : Nat)
      : Scoped route
          (itemOrigins
            ((EagerRecordedExecution.completeStreamItems schema resolvers
                variables fuel itemType fields values path index route).run
              state).1) := by
    cases values with
    | nil =>
        simpa only [EagerRecordedExecution.completeStreamItems, StateT.run_pure, id_pure_eq,
          itemOrigins, List.flatMap_nil] using Scoped.empty route
    | cons value rest =>
        have head := completeValue_origins schema resolvers variables fuel itemType fields
          value (path ++ [.index index]) [] [] false (route ++ [0]) state
        simp only [EagerRecordedExecution.completeStreamItems, run_bind]
        split
        · simpa only [StateT.run_pure, id_pure_eq, RecordedCompletion.outcome, itemOrigins, List.flatMap_cons,
            List.flatMap_nil, RecordedWork.origins, List.append_nil] using head.left.parent
        · have tail := completeStreamItems_origins schema resolvers variables fuel itemType
            fields rest path (index + 1) (route ++ [1])
            ((EagerRecordedExecution.completeValue schema resolvers variables fuel itemType fields
              value (path ++ [.index index]) [] [] false (route ++ [0])).run state).2
          simpa only [run_bind, StateT.run_pure, id_pure_eq, RecordedCompletion.outcome, itemOrigins, List.flatMap_cons,
            RecordedCompletion.origins, RecordedCompletion.outcome] using Scoped.join head tail
  termination_by (fuel, 2, sizeOf itemType, sizeOf values)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals omega

  theorem executeExecutionPlan_origins (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (parentType : Name)
      (source : ResolverValue ObjectRef) (newUsages : List DeferUsage)
      (plan : ExecutionPlan) (path : ResponsePath) (usages : List Nat)
      (context : DeferMap) (route : List Nat) (state : Nat)
      : Scoped route
          ((EagerRecordedExecution.executeExecutionPlan schema resolvers variables fuel
              parentType source newUsages plan path usages context route).run
            state).1.origins := by
    have initial := executeCollectedFields_origins schema resolvers variables fuel parentType
      source plan.collectedFieldsMap path usages (getNewDeferMap newUsages path context)
      (route ++ [0]) state
    simp only [EagerRecordedExecution.executeExecutionPlan, run_bind]
    split
    · simpa only [StateT.run_pure, id_pure_eq] using initial.parent
    · have tasks := collectExecutionGroups_origins schema resolvers variables fuel parentType
        source plan.newCollectedFieldsMaps path (getNewDeferMap newUsages path context)
        (route ++ [1])
        ((EagerRecordedExecution.executeCollectedFields schema resolvers variables fuel parentType
          source plan.collectedFieldsMap path usages (getNewDeferMap newUsages path context)
          (route ++ [0])).run state).2
      simpa only [run_bind, StateT.run_pure, id_pure_eq]
        using appendWork_scoped _ _ route initial tasks
  termination_by (fuel, 6, 0, 0)
  decreasing_by
    all_goals simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  theorem collectExecutionGroups_origins (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (parentType : Name) (source : ResolverValue ObjectRef)
      (partitions : List (List Nat × CollectedFieldsMap)) (path : ResponsePath)
      (context : DeferMap) (route : List Nat) (state : Nat)
      : Scoped route
          ((EagerRecordedExecution.collectExecutionGroups schema resolvers variables
              fuel parentType source partitions path context route).run
            state).1.origins := by
    cases partitions with
    | nil =>
        simpa only [EagerRecordedExecution.collectExecutionGroups, StateT.run_pure, id_pure_eq,
          RecordedWork.origins] using Scoped.empty route
    | cons partition rest =>
        obtain ⟨usages, fields⟩ := partition
        have head := executeCollectedFields_origins schema resolvers variables fuel parentType
          source fields path usages context (route ++ [0]) state
        have tail := collectExecutionGroups_origins schema resolvers variables fuel parentType
          source rest path context (route ++ [1])
          ((EagerRecordedExecution.executeCollectedFields schema resolvers variables fuel parentType
            source fields path usages context (route ++ [0])).run state).2
        simpa only [EagerRecordedExecution.collectExecutionGroups, run_bind,
          StateT.run_pure, id_pure_eq, RecordedWork.origins, RecordedCompletion.origins,
          RecordedCompletion.outcome]
          using Scoped.join head tail
  termination_by (fuel, 5, 0, sizeOf partitions)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals omega
end

/-- Every retained initial/task/item error in one arbitrary actual recursive run has
a distinct primitive origin. This says nothing about native starts or recording time. -/
def RecursiveEagerOriginUniqueness : Prop :=
  ∀ (ObjectRef : Type) (schema : Schema) (resolvers : Resolvers ObjectRef)
    variables fuel parentType (source : ResolverValue ObjectRef) selections route state,
    Scoped route
      ((EagerRecordedExecution.executeRootSelectionSetCore schema resolvers
          variables fuel parentType source selections route).run
        state).1.origins

theorem recursiveEagerOriginUniqueness_holds : RecursiveEagerOriginUniqueness := by
  intro ObjectRef schema resolvers variables fuel parentType source selections route state
  simp only [EagerRecordedExecution.executeRootSelectionSetCore, run_bind]
  exact executeExecutionPlan_origins schema resolvers variables fuel parentType source _ _
    [] [] [] route _

end EagerScopes

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.OriginAccounting
